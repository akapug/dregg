//! The portable fallback IO path: a thread-per-connection blocking host.
//!
//! Each accepted connection is handled by its own thread (soft-capped), which
//! reads a request off the wire, hands the request bytes to the serve thread
//! over the gateway, waits for the response, and writes it back — all while
//! other connection threads overlap their own reads, writes, and keep-alive idle
//! waits. This is the path used on platforms without io_uring (macOS and
//! others); on Linux the io_uring loop is preferred but this path remains
//! available for comparison.
//!
//! Buffers are pooled: the connection's accumulation buffer, the request buffer
//! handed to the serve thread, and the response buffer handed back all come from
//! and return to the shared [`BufferPool`], so a warm host allocates nothing per
//! request on the Rust side (§ `pool`).

use std::io::{Read, Write};
use std::net::{IpAddr, Ipv4Addr, TcpListener, TcpStream};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::sync::mpsc::channel;
use std::time::Duration;

use crate::http::{
    Frame, H2_PREFACE, annotate_connection, next_request, request_wants_keepalive,
    response_is_self_delimited,
};
use crate::pool::PooledBuf;
use crate::serve::{Meter, Seam, ServeGateway};
use crate::ws;

/// How long a kept-alive connection may sit idle between requests before the
/// host reclaims it.
const IDLE_TIMEOUT: Duration = Duration::from_secs(60);

/// Ceiling on concurrent connection threads. Beyond it, new connections are
/// closed immediately (refused) rather than spawning unbounded threads.
const MAX_CONNS: usize = 1024;

/// The process-global per-source connection counter for this reactor. Shared
/// (striped, not a single global mutex) because the blocking host is
/// thread-per-connection: the accept loop increments, each worker thread
/// decrements when it returns. Enforces the config's `max-connections` cap
/// per source (the proven `Reactor.Stage.ConnLimit` decision).
fn source_table() -> &'static crate::standing::SharedStanding {
    static TABLE: std::sync::OnceLock<crate::standing::SharedStanding> = std::sync::OnceLock::new();
    TABLE.get_or_init(crate::standing::SharedStanding::new)
}

/// The canned `503 Service Unavailable` a source at/over its `max-connections` cap
/// receives — the wire form of the proven `Reactor.Stage.ConnLimit.resp503`.
const CONN_LIMIT_503: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Type: text/plain\r\nContent-Length: 36\r\nConnection: close\r\n\r\nper-source connection limit reached\n";

/// The canned `429 Too Many Requests` a source over its `rate-limit` window receives
/// — the wire form of the proven `Reactor.Stage.StickTable.resp429`.
const RATE_LIMIT_429: &[u8] =
    b"HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain\r\nContent-Length: 20\r\nConnection: close\r\n\r\nrate limit exceeded\n";

/// The canned `408 Request Timeout` a connection whose header phase overran
/// `slowloris-timeout` receives — the wire form of the proven
/// `Reactor.Stage.Slowloris.resp408`.
const SLOWLORIS_408: &[u8] =
    b"HTTP/1.1 408 Request Timeout\r\nContent-Type: text/plain\r\nContent-Length: 23\r\nConnection: close\r\n\r\nrequest header timeout\n";

/// One socket read into a pooled accumulation buffer. Returns bytes read
/// (0 = clean EOF).
fn fill(data: &mut Vec<u8>, stream: &mut TcpStream) -> std::io::Result<usize> {
    let mut chunk = [0u8; 16384];
    let n = stream.read(&mut chunk)?;
    data.extend_from_slice(&chunk[..n]);
    Ok(n)
}

/// The client address the IP-filter gate should decide on. The connection's real
/// accept peer is the default; when that peer is a trusted proxy (here: loopback,
/// the only peer this host binds for), a well-formed `X-Forwarded-For` in the
/// request head overrides it with the originating client the proxy attributes —
/// the standard edge-attribution pattern (the proven core still decides admit or
/// deny). Only the FIRST address of the forwarded chain (the closest client) is
/// honored, and only when it parses as an IP; anything else falls back to `peer`.
pub(crate) fn client_addr(req: &[u8], peer: IpAddr) -> IpAddr {
    if !peer.is_loopback() {
        return peer; // never trust a forwarded header from an untrusted peer
    }
    // Scan the request head (up to the blank line) for `X-Forwarded-For`.
    let head_end = req
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 2)
        .unwrap_or(req.len());
    for line in req[..head_end].split(|&b| b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let Some(colon) = line.iter().position(|&b| b == b':') else {
            continue;
        };
        let (name, rest) = line.split_at(colon);
        if !name.eq_ignore_ascii_case(b"x-forwarded-for") {
            continue;
        }
        let value = &rest[1..]; // drop the ':'
        let first = value.split(|&b| b == b',').next().unwrap_or(value);
        let trimmed: &[u8] = {
            let s = first
                .iter()
                .position(|b| !b.is_ascii_whitespace())
                .unwrap_or(first.len());
            let e = first
                .iter()
                .rposition(|b| !b.is_ascii_whitespace())
                .map(|p| p + 1)
                .unwrap_or(s);
            &first[s..e]
        };
        if let Ok(text) = std::str::from_utf8(trimmed) {
            if let Ok(ip) = text.parse::<IpAddr>() {
                return ip;
            }
        }
        break; // first X-Forwarded-For header seen; do not scan further
    }
    peer
}

/// Handle one accepted connection: the keep-alive loop. Reads a request, routes
/// it through the proven core, writes the response, and loops on the same socket
/// until the client asks to close, the response cannot be kept alive, EOF, an
/// idle timeout, or an error.
fn handle_conn(mut stream: TcpStream, gw: &ServeGateway) {
    use std::io::ErrorKind;

    // The accept peer for this connection — the default client address the
    // IP-filter gate decides on. Unresolvable peers fall back to an unspecified
    // address, which the default-admit ruleset passes.
    let peer_ip = stream
        .peer_addr()
        .map(|a| a.ip())
        .unwrap_or(IpAddr::V4(Ipv4Addr::UNSPECIFIED));

    // Per-connection request index, threaded as the rate bucket's standing
    // depletion: request 0 sees a full bucket, request `cap` and later find it
    // empty (a burst on ONE kept-alive connection is what trips the limiter).
    let mut conn_seq: u64 = 0;

    // Sockets accepted from a non-blocking listener inherit non-blocking mode on
    // BSD/macOS; force this connection back to blocking so the idle read below
    // blocks (up to the read timeout) instead of returning WouldBlock at once.
    let _ = stream.set_nonblocking(false);
    let _ = stream.set_nodelay(true);
    let _ = stream.set_read_timeout(Some(IDLE_TIMEOUT));

    // Pooled accumulation buffer, reused across every request on this
    // connection; a per-connection reply channel, reused across keep-alive
    // requests so no channel is allocated per request.
    let mut acc: PooledBuf = gw.pool().take();
    let (reply_tx, reply_rx) = channel::<PooledBuf>();

    'conn: loop {
        // Peek at the connection opener: an h2c preface is not HTTP/1.1-framed.
        if acc.is_empty() {
            match fill(&mut acc, &mut stream) {
                Ok(0) => return,
                Ok(_) => {}
                Err(e) if e.kind() == ErrorKind::WouldBlock || e.kind() == ErrorKind::TimedOut => {
                    return;
                }
                Err(_) => return,
            }
            if acc.len() >= H2_PREFACE.len() && acc.starts_with(H2_PREFACE) {
                // h2c prior-knowledge (RFC 9113 §3.3/§3.4): the client writes its
                // connection preface, SETTINGS, and the request HEADERS as one
                // opening burst and then WAITS for the server to answer — it sends
                // nothing more until it gets the server SETTINGS + response frames.
                // So the host must collect the burst up to the request HEADERS
                // frame and then serve; a plain blocking read past that point
                // deadlocks (the client waits on us, we wait on it) and the client
                // times out. Read with a short grace timeout, stopping as soon as
                // the HEADERS frame is buffered, then hand the whole burst to the
                // proven H2 serve once and reply.
                let _ = stream.set_read_timeout(Some(Duration::from_millis(200)));
                while !crate::http::h2c_burst_complete(&acc) {
                    match fill(&mut acc, &mut stream) {
                        Ok(0) => break, // peer closed
                        Ok(_) => {}     // more of the burst arrived; rescan
                        Err(e)
                            if e.kind() == ErrorKind::WouldBlock
                                || e.kind() == ErrorKind::TimedOut =>
                        {
                            break; // grace elapsed: serve whatever we have
                        }
                        Err(_) => return,
                    }
                }
                let mut req = gw.pool().take();
                req.extend_from_slice(&acc);
                if let Some(resp) = gw.call(req, &reply_tx, &reply_rx) {
                    let _ = stream.write_all(&resp);
                }
                return;
            }
        }

        // SLOWLORIS: the header-phase deadline for the FIRST request on this
        // connection. Captured at the start of reading it; a drip that has not
        // completed a request head within `slowloris-timeout` is dropped with the REAL
        // proven 408 (`slowloris_fires`). Only the first request (`conn_seq == 0`) is
        // guarded — the classic slowloris defense. A fully-silent partial is reaped by
        // the socket read timeout (`IDLE_TIMEOUT`) instead.
        let slow_timeout = crate::config::slowloris_timeout();
        let hdr_start = std::time::Instant::now();
        // Read exactly one complete request into `acc`.
        let total = loop {
            // Consult the deadline BEFORE framing, so a slow drip that finally completes
            // its head past the deadline is still refused (mirrors the io_uring shard).
            if conn_seq == 0
                && crate::standing::header_expired(
                    slow_timeout,
                    hdr_start,
                    std::time::Instant::now(),
                )
            {
                let _ = stream.write_all(SLOWLORIS_408);
                let _ = stream.flush();
                return;
            }
            match next_request(&acc) {
                Frame::Complete(n) => break n,
                Frame::Oversize => return,
                Frame::NeedMore => match fill(&mut acc, &mut stream) {
                    Ok(0) => {
                        // Clean close only on a request boundary (empty buffer).
                        return;
                    }
                    Ok(_) => {}
                    Err(_) => return, // I/O error or idle timeout
                },
            }
        };

        // Move the request bytes into a pooled buffer, then drop them from the
        // accumulation buffer, retaining any pipelined bytes for the next round.
        let mut req = gw.pool().take();
        req.extend_from_slice(&acc[..total]);
        acc.drain(..total);

        // Access-log capture (opt-in, `DRORB_ACCESS_LOG`): grab the request line
        // and effective client BEFORE the request buffer is consumed by the serve
        // call, and start the request timer. Cheap and skipped entirely when the
        // log is off. `emit` writes one line at whichever response path serves it.
        let req_start = std::time::Instant::now();
        let logrec = if crate::access_log::enabled() {
            Some((
                crate::access_log::ReqLine::parse(&req),
                client_addr(&req, peer_ip),
            ))
        } else {
            None
        };
        let emit = |resp: &[u8], backend: Option<&str>| {
            // Untrusted-shell observability from the serve loop: bump the metric
            // counters (total / status-class / bytes / per-backend) for every
            // served response, then the opt-in access log. Neither touches the
            // proven core's decision.
            crate::metrics::record(resp, backend);
            if let Some((rl, client)) = &logrec {
                crate::access_log::log(*client, rl, resp, backend, req_start);
            }
        };
        // The same observability for a STREAMED response, whose body was written
        // straight to the socket and so was never in hand as one buffer: the host
        // records the status off the response head and the exact streamed byte total.
        let emit_streamed = |head: &[u8], bytes: u64, backend: Option<&str>| {
            crate::metrics::record_streamed(head, bytes, backend);
            if let Some((rl, client)) = &logrec {
                crate::access_log::log_streamed(*client, rl, head, bytes, backend, req_start);
            }
        };

        // WebSocket lane (RFC 6455): if this request is an Upgrade, complete the
        // handshake here (the host owns the accept token — see `ws`) and keep the
        // connection OPEN, running every subsequent frame through the proven
        // `Seam::WsFrame`. This is the TCP analogue of the proven Ingress fork.
        if ws::is_ws_upgrade(&req) {
            // AUTH GATE: the RFC 6455 handshake must not bypass authentication. Run
            // the upgrade REQUEST through the deployed `/admin` JWT gate (the same
            // gate the request path's fold runs) BEFORE returning 101. If the
            // upgrade targets a protected path with no/invalid credentials the gate
            // returns a 401; write that refusal and close instead of upgrading. An
            // authorized upgrade returns no gate bytes and proceeds to the 101.
            let mut gate_req = gw.pool().take();
            gate_req.extend_from_slice(&req);
            match gw.call_seam(gate_req, Seam::UpgradeGate, &reply_tx, &reply_rx) {
                Some(refusal) if !refusal.is_empty() => {
                    let _ = stream.write_all(&refusal);
                    return;
                }
                Some(_) => {}   // authorized: no refusal bytes — complete the handshake
                None => return, // serve thread gone (shutdown)
            }
            if let Some(resp) = ws::upgrade_response(&req) {
                if stream.write_all(&resp).is_err() {
                    return;
                }
                eprintln!("dataplane: WS upgrade OK — connection open, proven frame loop");
                ws_frame_loop(&mut stream, gw, &reply_tx, &reply_rx, &mut acc);
            }
            return;
        }

        let keepalive_req = request_wants_keepalive(&req);

        // GEARS-ENMESH: the exact `GET /health` request, when `DRORB_HEALTH_NATIVE=1`,
        // is answered by cake--pancake-compiled x64 machine code linked into this
        // process (ffi/health/health.S, driven by the re-entrant health_ffi.c) rather
        // than the leanc-compiled proven serve. The response bytes are produced by the
        // CakeML machine code and are byte-identical to the leanc path's wire output.
        // Returns false for every other request and every non-demo build (the native
        // library is not linked), so everything else runs the proven pipeline below.
        if crate::serve::wants_native_health(&req) {
            let mut native = gw.pool().take();
            if crate::serve::serve_native_into(&req, &mut native) {
                let keepalive = keepalive_req && response_is_self_delimited(&native);
                // The cake bytes are the final wire form (they already carry the
                // Connection header the leanc path's host annotation adds), so write
                // them as-is — no re-annotation.
                emit(&native, None);
                if stream.write_all(&native).is_err() {
                    return;
                }
                if !keepalive {
                    return;
                }
                continue 'conn;
            }
        }

        // CONNECT tunnel lane: the proven default-deny admission gate
        // (`drorb_connect_gate`) decides whether the named `host:port` may be
        // tunnelled; on admit the host dials it and runs the blind bidirectional
        // pump (reusing the streaming discipline), otherwise it writes the 403.
        // The connection is consumed by the tunnel either way.
        if crate::proxy_connect::is_connect(&req) {
            let tunnel_stream = match stream.try_clone() {
                Ok(s) => s,
                Err(_) => return,
            };
            crate::proxy_connect::handle_connect(&req, tunnel_stream, gw, &reply_tx, &reply_rx);
            return;
        }

        // Effect/continuation seam (`DRORB_EFFECT_SEAM=1`): the PROVEN core drives
        // the whole fabric decision — whether to proxy (which backend), whether to
        // cache (which key, what lifetime, gate-admitted HIT), and what to do with
        // an upstream reply — and the interpreter loop only executes the yielded
        // effects. `should_handle` is a conservative host prefilter (the seam is
        // consulted for the proxy route and the cacheable-route shape); the core
        // still makes the real decision. A `None` return means the request is not
        // one the seam acts on, so it falls through to the metered serve below
        // (which carries the real IP-filter / rate gates).
        if crate::interp::enabled() && crate::interp::should_handle(&req) {
            if let Some(mut resp) = crate::interp::run_effect_serve(&req, gw, &reply_tx, &reply_rx)
            {
                let keepalive = keepalive_req && response_is_self_delimited(&resp);
                annotate_connection(&mut resp, keepalive);
                emit(&resp, None);
                if stream.write_all(&resp).is_err() {
                    return;
                }
                if !keepalive {
                    return;
                }
                continue 'conn;
            }
        }

        // Reverse-proxy lane (established hook, effect seam OFF): a request under a
        // proxy route (/api) with a configured backend fleet is forwarded to a LIVE
        // upstream via `drorb_proxy_pick`. Returns None when no fleet is configured,
        // so /api falls through to the normal serve unchanged.
        if !crate::interp::enabled() && crate::proxy_hook::is_proxy_path(&req) {
            match crate::proxy_hook::handle_proxy_streaming(
                &req,
                keepalive_req,
                &mut stream,
                gw,
                &reply_tx,
                &reply_rx,
            ) {
                Some(Ok(out)) => {
                    // The upstream reply was already streamed to the client; the
                    // host only records it and decides the connection disposition.
                    emit_streamed(&out.head, out.bytes, out.backend.as_deref());
                    if !out.keepalive {
                        return;
                    }
                    continue 'conn;
                }
                Some(Err(_)) => return, // client write failed mid-stream
                None => {}              // no fleet configured: fall through
            }
        }

        // Per-host reverse-proxy: an operator config virtual host `route … proxy
        // <pool>` forwards requests whose `Host` names a declared proxy vhost to the
        // live backend fleet — the same `handle_proxy` path as `/api`, but gated on the
        // request authority instead of a fixed path. The proven `drorb_proxy_pick` still
        // chooses the backend; the `hostGlob` served path answers a proxy block route
        // with a placeholder, so the real forward is decided here, host-side. Fires
        // independent of the effect seam (a config vhost may proxy any path under a host).
        if let Some(dep) = crate::config::get() {
            if dep.is_vhost_proxy(&req) {
                match crate::proxy_hook::handle_proxy_streaming(
                    &req,
                    keepalive_req,
                    &mut stream,
                    gw,
                    &reply_tx,
                    &reply_rx,
                ) {
                    Some(Ok(out)) => {
                        emit_streamed(&out.head, out.bytes, out.backend.as_deref());
                        if !out.keepalive {
                            return;
                        }
                        continue 'conn;
                    }
                    Some(Err(_)) => return,
                    None => {}
                }
            }
        }

        // Config route-table serve: when the operator config (DRORB_CONFIG) declares
        // its own route table, non-proxy requests are served through `drorb_serve_cfg`
        // — the SAME proven fourteen-stage fold, but over the config's declared routes
        // (redirect/respond/static answered directly). Proxy `/api` requests were
        // already handled above (effect seam / proxy hook), so they never reach here.
        // With no DRORB_CONFIG (or a routeless one) this is skipped and the default
        // metered serve runs unchanged — so the default conformance is untouched.
        if let Some(dep) = crate::config::get() {
            if dep.has_routes() {
                if let Some(mut resp) = gw.call_cfg(&dep.config_text, &req, &reply_tx, &reply_rx) {
                    let keepalive = keepalive_req && response_is_self_delimited(&resp);
                    annotate_connection(&mut resp, keepalive);
                    emit(&resp, None);
                    if stream.write_all(&resp).is_err() {
                        return;
                    }
                    if !keepalive {
                        return;
                    }
                    continue 'conn;
                }
            }
        }

        // Host-side static-file streaming lane (roadmap Stage 3, gated on
        // `DRORB_STATIC_ROOT`): a GET/HEAD under the serving prefix streams the
        // resolved file to the client with a BOUNDED buffer — the head decided
        // batch-small (Content-Length + type), the body copied block-by-block, never
        // materialized whole. The emitted stream reassembles to `serialize` of the
        // static-file response the core would produce (proven core-side:
        // `Reactor.ServeStream.staticFile_emit_refines`). Unset ⇒ inert ⇒ the default
        // serve path is byte-identical.
        if let Some(sr) = crate::static_serve::get() {
            if sr.is_static_path(&req) {
                match sr.handle_streaming(&req, keepalive_req, &mut stream) {
                    Ok(out) => {
                        emit_streamed(&out.head, out.bytes, None);
                        if !out.keepalive {
                            return;
                        }
                        conn_seq = conn_seq.saturating_add(1);
                        continue 'conn;
                    }
                    Err(_) => return, // client write failed mid-stream
                }
            }
        }

        // Streaming response-emit path (`DRORB_STREAM_SERVE=1`): pull the proven
        // response out of `drorb_serve_stream` one bounded chunk at a time and write
        // each straight to the socket, so the host never holds the whole response.
        // The chunks reassemble to the exact `drorb_serve` bytes
        // (`serveChunkList_flatten`), so the wire output is byte-identical; only the
        // host's memory profile changes. Gated OFF by default (this path mirrors the
        // NON-metered serve), so the default metered conformance path is untouched.
        if crate::stream_serve::enabled() {
            match crate::stream_serve::serve_streamed(
                &req,
                keepalive_req,
                &mut stream,
                gw,
                &reply_tx,
                &reply_rx,
            ) {
                Some(Ok(out)) => {
                    emit_streamed(&out.head, out.bytes, None);
                    if !out.keepalive {
                        return;
                    }
                    conn_seq = conn_seq.saturating_add(1);
                    continue 'conn;
                }
                Some(Err(_)) => return, // client write failed mid-stream
                None => return,         // serve thread gone (shutdown)
            }
        }

        // Cross the METERED seam: the proven IP-filter gate decides on this
        // connection's client address (accept peer, or the forwarded client when
        // the peer is a trusted proxy) and the rate gate on the per-connection
        // request index. `conn_seq` advances once per served request, so a burst
        // on one kept-alive connection depletes the bucket.
        let meter = Meter {
            client: client_addr(&req, peer_ip),
            seq: conn_seq,
        };
        conn_seq = conn_seq.saturating_add(1);
        // Braid 0: the default serve is now the CONFIG-DRIVEN metered fold. The
        // request crosses `drorb_serve_metered_cfg` carrying the active deployment
        // config (`config::get()`), so the running default serve is a fold over
        // `deployment.middleware.chain`. With no `DRORB_CONFIG` the config is EMPTY
        // and the proven core serves `servePipelineOfMetered defaultDeployment` —
        // byte-for-byte the old `call_metered` (`servePipelineOfMetered_default`,
        // `rfl`), so the default conformance is untouched. A config declaring routes
        // was already served through `call_cfg` above and never reaches here; this
        // arm handles the routeless / no-config default. A future middleware braid is
        // a config-gated append to the chain, not shared-file surgery here.
        // Braid: when the deployment is braid-marked (`DRORB_BRAID=1`), the request
        // crosses the metered BRAIDED seam (`drorb_serve_metered_braided`) — the same
        // connection-aware IP-filter/rate gate chain, but folding over
        // `braidedDeployment` (the proven forward-auth gate + request-id echo at the
        // head). The composition is proven (`servePipelineOfMetered_braided_off_eq`
        // byte-identical when unmarked, `_fa_denies_status` = 401,
        // `_rid_echoes`). Unset ⇒ the config-driven default metered fold runs
        // unchanged (`servePipelineOfMetered_default` anchor intact).
        let mut resp = if crate::config::braid_enabled() {
            match gw.call_metered_braided(&req, meter, &reply_tx, &reply_rx) {
                Some(r) => r,
                None => return, // serve thread gone (shutdown)
            }
        } else {
            let active_cfg = crate::config::get();
            // The seam scans the config text for the middleware POLICY (max-body-size /
            // allow-method / allow-host) AND the route table. Use the parsed config's
            // text when a valid route config is in force, else the boot-cached RAW bytes
            // (so a policy-only config the route grammar does not model still enforces
            // its policy). No config ⇒ empty ⇒ byte-identical default.
            let raw;
            let cfg_bytes: &[u8] = match active_cfg.as_ref() {
                Some(d) => d.config_text.as_slice(),
                None => {
                    raw = crate::config::raw_text();
                    &raw
                }
            };
            match gw.call_metered_cfg(cfg_bytes, &req, meter, &reply_tx, &reply_rx) {
                Some(r) => r,
                None => return, // serve thread gone (shutdown)
            }
        };

        // REAL GZIP SEAM (`DRORB_RUST_GZIP=1`): replace the proven stored-block gzip
        // stage's (uncompressed) body with real flate2 DEFLATE before framing. Keyed on
        // the response's own `Content-Encoding: gzip`; inert when the flag is unset or
        // the response was not gzipped. Runs BEFORE keepalive detection so the rewritten
        // Content-Length is what decides self-delimitation. (Trusted, not verified.)
        if crate::gzip::enabled() {
            crate::gzip::recompress(&mut resp);
        }
        let keepalive = keepalive_req && response_is_self_delimited(&resp);
        annotate_connection(&mut resp, keepalive);
        emit(&resp, None);
        if stream.write_all(&resp).is_err() {
            return;
        }
        if !keepalive {
            return;
        }
        continue 'conn; // serve the next request (pipelined bytes already buffered)
    }
}

/// The open-connection WebSocket frame loop. After the 101 handshake, every
/// inbound chunk of frame bytes is handed to the proven `Seam::WsFrame`
/// (`drorb_serve_ws_frame`: decode + unmask + reassemble + re-encode) and the
/// proven response bytes are written straight back — a proven-path echo over one
/// kept-open TCP connection. Any bytes the client pipelined right after the
/// upgrade (already in `acc`) are fed first. Returns when the peer closes or on
/// error.
///
/// Each chunk is fed to a fresh WebSocket codec (the proven `drorbServeWsFrame`
/// starts from `{}` per call), so a frame must arrive whole in one recv — true
/// for the small client frames this demo drives over loopback, and the same
/// scheduling choice the C shell (`ffi/mac_io.c`) makes. Cross-recv partial-frame
/// buffering would carry the codec across calls; it is a host scheduling change,
/// not a change to the proven decoder.
fn ws_frame_loop(
    stream: &mut TcpStream,
    gw: &ServeGateway,
    reply_tx: &std::sync::mpsc::Sender<PooledBuf>,
    reply_rx: &std::sync::mpsc::Receiver<PooledBuf>,
    acc: &mut PooledBuf,
) {
    // Frames may sit idle on an open WebSocket; block indefinitely between them.
    let _ = stream.set_read_timeout(None);

    // Feed any bytes pipelined right after the upgrade request.
    if !acc.is_empty() {
        let mut req = gw.pool().take();
        req.extend_from_slice(acc);
        acc.clear();
        match gw.call_seam(req, Seam::WsFrame, reply_tx, reply_rx) {
            Some(out) if !out.is_empty() => {
                if stream.write_all(&out).is_err() {
                    return;
                }
            }
            Some(_) => {}
            None => return,
        }
    }

    let mut chunk = [0u8; 65536];
    loop {
        let n = match stream.read(&mut chunk) {
            Ok(0) => return, // peer closed
            Ok(n) => n,
            Err(_) => return,
        };
        let mut req = gw.pool().take();
        req.extend_from_slice(&chunk[..n]);
        match gw.call_seam(req, Seam::WsFrame, reply_tx, reply_rx) {
            Some(out) if !out.is_empty() => {
                if stream.write_all(&out).is_err() {
                    return;
                }
            }
            Some(_) => {}   // control/incomplete frame produced no echo bytes
            None => return, // serve thread gone
        }
    }
}

/// Run the blocking accept loop on `listener` until shutdown, driving every
/// request through `gw`.
pub fn run(listener: TcpListener, gw: ServeGateway) {
    // Non-blocking accept so the SIGINT flag is observed promptly.
    listener
        .set_nonblocking(true)
        .expect("failed to set the listener non-blocking");

    let gw = Arc::new(gw);
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping accept loop");
            break;
        }
        match listener.accept() {
            Ok((mut stream, peer)) => {
                if crate::ACTIVE_CONNS.load(Ordering::SeqCst) >= MAX_CONNS {
                    drop(stream); // at the soft cap: refuse by closing immediately
                    continue;
                }
                // REACTOR-LEVEL per-source connection-limit gate. The check-and-count
                // is atomic per source (`admit`), so a source at/over its cap is
                // refused the REAL 503 and closed WITHOUT spawning a serve — the
                // proven `Reactor.Stage.ConnLimit` decision on accept-path standing
                // state. `cap == 0` (directive absent) admits every source (unchanged).
                let ip = peer.ip();
                let cap = crate::config::max_connections();
                if !source_table().admit(ip, cap) {
                    let _ = stream.write_all(CONN_LIMIT_503); // best-effort 503
                    let _ = stream.flush();
                    drop(stream); // decrement not needed: admit did not increment
                    continue;
                }
                // REACTOR-LEVEL per-source REQUEST-RATE gate — note this arrival; over
                // the `rate-limit` window ⇒ the REAL 429, closed WITHOUT spawning a
                // serve (`rate_limit_fires`). The `admit` above already incremented the
                // connection counter, so decrement here (`on_close`) to keep it exact.
                if source_table().rate_note(
                    ip,
                    crate::config::rate_limit(),
                    crate::config::rate_window(),
                    std::time::Instant::now(),
                ) {
                    let _ = stream.write_all(RATE_LIMIT_429); // best-effort 429
                    let _ = stream.flush();
                    drop(stream);
                    source_table().on_close(ip);
                    continue;
                }
                crate::ACTIVE_CONNS.fetch_add(1, Ordering::SeqCst);
                let gw = Arc::clone(&gw);
                let _ = std::thread::Builder::new()
                    .name("drorb-conn".into())
                    .spawn(move || {
                        handle_conn(stream, &gw);
                        // Decrement the per-source counter EXACTLY ONCE when this
                        // connection's worker returns (matches the `admit` increment).
                        source_table().on_close(ip);
                        crate::ACTIVE_CONNS.fetch_sub(1, Ordering::SeqCst);
                    });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(_) => {
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
}
