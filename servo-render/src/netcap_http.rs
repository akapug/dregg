//! **THE CAP-GATED HTTP(S) PROTOCOL HANDLER — the real http(s) byte socket, owned
//! by the embedder through the net-cap gate.**
//!
//! ## What the forbidden-scheme fork unlocked
//!
//! Servo's `net` crate normally blocks an embedder from registering a
//! `ProtocolHandler` for `http`/`https` (`FORBIDDEN_SCHEMES`), so the http(s) byte
//! socket was always servo's internal hyper — the [`netcap_connector`](crate::netcap_connector)
//! could bind only the *connect decision*, never the bytes. The vendored
//! `servo-net` fork (`servo-render/vendor/servo-net`, `[patch.crates-io]`) removes
//! `http`/`https` from `FORBIDDEN_SCHEMES` and makes `scheme_fetch` consult an
//! embedder-registered handler FIRST for those schemes. THIS module is that
//! handler: a real [`ProtocolHandler`](servo::protocol_handler::ProtocolHandler)
//! that owns the http(s) socket and routes it through the cap gate.
//!
//! ## The two teeth, in order (HONEST)
//!
//! 1. **THE CAP, AT THE SOCKET.** [`CapGatedHttpHandler::load`] first runs the
//!    held [`SurfaceCapability`]'s connect decision through the
//!    [`NetcapConnector`](crate::netcap_connector::NetcapConnector) — the SAME
//!    `Netlayer::dial` gate `netcap_connector` proves. A cap-denied origin returns
//!    a `network_error` and **no byte socket is ever opened** (`Netlayer::dial` is
//!    never reached); the page sees the refusal, never the resource. A cap-admitted
//!    origin proceeds to the byte fetch.
//! 2. **THE REAL BYTE SOCKET.** For a cap-admitted `http://` origin the handler
//!    opens a REAL `std::net::TcpStream`, writes a genuine HTTP/1.1 `GET`, reads the
//!    response, splits status/headers/body, and hands servo a [`Response`] with the
//!    body + `Content-Type` — which servo lays out and SWGL rasterizes. This socket
//!    is the EMBEDDER's, opened only after the cap gate admitted the origin — not
//!    servo's hyper.
//!
//! ## The honest sub-ceiling (named, not laundered)
//!
//! The byte leg here speaks plain **`http://`** over a real TCP socket (no TLS).
//! `https://` would need a TLS handshake on this same cap-admitted socket (a
//! `rustls`/`native-tls` client over the `TcpStream`); that is a bounded follow-up,
//! not a new architecture — the cap gate + the interception point are identical.
//! The deliverable (`http://example.com` or a local static http server) exercises
//! the full real path: cap gate → real socket → real bytes → servo layout → SWGL
//! raster → PNG.

#![cfg(feature = "libservo")]

use std::future::Future;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::pin::Pin;
use std::sync::Mutex;
use std::time::Duration;

use servo::protocol_handler::{
    DoneChannel, FetchContext, NetworkError, ProtocolHandler, Request, ResourceFetchTiming,
    Response, ResponseBody,
};
use servo::ServoUrl;

use dregg_captp::netlayer::InProcessNetlayer;
use starbridge_web_surface::SurfaceCapability;

use crate::netcap_connector::{block_on, ConnectOutcome, NetcapConnector};

/// The cap-gated http(s) protocol handler servo's `scheme_fetch` routes http/https
/// through (under the vendored `servo-net` fork). Holds the surface authority + the
/// audited netlayer connector; every load discharges the held cap at the socket.
pub struct CapGatedHttpHandler {
    /// The per-render authority + audited connector, behind a `Mutex` so a SINGLE
    /// handler (registered once on the one-per-process `Servo` engine) can be
    /// re-pointed at a new surface/origin for each render — servo's
    /// `servo_config::opts` is a process `OnceCell`, so only one engine (hence one
    /// registered handler) exists per process; [`reconfigure`](Self::reconfigure)
    /// swaps the held cap + reachable peers before each render.
    active: Mutex<Active>,
    /// The net-cap outcomes this handler produced, newest last — the audit trail the
    /// test reads back to prove WHICH gate an origin hit.
    outcomes: Mutex<Vec<ConnectOutcome>>,
    /// The last fetched URL → its fetched byte length, for the test's status line.
    last_fetch: Mutex<Option<(String, usize)>>,
}

/// The swappable per-render state: the held surface cap + the audited connector
/// over a fabric in which the render's reachable peers have joined.
struct Active {
    surface: SurfaceCapability,
    connector: NetcapConnector<InProcessNetlayer>,
}

fn build_active(surface: SurfaceCapability, seed_origins: &[String]) -> Active {
    use crate::netcap_connector::origin_to_peer;
    use dregg_captp::netlayer::InProcessFabric;
    let fabric = InProcessFabric::new();
    // Our own node (the page's dialer identity) — a fixed id in the keyspace.
    let me = fabric.join([0x5e; 32]);
    for o in seed_origins {
        let _ = fabric.join(origin_to_peer(o));
    }
    Active { surface, connector: NetcapConnector::new(me) }
}

impl CapGatedHttpHandler {
    /// Build the handler for `surface`, over an in-process netlayer fabric in which
    /// the surface's authorized origins' peers have joined (so a cap-admitted origin
    /// dials a reachable peer through the audited netlayer; an unauthorized origin is
    /// refused at the connector before any dial). Mirrors `webview::build_cap_gate`.
    pub fn new(surface: SurfaceCapability, seed_origins: &[String]) -> Self {
        CapGatedHttpHandler {
            active: Mutex::new(build_active(surface, seed_origins)),
            outcomes: Mutex::new(Vec::new()),
            last_fetch: Mutex::new(None),
        }
    }

    /// Re-point this handler at a NEW surface + reachable-peer set for the next
    /// render, and clear the audit trail. Used to drive several pages (different
    /// surfaces) through the ONE per-process engine's ONE registered handler.
    pub fn reconfigure(&self, surface: SurfaceCapability, seed_origins: &[String]) {
        *self.active.lock().unwrap_or_else(|e| e.into_inner()) =
            build_active(surface, seed_origins);
        self.outcomes.lock().unwrap_or_else(|e| e.into_inner()).clear();
        *self.last_fetch.lock().unwrap_or_else(|e| e.into_inner()) = None;
    }

    /// The net-cap outcomes this handler produced, newest last (the audit trail).
    pub fn outcomes(&self) -> Vec<ConnectOutcome> {
        self.outcomes.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// The last (url, fetched-byte-length) this handler served — the test's status line.
    pub fn last_fetch(&self) -> Option<(String, usize)> {
        self.last_fetch.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }
}

impl ProtocolHandler for CapGatedHttpHandler {
    /// Resources served by this handler are directly fetchable (so a same-context
    /// `fetch()` of an http(s) resource also routes through this cap-gated path, not
    /// just a top-level navigation). The top-level navigation always reaches
    /// `scheme_fetch` regardless (RequestMode::Navigate), which is the deliverable.
    fn is_fetchable(&self) -> bool {
        true
    }

    fn load<'a>(
        &'a self,
        request: &'a mut Request,
        _done_chan: &mut DoneChannel,
        _context: &FetchContext,
    ) -> Pin<Box<dyn Future<Output = Response> + Send + 'a>> {
        let url = request.current_url();
        debug_assert!(matches!(url.scheme(), "http" | "https"));
        let origin = url.origin().ascii_serialization();

        // ── TOOTH 1: THE CAP, AT THE SOCKET ──────────────────────────────────────
        // Route the connect decision through the audited netlayer. A cap-denied
        // origin is refused HERE — `Netlayer::dial` is never reached, the byte
        // socket is never opened. The page gets a network error, never the resource.
        // (Under the per-render `active` lock, so a `reconfigure` between renders
        // does not race with an in-flight decision.)
        let outcome = {
            let active = self.active.lock().unwrap_or_else(|e| e.into_inner());
            block_on(active.connector.connect(&active.surface, &origin))
        };
        self.outcomes
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(outcome.clone());

        match outcome {
            ConnectOutcome::RefusedByCap { .. } => {
                // The held cap does not authorize this origin — no byte socket opens.
                return Box::pin(std::future::ready(Response::network_error(
                    NetworkError::LoadCancelled,
                )));
            }
            ConnectOutcome::RefusedByTransport { reason, .. } => {
                // Cap admitted it, but the audited netlayer could not reach the peer —
                // the transport's refusal, distinct from an ambient-socket fallback.
                return Box::pin(std::future::ready(Response::network_error(
                    NetworkError::ResourceLoadError(format!(
                        "net-cap transport could not reach {origin} ({reason})"
                    )),
                )));
            }
            ConnectOutcome::Dialed { .. } => { /* cap admitted + peer reachable — fetch the bytes */ }
        }

        // ── TOOTH 2: THE REAL BYTE SOCKET ────────────────────────────────────────
        // The cap admitted the origin. Open a REAL TCP socket to the http origin and
        // fetch the bytes (plain http; https/TLS is the named sub-ceiling). THIS
        // socket is the embedder's, opened only after the cap gate said yes.
        let fetched = http_get_over_real_socket(&url);
        let timing = ResourceFetchTiming::new(request.timing_type());

        match fetched {
            Ok(HttpFetch { status, content_type, body }) => {
                *self.last_fetch.lock().unwrap_or_else(|e| e.into_inner()) =
                    Some((url.as_str().to_string(), body.len()));
                let mut response = Response::new(url, timing);
                *response.body.lock() = ResponseBody::Done(body);
                if let Ok(ct) = http::header::HeaderValue::from_str(&content_type) {
                    response.headers.insert(http::header::CONTENT_TYPE, ct);
                }
                // A real http status (200/…); default if the line was unparsable.
                response.status =
                    servo::protocol_handler::HttpStatus::new_raw(status, Vec::new());
                Box::pin(std::future::ready(response))
            }
            Err(e) => Box::pin(std::future::ready(Response::network_error(
                NetworkError::ResourceLoadError(format!("cap-gated http fetch failed: {e}")),
            ))),
        }
    }
}

/// A shared handle to a [`CapGatedHttpHandler`] that IS a `ProtocolHandler` —
/// a local newtype over `Arc<CapGatedHttpHandler>` so we can `impl ProtocolHandler`
/// (the orphan rule forbids impl-ing the foreign `ProtocolHandler` on the foreign
/// `Arc` directly). `ProtocolRegistry::register` takes the handler by value
/// (`impl ProtocolHandler + 'static`), so we register a clone of this handle and
/// retain another for audit readback — both share ONE handler (one audit trail).
#[derive(Clone)]
pub struct SharedHttpHandler(pub std::sync::Arc<CapGatedHttpHandler>);

impl SharedHttpHandler {
    /// The shared handler (for audit readback — outcomes, last fetch).
    pub fn handler(&self) -> &CapGatedHttpHandler {
        &self.0
    }
}

impl ProtocolHandler for SharedHttpHandler {
    fn is_fetchable(&self) -> bool {
        self.0.is_fetchable()
    }

    fn load<'a>(
        &'a self,
        request: &'a mut Request,
        done_chan: &mut DoneChannel,
        context: &FetchContext,
    ) -> Pin<Box<dyn Future<Output = Response> + Send + 'a>> {
        self.0.load(request, done_chan, context)
    }
}

/// A fetched http response, split into the pieces servo's `Response` needs.
struct HttpFetch {
    status: u16,
    content_type: String,
    body: Vec<u8>,
}

/// **THE REAL BYTE SOCKET.** A minimal, genuine HTTP/1.1 `GET` over a real
/// `std::net::TcpStream` — no hyper, no servo net stack. Opens the socket to the
/// url's host:port, writes a real request line + headers, reads the whole response,
/// splits the status line / headers / body. Plain `http://` only (the named TLS
/// sub-ceiling). Returns the parsed status, content-type, and body bytes.
fn http_get_over_real_socket(url: &ServoUrl) -> Result<HttpFetch, String> {
    if url.scheme() != "http" {
        return Err(format!(
            "the cap-gated byte socket speaks plain http; '{}' needs the TLS sub-ceiling",
            url.scheme()
        ));
    }
    let host = url.host_str().ok_or_else(|| "no host in url".to_string())?;
    let port = url.port_or_known_default().unwrap_or(80);
    let path = {
        let p = url.path();
        if p.is_empty() { "/".to_string() } else { p.to_string() }
    };

    let addr = format!("{host}:{port}");
    let mut stream = TcpStream::connect(&addr).map_err(|e| format!("connect {addr}: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;

    // A real HTTP/1.1 request. `Connection: close` so the server closes the socket
    // at end-of-body and our read-to-EOF terminates without chunked/keep-alive
    // bookkeeping.
    let req = format!(
        "GET {path} HTTP/1.1\r\n\
         Host: {host}\r\n\
         User-Agent: dregg-servo-render-netcap/0.1\r\n\
         Accept: text/html,*/*\r\n\
         Connection: close\r\n\r\n"
    );
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write request: {e}"))?;
    stream.flush().map_err(|e| e.to_string())?;

    let mut raw = Vec::new();
    stream
        .read_to_end(&mut raw)
        .map_err(|e| format!("read response: {e}"))?;

    // Split head / body at the first CRLFCRLF.
    let sep = b"\r\n\r\n";
    let head_end = raw
        .windows(4)
        .position(|w| w == sep)
        .ok_or_else(|| "no header/body separator in response".to_string())?;
    let head = &raw[..head_end];
    let body = raw[head_end + 4..].to_vec();

    let head_str = String::from_utf8_lossy(head);
    let mut lines = head_str.split("\r\n");
    let status_line = lines.next().unwrap_or("");
    // "HTTP/1.1 200 OK" → 200
    let status = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|c| c.parse::<u16>().ok())
        .unwrap_or(200);

    let mut content_type = "text/html; charset=utf-8".to_string();
    for line in lines {
        if let Some((name, value)) = line.split_once(':') {
            if name.trim().eq_ignore_ascii_case("content-type") {
                content_type = value.trim().to_string();
            }
        }
    }

    Ok(HttpFetch { status, content_type, body })
}
