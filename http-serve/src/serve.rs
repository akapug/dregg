//! `serve` — the portable `std`-net HTTP/1.1 serving core.
//!
//! Given a handler `Fn(&ServeRequest) -> WebResponse`, [`serve_http`] binds a `std`
//! [`TcpListener`] and serves each connection on its own thread: it parses one
//! HTTP/1.1 request into a [`ServeRequest`] (method, `Host`, target, body, headers),
//! runs the handler, and writes the response. The HTTP/1.1 connection plumbing
//! (header read, request-line + content-length parse, body read, response write) is
//! written ONCE here.
//!
//! Every connection is served under the [`crate::limits`] robustness bounds
//! (`DREGG_HTTP_*`-configurable): per-socket read/write timeouts + a wall-clock
//! request deadline (slow-loris → `408`), a header cap (`431`), a body cap on both
//! sized and `Transfer-Encoding: chunked` bodies (`413`), bounded chunked decoding
//! (malformed framing → `400`), and a [`ConnGate`] ceiling on simultaneously-served
//! connections. A well-behaved client sees the same bytes as before.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

use crate::http::{HttpMethod, WebResponse};
use crate::limits::{
    is_timeout, read_chunked_body, read_sized_body, BodyOutcome, ConnGate, Limits,
};

/// One parsed HTTP/1.1 request the serving core hands to a handler: the parsed
/// method, the `Host` header, the request target, the body, and all headers.
pub struct ServeRequest {
    /// The parsed HTTP method (a request with an unsupported method is answered `405`
    /// before the handler is called, so this is always a method the handler can act on).
    pub method: HttpMethod,
    /// The `Host` header value (empty if absent).
    pub host: String,
    /// The request target (path + query).
    pub target: String,
    /// The request body bytes (read up to `Content-Length`; empty for a bodyless GET).
    pub body: Vec<u8>,
    /// All request header `(name, value)` pairs (name lower-cased), in order — for a
    /// handler that authenticates on a proxy-set header (e.g. `x-dregg-subject`).
    /// Use [`header`](ServeRequest::header), which is duplicate-safe.
    pub headers: Vec<(String, String)>,
}

impl ServeRequest {
    /// The value of header `name` (case-insensitive) IFF it appears EXACTLY ONCE.
    /// Returns `None` for zero or MULTIPLE occurrences — so a client that smuggles a
    /// duplicate identity header (banking on a proxy that appends rather than strips)
    /// gets no value, never the wrong one. The fail-closed default for auth headers.
    pub fn header(&self, name: &str) -> Option<&str> {
        let mut found: Option<&str> = None;
        for (n, v) in &self.headers {
            if n.eq_ignore_ascii_case(name) {
                if found.is_some() {
                    return None; // duplicate — ambiguous, refuse
                }
                found = Some(v.as_str());
            }
        }
        found
    }
}

/// Bind `bind` (e.g. `"127.0.0.1:8080"`) and serve forever — one thread per
/// connection, under [`Limits::from_env`] — dispatching each request through
/// `handler`. Returns only on a fatal bind/accept error.
pub fn serve_http<H>(bind: &str, handler: H) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse + Send + Sync + 'static,
{
    let listener = TcpListener::bind(bind)?;
    serve_on(listener, handler, Limits::from_env())
}

/// The accept loop behind [`serve_http`], on an already-bound listener with
/// explicit [`Limits`]. A [`ConnGate`] permit (`limits.max_connections`) is
/// acquired BEFORE each connection thread spawns and held for the connection's
/// lifetime, so at most `max_connections` connections are ever served at once;
/// excess accepts wait for a slot rather than spawning unboundedly.
pub fn serve_on<H>(listener: TcpListener, handler: H, limits: Limits) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse + Send + Sync + 'static,
{
    let handler = Arc::new(handler);
    let gate = ConnGate::new(limits.max_connections);
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let permit = gate.acquire();
                let handler = Arc::clone(&handler);
                let limits = limits.clone();
                std::thread::spawn(move || {
                    let _permit = permit; // released when this connection finishes
                    if let Err(e) = serve_http_connection_limited(stream, handler.as_ref(), &limits)
                    {
                        eprintln!("http-serve: connection error: {e}");
                    }
                });
            }
            Err(e) => eprintln!("http-serve: accept error: {e}"),
        }
    }
    Ok(())
}

/// Read one HTTP/1.1 request off `stream` under [`Limits::from_env`], parse it into
/// a [`ServeRequest`], run `handler`, and write the response. Public so a caller (or
/// test) can drive a single connection directly. An unsupported method is answered
/// `405` without calling `handler`; an oversized header block `431`; a stalled or
/// slow-trickling peer `408`; an over-cap body `413`; malformed chunked framing `400`.
pub fn serve_http_connection<H>(stream: TcpStream, handler: &H) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse,
{
    serve_http_connection_limited(stream, handler, &Limits::from_env())
}

/// [`serve_http_connection`] with explicit [`Limits`] — the hardened single-request
/// path every connection goes through.
pub fn serve_http_connection_limited<H>(
    mut stream: TcpStream,
    handler: &H,
    limits: &Limits,
) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse,
{
    limits.apply_socket(&stream)?;
    let deadline = limits.deadline_from_now();

    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
            break pos + 4;
        }
        if std::time::Instant::now() >= deadline {
            return write_response(&mut stream, &WebResponse::error(408, "request timed out"));
        }
        let n = match stream.read(&mut tmp) {
            Ok(n) => n,
            Err(e) if is_timeout(&e) => {
                return write_response(&mut stream, &WebResponse::error(408, "request timed out"));
            }
            Err(e) => return Err(e),
        };
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
        if buf.len() > limits.max_header_bytes {
            return write_response(&mut stream, &WebResponse::error(431, "header too large"));
        }
    };

    let header_block = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = header_block.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/").to_string();
    let mut host = String::new();
    let mut content_length = 0usize;
    let mut chunked = false;
    let mut headers: Vec<(String, String)> = Vec::new();
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        let (name, value) = (name.trim(), value.trim());
        if name.eq_ignore_ascii_case("host") {
            host = value.to_string();
        } else if name.eq_ignore_ascii_case("content-length") {
            content_length = value.parse().unwrap_or(0);
        } else if name.eq_ignore_ascii_case("transfer-encoding")
            && value.to_ascii_lowercase().contains("chunked")
        {
            chunked = true;
        }
        headers.push((name.to_ascii_lowercase(), value.to_string()));
    }

    let Some(method) = HttpMethod::parse(method) else {
        return write_response(
            &mut stream,
            &WebResponse::error(405, format!("unsupported method `{method}`")),
        );
    };

    // Read the body under the limits: chunked decoding is bounded, a sized body is
    // capped (a declared oversize is refused before a byte is read), and both honor
    // the request deadline. A bodyless GET is content_length 0.
    let leftover = &buf[header_end..];
    let outcome = if chunked {
        read_chunked_body(&mut stream, leftover, limits.max_body_bytes, deadline)?
    } else {
        read_sized_body(
            &mut stream,
            leftover,
            content_length,
            limits.max_body_bytes,
            deadline,
        )?
    };
    let body = match outcome {
        BodyOutcome::Body(body) => body,
        BodyOutcome::TooLarge => {
            return write_response(&mut stream, &WebResponse::error(413, "body too large"));
        }
        BodyOutcome::Timeout => {
            return write_response(&mut stream, &WebResponse::error(408, "request timed out"));
        }
        BodyOutcome::Malformed => {
            return write_response(
                &mut stream,
                &WebResponse::error(400, "malformed chunked body"),
            );
        }
    };

    let req = ServeRequest {
        method,
        host,
        target,
        body,
        headers,
    };
    let resp = handler(&req);
    write_response(&mut stream, &resp)
}

fn write_response(stream: &mut TcpStream, resp: &WebResponse) -> std::io::Result<()> {
    let head = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        resp.status,
        reason_phrase(resp.status),
        resp.content_type,
        resp.body.len(),
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(&resp.body)?;
    stream.flush()
}

fn reason_phrase(status: u16) -> &'static str {
    match status {
        200 => "OK",
        400 => "Bad Request",
        401 => "Unauthorized",
        402 => "Payment Required",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        408 => "Request Timeout",
        409 => "Conflict",
        413 => "Payload Too Large",
        431 => "Request Header Fields Too Large",
        500 => "Internal Server Error",
        502 => "Bad Gateway",
        _ => "Status",
    }
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::time::Duration;

    /// Bind an ephemeral port and serve exactly one connection through
    /// [`serve_http_connection_limited`] with the given limits; returns the address.
    fn spawn_one<H>(limits: Limits, handler: H) -> std::net::SocketAddr
    where
        H: Fn(&ServeRequest) -> WebResponse + Send + 'static,
    {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().unwrap();
        std::thread::spawn(move || {
            if let Ok((stream, _)) = listener.accept() {
                let _ = serve_http_connection_limited(stream, &handler, &limits);
            }
        });
        addr
    }

    fn echo_len(req: &ServeRequest) -> WebResponse {
        WebResponse::json(format!("{{\"len\":{}}}", req.body.len()).into_bytes())
    }

    // ── the 413 body cap bites: a declared oversize is refused, handler untouched ──
    #[test]
    fn an_oversized_declared_body_is_refused_with_413() {
        let called = Arc::new(AtomicBool::new(false));
        let called2 = Arc::clone(&called);
        let limits = Limits {
            max_body_bytes: 16,
            ..Limits::default()
        };
        let addr = spawn_one(limits, move |req: &ServeRequest| {
            called2.store(true, Ordering::SeqCst);
            echo_len(req)
        });

        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(
            b"POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 100000\r\nConnection: close\r\n\r\nAAAA",
        )
        .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 413"), "status line: {resp}");
        assert!(
            !called.load(Ordering::SeqCst),
            "handler must not run on a refused body"
        );
    }

    // ── the slow-loris guard bites: a stalled partial header is answered 408 ──────
    #[test]
    fn a_slow_loris_partial_header_is_timed_out_with_408() {
        let limits = Limits {
            read_timeout: Duration::from_millis(100),
            write_timeout: Duration::from_millis(1000),
            ..Limits::default()
        };
        let addr = spawn_one(limits, echo_len);

        let mut conn = TcpStream::connect(addr).expect("connect");
        // A partial request line, then silence — never a terminating CRLFCRLF.
        conn.write_all(b"GET / HTTP/1.1\r\nHost: lor").unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 408"), "status line: {resp}");
    }

    // ── the header cap bites: a no-newline flood is answered 431 ──────────────────
    #[test]
    fn a_no_newline_header_flood_is_refused_with_431() {
        let limits = Limits {
            max_header_bytes: 1024,
            ..Limits::default()
        };
        let addr = spawn_one(limits, echo_len);

        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(&[b'A'; 4096]).unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 431"), "status line: {resp}");
    }

    // ── chunked decode is wired AND bounded: legit decodes, over-cap is 413 ───────
    #[test]
    fn a_chunked_body_is_decoded_and_an_over_cap_chunked_body_is_413() {
        let limits = Limits {
            max_body_bytes: 64,
            ..Limits::default()
        };
        let addr = spawn_one(limits.clone(), echo_len);
        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(
            b"POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n",
        )
        .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 200"), "status line: {resp}");
        assert!(resp.contains("\"len\":11"), "decoded chunked body: {resp}");

        // One declared chunk over the cap → 413 before it is buffered.
        let addr = spawn_one(limits, echo_len);
        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(
            b"POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\nff\r\n",
        )
        .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 413"), "status line: {resp}");
    }

    // ── the connection gate bites: serve_on never serves above max_connections ────
    #[test]
    fn serve_on_bounds_live_connections_to_the_gate() {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().unwrap();
        let live = Arc::new(AtomicUsize::new(0));
        let max_seen = Arc::new(AtomicUsize::new(0));
        let (live2, max2) = (Arc::clone(&live), Arc::clone(&max_seen));
        let limits = Limits {
            max_connections: 1,
            ..Limits::default()
        };
        std::thread::spawn(move || {
            let _ = serve_on(
                listener,
                move |req: &ServeRequest| {
                    let now = live2.fetch_add(1, Ordering::SeqCst) + 1;
                    max2.fetch_max(now, Ordering::SeqCst);
                    std::thread::sleep(Duration::from_millis(50));
                    live2.fetch_sub(1, Ordering::SeqCst);
                    echo_len(req)
                },
                limits,
            );
        });

        let clients: Vec<_> = (0..4)
            .map(|_| {
                std::thread::spawn(move || {
                    let mut conn = TcpStream::connect(addr).expect("connect");
                    conn.write_all(b"GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
                        .unwrap();
                    let mut resp = String::new();
                    conn.read_to_string(&mut resp).unwrap();
                    resp
                })
            })
            .collect();
        for c in clients {
            let resp = c.join().unwrap();
            assert!(resp.starts_with("HTTP/1.1 200"), "status line: {resp}");
        }
        assert_eq!(
            max_seen.load(Ordering::SeqCst),
            1,
            "the ConnGate must never admit two live connections"
        );
    }

    /// A genuine local TCP round-trip: bind an ephemeral port, serve one connection
    /// in a thread with a trivial echo handler, and prove a real HTTP POST returns
    /// the handler's response — including the `Host` and a duplicate-safe header read.
    #[test]
    fn serves_a_real_tcp_round_trip() {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().unwrap();
        std::thread::spawn(move || {
            if let Ok((stream, _)) = listener.accept() {
                let _ = serve_http_connection(stream, &|req: &ServeRequest| {
                    let subject = req.header("x-dregg-subject").unwrap_or("anon");
                    WebResponse::json(
                        format!("{{\"host\":\"{}\",\"subject\":\"{subject}\"}}", req.host)
                            .into_bytes(),
                    )
                });
            }
        });

        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(
            b"POST /drive HTTP/1.1\r\nHost: alice.agents.dregg\r\nX-Dregg-Subject: dga1_bob\r\nContent-Length: 2\r\nConnection: close\r\n\r\nhi",
        )
        .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 200"), "status line: {resp}");
        assert!(resp.contains("alice.agents.dregg"), "host echoed: {resp}");
        assert!(resp.contains("dga1_bob"), "subject echoed: {resp}");
    }

    /// A smuggled duplicate identity header reads back `None` (fail-closed).
    #[test]
    fn duplicate_header_is_refused() {
        let req = ServeRequest {
            method: HttpMethod::Post,
            host: "h".into(),
            target: "/".into(),
            body: Vec::new(),
            headers: vec![
                ("x-dregg-subject".into(), "alice".into()),
                ("x-dregg-subject".into(), "mallory".into()),
            ],
        };
        assert_eq!(req.header("x-dregg-subject"), None);
    }
}
