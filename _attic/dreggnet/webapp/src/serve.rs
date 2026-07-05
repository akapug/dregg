//! `serve` — the portable static-site serving loop over a [`SiteRegistry`].
//!
//! A reusable, server-independent realization of static hosting on the verified
//! rail: given a [`SiteRegistry`] of published site cells, [`serve_registry`] binds a
//! `std` [`TcpListener`] and serves each request by resolving its `Host` to the site
//! cell the way the `dregg.works` gateway will (`<name>.dregg.works`), with a no-DNS
//! `Host: <name>` / `/<name>/…` path-prefix fallback for local use.
//!
//! This is the shared core of the `dreggnet-host` binary and the `dreggnet deploy
//! --serve` round-trip: both publish into a registry, then call [`serve_registry`].

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

use crate::hosting::{SiteRegistry, site_name_from_host};
use crate::verify::{SITE_RECEIPT_PATH, SiteReceiptBundle};
use crate::{HttpMethod, WebRequest, WebResponse};

const MAX_HEADER_BYTES: usize = 64 * 1024;

/// One parsed HTTP/1.1 request the portable serving core ([`serve_http`]) hands to a
/// handler: the parsed method, the `Host` header, the request target, and the body.
///
/// This is the single request shape BOTH portable serving front-ends drive through
/// the shared loop — the static [`serve_registry`] (resolves `host`) and the dynamic
/// `dreggnet-serve` binary (serves the `target`+`body` through a owned-sandbox `Router`) —
/// so the HTTP/1.1 connection plumbing (header read, request-line + content-length
/// parse, body read, response write) is written ONCE here rather than copied per
/// front-end.
pub struct ServeRequest {
    /// The parsed HTTP method (a request with an unsupported method is answered `405`
    /// before the handler is called, so this is always a method the handler can act on).
    pub method: HttpMethod,
    /// The `Host` header value (empty if absent) — the static path resolves the site
    /// cell from it; the dynamic path ignores it.
    pub host: String,
    /// The request target (path + query).
    pub target: String,
    /// The request body bytes (read up to `Content-Length`; empty for a bodyless GET).
    pub body: Vec<u8>,
}

/// Bind `bind` (e.g. `"127.0.0.1:8080"`) and serve forever — one thread per
/// connection — dispatching each request through `handler`. The shared portable
/// serving loop: returns only on a fatal bind/accept error.
///
/// This is the de-duplicated core of the two portable serving front-ends:
/// [`serve_registry`] (static minisites over a [`SiteRegistry`]) and the
/// `dreggnet-serve` binary (dynamic agent apps over a owned-sandbox `Router`) both bind
/// through here, supplying only the per-request handler closure. (The Linux-only
/// `httpe` gateway is a SEPARATE serving engine — Elide's `Handler` trait over
/// `elidehttp`, not std `TcpListener` — so it keeps its own loop in
/// `gateway/src/hosting.rs`; all three still share the `SiteRegistry` data plane.)
pub fn serve_http<H>(registry_bind: &str, handler: H) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse + Send + Sync + 'static,
{
    let handler = Arc::new(handler);
    let listener = TcpListener::bind(registry_bind)?;
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let handler = Arc::clone(&handler);
                std::thread::spawn(move || {
                    if let Err(e) = serve_http_connection(stream, handler.as_ref()) {
                        eprintln!("dreggnet serve: connection error: {e}");
                    }
                });
            }
            Err(e) => eprintln!("dreggnet serve: accept error: {e}"),
        }
    }
    Ok(())
}

/// Read one HTTP/1.1 request off `stream`, parse it into a [`ServeRequest`], run
/// `handler`, and write the response. Public so a caller (or test) can drive a single
/// connection directly. An unsupported method is answered `405` without calling
/// `handler`; an oversized header block is answered `431`.
pub fn serve_http_connection<H>(mut stream: TcpStream, handler: &H) -> std::io::Result<()>
where
    H: Fn(&ServeRequest) -> WebResponse,
{
    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
            break pos + 4;
        }
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
        if buf.len() > MAX_HEADER_BYTES {
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
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        if name.trim().eq_ignore_ascii_case("host") {
            host = value.trim().to_string();
        } else if name.trim().eq_ignore_ascii_case("content-length") {
            content_length = value.trim().parse().unwrap_or(0);
        }
    }

    let Some(method) = HttpMethod::parse(method) else {
        return write_response(
            &mut stream,
            &WebResponse::error(405, format!("unsupported method `{method}`")),
        );
    };

    // Read the body up to Content-Length (already-buffered bytes after the header
    // block first, then more from the socket). A bodyless GET is content_length 0.
    let mut body = buf[header_end..].to_vec();
    while body.len() < content_length {
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&tmp[..n]);
    }
    body.truncate(content_length);

    let req = ServeRequest {
        method,
        host,
        target,
        body,
    };
    let resp = handler(&req);
    write_response(&mut stream, &resp)
}

/// Bind `bind` (e.g. `"127.0.0.1:8080"`) and serve `registry` forever — one thread
/// per connection. The static-hosting front-end over the shared [`serve_http`] loop:
/// each request resolves its `Host` to the site cell ([`dispatch`]).
pub fn serve_registry(registry: Arc<SiteRegistry>, bind: &str) -> std::io::Result<()> {
    serve_http(bind, move |req| {
        dispatch(&registry, &req.host, req.method, &req.target)
    })
}

/// Read one HTTP request from `stream`, resolve it against `registry`, and write the
/// response. Public so a caller (or test) can drive a single connection directly — a
/// thin static-hosting binding over [`serve_http_connection`].
pub fn serve_connection(stream: TcpStream, registry: &SiteRegistry) -> std::io::Result<()> {
    serve_http_connection(stream, &|req: &ServeRequest| {
        dispatch(registry, &req.host, req.method, &req.target)
    })
}

/// Resolve a request: by `Host` first (`<name>.dregg.works`, what dregg.works
/// routes); falling back to a `/<name>/…` path prefix for no-DNS local testing.
pub fn dispatch(
    registry: &SiteRegistry,
    host: &str,
    method: HttpMethod,
    target: &str,
) -> WebResponse {
    // The trustless-read intercept: `/.well-known/dregg-receipt.json` returns the
    // site's signed receipt + served content (the SiteReceiptBundle), so a
    // non-witness can re-verify the bytes against the committed root without
    // trusting this host. Resolved before content so it is never shadowed by a 404.
    if let Some(resp) = receipt_response(registry, host, target) {
        return resp;
    }
    // Host-based: the production path.
    if site_name_from_host(host)
        .and_then(|n| registry.get(&n))
        .is_some()
    {
        return registry.resolve(host, &WebRequest::new(method, target, Vec::new()));
    }
    // Path-prefix fallback: `/<name>/rest` → serve site `<name>` at `/rest`.
    let trimmed = target.trim_start_matches('/');
    let (name, rest) = match trimmed.split_once('/') {
        Some((n, r)) => (n, format!("/{r}")),
        None => (trimmed, "/".to_string()),
    };
    if let Some(cell) = registry.get(name) {
        return cell.serve(&WebRequest::new(method, &rest, Vec::new()));
    }
    WebResponse::error(404, format!("no site for host `{host}` or path `{target}`"))
}

/// Resolve a request for the well-known receipt path to the site's
/// [`SiteReceiptBundle`] JSON, or `None` if the request is not for that path. Honors
/// both the host-based (`<name>.dregg.works`) and the `/<name>/…` path-prefix forms.
fn receipt_response(registry: &SiteRegistry, host: &str, target: &str) -> Option<WebResponse> {
    let path = target.split('?').next().unwrap_or(target);
    // Host-based: `<name>.dregg.works` + the exact well-known path.
    if let Some(name) = site_name_from_host(host).filter(|n| registry.get(n).is_some()) {
        if path == SITE_RECEIPT_PATH {
            return Some(bundle_response(registry, &name));
        }
        return None;
    }
    // Path-prefix fallback: `/<name>/.well-known/dregg-receipt.json`.
    let trimmed = path.trim_start_matches('/');
    if let Some((name, rest)) = trimmed.split_once('/') {
        if format!("/{rest}") == SITE_RECEIPT_PATH && registry.get(name).is_some() {
            return Some(bundle_response(registry, name));
        }
    }
    None
}

/// Serialize the site's [`SiteReceiptBundle`] as JSON, or a `404` if the site is
/// unsigned (no re-witnessable receipt to hand out).
fn bundle_response(registry: &SiteRegistry, name: &str) -> WebResponse {
    match registry.site_bundle(name) {
        Some(bundle) => match serde_json::to_vec(&bundle) {
            Ok(body) => WebResponse::json(body),
            Err(e) => WebResponse::error(500, format!("encode receipt bundle: {e}")),
        },
        None => WebResponse::error(
            404,
            format!("site `{name}` has no signed receipt (unsigned/free host)"),
        ),
    }
}

/// Fetch a site's [`SiteReceiptBundle`] from a running server over HTTP — the
/// non-witness read: connect to `addr` (e.g. `127.0.0.1:8080`), `GET` the
/// well-known receipt path with `Host: <host>`, and decode the bundle. `Ok(None)`
/// when the server has no signed receipt for the site (`404`). The caller then
/// re-verifies it with [`crate::verify::verify_site_bundle`], trusting only the
/// owner's pinned key — never this server.
pub fn fetch_site_bundle(addr: &str, host: &str) -> std::io::Result<Option<SiteReceiptBundle>> {
    let mut conn = TcpStream::connect(addr)?;
    let req =
        format!("GET {SITE_RECEIPT_PATH} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\n\r\n");
    conn.write_all(req.as_bytes())?;
    let mut buf = Vec::new();
    conn.read_to_end(&mut buf)?;
    let header_end = find_subslice(&buf, b"\r\n\r\n").ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::InvalidData, "no header terminator")
    })?;
    let head = String::from_utf8_lossy(&buf[..header_end]);
    let status: u16 = head
        .lines()
        .next()
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "no status line"))?;
    if status == 404 {
        return Ok(None);
    }
    if status != 200 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("receipt fetch returned HTTP {status}"),
        ));
    }
    let body = &buf[header_end + 4..];
    let bundle: SiteReceiptBundle = serde_json::from_slice(body).map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("decode bundle: {e}"),
        )
    })?;
    Ok(Some(bundle))
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
        402 => "Payment Required",
        404 => "Not Found",
        405 => "Method Not Allowed",
        431 => "Request Header Fields Too Large",
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
    use crate::hosting::{PublishCap, SiteContent};

    fn registry_with_blog() -> Arc<SiteRegistry> {
        let registry = Arc::new(SiteRegistry::new());
        let content =
            SiteContent::new().with("/index.html", "<h1>hi from blog</h1>".as_bytes().to_vec());
        let cap = PublishCap::for_site("agent:test", "blog");
        registry.publish(&cap, "blog", content).expect("publish");
        registry
    }

    #[test]
    fn dispatch_resolves_by_host() {
        let registry = registry_with_blog();
        let resp = dispatch(&registry, "blog.dregg.works", HttpMethod::Get, "/");
        assert_eq!(resp.status, 200);
        assert!(resp.body_str().contains("hi from blog"));
    }

    #[test]
    fn dispatch_path_prefix_fallback() {
        let registry = registry_with_blog();
        let resp = dispatch(&registry, "", HttpMethod::Get, "/blog/index.html");
        assert_eq!(resp.status, 200);
        assert!(resp.body_str().contains("hi from blog"));
    }

    #[test]
    fn dispatch_unknown_site_is_404() {
        let registry = registry_with_blog();
        let resp = dispatch(&registry, "ghost.dregg.works", HttpMethod::Get, "/");
        assert_eq!(resp.status, 404);
    }

    /// A genuine local TCP round-trip: bind an ephemeral port, serve one connection
    /// in a thread, and prove a real HTTP GET returns the published bytes.
    #[test]
    fn serves_a_real_tcp_round_trip() {
        let registry = registry_with_blog();
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().unwrap();
        let reg = Arc::clone(&registry);
        std::thread::spawn(move || {
            if let Ok((stream, _)) = listener.accept() {
                let _ = serve_connection(stream, &reg);
            }
        });

        let mut conn = TcpStream::connect(addr).expect("connect");
        conn.write_all(b"GET / HTTP/1.1\r\nHost: blog.dregg.works\r\nConnection: close\r\n\r\n")
            .unwrap();
        let mut resp = String::new();
        conn.read_to_string(&mut resp).unwrap();
        assert!(resp.starts_with("HTTP/1.1 200"), "status line: {resp}");
        assert!(resp.contains("hi from blog"), "body: {resp}");
    }
}
