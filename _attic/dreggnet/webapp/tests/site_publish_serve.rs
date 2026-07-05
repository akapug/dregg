//! The publish→serve round-trip, proven against a real local gateway.
//!
//! This is the headline proof for the static-hosting capability: publish a tiny
//! minisite (an `index.html` + a `style.css`) into a [`SiteRegistry`] as a
//! cap-gated, receipted turn, stand up a real `std::net` HTTP server over that
//! registry (the portable analog of the `example.com` gateway: it resolves the
//! request `Host` to the site cell and serves its content), then `GET` the routes
//! over a real TCP socket and assert the served bytes + content-types match what
//! was published.
//!
//! It exercises the same `SiteRegistry::resolve` path the Linux-only `httpe`
//! gateway adopts (`gateway/src/hosting.rs`), so the round-trip is proven on any
//! host (`cargo test -p dreggnet-webapp`), while the gateway adoption is the
//! cross-built production mount.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::thread;

use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};
use dreggnet_webapp::{HttpMethod, WebRequest, WebResponse};

/// A minimal HTTP/1.1 server over a `SiteRegistry`: reads one request (line +
/// headers, no body needed for GET), resolves it by `Host` against the registry,
/// and writes the response. The portable stand-in for the `example.com` gateway.
fn serve_one(stream: &mut TcpStream, registry: &SiteRegistry) -> std::io::Result<()> {
    let mut buf = Vec::new();
    let mut tmp = [0u8; 1024];
    let header_end = loop {
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos + 4;
        }
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
    };

    let header_block = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = header_block.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/");

    // Pull the Host header (case-insensitive) — the per-site key.
    let host = lines
        .find_map(|l| {
            let (n, v) = l.split_once(':')?;
            n.trim()
                .eq_ignore_ascii_case("host")
                .then(|| v.trim().to_string())
        })
        .unwrap_or_default();

    let resp = match HttpMethod::parse(method) {
        Some(m) => {
            let req = WebRequest::new(m, target, Vec::new());
            registry.resolve(&host, &req)
        }
        None => WebResponse::error(405, "unsupported method"),
    };

    let head = format!(
        "HTTP/1.1 {} OK\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        resp.status,
        resp.content_type,
        resp.body.len(),
    );
    stream.write_all(head.as_bytes())?;
    stream.write_all(&resp.body)?;
    stream.flush()
}

/// One `GET target` with an explicit `Host` over a fresh connection; returns the
/// raw response (head + body).
fn http_get(addr: &str, host: &str, target: &str) -> String {
    let mut stream = TcpStream::connect(addr).expect("connect");
    let req = format!("GET {target} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes()).expect("write");
    let mut out = String::new();
    stream.read_to_string(&mut out).expect("read");
    out
}

#[test]
fn publish_a_minisite_then_serve_it_over_real_tcp() {
    // 1. Publish: a cap-gated, receipted turn writes the site cell.
    let registry = Arc::new(SiteRegistry::new());
    let content = SiteContent::new()
        .with(
            "/index.html",
            "<!doctype html><title>hi</title><h1>published to example.com</h1>",
        )
        .with("/style.css", "h1{color:rebeccapurple}");
    let cap = PublishCap::for_site("agent:ember", "blog");
    let receipt = registry.publish(&cap, "blog", content).expect("publish");
    assert_eq!(receipt.name, "blog");
    assert_eq!(receipt.owner, "agent:ember");
    assert_eq!(receipt.asset_count, 2);
    assert!(!receipt.content_root.is_empty());

    // 2. Stand up the local gateway over the registry.
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let addr = listener.local_addr().expect("addr").to_string();
    let reg = Arc::clone(&registry);
    let server = thread::spawn(move || {
        // Serve exactly the four connections this test opens, then stop.
        for _ in 0..4 {
            let (mut stream, _) = listener.accept().expect("accept");
            let _ = serve_one(&mut stream, &reg);
        }
    });

    // 3. GET the index over `blog.example.com` → the published HTML.
    let index = http_get(&addr, "blog.example.com", "/");
    assert!(index.contains("200 OK"), "index status: {index}");
    assert!(
        index.contains("Content-Type: text/html; charset=utf-8"),
        "index ct: {index}"
    );
    assert!(
        index.contains("published to example.com"),
        "index body: {index}"
    );

    // 4. GET the stylesheet → the published CSS with the right content-type.
    let css = http_get(&addr, "blog.example.com", "/style.css");
    assert!(css.contains("200 OK"), "css status: {css}");
    assert!(
        css.contains("Content-Type: text/css; charset=utf-8"),
        "css ct: {css}"
    );
    assert!(css.contains("rebeccapurple"), "css body: {css}");

    // 5. An unknown site → 404.
    let missing_site = http_get(&addr, "nope.example.com", "/");
    assert!(missing_site.contains("404"), "missing site: {missing_site}");

    // 6. A known site, unknown path → 404.
    let missing_path = http_get(&addr, "blog.example.com", "/missing.html");
    assert!(missing_path.contains("404"), "missing path: {missing_path}");

    server.join().expect("server thread");
}
