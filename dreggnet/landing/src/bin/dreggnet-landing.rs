//! `dreggnet-landing` — the serving binary for the public landing page.
//!
//! A pure-std thread-per-connection HTTP/1.1 server (the same shape as
//! `dreggnet-ops` / `-status` / `-console`) serving the public, no-auth front
//! door:
//!
//! | Method + path  | Serves                                            |
//! |----------------|---------------------------------------------------|
//! | `GET /`        | the self-contained HTML landing page              |
//! | `GET /healthz` | the landing server's own liveness (for probes)    |
//!
//! The page links into the public status page + the signed-in console and embeds
//! the live status banner client-side (honest "checking…" until it lands). The
//! live-edge deploy (the Caddy route at the public apex + the real public URLs in
//! `LANDING_*`) is the reviewed-go step.
//!
//!   cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-landing

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

use dreggnet_landing::{LandingConfig, landing_html};

const MAX_HEADER_BYTES: usize = 64 * 1024;

fn main() -> std::io::Result<()> {
    let mut cfg = LandingConfig::from_env();
    let args: Vec<String> = std::env::args().collect();
    if let Some(bind) = parse_bind(&args) {
        cfg.bind = bind;
    }

    // Render once at boot (the page is static for a given config) and serve the
    // bytes; a config change is a redeploy, like the static portal.
    let page = Arc::new(landing_html(&cfg));
    let bind = cfg.bind.clone();

    let listener = TcpListener::bind(&bind)?;
    eprintln!("dreggnet-landing: serving the public landing page on http://{bind}");
    eprintln!("  status:  {}", cfg.status_url);
    eprintln!("  console: {}", cfg.console_url);

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let page = Arc::clone(&page);
                std::thread::spawn(move || {
                    if let Err(e) = serve(stream, &page) {
                        eprintln!("dreggnet-landing: connection error: {e}");
                    }
                });
            }
            Err(e) => eprintln!("dreggnet-landing: accept error: {e}"),
        }
    }
    Ok(())
}

/// Parse `--bind host` / `--port N` into a bind string, if either is present.
fn parse_bind(args: &[String]) -> Option<String> {
    let mut host: Option<String> = None;
    let mut port: Option<u16> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--bind" | "-b" => {
                host = args.get(i + 1).cloned();
                i += 2;
            }
            "--port" | "-p" => {
                port = args.get(i + 1).and_then(|s| s.parse().ok());
                i += 2;
            }
            _ => i += 1,
        }
    }
    if host.is_none() && port.is_none() {
        return None;
    }
    Some(format!(
        "{}:{}",
        host.unwrap_or_else(|| "0.0.0.0".into()),
        port.unwrap_or(8096)
    ))
}

/// Serve one connection: read the request line, route, write, close.
fn serve(mut stream: TcpStream, page: &str) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(15))).ok();

    let mut buf: Vec<u8> = Vec::with_capacity(2048);
    let mut tmp = [0u8; 2048];
    loop {
        if find(&buf, b"\r\n\r\n").is_some() {
            break;
        }
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
        if buf.len() > MAX_HEADER_BYTES {
            return write_resp(&mut stream, 431, "text/plain", b"header too large");
        }
    }

    let head_text = String::from_utf8_lossy(&buf);
    let request_line = head_text.lines().next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/");
    let path = target.split('?').next().unwrap_or("/");

    if path == "/healthz" {
        return write_resp(
            &mut stream,
            200,
            "application/json",
            br#"{"ok":true,"service":"dreggnet-landing"}"#,
        );
    }
    if method != "GET" {
        return write_resp(&mut stream, 405, "text/plain", b"method not allowed");
    }

    match path {
        "/" | "/index.html" => write_resp(
            &mut stream,
            200,
            "text/html; charset=utf-8",
            page.as_bytes(),
        ),
        _ => write_resp(&mut stream, 404, "text/plain", b"not found"),
    }
}

/// Write a full HTTP/1.1 response and close the connection.
fn write_resp(
    stream: &mut TcpStream,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> std::io::Result<()> {
    let reason = match status {
        200 => "OK",
        404 => "Not Found",
        405 => "Method Not Allowed",
        431 => "Request Header Fields Too Large",
        _ => "OK",
    };
    let header = format!(
        "HTTP/1.1 {status} {reason}\r\n\
         Content-Type: {content_type}\r\n\
         Content-Length: {}\r\n\
         Cache-Control: max-age=60\r\n\
         Connection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

/// First index of `needle` in `haystack`.
fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bind_override_parsing() {
        assert_eq!(parse_bind(&["landing".into()]), None);
        assert_eq!(
            parse_bind(&["landing".into(), "--port".into(), "9001".into()]),
            Some("0.0.0.0:9001".into())
        );
    }
}
