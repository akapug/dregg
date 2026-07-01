//! `dreggnet-status` — the serving binary for the public status page.
//!
//! A pure-std thread-per-connection HTTP/1.1 server (the same shape as
//! `dreggnet-ops`) serving the public, no-auth status surface:
//!
//! | Method + path   | Serves                                            |
//! |-----------------|---------------------------------------------------|
//! | `GET /`         | the self-contained HTML status page               |
//! | `GET /status.json` | the machine-readable [`StatusPage`] JSON       |
//! | `GET /healthz`  | the status server's own liveness (for probes)     |
//!
//! No auth — this is the PUBLIC "is the cloud up?" page anyone can check. The
//! source is [`LiveSource`] by default (reading the real health surfaces) or the
//! deterministic healthy fixture when `STATUS_DEMO=1`.
//!
//!   cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-status

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

use dreggnet_status::config::StatusConfig;
use dreggnet_status::live::LiveSource;
use dreggnet_status::source::StatusSource;
use dreggnet_status::{FixtureSource, render, status_page};

const MAX_HEADER_BYTES: usize = 64 * 1024;

fn main() -> std::io::Result<()> {
    let mut cfg = StatusConfig::from_env();
    let args: Vec<String> = std::env::args().collect();
    if let Some(bind) = parse_bind(&args) {
        cfg.bind = bind;
    }

    let source: Arc<dyn StatusSource> = if cfg.live {
        Arc::new(LiveSource::new(cfg.clone()))
    } else {
        Arc::new(FixtureSource::healthy())
    };
    let bind = cfg.bind.clone();

    let listener = TcpListener::bind(&bind)?;
    eprintln!("dreggnet-status: serving the public status page on http://{bind}");
    eprintln!(
        "  source:  {}",
        if cfg.live {
            "live"
        } else {
            "fixture (STATUS_DEMO)"
        }
    );
    if cfg.live {
        eprintln!("  node:    {}", cfg.node_url);
        eprintln!(
            "  gateway: {}",
            cfg.gateway_url.as_deref().unwrap_or("(not probed)")
        );
        eprintln!(
            "  control: {}",
            cfg.control_url.as_deref().unwrap_or("(not probed)")
        );
        eprintln!(
            "  bridge:  {}",
            cfg.bridge_url.as_deref().unwrap_or("(not probed)")
        );
        eprintln!(
            "  economy: {}",
            cfg.economy_url.as_deref().unwrap_or("(not probed)")
        );
    }

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let source = Arc::clone(&source);
                std::thread::spawn(move || {
                    if let Err(e) = serve(stream, source.as_ref()) {
                        eprintln!("dreggnet-status: connection error: {e}");
                    }
                });
            }
            Err(e) => eprintln!("dreggnet-status: accept error: {e}"),
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
        port.unwrap_or(8095)
    ))
}

/// Serve one connection: read the request line, route, write, close.
fn serve(mut stream: TcpStream, source: &dyn StatusSource) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(15))).ok();

    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 4096];
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
            br#"{"ok":true,"service":"dreggnet-status"}"#,
        );
    }

    if method != "GET" {
        return write_resp(&mut stream, 405, "text/plain", b"method not allowed");
    }

    match path {
        "/" | "/index.html" => {
            let page = status_page(source);
            write_resp(
                &mut stream,
                200,
                "text/html; charset=utf-8",
                render::page_html(&page).as_bytes(),
            )
        }
        "/status.json" => {
            let page = status_page(source);
            let body = serde_json::to_vec(&page).unwrap_or_default();
            write_resp(&mut stream, 200, "application/json", &body)
        }
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
         Access-Control-Allow-Origin: *\r\n\
         Cache-Control: no-store\r\n\
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
        assert_eq!(parse_bind(&["status".into()]), None);
        assert_eq!(
            parse_bind(&["status".into(), "--port".into(), "9000".into()]),
            Some("0.0.0.0:9000".into())
        );
    }
}
