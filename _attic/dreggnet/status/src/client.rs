//! A tiny dependency-free blocking HTTP/1.1 GET client for the live source.
//!
//! Like `dreggnet-ops`, the status page reaches its upstreams over the
//! compose-internal network in plaintext, so a short hand-rolled `GET` (timeouts,
//! `Connection: close`, de-chunking) is all it needs — and it carries zero TLS
//! closure, so the binary cross-builds trivially. Only used by [`crate::live`]
//! (the reviewed-go path); the tested core is source-agnostic.

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

/// A parsed HTTP response.
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub status: u16,
    pub body: Vec<u8>,
    pub elapsed: Duration,
}

impl HttpResponse {
    /// The body as UTF-8 (lossy).
    pub fn text(&self) -> String {
        String::from_utf8_lossy(&self.body).to_string()
    }
    /// Parse the body as JSON.
    pub fn json(&self) -> Result<serde_json::Value, String> {
        serde_json::from_slice(&self.body).map_err(|e| format!("json decode: {e}"))
    }
    /// Whether the status is 2xx.
    pub fn ok(&self) -> bool {
        (200..300).contains(&self.status)
    }
}

/// `GET url` over plain HTTP with a per-attempt `timeout`.
pub fn http_get(url: &str, timeout: Duration) -> Result<HttpResponse, String> {
    let (host, port, path) = parse_http_url(url).ok_or_else(|| format!("bad url: {url}"))?;
    let start = Instant::now();
    let addr = (host.as_str(), port)
        .to_socket_addrs()
        .map_err(|e| format!("resolve {host}:{port}: {e}"))?
        .next()
        .ok_or_else(|| format!("no address for {host}:{port}"))?;
    let mut stream =
        TcpStream::connect_timeout(&addr, timeout).map_err(|e| format!("connect {addr}: {e}"))?;
    stream.set_read_timeout(Some(timeout)).ok();
    stream.set_write_timeout(Some(timeout)).ok();

    let req = format!(
        "GET {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nAccept: application/json, */*\r\nUser-Agent: dreggnet-status\r\n\r\n"
    );
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write {host}: {e}"))?;

    let raw = read_to_end(&mut stream)?;
    parse_response(&raw, start.elapsed())
}

/// Read everything off a stream until EOF or a hard cap.
fn read_to_end<S: Read>(stream: &mut S) -> Result<Vec<u8>, String> {
    const CAP: usize = 8 * 1024 * 1024;
    let mut out = Vec::with_capacity(16 * 1024);
    let mut tmp = [0u8; 16 * 1024];
    loop {
        match stream.read(&mut tmp) {
            Ok(0) => break,
            Ok(n) => {
                out.extend_from_slice(&tmp[..n]);
                if out.len() > CAP {
                    break;
                }
            }
            Err(_) if !out.is_empty() => break,
            Err(e) => return Err(format!("read: {e}")),
        }
    }
    Ok(out)
}

/// Split a raw HTTP response into (status, de-chunked body).
fn parse_response(raw: &[u8], elapsed: Duration) -> Result<HttpResponse, String> {
    let split = find(raw, b"\r\n\r\n").ok_or("no header terminator in response")?;
    let head = &raw[..split];
    let body = &raw[split + 4..];

    let head_text = String::from_utf8_lossy(head);
    let mut lines = head_text.split("\r\n");
    let status_line = lines.next().unwrap_or("");
    let status = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|c| c.parse::<u16>().ok())
        .ok_or_else(|| format!("bad status line: {status_line}"))?;

    let chunked = lines.any(|l| {
        l.split_once(':')
            .map(|(k, v)| {
                k.trim().eq_ignore_ascii_case("transfer-encoding")
                    && v.to_ascii_lowercase().contains("chunked")
            })
            .unwrap_or(false)
    });

    let body = if chunked {
        dechunk(body)
    } else {
        body.to_vec()
    };
    Ok(HttpResponse {
        status,
        body,
        elapsed,
    })
}

/// Decode an HTTP/1.1 `Transfer-Encoding: chunked` body.
fn dechunk(mut b: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(b.len());
    while let Some(nl) = find(b, b"\r\n") {
        let size_str = String::from_utf8_lossy(&b[..nl]);
        let hexpart = size_str.split(';').next().unwrap_or("").trim();
        let Ok(size) = usize::from_str_radix(hexpart, 16) else {
            break;
        };
        let data_start = nl + 2;
        if size == 0 {
            break;
        }
        if data_start + size > b.len() {
            out.extend_from_slice(&b[data_start..]);
            break;
        }
        out.extend_from_slice(&b[data_start..data_start + size]);
        let next = data_start + size + 2;
        if next >= b.len() {
            break;
        }
        b = &b[next..];
    }
    out
}

/// First index of `needle` in `haystack`.
fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// Split `http://host[:port][/path]` into `(host, port, path)`. Plain `http` only.
pub fn parse_http_url(url: &str) -> Option<(String, u16, String)> {
    let rest = url.strip_prefix("http://")?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (h.to_string(), p.parse().ok()?),
        None => (authority.to_string(), 80),
    };
    if host.is_empty() {
        return None;
    }
    Some((host, port, path.to_string()))
}

/// Sum a Prometheus counter family (matching `metric` ignoring labels) from
/// exposition text. Returns `None` if the series is absent.
pub fn prom_sum(text: &str, metric: &str) -> Option<f64> {
    let mut found = false;
    let mut sum = 0.0;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((name_and_labels, value)) = line.rsplit_once(' ') else {
            continue;
        };
        let name = name_and_labels.split('{').next().unwrap_or("").trim();
        if name != metric {
            continue;
        }
        if let Ok(v) = value.trim().parse::<f64>() {
            sum += v;
            found = true;
        }
    }
    if found { Some(sum) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_url_variants() {
        assert_eq!(
            parse_http_url("http://dregg-node:8420/status"),
            Some(("dregg-node".into(), 8420, "/status".into()))
        );
        assert_eq!(parse_http_url("https://x/y"), None);
    }

    #[test]
    fn parses_response_and_dechunks() {
        let raw = b"HTTP/1.1 200 OK\r\nContent-Length: 11\r\n\r\n{\"ok\":true}";
        let r = parse_response(raw, Duration::ZERO).unwrap();
        assert_eq!(r.status, 200);
        assert!(r.ok());
        let chunked =
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n";
        assert_eq!(
            parse_response(chunked, Duration::ZERO).unwrap().text(),
            "hello world"
        );
    }

    #[test]
    fn prom_sum_adds_label_families() {
        let text = "dregg_consensus_differential_divergence_total{a=\"1\"} 2\n\
                    dregg_consensus_differential_divergence_total{a=\"2\"} 1\n";
        assert_eq!(
            prom_sum(text, "dregg_consensus_differential_divergence_total"),
            Some(3.0)
        );
        assert_eq!(prom_sum(text, "nope"), None);
    }
}
