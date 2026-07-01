//! A tiny blocking HTTP/1.1 client for aggregating upstream read surfaces.
//!
//! Deliberately dependency-free (no reqwest/hyper): the ops dashboard reaches its
//! upstreams over the compose-internal network in plaintext HTTP, so a short
//! hand-rolled `GET` (with timeouts, `Connection: close`, and de-chunking) is all
//! it needs — and it cross-builds with zero extra closure. The same primitive,
//! over a [`std::os::unix::net::UnixStream`], speaks the Docker Engine API for log
//! tailing (see [`request_unix`]).

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};

/// A parsed HTTP response.
#[derive(Debug, Clone)]
pub struct HttpResponse {
    /// The status code (e.g. 200, 401, 404).
    pub status: u16,
    /// The (de-chunked) response body bytes.
    pub body: Vec<u8>,
    /// Wall time the round-trip took.
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
}

/// `GET url` over plain HTTP with a per-attempt `timeout`, optionally carrying a
/// `Bearer` token. Returns the parsed response, or a human error string.
pub fn http_get(
    url: &str,
    timeout: Duration,
    bearer: Option<&str>,
) -> Result<HttpResponse, String> {
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

    let mut req = format!(
        "GET {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nAccept: application/json, */*\r\nUser-Agent: dreggnet-ops\r\n"
    );
    if let Some(tok) = bearer {
        req.push_str(&format!("Authorization: Bearer {tok}\r\n"));
    }
    req.push_str("\r\n");
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write {host}: {e}"))?;

    let raw = read_to_end(&mut stream)?;
    parse_response(&raw, start.elapsed())
}

/// `POST url` with a request body over plain HTTP (the alert webhook path).
/// Plain HTTP only — like [`http_get`], this carries no TLS closure. Returns the
/// parsed response, or a human error string. Best-effort: callers ignore the body.
pub fn http_post(
    url: &str,
    body: &[u8],
    content_type: &str,
    timeout: Duration,
) -> Result<HttpResponse, String> {
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
        "POST {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nUser-Agent: dreggnet-ops\r\n\r\n",
        body.len()
    );
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write {host}: {e}"))?;
    stream
        .write_all(body)
        .map_err(|e| format!("write body {host}: {e}"))?;

    let raw = read_to_end(&mut stream)?;
    parse_response(&raw, start.elapsed())
}

/// Read everything off a stream until EOF or a hard cap, honoring the read timeout.
fn read_to_end<S: Read>(stream: &mut S) -> Result<Vec<u8>, String> {
    // Cap the response to keep an upstream that streams forever from OOMing the
    // dashboard. The aggregated surfaces return small JSON; a few MB is plenty.
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
            // A read timeout after we already have bytes is a (server kept the
            // socket open) end-of-useful-data; surface what we got.
            Err(e) if !out.is_empty() => {
                let _ = e;
                break;
            }
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
    loop {
        let Some(nl) = find(b, b"\r\n") else { break };
        let size_str = String::from_utf8_lossy(&b[..nl]);
        // The chunk-size line may carry extensions after a ';'.
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
        // Advance past the chunk data + its trailing CRLF.
        let next = data_start + size + 2;
        if next >= b.len() {
            break;
        }
        b = &b[next..];
    }
    out
}

/// Make one request over a unix-domain socket (the Docker Engine API), reading the
/// full HTTP/1.0 response. Returns (status, raw_body_bytes). The Docker log stream
/// framing is de-multiplexed by the caller (see [`crate::docker`]).
#[cfg(unix)]
pub fn request_unix(
    socket_path: &str,
    raw_request: &str,
    timeout: Duration,
) -> Result<HttpResponse, String> {
    use std::os::unix::net::UnixStream;
    let start = Instant::now();
    let mut stream =
        UnixStream::connect(socket_path).map_err(|e| format!("connect {socket_path}: {e}"))?;
    stream.set_read_timeout(Some(timeout)).ok();
    stream.set_write_timeout(Some(timeout)).ok();
    stream
        .write_all(raw_request.as_bytes())
        .map_err(|e| format!("write docker socket: {e}"))?;
    let raw = read_to_end(&mut stream)?;
    parse_response(&raw, start.elapsed())
}

#[cfg(not(unix))]
pub fn request_unix(
    _socket_path: &str,
    _raw_request: &str,
    _timeout: Duration,
) -> Result<HttpResponse, String> {
    Err("unix sockets unavailable on this platform".to_string())
}

/// First index of `needle` in `haystack`.
fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// Split `http://host[:port][/path]` into `(host, port, path)`. Only plain `http`
/// is supported (we aggregate compose-internal services); `https` returns `None`.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_url_variants() {
        assert_eq!(
            parse_http_url("http://dregg-node:8420/status"),
            Some(("dregg-node".into(), 8420, "/status".into()))
        );
        assert_eq!(
            parse_http_url("http://host"),
            Some(("host".into(), 80, "/".into()))
        );
        assert_eq!(parse_http_url("https://x/y"), None);
    }

    #[test]
    fn parse_a_simple_response() {
        let raw = b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 13\r\n\r\n{\"ok\":true}\r\n";
        let r = parse_response(raw, Duration::ZERO).unwrap();
        assert_eq!(r.status, 200);
        assert!(r.text().contains("\"ok\":true"));
    }

    #[test]
    fn dechunks_a_chunked_body() {
        let raw =
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n6\r\n world\r\n0\r\n\r\n";
        let r = parse_response(raw, Duration::ZERO).unwrap();
        assert_eq!(r.status, 200);
        assert_eq!(r.text(), "hello world");
    }

    #[test]
    fn status_line_404_parses() {
        let raw = b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n";
        let r = parse_response(raw, Duration::ZERO).unwrap();
        assert_eq!(r.status, 404);
    }
}
