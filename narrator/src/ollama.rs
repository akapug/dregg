//! A tiny, dependency-free Ollama client over `std::net` — no async runtime, no HTTP crate.
//! Ported from the dungeon-service so the hosted-narrator fallback and the local model share
//! one client. POSTs `/api/generate` (`stream:false`) and returns the model's `response` text.
//!
//! This is the honest, no-spend LOCAL fallback: when Bedrock is unavailable or the budget is
//! exhausted, a reachable Ollama keeps narration alive at zero USD cost.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::Duration;

use serde_json::Value;

/// A local Ollama model at `endpoint` (e.g. `http://127.0.0.1:11434`) named `model`.
#[derive(Clone, Debug)]
pub struct OllamaBackend {
    pub endpoint: String,
    pub model: String,
}

/// The default endpoint when `OLLAMA_ENDPOINT` is unset.
pub const DEFAULT_ENDPOINT: &str = "http://127.0.0.1:11434";
/// The default model when `OLLAMA_MODEL` is unset.
pub const DEFAULT_MODEL: &str = "gemma2:2b";

impl OllamaBackend {
    /// The Ollama backend resolved from `OLLAMA_ENDPOINT` / `OLLAMA_MODEL`.
    pub fn from_env() -> OllamaBackend {
        OllamaBackend {
            endpoint: std::env::var("OLLAMA_ENDPOINT")
                .unwrap_or_else(|_| DEFAULT_ENDPOINT.to_string()),
            model: std::env::var("OLLAMA_MODEL").unwrap_or_else(|_| DEFAULT_MODEL.to_string()),
        }
    }

    /// The env-resolved backend, but only if it is REACHABLE (a live `/api/tags` probe). Returns
    /// `None` when Ollama is not running, so `auto()` can skip it cleanly.
    pub fn probe_env() -> Option<OllamaBackend> {
        let b = OllamaBackend::from_env();
        if b.reachable() {
            Some(b)
        } else {
            None
        }
    }

    /// True iff `GET /api/tags` succeeds — a cheap liveness probe.
    pub fn reachable(&self) -> bool {
        http_get(&self.endpoint, "/api/tags").is_ok()
    }

    /// `kind()` string for honest reporting, e.g. `model:gemma2:2b`.
    pub fn kind(&self) -> String {
        format!("model:{}", self.model)
    }

    /// Generate from a single prompt (system + user folded together), returning the model's
    /// `response` text. `stream:false`, temperature 0 for reproducible narration.
    pub fn generate(&self, prompt: &str) -> Result<String, String> {
        let req_body = serde_json::json!({
            "model": self.model,
            "prompt": prompt,
            "stream": false,
            "options": { "temperature": 0 },
        })
        .to_string();
        let raw = http_post(&self.endpoint, "/api/generate", &req_body)?;
        let envelope: Value =
            serde_json::from_str(&raw).map_err(|e| format!("ollama envelope not JSON: {e}"))?;
        envelope
            .get("response")
            .and_then(Value::as_str)
            .map(str::to_string)
            .ok_or_else(|| "ollama reply had no `response` field".to_string())
    }
}

/// A minimal blocking HTTP/1.1 GET over `std::net` (the liveness probe).
fn http_get(endpoint: &str, path: &str) -> Result<String, String> {
    let (host, port) = parse_authority(endpoint)?;
    let addr = format!("{host}:{port}");
    let mut stream = TcpStream::connect(&addr).map_err(|e| format!("connect {addr}: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .map_err(|e| e.to_string())?;
    let req = format!("GET {path} HTTP/1.1\r\nHost: {host}:{port}\r\nConnection: close\r\n\r\n",);
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write: {e}"))?;
    stream.flush().ok();
    let mut buf = Vec::new();
    stream
        .read_to_end(&mut buf)
        .map_err(|e| format!("read: {e}"))?;
    Ok(String::from_utf8_lossy(&buf).into_owned())
}

/// A minimal blocking HTTP/1.1 POST over `std::net`. `Connection: close` so we read to EOF;
/// de-chunks a `Transfer-Encoding: chunked` body.
fn http_post(endpoint: &str, path: &str, body: &str) -> Result<String, String> {
    let (host, port) = parse_authority(endpoint)?;
    let addr = format!("{host}:{port}");
    let mut stream = TcpStream::connect(&addr).map_err(|e| format!("connect {addr}: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(45)))
        .map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(Duration::from_secs(15)))
        .map_err(|e| e.to_string())?;

    let req = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: {host}:{port}\r\n\
         Content-Type: application/json\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\r\n{body}",
        len = body.len(),
    );
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write: {e}"))?;
    stream.flush().ok();

    let mut buf = Vec::new();
    stream
        .read_to_end(&mut buf)
        .map_err(|e| format!("read: {e}"))?;
    let text = String::from_utf8_lossy(&buf).into_owned();

    let split = text
        .find("\r\n\r\n")
        .ok_or_else(|| "no HTTP header terminator in reply".to_string())?;
    let (head, rest) = text.split_at(split);
    let raw_body = &rest[4..];
    if head
        .to_ascii_lowercase()
        .contains("transfer-encoding: chunked")
    {
        Ok(dechunk(raw_body))
    } else {
        Ok(raw_body.to_string())
    }
}

/// Decode an HTTP/1.1 chunked body into the concatenated payload.
fn dechunk(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    loop {
        let Some(nl) = rest.find("\r\n") else { break };
        let size_hex = rest[..nl].trim();
        let size = usize::from_str_radix(size_hex.split(';').next().unwrap_or("0").trim(), 16)
            .unwrap_or(0);
        if size == 0 {
            break;
        }
        let data_start = nl + 2;
        let data_end = (data_start + size).min(rest.len());
        out.push_str(&rest[data_start..data_end]);
        rest = &rest[(data_end + 2).min(rest.len())..];
    }
    out
}

/// Split `http://host:port` (or `host:port`) into `(host, port)`, defaulting port 11434.
fn parse_authority(endpoint: &str) -> Result<(String, u16), String> {
    let e = endpoint
        .trim()
        .trim_start_matches("http://")
        .trim_start_matches("https://")
        .trim_end_matches('/');
    let (host, port) = match e.rsplit_once(':') {
        Some((h, p)) => (
            h.to_string(),
            p.parse::<u16>()
                .map_err(|_| format!("bad port in `{endpoint}`"))?,
        ),
        None => (e.to_string(), 11434),
    };
    if host.is_empty() {
        return Err(format!("no host in `{endpoint}`"));
    }
    Ok((host, port))
}
