//! Service log tailing over the Docker Engine API (the mounted unix socket).
//!
//! The ops dashboard tails the running DreggNet services' container logs without
//! editing or instrumenting any of them: it speaks the Docker Engine API over
//! `/var/run/docker.sock` (mounted read-only into the ops container), lists the
//! compose containers, and reads `/containers/{id}/logs`. For a non-TTY container
//! the log stream is 8-byte-header multiplexed (stdout/stderr framing); we
//! de-multiplex it back to plain text. Everything degrades gracefully: no socket
//! mounted → the panel reports "logs unavailable", never an error page.

use std::time::Duration;

use serde::Serialize;

use crate::client::{HttpResponse, request_unix};

/// A running container, as the dashboard lists it for the logs picker.
#[derive(Debug, Clone, Serialize)]
pub struct ContainerInfo {
    /// The short container id.
    pub id: String,
    /// The primary container name (leading slash stripped).
    pub name: String,
    /// The image reference.
    pub image: String,
    /// The compose service label, if present.
    pub service: Option<String>,
    /// The human status string (e.g. "Up 2 hours", "Restarting (1) 3s ago").
    pub status: String,
    /// The state (e.g. "running", "restarting", "exited").
    pub state: String,
}

/// List the containers visible to the engine (all, including stopped).
pub fn list_containers(socket: &str, timeout: Duration) -> Result<Vec<ContainerInfo>, String> {
    let req = "GET /v1.41/containers/json?all=1 HTTP/1.0\r\nHost: localhost\r\nAccept: application/json\r\n\r\n";
    let resp = request_unix(socket, req, timeout)?;
    if resp.status != 200 {
        return Err(format!("docker containers: HTTP {}", resp.status));
    }
    let v: serde_json::Value = resp.json()?;
    let arr = v.as_array().ok_or("docker containers: not an array")?;
    let mut out = Vec::with_capacity(arr.len());
    for c in arr {
        let id = c
            .get("Id")
            .and_then(|x| x.as_str())
            .unwrap_or("")
            .chars()
            .take(12)
            .collect::<String>();
        let name = c
            .get("Names")
            .and_then(|n| n.as_array())
            .and_then(|a| a.first())
            .and_then(|s| s.as_str())
            .unwrap_or("")
            .trim_start_matches('/')
            .to_string();
        let image = c
            .get("Image")
            .and_then(|x| x.as_str())
            .unwrap_or("")
            .to_string();
        let service = c
            .get("Labels")
            .and_then(|l| l.get("com.docker.compose.service"))
            .and_then(|x| x.as_str())
            .map(|s| s.to_string());
        let status = c
            .get("Status")
            .and_then(|x| x.as_str())
            .unwrap_or("")
            .to_string();
        let state = c
            .get("State")
            .and_then(|x| x.as_str())
            .unwrap_or("")
            .to_string();
        out.push(ContainerInfo {
            id,
            name,
            image,
            service,
            status,
            state,
        });
    }
    Ok(out)
}

/// Resolve a `query` (a container name / compose-service substring) to a container
/// id, preferring an exact name or service match.
pub fn resolve_container(containers: &[ContainerInfo], query: &str) -> Option<String> {
    let q = query.to_ascii_lowercase();
    containers
        .iter()
        .find(|c| {
            c.name.eq_ignore_ascii_case(query)
                || c.service
                    .as_deref()
                    .map(|s| s.eq_ignore_ascii_case(query))
                    .unwrap_or(false)
        })
        .or_else(|| {
            containers.iter().find(|c| {
                c.name.to_ascii_lowercase().contains(&q)
                    || c.service
                        .as_deref()
                        .map(|s| s.to_ascii_lowercase().contains(&q))
                        .unwrap_or(false)
            })
        })
        .map(|c| c.id.clone())
}

/// Tail the last `tail` log lines of a container by id, returning plain text with
/// timestamps. De-multiplexes the Docker 8-byte stream framing.
pub fn tail_logs(
    socket: &str,
    container_id: &str,
    tail: usize,
    timeout: Duration,
) -> Result<String, String> {
    let req = format!(
        "GET /v1.41/containers/{container_id}/logs?stdout=1&stderr=1&timestamps=1&tail={tail} \
         HTTP/1.0\r\nHost: localhost\r\nAccept: */*\r\n\r\n"
    );
    let resp = request_unix(socket, &req, timeout)?;
    if resp.status != 200 {
        return Err(format!("docker logs: HTTP {}", resp.status));
    }
    Ok(demux(&resp))
}

/// De-multiplex the Docker log stream. A non-TTY stream is a sequence of frames
/// `[stream_type:u8, 0,0,0, size:u32 BE][payload]`; a TTY stream is raw bytes. We
/// detect framing heuristically (first byte is 0/1/2 and the declared size fits)
/// and fall back to raw text otherwise.
fn demux(resp: &HttpResponse) -> String {
    let b = &resp.body;
    if looks_framed(b) {
        let mut out = String::new();
        let mut i = 0;
        while i + 8 <= b.len() {
            let size = u32::from_be_bytes([b[i + 4], b[i + 5], b[i + 6], b[i + 7]]) as usize;
            let start = i + 8;
            let end = (start + size).min(b.len());
            out.push_str(&String::from_utf8_lossy(&b[start..end]));
            i = end;
        }
        out
    } else {
        String::from_utf8_lossy(b).to_string()
    }
}

/// Heuristic: the body starts with a plausible Docker stream frame header.
fn looks_framed(b: &[u8]) -> bool {
    if b.len() < 8 {
        return false;
    }
    let stream_type = b[0];
    let reserved_zero = b[1] == 0 && b[2] == 0 && b[3] == 0;
    let size = u32::from_be_bytes([b[4], b[5], b[6], b[7]]) as usize;
    matches!(stream_type, 0 | 1 | 2) && reserved_zero && size <= b.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn framed_resp(frames: &[(u8, &str)]) -> HttpResponse {
        let mut body = Vec::new();
        for (st, text) in frames {
            body.push(*st);
            body.extend_from_slice(&[0, 0, 0]);
            body.extend_from_slice(&(text.len() as u32).to_be_bytes());
            body.extend_from_slice(text.as_bytes());
        }
        HttpResponse {
            status: 200,
            body,
            elapsed: Duration::ZERO,
        }
    }

    #[test]
    fn demux_framed_stream() {
        let r = framed_resp(&[(1, "out line\n"), (2, "err line\n")]);
        assert_eq!(demux(&r), "out line\nerr line\n");
    }

    #[test]
    fn demux_falls_back_to_raw_when_unframed() {
        let r = HttpResponse {
            status: 200,
            body: b"plain tty text without frames".to_vec(),
            elapsed: Duration::ZERO,
        };
        assert_eq!(demux(&r), "plain tty text without frames");
    }
}
