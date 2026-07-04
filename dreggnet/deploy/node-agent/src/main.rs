//! `node-agent` — the DreggNet compute-backend bridge agent.
//!
//! This is the runnable server that sits at the far end of the mesh dispatch path
//! ([`dreggnet_control::dispatch_lease_over_mesh`], `control/src/mesh.rs`): the
//! edge control plane connects to a fleet node over the headscale/WireGuard
//! overlay and `POST`s a funded lease to `http://<overlay-addr>:8021/fulfill`.
//! This binary is what answers that POST on the compute node — it runs the lease as a
//! **real durable metered workflow** via [`dreggnet_bridge::fulfill`] and returns
//! the metered result.
//!
//! It binds `0.0.0.0:8021` (`DEFAULT_AGENT_PORT`) so it is reachable both on the
//! overlay address (edge dispatch) and on loopback (local dogfood).
//!
//! ## Routes
//!
//! - `GET  /health`  — liveness for the mesh health-check leg. `200 ok`.
//! - `POST /fulfill` — body is a JSON lease descriptor; runs it and returns the
//!   metered [`dreggnet_bridge::DurableOutput`] as JSON.
//!
//! ### `/fulfill` request body
//!
//! ```json
//! {
//!   "lessee": "agent-mesh",
//!   "cap_grade": "sandboxed",      // sandboxed | caged | microvm  (default sandboxed)
//!   "asset": "USD-mesh",           // default "USD-mesh"
//!   "budget_units": 100,            // default 100
//!   "per_period_units": 1,          // default 1
//!   "instance": "wl-1"             // default a generated id
//! }
//! ```
//!
//! An empty body / `{}` runs the default add(40,2)→×2 dogfood lease, so
//! `curl -X POST :8021/fulfill -d '{}'` is the smoke test.
//!
//! ### `/fulfill` response
//!
//! `200` with `{ "ok": true, lessee, instance, step1, step2, outputs, meter_units }`,
//! or `4xx`/`5xx` with `{ "ok": false, "error": "..." }` if the bridge refuses the
//! lease (unfunded / over-budget / ill-formed) — no work is claimed that the lease
//! did not authorize.

use std::sync::atomic::{AtomicU64, Ordering};

use dreggnet_bridge::{CapGrade, Lease, fulfill};
use serde::{Deserialize, Serialize};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

/// The default port the fleet bridge agent listens on, on the overlay — mirrors
/// `dreggnet_control::mesh::DEFAULT_AGENT_PORT`.
const DEFAULT_AGENT_PORT: u16 = 8021;
/// Cap on the request (header block + body) we will read off a connection.
const MAX_REQUEST_BYTES: usize = 256 * 1024;

/// The JSON lease descriptor a `/fulfill` request carries.
#[derive(Debug, Deserialize)]
struct FulfillRequest {
    #[serde(default = "default_lessee")]
    lessee: String,
    #[serde(default)]
    cap_grade: Option<String>,
    #[serde(default = "default_asset")]
    asset: String,
    #[serde(default = "default_budget")]
    budget_units: i64,
    #[serde(default = "default_per_period")]
    per_period_units: i64,
    #[serde(default)]
    instance: Option<String>,
}

fn default_lessee() -> String {
    "agent-mesh".into()
}
fn default_asset() -> String {
    "USD-mesh".into()
}
fn default_budget() -> i64 {
    100
}
fn default_per_period() -> i64 {
    1
}

impl Default for FulfillRequest {
    fn default() -> Self {
        FulfillRequest {
            lessee: default_lessee(),
            cap_grade: None,
            asset: default_asset(),
            budget_units: default_budget(),
            per_period_units: default_per_period(),
            instance: None,
        }
    }
}

/// The metered result returned to the dispatching edge.
#[derive(Debug, Serialize)]
struct FulfillResponse {
    ok: bool,
    lessee: String,
    instance: String,
    step1: String,
    step2: String,
    outputs: Vec<String>,
    meter_units: i64,
}

fn parse_cap_grade(s: &Option<String>) -> Result<CapGrade, String> {
    match s.as_deref() {
        None | Some("sandboxed") => Ok(CapGrade::Sandboxed),
        Some("caged") => Ok(CapGrade::Caged),
        Some("microvm") => Ok(CapGrade::MicroVm),
        Some(other) => Err(format!("unknown cap_grade `{other}`")),
    }
}

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let bind = std::env::var("NODE_AGENT_BIND")
        .unwrap_or_else(|_| format!("0.0.0.0:{DEFAULT_AGENT_PORT}"));
    let listener = TcpListener::bind(&bind).await?;
    eprintln!("node-agent: bridge agent listening on http://{bind}");
    eprintln!("  GET  /health");
    eprintln!("  POST /fulfill   (run a funded lease as a durable metered workflow)");
    eprintln!("  smoke: curl -s -X POST http://{bind}/fulfill -d '{{}}'");

    let counter = std::sync::Arc::new(AtomicU64::new(0));
    loop {
        // A transient `accept` error (a client that vanished mid-handshake, momentary
        // fd-table pressure) must NOT take the whole agent down — the previous `?`
        // propagated such an error out of `main` and exited the process, which under
        // a supervising container reads as "running but serving nothing". Log it
        // loudly and keep accepting: the bind is held for the process lifetime, so the
        // agent stays reachable on the port. (A brief pause avoids a hot loop if the
        // error is persistent, e.g. EMFILE.)
        let (stream, peer) = match listener.accept().await {
            Ok(pair) => pair,
            Err(e) => {
                eprintln!("node-agent: accept error (continuing to serve): {e}");
                tokio::time::sleep(std::time::Duration::from_millis(50)).await;
                continue;
            }
        };
        let counter = counter.clone();
        tokio::spawn(async move {
            if let Err(e) = serve_connection(stream, &counter).await {
                eprintln!("node-agent: connection from {peer} errored: {e}");
            }
        });
    }
}

/// Read one HTTP/1.1 request off `stream`, dispatch it, and write the response.
async fn serve_connection(mut stream: TcpStream, counter: &AtomicU64) -> std::io::Result<()> {
    let mut buf = Vec::with_capacity(8 * 1024);
    let mut tmp = [0u8; 8 * 1024];

    // Read until we have the full header block (\r\n\r\n).
    let header_end = loop {
        if let Some(pos) = find_header_end(&buf) {
            break pos;
        }
        if buf.len() > MAX_REQUEST_BYTES {
            return write_response(&mut stream, 431, "Request Header Fields Too Large", "{}").await;
        }
        let n = stream.read(&mut tmp).await?;
        if n == 0 {
            return Ok(()); // client closed before sending a full request
        }
        buf.extend_from_slice(&tmp[..n]);
    };

    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = head.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let path = parts.next().unwrap_or("");

    // Content-Length-bounded body read.
    let content_len = lines
        .find_map(|l| {
            let (k, v) = l.split_once(':')?;
            if k.trim().eq_ignore_ascii_case("content-length") {
                v.trim().parse::<usize>().ok()
            } else {
                None
            }
        })
        .unwrap_or(0);

    let body_start = header_end + 4;
    while buf.len() < body_start + content_len {
        if buf.len() > MAX_REQUEST_BYTES {
            return write_response(&mut stream, 413, "Payload Too Large", "{}").await;
        }
        let n = stream.read(&mut tmp).await?;
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&tmp[..n]);
    }
    let body = &buf[body_start..(body_start + content_len).min(buf.len())];

    match (method, path) {
        ("GET", "/health") => write_response(&mut stream, 200, "OK", "ok\n").await,
        ("POST", "/fulfill") => {
            let resp = handle_fulfill(body, counter).await;
            match resp {
                Ok(json) => write_json(&mut stream, 200, &json).await,
                Err((code, json)) => write_json(&mut stream, code, &json).await,
            }
        }
        _ => write_response(&mut stream, 404, "Not Found", "not found\n").await,
    }
}

/// Run the lease the request body describes, return the metered result JSON.
async fn handle_fulfill(body: &[u8], counter: &AtomicU64) -> Result<String, (u16, String)> {
    let req: FulfillRequest = if body.iter().all(|b| b.is_ascii_whitespace()) {
        FulfillRequest::default()
    } else {
        serde_json::from_slice(body)
            .map_err(|e| (400, err_json(&format!("bad request body: {e}"))))?
    };

    let grade = parse_cap_grade(&req.cap_grade).map_err(|e| (400, err_json(&e)))?;
    let lease = Lease::funded(
        req.lessee.clone(),
        grade,
        req.asset.clone(),
        req.budget_units,
        req.per_period_units,
    );
    let instance = req.instance.clone().unwrap_or_else(|| {
        let n = counter.fetch_add(1, Ordering::Relaxed);
        format!("mesh-wl-{n}")
    });

    match fulfill(&lease, &instance).await {
        Ok(out) => {
            let resp = FulfillResponse {
                ok: true,
                lessee: req.lessee,
                instance,
                step1: out.step1,
                step2: out.step2,
                outputs: out.outputs,
                meter_units: out.meter_units,
            };
            Ok(serde_json::to_string(&resp).unwrap_or_else(|_| "{}".into()))
        }
        // A refused lease is a 4xx with no claimed work; a runtime fault is 5xx.
        Err(e @ dreggnet_bridge::BridgeError::Unfunded { .. })
        | Err(e @ dreggnet_bridge::BridgeError::IllFormed(_))
        | Err(e @ dreggnet_bridge::BridgeError::GradeBelowFloor { .. })
        | Err(e @ dreggnet_bridge::BridgeError::WorkflowFailed(_)) => {
            Err((402, err_json(&e.to_string())))
        }
        Err(e) => Err((500, err_json(&e.to_string()))),
    }
}

fn err_json(msg: &str) -> String {
    serde_json::json!({ "ok": false, "error": msg }).to_string()
}

fn find_header_end(buf: &[u8]) -> Option<usize> {
    buf.windows(4).position(|w| w == b"\r\n\r\n")
}

async fn write_json(stream: &mut TcpStream, code: u16, json: &str) -> std::io::Result<()> {
    let reason = match code {
        200 => "OK",
        400 => "Bad Request",
        402 => "Payment Required",
        500 => "Internal Server Error",
        _ => "Status",
    };
    let resp = format!(
        "HTTP/1.1 {code} {reason}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{json}",
        json.len()
    );
    stream.write_all(resp.as_bytes()).await?;
    stream.flush().await
}

async fn write_response(
    stream: &mut TcpStream,
    code: u16,
    reason: &str,
    body: &str,
) -> std::io::Result<()> {
    let resp = format!(
        "HTTP/1.1 {code} {reason}\r\nContent-Type: text/plain\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        body.len()
    );
    stream.write_all(resp.as_bytes()).await?;
    stream.flush().await
}
