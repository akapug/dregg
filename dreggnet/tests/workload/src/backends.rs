//! The compute fleet — loopback `:8021/fulfill` backends that speak the real
//! node-agent contract, budget-gated exactly like the live agent.
//!
//! This is the same mock the offline gauntlet uses (`control/tests/orchestration_loop.rs`),
//! lifted into a reusable fleet builder. A backend stub:
//!   - answers a bare-TCP health probe (the `health_check_all` leg);
//!   - on a `/fulfill` POST, parses the lease budget + per-period rent, runs the
//!     2-step demo meter, and returns `402` (lapse) when the metered cost exceeds
//!     the budget, else `200` with `meter_units`.
//!   - honors a shared "down" flag so a fault can mark it unreachable mid-run.

use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use dreggnet_control::MachineId;
use dreggnet_control::mesh::{MeshKeypair, MeshNode};

/// A handle to one running backend stub: its name, its loopback address, and a
/// flag a fault flips to take it "down" (it then drops every connection).
#[derive(Clone)]
pub struct BackendHandle {
    pub name: String,
    pub addr: SocketAddr,
    pub down: Arc<AtomicBool>,
}

impl BackendHandle {
    /// Take this backend down (a `Fault::BackendDown` / `Partition` injector).
    pub fn take_down(&self) {
        self.down.store(true, Ordering::SeqCst);
    }
    /// Bring it back up (a partition heals).
    pub fn bring_up(&self) {
        self.down.store(false, Ordering::SeqCst);
    }
    /// The mesh node addressing this backend (loopback overlay + the stub's port).
    pub fn mesh_node(&self) -> MeshNode {
        node_at(&self.name, self.addr)
    }
}

/// A mesh node addressed at a concrete loopback `addr` — the stand-in for a
/// backend's tailnet/overlay address, exactly how the mesh live-link tests address
/// a node (`control/tests/orchestration_loop.rs::node_at`).
pub fn node_at(name: &str, addr: SocketAddr) -> MeshNode {
    let ip = match addr.ip() {
        std::net::IpAddr::V4(v4) => v4,
        _ => Ipv4Addr::new(127, 0, 0, 1),
    };
    let mut n = MeshNode::new(
        MachineId(name.into()),
        MeshKeypair::generate().public_base64(),
        "203.0.113.1:51820",
        ip,
    );
    n.agent_port = addr.port();
    n
}

/// Spawn a fleet of `n` budget-aware loopback fulfill backends named
/// `backend-{i}`. Returns their handles (each carries the address + the down flag).
pub async fn spawn_fulfill_fleet(n: usize) -> Vec<BackendHandle> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        out.push(spawn_one(format!("backend-{i}")).await);
    }
    out
}

/// Spawn one backend stub and return its handle.
pub async fn spawn_one(name: String) -> BackendHandle {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    let down = Arc::new(AtomicBool::new(false));
    let down_srv = down.clone();

    tokio::spawn(async move {
        loop {
            let (mut stream, _) = match listener.accept().await {
                Ok(s) => s,
                Err(_) => return,
            };
            // A "down" backend drops every connection (connect may succeed but the
            // request fails) — the loop marks it unhealthy and fails over.
            if down_srv.load(Ordering::SeqCst) {
                drop(stream);
                continue;
            }
            let down_conn = down_srv.clone();
            tokio::spawn(async move {
                let mut buf = Vec::new();
                let mut tmp = [0u8; 4096];
                let header_end = loop {
                    if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                        break pos;
                    }
                    let n = stream.read(&mut tmp).await.unwrap_or(0);
                    if n == 0 {
                        return; // a bare probe (the health-check leg)
                    }
                    buf.extend_from_slice(&tmp[..n]);
                };
                if down_conn.load(Ordering::SeqCst) {
                    return;
                }
                let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                let content_len = head
                    .split("\r\n")
                    .find_map(|l| {
                        let (k, v) = l.split_once(':')?;
                        (k.trim().eq_ignore_ascii_case("content-length"))
                            .then(|| v.trim().parse::<usize>().ok())
                            .flatten()
                    })
                    .unwrap_or(0);
                let body_start = header_end + 4;
                while buf.len() < body_start + content_len {
                    let n = stream.read(&mut tmp).await.unwrap_or(0);
                    if n == 0 {
                        break;
                    }
                    buf.extend_from_slice(&tmp[..n]);
                }
                // Parse the lease the control plane POSTed and run the bridge's
                // budget gate: the metered cost (per-period × steps) must fit budget.
                let body: serde_json::Value =
                    serde_json::from_slice(buf.get(body_start..).unwrap_or(&[]))
                        .unwrap_or_default();
                let budget = body
                    .get("budget_units")
                    .and_then(|v| v.as_i64())
                    .unwrap_or(0);
                let rent = body
                    .get("per_period_units")
                    .and_then(|v| v.as_i64())
                    .unwrap_or(1);
                // The 2-step demo workflow (matches the offline gauntlet's stub).
                let metered = 2 * rent;
                let (status, payload) = if metered > budget {
                    (
                        "402 Payment Required",
                        r#"{"ok":false,"error":"execution-lease exhausted after step1"}"#
                            .to_string(),
                    )
                } else {
                    (
                        "200 OK",
                        serde_json::json!({
                            "ok": true, "step1": "42", "step2": "84",
                            "outputs": ["42", "84"], "meter_units": metered,
                        })
                        .to_string(),
                    )
                };
                let resp = format!(
                    "HTTP/1.1 {status}\r\nContent-Type: application/json\r\n\
                     Content-Length: {}\r\nConnection: close\r\n\r\n{payload}",
                    payload.len()
                );
                let _ = stream.write_all(resp.as_bytes()).await;
                let _ = stream.flush().await;
            });
        }
    });

    BackendHandle { name, addr, down }
}
