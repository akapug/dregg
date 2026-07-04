//! The autonomous lease-orchestration loop, end to end — the core that makes
//! DreggNet an actual cloud, proven offline against loopback compute backends.
//!
//! One running daemon ([`Orchestrator::run_until_shutdown`]) drives the whole
//! cycle across a multi-backend fleet:
//!
//!   WATCH  — a [`ChannelLeaseSource`] feeds funded leases over time;
//!   SCHEDULE — the [`BackendRegistry`] picks a healthy backend (round-robin), and
//!              FAILS OVER from a dead box to a live one;
//!   DISPATCH — the lease is POSTed to the backend's `:8021/fulfill` bridge agent
//!              over the mesh (the proven node-a path, here loopback stubs);
//!   METER + SETTLE — the metered units are settled lessee → backend as a
//!              conserving, exactly-once transfer (Σδ = 0) on the [`ConservingLedger`];
//!   REAP   — an over-budget lease the backend refuses is reaped, never billed.
//!
//! The compute backend is mocked (a loopback server speaking the node-agent's
//! `/fulfill` contract); the loop, the multi-backend pick/health/failover, the
//! dispatch POST, and the conserving settlement are all real.

use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Arc;
use std::time::Duration;

use dreggnet_control::mesh::{MeshKeypair, MeshNode, TailscaleMesh};
use dreggnet_control::{
    Backend, BackendRegistry, CapGrade, ChannelLeaseSource, ConservingLedger, Lease, Orchestrator,
};
// The orchestrator's lifecycle state (distinct from the provider-scheduler's
// same-named enum re-exported at the crate root).
use dreggnet_control::orchestrator::WorkloadState as OrchState;

/// A mesh node addressed at a concrete loopback `addr` (the stand-in for a backend's
/// tailnet/overlay address — exactly how `mesh`'s live-link tests address a node).
fn node_at(name: &str, addr: SocketAddr) -> MeshNode {
    let ip = match addr.ip() {
        std::net::IpAddr::V4(v4) => v4,
        _ => Ipv4Addr::new(127, 0, 0, 1),
    };
    let mut n = MeshNode::new(
        dreggnet_control::MachineId(name.into()),
        MeshKeypair::generate().public_base64(),
        "203.0.113.1:51820",
        ip,
    );
    n.agent_port = addr.port();
    n
}

/// A node addressed at a port nothing listens on — an unreachable backend.
fn dead_node(name: &str) -> MeshNode {
    let mut n = MeshNode::new(
        dreggnet_control::MachineId(name.into()),
        MeshKeypair::generate().public_base64(),
        "203.0.113.9:51820",
        Ipv4Addr::new(127, 0, 0, 1),
    );
    n.agent_port = 1; // connect refused
    n
}

/// Stand up a loopback server speaking the `:8021/fulfill` contract, **budget-aware**
/// exactly like the real node-a bridge agent: it runs the 2-step demo workflow
/// (`add(40,2)→×2`) and refuses with `402` when the 2 metered ticks would exceed the
/// lease budget (a lapse), else returns the metered success (`meter_units = 2×rent`).
async fn spawn_agent_stub() -> SocketAddr {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move {
        loop {
            let (mut stream, _) = match listener.accept().await {
                Ok(s) => s,
                Err(_) => return,
            };
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
                // 2-step budget gate: both ticks of `rent` must fit the budget.
                let body: serde_json::Value =
                    serde_json::from_slice(&buf[body_start..]).unwrap_or_default();
                let budget = body
                    .get("budget_units")
                    .and_then(|v| v.as_i64())
                    .unwrap_or(0);
                let rent = body
                    .get("per_period_units")
                    .and_then(|v| v.as_i64())
                    .unwrap_or(1);
                let metered = 2 * rent; // the 2-step demo workflow
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
    addr
}

#[tokio::test]
async fn the_loop_watches_dispatches_meters_settles_and_reaps() {
    // ---- The fleet: a dead node box and a live node-a box ----
    let node_a = spawn_agent_stub().await;
    let registry = Arc::new(BackendRegistry::new());
    // The dead box is registered first, so a naive round-robin would hit it first —
    // the loop must fail over to the live box.
    registry.register(Backend::new("node-down", dead_node("node-down"), 2));
    registry.register(Backend::new("node-a", node_at("node-a", node_a), 4));

    // ---- The settlement rail: fund the lessees' lease reserves ----
    let ledger = Arc::new(ConservingLedger::new());
    ledger.fund("USD", "agent-good", 100);
    ledger.fund("USD", "agent-broke", 100);

    let mesh = Arc::new(TailscaleMesh::new());
    let orch = Arc::new(
        Orchestrator::new(registry.clone(), mesh, ledger.clone())
            .with_tick_interval(Duration::from_millis(10))
            // Health-check every tick so the dead box is marked down and the loop
            // schedules onto the live one.
            .with_health_every(1),
    );

    // ---- Run the daemon (a real continuous loop, not a one-shot) ----
    let (tx, source) = ChannelLeaseSource::channel();
    let (stop_tx, stop_rx) = tokio::sync::oneshot::channel::<()>();
    let daemon = {
        let orch = orch.clone();
        tokio::spawn(async move {
            orch.run_until_shutdown(source, async {
                let _ = stop_rx.await;
            })
            .await;
        })
    };

    // A genuinely funded lease (budget covers both metered steps).
    tx.send(
        "wl-good",
        Lease::funded("agent-good", CapGrade::Sandboxed, "USD", 100, 1),
    )
    .unwrap();
    // An over-budget lease (budget 1, needs 2): the backend refuses → lapse → reap.
    tx.send(
        "wl-broke",
        Lease::funded("agent-broke", CapGrade::Sandboxed, "USD", 1, 1),
    )
    .unwrap();

    // Let the daemon run several ticks, then stop + drain.
    tokio::time::sleep(Duration::from_millis(120)).await;
    let _ = stop_tx.send(());
    let _ = tokio::time::timeout(Duration::from_secs(2), daemon).await;

    // ---- The funded lease: scheduled (failed over to node-a), metered, settled ----
    let good = orch.workload("wl-good").expect("tracked");
    match good.state {
        OrchState::Settled {
            backend,
            meter_units,
            settled_units,
        } => {
            assert_eq!(backend, "node-a", "failed over from the dead box to node-a");
            assert_eq!(meter_units, 2);
            assert_eq!(
                settled_units, 2,
                "settled total equals metered total (the fold is coherent)"
            );
        }
        other => panic!("expected the funded lease Settled, got {other:?}"),
    }

    // The conserving transfer moved value lessee → backend, none created/destroyed.
    assert_eq!(ledger.balance("USD", "agent-good"), 98);
    assert_eq!(ledger.balance("USD", "node-a"), 2);
    assert_eq!(
        ledger.total_supply("USD"),
        200,
        "Σδ = 0 across all settlements"
    );

    // ---- The over-budget lease: reaped, never billed ----
    let broke = orch.workload("wl-broke").expect("tracked");
    assert!(
        matches!(broke.state, OrchState::Lapsed(_)),
        "over-budget lease reaped, got {:?}",
        broke.state
    );
    assert_eq!(
        ledger.balance("USD", "agent-broke"),
        100,
        "no unpaid work billed"
    );

    // ---- The fleet: the dead box was marked unhealthy by the health-check/failover ----
    let statuses = registry.statuses();
    let down = statuses.iter().find(|s| s.name == "node-down").unwrap();
    assert!(
        matches!(down.health, dreggnet_control::Health::Unhealthy(_)),
        "the dead backend is marked down"
    );
}
