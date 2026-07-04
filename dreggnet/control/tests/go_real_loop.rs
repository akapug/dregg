//! GO-REAL end-to-end: the orchestration loop driven entirely over the real
//! node-API wire — funded leases READ from a live dregg node's HTTP API and
//! metered work SETTLED as real conserving `Transfer` turns submitted back to it.
//!
//! This is the integration that proves the flip: the same [`Orchestrator`] loop
//! the unit tests drive over the in-memory twins ([`ChannelLeaseSource`] +
//! [`ConservingLedger`]) here runs over [`NodeApiLeaseSource`] +
//! [`NodeApiSettlement`] instead. A stub dregg node serves the public cell-read
//! endpoints + the submit endpoint (no kernel link — exactly the wire the real
//! node speaks), and a stub compute backend speaks the `:8021/fulfill` contract.
//! One tick: read the lease → dispatch + meter on the backend → settle each
//! period as a real `Transfer` POST → the node records the conserving move.

use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpListener};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use dreggnet_control::fleet::Backend;
use dreggnet_control::mesh::{MeshKeypair, MeshNode, TailscaleMesh};
use dreggnet_control::orchestrator::{LeaseSource, Orchestrator, WorkloadState};
use dreggnet_control::provider::MachineId;
use dreggnet_control::{BackendRegistry, NodeApiLeaseSource, NodeApiSettlement};

/// A 64-char hex cell id with every byte = `b`.
fn cell_id(b: u8) -> String {
    std::iter::repeat_n(format!("{b:02x}"), 32).collect()
}

/// A field-element hex (64 chars) holding `v` as a little-endian i64.
fn i64_field(v: i64) -> String {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&v.to_le_bytes());
    bytes.iter().map(|x| format!("{x:02x}")).collect()
}

/// A node mesh handle addressed at a loopback fulfill stub.
fn node_at(addr: SocketAddr) -> MeshNode {
    let ip = match addr.ip() {
        std::net::IpAddr::V4(v4) => v4,
        _ => Ipv4Addr::new(127, 0, 0, 1),
    };
    let mut n = MeshNode::new(
        MachineId("compute-1".into()),
        MeshKeypair::generate().public_base64(),
        "203.0.113.1:51820",
        ip,
    );
    n.agent_port = addr.port();
    n
}

/// A stub dregg node on its own OS thread serving the three endpoints the loop
/// uses: `GET /api/cells`, `GET /api/cell/{id}`, `POST /api/turns/submit`. Records
/// every submitted turn body. The lease cell carries rent=1 so a 2-output run
/// settles as two period charges.
fn spawn_stub_node(lessee: &str, provider_cell: &str, submits: Arc<Mutex<Vec<String>>>) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let host_port = format!("127.0.0.1:{}", listener.local_addr().unwrap().port());

    let cells = serde_json::json!([
        { "id": lessee, "balance": 5000, "nonce": 0, "has_program": true },
    ])
    .to_string();
    let mut fields = vec!["0".repeat(64); 16];
    fields[2] = i64_field(0); // LAPSED = 0 (active)
    fields[4] = i64_field(1); // RENT = 1 per period
    fields[5] = i64_field(50); // PERIOD
    fields[6] = provider_cell.to_string(); // PROVIDER
    let detail = serde_json::json!({
        "id": lessee, "found": true, "has_program": true,
        "balance": 5000, "token_id": cell_id(0x01), "fields": fields,
    })
    .to_string();
    let submit = serde_json::json!({ "accepted": true, "turn_hash": "feedface" }).to_string();

    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { return };
            let mut buf = [0u8; 16384];
            let n = stream.read(&mut buf).unwrap_or(0);
            let req = String::from_utf8_lossy(&buf[..n]).to_string();
            let first = req.lines().next().unwrap_or("").to_string();
            let body = if first.starts_with("GET /api/cells") {
                cells.clone()
            } else if first.starts_with("POST /api/turns/submit") {
                submits.lock().unwrap().push(req.clone());
                submit.clone()
            } else if first.starts_with("GET /api/cell/") {
                detail.clone()
            } else {
                "{}".to_string()
            };
            let resp = format!(
                "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
                 Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            );
            let _ = stream.write_all(resp.as_bytes());
            let _ = stream.flush();
        }
    });
    host_port
}

/// A loopback `:8021/fulfill` backend (the node-agent contract): returns a
/// 2-output metered run.
async fn spawn_fulfill_stub() -> SocketAddr {
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
                    if let Some(p) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                        break p;
                    }
                    let n = stream.read(&mut tmp).await.unwrap_or(0);
                    if n == 0 {
                        return;
                    }
                    buf.extend_from_slice(&tmp[..n]);
                };
                let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                let clen = head
                    .split("\r\n")
                    .find_map(|l| {
                        let (k, v) = l.split_once(':')?;
                        k.trim()
                            .eq_ignore_ascii_case("content-length")
                            .then(|| v.trim().parse::<usize>().ok())
                            .flatten()
                    })
                    .unwrap_or(0);
                let body_start = header_end + 4;
                while buf.len() < body_start + clen {
                    let n = stream.read(&mut tmp).await.unwrap_or(0);
                    if n == 0 {
                        break;
                    }
                    buf.extend_from_slice(&tmp[..n]);
                }
                let payload = serde_json::json!({
                    "ok": true, "step1": "42", "step2": "84",
                    "outputs": ["42", "84"], "meter_units": 2,
                })
                .to_string();
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
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

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn orchestrator_runs_on_real_node_leases_and_settles_real_transfers() {
    let lessee = cell_id(0xab);
    let provider_cell = cell_id(0x07);
    let submits = Arc::new(Mutex::new(Vec::new()));
    let node_host = spawn_stub_node(&lessee, &provider_cell, submits.clone());

    // The compute backend (the fulfill stub), reached over a live tailscale link.
    let fulfill_addr = spawn_fulfill_stub().await;
    let reg = Arc::new(BackendRegistry::new());
    reg.register(Backend::new("node-a", node_at(fulfill_addr), 4));
    reg.mark_healthy("node-a");

    // The REAL seams: a node-API lease source + a node-API settlement, both over
    // the same node. The backend "node-a" pays into its payable cell.
    let mut source = NodeApiLeaseSource::new(&node_host);
    let settlement = Arc::new(
        NodeApiSettlement::new(&node_host, "operator-bearer").map_backend("node-a", &provider_cell),
    );

    let orch = Orchestrator::new(reg, Arc::new(TailscaleMesh::new()), settlement)
        .with_tick_interval(Duration::from_millis(10))
        .with_health_every(0);

    // ONE tick of the real loop: read the lease from the node, dispatch + meter on
    // the backend, settle each metered period as a real Transfer turn to the node.
    let report = orch.tick(&mut source).await;
    assert_eq!(report.watched, 1, "one funded lease read from the node");
    assert_eq!(report.settled, 1, "the metered work settled");

    let w = orch.workload(&format!("lease-{lessee}")).unwrap();
    match w.state {
        WorkloadState::Settled {
            backend,
            meter_units,
            settled_units,
        } => {
            assert_eq!(backend, "node-a");
            assert_eq!(meter_units, 2);
            assert_eq!(settled_units, 2, "settled total == metered total");
        }
        other => panic!("expected Settled, got {other:?}"),
    }

    // Two real conserving Transfer turns hit the node's submit endpoint, lessee →
    // provider cell, each carrying its exactly-once memo.
    let posts = submits.lock().unwrap().clone();
    assert_eq!(posts.len(), 2, "one Transfer per metered period");
    for (i, post) in posts.iter().enumerate() {
        assert!(post.contains("Authorization: Bearer operator-bearer"));
        assert!(post.contains("\"kind\":\"transfer\""));
        assert!(post.contains(&format!("\"from\":\"{lessee}\"")));
        assert!(post.contains(&format!("\"to\":\"{provider_cell}\"")));
        assert!(post.contains(&format!("dreggnet-settle:lease-{lessee}:{}", i + 1)));
    }

    // A re-poll yields nothing (the lease was already orchestrated) — no double work.
    assert!(source.poll().is_empty());
}
