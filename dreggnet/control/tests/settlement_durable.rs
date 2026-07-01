//! LEASE-3 (CRITICAL) — a settler **restart** must NOT double-charge.
//!
//! The settlement dedup was in-memory only, so a restarted settler re-settled
//! every `(lease, period)` it was handed again — each as a fresh real on-chain
//! `Transfer`. This drives the real [`NodeApiSettlement`] over a stub dregg node
//! that COUNTS submitted turns, with a [`DurableSettleLedger`] persisted to a temp
//! file, and proves:
//!
//! 1. settling a period submits exactly one Transfer;
//! 2. a **restart** (a brand-new settlement instance with an empty in-memory map,
//!    sharing the same durable ledger path) re-settling the SAME `(lease, period)`
//!    submits **no** second transfer — the durable dedup replays it;
//! 3. a NEW period after the restart still settles (the ledger blocks replays, not
//!    progress).

use std::io::{Read, Write};
use std::net::TcpListener;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use dreggnet_control::{DurableSettleLedger, LeaseCharge, NodeApiSettlement, Settlement};

/// A 64-char hex cell id with every byte = `b`.
fn cell_id(b: u8) -> String {
    std::iter::repeat_n(format!("{b:02x}"), 32).collect()
}

fn temp_ledger_path(tag: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-settle-durable-{tag}-{nanos}.jsonl"));
    p
}

/// A stub dregg node counting `POST /api/turns/submit` (the on-chain Transfers),
/// and answering `GET /api/cell/{id}` for the post-transfer balance read. Returns
/// its `host:port` and the shared submit counter.
fn spawn_counting_node() -> (String, Arc<AtomicUsize>) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let host_port = format!("127.0.0.1:{}", listener.local_addr().unwrap().port());
    let submits = Arc::new(AtomicUsize::new(0));
    let counter = submits.clone();
    let detail = serde_json::json!({
        "id": cell_id(0xab), "found": true, "has_program": false,
        "balance": 4900, "token_id": cell_id(0x01), "fields": [],
    })
    .to_string();
    let submit = serde_json::json!({ "accepted": true, "turn_hash": "feedface" }).to_string();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { return };
            let mut buf = [0u8; 8192];
            let n = stream.read(&mut buf).unwrap_or(0);
            let req = String::from_utf8_lossy(&buf[..n]).to_string();
            let first = req.lines().next().unwrap_or("").to_string();
            let body = if first.starts_with("POST /api/turns/submit") {
                counter.fetch_add(1, Ordering::SeqCst);
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
    (host_port, submits)
}

#[test]
fn a_settler_restart_does_not_double_charge() {
    let (node, submits) = spawn_counting_node();
    let lessee = cell_id(0xab);
    let backend = cell_id(0x07);
    let ledger_path = temp_ledger_path("restart");

    let charge = LeaseCharge::new(&lessee, &backend, cell_id(0x01), "lease-x", 1, 100);

    // First settler instance — settles (lease-x, 1): exactly one Transfer hits the node.
    {
        let ledger = Arc::new(DurableSettleLedger::open(&ledger_path).unwrap());
        let settlement =
            NodeApiSettlement::new(&node, "operator-bearer").with_durable_ledger(ledger);
        let receipt = settlement.settle(&charge).expect("first settle");
        assert!(!receipt.replayed);
        assert_eq!(submits.load(Ordering::SeqCst), 1, "one Transfer submitted");
        // Dropped at the end of the block — the in-memory dedup is gone, but the
        // durable ledger on disk remains.
    }

    // RESTART: a brand-new settlement instance, empty in-memory map, sharing the
    // SAME durable ledger path. Re-settling the SAME (lease, period) must NOT submit
    // a second on-chain Transfer — the durable dedup replays it.
    {
        let ledger = Arc::new(DurableSettleLedger::open(&ledger_path).unwrap());
        assert_eq!(ledger.len(), 1, "the restart loaded the prior settlement");
        let settlement =
            NodeApiSettlement::new(&node, "operator-bearer").with_durable_ledger(ledger);

        let replay = settlement.settle(&charge).expect("replay after restart");
        assert!(
            replay.replayed,
            "the restarted settler replays the settled period"
        );
        assert_eq!(
            submits.load(Ordering::SeqCst),
            1,
            "NO second Transfer — the lessee is not double-charged across a restart"
        );

        // A genuinely new period still settles (the ledger blocks replays, not work).
        let p2 = LeaseCharge::new(&lessee, &backend, cell_id(0x01), "lease-x", 2, 100);
        let r2 = settlement.settle(&p2).expect("a new period settles");
        assert!(!r2.replayed);
        assert_eq!(
            submits.load(Ordering::SeqCst),
            2,
            "the new period's Transfer submitted"
        );
        assert_eq!(settlement.settled_total("lease-x"), 200);
    }

    std::fs::remove_file(&ledger_path).ok();
}

/// Without a durable ledger (the in-memory dev path) a single instance is still
/// exactly-once — the regression guard that the in-memory path is unchanged.
#[test]
fn in_memory_dedup_unchanged_without_a_ledger() {
    let (node, submits) = spawn_counting_node();
    let lessee = cell_id(0xab);
    let backend = cell_id(0x07);
    let settlement = NodeApiSettlement::new(&node, "b");
    let charge = LeaseCharge::new(&lessee, &backend, cell_id(0x01), "lease-y", 1, 100);

    assert!(!settlement.settle(&charge).unwrap().replayed);
    assert!(settlement.settle(&charge).unwrap().replayed);
    assert_eq!(
        submits.load(Ordering::SeqCst),
        1,
        "exactly-once within one instance"
    );
}
