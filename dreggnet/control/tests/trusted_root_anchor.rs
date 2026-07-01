//! Trusted-root hardening (`CommitBindsMMR`) — the verified read's root is pinned
//! to a FINALIZED checkpoint, not the node's bare `/api/receipts/index/root`.
//!
//! A stub dregg node serves a REAL receipt-index MMR window (built with the same
//! `Blake3Mmr` the node and verifier use) plus a `/checkpoint/latest` whose
//! finality (QC votes) + height the test varies. The [`VerifiedNodeLeaseSource`]
//! is pinned to a [`CheckpointAnchor`] and we assert it:
//!
//! - ACCEPTS the honest log when the node still recognizes the finalized anchor and
//!   the anchored root matches (the binding holds — verified read's root == the
//!   finalized-checkpoint's committed MMR root);
//! - REJECTS (fail-closed, no leases) an UNFINALIZED checkpoint (too few QC votes),
//!   a ROLLED-BACK node (latest checkpoint below the finalized anchor), and a WRONG
//!   anchor root (a node serving a different/forged log).

#![cfg(feature = "dregg-verify")]

use std::io::{Read, Write};
use std::net::TcpListener;

use dregg_query::client::IndexRangeResponse;
use dregg_query::{Blake3Mmr, EffectSummary, Mmr, ReceiptRecord};

use dreggnet_control::{CheckpointAnchor, VerifiedNodeLeaseSource};

fn hex32(b: u8) -> String {
    std::iter::repeat_n(format!("{b:02x}"), 32).collect()
}

/// A 3-receipt log; receipt 1 grants one funded execution-lease. Returns the real
/// MMR root (hex), the log length, and the certified `[0, len-1]` window JSON.
fn fixture() -> (String, u64, String) {
    let specs: [(u8, Option<&str>); 3] = [
        (0x10, None),
        (0x11, Some("exec-lease/caged/USD/500/5")),
        (0x12, None),
    ];
    let mut leaves = Vec::new();
    let mut recs = Vec::new();
    for (i, (seed, grant)) in specs.iter().enumerate() {
        let leaf = [*seed; 32];
        let effects = match grant {
            Some(cap) => vec![EffectSummary::Granted {
                from: hex32(0x07),
                to: hex32(0xab),
                cap: cap.to_string(),
            }],
            None => vec![],
        };
        recs.push(ReceiptRecord {
            chain_index: i as u64,
            receipt_hash: leaf.iter().map(|x| format!("{x:02x}")).collect(),
            height: i as u64 + 1,
            agent: hex32(0x07),
            effects,
        });
        leaves.push(leaf);
    }
    let len = recs.len() as u64;
    let mmr = Mmr::from_values(Blake3Mmr, leaves);
    let root: String = mmr.root().iter().map(|x| format!("{x:02x}")).collect();
    let (_v, opening) = mmr.open_range(0, len - 1);
    let window = serde_json::to_string(&IndexRangeResponse {
        receipts: recs,
        root: root.clone(),
        lo: 0,
        hi: len - 1,
        opening,
    })
    .unwrap();
    (root, len, window)
}

/// A stub node serving the real index window + a `/checkpoint/latest` with the
/// given finality (`qc_votes`) and `height`, and the served index root.
fn spawn_stub(root: String, window: String, cp_height: u64, cp_qc: usize) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let host_port = format!("127.0.0.1:{}", listener.local_addr().unwrap().port());
    let checkpoint =
        serde_json::json!({ "height": cp_height, "epoch": 1, "qc_votes": cp_qc }).to_string();
    let index_root = serde_json::json!({ "root": root, "len": 3 }).to_string();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { return };
            let mut buf = [0u8; 16384];
            let n = stream.read(&mut buf).unwrap_or(0);
            let req = String::from_utf8_lossy(&buf[..n]);
            let first = req.lines().next().unwrap_or("");
            let body = if first.starts_with("GET /checkpoint/latest") {
                checkpoint.clone()
            } else if first.starts_with("GET /api/receipts/index/range") {
                window.clone()
            } else if first.starts_with("GET /api/receipts/index/root") {
                index_root.clone()
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

fn anchor(root: String, len: u64, height: u64, min_qc: usize) -> CheckpointAnchor {
    CheckpointAnchor {
        height,
        len,
        mmr_root: root,
        min_qc_votes: min_qc,
    }
}

#[test]
fn anchored_read_accepts_a_finalized_node_and_decodes_the_lease() {
    let (root, len, window) = fixture();
    // Node's latest checkpoint: finalized (3 QC votes) and at/above the anchor.
    let host = spawn_stub(root.clone(), window, 10, 3);
    let mut source =
        VerifiedNodeLeaseSource::new(&host).with_checkpoint_anchor(anchor(root, len, 10, 3));
    let leases = source
        .read_verified_leases()
        .expect("a finalized node with a matching anchor verifies");
    assert_eq!(leases.len(), 1, "the funded exec-lease decodes");
    assert_eq!(leases[0].lease.budget_units, 500);
}

#[test]
fn anchored_read_rejects_an_unfinalized_checkpoint() {
    let (root, len, window) = fixture();
    // Only 1 QC vote — below the anchor's required 3: not finalized.
    let host = spawn_stub(root.clone(), window, 10, 1);
    let mut source =
        VerifiedNodeLeaseSource::new(&host).with_checkpoint_anchor(anchor(root, len, 10, 3));
    let err = source
        .read_verified_leases()
        .expect_err("an unfinalized checkpoint must fail closed");
    assert!(err.to_string().contains("not finalized"), "got: {err}");
}

#[test]
fn anchored_read_rejects_a_rolled_back_node() {
    let (root, len, window) = fixture();
    // Latest checkpoint height 5 — below the finalized anchor at 10 (a fork rewind).
    let host = spawn_stub(root.clone(), window, 5, 3);
    let mut source =
        VerifiedNodeLeaseSource::new(&host).with_checkpoint_anchor(anchor(root, len, 10, 3));
    let err = source
        .read_verified_leases()
        .expect_err("a rolled-back node must fail closed");
    assert!(err.to_string().contains("rolled back"), "got: {err}");
}

#[test]
fn anchored_read_rejects_a_wrong_anchor_root() {
    let (root, len, window) = fixture();
    let host = spawn_stub(root, window, 10, 3);
    // The anchor pins a DIFFERENT root than the node serves — the binding fails:
    // the verified read's root must equal the finalized-checkpoint's committed root.
    let mut source =
        VerifiedNodeLeaseSource::new(&host).with_checkpoint_anchor(anchor(hex32(0xff), len, 10, 3));
    let err = source
        .read_verified_leases()
        .expect_err("a mismatched anchor root must fail closed");
    assert!(
        err.to_string().contains("!= trusted index root"),
        "got: {err}"
    );
}
