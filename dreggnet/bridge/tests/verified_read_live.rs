//! Light-client VERIFIED lease read against a live dregg node — the path-B proof.
//!
//! `#[ignore]` by default (it needs a reachable node). Point it at one and run:
//!
//! ```sh
//! DREGGNET_LIVE_NODE=127.0.0.1:18420 \
//!   cargo test -p dreggnet-bridge --features dregg-verify --test verified_read_live -- --ignored --nocapture
//! ```
//!
//! It fetches the node's committed receipt-chain MMR root (`/index/root`) and the
//! certified whole-log slice (`/index/range`), then runs
//! [`dreggnet_bridge::dregg_verify::verified_leases_from_range`] — the genuine
//! light-client verification (non-omission certificate + row recomputation against
//! the trusted root) — over REAL chain data. It asserts the verification ACCEPTS
//! the honest slice, and REJECTS a tampered root (fail-closed).

#![cfg(feature = "dregg-verify")]

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

/// Minimal blocking HTTP/1.1 GET — returns the response body as a string.
fn http_get(host_port: &str, path: &str) -> String {
    let addr = host_port.to_socket_addrs().unwrap().next().unwrap();
    let mut s = TcpStream::connect_timeout(&addr, Duration::from_secs(10)).unwrap();
    s.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
    let req = format!("GET {path} HTTP/1.1\r\nHost: {host_port}\r\nConnection: close\r\n\r\n");
    s.write_all(req.as_bytes()).unwrap();
    let mut raw = Vec::new();
    s.read_to_end(&mut raw).unwrap();
    let sep = raw.windows(4).position(|w| w == b"\r\n\r\n").unwrap();
    String::from_utf8_lossy(&raw[sep + 4..]).to_string()
}

#[test]
#[ignore = "requires a reachable dregg node at DREGGNET_LIVE_NODE"]
fn verified_read_accepts_real_chain_and_rejects_tamper() {
    let node = std::env::var("DREGGNET_LIVE_NODE")
        .expect("set DREGGNET_LIVE_NODE=host:port to run this proof");

    // The committed receipt-chain MMR root (the trusted root).
    let root_body = http_get(&node, "/api/receipts/index/root");
    let root_json: serde_json::Value = serde_json::from_str(&root_body).unwrap();
    let root = root_json["root"].as_str().unwrap().to_string();
    let len = root_json["len"].as_u64().unwrap();
    println!("node index: root={root} len={len}");
    assert!(
        len > 0,
        "the node's receipt index is empty — nothing to verify"
    );

    // The certified whole-log slice [0, len-1] (rows + the non-omission opening).
    let range_body = http_get(
        &node,
        &format!("/api/receipts/index/range?lo=0&hi={}", len - 1),
    );

    // The genuine light-client verification over REAL chain data: it must ACCEPT.
    let leases = dreggnet_bridge::dregg_verify::verified_leases_from_range(&range_body, &root)
        .expect("the honest certified slice must verify against the trusted root");
    println!(
        "verified read OK over real chain data: {} funded execution-lease(s) decoded",
        leases.len()
    );

    // Tamper the trusted root by one nibble — verification must FAIL CLOSED.
    let mut bad = root.clone();
    let first = bad.remove(0);
    bad.insert(0, if first == '0' { '1' } else { '0' });
    let tampered = dreggnet_bridge::dregg_verify::verified_leases_from_range(&range_body, &bad);
    assert!(
        tampered.is_err(),
        "a tampered trusted root must be rejected (fail-closed), got {tampered:?}"
    );
    println!("tampered-root read correctly REJECTED (fail-closed)");
}
