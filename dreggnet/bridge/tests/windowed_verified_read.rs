//! Windowed light-client verified read — the long-chain proof.
//!
//! A receipt log longer than the node's single-range span cap (1024 rows) is read
//! as several `/api/receipts/index/range` windows that TILE the log; each window's
//! non-omission certificate verifies against the SAME whole-log MMR root, and the
//! windows must be contiguous and reach the head. This builds a REAL MMR (the same
//! `Blake3Mmr` the node and the verifier use), opens genuine multi-window range
//! certificates over it, and drives [`verified_leases_windowed`] over them —
//! proving it ACCEPTS an honest tiling and REJECTS a skipped window / omitted tail
//! / wrong root (all fail-closed).

#![cfg(feature = "dregg-verify")]

use dregg_query::client::IndexRangeResponse;
use dregg_query::{Blake3Mmr, EffectSummary, Mmr, ReceiptRecord};

/// A 64-char hex cell id with every byte = `b`.
fn hex32(b: u8) -> String {
    std::iter::repeat_n(format!("{b:02x}"), 32).collect()
}

/// A receipt at `chain_index` whose leaf hash is `[seed; 32]`, optionally granting
/// one funded execution-lease (`exec-lease/<grade>/<asset>/<budget>/<rent>`).
fn receipt(chain_index: u64, seed: u8, grant: Option<&str>) -> ([u8; 32], ReceiptRecord) {
    let leaf = [seed; 32];
    let effects = match grant {
        Some(cap) => vec![EffectSummary::Granted {
            from: hex32(0x07),
            to: hex32(0xab),
            cap: cap.to_string(),
        }],
        None => vec![],
    };
    let rec = ReceiptRecord {
        chain_index,
        receipt_hash: leaf.iter().map(|x| format!("{x:02x}")).collect(),
        height: chain_index + 1,
        agent: hex32(0x07),
        effects,
    };
    (leaf, rec)
}

/// One `/api/receipts/index/range?lo=&hi=` body, opened from the real MMR.
fn window_json(mmr: &Mmr<Blake3Mmr>, recs: &[ReceiptRecord], lo: u64, hi: u64) -> String {
    let (_values, opening) = mmr.open_range(lo, hi);
    let resp = IndexRangeResponse {
        receipts: recs[lo as usize..=hi as usize].to_vec(),
        root: mmr.root().iter().map(|x| format!("{x:02x}")).collect(),
        lo,
        hi,
        opening,
    };
    serde_json::to_string(&resp).unwrap()
}

/// Build a 5-receipt log; receipts 1 and 3 grant funded execution-leases.
fn fixture() -> (Mmr<Blake3Mmr>, Vec<ReceiptRecord>, String) {
    let specs: [(u8, Option<&str>); 5] = [
        (0x10, None),
        (0x11, Some("exec-lease/caged/USD/500/5")),
        (0x12, Some("tool-call")), // not an exec-lease — filtered
        (0x13, Some("exec-lease/sandboxed/USD/200/2")),
        (0x14, None),
    ];
    let mut leaves = Vec::new();
    let mut recs = Vec::new();
    for (i, (seed, grant)) in specs.iter().enumerate() {
        let (leaf, rec) = receipt(i as u64, *seed, *grant);
        leaves.push(leaf);
        recs.push(rec);
    }
    let mmr = Mmr::from_values(Blake3Mmr, leaves);
    let root_hex: String = mmr.root().iter().map(|x| format!("{x:02x}")).collect();
    (mmr, recs, root_hex)
}

#[test]
fn windowed_read_accepts_an_honest_tiling() {
    let (mmr, recs, root) = fixture();
    // Two contiguous windows tiling [0,4]: [0,2] then [3,4].
    let windows = vec![
        window_json(&mmr, &recs, 0, 2),
        window_json(&mmr, &recs, 3, 4),
    ];
    let leases = dreggnet_bridge::dregg_verify::verified_leases_windowed(&windows, &root)
        .expect("an honest tiling verifies");
    // Two funded exec-leases decode (the tool-call grant is filtered).
    assert_eq!(leases.len(), 2);
    assert_eq!(leases[0].instance, "lease-1-2");
    assert_eq!(leases[0].lease.budget_units, 500);
    assert_eq!(leases[1].instance, "lease-3-4");
    assert_eq!(leases[1].lease.per_period_units, 2);
}

#[test]
fn a_single_window_covering_the_whole_log_also_verifies() {
    let (mmr, recs, root) = fixture();
    let windows = vec![window_json(&mmr, &recs, 0, 4)];
    let leases = dreggnet_bridge::dregg_verify::verified_leases_windowed(&windows, &root)
        .expect("a single whole-log window verifies");
    assert_eq!(leases.len(), 2);
}

#[test]
fn an_omitted_tail_is_rejected() {
    let (mmr, recs, root) = fixture();
    // Only [0,2] — the log is length 5, so the tail [3,4] was omitted.
    let windows = vec![window_json(&mmr, &recs, 0, 2)];
    let err = dreggnet_bridge::dregg_verify::verified_leases_windowed(&windows, &root)
        .expect_err("an omitted tail must fail closed");
    assert!(err.contains("tail was omitted"), "got: {err}");
}

#[test]
fn a_skipped_window_is_rejected() {
    let (mmr, recs, root) = fixture();
    // [0,2] then [4,4] — window [3] was skipped (non-contiguous tiling).
    let windows = vec![
        window_json(&mmr, &recs, 0, 2),
        window_json(&mmr, &recs, 4, 4),
    ];
    let err = dreggnet_bridge::dregg_verify::verified_leases_windowed(&windows, &root)
        .expect_err("a skipped window must fail closed");
    assert!(err.contains("a window was skipped"), "got: {err}");
}

#[test]
fn a_wrong_trusted_root_is_rejected() {
    let (mmr, recs, _root) = fixture();
    let windows = vec![
        window_json(&mmr, &recs, 0, 2),
        window_json(&mmr, &recs, 3, 4),
    ];
    // A root the windows were not opened against — fail closed.
    let bad_root = hex32(0xff);
    let err = dreggnet_bridge::dregg_verify::verified_leases_windowed(&windows, &bad_root)
        .expect_err("a wrong trusted root must fail closed");
    assert!(err.contains("!= trusted index root"), "got: {err}");
}

#[test]
fn no_windows_is_an_error() {
    assert!(dreggnet_bridge::dregg_verify::verified_leases_windowed(&[], &hex32(0x01)).is_err());
}
