//! direct_vs_json_differential.rs — the no-copy boundary EQUALS the JSON oracle.
//!
//! For every entry in the conformance corpus (12 auth credentials + 30 action arms + the structural
//! deep-forest / full-state / demo / populated-host cases), run BOTH:
//!   * the JSON path: `marshal_turn_hosted` → `shadow_exec_full_forest_auth` → `decode_shadow_state`
//!     (the established, byte-exact oracle); and
//!   * the no-copy path: `shadow_exec_direct` (construct the Lean inductives via the `dregg_d_*`
//!     builders, run `dregg_exec_full_forest_auth_direct`, read the post-state back via the readers).
//! and assert the decoded [`ShadowState`] (verdict bits + FULL post-state) is byte-identical.
//!
//! GATED on `lean_available()` AND `direct_available()`: with no linked archive / no direct export it
//! prints a skip line. The corpus exercises every builder + reader arm, so a single divergent field
//! (a wrong refcount, a dropped side-table, a mis-ordered list) fails this test loudly.

use dregg_lean_ffi::marshal::{conformance_input_corpus, marshal_turn_hosted, WForest, WireTurn};
use dregg_lean_ffi::{
    decode_shadow_state, direct_available, lean_available, shadow_exec_direct, shadow_exec_full_forest_auth,
    WireTurnHdr,
};

/// Split a `WireTurn` into the envelope header (for the direct builder) + the root forest (built
/// recursively, shared with its children). `prev_low` is the low-64 of the `prev` digest — the same
/// `Nat` the JSON `parseHex32` folds for these demo/fixture chain heads (`Digest::from_u64`).
fn split_turn(t: &WireTurn) -> (WireTurnHdr, &WForest) {
    let prev_low = u64::from_be_bytes(t.prev_hash.0[24..32].try_into().unwrap());
    (
        WireTurnHdr {
            agent: t.agent,
            nonce: t.nonce,
            fee: t.fee,
            valid_until: t.valid_until,
            block_height: t.block_height,
            prev_low,
        },
        &t.root,
    )
}

#[test]
fn direct_path_equals_json_oracle_over_the_whole_corpus() {
    if !lean_available() {
        eprintln!("direct_vs_json: libdregg_lean.a not linked — skipped.");
        return;
    }
    if !direct_available() {
        eprintln!(
            "direct_vs_json: dregg_exec_full_forest_auth_direct not exported (stale archive) — \
             skipped. Rebuild the closure (scripts/rebuild-dregg2-closure.sh)."
        );
        return;
    }

    let corpus = conformance_input_corpus();
    assert!(!corpus.is_empty(), "corpus must be non-empty");
    let mut compared = 0usize;
    for (name, host, state, turn) in &corpus {
        // JSON oracle.
        let wire = marshal_turn_hosted(host, state, turn).expect("marshal");
        let json_out = shadow_exec_full_forest_auth(&wire).expect("json ffi");
        let json_state = decode_shadow_state(&json_out).expect("json decode");

        // No-copy direct path.
        let (hdr, root) = split_turn(turn);
        let direct_state = shadow_exec_direct(host, state, root, &hdr).expect("direct ffi");

        assert_eq!(
            direct_state, json_state,
            "DIVERGENCE on corpus case `{name}`: the no-copy direct path != the JSON oracle"
        );
        compared += 1;
    }
    eprintln!("direct_vs_json: {compared} corpus cases — direct == JSON oracle (byte-identical).");
    // The corpus is the 12+30+structural set; ensure we actually drove the whole surface.
    assert!(compared >= 45, "expected the full corpus (>=45 cases), got {compared}");
}
