//! # THE RETAINED-HISTORY → IVC-FOLD SEAM (Lane 4 composition tooth).
//!
//! The production whole-history path is `mcp::handlers_verify::tool_compress_history`:
//! the node's commit path retains a wrap-input `FinalizedTurn` per committed turn
//! (`turn_proving::mint_and_encode_finalized_turn`, called from
//! `blocklace_sync::execute_finalized_turn`), and compression later loads EXACTLY those
//! retained envelopes, decodes them (`decode_retained_finalized_turn`), and folds them
//! through `ivc_turn_chain::prove_turn_chain_recursive` — whose temporal tooth requires
//! `new_root[i] == old_root[i+1]` across CONSECUTIVE retained turns.
//!
//! Before this file, the two sides were tested only SEPARATELY:
//!   * node side: ONE turn's retention round-trips and host-readmits
//!     (`turn_proving::tests::retained_finalized_turn_round_trips_and_readmits`);
//!   * fold/light-client side: chains minted DIRECTLY from fixtures via
//!     `mint_rotated_participant_leg` (grain-verify `r3_whole_history`, lightclient
//!     `whole_history_demo`) — never through the node's retention encode/decode.
//!
//! Nothing checked the COMPOSITION: that two consecutive turns proven and retained the
//! commit path's way produce DECODED artifacts that actually CHAIN — the exact property
//! whose absence previously made whole-history proving impossible (the node used to
//! retain only hashes). If the node's state threading, the retention mint, or the
//! registry-row descriptor rebuild drifts, every per-side test stays green while
//! `dregg_compress_history` fails on every real node. This file is the RED flag for that.
//!
//! Tests:
//!   1. `retained_consecutive_turns_chain_for_the_fold` (default-run): two consecutive
//!      commit-path turns → retained → decoded → the fold's temporal precondition HOLDS
//!      on the decoded artifacts (all 8 anchor lanes), the decoded anchors equal the
//!      served proofs' anchors, and both legs pass the fold's host admission. A
//!      STALE-threaded third turn (a node that failed to advance the actor state)
//!      breaks the tooth — proving the equality assertions have discriminating power.
//!   2. `retained_history_folds_and_verifies_like_compress_history` (#[ignore], SLOW —
//!      real recursion folds, ~minutes): the decoded turns drive the REAL
//!      `prove_turn_chain_recursive` + `verify_whole_chain_proof_bytes` (the same
//!      light-client teeth `tool_compress_history` runs), and the stale-threaded chain
//!      is REFUSED by the fold.

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::verify_descriptor_participant;
use dregg_node::turn_proving::{
    decode_retained_finalized_turn, mint_and_encode_finalized_turn,
    prove_and_verify_finalized_turn, rotation_witness_for_self_sovereign_with_root,
};

/// One commit-path turn, proven + retained + decoded EXACTLY the way
/// `blocklace_sync::execute_finalized_turn` and `tool_compress_history` do it:
/// prove via `prove_and_verify_finalized_turn` (rotation witness threaded), retain
/// via `mint_and_encode_finalized_turn` anchor-tied to the served proof's commits,
/// decode via `decode_retained_finalized_turn` (registry-row descriptor rebuild).
struct RetainedTurn {
    proven_old: [BabyBear; 8],
    proven_new: [BabyBear; 8],
    /// The persisted retention envelope (what the config store holds).
    bytes: Vec<u8>,
    decoded: FinalizedTurn,
    /// The post-execution actor cell (what the ledger holds after this turn).
    after_cell: dregg_cell::Cell,
}

impl RetainedTurn {
    /// Re-decode the persisted envelope (the fold consumes OWNED turns; `FinalizedTurn`
    /// is not `Clone`, so re-decoding the same bytes is the faithful way to reuse one).
    fn redecode(&self) -> FinalizedTurn {
        decode_retained_finalized_turn(&self.bytes).expect("retained envelope re-decodes")
    }
}

fn prove_commit_and_retain(
    before_cell: &dregg_cell::Cell,
    pre_balance: u64,
    pre_nonce: u64,
    to: dregg_cell::CellId,
    amount: u64,
    turn_hash: [u8; 32],
) -> RetainedTurn {
    let alice = before_cell.id();

    // The ledger's post-execution actor cell: balance debited, nonce advanced
    // (the Effect-VM transition increments the nonce per applied effect).
    let mut after_cell = before_cell.clone();
    after_cell.state.set_balance((pre_balance - amount) as i64);
    let _ = after_cell.state.increment_nonce();

    let effects = vec![dregg_turn::Effect::Transfer {
        from: alice,
        to,
        amount,
    }];
    let receipt_hashes = [[0x11u8; 32]];
    let nullifier_root = dregg_turn::rotation_witness::empty_nullifier_root_8();
    let commitments_root = dregg_turn::rotation_witness::empty_commitments_root_8();

    let rotation = rotation_witness_for_self_sovereign_with_root(
        pre_balance,
        pre_nonce,
        before_cell,
        &after_cell,
        &receipt_hashes,
        &effects,
        &nullifier_root,
        &commitments_root,
    );
    assert!(
        rotation.is_some(),
        "a cap-less transfer turn must yield a rotation witness (pre_balance={pre_balance}, \
         pre_nonce={pre_nonce})"
    );

    let proven = prove_and_verify_finalized_turn(
        &alice,
        pre_balance,
        pre_nonce,
        &effects,
        turn_hash,
        rotation,
    )
    .expect("commit-path turn must prove and self-verify");

    let bytes = mint_and_encode_finalized_turn(
        &alice,
        pre_balance,
        pre_nonce,
        &effects,
        before_cell,
        &after_cell,
        &receipt_hashes,
        &nullifier_root,
        &commitments_root,
        proven.old_commit,
        proven.new_commit,
    )
    .expect("retention mint must bind the real turn context to the served proof's anchors");

    let decoded = decode_retained_finalized_turn(&bytes)
        .expect("retained envelope must decode (registry-row descriptor rebuild)");

    RetainedTurn {
        proven_old: proven.old_commit,
        proven_new: proven.new_commit,
        bytes,
        decoded,
        after_cell,
    }
}

fn wide_old(t: &RetainedTurn) -> [BabyBear; 8] {
    t.decoded
        .participant
        .rotated
        .wide_old_root8()
        .expect("a commit-path retained leg is wide-anchored (OLD)")
}

fn wide_new(t: &RetainedTurn) -> [BabyBear; 8] {
    t.decoded
        .participant
        .rotated
        .wide_new_root8()
        .expect("a commit-path retained leg is wide-anchored (NEW)")
}

/// Two consecutive commit-path turns (turn 2 starts from turn 1's post-state, the way
/// the live ledger threads the actor cell) plus one STALE-threaded turn (a node that
/// failed to advance state — same pre-state as turn 1).
fn make_consecutive_and_stale() -> (RetainedTurn, RetainedTurn, RetainedTurn) {
    let bob = dregg_cell::CellId::from_bytes([0xB4; 32]);
    let genesis_balance: u64 = 1_000;

    let before_cell_1 =
        dregg_cell::Cell::with_balance([0xA9; 32], [0u8; 32], genesis_balance as i64);

    // Turn 1: 1000 → 900, nonce 0 → 1.
    let t1 = prove_commit_and_retain(&before_cell_1, genesis_balance, 0, bob, 100, [0x51u8; 32]);

    // Turn 2: threaded from turn 1's POST-state (before-cell = the ledger's post-exec
    // cell, pre_balance/pre_nonce advanced): 900 → 850, nonce 1 → 2.
    let t2 = prove_commit_and_retain(&t1.after_cell, 900, 1, bob, 50, [0x52u8; 32]);

    // STALE: a broken node re-proves turn 2 from turn 1's PRE-state (state threading
    // failure — the exact bug class that silently kills whole-history compression).
    let stale = prove_commit_and_retain(&before_cell_1, genesis_balance, 0, bob, 50, [0x53u8; 32]);

    (t1, t2, stale)
}

/// **THE SEAM TOOTH (default-run).** Consecutive commit-path retained turns, once
/// decoded, satisfy the fold's temporal precondition — and a stale-threaded turn
/// does NOT (so the equalities below cannot pass vacuously).
#[test]
fn retained_consecutive_turns_chain_for_the_fold() {
    let (t1, t2, stale) = make_consecutive_and_stale();

    // (a) Both decoded legs pass the fold's per-turn host admission (the gate
    //     `prove_turn_chain_recursive` runs on every retained turn).
    verify_descriptor_participant(&t1.decoded.participant)
        .expect("decoded turn 1 must host-readmit");
    verify_descriptor_participant(&t2.decoded.participant)
        .expect("decoded turn 2 must host-readmit");

    // (b) The DECODED anchors are the SERVED proofs' anchors: what the fold will bind
    //     is exactly what `verify_full_turn` attested at commit time. If the retention
    //     encode/decode (registry rebuild, PI layout) drifts, this goes red.
    assert_eq!(
        wide_old(&t1),
        t1.proven_old,
        "decoded OLD == served old_commit (turn 1)"
    );
    assert_eq!(
        wide_new(&t1),
        t1.proven_new,
        "decoded NEW == served new_commit (turn 1)"
    );
    assert_eq!(
        wide_old(&t2),
        t2.proven_old,
        "decoded OLD == served old_commit (turn 2)"
    );
    assert_eq!(
        wide_new(&t2),
        t2.proven_new,
        "decoded NEW == served new_commit (turn 2)"
    );

    // (c) THE TEMPORAL TOOTH — the fold's chain precondition holds ACROSS the seam:
    //     turn 1's decoded NEW anchor is turn 2's decoded OLD anchor, all 8 lanes.
    //     This is the composition property nothing tested: per-turn retention was
    //     green while whole-history folding could still be impossible on a real node.
    assert_eq!(
        wide_new(&t1),
        wide_old(&t2),
        "CONSECUTIVE retained turns must chain: new_root[1] == old_root[2] — if this \
         breaks, `dregg_compress_history` fails on every real node while all per-turn \
         tests stay green"
    );
    // The served-proof chain agrees (the anchors the node logged at commit time).
    assert_eq!(
        t1.proven_new, t2.proven_old,
        "served proof anchors must chain across consecutive commits"
    );

    // (d) DISCRIMINATING POWER: the stale-threaded turn breaks the tooth. Its OLD
    //     anchor equals turn 1's OLD (same pre-state — the anchors are real functions
    //     of state, not constants) and does NOT equal turn 1's NEW, so a chain
    //     [turn1, stale] violates the fold's precondition.
    assert_eq!(
        wide_old(&stale),
        wide_old(&t1),
        "the stale turn re-proves from turn 1's pre-state, so its OLD anchor matches"
    );
    assert_ne!(
        wide_new(&t1),
        wide_old(&stale),
        "a stale-threaded successor must NOT chain — otherwise the temporal-tooth \
         equalities above are vacuous"
    );
}

/// **THE FULL COMPOSITION (SLOW: real recursion folds, ~minutes — run with
/// `cargo test -p dregg-node --test retained_history_ivc_seam -- --ignored`).**
/// The decoded node-retained turns drive the REAL whole-chain fold and the byte
/// envelope re-verifies through the SAME light-client teeth `tool_compress_history`
/// runs (`verify_whole_chain_proof_bytes` against the recomputed VK fingerprint);
/// the stale-threaded chain is REFUSED by the fold.
#[test]
#[ignore = "SLOW: real recursion folds (~minutes); run with --ignored"]
fn retained_history_folds_and_verifies_like_compress_history() {
    let (t1, t2, stale) = make_consecutive_and_stale();

    // THE REAL FOLD over the decoded retained turns — exactly `tool_compress_history`.
    let proof = dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive(&[
        t1.redecode(),
        t2.redecode(),
    ])
    .expect("two consecutive node-retained turns must fold to ONE whole-chain proof");
    assert_eq!(proof.num_turns, 2);

    // The byte envelope re-verifies through the light-client teeth against the
    // recomputed VK fingerprint (the honest-setup anchor mint), as the tool does.
    let bytes = proof.to_bytes();
    let vk = proof.root_vk_fingerprint();
    dregg_circuit_prove::ivc_turn_chain::verify_whole_chain_proof_bytes(&bytes, &vk)
        .expect("the folded node history must verify through the light-client teeth");

    // A stale-threaded (discontinuous) chain is REFUSED — the fold's continuity
    // check, driven with REAL node-retained artifacts rather than fixtures.
    let refused = dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive(&[
        t1.redecode(),
        stale.redecode(),
    ]);
    assert!(
        refused.is_err(),
        "a discontinuous retained chain (stale state threading) must be REFUSED by the fold"
    );
}
