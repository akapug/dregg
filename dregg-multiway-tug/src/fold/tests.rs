//! Phase 3 — the STARK fold, DRIVEN.
//!
//! The hidden-hand `Witnessed { MerkleMembership }` tooth lowers to a foldable leaf
//! ([`membership_leaf_for_play`]); a whole PRIVATE match (a sequence of membership-proven
//! plays) folds to ONE `verify_history`-accepted proof; a forged match is rejected. The
//! cheap tests always run (lowering is non-vacuous); the fold tests are `#[ignore]` SLOW.

use super::*;
use crate::hidden_hand::HandTree;
use dregg_cell::program::{StateConstraint, field_from_u64};
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_lightclient::verify_history;
use game_turn_slice::compiler::{GameProgramCompiler, SlotAssignment};

/// A deterministic six-card hand: distinct card ids across guilds, distinct nonces (the same
/// shape `hidden_hand::tests::sample_hand` uses).
fn sample_hand() -> Vec<(u64, u64)> {
    vec![
        (0, 1001),
        (1, 1002),
        (3, 1003),
        (7, 1004),
        (12, 1005),
        (18, 1006),
    ]
}

// The win/score turn's slot layout.
const WIN_CHARM: u8 = 0; // the winner's total influence — FieldGte >= 11 (range gadget)
const WIN_SCORE: u8 = 1; // running score — conserved this turn
const WIN_POINTS: u8 = 2; // influence gained this turn

/// The terminal win/score turn: a range-gadget leaf binding `[charm, winner]` as a public
/// output, proving the winner crossed the influence threshold (`FieldGte charm >= 11`) with a
/// conserved score (`new[score] == old[score] + new[points]`). The win is thus a BOUND public
/// output the light client attests via the leaf's commitment.
fn win_bundle(charm: u64, winner: u64) -> LeafBundle {
    let mut c = GameProgramCompiler::new("multiway-tug-win-v1", 16).with_public_inputs(2);
    c.lower_state_constraint(&StateConstraint::SumEqualsAcross {
        input_fields: vec![WIN_SCORE],
        output_fields: vec![WIN_POINTS],
    })
    .expect("score conservation lowers");
    c.lower_state_constraint(&StateConstraint::FieldGte {
        index: WIN_CHARM,
        value: field_from_u64(11),
    })
    .expect("the win threshold lowers via the range gadget");
    let program = c.finish();
    let assign = SlotAssignment::new()
        .set_new(WIN_CHARM, charm) // >= 11
        .set_new(WIN_SCORE, 20)
        .set_old(WIN_SCORE, 15)
        .set_new(WIN_POINTS, 5); // 20 - 15 - 5 == 0
    let witness_values = c.witness(&assign, 4).expect("honest win witness");
    LeafBundle {
        program,
        witness_values,
        num_rows: 4,
        public_inputs: vec![BabyBear::from_u64(charm), BabyBear::from_u64(winner)],
    }
}

// ---------------------------------------------------------------------------
// Cheap, always-run: the lowering is total + non-vacuous (no proving).
// ---------------------------------------------------------------------------

/// Every dealt card's Phase-2 play lowers to a foldable membership leaf: PIs `[leaf, root]`
/// (the card id is NOT among them — the hand is private-in-fold), leaf `== card_leaf(card,
/// nonce)`, root `== the committed hand root`.
#[test]
fn every_play_lowers_to_a_membership_leaf() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let root = root_felt_from_commitment(&tree.root_bytes());
    for &(card, nonce) in &hand {
        let proof = tree.prove_play(card).expect("a dealt card can be proven");
        let leaf = membership_leaf_for_play(&proof).expect("an honest play lowers to a leaf");
        assert_eq!(
            leaf.public_inputs,
            vec![card_leaf(card, nonce), root],
            "PIs are [leaf, root] — the card id is NOT in the proof"
        );
        assert!(
            !leaf.public_inputs.contains(&BabyBear::from_u64(card)),
            "the raw card id never appears in the public inputs"
        );
        assert_eq!(
            leaf.num_rows, 2,
            "depth-2 hand tree ⇒ a 2-row membership trace"
        );
    }
}

/// A fabricated card / tampered path has NO membership leaf: a card never dealt cannot be
/// proven at all, and a play whose path is corrupted (so it no longer climbs to the committed
/// root) is refused at lowering.
#[test]
fn fabricated_card_has_no_membership_leaf() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());

    // A card that was never dealt (20 ∉ the hand) cannot even be proven.
    assert!(
        tree.prove_play(20).is_none(),
        "a card not in the hand has no membership proof"
    );

    // A dealt card's proof with a corrupted sibling no longer climbs to the committed root.
    let mut proof = tree.prove_play(hand[0].0).expect("dealt card proves");
    proof.path[0].siblings[0] = proof.path[0].siblings[0] + BabyBear::ONE;
    assert!(
        membership_leaf_for_play(&proof).is_err(),
        "a tampered path that does not climb to the committed root is refused at lowering"
    );

    // A replay of a played card against the UPDATED remaining root fails membership.
    let remaining = tree.without(hand[0].0);
    assert!(
        remaining.prove_play(hand[0].0).is_none(),
        "a played card is no longer under the remaining-hand root (no double-play)"
    );
}

/// **THE WIN IS WELDED TO THE CELL'S STATE PREFIX.** The win leaf publishes
/// `[old8 ‖ new8 ‖ charm ‖ winner]`; its public-input commitment (the value the fold binds and
/// the deployed state-binding node connects to the leg's real rotated roots) MOVES when the
/// `[old8 ‖ new8]` prefix is one cell's vs another's — so a win cannot be claimed over a
/// different cell transition. The winner is still a bound output (a different winner moves the
/// commitment too).
///
/// This REPLACES the old `win_output_binds_the_winner`, which only asserted Poseidon2 is
/// injective over `[charm, winner]` (vacuous — it was true of any hash and said nothing about
/// the cell). The real-cell drive — the win folding over the WorldCell's own committed cell —
/// is `tests/fold_real_cell.rs`.
#[test]
fn win_output_is_welded_to_the_cell_prefix() {
    use super::{fixture_wire_commit8, win_leaf_bound};
    let new8: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(500 + i as u32));
    let cell_a: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(i as u32));

    let a = win_leaf_bound(cell_a, new8, 13, 1);
    let b = win_leaf_bound(fixture_wire_commit8(), new8, 13, 1);
    assert_ne!(
        custom_proof_pi_commitment(&a.public_inputs),
        custom_proof_pi_commitment(&b.public_inputs),
        "the SAME win over a DIFFERENT cell prefix must bind a different commitment — the win \
         is welded to the cell, not free"
    );

    let c = win_leaf_bound(cell_a, new8, 13, 2);
    assert_ne!(
        custom_proof_pi_commitment(&a.public_inputs),
        custom_proof_pi_commitment(&c.public_inputs),
        "a different winner still binds a different commitment"
    );
}

// ---------------------------------------------------------------------------
// SLOW (#[ignore]): the whole private match folds to one verify_history-accepted proof.
// ---------------------------------------------------------------------------

/// THE HARD GATE: a private multiway-tug match — TWO membership-proven plays (card A from the
/// full hand, then card B from the updated remaining hand, each proven under its own committed
/// root, the cards never revealed in the proof) — FOLDS via `prove_turn_chain_recursive` into
/// ONE `WholeChainProof` the pure light client `verify_history` ACCEPTS. Then a relabeled
/// `final_root` is REJECTED (a non-vacuous light-client bite), and the restored proof accepts.
// NOTE (state-prefix residual): the two SLOW tests below fold 2-felt membership/win leaves
// (`[leaf, root]` / `[charm, winner]`) that PREDATE the deployed custom state-binding node,
// which now requires every custom sub-proof leaf to publish the 16-felt `[old8 ‖ new8]` prefix
// (see `circuit/src/effect_vm/custom_state_binding.rs`). They therefore no longer mint through
// `prove_custom_leaf_with_state_commitment` as-is. The WIN leaf's prefix closure is
// `win_leaf_bound` + the real-cell fold (`tests/fold_real_cell.rs`); the MEMBERSHIP-leaf prefix
// (prepend the leg's real roots to `[leaf, root]`, identically) is the named residual for the
// hidden-hand plays.
#[test]
#[ignore = "SUPERSEDED by tests/fold_real_cell.rs: 2-PI membership leaves predate the state-binding prefix; membership-leaf prefixing is the named residual"]
fn private_match_folds_and_lightclient_accepts() {
    let hand = sample_hand();
    let t0 = HandTree::commit(hand.clone());
    let p0 = t0.prove_play(hand[0].0).expect("play A proves membership");
    let t1 = t0.without(hand[0].0);
    let p1 = t1
        .prove_play(hand[1].0)
        .expect("play B proves membership vs the remaining root");

    let b0: LeafBundle = membership_leaf_for_play(&p0)
        .expect("play A lowers to a membership leaf")
        .into();
    let b1: LeafBundle = membership_leaf_for_play(&p1)
        .expect("play B lowers to a membership leaf")
        .into();

    let mut whole = fold_match(&[b0, b1]).expect("the private match folds to one proof");
    let vk = whole.root_vk_fingerprint();

    let attested =
        verify_history(&whole, &vk).expect("the light client ACCEPTS the honest private match");
    assert_eq!(
        attested.num_turns, 2,
        "the attestation covers both membership-proven plays"
    );
    eprintln!(
        "MULTIWAY-TUG PHASE 3 ACCEPT: a 2-play PRIVATE match folded to ONE proof; \
         verify_history OK, num_turns={} (the cards never appeared in the proof).",
        attested.num_turns
    );

    // NON-VACUOUS FORGERY: relabel the carried final_root; verify_history REFUSES.
    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED by verify_history"
    );
    // Restore + re-accept — the refusal was the lie, not collateral damage.
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored honest match verifies again");
    eprintln!("MULTIWAY-TUG PHASE 3 REJECT: verify_history refused a spliced final_root.");
}

/// THE WIN AS A BOUND PUBLIC OUTPUT: a match of a membership-proven play followed by the
/// terminal win/score turn folds; the light client attests the whole chain, and the win turn's
/// leg publishes the honest `custom_proof_pi_commitment([charm, winner])` — the win is a bound
/// public output. A relabeled final_root is rejected.
#[test]
#[ignore = "SUPERSEDED by tests/fold_real_cell.rs::win_folds_over_the_real_cell_and_lightclient_accepts: the real-cell win fold carries the [old8 ‖ new8] prefix; this 2-PI form predates it"]
fn match_win_output_is_attested() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let p0 = tree
        .prove_play(hand[0].0)
        .expect("the play proves membership");
    let play: LeafBundle = membership_leaf_for_play(&p0)
        .expect("the play lowers to a membership leaf")
        .into();
    let win = win_bundle(13, 1); // winner = player 1, influence 13 (>= 11)

    let mut whole = fold_match(&[play, win]).expect("the play + win turn fold to one proof");
    let vk = whole.root_vk_fingerprint();

    let attested = verify_history(&whole, &vk)
        .expect("the light client ACCEPTS the membership-play + win-turn match");
    assert_eq!(attested.num_turns, 2, "one play + the win turn");
    eprintln!(
        "MULTIWAY-TUG PHASE 3 WIN: membership play + win turn folded; verify_history OK, \
         num_turns={}; the win [charm=13, winner=1] is a bound public output.",
        attested.num_turns
    );

    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED"
    );
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored match verifies again");
}
