//! # Phase 3 — the STARK FOLD: the hidden-hand tooth lowered into the recursive fold.
//!
//! Phase 2 ([`crate::hidden_hand`]) committed each hand as a Poseidon2 4-ary Merkle root
//! and proved each play with a `StateConstraint::Witnessed { MerkleMembership }` tooth,
//! checked IN THE CLEAR by the real cell evaluator + registry. Phase 3 lowers that tooth
//! INTO THE FOLD: a whole PRIVATE match — a sequence of membership-proven plays — becomes
//! ONE succinct proof a pure light client ([`dregg_lightclient::verify_history`]) accepts,
//! re-witnessing nothing.
//!
//! ## How the hidden-hand tooth reaches the fold
//!
//! The lowering lives in the IMT terminal ([`game_turn_slice::compiler`]): a
//! [`PlayProof`](crate::hidden_hand::PlayProof)'s leaf opening + authentication path + root
//! become a [`LoweredMembership`] leaf — the deployed circuit-DSL
//! `merkle_poseidon2_descriptor` (the SAME 4-ary Poseidon2 recurrence the clear-side
//! verifier walks, that `dregg_circuit::merkle_types::MerkleAir` proves) with a trace that
//! climbs the path to the committed root, and public inputs `[leaf, root]`. Each play's leaf
//! proves through `prove_custom_leaf_with_commitment` and binds into a `Custom`-effect turn;
//! the turns fold via [`prove_turn_chain_recursive`] into one `WholeChainProof`.
//!
//! ## What is private (honest scope)
//!
//! The played card IS revealed (a face-up play, as the game's Gift/Competition land on the
//! board), but the REST of the hand is not: the PIs carry only the blinded leaf commitment +
//! the hand root — the card ids are NOT in the proof, and the membership hides the other
//! cards (the path carries only sibling *hashes*). "Private-in-fold" here means exactly this:
//! the cards are not in the proof / public inputs, and data-availability + the membership
//! hide the hand. The deployed STARK is SUCCINCT, not zero-knowledge — true crypto-ZK (hiding
//! the transcript) is a separate, later concern. The named next phase is **Phase 4** (the
//! Lean refinement: the fold + the Witnessed lowering vs `MultiwayTug.lean`).
//!
//! ## The fold wiring (mirrors the audited deployed-custom-binding pattern)
//!
//! The per-turn leg minting (a wide `customVmDescriptor2R24` leg whose published
//! `custom_proof_commitment` is `custom_proof_pi_commitment([leaf, root])`, with the
//! re-provable membership witness retained prover-side) mirrors
//! `game-turn-slice/tests/game_turn_slice.rs`'s deployed template, specialized to the
//! membership leaf. A turn whose leg claims a commitment no verifying sub-proof backs is
//! UNSAT (no root) — so a forged match is rejected by the fold / light client.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive;
use dregg_circuit_prove::ivc_turn_chain::{FinalizedTurn, ir2_leaf_wrap_config};
use dregg_circuit_prove::joint_turn_aggregation::{
    CustomWitnessBundle, DescriptorParticipant, RotatedParticipantLeg,
};
use dregg_turn::rotation_witness as rw;
use game_turn_slice::compiler::{
    LoweredMembership, MembershipLevel, MerkleMembershipWitness, lower_witnessed_merkle_membership,
    root_felt_from_commitment,
};

use dregg_cell::{InputRef, WitnessedPredicate};

use crate::hidden_hand::{PlayProof, card_leaf};

// ===========================================================================
// A foldable leaf bundle (a membership play, or the terminal win/score turn).
// ===========================================================================

/// A foldable custom-leaf turn: the circuit-DSL program, its trace witness, the row count,
/// and the public inputs the fold binds. Uniform over a membership play
/// ([`LoweredMembership`]) and the win/score turn (a [`game_turn_slice::compiler`] range
/// gadget leaf), so the match folds a heterogeneous chain through one path.
#[derive(Clone)]
pub struct LeafBundle {
    pub program: dregg_circuit::dsl::circuit::CellProgram,
    pub witness_values: std::collections::HashMap<String, Vec<BabyBear>>,
    pub num_rows: usize,
    pub public_inputs: Vec<BabyBear>,
}

impl From<LoweredMembership> for LeafBundle {
    fn from(l: LoweredMembership) -> Self {
        LeafBundle {
            program: l.program,
            witness_values: l.witness_values,
            num_rows: l.num_rows,
            public_inputs: l.public_inputs,
        }
    }
}

/// **The hidden-hand tooth → a foldable leaf.** Lower a Phase-2 [`PlayProof`] into the
/// foldable membership leaf: reconstruct the blinded leaf commitment
/// ([`card_leaf`]) + the authentication path + the committed root from the proof, then run
/// [`lower_witnessed_merkle_membership`] against the SAME `Witnessed { MerkleMembership }`
/// tooth the executor checks in the clear (`hidden_hand::membership_program`). `Err` = a
/// fabricated card / tampered path (the proof does not climb to the committed root).
pub fn membership_leaf_for_play(proof: &PlayProof) -> Result<LoweredMembership, String> {
    let leaf = card_leaf(proof.card_id, proof.nonce);
    let levels: Vec<MembershipLevel> = proof
        .path
        .iter()
        .map(|lvl| MembershipLevel {
            position: lvl.position,
            siblings: lvl.siblings,
        })
        .collect();
    let root = root_felt_from_commitment(&proof.root);
    let witness = MerkleMembershipWitness { leaf, levels, root };
    // The identical predicate the clear-side check runs: the opening rides witness blob 0,
    // the path rides blob 1, committed under the played card's root.
    let wp = WitnessedPredicate::merkle_membership(proof.root, InputRef::Witness { index: 0 }, 1);
    lower_witnessed_merkle_membership(&wp, &witness).map_err(|b| b.to_string())
}

// ===========================================================================
// The per-turn leg minting (the deployed-custom-binding pattern).
// ===========================================================================

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// Mint a REAL wide `customVmDescriptor2R24` leg whose published `custom_proof_commitment`
/// (IR2 PI 46..53) is `commit`, attaching the prover-side re-provable `bundle` the deployed
/// chain prover re-proves + binds. Custom bumps nonce by 1, balance unchanged.
fn mint_custom_leg(
    balance: i64,
    nonce: u64,
    commit: [BabyBear; 8],
    bundle: Option<CustomWitnessBundle>,
) -> RotatedParticipantLeg {
    let st = CellState::new(balance as u64, nonce as u32);
    let effects = vec![Effect::Custom {
        program_vk_hash: [BabyBear::new(9); 8],
        proof_commitment: commit,
    }];
    let before_cell = producer_cell(balance, nonce);
    let after_cell = producer_cell(balance, nonce + 1);

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).expect("ledger seed");
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = bridge(&rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));
    let after_w = bridge(&rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    ));

    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &before_w,
        &after_w,
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("custom wide dispatch");
    assert!(
        dpis.len() >= 54,
        "custom leg PI vector must carry the 8-felt commitment slice at 46..53"
    );
    assert_eq!(
        &dpis[46..54],
        &commit[..],
        "custom leg must publish the claimed 8-felt commitment at PI 46..53"
    );

    let config = ir2_leaf_wrap_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mb,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("custom wide leg proves under the leaf-wrap config");

    let leg = RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    };
    match bundle {
        Some(b) => leg.with_custom_witness(b),
        None => leg,
    }
}

/// Mint one match turn from a foldable leaf bundle at `nonce`: the leg's published
/// commitment IS `custom_proof_pi_commitment(bundle.public_inputs)` (the honest binding), and
/// the re-provable membership/teeth witness is retained prover-side.
fn mint_turn(bundle: &LeafBundle, nonce: u64) -> FinalizedTurn {
    let balance = 1000i64;
    let commit = custom_proof_pi_commitment(&bundle.public_inputs);
    let cwb = CustomWitnessBundle {
        program: bundle.program.clone(),
        witness_values: bundle.witness_values.clone(),
        num_rows: bundle.num_rows,
        public_inputs: bundle.public_inputs.clone(),
    };
    let leg = mint_custom_leg(balance, nonce, commit, Some(cwb));
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// Build the chain of [`FinalizedTurn`]s for a match: turn `i` binds `bundles[i]` at nonce
/// `i`, linking off turn `i-1`'s post-state `(balance, i)`. Consecutive turns link because
/// turn `i`'s post-state nonce `i+1` equals turn `i+1`'s pre-state nonce.
pub fn build_match_turns(bundles: &[LeafBundle]) -> Vec<FinalizedTurn> {
    let turns: Vec<FinalizedTurn> = bundles
        .iter()
        .enumerate()
        .map(|(i, b)| mint_turn(b, i as u64))
        .collect();
    for w in turns.windows(2) {
        assert_eq!(
            w[0].new_root(),
            w[1].old_root(),
            "consecutive match turns must link (post-state → pre-state)"
        );
    }
    turns
}

/// Fold a whole match (a chain of foldable turns) into ONE `WholeChainProof` via the deployed
/// per-turn recursion fold. The returned proof is what a pure light client
/// ([`dregg_lightclient::verify_history`]) attests.
pub fn fold_match(
    bundles: &[LeafBundle],
) -> Result<dregg_circuit_prove::ivc_turn_chain::WholeChainProof, String> {
    let turns = build_match_turns(bundles);
    prove_turn_chain_recursive(&turns).map_err(|e| format!("match fold failed: {e}"))
}

#[cfg(test)]
mod tests;
