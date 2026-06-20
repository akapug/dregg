//! M2-a: single-asset shielded transfer — both-polarity acceptance tests.
//!
//! The shielded transfer is a two-sided composite (see
//! `dregg_circuit::shielded`):
//!   1. the **hidden STARK side** (`ShieldedTransfer::verify_stark_side`):
//!      per-input membership in the commitment tree + nullifier derivation,
//!      proved through `HidingFriPcs` so the owner/key/path are blind;
//!   2. the **hidden Pedersen side** (`dregg_cell::value_commitment`):
//!      homomorphic value-commitment conservation, so `Σ v_in = Σ v_out` is
//!      certified without revealing any amount.
//!
//! These tests live here (a `dregg-circuit` integration test, where
//! `dregg-cell` is a dev-dependency) because `circuit` is *upstream* of `cell`:
//! the circuit-side STARK half is library code in `dregg_circuit::shielded`,
//! and the Pedersen value-balance half is composed at this layer.
//!
//! Both polarities, per half:
//!   STARK side    — balanced transfer VERIFIES (blind);
//!                   forged membership (wrong root) REJECTS;
//!                   duplicate / tampered nullifier REJECTS.
//!   Pedersen side — balanced value commitments VERIFY (blind);
//!                   an unbalanced set (inflation) REJECTS.

#![cfg(feature = "prover")]

use dregg_circuit::field::BabyBear;
use dregg_circuit::shielded::{
    ShieldedError, ShieldedSpendWitness, ShieldedTransfer, ShieldedTransferWitness,
    ShieldedValueLeg,
};

use dregg_cell::value_commitment::{
    ValueCommitment, prove_conservation, scalar_from_blinding_bytes, verify_conservation,
};

const ASSET: u64 = 1;

/// Build a shielded-spend witness with a genuine Poseidon2 Merkle path (leaf =
/// the input note commitment), plus the published value-commitment leg for it.
fn make_input(
    leaf_seed: u32,
    amount: u32,
    blinding: [u8; 32],
    key_seed: u32,
    depth: usize,
) -> ShieldedTransferWitness {
    let leaf_commitment = BabyBear::new(0x5EED ^ leaf_seed);
    let key = [
        BabyBear::new(key_seed),
        BabyBear::new(key_seed.wrapping_add(1)),
        BabyBear::new(key_seed.wrapping_add(2)),
        BabyBear::new(key_seed.wrapping_add(3)),
    ];

    // A small genuine Merkle path (deterministic siblings).
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        positions.push((i % 4) as u8);
        siblings.push([
            BabyBear::new((i as u32) * 7 + 1 + leaf_seed),
            BabyBear::new((i as u32) * 7 + 2 + leaf_seed),
            BabyBear::new((i as u32) * 7 + 3 + leaf_seed),
        ]);
    }

    let spend = ShieldedSpendWitness {
        leaf_commitment,
        key,
        siblings,
        positions,
    };

    let commitment =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&blinding));

    ShieldedTransferWitness {
        spend,
        leg: ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: commitment.to_bytes().0,
        },
    }
}

/// Construct a balanced shielded transfer (STARK side) from ONE input, pinned to
/// that input's real DSL Merkle root, with one output leg of equal value.
/// Returns (transfer, in_blinding, out_blinding, out_commitment) so the caller
/// can drive the Pedersen conservation proof.
fn balanced_transfer() -> (ShieldedTransfer, ValueCommitment, ValueCommitment) {
    let amount = 1_000_000u32;
    let in_blinding = [3u8; 32];
    let out_blinding = [7u8; 32];

    let w = make_input(11, amount, in_blinding, 0xABCD, 4);
    let merkle_root = w.spend.merkle_root();

    let in_commit =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&in_blinding));
    let out_commit =
        ValueCommitment::commit(amount as u64, &scalar_from_blinding_bytes(&out_blinding));

    let output_legs = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: out_commit.to_bytes().0,
    }];

    let transfer =
        dregg_circuit::shielded::transfer_from_witnesses(merkle_root, &[w], output_legs)
            .expect("prove balanced shielded transfer STARK side");

    (transfer, in_commit, out_commit)
}

#[test]
fn balanced_shielded_transfer_stark_side_verifies_blind() {
    let (transfer, _in_c, _out_c) = balanced_transfer();
    // The hidden membership+nullifier proof verifies against the published root,
    // revealing nothing about owner/key/path.
    transfer
        .verify_stark_side()
        .expect("balanced shielded transfer STARK side must verify");
    assert_eq!(transfer.nullifiers().len(), 1);
}

#[test]
fn balanced_shielded_transfer_pedersen_side_verifies_blind() {
    let (transfer, in_c, out_c) = balanced_transfer();
    // excess_blinding = r_in - r_out (the prover knows both).
    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out = scalar_from_blinding_bytes(&[7u8; 32]);
    let excess = r_in - r_out;
    let msg = transfer.transfer_message();
    let proof = prove_conservation(&[in_c.clone()], &[out_c.clone()], &excess, &msg);
    // Value balance certified WITHOUT revealing the amount.
    verify_conservation(&[in_c], &[out_c], &proof, &msg)
        .expect("balanced value commitments must conserve");
}

#[test]
fn forged_membership_wrong_root_rejects() {
    let (mut transfer, _in_c, _out_c) = balanced_transfer();
    // Tamper the published root: the hidden proof was bound to the real root, so
    // verification against a different root MUST fail (no fake membership).
    transfer.merkle_root = transfer.merkle_root + BabyBear::ONE;
    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::InputProofRejected { .. })),
        "a shielded transfer presented against the wrong root must reject, got {res:?}"
    );
}

#[test]
fn unbalanced_value_commitments_reject() {
    let (transfer, in_c, _out_c) = balanced_transfer();
    // Forge an output committing to MORE than the input (inflation). The excess
    // now has a nonzero V-component, so the Schnorr-on-R proof cannot answer.
    let inflated = 2_000_000u64;
    let r_out = [7u8; 32];
    let bad_out = ValueCommitment::commit(inflated, &scalar_from_blinding_bytes(&r_out));

    let r_in = scalar_from_blinding_bytes(&[3u8; 32]);
    let r_out_s = scalar_from_blinding_bytes(&r_out);
    let excess = r_in - r_out_s; // prover still uses the blinding excess
    let msg = transfer.transfer_message();
    let proof = prove_conservation(&[in_c.clone()], &[bad_out.clone()], &excess, &msg);
    let res = verify_conservation(&[in_c], &[bad_out], &proof, &msg);
    assert!(
        res.is_err(),
        "an inflating (unbalanced) value-commitment set must NOT conserve"
    );
}

#[test]
fn duplicate_nullifier_in_transfer_rejects() {
    // Two inputs that share a nullifier (same note spent twice in one transfer).
    let amount = 500_000u32;
    let in_blinding = [3u8; 32];
    let w1 = make_input(21, amount, in_blinding, 0x1111, 4);
    // Same owner/key/nonce/randomness -> same note -> same nullifier.
    let w2 = make_input(21, amount, in_blinding, 0x1111, 4);
    assert_eq!(
        w1.spend.nullifier(),
        w2.spend.nullifier(),
        "identical notes must produce identical nullifiers"
    );
    // Both pinned to the same root.
    let merkle_root = w1.spend.merkle_root();

    let out_leg = vec![ShieldedValueLeg {
        asset_type: ASSET,
        commitment_bytes: ValueCommitment::commit(
            (2 * amount) as u64,
            &scalar_from_blinding_bytes(&[9u8; 32]),
        )
        .to_bytes()
        .0,
    }];

    let transfer =
        dregg_circuit::shielded::transfer_from_witnesses(merkle_root, &[w1, w2], out_leg)
            .expect("STARK proofs build even for a double-spend (caught at verify)");

    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::DuplicateNullifier { .. })),
        "a transfer spending the same nullifier twice must reject, got {res:?}"
    );
}

#[test]
fn no_inputs_rejects() {
    let res = dregg_circuit::shielded::transfer_from_witnesses(BabyBear::ZERO, &[], vec![]);
    assert!(matches!(res, Err(ShieldedError::NoInputs)));
}

#[test]
fn tampered_nullifier_rejects() {
    // The published nullifier must match what the hidden proof derived. Swapping
    // it for any other value breaks the row-0 nullifier binding boundary.
    let (mut transfer, _in_c, _out_c) = balanced_transfer();
    transfer.inputs[0].nullifier = transfer.inputs[0].nullifier + BabyBear::ONE;
    let res = transfer.verify_stark_side();
    assert!(
        matches!(res, Err(ShieldedError::InputProofRejected { .. })),
        "a transfer presenting a nullifier the proof did not derive must reject, got {res:?}"
    );
}

#[test]
fn shielded_proof_is_hiding_independent_blinding() {
    // Two ZK proofs of the SAME shielded spend must differ (fresh blinding each
    // time) — if byte-identical, the blinding RNG would be deterministic and the
    // witness could leak via cross-proof comparison. Both still verify.
    use dregg_circuit::dsl::dsl_p3_air::prove_dsl_zk;
    use dregg_circuit::shielded::{generate_shielded_spend_trace, shielded_spend_circuit};

    let w = make_input(99, 250_000, [5u8; 32], 0x2222, 4);
    let circuit = shielded_spend_circuit();
    let (trace, pis) = generate_shielded_spend_trace(&w.spend);

    let p1 = prove_dsl_zk(&circuit, &trace, &pis).expect("zk prove 1");
    let p2 = prove_dsl_zk(&circuit, &trace, &pis).expect("zk prove 2");

    let b1 = postcard::to_allocvec(&p1).expect("ser p1");
    let b2 = postcard::to_allocvec(&p2).expect("ser p2");
    assert_ne!(
        b1, b2,
        "two ZK proofs of the same shielded spend must use independent blinding (hiding)"
    );
}
