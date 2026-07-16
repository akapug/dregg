//! THE VALUE↔FACT WELD CANARY — the falsifier for the `≤` / `>` / `<` / `≠` / `InRange` predicate
//! descriptors' binding between the number they compare and the fact commitment they present.
//!
//! The `≥` sibling's canary is `predicate_arith_fact_weld_canary.rs`; this is the same falsifier for
//! the five siblings that shared its disease (M14).
//!
//! ## The statement under test
//!
//! Each deployed descriptor's job is to prove ONE thing:
//!
//! > "the value covered by the fact commitment `pi[last]` (which the verifier sources from trusted
//! > token state) satisfies the comparison against the public bound(s)."
//!
//! That is a conjunction with a SHARED variable: `INPUT op bound` **AND**
//! `FACT_COMMITMENT = commit(fact(INPUT), state_root)`. The second conjunct is what makes the first
//! one *about* token state. Before the weld nothing in these AIRs related the commitment column to
//! the compared column, so each descriptor proved the halves independently — "some value satisfies
//! the comparison" and "here is a commitment I was handed" — which is not the statement, and is
//! forgeable by a prover who supplies an `INPUT` of its own choosing alongside the honest,
//! verifier-expected commitment.
//!
//! ## The falsifier
//!
//! For each sibling, [`forged_value_with_honest_commitment_is_refused_*`] presents the honest,
//! verifier-expected commitment for a value that FAILS the predicate, while proving the predicate on
//! a different value of the prover's choosing. Each is paired with an honest pole so it can never
//! pass vacuously.
//!
//! The attack is expressed by HAND-FORGING the trace, not by calling the builder: the welded API
//! cannot express it (the commitment is computed FROM the compared value). Hand-forging is the
//! STRONGER form — it grants the attacker full control of every column, unconstrained by our own
//! builder's discipline, and asks the CIRCUIT to be the judge.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding};
use dregg_circuit::predicate_comparison_witness::{
    IR_FACT_COMMITMENT, NEQ_FACT_COMMITMENT, OS_FACT_COMMITMENT, PREDICATE_ARITH_GT_NAME,
    PREDICATE_ARITH_INRANGE_NAME, PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME,
    PREDICATE_ARITH_NEQ_NAME, predicate_gt_witness, predicate_inrange_witness,
    predicate_le_witness, predicate_lt_witness, predicate_neq_witness,
};
use dregg_circuit::refusal::{Outcome, classify};

/// The fact identity under test — one honest world shared by every test here.
fn fact() -> FactBinding {
    FactBinding {
        predicate_sym: BabyBear::new(0x9E),
        term1: BabyBear::new(0x11),
        term2: BabyBear::new(0x22),
        state_root: BabyBear::new(0x57A7E),
    }
}

/// The per-presentation blinding every test here is driven under — a REAL non-zero one, so the
/// falsifier bites in the deployed (blinded) posture. It is FIXED across the honest witness and the
/// verifier's expected commitment on purpose: a verifier reproduces the commitment from trusted
/// token state plus the blinding the presentation DISCLOSES, so the attacker and the verifier are
/// working under the same blinding. Blinding both sides with the same factor is what keeps the
/// forgery expressible — otherwise the commitments would differ for a reason that has nothing to do
/// with the weld, and the canary would pass vacuously.
fn test_blinding() -> Blinding {
    Blinding(BabyBear::new(0xB11D1))
}

/// The honest, verifier-expected fact commitment covering `value` at the state root under
/// [`test_blinding`] — the SAME production binding a verifier independently derives from trusted
/// token state and the disclosed blinding.
fn honest_commitment(value: u64) -> BabyBear {
    fact().commitment_of(BabyBear::from_u64(value), test_blinding())
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
/// Prove-THEN-verify is the faithful consumer posture: an attacker who gets a proof out of the prover
/// only wins if a verifier accepts it.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("weld-canary", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// Drive ONE sibling's falsifier, both directions.
///
/// * `built` — an HONEST witness for `forged_value` (it genuinely satisfies the comparison), whose
///   commitment the builder COMPUTES.
/// * `true_value` — the value token state actually commits to. It FAILS the comparison.
/// * `fact_col` / `pi_index` — where the commitment lives in this descriptor's trace / PI vector.
///
/// Asserts: the honest witness is ACCEPTED (non-vacuity), the builder computed the verifier's
/// expected commitment, and the FORGERY (honest comparison columns + the honest commitment for a
/// value that fails the predicate) is REFUSED.
fn drive_forgery(
    name: &str,
    built: (Vec<Vec<BabyBear>>, Vec<BabyBear>),
    forged_value: u64,
    true_value: u64,
    fact_col: usize,
    pi_index: usize,
) {
    let desc = descriptor_by_name(name).unwrap_or_else(|| panic!("{name} dispatches"));
    let (mut trace, mut pis) = built;

    // NON-VACUITY POLE: the honest proof about `forged_value` proves and verifies, and its commitment
    // is exactly what a verifier derives from token state for that value.
    assert!(
        !rejects(&desc, &trace, &pis),
        "{name}: the pre-forgery witness must be ACCEPTED, else this canary proves nothing"
    );
    assert_eq!(
        pis[pi_index],
        honest_commitment(forged_value),
        "{name}: the builder COMPUTES the commitment a verifier derives from token state — \
         the fact commitment is an OUTPUT of the weld, not an argument"
    );

    // What the verifier expects, sourced from trusted token state: the commitment covering the TRUE
    // value. The attacker does not forge this — it is public and honest.
    let expected_commitment = honest_commitment(true_value);
    assert_ne!(
        pis[pi_index], expected_commitment,
        "{name}: the honest witness for {forged_value} must not already carry {true_value}'s commitment"
    );

    // THE FORGERY: swap the commitment column (and the pinned PI) to the honest commitment for the
    // TRUE value, leaving the comparison columns untouched. Every constraint mentioning the compared
    // column still holds; the PI is exactly what the verifier expects.
    for row in &mut trace {
        row[fact_col] = expected_commitment;
    }
    pis[pi_index] = expected_commitment;

    assert!(
        rejects(&desc, &trace, &pis),
        "{name}: FORGERY ACCEPTED — the descriptor proved the comparison about {forged_value} \
         against the honest commitment for value {true_value} (which does NOT satisfy it). The \
         compared value and the committed fact are UNRELATED: the predicate proof does not bind to \
         token state."
    );
}

/// `≤`: token state commits to 200 (200 ≤ 100 is FALSE); the prover proves `40 ≤ 100`.
#[test]
fn forged_value_with_honest_commitment_is_refused_le() {
    drive_forgery(
        PREDICATE_ARITH_LE_NAME,
        predicate_le_witness(40, 100, fact(), test_blinding(), 4).expect("witness"),
        40,
        200,
        OS_FACT_COMMITMENT,
        1,
    );
}

/// `>`: token state commits to 5 (5 > 40 is FALSE); the prover proves `100 > 40`.
#[test]
fn forged_value_with_honest_commitment_is_refused_gt() {
    drive_forgery(
        PREDICATE_ARITH_GT_NAME,
        predicate_gt_witness(100, 40, fact(), test_blinding(), 4).expect("witness"),
        100,
        5,
        OS_FACT_COMMITMENT,
        1,
    );
}

/// `<`: token state commits to 200 (200 < 101 is FALSE); the prover proves `40 < 101`.
#[test]
fn forged_value_with_honest_commitment_is_refused_lt() {
    drive_forgery(
        PREDICATE_ARITH_LT_NAME,
        predicate_lt_witness(40, 101, fact(), test_blinding(), 4).expect("witness"),
        40,
        200,
        OS_FACT_COMMITMENT,
        1,
    );
}

/// `≠`: token state commits to 40 (40 ≠ 40 is FALSE); the prover proves `41 ≠ 40`.
#[test]
fn forged_value_with_honest_commitment_is_refused_neq() {
    drive_forgery(
        PREDICATE_ARITH_NEQ_NAME,
        predicate_neq_witness(41, 40, fact(), test_blinding(), 4).expect("witness"),
        41,
        40,
        NEQ_FACT_COMMITMENT,
        1,
    );
}

/// InRange: token state commits to 500 (10 ≤ 500 ≤ 100 is FALSE); the prover proves `10 ≤ 40 ≤ 100`.
#[test]
fn forged_value_with_honest_commitment_is_refused_inrange() {
    drive_forgery(
        PREDICATE_ARITH_INRANGE_NAME,
        predicate_inrange_witness(40, 10, 100, fact(), test_blinding(), 4).expect("witness"),
        40,
        500,
        IR_FACT_COMMITMENT,
        2,
    );
}
