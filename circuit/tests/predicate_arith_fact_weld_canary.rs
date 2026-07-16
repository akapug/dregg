//! THE VALUE↔FACT WELD CANARY — the falsifier for the `dregg-predicate-arith-ge::threshold-v1`
//! descriptor's binding between the number it compares and the fact commitment it presents.
//!
//! ## The statement under test
//!
//! The deployed descriptor's job is to prove ONE thing:
//!
//! > "the value covered by the fact commitment `pi[1]` (which the verifier sources from trusted
//! > token state) is `>= pi[0]`."
//!
//! That is a conjunction with a SHARED variable: `col0 >= threshold` **AND**
//! `col4 = commit(fact(col0), state_root)`. The second conjunct is what makes the first one *about*
//! token state. If nothing in the AIR relates `col4` to `col0`, the descriptor proves the halves
//! independently — "some value is `>= threshold`" and "here is a commitment I was handed" — which is
//! not the statement, and is forgeable by a prover who supplies a `col0` of its own choosing
//! alongside the honest, verifier-expected `col4`.
//!
//! ## The falsifier
//!
//! [`forged_value_with_honest_commitment_is_refused`] presents the honest, verifier-expected
//! commitment for a value that FAILS the predicate, while proving the predicate on a different value
//! of the prover's choosing. It is paired with [`honest_ge_still_proves_and_verifies`] so it can
//! never pass vacuously.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TID_P2, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::predicate_arith_witness::{
    FACT_COMMITMENT, FactBinding, PRED_WIDTH, PREDICATE_ARITH_NAME, predicate_arith_witness,
};
use dregg_circuit::refusal::{Outcome, classify};

const PREDICATE_SYM: u32 = 0x9E;
const TERM1: u32 = 0x11;
const TERM2: u32 = 0x22;
const STATE_ROOT: u32 = 0x57A7E;
const THRESHOLD: u64 = 40;

/// The value ACTUALLY committed in token state. Below the threshold — an honest prover cannot prove
/// the predicate about it. This is what the forgery must not be able to claim.
const TRUE_VALUE: u64 = 5;
/// The value the malicious prover substitutes into the compared column. It satisfies the comparison,
/// but token state says nothing about it.
const FORGED_VALUE: u64 = 100;

/// The fact identity under test — one honest world shared by every test here.
fn fact() -> FactBinding {
    FactBinding {
        predicate_sym: BabyBear::new(PREDICATE_SYM),
        term1: BabyBear::new(TERM1),
        term2: BabyBear::new(TERM2),
        state_root: BabyBear::new(STATE_ROOT),
    }
}

/// The honest, verifier-expected fact commitment covering `value` at `STATE_ROOT` — the SAME
/// production binding (`hash_fact(pred, &terms)` → `compute_arithmetic_fact_commitment`) a verifier
/// independently derives from trusted token state.
fn honest_commitment(value: u64) -> BabyBear {
    fact().commitment_of(BabyBear::from_u64(value))
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
/// Prove-THEN-verify is the faithful consumer posture: an attacker who gets a proof out of the
/// prover only wins if a verifier accepts it.
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

/// NON-VACUITY POLE — the honest path works: the prover's value genuinely satisfies the predicate
/// AND is the value token state commits to. The commitment is COMPUTED by the builder, and it
/// matches what a verifier independently derives from token state.
#[test]
fn honest_ge_still_proves_and_verifies() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    for height in [2usize, 4, 8] {
        // Token state commits to FORGED_VALUE (=100), and 100 >= 40 — the prover tells the truth
        // about the very value the commitment covers.
        let (trace, pis) = predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), height)
            .expect("honest witness builds");
        assert_eq!(
            pis[1],
            honest_commitment(FORGED_VALUE),
            "the builder COMPUTES the commitment a verifier derives from token state — \
             the fact commitment is an OUTPUT of the weld, not an argument"
        );
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest height-{height} witness must prove: {e}"));
        verify_vm_descriptor2(&desc, &proof, &pis)
            .unwrap_or_else(|e| panic!("honest height-{height} proof must verify: {e}"));
    }
}

/// **THE FALSIFIER.** Prove `FORGED_VALUE >= THRESHOLD` — true of `FORGED_VALUE`, and nothing to do
/// with token state — while pinning `col4` to the honest commitment covering `TRUE_VALUE` (=5),
/// which does NOT satisfy the predicate.
///
/// A verifier sourcing `pi[1]` from trusted token state sees exactly the commitment it expects and a
/// valid `>=` proof, and concludes "the committed value is >= 40". It is 5.
///
/// Note the attack is now expressed by HAND-FORGING the trace, not by calling the builder: the
/// welded API cannot express it (the commitment is computed FROM the compared value). Hand-forging
/// is the STRONGER form — it grants the attacker full control of every column, unconstrained by our
/// own builder's discipline, and asks the CIRCUIT to be the judge.
#[test]
fn forged_value_with_honest_commitment_is_refused() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");

    // What the verifier expects, sourced from trusted token state: the commitment covering the TRUE
    // value (5). The attacker does not forge this — it is public and honest.
    let expected_commitment = honest_commitment(TRUE_VALUE);

    // An honest, accepted proof about the FORGED value (100) — every comparison column is genuine.
    let (mut trace, mut pis) =
        predicate_arith_witness(FORGED_VALUE, THRESHOLD, fact(), 4).expect("witness builds");
    assert!(
        !rejects(&desc, &trace, &pis),
        "the pre-forgery witness must be accepted, else this canary proves nothing"
    );
    assert_ne!(
        pis[1], expected_commitment,
        "the honest witness for value 100 must not already carry value 5's commitment"
    );

    // THE FORGERY: swap col4 (and the pinned PI) to the honest commitment for the TRUE value,
    // leaving the comparison columns proving `100 >= 40` untouched. Every constraint mentioning
    // col0 still holds; the PI is exactly what the verifier expects.
    for row in &mut trace {
        row[FACT_COMMITMENT] = expected_commitment;
    }
    pis[1] = expected_commitment;

    assert!(
        rejects(&desc, &trace, &pis),
        "FORGERY ACCEPTED — the descriptor proved `value >= {THRESHOLD}` against the honest \
         commitment for value {TRUE_VALUE} (which is NOT >= {THRESHOLD}). The compared value and \
         the committed fact are UNRELATED: the predicate proof does not bind to token state."
    );
}

/// THE STRUCTURAL ANTI-FORK GATE — encode the weld as a CHECK on the DISPATCHED bytes rather than as
/// prose at the dispatch site (`descriptor_by_name.rs`). Production must serve a descriptor that
/// carries both weld legs and the full Lean-emitted 24-column layout.
#[test]
fn dispatched_descriptor_carries_both_weld_legs() {
    let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");
    assert_eq!(desc.name, PREDICATE_ARITH_NAME);
    assert_eq!(
        desc.trace_width, PRED_WIDTH,
        "the dispatched width must be the Lean-emitted PRED_WIDTH (24): 5 predicate columns + \
         5 fact witness columns + 2x7 chip lanes"
    );
    assert_eq!(
        desc.trace_width, 24,
        "PRED_WIDTH must itself be the Lean 24"
    );

    let poseidon2_lookups = desc
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        poseidon2_lookups, 2,
        "both weld legs must be present: leg 1 (hash_fact -> FACT_HASH) and \
         leg 2 (hash_2_to_1(FACT_HASH, STATE_ROOT) -> FACT_COMMITMENT)"
    );
}
