//! `DslComparisonRangeSoundnessResidual` — the decisive experiment (2026-07-17, board/lane-C),
//! and its CLOSURE (2026-07-17, lane dsl-range-soundness).
//!
//! QUESTION (from the `dregg-dsl/src/lib.rs` doc): the DSL's surviving comparison path — is a
//! field-wrapped negative difference UNSATISFIABLE, or can a wrapped value satisfy it?
//!
//! ANSWER, in two acts:
//!
//! **Act I — NOT SOUND (proven, then fixed).** `plonky3_runner::drive_inequality` hand-built a
//! "diff-le" `CircuitDescriptor` and proved it through the PRODUCTION interpreter
//! (`dregg_circuit::dsl::dsl_p3_air`). Its entire constraint system was:
//! ```text
//!     C1: bigger - smaller - diff == 0        (mod p — always satisfiable!)
//!     C2: indicator * (indicator - 1) == 0    (indicator is boolean)
//!     C3: indicator == 0
//! ```
//! NOTHING linked `indicator` to `diff`, and NO bit decomposition bounded `diff`. The comparison's
//! truth lived entirely in the HONEST WITNESS GENERATOR (native `ir_ok = smaller <= bigger`), which
//! volunteered a deliberately-invalid witness when the claim was false. A malicious prover declines
//! that courtesy: claiming `5 <= 3` with `diff = (3 - 5) mod p = p - 2`, `indicator = 0` satisfied
//! every constraint, and the production p3 prover AND verifier ACCEPTED the false statement. The
//! forgery used far-sub-30-bit operands, refuting the old in-file claim that capping operands to a
//! "30-bit range" made the encoding sound — capping the OPERANDS bounds nothing about a `diff`
//! column no constraint reads.
//!
//! **Act II — SOUND.** `diff-le` now carries a REAL range check (the deployed precedent:
//! `circuit/src/dsl/committed_threshold.rs` C4/C5, `derivation.rs` C17/C22): a 30-bit decomposition
//! of `diff` with every bit boolean-pinned, plus PI bindings tying `smaller`/`bigger` to the
//! publicly claimed operands. Because 30 boolean bits recompose to at most `2^30 - 1 < p`, the sum
//! cannot wrap, so C2 forces `diff ∈ [0, 2^30)` as an INTEGER — pinning the one degree of freedom
//! C1's mod-p subtraction left open. A false `smaller <= bigger` now has NO satisfying assignment:
//! its diff is `p - k`, which exceeds `2^30 - 1`. Rejection is the CONSTRAINT SYSTEM's verdict, not
//! the generator's confession.
//!
//! Note also (unrelated to `gen_air`): `Constraint::RangeCheck { diff_col, bit_col }` in
//! `dregg_dsl_runtime::AirConstraintSet` remains a TOPOLOGY DESCRIPTOR that proves nothing — its
//! only consumers are `air_runner.rs` (variant-shape match, then a NATIVE u64 re-derivation via
//! `check_le`) and structural token tests, and there is no `AirConstraintSet -> CircuitDescriptor`
//! converter in the repo. A single `bit_col` could not range-check a ~31-bit field difference
//! anyway. That is a SEPARATE named gap; this file speaks only for the lowering that reaches a real
//! prover.
//!
//! TEETH CONTRACT:
//! - `honest_le_accepts_through_production_p3` and `honest_max_diff_accepts` pin non-vacuity: the
//!   pipeline really proves, across the whole supported operand range.
//! - `rig_is_not_vacuous_inconsistent_diff_is_rejected` pins that the rig is not an
//!   accept-everything harness.
//! - `wrapped_negative_difference_forgery_is_rejected` is the ACT-II TOOTH — the forgery that once
//!   sailed through must now be UNSAT. This is the file's reason to exist. Do NOT delete it, and do
//!   NOT weaken it into a shape check.
//! - `non_binary_bits_cannot_launder_a_wrapped_diff` kills the obvious way around the tooth
//!   (recomposing `p - 2` out of non-boolean "bits"), pinning that C3 is load-bearing.
//! - `operands_must_match_the_public_inputs` pins the PI bindings: the proof is about the CLAIMED
//!   comparison, not some other pair the prover liked better.
//!
//! These tests drive the REAL `diff_le_descriptor()` exported from `plonky3_runner`. They used to
//! re-author a private copy of it, with a comment asking the next person to keep the copy in sync by
//! hand — i.e. the teeth could have gone on passing against a descriptor the harness no longer
//! proved. A soundness tooth pointed at a mirror of the thing it guards is not a tooth.

use dregg_circuit::dsl::circuit::DslCircuit;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_dsl_differential::plonky3_runner::{
    DIFF_RANGE_BITS, Verdict, diff_le_col, diff_le_descriptor, diff_le_row, prove_and_verify,
};
use dregg_dsl_differential::predicates::Requirement;

/// Round-trip an arbitrary (possibly adversarial) `diff-le` row against the public inputs
/// `[pi_smaller, pi_bigger]`. The p3 prover panics on an unsatisfiable trace (the harness catches
/// this the same way); treat a panic as rejection.
fn prove_diff_le_row(row: Vec<BabyBear>, pi_smaller: u64, pi_bigger: u64) -> Result<(), String> {
    let dsl = DslCircuit::new(diff_le_descriptor());
    let trace = vec![row.clone(), row];
    let pi = vec![
        BabyBear::from_u64(pi_smaller),
        BabyBear::from_u64(pi_bigger),
    ];
    let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_dsl_p3(&dsl, &trace, &pi)
    }));
    match proved {
        Ok(Ok(proof)) => verify_dsl_p3(&dsl, &proof, &pi).map_err(|e| format!("verify: {e}")),
        Ok(Err(e)) => Err(format!("prove: {e}")),
        Err(_) => Err("prove panicked (unsatisfiable trace)".to_string()),
    }
}

/// Claim `smaller <= bigger` with the witness `diff`, decomposed by the harness's own row builder.
fn prove_diff_le(smaller: u64, bigger: u64, diff: BabyBear) -> Result<(), String> {
    prove_diff_le_row(diff_le_row(smaller, bigger, diff), smaller, bigger)
}

/// Non-vacuity pin: the honest lowering of a TRUE `3 <= 5` proves and verifies through the
/// production p3 interpreter.
#[test]
fn honest_le_accepts_through_production_p3() {
    prove_diff_le(3, 5, BabyBear::from_u64(2))
        .expect("honest 3 <= 5 must prove+verify through production dsl_p3_air");
}

/// Non-vacuity at the RANGE EDGE: the largest diff the 30-bit decomposition must accept
/// (`0 <= 2^30 - 1`) still proves. Pins that the range check was not tightened into rejecting
/// honest claims — a range check that rejects everything is "sound" and useless.
#[test]
fn honest_max_diff_accepts() {
    let max_diff = (1u64 << DIFF_RANGE_BITS) - 1;
    prove_diff_le(0, max_diff, BabyBear::from_u64(max_diff))
        .expect("the largest in-range honest diff must still prove");
}

/// NON-VACUITY of the forgery rig itself: `prove_diff_le` is NOT an accept-everything harness. An
/// inconsistent `diff` (claiming `3 <= 5` with `diff = 7`, violating C1 `bigger - smaller - diff ==
/// 0`) IS rejected. So the rejections below are real properties of the constraint system.
#[test]
fn rig_is_not_vacuous_inconsistent_diff_is_rejected() {
    let res = prove_diff_le(3, 5, BabyBear::from_u64(7)); // 5 - 3 != 7
    assert!(
        res.is_err(),
        "the rig must reject a diff violating C1; if this passes, the teeth below prove nothing"
    );
}

/// Harness-verdict pin: the harness REJECTS a false `5 <= 3`. Post-fix this holds for the RIGHT
/// reason — the constraints are unsatisfiable, so the prover cannot find a witness at all (the
/// tooth below proves that directly).
#[test]
fn honest_false_le_is_rejected_by_harness() {
    let verdict = prove_and_verify(&[Requirement::LessEqualU64(5, 3)])
        .expect("inequality shape is expressible");
    assert!(
        matches!(verdict, Verdict::Reject),
        "harness must reject a false 5 <= 3, got {verdict:?}"
    );
}

/// ⚑ THE TOOTH — `DslComparisonRangeSoundnessResidual`, closed.
///
/// Claim `5 <= 3` with the field-wrapped witness `diff = (3 - 5) mod p = p - 2`. This satisfies C1
/// (mod-p subtraction) and once satisfied the ENTIRE system, so the production p3 prover+verifier
/// ACCEPTED the false statement. Now the 30-bit decomposition bounds `diff` to `[0, 2^30)`, and
/// `p - 2 ~= 2^31` is not in that interval — no assignment of the bit columns recomposes to it, so
/// the forgery is UNSAT.
///
/// This test was born as a characterization pin asserting the forgery WAS accepted; the fix turned
/// it red, which was its designed signal, and it is now flipped into this rejection tooth. If it
/// ever goes red again, the range check regressed and `5 <= 3` is provable — do not "fix" it by
/// deleting it or by relaxing the assertion.
#[test]
fn wrapped_negative_difference_forgery_is_rejected() {
    let wrapped = BabyBear::new(BABYBEAR_P - 2); // (3 - 5) mod p
    let res = prove_diff_le(5, 3, wrapped);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: the wrapped-diff forgery of `5 <= 3` was ACCEPTED ({res:?}). \
         The diff range check is gone or defeated; a false comparison is provable."
    );
}

/// The obvious way around the tooth above: keep the wrapped `diff = p - 2` (satisfying C1) and
/// recompose it out of NON-BOOLEAN "bits" — put `p - 2` in bit column 0 and zero the rest, so C2's
/// `sum(bit[i] * 2^i) == diff` holds exactly. Only C3 (`bit * (bit - 1) == 0`) stands in the way.
///
/// Pins that the binary constraints are LOAD-BEARING, not decoration: without them the
/// recomposition bounds nothing at all and the forgery walks straight back in.
#[test]
fn non_binary_bits_cannot_launder_a_wrapped_diff() {
    let wrapped = BabyBear::new(BABYBEAR_P - 2);
    let mut row = vec![BabyBear::ZERO; diff_le_col::WIDTH];
    row[diff_le_col::SMALLER] = BabyBear::from_u64(5);
    row[diff_le_col::BIGGER] = BabyBear::from_u64(3);
    row[diff_le_col::DIFF] = wrapped;
    // C1 holds: 3 - 5 - (p - 2) == 0 (mod p). C2 holds: (p - 2) * 2^0 == p - 2.
    row[diff_le_col::diff_bit(0)] = wrapped;

    let res = prove_diff_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: a wrapped diff recomposed from NON-BINARY bits was ACCEPTED \
         ({res:?}). The Binary constraints on the decomposition columns are not being enforced, \
         so the range check bounds nothing."
    );
}

/// The PI bindings are load-bearing: a prover cannot prove some other, true comparison and pass it
/// off as the claimed one. Here the trace honestly proves `3 <= 5` (every constraint satisfied)
/// while the PUBLIC claim is `5 <= 3` — the boundary bindings must reject it.
///
/// Without them, `smaller`/`bigger` would be free columns and the public inputs pure decoration:
/// every false comparison would be forgeable by simply proving its converse.
#[test]
fn operands_must_match_the_public_inputs() {
    // An internally-consistent, honest proof of `3 <= 5`...
    let row = diff_le_row(3, 5, BabyBear::from_u64(2));
    // ...offered against the public claim `5 <= 3`.
    let res = prove_diff_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: a proof of `3 <= 5` was accepted against the public claim `5 <= 3` \
         ({res:?}). The operand columns are not pinned to the public inputs."
    );
}
