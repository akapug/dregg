//! `DslComparisonRangeSoundnessResidual` — the decisive experiment (2026-07-17, board/lane-C), its
//! CLOSURE (2026-07-17, lane dsl-range-soundness), and the closure of the FALLBACK the closure left
//! behind (2026-07-17, lane dsl-2p30-fallback).
//!
//! QUESTION (from the `dregg-dsl/src/lib.rs` doc): the DSL's surviving comparison path — is a
//! field-wrapped negative difference UNSATISFIABLE, or can a wrapped value satisfy it?
//!
//! ANSWER, in three acts:
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
//! every constraint, and the production p3 prover AND verifier ACCEPTED the false statement.
//!
//! **Act II — SOUND, ON `[0, 2^30)`.** `diff-le` got a REAL range check: a 30-bit decomposition of
//! `diff`, every bit boolean-pinned, plus PI bindings tying `smaller`/`bigger` to the claimed
//! operands. 30 boolean bits recompose to at most `2^30 - 1 < p`, so the sum cannot wrap and the
//! range check forces `diff ∈ [0, 2^30)` as an INTEGER. The forgery went UNSAT.
//!
//! **Act III — SOUND, ON ALL OF u64.** Act II bought soundness with a HOLE: operands `>= 2^30`
//! short-circuited to `prove_trivial(ir_ok)` — no circuit, verdict == the native oracle's own
//! answer. For `u64::MAX` and friends (common in the predicate suite) the "Plonky3 vote" was the
//! oracle marking its own homework — Act I's disease, quarantined rather than cured, and with no
//! tooth on it. The hole could NOT be closed by widening the decomposition:
//!
//!   - `2^30 - 1 = 1073741823 < p = 2013265921`, but `2^31 - 1 = 2147483647 > p`. So 30 bits was
//!     already THE CEILING for a single-element decomposition, not a cautious choice.
//!   - Worse, `BabyBear::from_u64` reduces mod p: `from_u64(u64::MAX) = 1172168162` and
//!     `from_u64(BABYBEAR_P) = 0`. Operands `>= p` were never in their columns at all. That is the
//!     EMBEDDING, and no range check reaches it.
//!
//! So the gadget stopped asking one field element to carry a u64. `u64-le` splits each operand into
//! four base-`2^16` limbs (PI-bound, each range-checked by 16 boolean bits) and subtracts with a
//! borrow chain, requiring the top borrow to be zero. Every intermediate stays under `2^18` — ~13
//! bits of headroom under `p`, versus Act II's one — so each field equation implies its INTEGER
//! counterpart. The fallback is DELETED, and `>= 2^30` operands are now decided by constraints.
//!
//! Note also (unrelated to `gen_air`): `Constraint::RangeCheck { diff_col, bit_col }` in
//! `dregg_dsl_runtime::AirConstraintSet` remains a TOPOLOGY DESCRIPTOR that proves nothing — its
//! only consumers are `air_runner.rs` (variant-shape match, then a NATIVE u64 re-derivation via
//! `check_le`) and structural token tests, and there is no `AirConstraintSet -> CircuitDescriptor`
//! converter in the repo. That is a SEPARATE named gap; this file speaks only for the lowering that
//! reaches a real prover. So is `DslEqualityOperandAliasingResidual` — `drive_equality_u64` /
//! `drive_nonequality_u64` still carry the `2^30` oracle cutoff that inequalities no longer do.
//! This file speaks for `<=`/`>=` only.
//!
//! TEETH CONTRACT:
//! - `honest_le_accepts_through_production_p3`, `honest_max_diff_accepts` and
//!   `honest_u64_max_operands_accept` pin non-vacuity: the pipeline really proves, across the whole
//!   u64 operand range.
//! - `rig_is_not_vacuous_inconsistent_diff_is_rejected` pins that the rig is not an
//!   accept-everything harness.
//! - `wrapped_negative_difference_forgery_is_rejected` is the ACT-II TOOTH — the forgery that once
//!   sailed through must be UNSAT. Do NOT delete it, and do NOT weaken it into a shape check.
//! - `forged_top_borrow_cannot_prove_a_false_comparison` and
//!   `out_of_range_diff_limb_cannot_launder_a_borrow` are its `u64-le` descendants: the two ways to
//!   lie to a borrow chain.
//! - `huge_operands_are_decided_by_constraints_not_the_oracle` and
//!   `modulus_aliased_operands_are_decided_by_constraints` are the ACT-III TEETH — the
//!   `>= 2^30` path must be a real circuit, and immune to the mod-p aliasing that killed the naive
//!   widening.
//! - `every_operand_takes_the_circuit_never_the_oracle` is the one that GUARDS THE DELETION. The
//!   teeth above drive the descriptor directly, so a re-introduced short-circuit in
//!   `drive_inequality` would leave them all green; and no `Verdict` assertion can catch it either,
//!   since the oracle returns the right answer — that is what made the fallback undetectable in the
//!   first place. This asserts the PATH.
//! - `non_binary_bits_cannot_launder_an_out_of_range_limb` kills the obvious way around the range
//!   checks, pinning that the Binary constraints are load-bearing.
//! - `operands_must_match_the_public_inputs` pins the PI bindings: the proof is about the CLAIMED
//!   comparison, not some other pair the prover liked better.
//!
//! These tests drive the REAL `u64_le_descriptor()` exported from `plonky3_runner`. They used to
//! re-author a private copy of it, with a comment asking the next person to keep the copy in sync by
//! hand — i.e. the teeth could have gone on passing against a descriptor the harness no longer
//! proved. A soundness tooth pointed at a mirror of the thing it guards is not a tooth.
//!
//! ## Mutation matrix (2026-07-17, lane dsl-2p30-fallback)
//!
//! Every tooth here was PROVEN by deleting the constraint it names from `u64_le_descriptor()` and
//! watching it go red. Each row was verified; each mutation was reverted.
//!
//! | mutation                              | caught by                                            |
//! |---------------------------------------|------------------------------------------------------|
//! | re-add the `>= 2^30` oracle fallback  | `every_operand_takes_the_circuit_never_the_oracle`    |
//! | delete F (top borrow == 0)            | `forged_top_borrow_...` v1, `honest_false_le_...`, +2 |
//! | delete R3 (diff limb recomposition)   | `forged_top_borrow_...` v3                            |
//! | delete `Binary` on the diff bits      | `non_binary_bits_cannot_launder_an_out_of_range_limb` |
//! | delete `Binary` on the borrows        | `non_boolean_borrow_cannot_buy_back_the_modulus`      |
//! | delete R1/R2 (operand recomposition)  | `non_canonical_operand_limbs_cannot_name_a_false_claim` |
//! | delete the PI bindings                | `operands_must_match_the_public_inputs`               |
//!
//! THE MATRIX EARNED ITS KEEP THREE TIMES, and the lesson is worth more than the table. Three teeth
//! in the first draft of this file named a constraint they were not touching — the row under attack
//! was being rejected by a DIFFERENT constraint, so the named one could be deleted with the test
//! still green. Two were mis-documented; the third exposed a threat the lane had not modelled at all
//! (the non-boolean borrow above), and the forgery for it was accepted by the real prover the moment
//! the canary removed that constraint. A tooth that has never been watched failing is a tooth
//! pointed at an unknown target. If you add a constraint here, add its canary row.

use dregg_circuit::dsl::circuit::DslCircuit;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_dsl_differential::plonky3_runner::{
    InequalityPath, LIMB_BASE, N_LIMBS, Verdict, drive_inequality_traced, prove_and_verify,
    u64_le_borrow_chain, u64_le_col, u64_le_descriptor, u64_le_public_inputs, u64_le_row,
    u64_le_row_from,
};
use dregg_dsl_differential::predicates::Requirement;

/// Round-trip an arbitrary (possibly adversarial) `u64-le` row against the public inputs for the
/// claim `pi_smaller <= pi_bigger`. The p3 prover panics on an unsatisfiable trace (the harness
/// catches this the same way); treat a panic as rejection.
fn prove_u64_le_row(row: Vec<BabyBear>, pi_smaller: u64, pi_bigger: u64) -> Result<(), String> {
    let dsl = DslCircuit::new(u64_le_descriptor());
    let trace = vec![row.clone(), row];
    let pi = u64_le_public_inputs(pi_smaller, pi_bigger);
    let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_dsl_p3(&dsl, &trace, &pi)
    }));
    match proved {
        Ok(Ok(proof)) => verify_dsl_p3(&dsl, &proof, &pi).map_err(|e| format!("verify: {e}")),
        Ok(Err(e)) => Err(format!("prove: {e}")),
        Err(_) => Err("prove panicked (unsatisfiable trace)".to_string()),
    }
}

/// Claim `smaller <= bigger` with the honest borrow-chain witness.
fn prove_u64_le(smaller: u64, bigger: u64) -> Result<(), String> {
    prove_u64_le_row(u64_le_row(smaller, bigger), smaller, bigger)
}

/// Non-vacuity pin: the honest lowering of a TRUE `3 <= 5` proves and verifies through the
/// production p3 interpreter.
#[test]
fn honest_le_accepts_through_production_p3() {
    prove_u64_le(3, 5).expect("honest 3 <= 5 must prove+verify through production dsl_p3_air");
}

/// Non-vacuity at the OLD range edge: the largest diff the retired 30-bit gadget could accept
/// (`0 <= 2^30 - 1`) still proves. Pins that widening to limbs did not lose the ground Act II held.
#[test]
fn honest_max_diff_accepts() {
    let max_diff = (1u64 << 30) - 1;
    prove_u64_le(0, max_diff).expect("the largest Act-II-era honest diff must still prove");
}

/// Non-vacuity at the REAL edge: `u64::MAX - 1 <= u64::MAX`, and `0 <= u64::MAX`. These operands
/// are the ones that used to skip the circuit entirely. A range check that rejects honest claims is
/// "sound" and useless, so pin that the widened gadget still ACCEPTS at the top of the domain.
#[test]
fn honest_u64_max_operands_accept() {
    prove_u64_le(u64::MAX - 1, u64::MAX)
        .expect("honest u64::MAX - 1 <= u64::MAX must prove in-circuit");
    prove_u64_le(0, u64::MAX).expect("honest 0 <= u64::MAX must prove in-circuit");
    prove_u64_le(u64::MAX, u64::MAX).expect("honest u64::MAX <= u64::MAX must prove in-circuit");
}

/// NON-VACUITY of the forgery rig itself: `prove_u64_le_row` is NOT an accept-everything harness.
/// An inconsistent difference limb (claiming `3 <= 5` but witnessing `d_limb(0) = 7` instead of 2,
/// violating B_0) IS rejected. So the rejections below are real properties of the constraint system.
#[test]
fn rig_is_not_vacuous_inconsistent_diff_is_rejected() {
    let (mut diff_limbs, borrows) = u64_le_borrow_chain(3, 5);
    diff_limbs[0] = 7; // 5 - 3 != 7
    let row = u64_le_row_from(3, 5, diff_limbs, borrows);
    let res = prove_u64_le_row(row, 3, 5);
    assert!(
        res.is_err(),
        "the rig must reject a diff limb violating B_0; if this passes, the teeth below prove nothing"
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

/// ⚑ THE ACT-II TOOTH — `DslComparisonRangeSoundnessResidual`, closed.
///
/// The original forgery: claim `5 <= 3` and witness the field-wrapped difference
/// `(3 - 5) mod p = p - 2`. Against the retired `diff-le` this satisfied C1's mod-p subtraction and
/// once satisfied the ENTIRE system, so the production p3 prover+verifier ACCEPTED it.
///
/// `u64-le` has no single `diff` column to wrap, so the forgery is re-expressed in the shape the
/// new gadget offers: put `p - 2` where the low difference limb goes and zero the rest. Every path
/// to it is blocked — `p - 2` is not `< 2^16`, so no boolean 16-bit decomposition recomposes to it.
///
/// This test was born as a characterization pin asserting the forgery WAS accepted; the fix turned
/// it red, which was its designed signal, and it is now a rejection tooth. If it ever goes red
/// again, a false `5 <= 3` is provable — do not "fix" it by deleting it or relaxing the assertion.
#[test]
fn wrapped_negative_difference_forgery_is_rejected() {
    let mut row = u64_le_row(5, 3);
    // The wrapped difference, placed in the low difference limb, with the borrow chain forged flat.
    row[u64_le_col::d_limb(0)] = BabyBear::new(BABYBEAR_P - 2);
    for j in 0..N_LIMBS {
        row[u64_le_col::borrow(j)] = BabyBear::ZERO;
    }
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: the wrapped-diff forgery of `5 <= 3` was ACCEPTED ({res:?}). \
         The limb range checks are gone or defeated; a false comparison is provable."
    );
}

/// ⚑ THE ACT-II TOOTH, in the borrow chain's own terms — and a demonstration that the forger has
/// NOWHERE to go. The honest chain for `5 <= 3` ends with `borrow(3) = 1`; that borrow IS the
/// statement "3 < 5". Both escape routes are closed, by DIFFERENT constraints:
///
///   - **Keep the honest chain** (`borrow(3) = 1`): every B_j is satisfied and only **F** objects.
///     This variant isolates F — it is the only one of these teeth that goes red if F is deleted.
///   - **Zero the top borrow** and keep the honest difference limbs: now **B_3** objects, because
///     the `2^16 * borrow(3)` term it was relying on is gone. To repair B_3 the prover would need
///     `d_limb(3) = -1 = p - 1`, which the **range check** (R3 + Binary) refuses. So the forgery
///     needs all three constraint families to fail at once.
///
/// (Written after a mutation canary: an earlier version of this test asserted it pinned F while
/// B_3 was quietly doing the rejecting — it stayed GREEN with F deleted. A tooth that names the
/// wrong constraint is a tooth pointed at nothing.)
#[test]
fn forged_top_borrow_cannot_prove_a_false_comparison() {
    let (diff_limbs, borrows) = u64_le_borrow_chain(5, 3);
    assert_eq!(
        borrows[N_LIMBS - 1],
        1,
        "rig check: the honest chain for the FALSE `5 <= 3` must end in a top borrow"
    );

    // Variant 1 — the honest chain. Only F stands between this and an accepted `5 <= 3`.
    let row = u64_le_row_from(5, 3, diff_limbs, borrows);
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `5 <= 3` was ACCEPTED carrying its honest top borrow ({res:?}). \
         Constraint F (no borrow escapes the top limb) is not being enforced, so the borrow chain \
         computes the comparison and then nothing reads the answer."
    );

    // Variant 2 — the top borrow forged to zero. B_3 objects; repairing it needs an out-of-range
    // difference limb, which the range check refuses.
    let mut forged = borrows;
    forged[N_LIMBS - 1] = 0;
    let row = u64_le_row_from(5, 3, diff_limbs, forged);
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `5 <= 3` was ACCEPTED with a forged zero top borrow ({res:?})."
    );

    // Variant 3 — the repair B_3 would demand: d_limb(3) = p - 1. Only the range check kills this.
    let mut repaired = diff_limbs;
    repaired[N_LIMBS - 1] = BABYBEAR_P as u64 - 1;
    let row = u64_le_row_from(5, 3, repaired, forged);
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `5 <= 3` was ACCEPTED with the top borrow forged away and B_3 \
         repaired by a wrapped difference limb ({res:?}). The R3 range check on the difference \
         limbs is not bounding them."
    );
}

/// The other way to lie to a borrow chain: take a borrow's worth of value without DECLARING the
/// borrow. Claim `5 <= 3` with a flat-zero chain and `d_limb(0) = 3 - 5 + 2^16` — the value the
/// honest chain produces at limb 0, but with `borrow(0) = 0` so nothing pays for it.
///
/// Pins that the **B_j borrow accounting is load-bearing**: the `2^16 * borrow(j)` term is the only
/// thing that can fund a limb-0 result larger than `b_0`, so a borrow cannot be smuggled.
///
/// (Named for what it actually pins, after a mutation canary: this test's earlier docstring claimed
/// the R3 range check, but deleting R3 left it GREEN — B_0 was doing all the work. R3's own tooth is
/// `forged_top_borrow_cannot_prove_a_false_comparison`'s variant 3.)
#[test]
fn a_borrow_must_be_declared_not_smuggled_into_a_diff_limb() {
    let mut diff_limbs = [0u64; N_LIMBS];
    // The value an honest borrow would have produced — but with no borrow declared to pay for it.
    diff_limbs[0] = 3 + LIMB_BASE - 5;
    let row = u64_le_row_from(5, 3, diff_limbs, [0u64; N_LIMBS]);
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `5 <= 3` was ACCEPTED with a borrow laundered into a diff limb \
         ({res:?}). The B_0 borrow accounting is not being enforced."
    );

    // The direct form: an explicitly out-of-range difference limb, unpaid for.
    let mut diff_limbs = [0u64; N_LIMBS];
    diff_limbs[0] = LIMB_BASE + 4; // >= 2^16: no 16-bit boolean decomposition reaches it
    let row = u64_le_row_from(5, 3, diff_limbs, [0u64; N_LIMBS]);
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: an out-of-range difference limb was ACCEPTED ({res:?})."
    );
}

/// ⚑ THE SHARPEST TOOTH IN THIS FILE — and the one this lane did not see coming.
///
/// Found by a mutation canary: deleting `Binary { col: borrow(j) }` from the descriptor left ALL
/// the other teeth green. That is not a missing test, it is a missing THREAT MODEL — so the floor
/// was attacked directly, and it fell.
///
/// A non-boolean borrow is not merely "an invalid witness"; it is a purchase order. `borrow(j)`
/// enters B_j multiplied by `2^16`, so a borrow of `p - 30719` injects `-2^16 * 30719 ≡ p - ...`
/// into the chain — letting the prover buy back exactly `p` and land every difference limb inside
/// `[0, 2^16)`. Concretely, for the FALSE claim `5 <= 3`:
///
/// ```text
///     d_limb  = [65535, 30719, 0, 0]     — all genuinely 16-bit, so R3 is HAPPY
///     borrow  = [p - 30719, 0, 0, 0]     — borrow(3) = 0, so F is HAPPY
/// ```
/// because `65535 + 2 + 2^16 * 30719 = 2013265921 = p ≡ 0`. Every B_j holds, every difference limb
/// range-checks, the top borrow is zero, and the operands are the honestly PI-bound ones. The
/// ONLY constraint standing between this and a proof of `5 <= 3` is the booleanity of `borrow(0)`.
///
/// This is exactly the wrap the whole gadget exists to prevent, re-entering through the one column
/// the no-wrap argument in `u64_le_descriptor` quietly assumed was in `{0, 1}`. Pins that the
/// assumption is ENFORCED. If this goes red, `5 <= 3` is provable — verify with the witness above
/// before believing any claim that the failure is spurious.
#[test]
fn non_boolean_borrow_cannot_buy_back_the_modulus() {
    // Rig check: this witness must satisfy every constraint EXCEPT the borrow booleanity, or the
    // test is pinning something weaker than it claims.
    let diff_limbs = [65535u64, 30719, 0, 0];
    let borrows = [BABYBEAR_P as u64 - 30719, 0, 0, 0];
    assert_eq!(
        (65535u128 + 2 + (1u128 << 16) * 30719) % BABYBEAR_P as u128,
        0,
        "rig check: the forgery's arithmetic must actually close the chain mod p"
    );
    assert!(
        diff_limbs.iter().all(|&d| d < LIMB_BASE),
        "rig check: every forged difference limb must be in range, or R3 rejects it and this test \
         proves nothing about the borrow columns"
    );
    assert_eq!(
        borrows[N_LIMBS - 1],
        0,
        "rig check: the forgery must satisfy F, or F rejects it and this test proves nothing"
    );

    let row = u64_le_row_from(5, 3, diff_limbs, borrows);
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `5 <= 3` was ACCEPTED via a non-boolean borrow buying back the \
         modulus ({res:?}). The Binary constraints on the borrow columns are not being enforced, \
         and the borrow chain's no-wrap argument — which assumes borrow ∈ {{0,1}} — is void."
    );
}

/// ⚑ THE ACT-III TOOTH — the `>= 2^30` fallback, closed and ASSERTED.
///
/// These operands took the deleted `prove_trivial(ir_ok)` path: no circuit was built and the
/// verdict was the native-u64 oracle's own answer. Pin that they are now decided by the CONSTRAINT
/// SYSTEM — a false `u64::MAX <= 5` is UNSAT at the descriptor level, which the oracle path could
/// never have told us.
///
/// The tooth is the descriptor-level assertion, not the harness verdict: `prove_and_verify` would
/// report `Reject` either way (that is precisely why the fallback needed one).
#[test]
fn huge_operands_are_decided_by_constraints_not_the_oracle() {
    // Non-vacuity first: the TRUE claim at these operands proves in-circuit.
    prove_u64_le(5, u64::MAX).expect("honest 5 <= u64::MAX must prove in-circuit");

    // The false claim, with the honest (and unique) witness: UNSAT.
    let res = prove_u64_le(u64::MAX, 5);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `u64::MAX <= 5` was ACCEPTED ({res:?})."
    );

    // And with the top borrow forged away — the only degree of freedom a prover has.
    let (diff_limbs, mut borrows) = u64_le_borrow_chain(u64::MAX, 5);
    borrows[N_LIMBS - 1] = 0;
    let row = u64_le_row_from(u64::MAX, 5, diff_limbs, borrows);
    let res = prove_u64_le_row(row, u64::MAX, 5);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `u64::MAX <= 5` was ACCEPTED with a forged top borrow ({res:?}). \
         Operands >= 2^30 are not being decided by the constraint system."
    );

    // The harness agrees.
    let verdict = prove_and_verify(&[Requirement::LessEqualU64(u64::MAX, 5)])
        .expect("inequality shape is expressible");
    assert!(
        matches!(verdict, Verdict::Reject),
        "harness must reject a false u64::MAX <= 5, got {verdict:?}"
    );
}

/// ⚑ THE ACT-III TOOTH, aimed at the exact rock the naive widening would have foundered on.
///
/// `BabyBear::from_u64` reduces mod p, so a single-element encoding puts `BABYBEAR_P` and `0` in
/// the SAME column value. Had the fix widened `DIFF_RANGE_BITS` instead of moving to limbs, the
/// claim `BABYBEAR_P <= 0` would have been proved by the operands aliasing to `0 <= 0` — a false
/// statement with a perfectly honest-looking witness, and no range check anywhere near it.
///
/// The limb encoding is injective on u64, so these operands are distinct in the circuit and the
/// claim is UNSAT. Pins that the widening was done at the ENCODING and not merely at the bit count.
#[test]
fn modulus_aliased_operands_are_decided_by_constraints() {
    let p = BABYBEAR_P as u64;
    assert_eq!(
        BabyBear::from_u64(p).as_u32(),
        BabyBear::from_u64(0).as_u32(),
        "rig check: p and 0 must be indistinguishable to the single-element embedding — that is \
         the aliasing this tooth is about"
    );

    // p <= 0 is FALSE. If the operands alias, the circuit sees `0 <= 0` and accepts.
    let res = prove_u64_le(p, 0);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `BABYBEAR_P <= 0` was ACCEPTED ({res:?}). The operands are \
         aliasing mod p — the limb encoding is not injective, or is not what is PI-bound."
    );

    // 2^32 <= 0 is FALSE, and 2^32 is above every single-limb boundary.
    let res = prove_u64_le(1u64 << 32, 0);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: `2^32 <= 0` was ACCEPTED ({res:?})."
    );

    // Non-vacuity: the true direction proves.
    prove_u64_le(0, p).expect("honest 0 <= BABYBEAR_P must prove in-circuit");
}

/// ⚑ THE ACT-III STRUCTURAL TOOTH — the one that actually guards the DELETED fallback.
///
/// Every other tooth here drives `u64_le_descriptor()` directly, so none of them would notice if a
/// short-circuit were re-introduced into `drive_inequality`: the harness would go on returning the
/// right `Verdict` by asking the oracle, exactly as it did before this lane. And the harness-level
/// assertions cannot tell the difference either — `prove_trivial(u64::MAX <= 5)` rejects too. That
/// indistinguishability IS the disease; `InequalityPath` is the instrument for it.
///
/// Pins that across the operand domain — below the old cutoff, exactly at it, above it, at the
/// modulus, and at the u64 ceiling — the verdict comes from a CIRCUIT. If this goes red, the
/// harness is marking its own homework somewhere and its Plonky3 agreement vote is a fiction for
/// those operands.
#[test]
fn every_operand_takes_the_circuit_never_the_oracle() {
    let cutoff = 1u64 << 30; // the retired INEQUALITY_SAFE_RANGE
    let p = BABYBEAR_P as u64;
    let interesting = [
        0,
        1,
        5,
        cutoff - 1, // last operand the Act-II gadget handled
        cutoff,     // first operand that used to skip the circuit
        cutoff + 1,
        p - 1,
        p, // aliases to 0 under a single-element embedding
        p + 1,
        1u64 << 32,
        u64::MAX - 1,
        u64::MAX,
    ];

    for &a in &interesting {
        for &b in &interesting {
            let (verdict, path) = drive_inequality_traced(a, b);
            assert_eq!(
                path,
                InequalityPath::Circuit,
                "SOUNDNESS REGRESSION: `{a} <= {b}` was decided by the ORACLE, not a circuit. \
                 The 2^30 fallback (or a new one) is back: for these operands the harness is \
                 reporting the native-u64 answer as if a constraint system had produced it."
            );
            // And the circuit agrees with the truth — a circuit that decided WRONGLY would be a
            // worse failure than the oracle path, so pin both halves together.
            let expect_accept = a <= b;
            assert_eq!(
                matches!(verdict, Verdict::Accept),
                expect_accept,
                "the u64-le circuit disagreed with the truth on `{a} <= {b}`: got {verdict:?}"
            );
        }
    }
}

/// The obvious way around the range checks: recompose an out-of-range limb out of NON-BOOLEAN
/// "bits" — put the whole value in bit column 0 and zero the rest, so R3's
/// `sum(bit[i] * 2^i) == limb` holds exactly. Only the Binary constraints stand in the way.
///
/// Pins that they are LOAD-BEARING, not decoration: without them the recompositions bound nothing
/// at all, every limb is free, and the borrow chain's integer argument collapses.
#[test]
fn non_binary_bits_cannot_launder_an_out_of_range_limb() {
    // Claim `5 <= 3` with a flat borrow chain and `d_limb(0) = p - 2` (satisfying B_0 mod p),
    // recomposed from a single non-boolean "bit".
    let wrapped = BabyBear::new(BABYBEAR_P - 2);
    let mut row = u64_le_row(5, 3);
    for j in 0..N_LIMBS {
        row[u64_le_col::borrow(j)] = BabyBear::ZERO;
        row[u64_le_col::d_limb(j)] = BabyBear::ZERO;
        for i in 0..16 {
            row[u64_le_col::d_bit(j, i)] = BabyBear::ZERO;
        }
    }
    row[u64_le_col::d_limb(0)] = wrapped;
    // R3 holds for limb 0: (p - 2) * 2^0 == p - 2. Only Binary on d_bit(0, 0) objects.
    row[u64_le_col::d_bit(0, 0)] = wrapped;

    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: an out-of-range limb recomposed from NON-BINARY bits was ACCEPTED \
         ({res:?}). The Binary constraints on the decomposition columns are not being enforced, \
         so the range checks bound nothing."
    );
}

/// R1/R2 — the OPERAND limb range checks — are what make the 8 public inputs NAME A u64.
///
/// These are the only constraints here not aimed at a lying prover: `u64_le_public_inputs` publishes
/// canonical (`< 2^16`) limbs, and the PI bindings pin the columns to them, so within the harness a
/// prover has no freedom to abuse. They matter because the descriptor is a STANDALONE object whose
/// soundness should not rest on its caller's good manners.
///
/// The witness that shows the tooth is real: publish `smaller` limbs `[p - 1, 0, 0, 0]` and
/// `bigger` limbs `[0, 0, 0, 0]`. Read as integers — the only reading under which the gadget claims
/// anything — that is `2013265920 <= 0`, FALSE. But `-(p - 1) ≡ 1`, so `d_limb(0) = 1` with a
/// flat-zero borrow chain satisfies EVERY B_j, every difference limb is in range, and the top borrow
/// is zero. Without R1 the production prover and verifier accept it. R1 rejects it because `p - 1`
/// is not the sum of 16 boolean bits.
///
/// (Written after a mutation canary: an earlier version of this test used a `2^16 + 3` limb and
/// stayed GREEN with R1/R2 deleted — B_0 was rejecting it, not the range check. Third time in this
/// file that a tooth named a constraint it was not touching. Do not delete R1/R2 on the grounds
/// that the prover cannot reach them.)
#[test]
fn non_canonical_operand_limbs_cannot_name_a_false_claim() {
    let dsl = DslCircuit::new(u64_le_descriptor());

    // The statement: smaller = [p-1, 0, 0, 0], bigger = [0, 0, 0, 0] — i.e. `2013265920 <= 0`.
    let mut pi = u64_le_public_inputs(0, 0);
    pi[u64_le_col::S_LIMB_START] = BabyBear::new(BABYBEAR_P - 1);

    // The prover's witness, which satisfies the borrow chain exactly.
    let mut row = u64_le_row(0, 0);
    row[u64_le_col::s_limb(0)] = BabyBear::new(BABYBEAR_P - 1);
    row[u64_le_col::d_limb(0)] = BabyBear::ONE;
    row[u64_le_col::d_bit(0, 0)] = BabyBear::ONE;

    let trace = vec![row.clone(), row];
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_dsl_p3(&dsl, &trace, &pi).and_then(|proof| verify_dsl_p3(&dsl, &proof, &pi))
    }));
    assert!(
        !matches!(res, Ok(Ok(()))),
        "SOUNDNESS REGRESSION: the false claim `2013265920 <= 0` was ACCEPTED via a non-canonical \
         operand limb ({res:?}). R1/R2 do not bound the operand limbs, so the public inputs no \
         longer name a unique (smaller, bigger) and the gadget's meaning is not what its doc says."
    );
}

/// The PI bindings are load-bearing: a prover cannot prove some other, true comparison and pass it
/// off as the claimed one. Here the trace honestly proves `3 <= 5` (every constraint satisfied)
/// while the PUBLIC claim is `5 <= 3` — the boundary bindings must reject it.
///
/// Without them, the operand limbs would be free columns and the public inputs pure decoration:
/// every false comparison would be forgeable by simply proving its converse.
#[test]
fn operands_must_match_the_public_inputs() {
    // An internally-consistent, honest proof of `3 <= 5`...
    let row = u64_le_row(3, 5);
    // ...offered against the public claim `5 <= 3`.
    let res = prove_u64_le_row(row, 5, 3);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: a proof of `3 <= 5` was accepted against the public claim `5 <= 3` \
         ({res:?}). The operand columns are not pinned to the public inputs."
    );

    // Same, at operands that used to skip the circuit: an honest `5 <= u64::MAX` offered against
    // the claim `u64::MAX <= 5`.
    let row = u64_le_row(5, u64::MAX);
    let res = prove_u64_le_row(row, u64::MAX, 5);
    assert!(
        res.is_err(),
        "SOUNDNESS REGRESSION: a proof of `5 <= u64::MAX` was accepted against the public claim \
         `u64::MAX <= 5` ({res:?})."
    );
}
