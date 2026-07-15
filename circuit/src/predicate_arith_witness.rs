//! Rust witness builder for the emitted **arithmetic threshold** descriptor
//! (`dregg-predicate-arith-ge::threshold-v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/PredicatesArithmeticEmit.lean`).
//!
//! The arithmetic-threshold descriptor is the IR-v2 re-expression of the hand-AIR
//! `GreaterThanOrEqual(value, threshold)` predicate
//! (`circuit/src/dsl/predicates/arithmetic.rs::build_arithmetic_constraints`): a private `value`
//! satisfies `value ≥ threshold` for a PUBLIC `threshold`, carrying a PUBLIC `fact_commitment`
//! that binds the predicate to token state. Until now the only Rust producer for it lived inside
//! `circuit-prove/tests/predicates_arithmetic_emit_gate.rs` (private `honest_row` helpers); there
//! was NO production witness builder — the analog of
//! [`crate::membership_descriptor_4ary::membership_witness_4ary`] /
//! [`crate::adjacency_witness::adjacency_witness`] — that consumers of
//! [`crate::descriptor_by_name::descriptor_by_name`] could call. This module is that builder.
//!
//! ## The layout (a single logical row, repeated to a power-of-two height)
//!
//! | col | name              | meaning                                                          |
//! |-----|-------------------|------------------------------------------------------------------|
//! | 0   | `INPUT`           | the private compared value (`arithmetic.rs` input slot 0)        |
//! | 1   | `SLOT_A`          | the compiled expression-A result slot (`= INPUT` for bare-Input) |
//! | 2   | `THRESHOLD`       | the public comparison target, PI-bound to `PI_THRESHOLD`         |
//! | 3   | `DIFF`            | `value − threshold`, range-proved into `[0, 2^29)`               |
//! | 4   | `FACT_COMMITMENT` | the public fact commitment, PI-bound to `PI_FACT_COMMITMENT`     |
//!
//! The diff range-decomposition limbs the hand AIR lays down as ~30 explicit bit columns are NOT
//! base columns here: the descriptor's `⟨range, [DIFF]⟩` lookup makes the IR-v2 assembler
//! (`descriptor_ir2.rs::build_traces`) append the `decomp_cols(29)` limbs past `trace_width`.
//!
//! [`predicate_arith_witness`] is purely MECHANICAL — it does NOT enforce `value ≥ threshold`; it
//! computes `DIFF = value − threshold` in the field and lets the DESCRIPTOR be the judge:
//!   * C3 (`SLOT_A − INPUT == 0`) and C5 (`DIFF − SLOT_A + THRESHOLD == 0`) hold BY CONSTRUCTION
//!     on every row this builder emits (so a forge that keeps them consistent isolates C6);
//!   * C6 (`DIFF ∈ [0, 2^29)`) is the LOAD-BEARING tooth — a `value < threshold` witness wraps
//!     `DIFF` to `p − (threshold − value)`, far outside the interval, with no valid limb
//!     decomposition (UNSAT), which is exactly how the descriptor refuses a `<` claim;
//!   * C1 / C2 pin `THRESHOLD` / `FACT_COMMITMENT` to the public inputs, so a forged public
//!     `(threshold, fact_commitment)` is refused at verify.
//!
//! There is no in-circuit hash tooth on `FACT_COMMITMENT` (the hand AIR binds it as an opaque
//! pass-through public input), so — unlike the membership family's `hash_4_to_1` root — there is
//! no production hash-root a witness must reproduce byte-for-byte. The descriptor's identity is
//! itself byte-anchored: it is dispatched through [`crate::descriptor_by_name::descriptor_by_name`]
//! from the Lean-`#guard`-pinned golden. The production fact-commitment binding
//! ([`crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment`]) flows through this
//! builder unchanged and is asserted pinned in the tests.

use crate::field::BabyBear;

// --- Trace column layout (must match `PredicatesArithmeticEmit.lean` §1). ---
/// The private input value being compared (`arithmetic.rs` input slot 0).
pub const INPUT: usize = 0;
/// The compiled expression-A result slot; for a bare-`Input` expression C3 forces `SLOT_A = INPUT`.
pub const SLOT_A: usize = 1;
/// The public comparison target (`arithmetic.rs` `threshold_col`), PI-bound to `PI_THRESHOLD`.
pub const THRESHOLD: usize = 2;
/// The comparison difference (`arithmetic.rs` `diff_col`); range-proved into `[0, 2^29)`.
pub const DIFF: usize = 3;
/// The public fact commitment (`arithmetic.rs` `fact_commitment_col`), PI-bound to
/// `PI_FACT_COMMITMENT`.
pub const FACT_COMMITMENT: usize = 4;
/// Total base-trace width (the diff limbs are appended by the assembler, not counted here).
pub const PRED_WIDTH: usize = 5;

/// PI slot: the public threshold (`arithmetic.rs::PI_THRESHOLD`).
pub const PI_THRESHOLD: usize = 0;
/// PI slot: the public fact commitment (`arithmetic.rs::PI_FACT_COMMITMENT`).
pub const PI_FACT_COMMITMENT: usize = 1;
/// Public-input count.
pub const PRED_PI_COUNT: usize = 2;

/// The effective diff range width: the hand AIR's `NUM_BITS = 30` bits with the top bit forced to
/// zero leaves `diff ∈ [0, 2^29)` (`arithmetic.rs` @736); the emitted `range` table is 29 bits.
pub const DIFF_BITS: usize = 29;

/// The dispatched AIR-name of this descriptor (the [`crate::descriptor_by_name`] key).
pub const PREDICATE_ARITH_NAME: &str = "dregg-predicate-arith-ge::threshold-v1";

/// Build the 5-column arithmetic-threshold base trace + the 2-element public-input vector
/// `[threshold, fact_commitment]` for the emitted `dregg-predicate-arith-ge::threshold-v1`
/// descriptor.
///
/// `value` / `threshold` are the integers being compared (reduced into the field), `fact_commitment`
/// is the opaque public commitment binding the predicate to token state. The single logical
/// predicate row is repeated to `height` (a power of two ≥ 2 — the trace-height requirement). Every
/// row carries `INPUT = SLOT_A = value`, `THRESHOLD = threshold`, `DIFF = value − threshold` (field),
/// and `FACT_COMMITMENT = fact_commitment`; the range-decomposition limbs are appended by
/// `prove_vm_descriptor2`'s assembler, not here.
///
/// This builder does NOT pre-judge `value ≥ threshold`: it computes the field diff and the
/// descriptor's `⟨range, [DIFF]⟩` lookup is the judge. For an HONEST `≥` witness pass
/// `value ≥ threshold` with `value − threshold < 2^29` (then `DIFF ∈ [0, 2^29)` and the proof
/// verifies); a `value < threshold` wraps `DIFF` out of range and the descriptor rejects it.
pub fn predicate_arith_witness(
    value: u64,
    threshold: u64,
    fact_commitment: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "predicate-arith trace height {height} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }

    let value_f = BabyBear::from_u64(value);
    let threshold_f = BabyBear::from_u64(threshold);
    // DIFF = value − threshold in the field. For value ≥ threshold (small operands) this is the
    // genuine nonneg difference and lands in [0, 2^29); for value < threshold it wraps to
    // p − (threshold − value), which the descriptor's range lookup refuses. C3 (SLOT_A = INPUT) and
    // C5 (DIFF = SLOT_A − THRESHOLD) hold by construction on this row.
    let diff_f = value_f - threshold_f;

    let mut row = vec![BabyBear::ZERO; PRED_WIDTH];
    row[INPUT] = value_f;
    row[SLOT_A] = value_f;
    row[THRESHOLD] = threshold_f;
    row[DIFF] = diff_f;
    row[FACT_COMMITMENT] = fact_commitment;

    let trace = vec![row; height];
    let pis = vec![threshold_f, fact_commitment];
    Ok((trace, pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, TID_RANGE, VmConstraint2, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment;
    use crate::refusal::{Outcome, classify};
    use std::panic::AssertUnwindSafe;

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails
    /// to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// The dispatched descriptor decodes, carries the expected name, and has width 5 / 2 PIs.
    #[test]
    fn predicate_arith_dispatches_with_expected_shape() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("predicate-arith dispatches");
        assert_eq!(desc.name, PREDICATE_ARITH_NAME);
        assert_eq!(desc.trace_width, PRED_WIDTH);
        assert_eq!(desc.public_input_count, PRED_PI_COUNT);
        // exactly one range lookup (C6) on the diff column.
        let range_lookups = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_RANGE))
            .count();
        assert_eq!(range_lookups, 1, "the single diff range lookup (C6)");
    }

    /// THE POSITIVE POLE + the production fact-commitment binding: an honest `value ≥ threshold`
    /// witness (with `fact_commitment` produced by the production
    /// [`compute_arithmetic_fact_commitment`]) proves through the DISPATCHED descriptor and
    /// re-verifies against the public `[threshold, fact_commitment]`.
    #[test]
    fn honest_ge_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        // A genuine fact commitment binding fact_hash to a token state root (pass-through PI).
        let fact =
            compute_arithmetic_fact_commitment(BabyBear::new(0xFAC7), BabyBear::new(0x57A7E));

        for height in [2usize, 4, 8] {
            let (trace, pis) =
                predicate_arith_witness(100, 40, fact, height).expect("witness builds");
            assert_eq!(trace.len(), height);
            assert_eq!(trace[0].len(), PRED_WIDTH);
            // the fact-commitment binding flows through unchanged and is the pinned public input.
            assert_eq!(pis[PI_THRESHOLD], BabyBear::new(40));
            assert_eq!(
                pis[PI_FACT_COMMITMENT], fact,
                "the production fact commitment is the pinned public input (C2)"
            );

            let proof =
                prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
                    .unwrap_or_else(|e| panic!("honest height-{height} witness must prove: {e}"));
            verify_vm_descriptor2(&desc, &proof, &pis)
                .unwrap_or_else(|e| panic!("honest height-{height} proof must verify: {e}"));
        }
    }

    /// THE LOAD-BEARING C6 TOOTH: a `value < threshold` witness (diff wraps out of `[0, 2^29)`) is
    /// REFUSED by the range lookup, and the refusal is provably the RANGE mechanism (the error names
    /// the range wire / the `2^bits` bound). Non-vacuous: the honest `value ≥ threshold` accepts.
    #[test]
    fn value_below_threshold_refuses_on_range() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let fact = BabyBear::new(12345);

        // non-vacuity: value 100 ≥ threshold 40 is ACCEPTED.
        let (ok_trace, ok_pis) = predicate_arith_witness(100, 40, fact, 4).expect("witness");
        assert!(
            !rejects(&desc, &ok_trace, &ok_pis),
            "honest value ≥ threshold must be accepted — else the canary is vacuous"
        );

        // value 30 < threshold 40 ⇒ diff = p − 10, out of [0, 2^29). C3 and C5 still hold; ONLY C6 fails.
        let (bad_trace, bad_pis) = predicate_arith_witness(30, 40, fact, 4).expect("witness");
        let err = match prove_vm_descriptor2(
            &desc,
            &bad_trace,
            &bad_pis,
            &MemBoundaryWitness::default(),
            &[],
        ) {
            Ok(_) => panic!("value < threshold must be REFUSED (diff out of range, C6 tooth)"),
            Err(e) => e,
        };
        assert!(
            err.contains("range") || err.contains("2^"),
            "the refusal must be the RANGE mechanism (diff ∉ [0, 2^29)), got: {err}"
        );
        assert!(rejects(&desc, &bad_trace, &bad_pis));
    }

    /// C5 diff gate: a TAMPERED, in-range but inconsistent `diff` (59 where `value − threshold = 60`)
    /// passes the range proof and C3 but violates C5 → REJECTED. Non-vacuous: the honest trace accepts.
    #[test]
    fn tampered_diff_refuses_on_c5() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let fact = BabyBear::new(777);
        let (mut trace, pis) = predicate_arith_witness(100, 40, fact, 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );
        for row in &mut trace {
            row[DIFF] = BabyBear::new(59); // should be 60; still in range but breaks C5
        }
        assert!(
            rejects(&desc, &trace, &pis),
            "an in-range diff that violates diff = value − threshold must be REJECTED (C5 gate)"
        );
    }

    /// C3 slot identity: a TAMPERED `slot_a ≠ input` (with `diff` re-consistent so C5 and the range
    /// proof still hold) violates only C3 → REJECTED.
    #[test]
    fn tampered_slot_refuses_on_c3() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let fact = BabyBear::new(888);
        let (mut trace, pis) = predicate_arith_witness(100, 40, fact, 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );
        for row in &mut trace {
            row[SLOT_A] = BabyBear::new(101); // ≠ input 100 → C3 broken
            row[DIFF] = BabyBear::new(101 - 40); // keep C5 satisfied (61 ∈ range), isolate C3
        }
        assert!(
            rejects(&desc, &trace, &pis),
            "slot_a ≠ input must be REJECTED (C3 slot-identity gate)"
        );
    }

    /// C1 threshold PI binding: honest trace, forged public `threshold` (41 ≠ the witness 40) →
    /// REJECTED at verify. Non-vacuous: the correct threshold PI accepts.
    #[test]
    fn forged_threshold_pi_refuses_on_c1() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let fact = BabyBear::new(12345);
        let (trace, pis) = predicate_arith_witness(100, 40, fact, 4).expect("witness");
        assert!(!rejects(&desc, &trace, &pis));
        let forged = vec![BabyBear::new(41), fact];
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged public threshold must be REJECTED (C1 PI binding)"
        );
    }

    /// C2 fact-commitment PI binding: honest trace, forged public `fact_commitment` → REJECTED.
    #[test]
    fn forged_fact_pi_refuses_on_c2() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let fact = BabyBear::new(12345);
        let (trace, pis) = predicate_arith_witness(100, 40, fact, 4).expect("witness");
        assert!(!rejects(&desc, &trace, &pis));
        let forged = vec![BabyBear::new(40), BabyBear::new(99999)];
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged public fact_commitment must be REJECTED (C2 PI binding)"
        );
    }

    /// AUDIT (independent forge): tamper the TRACE-side `FACT_COMMITMENT` column (honest PI kept) →
    /// the first-row `pi_binding` (col4 ↔ PI[1]) no longer holds → REJECTED. Distinct from
    /// `forged_fact_pi_refuses_on_c2` (which tampers the PI side); this probes the trace side.
    #[test]
    fn audit_tampered_trace_fact_refuses() {
        let desc = descriptor_by_name(PREDICATE_ARITH_NAME).expect("dispatch");
        let fact = compute_arithmetic_fact_commitment(BabyBear::new(0xBEEF), BabyBear::new(0xF00D));
        let (mut trace, pis) = predicate_arith_witness(100, 40, fact, 4).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepts (non-vacuity)"
        );
        for row in &mut trace {
            row[FACT_COMMITMENT] = BabyBear::new(0xDEAD); // trace col4 ≠ honest PI[1]
        }
        assert!(
            rejects(&desc, &trace, &pis),
            "a tampered trace fact_commitment (≠ honest PI) must be REJECTED (C1 first-row binding)"
        );
    }

    /// Malformed heights (non-power-of-two, < 2) are refused at build time.
    #[test]
    fn malformed_witness_refuses() {
        let fact = BabyBear::new(1);
        assert!(predicate_arith_witness(100, 40, fact, 3).is_err()); // not a power of two
        assert!(predicate_arith_witness(100, 40, fact, 1).is_err()); // < 2
        assert!(predicate_arith_witness(100, 40, fact, 0).is_err());
    }
}
