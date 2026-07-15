//! # The emit-from-Lean EQUALITY GATE — arithmetic predicate `GreaterThanOrEqual(value, threshold)`.
//!
//! Validates the `emit-from-Lean` pattern for the arithmetic-predicate family
//! (`circuit/src/dsl/predicates/arithmetic.rs`) on its canonical GTE-against-a-public-threshold
//! lane, and with it the RANGE-lookup mapping of the diff bit-decomposition range proof.
//!
//! The descriptor is AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/PredicatesArithmeticEmit.lean`, `predicateGeDesc`) and its
//! wire string is byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT string
//! ([`GOLDEN_JSON`]), and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST `value ≥ threshold` witness through [`prove_vm_descriptor2`], asserts
//!      ACCEPT, and re-verifies the proof against the public `(threshold, fact_commitment)`;
//!   3. the MUTATION CANARIES — each tampers ONE thing and asserts prove-or-verify REFUSES (real
//!      UNSAT), biting a DISTINCT hand-AIR constraint:
//!        - `value < threshold`  → `diff` wraps out of `[0, 2^29)` → the **C6 range** tooth
//!          (asserted with the range-specific error message, so the refusal is provably the range
//!          mechanism, not an unrelated error);
//!        - an in-range but inconsistent `diff` → the **C5** diff-computation gate;
//!        - `slot_a ≠ input` (with `diff` re-consistent) → the **C3** slot-identity gate;
//!        - a forged public `threshold` → the **C1** PI binding;
//!        - a forged public `fact_commitment` → the **C2** PI binding.
//!
//! Each canary is NON-VACUOUS: the honest witness proves-and-verifies (step 2 + the in-canary
//! sanity), and each tamper genuinely breaks a named constraint.
//!
//! ## The C6 range tooth (the predicate's load-bearing edge)
//!
//! The hand AIR (`arithmetic.rs` C6 @708–738) decomposes `diff` into `NUM_BITS = 30` bits and
//! forces the top bit to zero, i.e. `diff ∈ [0, 2^29)`. The emitted descriptor maps that to a
//! `Range{bits:29}` lookup on the `diff` column; the IR-v2 assembler realizes it as a byte-limb
//! decomposition (`descriptor_ir2.rs::eval_decomp`). For a GTE predicate `diff = value − threshold`
//! lands in `[0, 2^29)` IFF `value ≥ threshold` — a `value < threshold` wraps `diff` to
//! `p − (threshold − value)`, far outside the interval, with NO valid limb witness (UNSAT). That
//! is what the first canary exercises.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, TID_RANGE, TableDef2, TableSem, VmConstraint2, chip_absorb_all_lanes,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::{hash_2_to_1, hash_fact};
use dregg_circuit::refusal::{Outcome, classify};

/// The fixed fact context the honest witness commits; the honest fact's VALUE is the proven value.
const FIXED_PRED: u32 = 42;
const FIXED_STATE_ROOT: u32 = 99_999;
const FACT_MARK: u32 = 0xFACF;

/// The credentialed fact commitment for a fact whose value is `value`:
/// `hash_2_to_1(hash_fact(pred, [value, 0, 0]), state_root)`.
fn derived_fact(value: u32) -> BabyBear {
    let fh = hash_fact(
        BabyBear::new(FIXED_PRED),
        &[BabyBear::new(value), BabyBear::ZERO, BabyBear::ZERO],
    );
    hash_2_to_1(fh, BabyBear::new(FIXED_STATE_ROOT))
}

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 predicateGeDesc` emits (pinned by the
/// `#guard` in `PredicatesArithmeticEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if
/// this literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-predicate-arith-ge::threshold-v1","ir":2,"trace_width":24,"public_input_count":2,"tables":[{"id":2,"name":"range","arity":1,"sem":"range","bits":29}],"constraints":[{"t":"pi_binding","row":"first","col":2,"pi_index":0},{"t":"pi_binding","row":"first","col":4,"pi_index":1},{"t":"gate","body":{"t":"add","l":{"t":"var","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}}},"r":{"t":"var","v":2}}},{"t":"lookup","table":2,"tuple":[{"t":"var","v":3}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":5},{"t":"var","v":0},{"t":"var","v":6},{"t":"var","v":7},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":9},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":9},{"t":"var","v":8},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":4},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23}]}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `PredicatesArithmeticEmit.lean` §1). ---
const INPUT: usize = 0;
const SLOT_A: usize = 1;
const THRESHOLD: usize = 2;
const DIFF: usize = 3;
const FACT_COMMITMENT: usize = 4;
// value<->fact weld columns
const PREDICATE_SYM: usize = 5;
const TERM1: usize = 6;
const TERM2: usize = 7;
const STATE_ROOT: usize = 8;
const FACT_HASH: usize = 9;
const FH_LANE_BASE: usize = 10; // fact-hash out-lanes 1..7 at 10..16
const FC_LANE_BASE: usize = 17; // fact-commitment out-lanes 1..7 at 17..23
const PRED_WIDTH: usize = 24;
const DIFF_BITS: usize = 29;
const PI_THRESHOLD: usize = 0;
const PI_FACT_COMMITMENT: usize = 1;

/// A generic `TID_P2` chip lookup with arity `inputs.len()` — built EXACTLY as Lean's
/// `chipLookupTuple ins out_col lanes` (arity tag, `CHIP_RATE` zero-padded input exprs, out0 :: 7
/// lane vars).
fn chip_lookup(inputs: &[LeanExpr], out_col: usize, lane_base: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(inputs.len() as i64));
    for i in 0..CHIP_RATE {
        tuple.push(inputs.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    tuple.push(LeanExpr::Var(out_col));
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The value↔fact weld's two lookups (descriptor order: after the range lookup): arity-7
/// `fact_hash = hash_fact(pred, [INPUT, term1, term2])`, then arity-2
/// `fact_commitment = hash_2_to_1(fact_hash, state_root)`.
fn fact_hash_lookup() -> VmConstraint2 {
    chip_lookup(
        &[
            LeanExpr::Var(PREDICATE_SYM),
            LeanExpr::Var(INPUT),
            LeanExpr::Var(TERM1),
            LeanExpr::Var(TERM2),
            LeanExpr::Const(0),
            LeanExpr::Const(FACT_MARK as i64),
            LeanExpr::Const(1),
        ],
        FACT_HASH,
        FH_LANE_BASE,
    )
}
fn fact_commit_lookup() -> VmConstraint2 {
    chip_lookup(
        &[LeanExpr::Var(FACT_HASH), LeanExpr::Var(STATE_ROOT)],
        FACT_COMMITMENT,
        FC_LANE_BASE,
    )
}

/// The independently-hand-built twin of the Lean `predicateGeDesc` (the "hand AIR semantics"
/// shape): C1/C2 PI bindings, the C3 slot identity, the C5 diff gate, the C6 range lookup.
fn hand_built_desc() -> EffectVmDescriptor2 {
    // C3: SLOT_A − INPUT == 0.
    let c3 = VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::Var(SLOT_A),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(INPUT)),
    )));
    // C5: (DIFF − SLOT_A) + THRESHOLD == 0.
    let c5 = VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::add(
            LeanExpr::Var(DIFF),
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(SLOT_A)),
        ),
        LeanExpr::Var(THRESHOLD),
    )));
    EffectVmDescriptor2 {
        name: "dregg-predicate-arith-ge::threshold-v1".to_string(),
        trace_width: PRED_WIDTH,
        public_input_count: 2,
        tables: vec![TableDef2 {
            id: TID_RANGE,
            name: "range".to_string(),
            arity: 1,
            sem: TableSem::Range { bits: DIFF_BITS },
        }],
        constraints: vec![
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: THRESHOLD,
                pi_index: PI_THRESHOLD,
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: FACT_COMMITMENT,
                pi_index: PI_FACT_COMMITMENT,
            }),
            c3,
            c5,
            VmConstraint2::Lookup(LookupSpec {
                table: TID_RANGE,
                tuple: vec![LeanExpr::Var(DIFF)],
            }),
            // THE VALUE<->FACT WELD (held forgery #2).
            fact_hash_lookup(),
            fact_commit_lookup(),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// One honest predicate row for `(value, threshold)` with `value ≥ threshold`: `slot_a = value`
/// (C3), `diff = value − threshold` (C5), AND the value↔fact weld columns filled for a fact whose
/// VALUE is exactly `value` — `fact_hash = hash_fact(pred, [value, 0, 0])` (arity-7 lookup out0,
/// over the SAME `INPUT` column) and `fact_commitment = hash_2_to_1(fact_hash, state_root)` (arity-2
/// lookup out0). Chip LANE columns are left zero — the prover fills them. The range limb columns are
/// appended by the assembler.
fn honest_row(value: u32, threshold: u32) -> Vec<BabyBear> {
    let pred = BabyBear::new(FIXED_PRED);
    let sr = BabyBear::new(FIXED_STATE_ROOT);
    let v = BabyBear::new(value);
    let fact_hash = chip_absorb_all_lanes(
        7,
        &[
            pred,
            v,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(FACT_MARK),
            BabyBear::ONE,
        ],
    )[0];
    let fact_commitment = hash_2_to_1(fact_hash, sr);
    let mut row = vec![BabyBear::ZERO; PRED_WIDTH];
    row[INPUT] = v;
    row[SLOT_A] = v;
    row[THRESHOLD] = BabyBear::new(threshold);
    row[DIFF] = v - BabyBear::new(threshold);
    row[FACT_COMMITMENT] = fact_commitment;
    row[PREDICATE_SYM] = pred;
    row[STATE_ROOT] = sr;
    row[FACT_HASH] = fact_hash;
    row
}

/// A 4-row (power-of-two) base trace of identical honest rows.
fn honest_trace(value: u32, threshold: u32) -> Vec<Vec<BabyBear>> {
    let row = honest_row(value, threshold);
    vec![row.clone(), row.clone(), row.clone(), row]
}

/// The honest public inputs `[threshold, fact_commitment]` — the fact commitment is the genuine
/// double-hash of the value-`value` fact.
fn honest_pis(value: u32, threshold: u32) -> Vec<BabyBear> {
    vec![BabyBear::new(threshold), derived_fact(value)]
}

/// Public inputs with an explicit (possibly forged) fact commitment.
fn pis_fc(threshold: u32, fact_commitment: BabyBear) -> Vec<BabyBear> {
    vec![BabyBear::new(threshold), fact_commitment]
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies.
///
/// Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies the first-row
/// `PiBinding` against the public inputs only under `debug_assertions`, so in a `--release` test
/// the CONSUMER's `verify_vm_descriptor2` is the real PI check (the production posture).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], public: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, public, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, public)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), and has exactly the expected shape.
#[test]
fn predicate_ge_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, PRED_WIDTH);
    assert_eq!(decoded.public_input_count, 2);
    // one range table declared, at 29 bits (the hand AIR's diff < 2^29).
    assert_eq!(decoded.tables.len(), 1);
    assert_eq!(decoded.tables[0].sem, TableSem::Range { bits: DIFF_BITS });
    // the C6 range lookup on the diff column is present.
    let range_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_RANGE))
        .count();
    assert_eq!(range_lookups, 1, "the single diff range lookup (C6)");
    // the two value<->fact weld chip lookups (arity-7 fact-hash + arity-2 fact-commitment).
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        chip_lookups, 2,
        "the fact-hash + fact-commitment weld chip lookups"
    );
    // the two PI bindings (C1, C2).
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 2, "the threshold + fact-commitment PI bindings");
    assert_eq!(
        decoded.constraints.len(),
        7,
        "5 base teeth + 2 weld chip lookups"
    );
}

/// STEP 2 — THE POSITIVE POLE: an honest `value ≥ threshold` witness proves through the emitted
/// descriptor and re-verifies against the public `(threshold, fact)`. The proof commits exactly
/// two instances (main + byte/range table).
#[test]
fn honest_ge_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // value 100 ≥ threshold 40, diff = 60 ∈ [0, 2^29).
    let trace = honest_trace(100, 40);
    let public = honest_pis(100, 40);
    let proof = prove_vm_descriptor2(&desc, &trace, &public, &MemBoundaryWitness::default(), &[])
        .expect("the honest value ≥ threshold witness must prove");
    assert_eq!(
        proof.degree_bits.len(),
        3,
        "the welded descriptor commits main + byte/range table + Poseidon2 chip table"
    );
    verify_vm_descriptor2(&desc, &proof, &public)
        .expect("the honest proof must re-verify against the public (threshold, fact)");
}

/// STEP 3a — MUTATION CANARY (C6 range tooth): `value < threshold`. `diff = value − threshold`
/// wraps to `p − (threshold − value)`, outside `[0, 2^29)` — no valid limb decomposition. The
/// refusal is asserted to be the RANGE mechanism specifically (the error names the range wire and
/// the `2^bits` bound), so this is provably rejected BY the range constraint, not an unrelated error.
#[test]
fn value_below_threshold_refuses_on_range() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // non-vacuity: the honest value ≥ threshold witness is ACCEPTED.
    assert!(
        !rejects(&desc, &honest_trace(100, 40), &honest_pis(100, 40)),
        "honest value ≥ threshold must be accepted — else the canary is vacuous"
    );
    // value 30 < threshold 40 ⇒ diff = -10 (field) = p - 10, out of [0, 2^29).
    // C3, C5 and the weld lookups all hold on this trace; ONLY the range proof can fail.
    let trace = honest_trace(30, 40);
    let public = honest_pis(30, 40);
    let err =
        match prove_vm_descriptor2(&desc, &trace, &public, &MemBoundaryWitness::default(), &[]) {
            Ok(_) => panic!("value < threshold must be REFUSED (diff out of range, C6 tooth)"),
            Err(e) => e,
        };
    assert!(
        err.contains("range") || err.contains("2^"),
        "the refusal must be the RANGE mechanism (diff ∉ [0, 2^29)), got: {err}"
    );
    // and end-to-end it is rejected.
    assert!(rejects(&desc, &trace, &public));
}

/// STEP 3b — MUTATION CANARY (C5 diff gate): an in-range but INCONSISTENT `diff` (59 where
/// `value − threshold = 60`). The range proof passes (59 ∈ [0, 2^29)), C3 holds, but the C5 gate
/// `diff − slot_a + threshold == 0` is violated → the batch prover/verifier rejects.
#[test]
fn inconsistent_diff_refuses_on_c5() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let mut trace = honest_trace(100, 40);
    for row in &mut trace {
        row[DIFF] = BabyBear::new(59); // should be 60; still in range, but breaks C5
    }
    let public = honest_pis(100, 40);
    assert!(
        rejects(&desc, &trace, &public),
        "an in-range diff that violates diff = value − threshold must be REJECTED (C5 gate)"
    );
}

/// STEP 3c — MUTATION CANARY (C3 slot identity): `slot_a ≠ input`, with `diff` re-consistent so
/// C5 still holds and `diff` stays in range. Only the C3 slot-identity gate `slot_a − input == 0`
/// fails → rejected. The compiled-expression slot binding is load-bearing.
#[test]
fn tampered_slot_refuses_on_c3() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let mut trace = honest_trace(100, 40);
    for row in &mut trace {
        row[SLOT_A] = BabyBear::new(101); // ≠ input 100 → C3 broken
        row[DIFF] = BabyBear::new(101 - 40); // keep C5 satisfied (61 ∈ range), isolate C3
    }
    let public = honest_pis(100, 40);
    assert!(
        rejects(&desc, &trace, &public),
        "slot_a ≠ input must be REJECTED (C3 slot-identity gate)"
    );
}

/// STEP 3d — MUTATION CANARY (C1 threshold PI binding): honest trace, forged public `threshold`.
/// The first-row `threshold` column (40) no longer equals `PI[0]` (41) → the C1 PI binding is
/// violated at verify → rejected. The public comparison target is bound to the witness.
#[test]
fn forged_threshold_pi_refuses_on_c1() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let trace = honest_trace(100, 40);
    // non-vacuity: the correct threshold PI is accepted.
    assert!(!rejects(&desc, &trace, &honest_pis(100, 40)));
    assert!(
        rejects(&desc, &trace, &pis_fc(41, derived_fact(100))),
        "a forged public threshold must be REJECTED (C1 PI binding)"
    );
}

/// STEP 3e — MUTATION CANARY (C2 fact-commitment PI binding): honest trace, forged public
/// `fact_commitment`. The first-row `fact_commitment` column (12345) no longer equals `PI[1]`
/// (99999) → the C2 PI binding is violated at verify → rejected.
#[test]
fn forged_fact_pi_refuses_on_c2() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let trace = honest_trace(100, 40);
    assert!(!rejects(&desc, &trace, &honest_pis(100, 40)));
    assert!(
        rejects(&desc, &trace, &pis_fc(40, BabyBear::new(99999))),
        "a forged public fact_commitment must be REJECTED (C2 PI binding)"
    );
}

/// STEP 3f — MUTATION CANARY (THE VALUE↔FACT WELD / held forgery #2): prove `value 100 >= threshold
/// 40` but commit to a DIFFERENT real fact whose value is `30` (a fact the prover holds that FAILS
/// the threshold). Before the weld, `fact_commitment` was a free PI, so this passed. Now the arity-7
/// fact-hash lookup forces `fact_hash = hash_fact(pred, [INPUT=100, 0, 0])` and the arity-2 lookup
/// forces `fact_commitment = hash_2_to_1(fact_hash, state_root)`; pinning `fact_commitment` to the
/// value-30 fact names a chip row no genuine permutation serves → LogUp UNSAT. Honest ACCEPTS.
#[test]
fn forge_committed_value_neq_fact_rejects() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // Non-vacuity: honest (value 100 == committed fact value 100) ACCEPTS.
    assert!(!rejects(
        &desc,
        &honest_trace(100, 40),
        &honest_pis(100, 40)
    ));
    // Forge: prove value 100 >= 40 but commit to the value-30 fact the prover actually holds.
    let mut trace = honest_trace(100, 40); // internally consistent for INPUT=100 (fact for 100)
    let fc_30 = derived_fact(30);
    for row in &mut trace {
        row[FACT_COMMITMENT] = fc_30; // keep the C2 pin satisfied against the value-30 fact
    }
    assert!(
        rejects(&desc, &trace, &pis_fc(40, fc_30)),
        "proving a value (100) different from the committed fact's value (30) must be REJECTED — \
         the value↔fact weld (held forgery #2)"
    );
}
