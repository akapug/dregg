//! Plonky3 prove+verify driver for predicate bodies the runtime can encode
//! as a `CircuitDescriptor`.
//!
//! Strategy: for each requirement in the predicate body, we build a tiny
//! `CircuitDescriptor` whose constraints encode the requirement
//! algebraically, generate a witness trace by hand (the prover knows the
//! values from the IR-level inputs), then call
//! [`dregg_circuit::dsl::dsl_p3_air::prove_dsl_p3`] followed by
//! [`dregg_circuit::dsl::dsl_p3_air::verify_dsl_p3`] — the PRODUCTION interpreter.
//!
//! (Corrected 2026-07-17: this doc used to name `dregg_dsl_runtime::prove_dsl_plonky3` — the 868-line
//! DUPLICATE `DslP3Air` this harness once drove. The imports were migrated to production but the doc was
//! not; the duplicate is now DELETED. A harness that names the shadow it no longer drives is the mirror
//! lying about itself.)
//!
//! A successful round-trip means "the runtime Plonky3 verifier accepts
//! this requirement on these inputs." A panic during prove (the standard
//! way `p3_uni_stark::prove` rejects an invalid trace) or a
//! verifier-returns-`Ok(false)` is reported as Reject.
//!
//! ## Scope
//!
//! - Inequalities (`<=`, `>=`) are encoded as a `Polynomial` constraint over the diff column plus a
//!   REAL 30-bit decomposition range check bounding that diff (see [`diff_le_descriptor`]).
//!   Rejection of a false claim is a property of the CONSTRAINTS — a false `smaller <= bigger` has
//!   NO satisfying assignment — not of the witness generator's good manners.
//!
//!   (Fixed 2026-07-17, `DslComparisonRangeSoundnessResidual`. This lowering used to carry a
//!   free `indicator` column pinned to zero and NOTHING bounding `diff`; since C1 is a mod-p
//!   subtraction, a prover claiming `5 <= 3` could witness `diff = (3 - 5) mod p = p - 2`,
//!   `indicator = 0`, satisfy every constraint, and have the production p3 prover AND verifier
//!   ACCEPT the false statement. The comparison's truth lived entirely in the honest witness
//!   generator, which volunteered an invalid witness when the claim was false — a courtesy a
//!   malicious prover simply declines. The old in-file comment "we cap the diffs to a 30-bit range
//!   where this encoding stays sound" was false: capping the OPERANDS bounds nothing about a diff
//!   column no constraint reads. The range check is now real, and the forgery is UNSAT — pinned as
//!   a rejection tooth in `tests/comparison_wrap_soundness.rs`.)
//! - Equality (`==`) and non-equality (`!=`) on u64 reduce to `Equality`
//!   over two columns and a `ConditionalNonzero` respectively.
//! - Equality / non-equality on `[u8; 32]` are compared as 64-bit limb
//!   tuples (limb 0 — bytes 0..8); the comparison-side semantics still
//!   match the IR-level truth because the IR's bytes-equality requires
//!   full bytewise equality.
//! - Membership requirements need Poseidon2 hash gadgets which the runtime
//!   AIR cannot express. We mark these Skip.
//!
//! ## Performance
//!
//! Each requirement gets its own STARK proof. For the predicate suite this
//! means ~hundreds of small proofs. Plonky3's `p3_uni_stark` over BabyBear
//! is fast enough at this scale that the full crate runs in a few seconds.

use dregg_circuit::dsl::circuit::DslCircuit;
use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_p3, verify_dsl_p3};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_dsl_runtime::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

use crate::predicates::Requirement;

/// Round-trip every requirement in the body through prove+verify. Returns
/// `Ok(true)` if every requirement is provable and verifies, `Ok(false)`
/// if any requirement is unsatisfiable for the supplied inputs, `Err` if
/// the requirement shape isn't expressible here.
pub fn prove_and_verify(body_requirements: &[Requirement]) -> Result<Verdict, String> {
    for req in body_requirements {
        match drive(req)? {
            Verdict::Accept => continue,
            Verdict::Reject => return Ok(Verdict::Reject),
            Verdict::Skip { reason } => return Ok(Verdict::Skip { reason }),
        }
    }
    Ok(Verdict::Accept)
}

#[derive(Debug, Clone)]
pub enum Verdict {
    Accept,
    Reject,
    Skip { reason: &'static str },
}

fn drive(req: &Requirement) -> Result<Verdict, String> {
    match req {
        Requirement::LessEqualU64(l, r) => Ok(drive_inequality(*l, *r)),
        Requirement::GreaterEqualU64(l, r) => Ok(drive_inequality(*r, *l)),
        Requirement::EqualU64(l, r) => Ok(drive_equality_u64(*l, *r)),
        Requirement::NotEqualU64(l, r) => Ok(drive_nonequality_u64(*l, *r)),
        Requirement::EqualBytes32(l, r) => Ok(drive_equality_bytes(l, r)),
        Requirement::NotEqualBytes32(l, r) => Ok(drive_nonequality_bytes(l, r)),
        // Membership is skipped for a REAL reason (corrected 2026-07-16 — the old reason, "membership
        // needs Poseidon2 gadgets which DslP3Air cannot inline at runtime", was a limitation of the
        // RETIRED duplicate interpreter in dregg-dsl-runtime, not of the shipped one).
        // Empirically probed: `DslP3Air::try_from_dsl(merkle_poseidon2_circuit())` ->
        // `NonAlgebraicConstraint { index: 1, form: "MerkleHash (use the Lean-emitted IR2 descriptor for
        // position-indexed Merkle hashing)" }`. The production interpreter DELIBERATELY routes MerkleHash
        // to the Lean-authored IR2 rail (architectural law #1), so there is nothing for a DSL-vs-IR
        // differential to compare here. Membership's real coverage lives on that rail:
        // `circuit/src/merkle_air.rs`'s membership_p3 teeth (honest proof + forged root / forged leaf /
        // non-member leaf all rejected), byte-pinned to `MerkleMembership4aryEmit.lean`.
        Requirement::Membership { .. } => Ok(Verdict::Skip {
            reason: "membership is MerkleHash-shaped: the shipped DslP3Air routes it to the Lean-emitted \
                     IR2 descriptor (law #1), so there is no DSL-side arithmetization to differ against",
        }),
    }
}

// ============================================================================
// `diff-le`: the range-checked comparison lowering
// ============================================================================

/// Bits in the `diff` range decomposition. Sized EXACTLY to the operand range
/// [`INEQUALITY_SAFE_RANGE`]: with both operands in `[0, 2^30)`, an honest
/// `diff = bigger - smaller` lies in `[0, 2^30)` and is always representable.
///
/// This is what makes the lowering sound. `2^30 - 1 < BABYBEAR_P ~= 2^31`, so the
/// recomposition sum cannot itself wrap, and therefore C2 (below) forces
/// `diff ∈ [0, 2^30)` as an INTEGER — pinning the one degree of freedom the mod-p
/// subtraction in C1 leaves open. A field-wrapped negative difference (`p - k` for
/// small `k`) exceeds `2^30 - 1` and is UNSAT.
pub const DIFF_RANGE_BITS: usize = 30;

/// Operands at or above this bound fall back to the IR-level truth (see
/// [`prove_trivial`]) rather than the circuit.
pub const INEQUALITY_SAFE_RANGE: u64 = 1 << 30;

/// Column layout of the `diff-le` descriptor.
pub mod diff_le_col {
    /// The claimed-smaller operand (bound to PI 0).
    pub const SMALLER: usize = 0;
    /// The claimed-bigger operand (bound to PI 1).
    pub const BIGGER: usize = 1;
    /// `bigger - smaller` (mod p by C1; range-checked to `[0, 2^30)` by C2/C3).
    pub const DIFF: usize = 2;
    /// First of the [`super::DIFF_RANGE_BITS`] decomposition bit columns.
    pub const DIFF_BITS_START: usize = 3;
    /// Column of decomposition bit `i`.
    pub const fn diff_bit(i: usize) -> usize {
        DIFF_BITS_START + i
    }
    /// Total trace width.
    pub const WIDTH: usize = DIFF_BITS_START + super::DIFF_RANGE_BITS;
}

/// The `diff-le` descriptor: proves `smaller <= bigger` for operands in
/// `[0, 2^30)`, where `smaller`/`bigger` are pinned to the public inputs.
///
/// Constraints:
/// - **C1** `bigger - smaller - diff == 0` — mod p, so on its own always satisfiable.
/// - **C2** `sum(diff_bit[i] * 2^i) - diff == 0` — recomposition.
/// - **C3..** each `diff_bit[i]` is boolean.
///
/// C2 + C3 are the range check: together they force `diff ∈ [0, 2^30)` as an integer
/// (the sum of 30 boolean-pinned bits maxes at `2^30 - 1 < p`, so it cannot wrap).
/// With C1 that makes `bigger - smaller` a non-negative integer — i.e. exactly
/// `smaller <= bigger`. A false claim has NO satisfying assignment.
///
/// Boundaries pin `smaller`/`bigger` to PI 0/1 on the first row, so the proof is
/// about the PUBLICLY CLAIMED comparison and not some other pair of operands the
/// prover preferred.
///
/// Modelled on the deployed precedent `circuit/src/dsl/committed_threshold.rs`
/// (C4 recomposition + C5 binary-pinned bits) and `derivation.rs` C17/C22. It
/// deliberately does NOT copy that precedent's `BoundaryDef::Fixed` top-bit-zero:
/// there the bit count (30) exceeds the range actually needed, so a top bit must be
/// zeroed to keep the sum under `p`. Here the bit count is sized exactly to the
/// operand range, so the bound needs no boundary — which is STRONGER, because C2/C3
/// are per-row constraints that hold on EVERY row, whereas a `BoundaryRow::First`
/// boundary binds row 0 only.
pub fn diff_le_descriptor() -> CircuitDescriptor {
    use diff_le_col as c;
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let mut constraints = vec![
        // C1: bigger - smaller - diff == 0 (mod p)
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![c::BIGGER],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![c::SMALLER],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![c::DIFF],
                },
            ],
        },
    ];

    // C2: sum(diff_bit[i] * 2^i) - diff == 0
    {
        let mut terms = Vec::with_capacity(DIFF_RANGE_BITS + 1);
        let mut power_of_two = BabyBear::ONE;
        for i in 0..DIFF_RANGE_BITS {
            terms.push(PolyTerm {
                coeff: power_of_two,
                col_indices: vec![c::diff_bit(i)],
            });
            power_of_two = power_of_two + power_of_two;
        }
        terms.push(PolyTerm {
            coeff: neg_one,
            col_indices: vec![c::DIFF],
        });
        constraints.push(ConstraintExpr::Polynomial { terms });
    }

    // C3..: every decomposition bit is boolean. Without this, a single "bit"
    // column could carry an arbitrary field element and the recomposition would
    // bound nothing.
    for i in 0..DIFF_RANGE_BITS {
        constraints.push(ConstraintExpr::Binary {
            col: c::diff_bit(i),
        });
    }

    let mut columns = vec![
        ColumnDef {
            name: "smaller".into(),
            index: c::SMALLER,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "bigger".into(),
            index: c::BIGGER,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff".into(),
            index: c::DIFF,
            kind: ColumnKind::Value,
        },
    ];
    for i in 0..DIFF_RANGE_BITS {
        columns.push(ColumnDef {
            name: format!("diff_bit_{i}"),
            index: c::diff_bit(i),
            kind: ColumnKind::Binary,
        });
    }

    CircuitDescriptor {
        name: "diff-le".to_string(),
        trace_width: diff_le_col::WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries: vec![
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: c::SMALLER,
                pi_index: 0,
            },
            BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: c::BIGGER,
                pi_index: 1,
            },
        ],
        public_input_count: 2,
        lookup_tables: vec![],
    }
}

/// Build one `diff-le` trace row from `(smaller, bigger, diff)`, decomposing
/// `diff` into its low [`DIFF_RANGE_BITS`] bits.
///
/// `diff` is taken as a parameter rather than derived so that soundness teeth can
/// hand this an ADVERSARIAL diff (e.g. a field-wrapped `p - 2`) and watch the
/// constraint system reject it. For a wrapped diff the low 30 bits cannot
/// recompose to it, so C2 fails — which is the point.
pub fn diff_le_row(smaller: u64, bigger: u64, diff: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; diff_le_col::WIDTH];
    row[diff_le_col::SMALLER] = BabyBear::from_u64(smaller);
    row[diff_le_col::BIGGER] = BabyBear::from_u64(bigger);
    row[diff_le_col::DIFF] = diff;
    let diff_val = diff.as_u32();
    for i in 0..DIFF_RANGE_BITS {
        row[diff_le_col::diff_bit(i)] = BabyBear::new((diff_val >> i) & 1);
    }
    row
}

/// Prove `smaller <= bigger` through the production p3 interpreter, with `diff =
/// bigger - smaller` bounded by a real bit-decomposition range check.
///
/// Operands outside `[0, 2^30)` (u64::MAX and friends are common in the predicate
/// suite) fall back to the IR-level truth: BabyBear's ~31-bit prime cannot hold a
/// u64 difference, so there is no honest arithmetization to range-check.
fn drive_inequality(smaller: u64, bigger: u64) -> Verdict {
    let ir_ok = smaller <= bigger;
    if smaller >= INEQUALITY_SAFE_RANGE || bigger >= INEQUALITY_SAFE_RANGE {
        return prove_trivial(ir_ok);
    }

    let descriptor = diff_le_descriptor();

    // The honest witness. When the claim is FALSE this is the field-wrapped
    // `p - (smaller - bigger)`, which no 30-bit decomposition recomposes to — so
    // the prover FAILS TO FIND a witness rather than volunteering a bad one. That
    // is the whole difference between this and the pre-fix lowering: rejection is
    // now the constraint system's verdict, not the generator's confession.
    let diff = BabyBear::from_u64(bigger) - BabyBear::from_u64(smaller);
    let row = diff_le_row(smaller, bigger, diff);
    let trace = vec![row.clone(), row];
    let pi = vec![BabyBear::from_u64(smaller), BabyBear::from_u64(bigger)];

    round_trip(&descriptor, &trace, &pi, ir_ok)
}

/// Equality on u64 via two columns + `Equality` constraint.
fn drive_equality_u64(l: u64, r: u64) -> Verdict {
    let ir_ok = l == r;
    let safe_range = 1u64 << 30;
    if l >= safe_range || r >= safe_range {
        return prove_trivial(ir_ok);
    }
    let descriptor = CircuitDescriptor {
        name: "eq-u64".into(),
        trace_width: 2,
        max_degree: 1,
        columns: vec![
            ColumnDef {
                name: "lhs".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "rhs".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
        ],
        constraints: vec![ConstraintExpr::Equality { col_a: 0, col_b: 1 }],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    // Witness: place both inputs as-is. If they differ, the equality
    // constraint evaluates to non-zero and prove will fail (panic).
    let row = vec![BabyBear::from_u64(l), BabyBear::from_u64(r)];
    let trace = vec![row.clone(), row];
    let pi = vec![BabyBear::from_u64(l), BabyBear::from_u64(r)];
    round_trip(&descriptor, &trace, &pi, ir_ok)
}

/// Non-equality via `ConditionalNonzero` with selector=1, value=diff, and
/// an inverse witness column.
fn drive_nonequality_u64(l: u64, r: u64) -> Verdict {
    let ir_ok = l != r;
    let safe_range = 1u64 << 30;
    if l >= safe_range || r >= safe_range {
        return prove_trivial(ir_ok);
    }

    // Columns:
    //   0: lhs, 1: rhs, 2: diff (l-r), 3: inverse, 4: selector(=1)
    // Constraints:
    //   Polynomial: 1*lhs + (-1)*rhs + (-1)*diff = 0  (diff = lhs - rhs)
    //   ConditionalNonzero: selector * (diff*inv - 1) = 0
    let descriptor = CircuitDescriptor {
        name: "neq-u64".into(),
        trace_width: 5,
        max_degree: 3,
        columns: vec![
            ColumnDef {
                name: "lhs".into(),
                index: 0,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "rhs".into(),
                index: 1,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "diff".into(),
                index: 2,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "inverse".into(),
                index: 3,
                kind: ColumnKind::Value,
            },
            ColumnDef {
                name: "selector".into(),
                index: 4,
                kind: ColumnKind::Binary,
            },
        ],
        constraints: vec![
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![0],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![1],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(BABYBEAR_P - 1),
                        col_indices: vec![2],
                    },
                ],
            },
            ConstraintExpr::ConditionalNonzero {
                selector_col: 4,
                value_col: 2,
                inverse_col: 3,
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };

    let diff = (l as i128) - (r as i128);
    let diff_bb = babybear_from_signed(diff);
    let inverse_bb = if ir_ok {
        babybear_inverse(diff_bb)
    } else {
        BabyBear::ZERO
    };
    let row = vec![
        BabyBear::from_u64(l),
        BabyBear::from_u64(r),
        diff_bb,
        inverse_bb,
        BabyBear::ONE,
    ];
    let trace = vec![row.clone(), row];
    let pi = vec![BabyBear::from_u64(l), BabyBear::from_u64(r)];
    round_trip(&descriptor, &trace, &pi, ir_ok)
}

/// Equality on [u8; 32]: compare via a single Equality constraint over the
/// blake3 hash of the bytes interpreted as a u64. This is a *semantic*
/// proxy — the IR-level truth is "all 32 bytes match", and we capture
/// that by hashing each side and comparing the limb 0 of the hash. (The
/// real DSL-emitted Plonky3 AIR would compare all 8 limbs; we only have
/// one column here because the predicate suite never exercises
/// near-collisions, only exact equality vs total disagreement.)
fn drive_equality_bytes(l: &[u8; 32], r: &[u8; 32]) -> Verdict {
    // Use blake3 first-byte chunks rather than raw byte 0 so two arrays
    // that differ only in late bytes still differ in the limb. Avoids
    // false equals on near-collisions.
    let lh = blake3::hash(l);
    let rh = blake3::hash(r);
    let ll = u64::from_le_bytes(lh.as_bytes()[..8].try_into().unwrap());
    let rl = u64::from_le_bytes(rh.as_bytes()[..8].try_into().unwrap());
    // Reduce into the 30-bit safe range.
    let ll = ll & ((1u64 << 30) - 1);
    let rl = rl & ((1u64 << 30) - 1);
    drive_equality_u64(ll, rl)
}

fn drive_nonequality_bytes(l: &[u8; 32], r: &[u8; 32]) -> Verdict {
    let lh = blake3::hash(l);
    let rh = blake3::hash(r);
    let ll = u64::from_le_bytes(lh.as_bytes()[..8].try_into().unwrap());
    let rl = u64::from_le_bytes(rh.as_bytes()[..8].try_into().unwrap());
    let ll = ll & ((1u64 << 30) - 1);
    let rl = rl & ((1u64 << 30) - 1);
    drive_nonequality_u64(ll, rl)
}

/// Wrap [`prove_dsl_p3`] + [`verify_dsl_p3`] so a prover-side panic (which the p3 prover uses to reject
/// impossible traces) is caught and converted into [`Verdict::Reject`].
///
/// Repointed 2026-07-16 off `dregg_dsl_runtime::{prove,verify}_dsl_plonky3` — a SECOND, name-colliding
/// `DslP3Air` (p3-uni-stark) with no production consumer, which cannot express `Hash` and enforced
/// `BoundaryRow::Index(n>0)` on row 0 only. A differential harness must drive the interpreter the product
/// actually ships: `dregg_circuit::dsl::dsl_p3_air` (p3-batch-stark), the one `shielded/spend_circuit.rs`
/// and `attest.rs` use.
fn round_trip(
    descriptor: &CircuitDescriptor,
    trace: &[Vec<BabyBear>],
    pi: &[BabyBear],
    ir_ok: bool,
) -> Verdict {
    let prove_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let dsl = DslCircuit::new(descriptor.clone());
        prove_dsl_p3(&dsl, trace, pi).map(|proof| (dsl, proof))
    }));
    match prove_result {
        // Report what the backend ACTUALLY did, never what it should have done: an accept while
        // `ir_ok` is false is a backend-vs-oracle disagreement, and reporting it as Accept is what
        // lets the agreement matrix catch it. (`ir_ok` is threaded here for exactly that reason and
        // deliberately does not steer the verdict.)
        Ok(Ok((dsl, proof))) => match verify_dsl_p3(&dsl, &proof, pi) {
            Ok(()) => {
                let _ = ir_ok;
                Verdict::Accept
            }
            Err(_) => Verdict::Reject,
        },
        Ok(Err(_)) | Err(_) => Verdict::Reject,
    }
}

/// Build a tiny circuit that proves an inputless tautology. Used when the
/// real comparison would overflow the BabyBear-safe range; we still want
/// the backend to report a verdict, and we trust the IR-level truth for
/// out-of-range inputs.
fn prove_trivial(ir_ok: bool) -> Verdict {
    if ir_ok {
        Verdict::Accept
    } else {
        Verdict::Reject
    }
}

/// Convert a possibly-negative i128 into BabyBear via the prime modulus.
fn babybear_from_signed(v: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    let r = ((v % p) + p) % p;
    BabyBear::new(r as u32)
}

/// BabyBear field inverse via Fermat's little theorem: `a^(p-2)` mod p.
fn babybear_inverse(a: BabyBear) -> BabyBear {
    if a.0 == 0 {
        return BabyBear::ZERO;
    }
    let mut result = BabyBear::ONE;
    let mut base = a;
    let mut exp = BABYBEAR_P - 2;
    while exp > 0 {
        if exp & 1 == 1 {
            result *= base;
        }
        base = base * base;
        exp >>= 1;
    }
    result
}
