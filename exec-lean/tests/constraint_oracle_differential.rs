//! DIFFERENTIAL GATE (game-proof LARP-audit, Step 2): the verified Lean deployed-constraint
//! evaluator (`dregg_constraint_admits`) and the deployed Rust evaluator (`cell/src/program/eval.rs`)
//! decide a shared corpus IDENTICALLY — INCLUDING the two boundaries the audit found DIVERGENT
//! (unsigned-256 fieldGe near the top bit; first-write-free heap `Immutable`). This converts the prose
//! "mirror" into a checked correspondence: it would have caught both original bugs, and it fails if the
//! Lean source and the Rust guest-path evaluator ever drift on the subset.
//!
//! NOTE: this test does NOT install the global oracle — so `CellProgram::evaluate` runs the RUST
//! evaluator, and the Lean side is read by calling `LeanConstraintOracle::admits` directly. That lets
//! us compare the two sources in one process.

use dregg_cell::program::{CellProgram, ConstraintOracle, HeapAtom, ProgramError};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint, field_from_u64};
use dregg_exec_lean::LeanConstraintOracle;

/// A 32-byte big-endian field element from a full 256-bit value given as a hex string.
fn field_hex(h: &str) -> [u8; 32] {
    let padded = format!("{:0>64}", h);
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&padded[i * 2..i * 2 + 2], 16).unwrap();
    }
    out
}

/// Compare accept/reject AND (on reject) the error VARIANT — the soundness-relevant equality.
fn agree(lean: &Result<(), ProgramError>, rust: &Result<(), ProgramError>) -> bool {
    match (lean, rust) {
        (Ok(()), Ok(())) => true,
        (Err(a), Err(b)) => std::mem::discriminant(a) == std::mem::discriminant(b),
        _ => false,
    }
}

fn check(c: StateConstraint, new: &CellState, old: Option<&CellState>) {
    if !dregg_lean_ffi::constraint_admits_available() {
        return; // skip on FFI-free targets
    }
    let oracle = LeanConstraintOracle;
    let lean = oracle
        .admits(&c, new, old)
        .expect("constraint is in the pure subset");
    // No oracle installed in this binary ⇒ evaluate() runs the RUST evaluator.
    let rust = CellProgram::Predicate(vec![c.clone()]).evaluate(new, old, None);
    assert!(
        agree(&lean, &rust),
        "LEAN vs RUST DISAGREE on {c:?}\n  lean={lean:?}\n  rust={rust:?}"
    );
}

fn reg(i: usize, v: u64) -> CellState {
    let mut s = CellState::default();
    s.fields[i] = field_from_u64(v);
    s
}

const HEAP_KEY: u64 = 20; // >= STATE_SLOTS(16) ⇒ the unbounded heap map

fn heap(key: u64, v: u64) -> CellState {
    let mut s = CellState::default();
    s.set_field_ext(key, field_from_u64(v));
    s
}

#[test]
fn field_gte_boundaries() {
    // equal, below, above.
    check(
        StateConstraint::FieldGte {
            index: 0,
            value: field_from_u64(5),
        },
        &reg(0, 5),
        None,
    );
    check(
        StateConstraint::FieldGte {
            index: 0,
            value: field_from_u64(5),
        },
        &reg(0, 4),
        None,
    );
    check(
        StateConstraint::FieldGte {
            index: 0,
            value: field_from_u64(5),
        },
        &reg(0, 6),
        None,
    );
}

#[test]
fn unsigned_top_bit_divergence() {
    // ⚑ DIVERGENCE (b): new reg[0] has the top bit set (2^255). Under UNSIGNED it is >= 1 (admit);
    // a signed-Int reading would call it negative (refuse). Rust IS unsigned, so both must ADMIT.
    let mut s = CellState::default();
    s.fields[0] = field_hex("8000000000000000000000000000000000000000000000000000000000000000");
    check(
        StateConstraint::FieldGte {
            index: 0,
            value: field_from_u64(1),
        },
        &s,
        None,
    );
    check(
        StateConstraint::FieldLte {
            index: 0,
            value: field_from_u64(1),
        },
        &s,
        None,
    );
}

#[test]
fn heap_immutable_divergence() {
    // ⚑ DIVERGENCE (a): first write (absent old) is FREE; flip after freezes; same is fine.
    let atom = HeapAtom::Immutable;
    let c = || StateConstraint::HeapField {
        key: HEAP_KEY,
        atom: atom.clone(),
    };
    // absent old, present new ⇒ first write free.
    check(c(), &heap(HEAP_KEY, 7), None);
    // present old=7, new=9 ⇒ frozen (refuse).
    check(c(), &heap(HEAP_KEY, 9), Some(&heap(HEAP_KEY, 7)));
    // present old=7, new=7 ⇒ admit.
    check(c(), &heap(HEAP_KEY, 7), Some(&heap(HEAP_KEY, 7)));
}

#[test]
fn heap_atoms() {
    let old = heap(HEAP_KEY, 5);
    check(
        StateConstraint::HeapField {
            key: HEAP_KEY,
            atom: HeapAtom::Gte {
                value: field_from_u64(3),
            },
        },
        &heap(HEAP_KEY, 5),
        None,
    );
    check(
        StateConstraint::HeapField {
            key: HEAP_KEY,
            atom: HeapAtom::Monotonic,
        },
        &heap(HEAP_KEY, 8),
        Some(&old),
    );
    check(
        StateConstraint::HeapField {
            key: HEAP_KEY,
            atom: HeapAtom::Monotonic,
        },
        &heap(HEAP_KEY, 2),
        Some(&old),
    );
    check(
        StateConstraint::HeapField {
            key: HEAP_KEY,
            atom: HeapAtom::DeltaEquals { d: 3 },
        },
        &heap(HEAP_KEY, 8),
        Some(&old),
    );
    check(
        StateConstraint::HeapField {
            key: HEAP_KEY,
            atom: HeapAtom::MemberOf { set: vec![5, 9] },
        },
        &heap(HEAP_KEY, 5),
        None,
    );
    check(
        StateConstraint::HeapField {
            key: HEAP_KEY,
            atom: HeapAtom::InRangeTwoSided { lo: 3, hi: 7 },
        },
        &heap(HEAP_KEY, 5),
        None,
    );
}

#[test]
fn transition_variants_and_errors() {
    // Immutable register: old present unchanged ⇒ admit; changed ⇒ refuse.
    check(
        StateConstraint::Immutable { index: 0 },
        &reg(0, 7),
        Some(&reg(0, 7)),
    );
    check(
        StateConstraint::Immutable { index: 0 },
        &reg(0, 9),
        Some(&reg(0, 7)),
    );
    // Immutable, old absent, nonce 0 ⇒ genesis ok. (default nonce is 0.)
    check(StateConstraint::Immutable { index: 0 }, &reg(0, 9), None);
    // Immutable, old absent, nonce != 0 ⇒ needsOld (TransitionCheckRequiresOldState).
    let mut n = reg(0, 9);
    n.nonce = 5;
    check(StateConstraint::Immutable { index: 0 }, &n, None);
    // WriteOnce / Monotonic / StrictMonotonic transitions.
    check(
        StateConstraint::WriteOnce { index: 0 },
        &reg(0, 9),
        Some(&reg(0, 0)),
    );
    check(
        StateConstraint::WriteOnce { index: 0 },
        &reg(0, 9),
        Some(&reg(0, 7)),
    );
    check(
        StateConstraint::Monotonic { index: 0 },
        &reg(0, 9),
        Some(&reg(0, 7)),
    );
    check(
        StateConstraint::StrictMonotonic { index: 0 },
        &reg(0, 7),
        Some(&reg(0, 7)),
    );
    // Index out of range ⇒ InvalidFieldIndex.
    check(
        StateConstraint::FieldEquals {
            index: 16,
            value: field_from_u64(0),
        },
        &reg(0, 0),
        None,
    );
}

#[test]
fn sum_equals() {
    let mut s = CellState::default();
    s.fields[0] = field_from_u64(3);
    s.fields[1] = field_from_u64(4);
    check(
        StateConstraint::SumEquals {
            indices: vec![0, 1],
            value: field_from_u64(7),
        },
        &s,
        None,
    );
    check(
        StateConstraint::SumEquals {
            indices: vec![0, 1],
            value: field_from_u64(8),
        },
        &s,
        None,
    );
}
