//! Integration differential for the **policy-combinator core** —
//! `MemberOf` / `PrefixOf` / `InRangeTwoSided` / `DeltaBounded` / `AffineLe` /
//! `AffineEq` / `Reachable` / `AllOf` — the Rust mirror of the verified Lean
//! atom set (`metatheory/Dregg2/Exec/Program.lean`).
//!
//! Each test is the admit/reject NON-VACUITY pair that the Lean side proves by
//! `#guard`/`by decide` (`roleProgram`, `nsProgram`, `priceProgram`,
//! `jitterProgram`, `bandProgram`, `consvProgram`, `workflowProgram`). Running
//! them here through the full `CellProgram::evaluate` → `evaluate_constraint_full`
//! dispatch is the executable Rust↔Lean differential: the two transcriptions of
//! the same atom semantics must AGREE on admit AND reject.
//!
//! (An integration target — it links only the crate's public API, so it is
//! independent of any in-crate `#[cfg(test)]` module.)

use dregg_cell::{
    program::{field_from_u64, SimpleStateConstraint},
    CellProgram, CellState, StateConstraint,
};

/// `MemberOf` — Lean `roleProgram`: role ∈ {1,2,3}.
#[test]
fn member_of_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::MemberOf {
        index: 0,
        set: vec![1, 2, 3],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(2);
    assert!(p.evaluate(&s, None, None).is_ok(), "2 ∈ set ⇒ admit");
    s.fields[0] = field_from_u64(9);
    assert!(p.evaluate(&s, None, None).is_err(), "9 ∉ set ⇒ reject");
}

/// `PrefixOf` — Lean `nsProgram`: path must start with [10,20]; fail-closed when shorter.
#[test]
fn prefix_of_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::PrefixOf {
        seg_indices: vec![0, 1, 2],
        prefix: vec![10, 20],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(10);
    s.fields[1] = field_from_u64(20);
    s.fields[2] = field_from_u64(7);
    assert!(p.evaluate(&s, None, None).is_ok(), "[10,20,7] starts with [10,20]");
    s.fields[1] = field_from_u64(99);
    assert!(p.evaluate(&s, None, None).is_err(), "[10,99,7] ⇏ prefix");

    let p_short = CellProgram::Predicate(vec![StateConstraint::PrefixOf {
        seg_indices: vec![0],
        prefix: vec![10, 20],
    }]);
    assert!(
        p_short.evaluate(&s, None, None).is_err(),
        "path shorter than prefix ⇒ fail-closed"
    );
}

/// `InRangeTwoSided` — Lean `priceProgram`: 100 ≤ price ≤ 200.
#[test]
fn in_range_two_sided_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::InRangeTwoSided {
        index: 0,
        lo: 100,
        hi: 200,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(150);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(250);
    assert!(p.evaluate(&s, None, None).is_err(), "250 > 200 ⇒ reject");
}

/// `DeltaBounded` — Lean `jitterProgram`: |new − old| ≤ 5 (REAL two-sided).
#[test]
fn delta_bounded_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::DeltaBounded { index: 0, d: 5 }]);
    let mut old = CellState::new(1);
    old.fields[0] = field_from_u64(100);
    let mut new_s = CellState::new(2);
    for (v, ok) in [(104u64, true), (96, true), (110, false), (90, false)] {
        new_s.fields[0] = field_from_u64(v);
        assert_eq!(
            p.evaluate(&new_s, Some(&old), None).is_ok(),
            ok,
            "delta to {v} (from 100) admit={ok}"
        );
    }
}

/// `AffineLe` — Lean `bandProgram`: 2·bid − ask ≤ 100.
#[test]
fn affine_le_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::AffineLe {
        terms: vec![(2, 0), (-1, 1)],
        c: 100,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(60);
    s.fields[1] = field_from_u64(40); // 120−40 = 80 ≤ 100
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(90); // 180−40 = 140 > 100
    assert!(p.evaluate(&s, None, None).is_err());
}

/// `AffineEq` — Lean `consvProgram`: inp − o0 − o1 = 0 (conservation).
#[test]
fn affine_eq_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::AffineEq {
        terms: vec![(1, 0), (-1, 1), (-1, 2)],
        c: 0,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(10);
    s.fields[1] = field_from_u64(6);
    s.fields[2] = field_from_u64(4); // 10−6−4 = 0
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[2] = field_from_u64(3); // 10−6−3 = 1 ≠ 0
    assert!(p.evaluate(&s, None, None).is_err());
}

/// `Reachable` — Lean `workflowProgram`: step must reach prerequisite 1 in DAG 3→2→1.
#[test]
fn reachable_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::Reachable {
        from_index: 0,
        to_label: 1,
        edges: vec![(3, 2), (2, 1)],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(3); // publish reaches drafted (3→2→1)
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(4); // 4 ∉ DAG ⇒ unreachable
    assert!(p.evaluate(&s, None, None).is_err());
}

/// `AllOf` — the n-ary Boolean conjunction (mirrors Lean `Pred.allOf`): 10 ≤ v ≤ 20.
/// Empty `AllOf` admits (mirrors `Pred.allOf_nil_admits`).
#[test]
fn all_of_differential() {
    let p = CellProgram::Predicate(vec![StateConstraint::AllOf {
        variants: vec![
            SimpleStateConstraint::FieldGte {
                index: 0,
                value: field_from_u64(10),
            },
            SimpleStateConstraint::FieldLte {
                index: 0,
                value: field_from_u64(20),
            },
        ],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(15);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(25);
    assert!(p.evaluate(&s, None, None).is_err(), "25 > 20 ⇒ second conjunct fails");

    let p_empty = CellProgram::Predicate(vec![StateConstraint::AllOf { variants: vec![] }]);
    assert!(p_empty.evaluate(&s, None, None).is_ok(), "empty AllOf admits (vacuous AND)");
}
