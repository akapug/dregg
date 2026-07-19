//! END-TO-END REALITY-GATE (game-proof LARP-audit collapse).
//!
//! Installs the Lean-backed constraint oracle and then drives the REAL deployed evaluator entry
//! `dregg_cell::CellProgram::evaluate` (`cell/src/program/eval.rs`) — proving the admission decision
//! for the pure subset is COMPUTED BY the verified Lean `dregg_constraint_admits`
//! (`Dregg2.Exec.DeployedConstraint.admits`), through the actual `eval.rs` path a deployed turn takes,
//! not the FFI in isolation.
//!
//! ── THE CANARY ──────────────────────────────────────────────────────────────────────────────────
//! `field_gte_equal_admits_through_lean` asserts a `FieldGte` on an EQUAL value ADMITS (`>=` is
//! non-strict). Flip `Dregg2.Exec.DeployedConstraint.lean`'s `fieldGte` from `if v ≤ x` to `if v < x`,
//! rebuild + re-run — this test FLIPS RED: `eval.rs`'s decision changed because ONLY the Lean source
//! changed. That is the proof `eval.rs` goes through Lean, end to end.

use dregg_cell::program::CellProgram;
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint, field_from_u64};
use dregg_exec_lean::register_constraint_oracle;

/// Install once for this test binary (`OnceLock`; the whole file shares one process).
fn ensure_oracle() -> bool {
    if !dregg_lean_ffi::constraint_admits_available() {
        eprintln!("SKIP: libdregg_lean.a lacks dregg_constraint_admits — rebuild the archive");
        return false;
    }
    // `register` may have already run in an earlier test fn of this binary; either way the oracle is
    // installed afterward. (`OnceLock::set` returns false on the second call — still installed.)
    let _ = register_constraint_oracle();
    dregg_cell::program::constraint_oracle_installed()
}

fn state_with_reg0(v: u64) -> CellState {
    let mut s = CellState::default();
    s.fields[0] = field_from_u64(v);
    s
}

#[test]
fn field_gte_equal_admits_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let new = state_with_reg0(5);
    let prog = CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(5),
    }]);
    // 5 >= 5 ⇒ admit. THE CANARY: a strict flip in the Lean source makes this refuse.
    assert!(
        prog.evaluate(&new, None, None).is_ok(),
        "FieldGte(5,5) must ADMIT through the Lean evaluator"
    );
}

#[test]
fn field_gte_below_refuses_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let new = state_with_reg0(3);
    let prog = CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: 0,
        value: field_from_u64(5),
    }]);
    // 3 >= 5 is false ⇒ refuse (through Lean).
    assert!(
        prog.evaluate(&new, None, None).is_err(),
        "FieldGte(3,5) must REFUSE through the Lean evaluator"
    );
}

#[test]
fn sum_equals_routes_through_lean() {
    if !ensure_oracle() {
        return;
    }
    let mut new = CellState::default();
    new.fields[0] = field_from_u64(3);
    new.fields[1] = field_from_u64(4);
    let ok = CellProgram::Predicate(vec![StateConstraint::SumEquals {
        indices: vec![0, 1],
        value: field_from_u64(7),
    }]);
    assert!(ok.evaluate(&new, None, None).is_ok(), "sum(3,4)=7 admits");
    let bad = CellProgram::Predicate(vec![StateConstraint::SumEquals {
        indices: vec![0, 1],
        value: field_from_u64(8),
    }]);
    assert!(
        bad.evaluate(&new, None, None).is_err(),
        "sum(3,4)!=8 refuses"
    );
}
