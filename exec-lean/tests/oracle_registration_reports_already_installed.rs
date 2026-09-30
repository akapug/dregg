//! #89: a second registration of a verified oracle in one process reports `AlreadyInstalled`, not
//! `Unavailable`. A node installs both oracles at boot and an SDK `AgentRuntime` in the same
//! process registers again; when `register_*` returned a bool, that second call read `false` and
//! the SDK logged that the archive "does NOT export" a decision it had just installed.
//!
//! Each test registers ONE oracle, so the two never share a slot even under a single-process
//! runner. Without the export the registration must say `Unavailable`; `DREGG_TEST_REQUIRE_LEAN=1`
//! makes that exit a failure instead of a skip.

use dregg_exec_lean::{OracleRegistration, register_conservation_oracle, register_constraint_oracle};

#[test]
fn a_second_constraint_registration_is_already_installed_not_unavailable() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::constraint_admits_available(),
        "dregg_constraint_admits export (the Lean-backed constraint oracle)",
    ) {
        assert_eq!(register_constraint_oracle(), OracleRegistration::Unavailable);
        return;
    }
    assert_eq!(register_constraint_oracle(), OracleRegistration::Installed);
    let second = register_constraint_oracle();
    assert_eq!(second, OracleRegistration::AlreadyInstalled);
    assert!(second.is_armed());
    assert!(dregg_cell::program::constraint_oracle_installed());
}

#[test]
fn a_second_conservation_registration_is_already_installed_not_unavailable() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::cross_cell_conserves_available(),
        "dregg_cross_cell_conserves export (the Lean-backed conservation oracle)",
    ) {
        assert_eq!(register_conservation_oracle(), OracleRegistration::Unavailable);
        return;
    }
    assert_eq!(register_conservation_oracle(), OracleRegistration::Installed);
    let second = register_conservation_oracle();
    assert_eq!(second, OracleRegistration::AlreadyInstalled);
    assert!(second.is_armed());
    assert!(dregg_turn::executor::conservation_oracle_installed());
}
