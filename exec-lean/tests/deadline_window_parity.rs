//! The deadline window, decided by both executors on the covered path.
//!
//! `Turn.valid_until` is a block height. The Rust executor admits a turn while
//! `block_height ≤ valid_until ≤ block_height + MAX_TURN_VALIDITY_HORIZON_BLOCKS` and refuses a
//! deadline on an executor with no height (`dregg_turn::check_deadline`). The verified kernel runs
//! the same leg (`Dregg2.Exec.Admission.expiryOk`, horizon `maxTurnValidityHorizon`). On a covered
//! turn Lean's verdict is authoritative, so a Lean admission where Rust refuses would COMMIT the
//! turn: the two legs must agree at every edge, and this file drives both through
//! `produce_via_lean` at each one.
//!
//! The two horizon edges together pin the Lean constant to the Rust one: `height + MAX` committing
//! means Lean's horizon is at least MAX, and `height + MAX + 1` being refused by Lean (the
//! verdict is Lean's, and no Rust bug is surfaced) means it is at most MAX.
//!
//! Run (needs the Lean archive):
//!   DREGG_TEST_REQUIRE_LEAN=1 cargo nextest run -p dregg-exec-lean --test deadline_window_parity

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect,
    MAX_TURN_VALIDITY_HORIZON_BLOCKS, TurnError, TurnExecutor, turn::Turn,
};

const HEIGHT: u64 = 1000;

fn executor_at(height: u64) -> TurnExecutor {
    let mut executor = TurnExecutor::new(ComputronCosts::zero())
        .with_shadow_observer(dregg_exec_lean::LeanShadowObserver::arc());
    executor.set_block_height(height);
    // A wall clock far past every deadline below: a seconds comparison would refuse the
    // in-window cases, so their commits show the clock is the height.
    executor.set_timestamp(1_760_000_000);
    executor
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn one_cell_ledger() -> (Ledger, CellId) {
    let mut pk = [0u8; 32];
    pk[0] = 1;
    pk[31] = 41;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 100);
    cell.permissions = open_permissions();
    let id = cell.id();
    let mut l = Ledger::new();
    l.insert_cell(cell).unwrap();
    (l, id)
}

/// A low-64 wire-carriable field value, so the SetField turn is in the covered set.
const WIRE_CARRIABLE_FIELD: [u8; 32] = {
    let mut v = [0u8; 32];
    v[31] = 0x5a;
    v
};

fn set_field_turn(agent: CellId, valid_until: i64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: agent,
            index: 3,
            value: WIRE_CARRIABLE_FIELD,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(valid_until),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn require_lean() -> bool {
    dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "verified Turn executor archive (lean_available)",
    )
}

/// Drive one deadline at one height through the authoritative producer. Asserts the turn was
/// COVERED (Lean decided it) and that the two executors agreed; returns the result.
fn decide(height: u64, valid_until: i64) -> dregg_turn::TurnResult {
    let (mut ledger, agent) = one_cell_ledger();
    let executor = executor_at(height);
    let (result, outcome) = dregg_exec_lean::produce_via_lean(
        &executor,
        &set_field_turn(agent, valid_until),
        &mut ledger,
    );
    assert!(
        matches!(
            outcome,
            dregg_exec_lean::ProducerOutcome::LeanAuthoritative { .. }
        ),
        "height {height}, valid_until {valid_until}: the turn must be covered, got {outcome:?}"
    );
    assert!(
        !outcome.rust_bug_surfaced(),
        "height {height}, valid_until {valid_until}: Lean and Rust must agree on the deadline, \
         got {outcome:?}"
    );
    result
}

#[test]
fn inside_the_window_both_executors_commit() {
    if !require_lean() {
        return;
    }
    let max = MAX_TURN_VALIDITY_HORIZON_BLOCKS as i64;
    let h = HEIGHT as i64;
    for valid_until in [h, h + 1800, h + max] {
        let result = decide(HEIGHT, valid_until);
        assert!(
            result.is_committed(),
            "valid_until {valid_until} at height {HEIGHT} must commit, got {result:?}"
        );
    }
}

#[test]
fn below_the_window_both_executors_refuse_as_expired() {
    if !require_lean() {
        return;
    }
    let (reason, _) = decide(HEIGHT, HEIGHT as i64 - 1).unwrap_rejected();
    assert_eq!(
        reason,
        TurnError::Expired {
            valid_until: HEIGHT as i64 - 1,
            height: HEIGHT,
        }
    );
}

#[test]
fn above_the_window_both_executors_refuse_including_a_seconds_deadline() {
    if !require_lean() {
        return;
    }
    let one_past = HEIGHT as i64 + MAX_TURN_VALIDITY_HORIZON_BLOCKS as i64 + 1;
    for valid_until in [one_past, 1_760_000_000] {
        let (reason, _) = decide(HEIGHT, valid_until).unwrap_rejected();
        assert_eq!(
            reason,
            TurnError::DeadlineBeyondHorizon {
                valid_until,
                height: HEIGHT,
                max_horizon: MAX_TURN_VALIDITY_HORIZON_BLOCKS,
            }
        );
    }
}

#[test]
fn without_a_height_both_executors_refuse_a_deadline() {
    if !require_lean() {
        return;
    }
    let (reason, _) = decide(0, 10).unwrap_rejected();
    assert_eq!(reason, TurnError::DeadlineWithoutHeight { valid_until: 10 });
}
