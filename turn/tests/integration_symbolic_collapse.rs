//! SYMBOLIC EXECUTION — the witness-mode + collapse soundness tests.
//!
//! These exercise the three load-bearing guarantees of `crate::collapse`:
//!
//!   (a) a Symbolic turn APPLIES the state transition (balances move) WITHOUT
//!       materializing a Merkle witness (the receipt carries the deferred
//!       sentinel state-hash, not a real root);
//!   (b) `collapse` re-running the recorded symbolic turns under Full execution
//!       reproduces the SAME final root + receipts a Full run would have;
//!   (c) Full mode is byte-identical to before symbolic mode existed (no
//!       regression — same receipts as a default-Full executor).
//!
//! Plus the SOUNDNESS guard: a turn rejected in Full is rejected in Symbolic
//! (admission is mode-independent — only the witness is deferred, never the
//! decision).

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    collapse::{DEFERRED_STATE_HASH, WitnessMode, collapse, is_deferred},
    turn::{Turn, TurnResult},
};

// ---------------------------------------------------------------------------
// Shared helpers (mirror integration_lifecycle.rs)
// ---------------------------------------------------------------------------

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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn zero_executor() -> TurnExecutor {
    TurnExecutor::new(ComputronCosts::zero())
}

fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
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

/// A fresh 3-cell ledger (alice, bob, carol) and their ids.
fn three_cell_ledger() -> (Ledger, CellId, CellId, CellId) {
    let mut ledger = Ledger::new();
    let alice = make_open_cell(0x01, 1_000);
    let bob = make_open_cell(0x02, 0);
    let carol = make_open_cell(0x03, 0);
    let (ai, bi, ci) = (alice.id(), bob.id(), carol.id());
    ledger.insert_cell(alice).unwrap();
    ledger.insert_cell(bob).unwrap();
    ledger.insert_cell(carol).unwrap();
    (ledger, ai, bi, ci)
}

/// Drive a turn through an executor exactly as the live commit path does
/// (thread + advance the chain head). Returns the committed receipt.
fn drive(
    exec: &TurnExecutor,
    ledger: &mut Ledger,
    mut turn: Turn,
) -> dregg_turn::turn::TurnReceipt {
    turn.previous_receipt_hash = exec.get_last_receipt_hash(&turn.agent);
    match exec.execute(&turn, ledger) {
        TurnResult::Committed { receipt, .. } => {
            exec.set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
            receipt
        }
        other => panic!("expected commit, got {other:?}"),
    }
}

// ===========================================================================
// (a) A symbolic turn applies the state transition WITHOUT a materialized root.
// ===========================================================================

#[test]
fn symbolic_turn_applies_transition_without_witness() {
    let (mut ledger, alice, bob, _carol) = three_cell_ledger();
    let exec = zero_executor();
    exec.set_witness_mode(WitnessMode::Symbolic);
    assert!(exec.is_symbolic());

    let t = bare_turn(
        alice,
        0,
        vec![Effect::Transfer {
            from: alice,
            to: bob,
            amount: 250,
        }],
    );
    let receipt = drive(&exec, &mut ledger, t);

    // The STATE TRANSITION fully applied — balances moved (the AbstractState
    // progress is mode-independent).
    assert_eq!(ledger.get(&alice).unwrap().state.balance(), 750);
    assert_eq!(ledger.get(&bob).unwrap().state.balance(), 250);

    // But the WITNESS was DEFERRED: the receipt carries the deferred sentinel,
    // not a real Merkle root.
    assert_eq!(receipt.post_state_hash, DEFERRED_STATE_HASH);
    assert_eq!(receipt.pre_state_hash, DEFERRED_STATE_HASH);
    assert!(
        is_deferred(&receipt),
        "symbolic receipt must be flagged deferred"
    );
}

// ===========================================================================
// (c) Full mode is byte-identical to a default-Full executor (no regression).
// ===========================================================================

#[test]
fn full_mode_is_byte_identical_to_default() {
    // A default executor (no mode ever set — the pre-symbolic behavior).
    let (mut l_default, alice, bob, _c) = three_cell_ledger();
    let exec_default = zero_executor();
    let r_default = drive(
        &exec_default,
        &mut l_default,
        bare_turn(
            alice,
            0,
            vec![Effect::Transfer {
                from: alice,
                to: bob,
                amount: 250,
            }],
        ),
    );

    // An executor explicitly set to Full.
    let (mut l_full, alice2, bob2, _c2) = three_cell_ledger();
    assert_eq!((alice, bob), (alice2, bob2), "deterministic cell ids");
    let exec_full = zero_executor();
    exec_full.set_witness_mode(WitnessMode::Full);
    let r_full = drive(
        &exec_full,
        &mut l_full,
        bare_turn(
            alice2,
            0,
            vec![Effect::Transfer {
                from: alice2,
                to: bob2,
                amount: 250,
            }],
        ),
    );

    // Byte-identical receipts (same receipt_hash) and a REAL, non-deferred root.
    assert_eq!(r_default.receipt_hash(), r_full.receipt_hash());
    assert_eq!(r_default.post_state_hash, r_full.post_state_hash);
    assert_ne!(r_full.post_state_hash, DEFERRED_STATE_HASH);
    assert!(!is_deferred(&r_full));
}

// ===========================================================================
// (b) collapse(symbolic run) reproduces the SAME final root + receipts a Full
//     run would have produced.
// ===========================================================================

#[test]
fn collapse_reproduces_full_run() {
    // The symbolic run: three turns, witnesses deferred.
    let (mut sym_ledger, alice, bob, carol) = three_cell_ledger();
    let sym_pre = sym_ledger.clone(); // the pre-symbolic base, for collapse seeding
    let sym_exec = zero_executor();
    sym_exec.set_witness_mode(WitnessMode::Symbolic);

    let turns = vec![
        bare_turn(
            alice,
            0,
            vec![Effect::Transfer {
                from: alice,
                to: bob,
                amount: 300,
            }],
        ),
        bare_turn(
            bob,
            0,
            vec![Effect::Transfer {
                from: bob,
                to: carol,
                amount: 100,
            }],
        ),
        bare_turn(
            alice,
            1,
            vec![Effect::Transfer {
                from: alice,
                to: carol,
                amount: 50,
            }],
        ),
    ];
    for t in &turns {
        let r = drive(&sym_exec, &mut sym_ledger, t.clone());
        assert!(is_deferred(&r), "every symbolic receipt is deferred");
    }
    let sym_final_balances = (
        sym_ledger.get(&alice).unwrap().state.balance(),
        sym_ledger.get(&bob).unwrap().state.balance(),
        sym_ledger.get(&carol).unwrap().state.balance(),
    );

    // The Full run: the SAME turns through a Full executor (the ground truth).
    let (mut full_ledger, _a, _b, _c) = three_cell_ledger();
    let full_exec = zero_executor(); // Full by default
    let mut full_receipts = Vec::new();
    for t in &turns {
        full_receipts.push(drive(&full_exec, &mut full_ledger, t.clone()));
    }
    // The Full run's HEAD is its last receipt's AIR-bound post-state anchor
    // (`dregg_turn::state_commit`) — the object `CollapseResult::final_root` now
    // carries, replacing the trusted-Rust BLAKE3 `ledger.root()`. Same
    // assertion strength: collapse must land on exactly the Full run's head.
    let full_final_root = full_receipts
        .last()
        .expect("the Full run committed at least one turn")
        .post_state_hash;

    // COLLAPSE the recorded symbolic run: re-run through Full from the same
    // pre-state base. (collapse pins its own Full executor to the timestamp.)
    let collapsed = collapse(&turns, sym_pre, 0, ComputronCosts::zero())
        .expect("collapse must succeed (symbolic admitted only Full-legal turns)");

    // The final root matches the Full run.
    assert_eq!(
        collapsed.final_root, full_final_root,
        "collapse must reproduce the Full final root"
    );

    // Every collapsed receipt is byte-identical to the Full run's, and is now a
    // REAL witness (no longer deferred).
    assert_eq!(collapsed.receipts.len(), full_receipts.len());
    for (c, f) in collapsed.receipts.iter().zip(full_receipts.iter()) {
        assert!(
            !is_deferred(c),
            "a collapsed receipt carries a real witness"
        );
        assert_eq!(
            c.receipt_hash(),
            f.receipt_hash(),
            "collapse == Full receipt"
        );
        assert_eq!(c.post_state_hash, f.post_state_hash);
    }

    // And the symbolic state transition equalled the Full one all along (the
    // abstract progress was identical; only the witness was deferred).
    assert_eq!(
        sym_final_balances,
        (
            full_ledger.get(&alice).unwrap().state.balance(),
            full_ledger.get(&bob).unwrap().state.balance(),
            full_ledger.get(&carol).unwrap().state.balance(),
        )
    );
}

// ===========================================================================
// SOUNDNESS GUARD: admission is mode-independent — a turn rejected in Full is
// rejected in Symbolic, identically. The witness is deferred; the DECISION is
// never deferred.
// ===========================================================================

#[test]
fn symbolic_does_not_relax_admission() {
    // An over-spend (insufficient balance) must be rejected in BOTH modes.
    let bad_transfer = |from: CellId, to: CellId| {
        bare_turn(
            from,
            0,
            vec![Effect::Transfer {
                from,
                to,
                amount: 10_000,
            }],
        )
    };

    let (mut l_full, alice, bob, _c) = three_cell_ledger();
    let exec_full = zero_executor();
    let mut t = bad_transfer(alice, bob);
    t.previous_receipt_hash = exec_full.get_last_receipt_hash(&t.agent);
    let full_rejected = matches!(
        exec_full.execute(&t, &mut l_full),
        TurnResult::Rejected { .. }
    );

    let (mut l_sym, alice2, bob2, _c2) = three_cell_ledger();
    let exec_sym = zero_executor();
    exec_sym.set_witness_mode(WitnessMode::Symbolic);
    let mut t2 = bad_transfer(alice2, bob2);
    t2.previous_receipt_hash = exec_sym.get_last_receipt_hash(&t2.agent);
    let sym_rejected = matches!(
        exec_sym.execute(&t2, &mut l_sym),
        TurnResult::Rejected { .. }
    );

    assert!(full_rejected, "an over-spend is rejected in Full");
    assert!(
        sym_rejected,
        "an over-spend is rejected IDENTICALLY in Symbolic"
    );

    // And the rejecting ledgers are equal: neither mode edited state on refusal.
    assert_eq!(l_full.get(&alice).unwrap().state.balance(), 1_000);
    assert_eq!(l_sym.get(&alice2).unwrap().state.balance(), 1_000);
}
