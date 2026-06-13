//! Cutover C1 validation — the ROTATED sovereign proof-carrying matched pair.
//!
//! This integration test drives the cutover's first coherent checkpoint
//! (ROTATION-CUTOVER §EXEC, C1): the sovereign producer
//! ([`AgentCipherclerk::execute_sovereign_turn_with_proof`]) now mints a rotated
//! R=24 `Ir2BatchProof` over the cohort descriptor (instead of the weak hand-AIR
//! `EffectVmAir`), carrying the v9 felt commitment; the matched verifier
//! (`dregg_turn`'s `executor::verify_and_commit_proof`, which graduates to
//! `descriptor_ir2::verify_vm_descriptor2`) reconstructs the 38-PI layout from
//! the after-state it holds and accepts.
//!
//! It lives in `sdk/tests/` (a self-contained compilation unit) rather than the
//! workspace `dregg-tests` harness so the C1 matched pair is validatable
//! independently. Requires the `recursion` feature (the SDK default), which
//! compiles the rotated producer + pulls `dregg-circuit/recursion` (the rotated
//! verifier). Under `not(recursion)` the rotated path does not exist, so the
//! test self-skips.

#![cfg(feature = "recursion")]

use dregg_cell::{Cell, CellId, CellMode, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{ComputronCosts, Effect, TurnExecutor, TurnResult};

/// Register a sovereign cell with the v9 commitment the rotated producer derives
/// for its before-state (single-cell `cells_root`, empty nullifier root, empty
/// receipt-chain `iroot`). The executor reads this back as OLD_COMMIT (PI 34).
fn setup_sovereign_cell(balance: u64) -> (AgentCipherclerk, CellId, Ledger) {
    let cclerk = AgentCipherclerk::new();
    let pub_key = cclerk.public_key().0;
    let token_id = *blake3::hash(b"c1-domain").as_bytes();

    let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();

    let nullifier_root = [0u8; 32];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let cells_root = dregg_turn::rotation_witness::cells_root(&ctx_ledger);
    let iroot = dregg_turn::rotation_witness::iroot(&[]);
    let v9_ctx = dregg_cell::commitment::V9RotationContext {
        cells_root,
        nullifier_root,
        iroot,
    };
    let commitment = dregg_cell::commitment::compute_canonical_state_commitment_v9(&cell, &v9_ctx);

    let mut cclerk = cclerk;
    cclerk.store_sovereign_state(cell.clone());

    let mut ledger = Ledger::new();
    ledger.register_sovereign_cell(cell_id, commitment).unwrap();
    let _ = ledger.insert_cell(cell);

    (cclerk, cell_id, ledger)
}

/// CONTROL: an honest rotated sovereign turn proves (rotated `Ir2BatchProof`) and
/// the executor ACCEPTS it through the rotated `verify_vm_descriptor2` leg, then
/// advances the stored v9 commitment.
#[test]
fn rotated_sovereign_turn_proves_and_verifies() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_cell = Cell::with_balance([42u8; 32], *blake3::hash(b"c1-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 100,
    }];

    let turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500)
        .expect("rotated sovereign turn should prove");

    // The proof is real, postcard-encoded (NOT the `DREG`-magic hand-AIR wire).
    let proof_bytes = turn
        .execution_proof
        .as_ref()
        .expect("execution_proof attached");
    assert!(!proof_bytes.is_empty());
    assert_ne!(&proof_bytes[0..4], b"DREG", "rotated wire is a postcard BatchProof");
    assert_eq!(turn.execution_proof_cell, Some(cell_id));
    assert!(turn.execution_proof_new_commitment.is_some());
    assert!(turn.sovereign_witnesses.is_empty());

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed { .. } => {}
        other => panic!("rotated sovereign turn must commit, got {other:?}"),
    }

    // The stored sovereign commitment advanced to the proven post-state (v9 felt).
    let new_commitment = ledger
        .get_sovereign_commitment(&cell_id)
        .expect("commitment present after commit");
    assert_eq!(*new_commitment, turn.execution_proof_new_commitment.unwrap());
}

/// ANTI-GHOST: a rotated sovereign turn whose claimed post-state commitment is
/// FORGED is REJECTED — the forged PI 35 disagrees with the trace's after-block
/// `STATE_COMMIT` carrier (the descriptor's col-261 `pi_binding`), so
/// `verify_vm_descriptor2` fails.
#[test]
fn rotated_sovereign_forged_post_state_is_rejected() {
    let (mut cclerk, cell_id, mut ledger) = setup_sovereign_cell(1000);

    let dest_cell = Cell::with_balance([43u8; 32], *blake3::hash(b"c1-domain").as_bytes(), 0);
    let dest_id = dest_cell.id();
    let _ = ledger.insert_cell(dest_cell);

    let effects = vec![Effect::Transfer {
        from: cell_id,
        to: dest_id,
        amount: 50,
    }];

    let mut turn = cclerk
        .execute_sovereign_turn_with_proof(&cell_id, effects, 500)
        .expect("rotated sovereign turn should prove");

    // Forge the claimed post-state commitment.
    turn.execution_proof_new_commitment = Some([0xFFu8; 32]);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            let s = format!("{reason:?}");
            assert!(
                s.contains("ProofVerificationFailed") || s.contains("rotated"),
                "expected a rotated verify rejection, got: {s}"
            );
        }
        other => panic!("ANTI-GHOST: forged post-state must be rejected, got {other:?}"),
    }
}
