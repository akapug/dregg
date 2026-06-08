//! lean_state_producer_sidetable.rs — THE SWAP state-producer differential for the OFF-LEDGER
//! HOLDING-STORE families (escrow-create, obligation-create).
//!
//! `lean_state_producer_widen.rs` pinned the cell-state effect families (Transfer / SetField / Burn /
//! IncrementNonce / Revoke) and the lifecycle / cap-fidelity SWAP-GAPS. This file extends the producer
//! differential to the SIDE-TABLE CREATE families — the ones that LOCK value into an OFF-LEDGER store
//! (`self.escrows` / `self.obligations`) that does NOT feed `cell::Ledger::root()` — and PINS that they
//! ROUND-TRIP through the verified Lean producer with ZERO post-state divergence.
//!
//! # Why these round-trip on `.root()` despite touching a side-table
//!
//! `cell::Ledger::root()` hashes ONLY the cells (`compute_canonical_state_commitment` per cell). The
//! escrow / obligation records live in the executor's OWN tables, NOT in the `Ledger`, so they are
//! invisible to `.root()`. The ONLY cell-commitment field either family touches is the locker's asset-0
//! BALANCE:
//!   * `apply_create_escrow` (`apply.rs:1674`) DEBITS the creator's balance by `amount`
//!     (`set_balance(old - amount)`) and parks an unresolved `EscrowRecord` off-root;
//!   * `apply_create_obligation` (`apply.rs:1337`) DEBITS the obligor's (= action target's) balance by
//!     `stake_amount` and parks an `ObligationRecord` off-root.
//! The verified `createEscrowKAsset` / `createObligationA` (dispatch-aliased to `createEscrowChainA`) do
//! the SAME single-cell asset-0 DEBIT (`recBalCreditCell k.bal creator 0 (-amount)`) and park the record
//! off-root. The `bal` side-table carries the debit, so the reconstituted creator/obligor balance matches
//! Rust exactly, and every OTHER cell field is untouched — so `.root()` AGREES. This is the holding-store
//! analog of the `bal`-only round-trip the Transfer/Burn families already exercise.
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent.

#![cfg(feature = "lean-shadow")]

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_turn::lean_apply::{self, execute_via_lean};
use dregg_turn::lean_shadow::ShadowHostCtx;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

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

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![effect],
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
        valid_until: Some(1_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Compare two ledgers cell-by-cell (balance + nonce + the 8 state fields + the canonical capability
/// root) AND on `.root()`. Returns Ok(()) on full agreement or Err(why) on the first divergence.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        let r = rust.get(id).ok_or_else(|| format!("cell {id:?} missing from RUST ledger"))?;
        let l = lean.get(id).ok_or_else(|| format!("cell {id:?} missing from LEAN ledger"))?;
        if r.state.balance() != l.state.balance() {
            return Err(format!(
                "balance divergence on {id:?}: rust={} lean={}",
                r.state.balance(),
                l.state.balance()
            ));
        }
        if r.state.nonce() != l.state.nonce() {
            return Err(format!(
                "nonce divergence on {id:?}: rust={} lean={}",
                r.state.nonce(),
                l.state.nonce()
            ));
        }
        for slot in 0..dregg_cell::state::STATE_SLOTS {
            if r.state.fields[slot] != l.state.fields[slot] {
                return Err(format!(
                    "field[{slot}] divergence on {id:?}: rust={:?} lean={:?}",
                    r.state.fields[slot], l.state.fields[slot]
                ));
            }
        }
        let rc = dregg_cell::compute_canonical_capability_root(&r.capabilities);
        let lc = dregg_cell::compute_canonical_capability_root(&l.capabilities);
        if rc != lc {
            return Err(format!("cap_root divergence on {id:?}: rust={rc:?} lean={lc:?}"));
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// Run both producers and return `Ok(())` on full agreement, or `Err(why)` on the first divergence.
fn diff(pre: Ledger, turn: Turn, ids: &[CellId]) -> Result<(), String> {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!("legacy Rust executor did not commit: {rust_result:?}"));
    }

    let host = ShadowHostCtx::diag();
    let (mut lean_ledger, lean_committed) = match execute_via_lean(&turn, &pre, &host) {
        Ok(x) => x,
        Err(lean_apply::ExtractError::Ineligible) => {
            return Err("turn was Lean-ineligible (a marshaller GAP — no wire arm)".to_string());
        }
        Err(e) => return Err(format!("Lean state-producer path errored: {e}")),
    };
    if !lean_committed {
        return Err("commit-bit divergence: Rust committed, Lean did not".to_string());
    }
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, ids)
}

fn skip_no_lean() -> bool {
    if !dregg_lean_ffi::lean_available() {
        eprintln!("SKIP: Lean archive not linked (lean_available()==false)");
        true
    } else {
        false
    }
}

// =====================================================================================
// ROUND-TRIP — the holding-store CREATE families lock value into an OFF-ROOT store while
// debiting only the locker's asset-0 balance (carried by `bal`), so the reconstituted
// ledger AGREES on full cell state + cap_root + `.root()`.
// =====================================================================================

#[test]
fn create_escrow_round_trips() {
    if skip_no_lean() {
        return;
    }
    // A self-create escrow: `actor == creator` short-circuits the verified `authorizedB` (`actor == src`
    // ⇒ true), matching Rust's self-targeted lock; the creator's balance ≥ amount and a non-null,
    // unused id make BOTH executors commit. The lock DEBITS the creator's asset-0 balance by `amount`
    // (carried by `bal`) and parks an off-root `EscrowRecord` — so the reconstituted ledger agrees on
    // balance, cap_root, and `.root()`. The recipient must EXIST (Rust requires it) — it does.
    let creator = make_open_cell(1, 100);
    let recipient = make_open_cell(2, 5);
    let creator_id = creator.id();
    let recipient_id = recipient.id();
    let mut pre = Ledger::new();
    pre.insert_cell(creator).unwrap();
    pre.insert_cell(recipient).unwrap();

    let turn = single_effect_turn(
        creator_id,
        creator_id,
        0,
        Effect::CreateEscrow {
            cell: creator_id,
            recipient: recipient_id,
            amount: 40,
            condition: dregg_turn::EscrowCondition::PredicateSatisfied { predicate_hash: [7u8; 32] },
            timeout_height: 10_000,
            escrow_id: [9u8; 32],
        },
    );

    // Confirm Rust really LOCKED (debited the creator) so the round-trip is about a genuine balance move.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(executor.execute(&turn, &mut rust_ledger).is_committed(), "Rust CreateEscrow should commit");
    assert_eq!(
        rust_ledger.get(&creator_id).unwrap().state.balance(),
        60,
        "Rust must have debited the creator by the escrow amount"
    );

    diff(pre, turn, &[creator_id, recipient_id])
        .expect("CreateEscrow must round-trip through the verified producer");
}

#[test]
fn create_obligation_round_trips() {
    if skip_no_lean() {
        return;
    }
    // CreateObligation locks a BOND: dregg1 debits the obligor (= action target) by `stake_amount` and
    // parks an off-root `ObligationRecord`; the verified `createObligationA` dispatch-aliases to
    // `createEscrowChainA` (the SAME single-cell debit + record insert). Self-targeted (obligor = actor)
    // passes `authorizedB`; the beneficiary must exist (it does). Only the obligor's asset-0 balance
    // moves (carried by `bal`), the record is off-root — so the reconstituted ledger agrees on `.root()`.
    let obligor = make_open_cell(3, 100);
    let beneficiary = make_open_cell(4, 5);
    let obligor_id = obligor.id();
    let beneficiary_id = beneficiary.id();
    let mut pre = Ledger::new();
    pre.insert_cell(obligor).unwrap();
    pre.insert_cell(beneficiary).unwrap();

    let turn = single_effect_turn(
        obligor_id,
        obligor_id,
        0,
        Effect::CreateObligation {
            beneficiary: beneficiary_id,
            condition: dregg_turn::ProofCondition::HashPreimage { hash: [0u8; 32] },
            deadline_height: 10_000,
            stake: dregg_cell::NoteCommitment([0xAA; 32]),
            stake_amount: 30,
        },
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = pre.clone();
    assert!(
        executor.execute(&turn, &mut rust_ledger).is_committed(),
        "Rust CreateObligation should commit"
    );
    assert_eq!(
        rust_ledger.get(&obligor_id).unwrap().state.balance(),
        70,
        "Rust must have debited the obligor by the stake amount"
    );

    diff(pre, turn, &[obligor_id, beneficiary_id])
        .expect("CreateObligation must round-trip through the verified producer");
}
