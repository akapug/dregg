//! SUPPLY-MODEL Stage 1 conservation property test (`.docs-history-noclaude/SUPPLY-MODEL.md`).
//!
//! Property: a `Burn` of ANY asset (default `[0u8;32]` or any non-default
//! `token_id`), for any amount up to the holder's balance, is a CONSERVING
//! holder→well MOVE — the per-asset ISSUER WELL is materialized (lazily, if
//! absent) and credited the burned amount, so the per-turn sum of ALL balance
//! deltas is exactly zero (Σδ=0). This closes the non-conserving-`destroy`
//! hole: before Stage 1 a well-less asset's burn was a bare debit (Σδ≠0).
//!
//! HONEST SCOPE: this asserts PER-TURN conservation (each burn nets zero), the
//! guarantee Stage 1 delivers. The STANDING invariant `Σholders + well = 0`
//! (the well as a proper −supply account) waits for Stage 2 (`Effect::Mint`
//! initializing the well to −supply at issuance); a lazily-created Stage-1 well
//! starts at 0 and goes POSITIVE as it accumulates burns. Authority is
//! unchanged: self-burn stays permissionless (Stage 3 would gate non-self/
//! issuer burns).

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::{Turn, TurnResult},
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

/// An open hosted cell with a chosen `token_id` (asset class) and balance.
fn open_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn self_burn_turn(agent: CellId, amount: u64) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Burn {
            target: agent,
            slot: 0,
            amount,
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

/// The deterministic per-asset well id — mirrors `derive_issuer_well`.
fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// Snapshot every cell's balance keyed by id.
fn balances(ledger: &Ledger) -> std::collections::HashMap<CellId, i64> {
    ledger
        .iter()
        .map(|(id, c)| (*id, c.state.balance()))
        .collect()
}

/// Sum of ALL per-cell balance deltas across the whole ledger (including any
/// lazily-created well, which appears as a delta from 0).
fn total_delta(
    before: &std::collections::HashMap<CellId, i64>,
    after: &std::collections::HashMap<CellId, i64>,
) -> i128 {
    let mut keys: std::collections::HashSet<&CellId> = before.keys().collect();
    keys.extend(after.keys());
    keys.into_iter()
        .map(|k| {
            let b = before.get(k).copied().unwrap_or(0) as i128;
            let a = after.get(k).copied().unwrap_or(0) as i128;
            a - b
        })
        .sum()
}

#[test]
fn burn_conserves_per_turn_across_assets_and_amounts() {
    // A corpus of (asset, balance, burn_amount) triples spanning the default
    // asset and several non-default assets, with varied amounts (partial,
    // full, small).
    let mut assets: Vec<[u8; 32]> = vec![[0u8; 32]];
    for marker in [1u8, 7, 42, 200, 255] {
        let mut t = [marker; 32];
        t[0] = marker.wrapping_add(3); // non-uniform so each asset differs
        assets.push(t);
    }

    let amounts: [(i64, u64); 4] = [
        (1_000, 1),     // tiny burn
        (1_000, 400),   // partial
        (777, 777),     // full
        (500_000, 123), // large balance, modest burn
    ];

    let mut case = 0usize;
    for token_id in &assets {
        for (balance, burn_amount) in amounts {
            let cell = open_cell((case % 250 + 1) as u8, *token_id, balance);
            let cell_id = cell.id();
            let well_id = derived_well_id(token_id);

            let mut ledger = Ledger::new();
            ledger.insert_cell(cell).unwrap();

            // Sanity: no well exists before the burn (lazy creation only).
            assert!(
                ledger.get(&well_id).is_none(),
                "well must not pre-exist (case {case})"
            );

            let before = balances(&ledger);
            let executor = TurnExecutor::new(ComputronCosts::zero());
            let result = executor.execute(&self_burn_turn(cell_id, burn_amount), &mut ledger);
            assert!(
                matches!(result, TurnResult::Committed { .. }),
                "self-burn must commit (case {case}): {result:?}"
            );
            let after = balances(&ledger);

            // PER-TURN CONSERVATION: every balance delta nets to zero.
            assert_eq!(
                total_delta(&before, &after),
                0,
                "per-turn Σδ must be zero (holder debit == well credit) (case {case})"
            );

            // The holder was debited exactly `burn_amount`.
            assert_eq!(
                ledger.get(&cell_id).unwrap().state.balance(),
                balance - burn_amount as i64,
                "holder debited by burn amount (case {case})"
            );

            // The well exists and carries the credit (it started at 0, so it is
            // exactly +burn_amount this turn — POSITIVE, per Stage-1 honesty).
            let well = ledger
                .get(&well_id)
                .expect("well must be lazily created and carry the credit");
            assert_eq!(
                well.state.balance(),
                burn_amount as i64,
                "well credited the burned amount (case {case})"
            );
            // The well is a real cell in the SAME asset class as the holder.
            assert_eq!(
                well.token_id(),
                token_id,
                "well must share the holder's asset class (case {case})"
            );

            case += 1;
        }
    }
}
