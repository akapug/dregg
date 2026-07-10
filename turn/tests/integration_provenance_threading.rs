//! EXECUTOR PROVENANCE THREADING — collision-freedom across slot reuse.
//!
//! The revocation campaign's `provenance` field is meant to be collision-free
//! when a `(cell, slot)` is reused (revoke-then-regrant): folding the creating
//! turn's INPUT hash into the derived provenance makes the regrant a DISTINCT
//! derivation-node identity from the revoked instance, so the regranted cap is
//! NOT born carrying the revoked instance's `cred_nul` (a permanently-poisoned
//! slot — a liveness bug).
//!
//! Before this fix the executor's grant arm installed via the context-free
//! `grant_ref` (turn = `NO_TURN_CONTEXT = [0u8; 32]`), so two structurally
//! identical grants at the same `(target, slot)` in DIFFERENT turns produced
//! the IDENTICAL provenance. These tests exercise the real executor grant path
//! (`apply_grant_capability` → `grant_ref_provenanced`), holding
//! `(target, slot, parent_provenance)` CONSTANT and varying ONLY the turn:
//!
//!  * `..._collision_free_across_turns` — different turn ⇒ DIFFERENT provenance
//!    (and different `cred_nul`): the fix. Without threading these would be equal.
//!  * `..._deterministic_for_identical_turn` — identical turn ⇒ IDENTICAL
//!    provenance: proves the divergence above is caused SPECIFICALLY by the turn
//!    hash (non-vacuity), and that provenance is otherwise deterministic.

use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A wire capability (the untrusted PARENT the executor recomputes provenance
/// from). `slot`/`provenance` are advisory — the recipient c-list assigns a
/// fresh slot and RECOMPUTES the installed provenance chaining this one.
fn wire_cap(target: CellId) -> dregg_cell::CapabilityRef {
    dregg_cell::CapabilityRef {
        target,
        slot: 0,
        permissions: AuthRequired::None,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        // A fixed, non-zero "parent" provenance: held CONSTANT across every turn
        // in these tests so the ONLY varying input is the turn hash.
        provenance: [0x11u8; 32],
    }
}

/// A one-effect turn granting `cap` from `owner` (self-grant: `cap.target ==
/// owner`) to `recipient`. `memo` perturbs `Turn::hash()` without touching the
/// grant coordinates, so two turns can differ ONLY in their input hash.
fn grant_turn(
    owner: CellId,
    recipient: CellId,
    cap: dregg_cell::CapabilityRef,
    nonce: u64,
    memo: Option<String>,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: owner, // from == action_target ⇒ no cross-cell Delegate check
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::GrantCapability {
            from: owner,
            to: recipient,
            cap,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent: owner,
        nonce,
        call_forest: forest,
        fee: 0,
        memo,
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

/// Grant `owner`'s self-cap to a FRESH recipient (empty c-list, `next_slot = 0`)
/// via the real executor and return the installed cap's provenance at slot 0.
/// `recipient_seed` is fixed by callers so the recipient CellId is identical
/// across invocations — `(target, slot)` held constant, turn varied.
fn install_and_read_provenance(
    owner_seed: u8,
    recipient_seed: u8,
    nonce: u64,
    memo: Option<String>,
) -> [u8; 32] {
    let owner = make_open_cell(owner_seed, 1_000);
    let owner_id = owner.id();
    let recipient = make_open_cell(recipient_seed, 0);
    let recipient_id = recipient.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(owner).unwrap();
    ledger.insert_cell(recipient).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let turn = grant_turn(owner_id, recipient_id, wire_cap(owner_id), nonce, memo);
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "grant turn must commit; got {result:?}"
    );

    let installed = ledger
        .get(&recipient_id)
        .expect("recipient present")
        .capabilities
        .lookup(0)
        .expect("granted cap installed at slot 0");
    assert_eq!(installed.target, owner_id, "cap targets owner");
    assert_eq!(installed.slot, 0, "recipient assigned slot 0");
    installed.provenance
}

/// THE FIX: revoke-then-regrant collision-freedom. Same `(target, slot=0,
/// parent_provenance)` reused across two DIFFERENT turns ⇒ DISTINCT provenance
/// (hence distinct `cred_nul`), so a regrant is never born poisoned by the
/// revoked instance's revocation key. Without turn threading these are EQUAL.
#[test]
fn grant_provenance_collision_free_across_turns() {
    // Same recipient id + slot 0 + same wire parent in BOTH; only the turn hash
    // differs (via memo — each runs on a fresh ledger at agent nonce 0).
    let p_alpha = install_and_read_provenance(1, 2, 0, Some("turn-alpha".to_string()));
    let p_beta = install_and_read_provenance(1, 2, 0, Some("turn-beta".to_string()));

    assert_ne!(
        p_alpha, p_beta,
        "regrant at the SAME (target, slot) in a DIFFERENT turn must yield a \
         DISTINCT provenance — else the reused slot is poisoned by the revoked \
         instance's cred_nul"
    );

    // The whole point: the revocation KEYS differ, so the regrant is not born
    // carrying the revoked instance's cred_nul.
    let nul_alpha = dregg_cell::derivation::cred_nul(&p_alpha);
    let nul_beta = dregg_cell::derivation::cred_nul(&p_beta);
    assert_ne!(
        nul_alpha, nul_beta,
        "distinct provenance ⇒ distinct cred_nul: the regrant survives a revoke \
         of the original"
    );
}

/// NON-VACUITY: identical turn (byte-identical agent/nonce/forest/memo) over the
/// same `(target, slot)` ⇒ IDENTICAL provenance. This proves the divergence in
/// `..._collision_free_across_turns` is caused SPECIFICALLY by the turn hash —
/// had the executor kept installing with `NO_TURN_CONTEXT`, that test's two
/// provenances would collide exactly like these two do.
#[test]
fn grant_provenance_deterministic_for_identical_turn() {
    let p_first = install_and_read_provenance(1, 2, 0, Some("same-turn".to_string()));
    let p_second = install_and_read_provenance(1, 2, 0, Some("same-turn".to_string()));
    assert_eq!(
        p_first, p_second,
        "identical turn + identical (target, slot) must be DETERMINISTIC — the \
         only load-bearing differentiator is the turn hash"
    );
}
