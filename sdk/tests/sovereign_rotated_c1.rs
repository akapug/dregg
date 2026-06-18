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

#![cfg(feature = "prover")]

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
    let commitments_root = [0u8; 32];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(cell.clone());
    let cells_root = dregg_turn::rotation_witness::cells_root(&ctx_ledger);
    let iroot = dregg_turn::rotation_witness::iroot(&[]);
    let v9_ctx = dregg_cell::commitment::V9RotationContext {
        cells_root,
        nullifier_root,
        commitments_root,
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
    assert_ne!(
        &proof_bytes[0..4],
        b"DREG",
        "rotated wire is a postcard BatchProof"
    );
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
    assert_eq!(
        *new_commitment,
        turn.execution_proof_new_commitment.unwrap()
    );
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

// ===========================================================================
// THE RECORD-PIN ANCHOR — setPermissions BEACHHEAD (deployment-soundness close).
//
// The rotated record-pin descriptor (`setPermsVmDescriptor2R24`, 39 PIs) welds the AFTER
// block's `B_RECORD_DIGEST` limb (col 256) to rotated PI 38. PI 38 is a FREE public input the
// prover fills from its honest after-cell's authority digest — so the pin alone is a
// published-value binding, NOT a forcing gate, UNTIL the verifier independently ANCHORS PI 38 to
// `compute_authority_digest_felt(trusted before-cell + effect)` through the SHARED
// `apply_effect_to_cell` weld (`verify_and_commit_proof_rotated`'s record-pin anchor). These two
// tests close that gate:
//   * `rotated_sovereign_set_permissions_proves_and_verifies` — an HONEST setPermissions turn
//     proves → verifies → ACCEPT, and the committed cell's permissions changed. This itself BITES:
//     without the anchor the verifier leaves PI 38 at the placeholder reconstruction (0), which
//     disagrees with the honest proof's nonzero after-digest ⇒ the honest turn would be REJECTED.
//   * `rotated_sovereign_forged_after_permissions_is_rejected` — a proof whose after-block
//     record-digest is for permissions the effect did NOT produce (the kernel effect sets
//     `zkapp()`, the proof's after-block carries `frozen()`), with all OTHER PIs honest, is
//     REJECTED: the anchored PI 38 = digest(zkapp) ≠ the proof's bound col-256 = digest(frozen)
//     ⇒ `verify_vm_descriptor2` UNSAT.
// ===========================================================================
mod record_pin_anchor {
    use dregg_cell::{Cell, CellMode, Ledger, Permissions};
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::rotation_witness as rw;
    use dregg_turn::{ComputronCosts, Effect, Turn, TurnExecutor, TurnResult};

    /// Re-derive the same sovereign-cell registration `setup_sovereign_cell` produces, but expose
    /// the before-`Cell` so the forged test can build witnesses over it. Returns the live
    /// cipherclerk + cell + ledger + the before-cell clone.
    fn setup_with_cell(balance: u64) -> (AgentCipherclerk, dregg_cell::CellId, Ledger, Cell) {
        let cclerk = AgentCipherclerk::new();
        let pub_key = cclerk.public_key().0;
        let token_id = *blake3::hash(b"c1-domain").as_bytes();

        let mut cell = Cell::with_balance(pub_key, token_id, i64::try_from(balance).unwrap());
        cell.mode = CellMode::Sovereign;
        let cell_id = cell.id();

        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(cell.clone());
        let cells_root = rw::cells_root(&ctx_ledger);
        let iroot = rw::iroot(&[]);
        let v9_ctx = dregg_cell::commitment::V9RotationContext {
            cells_root,
            nullifier_root,
            commitments_root,
            iroot,
        };
        let commitment =
            dregg_cell::commitment::compute_canonical_state_commitment_v9(&cell, &v9_ctx);

        let mut cclerk = cclerk;
        cclerk.store_sovereign_state(cell.clone());

        let mut ledger = Ledger::new();
        ledger.register_sovereign_cell(cell_id, commitment).unwrap();
        let _ = ledger.insert_cell(cell.clone());

        (cclerk, cell_id, ledger, cell)
    }

    /// CONTROL + BITE: an HONEST sovereign `SetPermissions` turn proves and verifies, the committed
    /// permissions changed. This passes ONLY because the verifier anchors PI 38 to the trusted
    /// post-cell digest; without the anchor the placeholder PI 38 (0) would reject this honest turn.
    #[test]
    fn rotated_sovereign_set_permissions_proves_and_verifies() {
        let (mut cclerk, cell_id, mut ledger, _before) = setup_with_cell(1000);

        // The before-cell carries the default permissions; the turn locks it down to `zkapp()`.
        let new_perms = Permissions::zkapp();
        assert_ne!(
            new_perms,
            Permissions::default(),
            "the test must actually change permissions"
        );

        let effects = vec![Effect::SetPermissions {
            cell: cell_id,
            new_permissions: new_perms.clone(),
        }];

        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0)
            .expect("rotated sovereign setPermissions turn should prove");

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            // The proof VERIFYING (not rejected) is the proof the anchor accepted: the verifier's
            // anchored PI 38 = digest(before + zkapp) EQUALS the proof's bound after-limb. Without
            // the anchor the verifier would carry PI 38 = placeholder 0 ≠ the honest after-digest
            // and reject — so a Committed result here exercises the anchor's accept side.
            TurnResult::Committed { .. } => {}
            other => panic!("honest setPermissions turn must commit, got {other:?}"),
        }

        // The federation sovereign commitment advanced to the proven post-state (the proof path is
        // commitment-only at the federation; the cell's full state lives with the cipherclerk).
        let committed_commitment = ledger
            .get_sovereign_commitment(&cell_id)
            .expect("sovereign commitment present after commit");
        assert_eq!(
            *committed_commitment,
            turn.execution_proof_new_commitment.unwrap(),
            "the sovereign commitment must advance to the proven post-state"
        );

        // The cipherclerk's LOCAL sovereign state carries the new permissions — the producer
        // applied the effect through the SHARED `apply_effect_to_cell` weld, the SAME projection the
        // verifier anchored PI 38 against (the anti-drift guarantee: both sides moved together).
        let local = cclerk
            .sovereign_state(&cell_id)
            .expect("cipherclerk local sovereign state present");
        assert_eq!(
            local.permissions, new_perms,
            "the cipherclerk's after-state permissions must be the turn's new value"
        );
    }

    /// ANTI-GHOST (the anchor BITES): a proof whose after-block record-digest is for `frozen()`
    /// permissions — which the `zkapp()` effect did NOT produce — is REJECTED. Every OTHER PI is
    /// honest (the kernel effect sets `zkapp()`, so the verifier's reconstructed `vm_effects` /
    /// `effects_hash` MATCH the proof), so the rejection is ISOLATED to the PI-38 anchor:
    /// anchored digest(zkapp) ≠ the proof's bound col-256 digest(frozen) ⇒ UNSAT.
    #[test]
    fn rotated_sovereign_forged_after_permissions_is_rejected() {
        use dregg_sdk::full_turn_proof::prove_effect_vm_rotated_ir2_with_caveat;

        let (_cclerk, cell_id, mut ledger, before_cell) = setup_with_cell(1000);

        // The HONEST effect the turn carries: set permissions to `zkapp()`.
        let honest_perms = Permissions::zkapp();
        let effects = vec![Effect::SetPermissions {
            cell: cell_id,
            new_permissions: honest_perms.clone(),
        }];
        // The HONEST vm-effects (zkapp identity) — what the verifier reconstructs from the kernel
        // effect. The forged proof uses THESE, so PI 0..37 match the verifier by construction.
        let vm_effects = AgentCipherclerk::convert_effects_to_vm(&cell_id, &effects);

        // The FORGED after-cell: the prover claims the cell moved to `frozen()` — a value the
        // `zkapp()` effect did NOT produce. (digest(frozen) ≠ digest(zkapp).)
        let mut forged_after = before_cell.clone();
        forged_after.permissions = Permissions::frozen();
        assert_ne!(
            dregg_cell::compute_authority_digest_felt(&forged_after),
            {
                let mut honest_after = before_cell.clone();
                honest_after.permissions = honest_perms.clone();
                dregg_cell::compute_authority_digest_felt(&honest_after)
            },
            "the forgery must move the authority digest off the honest post-value"
        );

        // Witness context, mirroring the cipherclerk producer's single-cell sovereign turn.
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_hashes: Vec<[u8; 32]> = Vec::new();
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());

        // BEFORE witness = the GENUINE before-cell (so OLD_COMMIT / PI 34 matches the registration).
        let before_w = rw::produce(
            &before_cell,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &receipt_hashes,
        );
        // AFTER witness = the FORGED after-cell (its r23 authority digest = digest(frozen)).
        let after_w = rw::produce(
            &forged_after,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &receipt_hashes,
        );

        let initial_vm_state =
            dregg_circuit::effect_vm::CellState::with_capability_root_and_record_digest(
                u64::try_from(before_cell.state.balance()).unwrap(),
                before_cell.state.nonce() as u32,
                dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
                dregg_cell::compute_authority_digest_felt(&before_cell),
            );

        let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
        let forged_proof = prove_effect_vm_rotated_ir2_with_caveat(
            &initial_vm_state,
            &vm_effects,
            &before_w,
            &after_w,
            &caveat,
            None,
        )
        .expect("the forged proof is internally consistent (it proves a frozen() after-state)");
        let proof_bytes = postcard::to_allocvec(&forged_proof).expect("serialize forged proof");

        // The forged NEW commitment = the v9 felt of the FORGED after-cell (so PI 35 matches the
        // proof's after-block STATE_COMMIT — the forgery is NOT caught by the commitment chain, only
        // by the record-digest anchor).
        let new_commit_felt = dregg_cell::commitment::compute_canonical_state_commitment_v9_felt(
            &forged_after,
            &dregg_cell::commitment::V9RotationContext {
                cells_root: after_w.pre_limbs[0],
                nullifier_root,
                commitments_root,
                iroot: after_w.iroot,
            },
        );
        let new_commitment = dregg_cell::commitment::felt_to_bytes32(new_commit_felt);

        // Assemble the proof-carrying turn (mirroring the cipherclerk producer's turn shape).
        let mut forest = dregg_turn::forest::CallForest::new();
        let action = dregg_sdk::raw::unsigned_action_named(
            cell_id,
            "sovereign_execute_proven",
            effects.clone(),
        );
        forest.add_root(action);
        let turn = Turn {
            agent: cell_id,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: Some(proof_bytes),
            execution_proof_cell: Some(cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Rejected { reason, .. } => {
                let s = format!("{reason:?}");
                assert!(
                    s.contains("ProofVerificationFailed") || s.contains("rotated"),
                    "expected a rotated verify rejection from the PI-38 anchor mismatch, got: {s}"
                );
            }
            other => panic!(
                "ANTI-GHOST: a forged after-permissions proof must be rejected by the record-pin \
                 anchor, got {other:?}"
            ),
        }
    }

    /// CONTROL + BITE (setVK fan-out): an HONEST sovereign `SetVerificationKey` turn proves and
    /// verifies. setVK is the record-digest sibling of setPermissions — `compute_authority_digest_felt`
    /// folds `vk.hash`, so the after r23 residue MOVES, and the verifier anchor's accept side is
    /// exercised (without the anchor the placeholder PI 38 = 0 would reject this honest turn).
    #[test]
    fn rotated_sovereign_set_vk_proves_and_verifies() {
        let (mut cclerk, cell_id, mut ledger, before) = setup_with_cell(1000);
        assert!(before.verification_key.is_none(), "before cell has no VK");

        // A canonical VK whose declared hash == blake3(data) (the executor's apply integrity gate).
        #[allow(deprecated)]
        let vk = dregg_cell::VerificationKey::new(b"c1-setvk-program".to_vec());
        let effects = vec![Effect::SetVerificationKey {
            cell: cell_id,
            new_vk: Some(vk.clone()),
        }];

        let turn = cclerk
            .execute_sovereign_turn_with_proof(&cell_id, effects, 0)
            .expect("rotated sovereign setVK turn should prove");

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            other => panic!("honest setVK turn must commit, got {other:?}"),
        }

        // The cipherclerk's LOCAL sovereign state carries the installed VK (the producer applied the
        // effect through the SHARED `apply_effect_to_cell` weld — the SAME projection the verifier
        // anchored PI 38 against).
        let local = cclerk
            .sovereign_state(&cell_id)
            .expect("cipherclerk local sovereign state present");
        assert_eq!(
            local.verification_key.as_ref().map(|v| v.hash),
            Some(vk.hash),
            "the cipherclerk's after-state VK must be the turn's new value"
        );
    }

    /// ANTI-GHOST (the setVK anchor BITES): a proof whose after-block record-digest is for a
    /// DIFFERENT VK than the kernel effect installs is REJECTED. Every other PI is honest (the
    /// kernel effect installs `vk_honest`, so the reconstructed vm-effects / effects_hash MATCH), so
    /// the rejection is ISOLATED to the PI-38 anchor: anchored digest(vk_honest) ≠ the proof's bound
    /// col-256 digest(vk_forged) ⇒ UNSAT.
    #[test]
    fn rotated_sovereign_forged_after_vk_is_rejected() {
        use dregg_sdk::full_turn_proof::prove_effect_vm_rotated_ir2_with_caveat;

        let (_cclerk, cell_id, mut ledger, before_cell) = setup_with_cell(1000);

        // The HONEST effect the turn carries: install `vk_honest`.
        #[allow(deprecated)]
        let vk_honest = dregg_cell::VerificationKey::new(b"c1-setvk-honest".to_vec());
        let effects = vec![Effect::SetVerificationKey {
            cell: cell_id,
            new_vk: Some(vk_honest.clone()),
        }];
        let vm_effects = AgentCipherclerk::convert_effects_to_vm(&cell_id, &effects);

        // The FORGED after-cell: the prover claims a DIFFERENT VK was installed.
        #[allow(deprecated)]
        let vk_forged = dregg_cell::VerificationKey::new(b"c1-setvk-FORGED".to_vec());
        let mut forged_after = before_cell.clone();
        forged_after.verification_key = Some(vk_forged.clone());
        assert_ne!(
            dregg_cell::compute_authority_digest_felt(&forged_after),
            {
                let mut honest_after = before_cell.clone();
                honest_after.verification_key = Some(vk_honest.clone());
                dregg_cell::compute_authority_digest_felt(&honest_after)
            },
            "the forgery must move the authority digest off the honest post-value"
        );

        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_hashes: Vec<[u8; 32]> = Vec::new();
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());

        let before_w = rw::produce(
            &before_cell,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &receipt_hashes,
        );
        let after_w = rw::produce(
            &forged_after,
            &ctx_ledger,
            &nullifier_root,
            &commitments_root,
            &receipt_hashes,
        );

        let initial_vm_state =
            dregg_circuit::effect_vm::CellState::with_capability_root_and_record_digest(
                u64::try_from(before_cell.state.balance()).unwrap(),
                before_cell.state.nonce() as u32,
                dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
                dregg_cell::compute_authority_digest_felt(&before_cell),
            );

        let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
        let forged_proof = prove_effect_vm_rotated_ir2_with_caveat(
            &initial_vm_state,
            &vm_effects,
            &before_w,
            &after_w,
            &caveat,
            None,
        )
        .expect("the forged proof is internally consistent (it proves a vk_forged after-state)");
        let proof_bytes = postcard::to_allocvec(&forged_proof).expect("serialize forged proof");

        let new_commit_felt = dregg_cell::commitment::compute_canonical_state_commitment_v9_felt(
            &forged_after,
            &dregg_cell::commitment::V9RotationContext {
                cells_root: after_w.pre_limbs[0],
                nullifier_root,
                commitments_root,
                iroot: after_w.iroot,
            },
        );
        let new_commitment = dregg_cell::commitment::felt_to_bytes32(new_commit_felt);

        let mut forest = dregg_turn::forest::CallForest::new();
        let action = dregg_sdk::raw::unsigned_action_named(
            cell_id,
            "sovereign_execute_proven",
            effects.clone(),
        );
        forest.add_root(action);
        let turn = Turn {
            agent: cell_id,
            nonce: 0,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: Some(proof_bytes),
            execution_proof_cell: Some(cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Rejected { reason, .. } => {
                let s = format!("{reason:?}");
                assert!(
                    s.contains("ProofVerificationFailed") || s.contains("rotated"),
                    "expected a rotated verify rejection from the PI-38 setVK anchor mismatch, got: {s}"
                );
            }
            other => panic!(
                "ANTI-GHOST: a forged after-vk proof must be rejected by the record-pin anchor, \
                 got {other:?}"
            ),
        }
    }
}

// ===========================================================================
// WALL A — the rotated `prove_full_turn` / `verify_full_turn` round-trip carries
// ZERO v1 dependency. These drive `prove_full_turn` DIRECTLY with a rotation
// witness (not the executor-mint path) so the rotated leg's vk_hash (A.1) and the
// rotated-PI conservation read (A.2) are exercised, and so the v1 trace is NOT
// generated on the rotated path (A.3). The witness is built mirroring the
// cipherclerk's validated reference shape (a single outgoing sovereign transfer,
// the transfer caveat manifest).
// ===========================================================================
mod wall_a {
    use dregg_cell::commitment::{V9RotationContext, compute_canonical_state_commitment_v9_felt};
    use dregg_cell::{Cell, CellMode, Ledger};
    use dregg_circuit::effect_vm::{self, CellState};
    use dregg_sdk::full_turn_proof::{
        ConservationWitness, FullTurnWitness, RotationTurnWitness, prove_full_turn,
        verify_full_turn,
    };
    use dregg_turn::rotation_witness as rw;

    /// Build a valid rotated `FullTurnWitness` for a single outgoing transfer of `amount`
    /// from a sovereign cell of `balance`. Returns `(witness, old_commit_felt,
    /// new_commit_felt)` — the latter two are the rotated PI 34/35 the verifier expects.
    /// Mirrors `AgentCipherclerk::prove_sovereign_turn_rotated` (the C1 reference).
    fn build_rotated_transfer_witness(
        balance: u64,
        amount: u64,
    ) -> (
        FullTurnWitness,
        dregg_circuit::field::BabyBear,
        dregg_circuit::field::BabyBear,
    ) {
        let token_id = *blake3::hash(b"wallA-domain").as_bytes();
        let mut before_cell = Cell::with_balance([7u8; 32], token_id, balance as i64);
        before_cell.mode = CellMode::Sovereign;

        // after-state: an outgoing transfer debits the balance.
        let mut after_cell = before_cell.clone();
        after_cell
            .state
            .set_balance(after_cell.state.balance().saturating_sub(amount as i64));

        // circuit pre-state (cap-root-seeded), identical to the v1 path.
        let initial_vm_state = CellState::with_capability_root(
            before_cell.state.balance() as u64,
            before_cell.state.nonce() as u32,
            dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        );

        let vm_effects = vec![effect_vm::Effect::Transfer {
            amount,
            direction: 1, // outgoing
        }];

        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_hashes: Vec<[u8; 32]> = Vec::new();
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(before_cell.clone());

        let before_w = rw::produce(&before_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);
        let after_w = rw::produce(&after_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);

        // The cell-side v9 commitment of the before-state == rotated PI 34; the after-state
        // v9 == rotated PI 35 (the cross-checks the cipherclerk asserts by construction).
        let old_commit = compute_canonical_state_commitment_v9_felt(
            &before_cell,
            &V9RotationContext {
                cells_root: before_w.pre_limbs[0],
                nullifier_root,
                commitments_root,
                iroot: before_w.iroot,
            },
        );
        let new_commit = compute_canonical_state_commitment_v9_felt(
            &after_cell,
            &V9RotationContext {
                cells_root: after_w.pre_limbs[0],
                nullifier_root,
                commitments_root,
                iroot: after_w.iroot,
            },
        );

        let rotation = RotationTurnWitness::for_effects(before_w, after_w, &vm_effects);
        let witness = FullTurnWitness {
            initial_cell_state: initial_vm_state,
            effects: vm_effects,
            authorization: None,
            membership: None,
            conservation: None,
            non_revocation: None,
            cap_membership: None,
            turn_hash: *blake3::hash(b"wallA-turn").as_bytes(),
            rotation: Some(rotation),
        };
        (witness, old_commit, new_commit)
    }

    /// CONTROL: a rotated full-turn proves through `prove_full_turn` and `verify_full_turn`
    /// ACCEPTS it — the rotated leg's vk_hash is the rotated cohort descriptor's fingerprint
    /// (A.1) and is re-checked at verify; the v1 effect-vm trace was never generated (A.3).
    #[test]
    fn rotated_full_turn_round_trips() {
        let (witness, _old, _new) = build_rotated_transfer_witness(1000, 100);
        let proof = prove_full_turn(&witness).expect("rotated full-turn should prove");

        // The attached leg is the rotated one (not the v1 "effect-vm").
        let labels: Vec<&str> = proof
            .composed
            .sub_proofs
            .iter()
            .map(|sp| sp.label.as_str())
            .collect();
        assert!(
            labels.contains(&"effect-vm-rotated"),
            "expected a rotated effect-vm leg, got {labels:?}"
        );
        assert!(
            !labels.contains(&"effect-vm"),
            "the v1 effect-vm leg must be ABSENT on the rotated path, got {labels:?}"
        );

        // The verifier cross-binds OLD_COMMIT(0)/NEW_COMMIT(4) of the rotated leg's PI; those
        // carriers are the trace's OWN before/after state-commit (NOT a separately-recomputed
        // v9), so the expected commits ARE the proof's bound PI at those offsets.
        let rot_pi = &proof
            .composed
            .sub_proofs
            .iter()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("rotated leg present")
            .sub_public_inputs;
        let old_commit = rot_pi[dregg_circuit::effect_vm::pi::OLD_COMMIT];
        let new_commit = rot_pi[dregg_circuit::effect_vm::pi::NEW_COMMIT];

        verify_full_turn(&proof, old_commit, new_commit).expect("rotated full-turn should verify");
    }

    /// ANTI-GHOST (A.1): tampering the rotated leg's vk_hash is REJECTED. The verifier
    /// re-derives the expected fingerprint from the uniquely-accepting cohort descriptor and
    /// the mismatch fails — proving vk_hash is load-bearing on the rotated leg (not cosmetic).
    #[test]
    fn rotated_full_turn_tampered_vk_hash_rejected() {
        let (witness, old_commit, new_commit) = build_rotated_transfer_witness(1000, 100);
        let mut proof = prove_full_turn(&witness).expect("rotated full-turn should prove");

        let leg = proof
            .composed
            .sub_proofs
            .iter_mut()
            .find(|sp| sp.label == "effect-vm-rotated")
            .expect("rotated leg present");
        leg.vk_hash[0] ^= 0xFF; // flip a byte of the descriptor fingerprint

        let err = verify_full_turn(&proof, old_commit, new_commit)
            .expect_err("ANTI-GHOST: a tampered rotated vk_hash must be rejected");
        let s = format!("{err:?}");
        assert!(
            s.contains("vk_hash") || s.contains("fingerprint"),
            "expected a vk_hash-mismatch rejection, got: {s}"
        );
    }

    /// ANTI-GHOST (A.2): with a conservation witness present, a FORGED expected_net_delta is
    /// rejected — and the check reads net_delta from the ROTATED PI (the v1 trace does not
    /// exist on this path), so this also proves the conservation leg has no v1 dependency.
    #[test]
    fn rotated_full_turn_forged_net_delta_rejected() {
        let (mut witness, _old, _new) = build_rotated_transfer_witness(1000, 100);
        // A wrong expected net_delta (the honest turn's is the outgoing-100 encoding).
        witness.conservation = Some(ConservationWitness {
            expected_net_delta: 999_999,
        });
        let err = prove_full_turn(&witness)
            .expect_err("ANTI-GHOST: a forged conservation net_delta must be rejected");
        let s = format!("{err:?}");
        assert!(
            s.contains("conservation"),
            "expected a conservation mismatch (read from the rotated PI), got: {s}"
        );
    }
}
