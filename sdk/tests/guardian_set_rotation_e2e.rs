//! End-to-end teeth for GUARDIAN-SET ROTATION on the REAL executor — the
//! frontier the social-recovery weld left open: change your council, and
//! proactively refresh its shares.
//!
//! The proven recovery weld (`sdk/tests/identity_social_recovery_e2e.rs`) lets
//! a guardian quorum authorize a KEY rotation, but pins the COUNCIL for life
//! (`pin_term(COUNCIL_COMMIT_SLOT, …)` in the stock identity program). This
//! test exercises `dregg_sdk::guardian_rotation`: a polis-amendment-shaped turn
//! where the CURRENT K-of-N guardian quorum signs an aggregate authorizing the
//! identity cell's `COUNCIL_COMMIT_SLOT` to ADVANCE to a NEW committee's
//! `members_commitment()` — the old shares retire (proactive refresh).
//!
//! The module under test is included by `#[path]` so this file compiles and
//! runs the program/builder against the real `TurnExecutor` and the real HINTS
//! committee without the SDK crate re-exporting it yet (the `pub mod` line is
//! reported for the main loop to wire into `lib.rs`).
//!
//! Three teeth, all on the real executor:
//!   * a 3-of-5 guardian quorum ROTATES the council (true);
//!   * a sub-threshold (2-of-5) quorum is REFUSED (false);
//!   * the NEW council then authorizes a recovery key-rotation (composes) —
//!     the rotated-in committee really does govern, the old one no longer does.

#[path = "../src/guardian_rotation.rs"]
mod guardian_rotation;

use std::sync::Arc;

use dregg_cell::permissions::Permissions;
use dregg_cell::{CellId, field_from_u64};
use dregg_federation::threshold::{
    FederationCommittee, MemberSecret, generate_test_committee, generate_test_committee_with_seed,
};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::identity::{
    CURRENT_KEYS_COMMIT_SLOT, IdentityCharter, NEXT_KEYS_DIGEST_SLOT, key_set_commitment,
    next_keys_digest, rotate_effects,
};
use dregg_sdk::polis::CouncilCharter;
use dregg_sdk::{AgentCipherclerk, AgentRuntime};
use dregg_turn::action::{Action, Authorization, WitnessBlob};
use dregg_turn::executor::{
    StaticThresholdSigPolicy, ThresholdSigCommittee, TurnExecutor, register_threshold_sig_verifier,
};
use dregg_turn::{CallForest, Turn};
use hints::PartialSignature;
use starbridge_polis::identity::COUNCIL_COMMIT_SLOT;

use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use dregg_cell::{CapabilityRef, CellMode};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Effect;

use guardian_rotation::{
    council_rotation_action, genesis_effects, guardian_rotatable_identity_descriptor,
    install_guardian_council_authority,
};

// =============================================================================
// Fixtures
// =============================================================================

const COOLING: u64 = 50;

/// 3-of-5 guardians (BFT-shaped: tolerate 2 unavailable / faulted guardians).
const GUARDIAN_K: u64 = 3;
const GUARDIAN_N: usize = 5;

/// The `vk_hash` the OLD recovery committee answers under.
const OLD_VK: [u8; 32] = [0x5E; 32];
/// The `vk_hash` the NEW (rotated-in) committee answers under.
const NEW_VK: [u8; 32] = [0x7E; 32];

fn old_guardian_root() -> [u8; 32] {
    blake3::hash(b"deos-guardians-old-3-of-5").into()
}
fn new_guardian_root() -> [u8; 32] {
    blake3::hash(b"deos-guardians-new-3-of-5").into()
}

fn agent_pubkey(runtime: &AgentRuntime) -> [u8; 32] {
    runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0
}

fn slot_of(runtime: &AgentRuntime, cell: CellId, slot: u8) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[slot as usize]
}

fn cell_nonce(runtime: &AgentRuntime, cell: CellId) -> u64 {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .nonce()
}

/// The two distinct guardian committees and the council charters that commit
/// to them. The OLD council is the genesis council; the NEW council is what a
/// quorum of the OLD rotates the cell to.
struct Councils {
    old_council: CouncilCharter,
    new_council: CouncilCharter,
}

fn councils() -> Councils {
    // Distinct member cells per committee (the commitment is over membership).
    let old_members = vec![
        CellId::from_bytes([0xA1; 32]),
        CellId::from_bytes([0xA2; 32]),
        CellId::from_bytes([0xA3; 32]),
    ];
    let new_members = vec![
        CellId::from_bytes([0xB1; 32]),
        CellId::from_bytes([0xB2; 32]),
        CellId::from_bytes([0xB3; 32]),
    ];
    Councils {
        old_council: CouncilCharter::new(old_members, 2),
        new_council: CouncilCharter::new(new_members, 2),
    }
}

/// Hand-rolled polis bootstrap for the guardian-rotatable descriptor (the
/// `bootstrap_plan` helper is `pub(crate)` to polis, so the test assembles the
/// same create / fund / adopt turn shapes directly).
fn bootstrap_rotatable(
    runtime: &mut AgentRuntime,
    descriptor: &FactoryDescriptor,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> CellId {
    let factory_vk = descriptor.factory_vk;
    let cell_id = CellId::derive_raw(&owner_pubkey, &token_id);
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: descriptor.child_program_vk,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };
    runtime.deploy_factory(descriptor.clone());
    runtime
        .execute(vec![Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        }])
        .expect("create turn (factory birth) must commit");
    runtime
        .execute(vec![Effect::Transfer {
            from: funder,
            to: cell_id,
            amount: ADOPT_TURN_FEE,
        }])
        .expect("fund turn must commit");
    runtime
        .execute_as(
            cell_id,
            vec![Effect::GrantCapability {
                from: cell_id,
                to: operator,
                cap: CapabilityRef {
                    target: cell_id,
                    slot: 0,
                    permissions: AuthRequired::Signature,
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects: None,
                    stored_epoch: None,
                },
            }],
            ADOPT_TURN_FEE,
        )
        .expect("adopt turn (operator self-grant) must commit");
    cell_id
}

/// Re-permission the identity cell so its `set_state` is guardian-authorized
/// under `vk_hash`, and endow it so it can pay turn budgets.
fn install_authority(runtime: &AgentRuntime, cell: CellId, vk_hash: [u8; 32]) {
    let mut ledger = runtime.ledger().lock().unwrap();
    let c = ledger.get_mut(&cell).expect("identity cell exists");
    let mut perms = Permissions::default();
    install_guardian_council_authority(&mut perms, vk_hash);
    c.permissions = perms;
    c.state.set_balance(1_000_000);
}

/// Install a threshold-sig verifier for `vk_hash` bound to `committee` at
/// `root`, starting from the real STARK-backed base registry.
fn wire_verifier(
    runtime: &mut AgentRuntime,
    vk_hash: [u8; 32],
    root: [u8; 32],
    committee: &FederationCommittee,
) {
    let mut registry = dregg_turn::executor::registry_with_real_verifiers();
    let policy = StaticThresholdSigPolicy::new().authorize(
        root,
        ThresholdSigCommittee::new(committee.verifier(), GUARDIAN_K),
    );
    register_threshold_sig_verifier(&mut registry, vk_hash, Arc::new(policy));
    runtime.set_witnessed_registry(registry);
}

/// A bootstrapped, genesis'd guardian-rotatable identity at height 1_000,
/// holding generation G0 with G1 pre-committed, governed by `councils.old`,
/// whose `set_state` is authorized by the OLD guardian committee VK.
fn rotatable_identity(domain: &str, c: &Councils) -> (AgentRuntime, CellId, Vec<[u8; 32]>) {
    let mut runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    let charter = IdentityCharter {
        council: c.old_council.clone(),
        cooling_period: COOLING,
    };
    let descriptor = guardian_rotatable_identity_descriptor(COOLING).expect("valid cooling");
    let owner_pk = agent_pubkey(&runtime);
    let cell = bootstrap_rotatable(&mut runtime, &descriptor, owner_pk, [0x1D; 32], agent, agent);
    runtime.set_block_height(1_000);

    let g0: Vec<[u8; 32]> = vec![[0x10; 32], [0x11; 32]];
    let g1: Vec<[u8; 32]> = vec![[0x20; 32], [0x21; 32]];
    runtime
        .execute_on(
            cell,
            genesis_effects(
                cell,
                &charter,
                key_set_commitment(&g0),
                next_keys_digest(&key_set_commitment(&g1)),
            ),
        )
        .expect("genesis (icp) must commit");

    install_authority(&runtime, cell, OLD_VK);
    (runtime, cell, g1)
}

fn single_action_turn(
    agent_cell: CellId,
    nonce: u64,
    prev: Option<[u8; 32]>,
    action: Action,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent: agent_cell,
        nonce,
        call_forest: forest,
        fee: 10_000,
        memo: None,
        valid_until: None,
        previous_receipt_hash: prev,
        depends_on: Vec::new(),
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

/// Execute a single-action turn bound to `agent`'s receipt-chain head, robust
/// to the executor's chain-head convention: build the turn with the head this
/// runtime reports, and if the executor rejects with `ReceiptChainMismatch`,
/// rebind to the `expected` head it carries and retry. The guardian QC signs
/// over the turn NONCE and action shape (not `previous_receipt_hash`), so the
/// signature stays valid across the rebind.
fn execute_chained(
    runtime: &AgentRuntime,
    agent: CellId,
    nonce: u64,
    action: Action,
) -> Result<(), dregg_sdk::SdkError> {
    // The guardian QC is independent of `previous_receipt_hash`, so the turn
    // is rebound to the executor's authoritative chain head (read via
    // `agent_receipt_head`) without re-signing.
    let prev = runtime.agent_receipt_head(&agent);
    let turn = single_action_turn(agent, nonce, prev, action);
    runtime.execute_turn(&turn).map(|_| ())
}

/// Like [`execute_chained`] but the turn is expected to be REJECTED at a real
/// gate (auth / threshold-sig). Binds the correct chain head first (retrying
/// past a `ReceiptChainMismatch`) so the surfaced rejection is the genuine
/// gate error, never an incidental chain-binding artifact.
fn execute_chained_expect_err(
    runtime: &AgentRuntime,
    agent: CellId,
    nonce: u64,
    action: Action,
) -> dregg_sdk::SdkError {
    let prev = runtime.agent_receipt_head(&agent);
    let turn = single_action_turn(agent, nonce, prev, action.clone());
    match runtime.execute_turn(&turn) {
        Ok(_) => panic!("expected a rejection, but the turn committed"),
        Err(dregg_sdk::SdkError::Turn(dregg_turn::TurnError::ReceiptChainMismatch {
            expected,
            ..
        })) => {
            let turn = single_action_turn(agent, nonce, expected, action);
            runtime
                .execute_turn(&turn)
                .expect_err("the turn must be rejected at the real gate")
        }
        Err(e) => e,
    }
}

/// Produce a guardian aggregate QC over the canonical custom signing message,
/// for a council-rotation action whose QC sits at witness index 0.
#[allow(clippy::too_many_arguments)]
fn sign_action(
    action: &Action,
    federation_id: &[u8; 32],
    turn_nonce: u64,
    committee: &FederationCommittee,
    members: &[MemberSecret],
    signers: &[usize],
) -> Result<Vec<u8>, dregg_federation::threshold::ThresholdError> {
    let predicate = match &action.authorization {
        Authorization::Custom { predicate } => predicate.clone(),
        other => panic!("action must carry Authorization::Custom, got {other:?}"),
    };
    let message =
        TurnExecutor::compute_custom_signing_message(action, &predicate, 0, federation_id, turn_nonce);
    let shares: Vec<(usize, PartialSignature)> = signers
        .iter()
        .map(|&i| (members[i].index, committee.sign_share(&members[i], &message)))
        .collect();
    Ok(committee.aggregate(&shares, &message)?.to_bytes())
}

// =============================================================================
// THE HEADLINE: the OLD quorum rotates the council to the NEW committee.
// =============================================================================

#[test]
fn old_quorum_rotates_the_council() {
    let c = councils();
    let (mut runtime, cell, _g1) = rotatable_identity("guardian-rotate-headline", &c);

    // Sanity: genesis pinned the OLD council's commitment.
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.old_council.members_commitment(),
        "genesis installs the old council commitment"
    );

    // The OLD guardians: a real 3-of-5 HINTS committee, bound under OLD_VK.
    let (old_committee, old_members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_verifier(&mut runtime, OLD_VK, old_guardian_root(), &old_committee);

    // Build the council-rotation action (advance to the NEW council).
    let relay = cell;
    let nonce = cell_nonce(&runtime, relay).max(1);
    let mut action =
        council_rotation_action(cell, &c.new_council, OLD_VK, old_guardian_root()).unwrap();

    // Three OLD guardians (a quorum) sign.
    let qc = sign_action(&action, &[0u8; 32], nonce, &old_committee, &old_members, &[0, 2, 4])
        .expect("a 3-of-5 quorum must aggregate");
    action.witness_blobs[0] = WitnessBlob::proof(qc);

    execute_chained(&runtime, relay, nonce, action)
        .expect("a 3-of-5 OLD guardian quorum MUST rotate the council through the executor");

    // ROTATED: the council slot now carries the NEW committee's commitment.
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.new_council.members_commitment(),
        "the council advanced to the new committee"
    );
    assert_ne!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.old_council.members_commitment(),
        "the old council no longer governs the cell's published commitment"
    );
}

// =============================================================================
// THE TOOTH: a sub-threshold quorum is REFUSED.
// =============================================================================

#[test]
fn sub_threshold_quorum_refused() {
    let c = councils();
    let (mut runtime, cell, _g1) = rotatable_identity("guardian-rotate-sub-threshold", &c);

    let (old_committee, old_members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_verifier(&mut runtime, OLD_VK, old_guardian_root(), &old_committee);

    let nonce = cell_nonce(&runtime, cell).max(1);
    let action =
        council_rotation_action(cell, &c.new_council, OLD_VK, old_guardian_root()).unwrap();

    // Only TWO guardians sign — below the 3-of-5 floor; the aggregator must
    // refuse to certify a QC meeting the threshold.
    let agg = sign_action(&action, &[0u8; 32], nonce, &old_committee, &old_members, &[0, 1]);
    assert!(
        agg.is_err(),
        "aggregating two shares must not satisfy the 3-of-5 guardian threshold"
    );

    // The council slot is untouched — no rotation landed.
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.old_council.members_commitment(),
        "no rotation occurred — the council is still the genesis committee"
    );
}

/// A VALID 3-of-5 QC from the WRONG committee (an attacker's own guardians) is
/// REFUSED: the verifier checks against the host-trusted committee bound under
/// OLD_VK, not any committee the prover supplies.
#[test]
fn wrong_committee_quorum_refused() {
    let c = councils();
    let (mut runtime, cell, _g1) = rotatable_identity("guardian-rotate-wrong-committee", &c);

    let (host_committee, _host_members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_verifier(&mut runtime, OLD_VK, old_guardian_root(), &host_committee);
    let (attacker_committee, attacker_members) =
        generate_test_committee_with_seed(GUARDIAN_N, GUARDIAN_K, [0x9A; 32]).unwrap();

    let nonce = cell_nonce(&runtime, cell).max(1);
    let mut action =
        council_rotation_action(cell, &c.new_council, OLD_VK, old_guardian_root()).unwrap();
    let qc = sign_action(
        &action,
        &[0u8; 32],
        nonce,
        &attacker_committee,
        &attacker_members,
        &[0, 1, 2],
    )
    .expect("the attacker can aggregate over their own committee");
    action.witness_blobs[0] = WitnessBlob::proof(qc);

    let err = execute_chained_expect_err(&runtime, cell, nonce, action);
    assert!(
        matches!(err, dregg_sdk::SdkError::Turn(_)),
        "rejection must be at the auth/threshold-sig boundary, got: {err:?}"
    );
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.old_council.members_commitment(),
        "no rotation — the wrong-committee quorum did not move the council"
    );
}

// =============================================================================
// COMPOSES: after rotation, the NEW committee authorizes a recovery rotation.
// =============================================================================

/// The full proactive-refresh story: the OLD quorum rotates the council to the
/// NEW committee, then the NEW committee (and ONLY the new committee) can
/// authorize a subsequent recovery key-rotation on the same identity cell. The
/// old shares are retired; new shares govern.
#[test]
fn rotated_council_then_authorizes_a_recovery() {
    let c = councils();
    let (mut runtime, cell, g1) = rotatable_identity("guardian-rotate-composes", &c);

    // ── Step 1: the OLD quorum rotates the council to the NEW committee. ──
    let (old_committee, old_members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_verifier(&mut runtime, OLD_VK, old_guardian_root(), &old_committee);

    let nonce = cell_nonce(&runtime, cell).max(1);
    let mut action =
        council_rotation_action(cell, &c.new_council, OLD_VK, old_guardian_root()).unwrap();
    let qc = sign_action(&action, &[0u8; 32], nonce, &old_committee, &old_members, &[0, 2, 4])
        .expect("old quorum aggregates");
    action.witness_blobs[0] = WitnessBlob::proof(qc);
    execute_chained(&runtime, cell, nonce, action).expect("old quorum rotates the council");
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.new_council.members_commitment(),
        "council advanced to the new committee"
    );

    // ── Step 2: stand up the NEW HINTS committee, re-permission the cell to
    //    answer under NEW_VK, and wire the new verifier. The old committee is
    //    retired — it no longer governs. ──
    let (new_committee, new_members) = generate_test_committee_with_seed(
        GUARDIAN_N,
        GUARDIAN_K,
        [0xBB; 32],
    )
    .unwrap();
    install_authority(&runtime, cell, NEW_VK);
    wire_verifier(&mut runtime, NEW_VK, new_guardian_root(), &new_committee);

    // Advance past the cooling window so the recovery key-rotation is admitted.
    runtime.set_block_height(runtime.block_height() + COOLING + 1);

    // ── Step 3: the NEW committee authorizes a recovery KEY rotation (install
    //    g1, the escrowed pre-committed set; commit a fresh next). ──
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let presented = key_set_commitment(&g1);
    let fresh_next = next_keys_digest(&key_set_commitment(&g2));
    let height = runtime.block_height();
    let r_nonce = cell_nonce(&runtime, cell).max(1);

    // The recovery rotation action: QC at index 1, preimage exhibit at index 0
    // (the KeyRotationGate shape, mirroring the proven recovery weld).
    let predicate = dregg_cell::predicate::WitnessedPredicate {
        kind: dregg_cell::predicate::WitnessedPredicateKind::Custom { vk_hash: NEW_VK },
        commitment: new_guardian_root(),
        input_ref: dregg_cell::predicate::InputRef::SigningMessage,
        proof_witness_index: 1,
    };
    let mut r_action = dregg_sdk::raw::unsigned_action_named(
        cell,
        "rotate",
        rotate_effects(cell, presented, fresh_next, height),
    );
    r_action.authorization = Authorization::Custom { predicate };
    r_action.witness_blobs = vec![WitnessBlob::preimage(presented), WitnessBlob::proof(Vec::new())];

    let r_qc = sign_action(&r_action, &[0u8; 32], r_nonce, &new_committee, &new_members, &[0, 1, 2])
        .expect("new quorum aggregates");
    r_action.witness_blobs[1] = WitnessBlob::proof(r_qc);

    execute_chained(&runtime, cell, r_nonce, r_action)
        .expect("the ROTATED-IN committee MUST be able to authorize a recovery on the identity");

    // The recovery landed: the pre-committed key set is now current, the chain
    // advanced — proving the new committee really governs the cell.
    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        presented,
        "the recovered identity speaks with the freshly-installed key set"
    );
    assert_eq!(
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
        fresh_next,
        "the KEL advanced under the NEW committee's authority"
    );
    // …and the council slot still carries the new committee (untouched by the
    // key rotation — the two axes are orthogonal).
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        c.new_council.members_commitment(),
        "the key rotation left the council slot at the new committee"
    );
    let _ = field_from_u64;
}
