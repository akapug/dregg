//! End-to-end teeth for the DEVICE-PAIRING CEREMONY on the REAL executor — the
//! everyday "add a new device" flow (distinct from guardian recovery in
//! `identity_social_recovery_e2e.rs`).
//!
//! Pairing is a KERI *forward rotation* of the identity cell whose WHO is one
//! ALREADY-AUTHORIZED device's Ed25519 attestation (a powerbox designation),
//! not a guardian quorum. This test welds the green parts:
//!
//!   1. `KeyRotationGate` — the KERI pre-rotation StateConstraint
//!      (`starbridge-apps/polis`): the presented set
//!      `key_set_commitment(current ++ [new])` must be the pre-committed
//!      `next_keys_digest` preimage, the install matches, the chain re-commits
//!      forward, cooling passes. Reused verbatim from rotate/recover.
//!   2. `DevicePairingVerifier` -> `Authorization::Custom { PAIRING_VK }`
//!      (`sdk/src/device_pairing.rs`): an existing device that is a member of
//!      the current committed key set signs an attestation over the canonical
//!      custom signing message ‖ the new device's pubkey. The verifier pins the
//!      attestor's exhibited current set to the host-trusted commitment, checks
//!      membership, and checks the Ed25519 signature.
//!   3. The `AgentCipherclerk` of the EXISTING device — the real Ed25519
//!      signing surface (`sign_bytes`) — produces the attestation.
//!
//! WHO and HOW are orthogonal: the existing-device attestation authorizes the
//! cell's `set_state`, while the `KeyRotationGate` independently enforces how a
//! rotation is shaped. Pairing is empowered, never amplified — a forged /
//! non-member / wrong-device attestation is REFUSED by the real executor.

use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::{CellId, field_from_u64};
use dregg_sdk::device_pairing::{
    PAIRING_VK, PairingAttestation, fill_pairing_attestation, pairing_action,
    pairing_signing_message, register_device_pairing_verifier,
};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::identity::{
    CURRENT_KEYS_COMMIT_SLOT, IdentityCharter, LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT,
    create_identity, genesis_effects, key_set_commitment, next_keys_digest,
};
use dregg_sdk::polis::{CouncilCharter, GovernanceCellPlan};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};
use dregg_turn::action::Action;
use dregg_turn::executor::registry_with_real_verifiers;
use dregg_turn::{CallForest, Turn};
use ed25519_dalek::{Signer, SigningKey};

const COOLING: u64 = 50;

fn device(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

fn pubkey(sk: &SigningKey) -> [u8; 32] {
    sk.verifying_key().to_bytes()
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

fn bootstrap(runtime: &mut AgentRuntime, plan: &GovernanceCellPlan) {
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (factory birth) must commit");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn must commit");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn (operator self-grant) must commit");
}

/// Re-permission the identity so `set_state`/`increment_nonce` are authorized
/// by the device-pairing predicate (`Authorization::Custom { PAIRING_VK }`).
/// This is the deos posture for the everyday flow: the who-may-add-a-device
/// decision is an existing-device attestation, while the `KeyRotationGate`
/// still enforces how.
fn install_pairing_authority(runtime: &AgentRuntime, cell: CellId) {
    let mut ledger = runtime.ledger().lock().unwrap();
    let c = ledger.get_mut(&cell).expect("identity cell exists");
    c.permissions = Permissions {
        send: AuthRequired::Impossible,
        receive: AuthRequired::None,
        set_state: AuthRequired::Custom { vk_hash: PAIRING_VK },
        set_permissions: AuthRequired::Impossible,
        set_verification_key: AuthRequired::Impossible,
        increment_nonce: AuthRequired::Custom { vk_hash: PAIRING_VK },
        delegate: AuthRequired::Impossible,
        access: AuthRequired::None,
    };
    c.state.set_balance(1_000_000);
}

fn wire_pairing_verifier(runtime: &mut AgentRuntime) {
    let mut registry = registry_with_real_verifiers();
    register_device_pairing_verifier(&mut registry);
    runtime.set_witnessed_registry(registry);
}

/// A bootstrapped, genesis'd identity at height 1_000 whose CURRENT key set is
/// `current` (a single phone, say) and whose pre-committed `next_keys_digest`
/// is the digest of `current ++ [new_device]` — i.e. the new device was chosen
/// and pre-committed at the previous key event (KERI pre-rotation), and pairing
/// exposes it. `set_state` is PAIRING-authorized.
///
/// Returns `(runtime, cell, current_key_set)`.
fn paired_ready_identity(
    domain: &str,
    current: &[[u8; 32]],
    new_device: [u8; 32],
) -> (AgentRuntime, CellId, Vec<[u8; 32]>) {
    let mut runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    let charter = IdentityCharter {
        council: CouncilCharter::new(
            vec![CellId::from_bytes([0xD1; 32]), CellId::from_bytes([0xD2; 32])],
            2,
        ),
        cooling_period: COOLING,
    };
    let plan = create_identity(&charter, agent_pubkey(&runtime), [0x1D; 32], agent, agent)
        .expect("valid charter");
    bootstrap(&mut runtime, &plan);
    runtime.set_block_height(1_000);

    // Genesis: current set is `current`; the pre-commitment is the digest of
    // the PAIRED set (current with the new device appended) — the device was
    // foreseen at the previous key event.
    let paired = PairingAttestation::paired_key_set(current, new_device);
    runtime
        .execute_on(
            plan.cell_id,
            genesis_effects(
                plan.cell_id,
                &charter,
                key_set_commitment(current),
                next_keys_digest(&key_set_commitment(&paired)),
            ),
        )
        .expect("genesis (icp) must commit");

    install_pairing_authority(&runtime, plan.cell_id);
    (runtime, plan.cell_id, current.to_vec())
}

fn single_action_turn(
    agent_cell: CellId,
    nonce: u64,
    action: Action,
    previous_receipt_hash: Option<[u8; 32]>,
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
        previous_receipt_hash,
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

/// Build the freshly-signed pairing turn: an existing device (`attestor`,
/// already in `current`) attests the new device. `fresh_next` is the forward
/// chain's next link. Returns the turn ready for `execute_turn`.
#[allow(clippy::too_many_arguments)]
fn build_pairing_turn(
    cell: CellId,
    current: &[[u8; 32]],
    new_device: [u8; 32],
    fresh_next: [u8; 32],
    height: u64,
    nonce: u64,
    prev_receipt: Option<[u8; 32]>,
    attestor: &SigningKey,
) -> Turn {
    let mut action = pairing_action(cell, current, new_device, fresh_next, height);
    // The runtime's default local federation id is all-zero.
    let msg = pairing_signing_message(&action, &[0u8; 32], nonce);
    let signed = PairingAttestation::signed_bytes(&msg, &new_device);
    let sig = attestor.sign(&signed).to_bytes();
    let attestation = PairingAttestation {
        attestor_pubkey: pubkey(attestor),
        current_key_set: current.to_vec(),
        new_device_pubkey: new_device,
        signature: sig,
    };
    fill_pairing_attestation(&mut action, &attestation);
    single_action_turn(cell, nonce, action, prev_receipt)
}

// =============================================================================
// THE HEADLINE (true): an existing device pairs a new one through the executor.
// =============================================================================

#[test]
fn existing_device_pairs_new_device() {
    let phone = device(0x01); // the existing, authorized device
    let laptop = device(0x02); // the new device being added
    let current = vec![pubkey(&phone)];
    let (mut runtime, cell, current) =
        paired_ready_identity("pairing-headline", &current, pubkey(&laptop));
    wire_pairing_verifier(&mut runtime);

    // The forward chain's next link (the next set the user pre-commits now).
    let after_next = vec![pubkey(&phone), pubkey(&laptop), [0x03; 32]];
    let fresh_next = next_keys_digest(&key_set_commitment(&after_next));
    let height = runtime.block_height();
    let nonce = cell_nonce(&runtime, cell).max(1);
    let prev = runtime.agent_receipt_head(&cell);

    let turn = build_pairing_turn(
        cell,
        &current,
        pubkey(&laptop),
        fresh_next,
        height,
        nonce,
        prev,
        &phone,
    );
    runtime
        .execute_turn(&turn)
        .expect("an existing-device attestation MUST pair the new device through the executor");

    // PAIRED: the current key set is now the augmented (phone + laptop) set…
    let paired = PairingAttestation::paired_key_set(&current, pubkey(&laptop));
    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        key_set_commitment(&paired),
        "the identity now speaks with the augmented key set (new device admitted)"
    );
    // …the forward chain advanced…
    assert_eq!(
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
        fresh_next,
        "the KEL advanced to the freshly pre-committed next set"
    );
    // …and the height was stamped.
    assert_eq!(
        slot_of(&runtime, cell, LAST_ROTATED_AT_SLOT),
        field_from_u64(height),
        "the pairing rotation anchored the cooling window"
    );
}

// =============================================================================
// THE TOOTH (false): a forged / unauthorized attestation is REFUSED.
// =============================================================================

/// An attacker who holds NO current device key signs a pairing attestation for
/// their own device. Because the attestor key is not a member of the current
/// committed set, the executor refuses — the identity is untouched.
#[test]
fn unauthorized_attestor_refused() {
    let phone = device(0x01);
    let laptop = device(0x02);
    let current = vec![pubkey(&phone)];
    let (mut runtime, cell, current) =
        paired_ready_identity("pairing-unauthorized", &current, pubkey(&laptop));
    wire_pairing_verifier(&mut runtime);

    let after_next = vec![pubkey(&phone), pubkey(&laptop), [0x03; 32]];
    let fresh_next = next_keys_digest(&key_set_commitment(&after_next));
    let height = runtime.block_height();
    let nonce = cell_nonce(&runtime, cell).max(1);

    // The ATTACKER (not in the current set) signs — over the genuine message.
    let attacker = device(0xEE);
    let prev = runtime.agent_receipt_head(&cell);
    let turn = build_pairing_turn(
        cell,
        &current,
        pubkey(&laptop),
        fresh_next,
        height,
        nonce,
        prev,
        &attacker, // <-- not a member of the current key set
    );
    let err = runtime
        .execute_turn(&turn)
        .expect_err("an attestation by a non-member device must be refused");
    assert!(
        matches!(err, dregg_sdk::SdkError::Turn(_)),
        "rejection must be at the auth boundary, got: {err:?}"
    );

    // Untouched: still the original (phone-only) current set.
    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        key_set_commitment(&current),
        "no pairing occurred — the current key set is still the single original device"
    );
}

/// A genuine current device signs over the WRONG new device (or an attacker
/// tampers the blob to claim a different new device than was signed): the
/// signature does not verify over the claimed pubkey, so the executor refuses.
#[test]
fn forged_new_device_refused() {
    let phone = device(0x01);
    let laptop = device(0x02); // the device that was pre-committed
    let current = vec![pubkey(&phone)];
    let (mut runtime, cell, current) =
        paired_ready_identity("pairing-forged-device", &current, pubkey(&laptop));
    wire_pairing_verifier(&mut runtime);

    let after_next = vec![pubkey(&phone), pubkey(&laptop), [0x03; 32]];
    let fresh_next = next_keys_digest(&key_set_commitment(&after_next));
    let height = runtime.block_height();
    let nonce = cell_nonce(&runtime, cell).max(1);

    // Build a genuine action/message for `laptop`, but the phone signs over a
    // DIFFERENT device, and the blob claims `laptop`. The bound new-pubkey in
    // the signed bytes won't match what the verifier reconstructs.
    let mut action = pairing_action(cell, &current, pubkey(&laptop), fresh_next, height);
    let msg = pairing_signing_message(&action, &[0u8; 32], nonce);
    let evil = device(0xDD);
    let signed_over_evil = PairingAttestation::signed_bytes(&msg, &pubkey(&evil));
    let sig = phone.sign(&signed_over_evil).to_bytes(); // signs evil, claims laptop
    let attestation = PairingAttestation {
        attestor_pubkey: pubkey(&phone),
        current_key_set: current.clone(),
        new_device_pubkey: pubkey(&laptop),
        signature: sig,
    };
    fill_pairing_attestation(&mut action, &attestation);
    let prev = runtime.agent_receipt_head(&cell);
    let turn = single_action_turn(cell, nonce, action, prev);

    let err = runtime
        .execute_turn(&turn)
        .expect_err("a signature over a different device than the blob claims must be refused");
    assert!(matches!(err, dregg_sdk::SdkError::Turn(_)));

    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        key_set_commitment(&current),
        "no pairing occurred — the current key set is untouched"
    );
}
