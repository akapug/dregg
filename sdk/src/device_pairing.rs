//! # Device pairing — the powerbox "add a new device" ceremony.
//!
//! This is the *everyday* identity flow, distinct from guardian recovery
//! (`tests/identity_social_recovery_e2e.rs`). Recovery answers "I lost every
//! device" with an M-of-N guardian **quorum**; pairing answers "I have my
//! phone and want to add my laptop" with a single **already-authorized
//! device** designating the new one — a powerbox grant, not a council vote.
//!
//! ## The shape
//!
//! Pairing is a KERI *forward rotation* of the identity cell (the SAME
//! [`KeyRotationGate`](starbridge_polis) the rotate/recover paths drive), but
//! the WHO is one existing device's Ed25519 attestation rather than a HINTS
//! threshold QC:
//!
//! * **WHO (this module).** An existing device whose public key is a member of
//!   the identity's CURRENT committed key set signs a [`PairingAttestation`]
//!   over the canonical custom signing message *concatenated with the new
//!   device's public key*. The executor discharges this through a
//!   [`DevicePairingVerifier`] registered under [`PAIRING_VK`] — an
//!   `Authorization::Custom` predicate whose host-trusted `commitment` is the
//!   current key-set commitment. The verifier recomputes that commitment from
//!   the attestor's exhibited key set, checks the attestor is a member, and
//!   checks the Ed25519 signature. A signer who is NOT in the current set, a
//!   signature over a different new device, or an attestation whose exhibited
//!   set does not reproduce the host-pinned commitment all fail closed.
//!
//! * **HOW (reused verbatim).** The pairing turn presents
//!   `key_set_commitment(current ++ [new_device])` as the new current set, and
//!   that commitment must be the preimage of the cell's pre-committed
//!   `next_keys_digest` — so the new device had to be chosen and pre-committed
//!   at the *previous* key event (KERI pre-rotation discipline; a thief who
//!   compromises a current device still cannot smuggle in an unforeseen key).
//!   The `KeyRotationGate` independently enforces install + forward-recommit +
//!   cooling, exactly as for rotate and recover.
//!
//! Empowered, never amplified: the attestation only lets an *already-authorized*
//! device admit an *already-pre-committed* new key. It can neither name a key the
//! KEL did not foresee (the gate refuses) nor act from a key outside the current
//! set (the verifier refuses).
//!
//! ## Proof-blob wire (`PairingAttestation`)
//!
//! The `Authorization::Custom` proof blob at the predicate's
//! `proof_witness_index` carries a [`PairingAttestation`]: the attestor's
//! public key, the ordered current key set (the membership opening for the
//! host-pinned `commitment`), the new device's public key, and the 64-byte
//! Ed25519 signature. [`PairingAttestation::encode`] / [`decode`] are a fixed
//! length-prefixed framing — no serde, stable across builds.
//!
//! [`KeyRotationGate`]: starbridge_polis
//! [`decode`]: PairingAttestation::decode

use ed25519_dalek::{Signature as DalekSignature, Verifier, VerifyingKey};

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::state::FieldElement;
use dregg_cell::{CellId, predicate::InputRef};
use dregg_turn::action::{Action, Authorization, WitnessBlob};

use crate::identity::{key_set_commitment, rotate_effects};

use std::sync::Arc;

/// The `vk_hash` the device-pairing predicate answers under. The identity
/// cell's rotation authority demands `Authorization::Custom { vk_hash:
/// PAIRING_VK }`, and the [`DevicePairingVerifier`] registers under the same
/// hash. Distinct bytes from the social-recovery `RECOVERY_VK` so the registry
/// dispatch never confuses the two ceremonies.
pub const PAIRING_VK: [u8; 32] = [0xDE; 32]; // "DEvice pairing".

/// Domain tag mixed into the bytes the attestor signs, so a device-pairing
/// signature can never be replayed as a plain action signature (`dregg-action-
/// sig-v2`) or a custom QC message. The attestor signs
/// `PAIRING_SIG_DOMAIN ‖ signing_message ‖ new_device_pubkey`.
pub const PAIRING_SIG_DOMAIN: &[u8] = b"dregg-device-pairing-attestation-v1:";

// =============================================================================
// The attestation proof blob
// =============================================================================

/// An existing authorized device's attestation that a new device may join the
/// identity's key set. Rides the `Authorization::Custom` proof blob; the
/// executor hands its bytes to [`DevicePairingVerifier::verify`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingAttestation {
    /// The attesting (existing) device's Ed25519 public key. MUST be a member
    /// of `current_key_set`.
    pub attestor_pubkey: [u8; 32],
    /// The identity's CURRENT ordered key set — the membership opening for the
    /// host-pinned predicate `commitment` (`key_set_commitment(current)`). The
    /// verifier recomputes the commitment from this and pins it to the
    /// host-trusted value, so the prover cannot supply a set of their choosing.
    pub current_key_set: Vec<[u8; 32]>,
    /// The new device's Ed25519 public key being admitted. Bound into the
    /// signed message so the attestation authorizes THIS device, not any other.
    pub new_device_pubkey: [u8; 32],
    /// Ed25519 signature by `attestor_pubkey` over
    /// `PAIRING_SIG_DOMAIN ‖ signing_message ‖ new_device_pubkey`.
    pub signature: [u8; 64],
}

impl PairingAttestation {
    /// The augmented key set a successful pairing installs: the current set
    /// with the new device appended (position-committed; appending keeps every
    /// existing opening stable). This is what the rotation presents as the new
    /// current set, and whose commitment must equal the pre-committed
    /// `next_keys_digest` preimage.
    pub fn paired_key_set(current_key_set: &[[u8; 32]], new_device_pubkey: [u8; 32]) -> Vec<[u8; 32]> {
        let mut keys = Vec::with_capacity(current_key_set.len() + 1);
        keys.extend_from_slice(current_key_set);
        keys.push(new_device_pubkey);
        keys
    }

    /// The bytes the attestor signs: domain ‖ canonical custom signing message
    /// ‖ new device pubkey. Binding the signing message pins federation_id,
    /// nonce, position, and the whole action body (target/method/effects);
    /// binding the new pubkey pins WHICH device is admitted.
    pub fn signed_bytes(signing_message: &[u8], new_device_pubkey: &[u8; 32]) -> Vec<u8> {
        let mut m = Vec::with_capacity(PAIRING_SIG_DOMAIN.len() + signing_message.len() + 32);
        m.extend_from_slice(PAIRING_SIG_DOMAIN);
        m.extend_from_slice(signing_message);
        m.extend_from_slice(new_device_pubkey);
        m
    }

    /// Fixed length-prefixed framing (no serde): attestor(32) ‖ new(32) ‖
    /// sig(64) ‖ n(u32-le) ‖ n×key(32). Stable across builds.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(32 + 32 + 64 + 4 + self.current_key_set.len() * 32);
        out.extend_from_slice(&self.attestor_pubkey);
        out.extend_from_slice(&self.new_device_pubkey);
        out.extend_from_slice(&self.signature);
        out.extend_from_slice(&(self.current_key_set.len() as u32).to_le_bytes());
        for k in &self.current_key_set {
            out.extend_from_slice(k);
        }
        out
    }

    /// Decode the framing produced by [`encode`](Self::encode). Returns `None`
    /// on any length/shape error (the verifier maps that to a fail-closed
    /// rejection).
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < 32 + 32 + 64 + 4 {
            return None;
        }
        let mut off = 0;
        let mut take = |n: usize| -> Option<&[u8]> {
            let s = bytes.get(off..off + n)?;
            off += n;
            Some(s)
        };
        let attestor_pubkey: [u8; 32] = take(32)?.try_into().ok()?;
        let new_device_pubkey: [u8; 32] = take(32)?.try_into().ok()?;
        let signature: [u8; 64] = take(64)?.try_into().ok()?;
        let n = u32::from_le_bytes(take(4)?.try_into().ok()?) as usize;
        let mut current_key_set = Vec::with_capacity(n);
        for _ in 0..n {
            current_key_set.push(take(32)?.try_into().ok()?);
        }
        if off != bytes.len() {
            return None; // trailing garbage — fail closed.
        }
        Some(Self {
            attestor_pubkey,
            current_key_set,
            new_device_pubkey,
            signature,
        })
    }
}

// =============================================================================
// The verifier
// =============================================================================

/// Discharges an `Authorization::Custom { vk_hash: PAIRING_VK }` device-pairing
/// attestation.
///
/// `verify` decodes the [`PairingAttestation`] from the proof blob, recomputes
/// `key_set_commitment(current_key_set)` and pins it to the host-trusted
/// predicate `commitment` (so the prover cannot present a set of their own),
/// checks the attestor is a member of that set, and checks the Ed25519
/// signature over `PAIRING_SIG_DOMAIN ‖ signing_message ‖ new_device_pubkey`.
/// Any divergence fails closed. The predicate `commitment` IS the identity
/// cell's current key-set commitment, host-installed at registration.
#[derive(Clone, Debug, Default)]
pub struct DevicePairingVerifier;

impl WitnessedPredicateVerifier for DevicePairingVerifier {
    fn name(&self) -> &'static str {
        "device-pairing-attestation"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom { vk_hash: PAIRING_VK }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The only input shape an authorization discharge supplies.
        let signing_message: &[u8] = match input {
            PredicateInput::SigningMessage(m) => m,
            PredicateInput::Bytes(b) => b,
            other => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "DevicePairing",
                    expected: "SigningMessage (canonical custom-auth message bytes)",
                    actual: match other {
                        PredicateInput::Slot(_) => "Slot",
                        PredicateInput::PublicInput(_) => "PublicInput",
                        PredicateInput::Sender(_) => "Sender",
                        _ => "unexpected",
                    },
                });
            }
        };

        let att = PairingAttestation::decode(proof_bytes).ok_or(
            WitnessedPredicateError::Rejected {
                kind_name: "DevicePairing",
                reason: "pairing attestation did not decode".into(),
            },
        )?;

        // (1) The exhibited current key set MUST reproduce the host-pinned
        // commitment. This is what makes the attestor's authority real: the
        // host trusts `commitment` (the identity's current key-set
        // commitment), and only a set hashing to it is accepted.
        if &key_set_commitment(&att.current_key_set) != commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "DevicePairing",
                reason: "exhibited current key set does not match the host-trusted \
                         current-keys commitment (an unauthorized set was presented)"
                    .into(),
            });
        }

        // (2) The attestor MUST be a member of that current set — only an
        // already-authorized device may designate. (Empowered, not amplified.)
        if !att.current_key_set.contains(&att.attestor_pubkey) {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "DevicePairing",
                reason: "attestor public key is not a member of the current key set; \
                         only an already-authorized device may pair a new one"
                    .into(),
            });
        }

        // (3) The Ed25519 signature over domain ‖ signing_message ‖ new pubkey
        // MUST verify under the attestor key. Binds the whole action body (via
        // the signing message) AND the specific new device being admitted.
        let vk = VerifyingKey::from_bytes(&att.attestor_pubkey).map_err(|e| {
            WitnessedPredicateError::Rejected {
                kind_name: "DevicePairing",
                reason: format!("attestor public key is not a valid Ed25519 point: {e}"),
            }
        })?;
        let sig = DalekSignature::from_bytes(&att.signature);
        let signed = PairingAttestation::signed_bytes(signing_message, &att.new_device_pubkey);
        vk.verify(&signed, &sig).map_err(|_| WitnessedPredicateError::Rejected {
            kind_name: "DevicePairing",
            reason: "pairing attestation signature did not verify under the attestor key \
                     (forged, wrong device, or wrong turn)"
                .into(),
        })?;

        Ok(())
    }
}

/// Install a [`DevicePairingVerifier`] into `registry` under [`PAIRING_VK`].
/// Call after building the base production registry
/// (`registry_with_real_verifiers`) so the identity program's other witnessed
/// predicates still enforce, then set it on the runtime.
pub fn register_device_pairing_verifier(registry: &mut WitnessedPredicateRegistry) {
    registry.register_custom(PAIRING_VK, Arc::new(DevicePairingVerifier));
}

// =============================================================================
// The turn builder
// =============================================================================

/// Build the device-pairing rotation action, UNSIGNED (a placeholder proof
/// blob at index 0). The caller fixes the turn nonce, computes the canonical
/// custom signing message, has the existing device sign the attestation, then
/// swaps the encoded [`PairingAttestation`] into `witness_blobs[1]` (see
/// [`fill_pairing_attestation`]).
///
/// * `identity_cell` — the identity whose key set the new device joins.
/// * `current_key_set` — the identity's current ordered device keys. The
///   `new_device_pubkey` is appended to form the presented set; its commitment
///   must equal the pre-committed `next_keys_digest` preimage (KERI discipline).
/// * `new_device_pubkey` — the device being added.
/// * `fresh_next_digest` — the forward chain's next link
///   (`next_keys_digest(key_set_commitment(after-next set))`).
/// * `height` — the execution height the gate pins for the cooling window.
///
/// Layout: `witness_blobs[0]` = the `KeyRotationGate` preimage exhibit (the
/// presented commitment); `witness_blobs[1]` = the pairing attestation (filled
/// after signing).
pub fn pairing_action(
    identity_cell: CellId,
    current_key_set: &[[u8; 32]],
    new_device_pubkey: [u8; 32],
    fresh_next_digest: FieldElement,
    height: u64,
) -> Action {
    let paired = PairingAttestation::paired_key_set(current_key_set, new_device_pubkey);
    let presented = key_set_commitment(&paired);

    let predicate = WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom { vk_hash: PAIRING_VK },
        // The host-trusted current key-set commitment — the verifier pins the
        // attestor's exhibited set to exactly this.
        commitment: key_set_commitment(current_key_set),
        input_ref: InputRef::SigningMessage,
        proof_witness_index: 1,
    };

    let mut action = crate::raw::unsigned_action_named(
        identity_cell,
        "pair_device",
        rotate_effects(identity_cell, presented, fresh_next_digest, height),
    );
    action.authorization = Authorization::Custom { predicate };
    action.witness_blobs = vec![
        // index 0: the KeyRotationGate preimage exhibit (the augmented set's
        // commitment — proves the presented set is the pre-committed one).
        WitnessBlob::preimage(presented),
        // index 1: a placeholder for the pairing attestation, swapped in after
        // the existing device signs.
        WitnessBlob::proof(Vec::new()),
    ];
    action
}

/// The canonical signing-message bytes for a pairing `action` at `turn_nonce`,
/// position 0, under `federation_id` — exactly what the executor recomputes at
/// verification time. The existing device signs
/// [`PairingAttestation::signed_bytes`] of this.
pub fn pairing_signing_message(
    action: &Action,
    federation_id: &[u8; 32],
    turn_nonce: u64,
) -> Vec<u8> {
    let predicate = match &action.authorization {
        Authorization::Custom { predicate } => predicate.clone(),
        other => panic!("pairing action must carry Authorization::Custom, got {other:?}"),
    };
    dregg_turn::executor::TurnExecutor::compute_custom_signing_message(
        action,
        &predicate,
        0,
        federation_id,
        turn_nonce,
    )
}

/// Swap the encoded attestation into the pairing action's `witness_blobs[1]`.
pub fn fill_pairing_attestation(action: &mut Action, attestation: &PairingAttestation) {
    action.witness_blobs[1] = WitnessBlob::proof(attestation.encode());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::next_keys_digest;
    use ed25519_dalek::{Signer, SigningKey};

    fn sk(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn pk(sk: &SigningKey) -> [u8; 32] {
        sk.verifying_key().to_bytes()
    }

    #[test]
    fn attestation_roundtrips() {
        let att = PairingAttestation {
            attestor_pubkey: [1u8; 32],
            current_key_set: vec![[1u8; 32], [2u8; 32], [3u8; 32]],
            new_device_pubkey: [9u8; 32],
            signature: [7u8; 64],
        };
        assert_eq!(PairingAttestation::decode(&att.encode()), Some(att));
    }

    #[test]
    fn decode_rejects_trailing_garbage() {
        let att = PairingAttestation {
            attestor_pubkey: [1u8; 32],
            current_key_set: vec![[1u8; 32]],
            new_device_pubkey: [9u8; 32],
            signature: [7u8; 64],
        };
        let mut bytes = att.encode();
        bytes.push(0xFF);
        assert_eq!(PairingAttestation::decode(&bytes), None);
    }

    /// THE TOOTH (verifier unit, true): a genuine attestation by a current-set
    /// device over the right message admits.
    #[test]
    fn verifier_accepts_genuine_attestation() {
        let device_a = sk(0xA1);
        let device_b = sk(0xB2); // the new device
        let current = vec![pk(&device_a), [0x22; 32]];
        let commitment = key_set_commitment(&current);
        let msg = b"canonical-custom-signing-message".to_vec();

        let signed = PairingAttestation::signed_bytes(&msg, &pk(&device_b));
        let sig = device_a.sign(&signed).to_bytes();
        let att = PairingAttestation {
            attestor_pubkey: pk(&device_a),
            current_key_set: current,
            new_device_pubkey: pk(&device_b),
            signature: sig,
        };

        DevicePairingVerifier
            .verify(&commitment, &PredicateInput::SigningMessage(&msg), &att.encode())
            .expect("a current-device attestation over the right message admits");
    }

    /// THE TOOTH (verifier unit, false): a signer who is NOT in the current set
    /// is refused even with a valid signature.
    #[test]
    fn verifier_refuses_non_member_attestor() {
        let outsider = sk(0xEE); // NOT in the current set
        let device_b = sk(0xB2);
        let current = vec![[0x11; 32], [0x22; 32]];
        let commitment = key_set_commitment(&current);
        let msg = b"canonical-custom-signing-message".to_vec();

        let signed = PairingAttestation::signed_bytes(&msg, &pk(&device_b));
        let sig = outsider.sign(&signed).to_bytes();
        let att = PairingAttestation {
            attestor_pubkey: pk(&outsider),
            current_key_set: current,
            new_device_pubkey: pk(&device_b),
            signature: sig,
        };

        let err = DevicePairingVerifier
            .verify(&commitment, &PredicateInput::SigningMessage(&msg), &att.encode())
            .expect_err("a non-member attestor must be refused");
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    /// THE TOOTH (verifier unit, false): a set that does not hash to the
    /// host-trusted commitment is refused (a prover cannot present their own
    /// set to manufacture membership).
    #[test]
    fn verifier_refuses_wrong_current_set() {
        let device_a = sk(0xA1);
        let device_b = sk(0xB2);
        let real_current = vec![pk(&device_a), [0x22; 32]];
        let host_commitment = key_set_commitment(&real_current);

        // The attacker exhibits a DIFFERENT set (containing their own key) and
        // signs correctly over it — but it does not hash to `host_commitment`.
        let attacker = sk(0xCC);
        let attacker_set = vec![pk(&attacker)];
        let msg = b"canonical-custom-signing-message".to_vec();
        let signed = PairingAttestation::signed_bytes(&msg, &pk(&device_b));
        let sig = attacker.sign(&signed).to_bytes();
        let att = PairingAttestation {
            attestor_pubkey: pk(&attacker),
            current_key_set: attacker_set,
            new_device_pubkey: pk(&device_b),
            signature: sig,
        };

        let err = DevicePairingVerifier
            .verify(&host_commitment, &PredicateInput::SigningMessage(&msg), &att.encode())
            .expect_err("an exhibited set that does not match the host commitment must be refused");
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    /// THE TOOTH (verifier unit, false): a signature over a DIFFERENT new
    /// device (the attacker tries to swap which device gets admitted) is
    /// refused — the new pubkey is bound into the signed bytes.
    #[test]
    fn verifier_refuses_swapped_new_device() {
        let device_a = sk(0xA1);
        let honest_new = sk(0xB2);
        let attacker_new = sk(0xDD);
        let current = vec![pk(&device_a), [0x22; 32]];
        let commitment = key_set_commitment(&current);
        let msg = b"canonical-custom-signing-message".to_vec();

        // device_a signed over honest_new…
        let signed = PairingAttestation::signed_bytes(&msg, &pk(&honest_new));
        let sig = device_a.sign(&signed).to_bytes();
        // …but the blob claims attacker_new.
        let att = PairingAttestation {
            attestor_pubkey: pk(&device_a),
            current_key_set: current,
            new_device_pubkey: pk(&attacker_new),
            signature: sig,
        };

        let err = DevicePairingVerifier
            .verify(&commitment, &PredicateInput::SigningMessage(&msg), &att.encode())
            .expect_err("a signature over a different new device must be refused");
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn paired_key_set_appends_and_recommits_stably() {
        let current = vec![[1u8; 32], [2u8; 32]];
        let new = [9u8; 32];
        let paired = PairingAttestation::paired_key_set(&current, new);
        assert_eq!(paired, vec![[1u8; 32], [2u8; 32], [9u8; 32]]);
        // Position-committed + deterministic.
        assert_eq!(key_set_commitment(&paired), key_set_commitment(&PairingAttestation::paired_key_set(&current, new)));
        // Adding the device changes the commitment (the rotation is real).
        assert_ne!(key_set_commitment(&paired), key_set_commitment(&current));
        // next_keys_digest of the paired commitment is the gate preimage relation.
        let _ = next_keys_digest(&key_set_commitment(&paired));
    }
}
