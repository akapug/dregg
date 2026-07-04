//! Proof-carrying dregg → Midnight bridge envelope.
//!
//! # What this adds over [`crate::midnight`]
//!
//! The plain [`DreggToMidnightMessage`] is a *Level 1* (attestation-only) bridge
//! message: the Midnight contract trusts the dregg federation's threshold
//! signature that a burn happened with the stated `(nullifier, amount,
//! recipient)`. There is no independent way for a watcher to check that the
//! federation is telling the truth — safety rests entirely on *threshold*
//! honesty.
//!
//! Now that the deployed circuit carries a verified bridge-action AIR
//! ([`dregg_circuit::bridge_action_air`], wrapped by [`crate::action_binding`]),
//! we can make the message *proof-carrying*. A [`VerifiedDreggToMidnight`]
//! envelope bundles the federation attestation with a [`PortableActionBinding`]
//! — a STARK proof that algebraically pins the burn's
//! `(nullifier, recipient_commitment, destination_federation, amount)` at full
//! byte/bit fidelity.
//!
//! This is the production plan's **Level 1.5 / 1-of-N** shape
//! (`plans/midnight-bridge-production.md`):
//!
//! - **Liveness** comes from the federation attestation (same as Level 1).
//! - **Safety** comes from the embedded circuit proof: *any single* honest
//!   watcher can verify the proof and detect a federation that attests to a
//!   burn the circuit never witnessed. The proof IS the fraud-proof material.
//!
//! # The cross-binding
//!
//! The bridge-action AIR binds four 32-byte/u64 fields. We thread the
//! cross-chain message into them as follows:
//!
//! | AIR field                | bound to                                            |
//! |--------------------------|-----------------------------------------------------|
//! | `nullifier`              | the spent dregg note's nullifier (== message)       |
//! | `recipient`              | `commit_midnight_recipient(message.midnight_recipient)` |
//! | `destination_federation` | a well-known Midnight-bridge federation id          |
//! | `amount`                 | the full u64 bridge amount (== message)             |
//!
//! The `recipient` field is a BLAKE3 commitment to the Midnight recipient key,
//! which cryptographically ties the circuit-proven burn to the *specific*
//! Midnight payout target. `destination_federation` pins the burn as routed to
//! Midnight (not some other federation), so a proof minted for a different
//! destination cannot be replayed at the Midnight contract.

use serde::{Deserialize, Serialize};

use crate::action_binding::{
    ActionBindingError, PortableActionBinding, create_action_binding, verify_action_binding,
};
use crate::midnight::{
    DreggToMidnightMessage, FederationAttestation, MidnightBridgeConfig, MidnightBridgeError,
    NonceTracker, validate_dregg_to_midnight,
};

/// Domain-separation tag for committing a Midnight recipient key into the
/// dregg-side bridge-action proof's `recipient` field.
const RECIPIENT_COMMIT_TAG: &str = "dregg-midnight-recipient-commit-v1";

/// Commit a Midnight recipient public key to the 32-byte `recipient` field that
/// the bridge-action circuit binds.
///
/// Using a commitment (rather than embedding the raw key) keeps the AIR field a
/// fixed 32 bytes regardless of the recipient encoding, and domain-separates the
/// bridge-out path from any other use of the same key.
pub fn commit_midnight_recipient(midnight_recipient: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(RECIPIENT_COMMIT_TAG);
    hasher.update(midnight_recipient);
    *hasher.finalize().as_bytes()
}

/// A dregg → Midnight bridge message bound to a verified circuit proof of the
/// underlying burn.
///
/// See the module docs for the trust model. Verify with [`Self::verify`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VerifiedDreggToMidnight {
    /// The attestation-bearing cross-chain message (Level 1 payload).
    pub message: DreggToMidnightMessage,
    /// The verified bridge-action binding: a STARK proof pinning the burn
    /// parameters at full fidelity (the fraud-proof material).
    pub binding: PortableActionBinding,
}

/// Errors from verifying a [`VerifiedDreggToMidnight`] envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifiedBridgeError {
    /// The Level 1 attestation / limit / nonce / recipient-length checks failed.
    Attestation(MidnightBridgeError),
    /// The embedded STARK proof failed to deserialize or verify.
    Binding(ActionBindingError),
    /// The binding's nullifier disagrees with the message's nullifier.
    NullifierMismatch,
    /// The binding's amount disagrees with the message's amount.
    AmountMismatch,
    /// The binding's `recipient` is not the commitment to the message's
    /// `midnight_recipient`.
    RecipientCommitmentMismatch,
    /// The binding's `destination_federation` is not the expected Midnight
    /// bridge federation id (proof was minted for a different destination).
    DestinationMismatch { expected: [u8; 32] },
}

impl core::fmt::Display for VerifiedBridgeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Attestation(e) => write!(f, "federation attestation invalid: {e}"),
            Self::Binding(e) => write!(f, "bridge-action circuit binding invalid: {e}"),
            Self::NullifierMismatch => {
                write!(f, "binding nullifier does not match message nullifier")
            }
            Self::AmountMismatch => write!(f, "binding amount does not match message amount"),
            Self::RecipientCommitmentMismatch => write!(
                f,
                "binding recipient is not the commitment to the message's midnight recipient"
            ),
            Self::DestinationMismatch { expected } => write!(
                f,
                "binding destination_federation does not match expected midnight bridge id \
                 ({:02x}{:02x}{:02x}{:02x}...)",
                expected[0], expected[1], expected[2], expected[3]
            ),
        }
    }
}

impl std::error::Error for VerifiedBridgeError {}

impl VerifiedDreggToMidnight {
    /// Build a proof-carrying envelope from a burn.
    ///
    /// Produces both halves over the *same* parameters:
    /// 1. the verified bridge-action circuit binding (full-fidelity STARK proof),
    /// 2. the federation attestation over the canonical message payload.
    ///
    /// `midnight_federation_id` is the well-known identity that marks "routed to
    /// the Midnight bridge"; the same value must be passed to [`Self::verify`].
    ///
    /// Note: [`create_action_binding`] runs a STARK prover, so this is not free.
    #[allow(clippy::too_many_arguments)]
    pub fn create(
        nullifier: [u8; 32],
        amount: u64,
        midnight_recipient: Vec<u8>,
        nonce: u64,
        midnight_federation_id: [u8; 32],
        signing_key: &ed25519_dalek::SigningKey,
        epoch: u64,
    ) -> Self {
        let recipient_commitment = commit_midnight_recipient(&midnight_recipient);
        let binding = create_action_binding(
            nullifier,
            recipient_commitment,
            midnight_federation_id,
            amount,
        );

        // Canonical payload does not depend on the attestation field, so we can
        // build it from a proto message and then attach the real signature.
        let proto = DreggToMidnightMessage {
            nullifier,
            amount,
            midnight_recipient: midnight_recipient.clone(),
            attestation: FederationAttestation {
                message_hash: [0u8; 32],
                signature: Vec::new(),
                epoch: 0,
                federation_pubkey: Vec::new(),
            },
            nonce,
        };
        let payload = proto.canonical_payload();
        let attestation = FederationAttestation::create(&payload, signing_key, epoch);

        let message = DreggToMidnightMessage {
            nullifier,
            amount,
            midnight_recipient,
            attestation,
            nonce,
        };

        Self { message, binding }
    }

    /// Fully verify the envelope.
    ///
    /// Checks, in order:
    /// 1. **Attestation leg** — [`validate_dregg_to_midnight`]: self-consistency,
    ///    federation signature for the epoch, amount limits, nonce freshness,
    ///    recipient length.
    /// 2. **Cross-binding** — the embedded proof's fields agree with the message
    ///    (nullifier, amount, recipient commitment, Midnight destination id).
    /// 3. **Circuit leg** — the STARK proof itself verifies against those exact
    ///    parameters (the fraud-proof check any single watcher can run).
    ///
    /// Returns `Ok(())` iff every leg passes.
    pub fn verify(
        &self,
        config: &MidnightBridgeConfig,
        nonce_tracker: &NonceTracker,
        midnight_federation_id: &[u8; 32],
    ) -> Result<(), VerifiedBridgeError> {
        // 1. Attestation leg (reuses the full Level 1 validation).
        validate_dregg_to_midnight(&self.message, config, nonce_tracker)
            .map_err(VerifiedBridgeError::Attestation)?;

        // 2. Cross-binding: the proof must describe THIS message's burn.
        if self.binding.nullifier != self.message.nullifier {
            return Err(VerifiedBridgeError::NullifierMismatch);
        }
        if self.binding.amount != self.message.amount {
            return Err(VerifiedBridgeError::AmountMismatch);
        }
        let expected_recipient = commit_midnight_recipient(&self.message.midnight_recipient);
        if self.binding.recipient != expected_recipient {
            return Err(VerifiedBridgeError::RecipientCommitmentMismatch);
        }
        if &self.binding.destination_federation != midnight_federation_id {
            return Err(VerifiedBridgeError::DestinationMismatch {
                expected: *midnight_federation_id,
            });
        }

        // 3. Circuit leg: the STARK proof binds those exact parameters. We pass
        //    the message-derived values (not the binding's self-reported ones)
        //    so a tampered binding cannot smuggle different params past the AIR.
        verify_action_binding(
            &self.binding,
            &self.message.nullifier,
            &expected_recipient,
            midnight_federation_id,
            self.message.amount,
        )
        .map_err(VerifiedBridgeError::Binding)?;

        Ok(())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::midnight::EpochKey;

    const MIDNIGHT_FED_ID: [u8; 32] = [0x6D; 32]; // 'm'

    fn signing_key() -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[0x42u8; 32])
    }

    fn config() -> MidnightBridgeConfig {
        let vk = signing_key().verifying_key();
        MidnightBridgeConfig {
            contract_address: [0xCC; 32],
            midnight_rpc_url: "ws://localhost:9944".to_string(),
            confirmations: 0,
            federation_keys: vec![EpochKey {
                from_epoch: 0,
                to_epoch: Some(10),
                pubkey: vk.to_bytes(),
            }],
            min_amount: 1_000_000,
            max_amount: 1_000_000_000_000,
        }
    }

    fn sample() -> VerifiedDreggToMidnight {
        VerifiedDreggToMidnight::create(
            [0xAA; 32],
            5_000_000,
            vec![0xBB; 32],
            1,
            MIDNIGHT_FED_ID,
            &signing_key(),
            0,
        )
    }

    #[test]
    fn recipient_commitment_is_deterministic_and_separating() {
        let a = commit_midnight_recipient(&[0x01; 32]);
        let b = commit_midnight_recipient(&[0x01; 32]);
        let c = commit_midnight_recipient(&[0x02; 32]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn honest_envelope_verifies() {
        let env = sample();
        let r = env.verify(&config(), &NonceTracker::new(), &MIDNIGHT_FED_ID);
        assert!(
            r.is_ok(),
            "honest proof-carrying envelope must verify: {r:?}"
        );
    }

    #[test]
    fn envelope_message_remains_level1_valid() {
        // The embedded message is still a perfectly good Level 1 message.
        let env = sample();
        assert!(env.message.is_self_consistent());
        assert!(validate_dregg_to_midnight(&env.message, &config(), &NonceTracker::new()).is_ok());
    }

    #[test]
    fn tampered_amount_in_message_rejected() {
        let mut env = sample();
        env.message.amount = 6_000_000; // proof + attestation both bind 5_000_000
        let r = env.verify(&config(), &NonceTracker::new(), &MIDNIGHT_FED_ID);
        // The attestation leg catches this first (canonical payload changed).
        assert!(
            matches!(r, Err(VerifiedBridgeError::Attestation(_))),
            "got {r:?}"
        );
    }

    #[test]
    fn tampered_amount_in_binding_rejected() {
        // Re-sign the message for a different amount than the proof binds, so the
        // attestation leg passes but the cross-binding catches the divergence.
        let nullifier = [0xAA; 32];
        let recipient = vec![0xBB; 32];
        let nonce = 1u64;
        let bad = VerifiedDreggToMidnight {
            // message attests to 5_000_000 ...
            message: VerifiedDreggToMidnight::create(
                nullifier,
                5_000_000,
                recipient.clone(),
                nonce,
                MIDNIGHT_FED_ID,
                &signing_key(),
                0,
            )
            .message,
            // ... but the binding proves a 4_000_000 burn.
            binding: crate::action_binding::create_action_binding(
                nullifier,
                commit_midnight_recipient(&recipient),
                MIDNIGHT_FED_ID,
                4_000_000,
            ),
        };
        let r = bad.verify(&config(), &NonceTracker::new(), &MIDNIGHT_FED_ID);
        assert!(
            matches!(r, Err(VerifiedBridgeError::AmountMismatch)),
            "got {r:?}"
        );
    }

    #[test]
    fn wrong_destination_federation_rejected() {
        let env = sample();
        let other = [0x99; 32];
        let r = env.verify(&config(), &NonceTracker::new(), &other);
        assert!(
            matches!(r, Err(VerifiedBridgeError::DestinationMismatch { .. })),
            "got {r:?}"
        );
    }

    #[test]
    fn swapped_recipient_commitment_rejected() {
        // Binding commits to a different Midnight recipient than the message.
        let nullifier = [0xAA; 32];
        let nonce = 1u64;
        let env = VerifiedDreggToMidnight {
            message: VerifiedDreggToMidnight::create(
                nullifier,
                5_000_000,
                vec![0xBB; 32],
                nonce,
                MIDNIGHT_FED_ID,
                &signing_key(),
                0,
            )
            .message,
            binding: crate::action_binding::create_action_binding(
                nullifier,
                commit_midnight_recipient(&[0xCD; 32]), // different recipient
                MIDNIGHT_FED_ID,
                5_000_000,
            ),
        };
        let r = env.verify(&config(), &NonceTracker::new(), &MIDNIGHT_FED_ID);
        assert!(
            matches!(r, Err(VerifiedBridgeError::RecipientCommitmentMismatch)),
            "got {r:?}"
        );
    }

    #[test]
    fn tampered_proof_bytes_rejected() {
        let mut env = sample();
        env.binding.proof_bytes[20] ^= 0xFF;
        let r = env.verify(&config(), &NonceTracker::new(), &MIDNIGHT_FED_ID);
        assert!(
            matches!(r, Err(VerifiedBridgeError::Binding(_))),
            "got {r:?}"
        );
    }

    #[test]
    fn serialization_roundtrip() {
        let env = sample();
        let bytes = postcard::to_stdvec(&env).unwrap();
        let decoded: VerifiedDreggToMidnight = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.message, env.message);
        assert_eq!(decoded.binding.nullifier, env.binding.nullifier);
        assert_eq!(decoded.binding.amount, env.binding.amount);
        // The decoded envelope still verifies.
        assert!(
            decoded
                .verify(&config(), &NonceTracker::new(), &MIDNIGHT_FED_ID)
                .is_ok()
        );
    }
}
