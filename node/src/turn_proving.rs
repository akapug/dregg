//! Full-turn STARK proving on the node's finalized-turn commit path.
//!
//! This module makes the public claim — *every committed state transition is
//! proven* — TRUE for the running node. When the devnet enables full-turn
//! proving, [`crate::blocklace_sync::execute_finalized_turn`] calls
//! [`prove_and_verify_finalized_turn`] for each finalized turn:
//!
//! 1. **Prove.** The turn's effects (projected onto the actor cell) are
//!    marshalled into the Effect VM encoding via the cipherclerk's existing
//!    [`AgentCipherclerk::convert_effects_to_vm`] marshaller, and a real
//!    `FullTurnProof` (a composed STARK over the Effect-VM AIR) is generated
//!    with [`dregg_sdk::prove_turn_self_sovereign`].
//!
//! 2. **Verify → accept.** The freshly generated proof is *re-verified*
//!    against the actor cell's pre-state commitment (`old_commit`) and the
//!    proven post-state commitment (`new_commit`) using
//!    [`dregg_sdk::verify_full_turn`] — the same verifier remote peers use.
//!    Acceptance is **gated** on this check: if the proof does not verify
//!    against the expected commitments, the turn is *not* accepted as proven
//!    (the caller surfaces a rejection).
//!
//! The anti-ghost property is exercised in this module's tests: a turn whose
//! post-state commitment is forged (any felt off by one) is **REJECTED** by
//! `verify_full_turn`, because the Effect-VM AIR binds the new commitment at
//! its boundary row and the verifier checks it against the caller's expected
//! value (`CommitmentMismatch`).
//!
//! ## Soundness scope (honest)
//!
//! The Effect VM proves the actor cell's `(balance, nonce, fields, cap_root)`
//! transition. `old_commit` is the actor cell's pre-execution
//! `CellState::compute_commitment` and `new_commit` is read from the AIR's
//! boundary public input (the prover cannot forge it without producing an
//! invalid trace). This is the per-cell whole-turn binding the SDK FullTurn
//! phase established; it is the load-bearing commit-path leg the public claim
//! rests on. Cross-cell / multi-root aggregation is the Silver→Gold vision and
//! is tracked separately — it does not weaken what is proven here.

use dregg_circuit::field::BabyBear;
use dregg_circuit::{CellState, generate_effect_vm_trace};
use dregg_sdk::{AgentCipherclerk, FullTurnProof, FullTurnVerifyError, prove_turn_self_sovereign};
use dregg_types::CellId;

/// A finalized turn that carries a real, re-verified full-turn STARK proof.
#[derive(Clone)]
pub struct ProvenFinalizedTurn {
    /// The composed full-turn proof (Effect-VM STARK), ready for wire transmission.
    pub proof: FullTurnProof,
    /// Position-0 felt of the actor cell's pre-execution state commitment.
    pub old_commit: BabyBear,
    /// Position-0 felt of the proven post-execution state commitment.
    pub new_commit: BabyBear,
}

impl ProvenFinalizedTurn {
    /// Serialized proof bytes (the wire form attached to the committed turn).
    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof.proof_bytes
    }
}

/// Errors from the full-turn proving + verify→accept leg.
#[derive(Debug)]
pub enum FullTurnProvingError {
    /// Proof generation failed (invalid witness).
    Prove(dregg_sdk::SdkError),
    /// The freshly generated proof did NOT verify against the expected
    /// pre/post commitments. Acceptance is gated on this: a turn whose proof
    /// does not verify is not accepted as proven.
    Verify(FullTurnVerifyError),
}

impl std::fmt::Display for FullTurnProvingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Prove(e) => write!(f, "full-turn proof generation failed: {e}"),
            Self::Verify(e) => write!(f, "full-turn proof verification failed: {e}"),
        }
    }
}

impl std::error::Error for FullTurnProvingError {}

/// Prove a finalized turn and gate acceptance on the proof verifying.
///
/// `pre_balance` / `pre_nonce` are the actor cell's state captured **before**
/// the executor mutated the ledger (the pre-state the proof's `old_commit`
/// binds to). `effects` are the turn's effects (the caller passes
/// `turn.call_forest.total_effects()` cloned).
///
/// Returns the proven turn on success, or [`FullTurnProvingError`] if proving
/// fails or — critically — if the freshly generated proof does not verify
/// against the expected commitments (the verify→accept leg).
pub fn prove_and_verify_finalized_turn(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // 1. Marshal the turn's effects onto the actor cell in the Effect-VM
    //    encoding (reuses the cipherclerk's canonical marshaller so the node
    //    proves exactly what the cipherclerk would sign).
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(agent, effects);

    // 2. Build the actor cell's pre-execution Effect-VM state. The old
    //    commitment the proof binds to is this state's commitment.
    let initial_vm_state = CellState::new(pre_balance, pre_nonce as u32);
    let old_commit = initial_vm_state.state_commitment;

    // 3. Derive the proven post-state commitment from the AIR boundary public
    //    input. The prover cannot forge this without an invalid trace.
    let (_trace, pi) = generate_effect_vm_trace(&initial_vm_state, &vm_effects);
    let new_commit = pi[dregg_circuit::effect_vm::pi::NEW_COMMIT];

    // 4. Generate the real composed full-turn STARK proof.
    let proof = prove_turn_self_sovereign(&initial_vm_state, &vm_effects, turn_hash)
        .map_err(FullTurnProvingError::Prove)?;

    // 5. VERIFY → ACCEPT leg. Re-verify the proof against the expected
    //    pre/post commitments using the same verifier a remote peer runs.
    //    Acceptance is gated on this returning Ok.
    dregg_sdk::verify_full_turn(&proof, old_commit, new_commit)
        .map_err(FullTurnProvingError::Verify)?;

    Ok(ProvenFinalizedTurn {
        proof,
        old_commit,
        new_commit,
    })
}

/// Config-store key under which a finalized turn's proof bytes are persisted,
/// keyed by the turn hash (hex). Lets an operator / API surface the attached
/// proof for any committed turn.
pub fn turn_proof_config_key(turn_hash_hex: &str) -> String {
    format!("full_turn_proof:{turn_hash_hex}")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A committed transfer turn carries a proof that VERIFIES against the
    /// expected pre/post commitments (the verify→accept leg succeeds).
    #[test]
    fn committed_turn_carries_verifying_proof() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        // Alice sends 100 to Bob. From Alice's actor-cell perspective this is
        // an outgoing transfer (balance debits by 100).
        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 100,
        }];
        let turn_hash = [0x11u8; 32];

        let proven = prove_and_verify_finalized_turn(&alice, 1000, 0, &effects, turn_hash)
            .expect("finalized turn should prove and self-verify");

        // The proof is real (non-empty wire bytes) and re-verifies.
        assert!(!proven.proof_bytes().is_empty());
        assert!(proven.proof.components.has_state_transition);
        assert_eq!(proven.proof.turn_hash, turn_hash);

        // Independent re-verification against the carried commitments.
        dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit)
            .expect("carried proof must re-verify against carried commitments");
    }

    /// ANTI-GHOST: a turn whose post-state commitment is FORGED (off by one
    /// felt) is REJECTED. The Effect-VM AIR binds the new commitment at its
    /// boundary; `verify_full_turn` checks it against the expected value and
    /// returns `CommitmentMismatch`.
    #[test]
    fn forged_post_state_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 100,
        }];
        let turn_hash = [0x22u8; 32];

        let proven = prove_and_verify_finalized_turn(&alice, 1000, 0, &effects, turn_hash)
            .expect("honest turn should prove");

        // Forge the post-state commitment: claim a DIFFERENT new state than
        // the one the proof actually attests.
        let forged_new_commit = proven.new_commit + BabyBear::new(1);
        assert_ne!(forged_new_commit, proven.new_commit);

        let result =
            dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, forged_new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: forged post-state commitment MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "new_commitment");
            }
            other => panic!("expected new_commitment mismatch, got {other:?}"),
        }
    }

    /// ANTI-GHOST (pre-state): forging the OLD commitment (claiming the turn
    /// started from a different cell state than it did) is also REJECTED.
    #[test]
    fn forged_pre_state_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 50,
        }];
        let turn_hash = [0x33u8; 32];

        let proven = prove_and_verify_finalized_turn(&alice, 777, 3, &effects, turn_hash)
            .expect("honest turn should prove");

        let forged_old_commit = proven.old_commit + BabyBear::new(1);
        let result =
            dregg_sdk::verify_full_turn(&proven.proof, forged_old_commit, proven.new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: forged pre-state commitment MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "old_commitment");
            }
            other => panic!("expected old_commitment mismatch, got {other:?}"),
        }
    }
}
