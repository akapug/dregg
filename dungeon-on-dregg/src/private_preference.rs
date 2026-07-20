//! Hiding private party preference as a transportable game decision.
//!
//! Four participants privately score four public options from 0 through 3. The
//! Lean-authored `private-preference-n4k4` relation proves the lowest-index
//! aggregate maximizer and publishes only `(session, rule, ballot_root8,
//! winner)`. Ballots, totals, the winning total, and commitment blinding stay
//! absent from the receipt.
//!
//! [`PrivatePreferenceSession`] is the public one-shot game lifecycle. It pins
//! the session and standalone HidingFri verifier identity, verifies transported
//! proof bytes, and refuses replay without changing the landed decision. The
//! proof producer still sees all four ballots (Tier 1); this module is not a
//! distributed ballot-assembly protocol. A separate Lean-emitted custom-cell
//! descriptor and canonical-v2 registry exist for recursive `Effect::Custom`
//! settlement, but this lightweight hosted receipt does not claim that fold.

use dregg_circuit_prove::private_preference as proof;
use serde::{Deserialize, Serialize};

pub const PARTICIPANTS: usize = proof::PARTICIPANT_COUNT;
pub const OPTIONS: usize = proof::OPTION_COUNT;
pub const DIGEST_WIDTH: usize = proof::DIGEST_WIDTH;

pub use proof::PrivateBallot;

/// Stable storage/network representation. Its public inputs are the exact
/// Lean descriptor ABI; proof bytes are opaque to every layer except the
/// canonical verifier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivatePreferenceWireReceipt {
    pub verifier_key: [u8; 32],
    pub public_inputs: Vec<u32>,
    pub proof_bytes: Vec<u8>,
}

impl PrivatePreferenceWireReceipt {
    pub fn to_postcard(&self) -> Result<Vec<u8>, PrivatePreferenceError> {
        postcard::to_allocvec(self).map_err(|error| {
            PrivatePreferenceError::WireFormat(format!(
                "cannot encode private preference receipt: {error}"
            ))
        })
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, PrivatePreferenceError> {
        postcard::from_bytes(bytes).map_err(|error| {
            PrivatePreferenceError::WireFormat(format!(
                "cannot decode private preference receipt: {error}"
            ))
        })
    }

    pub fn into_receipt(self) -> Result<PrivatePreferenceReceipt, PrivatePreferenceError> {
        if self.verifier_key != proof::canonical_vk_hash() {
            return Err(PrivatePreferenceError::VerifierMismatch);
        }
        let statement = proof::PublicStatement::try_from_u32s(&self.public_inputs)
            .map_err(PrivatePreferenceError::InvalidStatement)?;
        if self.proof_bytes.is_empty() {
            return Err(PrivatePreferenceError::WireFormat(
                "private preference proof is empty".to_string(),
            ));
        }
        Ok(PrivatePreferenceReceipt {
            statement,
            proof_bytes: self.proof_bytes,
            verifier_key: self.verifier_key,
        })
    }
}

/// Owning public receipt. Its `Debug` surface reports only public metadata and
/// proof length, never private ballots or a deserialized proof internals tree.
#[derive(Clone, PartialEq, Eq)]
pub struct PrivatePreferenceReceipt {
    statement: proof::PublicStatement,
    proof_bytes: Vec<u8>,
    verifier_key: [u8; 32],
}

impl std::fmt::Debug for PrivatePreferenceReceipt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivatePreferenceReceipt")
            .field("statement", &self.statement)
            .field("verifier_key", &self.verifier_key)
            .field("proof_len", &self.proof_bytes.len())
            .finish()
    }
}

impl PrivatePreferenceReceipt {
    fn from_proof(
        zk_proof: &proof::PrivatePreferenceZkProof,
        statement: proof::PublicStatement,
    ) -> Result<Self, PrivatePreferenceError> {
        proof::verify_zk(zk_proof, statement).map_err(PrivatePreferenceError::InvalidProof)?;
        Ok(Self {
            statement,
            proof_bytes: zk_proof
                .to_postcard()
                .map_err(PrivatePreferenceError::InvalidProof)?,
            verifier_key: proof::canonical_vk_hash(),
        })
    }

    pub const fn statement(&self) -> proof::PublicStatement {
        self.statement
    }

    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }

    pub const fn verifier_key(&self) -> [u8; 32] {
        self.verifier_key
    }

    pub fn to_wire(&self) -> PrivatePreferenceWireReceipt {
        PrivatePreferenceWireReceipt {
            verifier_key: self.verifier_key,
            public_inputs: self.statement.as_u32_vec(),
            proof_bytes: self.proof_bytes.clone(),
        }
    }

    pub fn to_postcard(&self) -> Result<Vec<u8>, PrivatePreferenceError> {
        self.to_wire().to_postcard()
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, PrivatePreferenceError> {
        PrivatePreferenceWireReceipt::from_postcard(bytes)?.into_receipt()
    }
}

/// Produce a real HidingFri receipt from exactly four private ballots.
pub fn prove_private_preference(
    session: u32,
    ballots: &[PrivateBallot],
) -> Result<PrivatePreferenceReceipt, PrivatePreferenceError> {
    let (zk_proof, statement) = proof::prove_ballots_zk(session, ballots)
        .map_err(PrivatePreferenceError::InvalidPrivateInput)?;
    PrivatePreferenceReceipt::from_proof(&zk_proof, statement)
}

/// Public application value minted only after proof verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivatePartyDecision {
    session: u32,
    ballot_root: [u32; DIGEST_WIDTH],
    winner: usize,
}

impl PrivatePartyDecision {
    pub const fn session(self) -> u32 {
        self.session
    }

    pub const fn ballot_root(self) -> [u32; DIGEST_WIDTH] {
        self.ballot_root
    }

    pub const fn winner(self) -> usize {
        self.winner
    }
}

/// One public decision slot. Exactly one verified private preference result may
/// land for the session; all refusals leave the previous value unchanged.
#[derive(Clone, Debug)]
pub struct PrivatePreferenceSession {
    session: u32,
    decision: Option<PrivatePartyDecision>,
}

impl PrivatePreferenceSession {
    pub fn new(session: u32) -> Result<Self, PrivatePreferenceError> {
        proof::PublicStatement {
            session,
            rule: proof::RULE_ID,
            ballot_root: [0; DIGEST_WIDTH],
            winner: 0,
        }
        .validate_shape()
        .map_err(PrivatePreferenceError::InvalidStatement)?;
        Ok(Self {
            session,
            decision: None,
        })
    }

    pub const fn session(&self) -> u32 {
        self.session
    }

    pub const fn decision(&self) -> Option<&PrivatePartyDecision> {
        self.decision.as_ref()
    }

    pub fn accept(
        &mut self,
        receipt: &PrivatePreferenceReceipt,
    ) -> Result<PrivatePartyDecision, PrivatePreferenceError> {
        if self.decision.is_some() {
            return Err(PrivatePreferenceError::Replay);
        }
        if receipt.verifier_key != proof::canonical_vk_hash() {
            return Err(PrivatePreferenceError::VerifierMismatch);
        }
        if receipt.statement.session != self.session {
            return Err(PrivatePreferenceError::SessionMismatch {
                expected: self.session,
                claimed: receipt.statement.session,
            });
        }
        let zk_proof = proof::PrivatePreferenceZkProof::from_postcard(&receipt.proof_bytes)
            .map_err(PrivatePreferenceError::InvalidProof)?;
        let verified = proof::verify_decision_zk(&zk_proof, receipt.statement)
            .map_err(PrivatePreferenceError::InvalidProof)?;
        let decision = PrivatePartyDecision {
            session: verified.session,
            ballot_root: verified.ballot_root,
            winner: verified.winner,
        };
        self.decision = Some(decision);
        Ok(decision)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivatePreferenceError {
    InvalidPrivateInput(String),
    InvalidStatement(String),
    InvalidProof(String),
    WireFormat(String),
    VerifierMismatch,
    SessionMismatch { expected: u32, claimed: u32 },
    Replay,
}

impl std::fmt::Display for PrivatePreferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPrivateInput(reason) => {
                write!(f, "private preference input refused: {reason}")
            }
            Self::InvalidStatement(reason) => {
                write!(f, "private preference public statement refused: {reason}")
            }
            Self::InvalidProof(reason) => write!(f, "private preference proof refused: {reason}"),
            Self::WireFormat(reason) => {
                write!(f, "private preference receipt refused: {reason}")
            }
            Self::VerifierMismatch => write!(f, "private preference verifier identity mismatch"),
            Self::SessionMismatch { expected, claimed } => write!(
                f,
                "private preference session mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::Replay => write!(f, "private preference session is already decided"),
        }
    }
}

impl std::error::Error for PrivatePreferenceError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn ballots() -> [PrivateBallot; PARTICIPANTS] {
        [
            PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
            PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
            PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
            PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
        ]
    }

    #[test]
    fn hiding_preference_receipt_is_strict_session_bound_and_one_shot() {
        let receipt = prove_private_preference(77, &ballots()).unwrap();
        let bytes = receipt.to_postcard().unwrap();
        let decoded = PrivatePreferenceReceipt::from_postcard(&bytes).unwrap();
        assert_eq!(decoded.to_postcard().unwrap(), bytes);
        assert_eq!(decoded.statement().winner, 1);

        let mut wrong = PrivatePreferenceSession::new(78).unwrap();
        assert!(matches!(
            wrong.accept(&decoded),
            Err(PrivatePreferenceError::SessionMismatch { .. })
        ));
        assert!(wrong.decision().is_none());

        let mut session = PrivatePreferenceSession::new(77).unwrap();
        let decision = session.accept(&decoded).unwrap();
        assert_eq!(decision.winner(), 1);
        assert_eq!(session.decision(), Some(&decision));
        assert_eq!(
            session.accept(&decoded),
            Err(PrivatePreferenceError::Replay)
        );
        assert_eq!(session.decision(), Some(&decision));
    }
}
