//! Commit-before-reveal, bias-free private eight-seat card deal.
//!
//! The proof relation is the Lean-authored `private-shuffle-fair-n8` AIR. Eight
//! private `u16` contributions are added modulo `2^16`; values below `8!` are
//! decoded with Lean's proved-bijective `Perm.decomposeFin` map, while values
//! `>= 8!` produce a proved rejected attempt rather than modulo bias. Cards and
//! contributions stay absent from the public receipt.
//!
//! [`FairShuffleTable`] supplies the temporal protocol the static AIR cannot:
//! every participant commitment must land before the proof, the recorded leaf
//! commitments must reconstruct the proof's commitment root, rejected attempts
//! are retained and advance the attempt counter, and deal openings cannot land
//! before an accepted proof. Every refusal is atomic.
//!
//! [`PreparedFairShuffle`] is deliberately a local Tier-1 producer: it sees all
//! eight contributions while constructing the trace. This is not distributed
//! input assembly, MPC, or an `Effect::Custom` cell binding. The transportable
//! receipt pins the standalone Lean-emitted HidingFri verifier identity.
//! Unbiasedness still assumes at least one participant contribution is uniform
//! conditional on the others; this local producer does not establish that
//! distributed-setup premise.

use dregg_circuit_prove::{private_shuffle, private_shuffle_fair as proof};
use serde::{Deserialize, Serialize};

pub const PARTICIPANTS: usize = proof::PARTICIPANT_COUNT;
pub const SEATS: usize = proof::SEAT_COUNT;
pub const DIGEST_WIDTH: usize = proof::DIGEST_WIDTH;
pub const OPENING_DEPTH: usize = private_shuffle::TREE_DEPTH;

/// Private producer state. Only commitments, receipts, and requested card
/// openings should cross from this object into the public game state.
pub struct PreparedFairShuffle {
    session: u32,
    attempt: u32,
    witness: proof::FairShuffleWitness,
}

impl PreparedFairShuffle {
    pub fn fresh(
        session: u32,
        attempt: u32,
        contributions: [u16; PARTICIPANTS],
    ) -> Result<Self, FairShuffleError> {
        let witness = proof::FairShuffleWitness::fresh(contributions)
            .map_err(FairShuffleError::InvalidPrivateInput)?;
        // This performs the canonical session/attempt boundary check and
        // confirms the witness fills the descriptor's exact bounded layout.
        proof::statement(session, attempt, &witness)
            .map_err(FairShuffleError::InvalidPrivateInput)?;
        Ok(Self {
            session,
            attempt,
            witness,
        })
    }

    pub const fn session(&self) -> u32 {
        self.session
    }

    pub const fn attempt(&self) -> u32 {
        self.attempt
    }

    /// Public leaf commitment for one participant. It discloses neither the
    /// contribution nor its eight-felt blinding vector.
    pub fn participant_commitment(
        &self,
        participant: usize,
    ) -> Result<[u32; DIGEST_WIDTH], FairShuffleError> {
        if participant >= PARTICIPANTS {
            return Err(FairShuffleError::ParticipantOutOfRange(participant));
        }
        proof::participant_commitment(
            self.session,
            self.attempt,
            participant,
            self.witness.seeds[participant],
            self.witness.commitment_blinding[participant],
        )
        .map_err(FairShuffleError::InvalidPrivateInput)
    }

    /// Produce the real HidingFri proof only against a table that has already
    /// recorded these exact eight public commitments.
    pub fn prove_receipt(
        &self,
        table: &FairShuffleTable,
    ) -> Result<FairShuffleReceipt, FairShuffleError> {
        if table.accepted_receipt.is_some() || table.next_attempt.is_none() {
            return Err(FairShuffleError::RoundClosed);
        }
        if table.session != self.session {
            return Err(FairShuffleError::SessionMismatch {
                expected: table.session,
                claimed: self.session,
            });
        }
        let expected_attempt = table.next_attempt.expect("open table checked above");
        if expected_attempt != self.attempt {
            return Err(FairShuffleError::AttemptMismatch {
                expected: expected_attempt,
                claimed: self.attempt,
            });
        }
        for participant in 0..PARTICIPANTS {
            let recorded =
                table.commitments[participant].ok_or(FairShuffleError::CommitmentsIncomplete)?;
            if recorded != self.participant_commitment(participant)? {
                return Err(FairShuffleError::CommitmentLeafMismatch(participant));
            }
        }
        let (zk_proof, statement) = proof::prove_zk(self.session, self.attempt, &self.witness)
            .map_err(FairShuffleError::InvalidProof)?;
        FairShuffleReceipt::from_proof(&zk_proof, statement)
    }

    /// Produce one recipient's depth-three selective opening. Rejected
    /// attempts have no deal and refuse here.
    pub fn card_opening(&self, seat: usize) -> Result<FairCardOpening, FairShuffleError> {
        proof::deal_opening(self.session, &self.witness, seat)
            .map(FairCardOpening::from)
            .map_err(FairShuffleError::InvalidOpening)
    }
}

/// Stable storage/network representation of the fair-shuffle proof receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FairShuffleWireReceipt {
    pub verifier_key: [u8; 32],
    pub public_inputs: Vec<u32>,
    pub proof_bytes: Vec<u8>,
}

impl FairShuffleWireReceipt {
    pub fn to_postcard(&self) -> Result<Vec<u8>, FairShuffleError> {
        postcard::to_allocvec(self).map_err(|error| {
            FairShuffleError::WireFormat(format!(
                "cannot encode private fair-shuffle receipt: {error}"
            ))
        })
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, FairShuffleError> {
        postcard::from_bytes(bytes).map_err(|error| {
            FairShuffleError::WireFormat(format!(
                "cannot decode private fair-shuffle receipt: {error}"
            ))
        })
    }

    pub fn into_receipt(self) -> Result<FairShuffleReceipt, FairShuffleError> {
        if self.verifier_key != proof::canonical_vk_hash() {
            return Err(FairShuffleError::VerifierMismatch);
        }
        let statement = proof::PublicStatement::try_from_u32s(&self.public_inputs)
            .map_err(FairShuffleError::InvalidStatement)?;
        if self.proof_bytes.is_empty() {
            return Err(FairShuffleError::WireFormat(
                "private fair-shuffle proof is empty".to_string(),
            ));
        }
        Ok(FairShuffleReceipt {
            statement,
            proof_bytes: self.proof_bytes,
            verifier_key: self.verifier_key,
        })
    }
}

/// Owning public receipt. Contributions, blinds, rank, and cards are absent.
#[derive(Clone, PartialEq, Eq)]
pub struct FairShuffleReceipt {
    statement: proof::PublicStatement,
    proof_bytes: Vec<u8>,
    verifier_key: [u8; 32],
}

impl std::fmt::Debug for FairShuffleReceipt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FairShuffleReceipt")
            .field("statement", &self.statement)
            .field("verifier_key", &self.verifier_key)
            .field("proof_len", &self.proof_bytes.len())
            .finish()
    }
}

impl FairShuffleReceipt {
    fn from_proof(
        zk_proof: &proof::FairShuffleZkProof,
        statement: proof::PublicStatement,
    ) -> Result<Self, FairShuffleError> {
        proof::verify_zk(zk_proof, statement).map_err(FairShuffleError::InvalidProof)?;
        Ok(Self {
            statement,
            proof_bytes: zk_proof
                .to_postcard()
                .map_err(FairShuffleError::InvalidProof)?,
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

    pub fn to_wire(&self) -> FairShuffleWireReceipt {
        FairShuffleWireReceipt {
            verifier_key: self.verifier_key,
            public_inputs: self.statement.as_u32_vec(),
            proof_bytes: self.proof_bytes.clone(),
        }
    }

    pub fn to_postcard(&self) -> Result<Vec<u8>, FairShuffleError> {
        self.to_wire().to_postcard()
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, FairShuffleError> {
        FairShuffleWireReceipt::from_postcard(bytes)?.into_receipt()
    }
}

/// Transportable one-card disclosure. It carries no other card and is not
/// accepted until its Merkle path is checked against the accepted deal root.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FairCardOpening {
    pub seat: u8,
    pub card: u8,
    pub blinding: [u32; DIGEST_WIDTH],
    pub siblings: [[u32; DIGEST_WIDTH]; OPENING_DEPTH],
}

impl From<private_shuffle::CardOpening> for FairCardOpening {
    fn from(opening: private_shuffle::CardOpening) -> Self {
        Self {
            seat: opening.seat,
            card: opening.card,
            blinding: opening.blinding,
            siblings: opening.siblings,
        }
    }
}

impl FairCardOpening {
    fn proof_opening(self) -> private_shuffle::CardOpening {
        private_shuffle::CardOpening {
            seat: self.seat,
            card: self.card,
            blinding: self.blinding,
            siblings: self.siblings,
        }
    }

    pub fn to_postcard(self) -> Result<Vec<u8>, FairShuffleError> {
        postcard::to_allocvec(&self).map_err(|error| {
            FairShuffleError::WireFormat(format!("cannot encode fair card opening: {error}"))
        })
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, FairShuffleError> {
        postcard::from_bytes(bytes).map_err(|error| {
            FairShuffleError::WireFormat(format!("cannot decode fair card opening: {error}"))
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FairShuffleAttemptOutcome {
    Accepted,
    Rejected,
}

/// Public, auditable game state for one fair deal lifecycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FairShuffleTable {
    session: u32,
    next_attempt: Option<u32>,
    commitments: [Option<[u32; DIGEST_WIDTH]>; PARTICIPANTS],
    rejected_receipts: Vec<FairShuffleReceipt>,
    accepted_receipt: Option<FairShuffleReceipt>,
    revealed_cards: [Option<u8>; SEATS],
}

impl FairShuffleTable {
    pub fn new(session: u32) -> Result<Self, FairShuffleError> {
        proof::PublicStatement {
            session,
            rule: proof::RULE_ID,
            attempt: 0,
            commitment_root: [0; DIGEST_WIDTH],
            accepted: false,
            deal_root: [0; DIGEST_WIDTH],
        }
        .validate()
        .map_err(FairShuffleError::InvalidStatement)?;
        Ok(Self {
            session,
            next_attempt: Some(0),
            commitments: [None; PARTICIPANTS],
            rejected_receipts: Vec::new(),
            accepted_receipt: None,
            revealed_cards: [None; SEATS],
        })
    }

    pub const fn session(&self) -> u32 {
        self.session
    }

    pub const fn next_attempt(&self) -> Option<u32> {
        self.next_attempt
    }

    pub fn commitments(&self) -> &[Option<[u32; DIGEST_WIDTH]>; PARTICIPANTS] {
        &self.commitments
    }

    pub fn rejected_receipts(&self) -> &[FairShuffleReceipt] {
        &self.rejected_receipts
    }

    pub fn accepted_receipt(&self) -> Option<&FairShuffleReceipt> {
        self.accepted_receipt.as_ref()
    }

    pub const fn revealed_cards(&self) -> &[Option<u8>; SEATS] {
        &self.revealed_cards
    }

    /// Record one participant commitment. Duplicate, late, malformed, and
    /// out-of-range submissions leave the table unchanged.
    pub fn commit(
        &mut self,
        participant: usize,
        commitment: [u32; DIGEST_WIDTH],
    ) -> Result<(), FairShuffleError> {
        if self.accepted_receipt.is_some() || self.next_attempt.is_none() {
            return Err(FairShuffleError::RoundClosed);
        }
        if participant >= PARTICIPANTS {
            return Err(FairShuffleError::ParticipantOutOfRange(participant));
        }
        if self.commitments[participant].is_some() {
            return Err(FairShuffleError::DuplicateCommitment(participant));
        }
        let mut validation = [[0u32; DIGEST_WIDTH]; PARTICIPANTS];
        validation[participant] = commitment;
        proof::commitment_root_from_leaves(validation)
            .map_err(FairShuffleError::InvalidCommitment)?;
        self.commitments[participant] = Some(commitment);
        Ok(())
    }

    /// Verify and apply one attempt atomically. A rejected proof is an admitted
    /// state transition: its receipt is retained, commitments are cleared, and
    /// the next attempt opens. An accepted proof seals the deal.
    pub fn accept_attempt(
        &mut self,
        receipt: &FairShuffleReceipt,
    ) -> Result<FairShuffleAttemptOutcome, FairShuffleError> {
        if self.accepted_receipt.is_some() || self.next_attempt.is_none() {
            return Err(FairShuffleError::RoundClosed);
        }
        let expected_attempt = self.next_attempt.expect("checked above");
        if receipt.verifier_key != proof::canonical_vk_hash() {
            return Err(FairShuffleError::VerifierMismatch);
        }
        if receipt.statement.session != self.session {
            return Err(FairShuffleError::SessionMismatch {
                expected: self.session,
                claimed: receipt.statement.session,
            });
        }
        if receipt.statement.attempt != expected_attempt {
            return Err(FairShuffleError::AttemptMismatch {
                expected: expected_attempt,
                claimed: receipt.statement.attempt,
            });
        }
        let leaves: [[u32; DIGEST_WIDTH]; PARTICIPANTS] = self
            .commitments
            .map(|entry| entry.ok_or(FairShuffleError::CommitmentsIncomplete))
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .expect("fixed participant count");
        let recorded_root = proof::commitment_root_from_leaves(leaves)
            .map_err(FairShuffleError::InvalidCommitment)?;
        if recorded_root != receipt.statement.commitment_root {
            return Err(FairShuffleError::CommitmentRootMismatch);
        }
        let verified =
            proof::verify_postcard(&receipt.proof_bytes, &receipt.statement.as_u32_vec())
                .map_err(FairShuffleError::InvalidProof)?;

        match verified {
            proof::VerifiedAttempt::Accepted(_) => {
                self.accepted_receipt = Some(receipt.clone());
                self.next_attempt = None;
                Ok(FairShuffleAttemptOutcome::Accepted)
            }
            proof::VerifiedAttempt::Rejected(_) => {
                let next = expected_attempt.checked_add(1).filter(|&attempt| {
                    proof::PublicStatement {
                        session: self.session,
                        rule: proof::RULE_ID,
                        attempt,
                        commitment_root: [0; DIGEST_WIDTH],
                        accepted: false,
                        deal_root: [0; DIGEST_WIDTH],
                    }
                    .validate()
                    .is_ok()
                });
                self.rejected_receipts.push(receipt.clone());
                self.commitments = [None; PARTICIPANTS];
                self.next_attempt = next;
                Ok(FairShuffleAttemptOutcome::Rejected)
            }
        }
    }

    /// Admit one card disclosure only after the accepted proof. Replay and
    /// every invalid path leave the reveal array unchanged.
    pub fn reveal_card(&mut self, opening: FairCardOpening) -> Result<u8, FairShuffleError> {
        let receipt = self
            .accepted_receipt
            .as_ref()
            .ok_or(FairShuffleError::DealNotAccepted)?;
        let seat = opening.seat as usize;
        if seat >= SEATS {
            return Err(FairShuffleError::SeatOutOfRange(seat));
        }
        if self.revealed_cards[seat].is_some() {
            return Err(FairShuffleError::OpeningReplay(seat));
        }
        proof::verify_deal_opening(receipt.statement, &opening.proof_opening())
            .map_err(FairShuffleError::InvalidOpening)?;
        self.revealed_cards[seat] = Some(opening.card);
        Ok(opening.card)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FairShuffleError {
    InvalidPrivateInput(String),
    InvalidStatement(String),
    InvalidProof(String),
    InvalidOpening(String),
    InvalidCommitment(String),
    WireFormat(String),
    VerifierMismatch,
    SessionMismatch { expected: u32, claimed: u32 },
    AttemptMismatch { expected: u32, claimed: u32 },
    ParticipantOutOfRange(usize),
    SeatOutOfRange(usize),
    DuplicateCommitment(usize),
    CommitmentsIncomplete,
    CommitmentLeafMismatch(usize),
    CommitmentRootMismatch,
    DealNotAccepted,
    OpeningReplay(usize),
    RoundClosed,
}

impl std::fmt::Display for FairShuffleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPrivateInput(reason) => {
                write!(f, "private fair-shuffle input refused: {reason}")
            }
            Self::InvalidStatement(reason) => write!(f, "fair-shuffle statement refused: {reason}"),
            Self::InvalidProof(reason) => write!(f, "fair-shuffle proof refused: {reason}"),
            Self::InvalidOpening(reason) => write!(f, "fair-shuffle opening refused: {reason}"),
            Self::InvalidCommitment(reason) => {
                write!(f, "fair-shuffle commitment refused: {reason}")
            }
            Self::WireFormat(reason) => write!(f, "fair-shuffle transport refused: {reason}"),
            Self::VerifierMismatch => write!(f, "fair-shuffle verifier identity mismatch"),
            Self::SessionMismatch { expected, claimed } => write!(
                f,
                "fair-shuffle session mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::AttemptMismatch { expected, claimed } => write!(
                f,
                "fair-shuffle attempt mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::ParticipantOutOfRange(participant) => write!(
                f,
                "participant {participant} is outside fixed range 0..{}",
                PARTICIPANTS - 1
            ),
            Self::SeatOutOfRange(seat) => {
                write!(f, "seat {seat} is outside fixed range 0..{}", SEATS - 1)
            }
            Self::DuplicateCommitment(participant) => write!(
                f,
                "participant {participant} already committed for this attempt"
            ),
            Self::CommitmentsIncomplete => write!(
                f,
                "all participant commitments must land before proof acceptance"
            ),
            Self::CommitmentLeafMismatch(participant) => write!(
                f,
                "recorded commitment for participant {participant} does not match the private contribution"
            ),
            Self::CommitmentRootMismatch => write!(
                f,
                "recorded participant commitments do not reconstruct the proved root"
            ),
            Self::DealNotAccepted => {
                write!(f, "card opening cannot land before an accepted fair deal")
            }
            Self::OpeningReplay(seat) => write!(f, "seat {seat} card was already revealed"),
            Self::RoundClosed => write!(f, "fair-shuffle round is closed"),
        }
    }
}

impl std::error::Error for FairShuffleError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn commit_all(table: &mut FairShuffleTable, prepared: &PreparedFairShuffle) {
        for participant in 0..PARTICIPANTS {
            table
                .commit(
                    participant,
                    prepared.participant_commitment(participant).unwrap(),
                )
                .unwrap();
        }
    }

    #[test]
    fn accepted_deal_enforces_commit_before_proof_and_selective_reveal() {
        let prepared = PreparedFairShuffle::fresh(707, 0, [12_345, 1, 2, 3, 4, 5, 6, 7]).unwrap();
        let mut producer_table = FairShuffleTable::new(707).unwrap();
        assert!(matches!(
            prepared.prove_receipt(&producer_table),
            Err(FairShuffleError::CommitmentsIncomplete)
        ));
        commit_all(&mut producer_table, &prepared);
        let receipt = prepared.prove_receipt(&producer_table).unwrap();
        assert!(receipt.statement().accepted);
        let restored = FairShuffleReceipt::from_postcard(&receipt.to_postcard().unwrap()).unwrap();
        assert_eq!(restored, receipt);

        let mut table = FairShuffleTable::new(707).unwrap();
        for participant in 0..PARTICIPANTS - 1 {
            table
                .commit(
                    participant,
                    prepared.participant_commitment(participant).unwrap(),
                )
                .unwrap();
        }
        let before_incomplete = table.clone();
        assert!(matches!(
            table.accept_attempt(&restored),
            Err(FairShuffleError::CommitmentsIncomplete)
        ));
        assert_eq!(table, before_incomplete);

        table
            .commit(
                PARTICIPANTS - 1,
                prepared.participant_commitment(PARTICIPANTS - 1).unwrap(),
            )
            .unwrap();
        assert_eq!(
            table.accept_attempt(&restored).unwrap(),
            FairShuffleAttemptOutcome::Accepted
        );

        let opening = prepared.card_opening(6).unwrap();
        let opening = FairCardOpening::from_postcard(&opening.to_postcard().unwrap()).unwrap();
        let expected_card = opening.card;
        assert_eq!(table.reveal_card(opening).unwrap(), expected_card);
        assert_eq!(table.revealed_cards()[6], Some(expected_card));

        let landed = table.clone();
        assert!(matches!(
            table.reveal_card(opening),
            Err(FairShuffleError::OpeningReplay(6))
        ));
        assert_eq!(table, landed);
        assert!(matches!(
            table.accept_attempt(&restored),
            Err(FairShuffleError::RoundClosed)
        ));
        assert_eq!(table, landed);
    }

    #[test]
    fn rejected_attempt_is_recorded_before_bias_free_retry() {
        let rejected = PreparedFairShuffle::fresh(808, 0, [40_320, 0, 0, 0, 0, 0, 0, 0]).unwrap();
        let mut table = FairShuffleTable::new(808).unwrap();
        commit_all(&mut table, &rejected);
        let rejected_receipt = rejected.prove_receipt(&table).unwrap();
        assert!(!rejected_receipt.statement().accepted);
        assert_eq!(
            table.accept_attempt(&rejected_receipt).unwrap(),
            FairShuffleAttemptOutcome::Rejected
        );
        assert_eq!(table.rejected_receipts(), &[rejected_receipt.clone()]);
        assert_eq!(table.next_attempt(), Some(1));
        assert!(table.commitments().iter().all(Option::is_none));
        assert!(matches!(
            table.accept_attempt(&rejected_receipt),
            Err(FairShuffleError::AttemptMismatch { .. })
        ));

        let accepted = PreparedFairShuffle::fresh(808, 1, [9_999, 1, 2, 3, 4, 5, 6, 7]).unwrap();
        commit_all(&mut table, &accepted);
        let accepted_receipt = accepted.prove_receipt(&table).unwrap();
        assert_eq!(
            table.accept_attempt(&accepted_receipt).unwrap(),
            FairShuffleAttemptOutcome::Accepted
        );
        assert_eq!(table.rejected_receipts().len(), 1);
        assert!(table.accepted_receipt().is_some());
    }

    #[test]
    fn transport_root_proof_and_opening_tampers_refuse_atomically() {
        let prepared = PreparedFairShuffle::fresh(909, 0, [456, 1, 2, 3, 4, 5, 6, 7]).unwrap();
        let mut table = FairShuffleTable::new(909).unwrap();
        commit_all(&mut table, &prepared);
        let receipt = prepared.prove_receipt(&table).unwrap();
        let honest_wire = receipt.to_wire();

        let mut wrong_vk = honest_wire.clone();
        wrong_vk.verifier_key[0] ^= 1;
        assert!(matches!(
            wrong_vk.into_receipt(),
            Err(FairShuffleError::VerifierMismatch)
        ));

        let mut wrong_root = honest_wire.clone();
        wrong_root.public_inputs[3] ^= 1;
        let wrong_root = wrong_root.into_receipt().unwrap();
        let before = table.clone();
        assert!(matches!(
            table.accept_attempt(&wrong_root),
            Err(FairShuffleError::CommitmentRootMismatch)
        ));
        assert_eq!(table, before);

        let mut wrong_proof = honest_wire;
        let at = wrong_proof.proof_bytes.len() / 2;
        wrong_proof.proof_bytes[at] ^= 1;
        let wrong_proof = wrong_proof.into_receipt().unwrap();
        assert!(matches!(
            table.accept_attempt(&wrong_proof),
            Err(FairShuffleError::InvalidProof(_))
        ));
        assert_eq!(table, before);

        table.accept_attempt(&receipt).unwrap();
        let mut opening = prepared.card_opening(2).unwrap();
        opening.siblings[1][3] ^= 1;
        let before_opening = table.clone();
        assert!(matches!(
            table.reveal_card(opening),
            Err(FairShuffleError::InvalidOpening(_))
        ));
        assert_eq!(table, before_opening);
    }
}
