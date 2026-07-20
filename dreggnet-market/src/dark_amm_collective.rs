//! Public-only, two-phase collective Dark AMM session.
//!
//! Phase one accepts the existing strict-v3 request, but reconstructs its
//! Tier-1 same-opening claim under the configured *collective* DKG identity
//! instead of the single-host `n=1` identity used by `dark_amm_game`. It checks
//! the same-opening replay slot without consuming it and stages exactly one
//! ciphertext-bound candidate. Phase two re-verifies and atomically consumes
//! both same-opening and FHDAR replay slots while advancing encrypted host
//! material, the HidingFri root, and sequence.
//!
//! This module imports no BFV secret key, decryption share, or plaintext reserve
//! opening. Initial public host material still needs creation evidence: matching
//! the embedded public key to the configured collective key does not prove that
//! its relinearization key and initial reserve ciphertexts were honestly
//! generated. Tier-1 issuers also see the private HidingFri/BFV openings; this
//! module verifies their authenticated receipt and does not rename it as ZK.

use std::fmt;

use dregg_circuit_prove::dark_amm_private::RULE_ID as PRIVATE_AMM_RULE_ID;
use fhe_traits::Serialize as FheSerialize;
use fhegg_fhe::amm_same_opening::{
    AmmPrivacyTier, AmmSameOpeningContext, canonical_bfv_parameters_digest,
};
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityVerifier, ReplayGuard, SnapshotReplayGuard,
};
use fhegg_fhe::dark_amm::{
    DarkPool, DarkPoolPublicHostMaterial, MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES,
};
use fhegg_fhe::dark_amm_attested::{
    AttestedPrivateDecisionPolicy, commit_attested_private_decision,
};
use fhegg_fhe::decision_attestation::AttestedDecisionReceipt;
use fhegg_fhe::mpc_party::DecisionTranscript;
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, KeygenSession};

use crate::dark_amm_game::{
    DarkAmmPublicSession, MAX_DARK_AMM_REQUEST_BYTES, SameOpeningProvedEncryptedSwapRequest,
};

const CHECKPOINT_MAGIC: &[u8; 8] = b"DBACv001";
const CHECKPOINT_DOMAIN: &str = "dregg-dark-amm-collective-checkpoint-v1";
const REPLAY_CONTEXT_DOMAIN: &str = "dregg-dark-amm-collective-replay-context-v2";
const BABYBEAR_P: u32 = 2_013_265_921;
const MAX_REPLAY_WIRE_BYTES: usize = 40 * 1024 * 1024;
const MAX_CHECKPOINT_BYTES: usize = MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES
    + MAX_DARK_AMM_REQUEST_BYTES
    + 2 * MAX_REPLAY_WIRE_BYTES
    + 1024;

/// Stable refusal surface for the public-only collective session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveDarkAmmError {
    Malformed(String),
    Configuration(String),
    Refused(String),
    PendingCandidateExists,
    NoPendingCandidate,
    SequenceExhausted,
}

impl fmt::Display for CollectiveDarkAmmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(reason) => write!(f, "malformed collective Dark AMM state: {reason}"),
            Self::Configuration(reason) => {
                write!(f, "invalid collective Dark AMM configuration: {reason}")
            }
            Self::Refused(reason) => write!(f, "collective Dark AMM request refused: {reason}"),
            Self::PendingCandidateExists => write!(f, "one encrypted candidate is already pending"),
            Self::NoPendingCandidate => write!(f, "no encrypted candidate is pending"),
            Self::SequenceExhausted => write!(f, "collective Dark AMM sequence is exhausted"),
        }
    }
}

impl std::error::Error for CollectiveDarkAmmError {}

/// Exact public relying-party configuration. The same-opening authority and
/// FHDAR decision verifier are independent policies even when a deployment
/// intentionally gives them overlapping rosters.
pub struct CollectiveDarkAmmConfig {
    hosted_session: [u8; 32],
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    same_opening_verifier: AuthenticatedQuorumVerifier,
    decision_policy: AttestedPrivateDecisionPolicy,
    same_opening_replay_context: [u8; 32],
    decision_replay_context: [u8; 32],
}

impl CollectiveDarkAmmConfig {
    pub fn new(
        hosted_session: [u8; 32],
        params: BfvParams,
        keygen: KeygenSession,
        collective: CollectivePublicKey,
        same_opening_verifier: AuthenticatedQuorumVerifier,
        decision_policy: AttestedPrivateDecisionPolicy,
    ) -> Result<Self, CollectiveDarkAmmError> {
        if hosted_session == [0; 32] {
            return Err(CollectiveDarkAmmError::Configuration(
                "hosted session must be nonzero".to_string(),
            ));
        }
        if keygen.n_parties() != decision_policy.n_parties() {
            return Err(CollectiveDarkAmmError::Configuration(format!(
                "DKG has {} parties but the decision circuit policy has {}",
                keygen.n_parties(),
                decision_policy.n_parties()
            )));
        }
        if params.plaintext_modulus() != decision_policy.plaintext_modulus() {
            return Err(CollectiveDarkAmmError::Configuration(
                "decision policy names a different BFV plaintext modulus".to_string(),
            ));
        }
        let collective_identity_digest = collective_identity_digest(&params, &keygen, &collective);
        let same_opening_replay_context = replay_context(
            b"same-opening",
            &hosted_session,
            &same_opening_verifier.verifier_id(),
            &collective_identity_digest,
        );
        let decision_replay_context = replay_context(
            b"fhdar-decision",
            &hosted_session,
            &decision_policy.verifier().verifier_id(),
            &collective_identity_digest,
        );
        Ok(Self {
            hosted_session,
            params,
            keygen,
            collective,
            same_opening_verifier,
            decision_policy,
            same_opening_replay_context,
            decision_replay_context,
        })
    }

    pub const fn hosted_session(&self) -> [u8; 32] {
        self.hosted_session
    }

    pub fn params(&self) -> &BfvParams {
        &self.params
    }

    pub fn keygen(&self) -> &KeygenSession {
        &self.keygen
    }

    pub fn collective(&self) -> &CollectivePublicKey {
        &self.collective
    }

    pub fn same_opening_verifier(&self) -> &AuthenticatedQuorumVerifier {
        &self.same_opening_verifier
    }

    pub fn decision_policy(&self) -> &AttestedPrivateDecisionPolicy {
        &self.decision_policy
    }

    fn public_key_digest(&self) -> [u8; 32] {
        *blake3::hash(&self.collective.pk.to_bytes()).as_bytes()
    }

    fn validate_material(
        &self,
        material: &DarkPoolPublicHostMaterial,
    ) -> Result<(), CollectiveDarkAmmError> {
        DarkPool::restore_public_host(self.params.arc(), material)
            .map_err(|error| CollectiveDarkAmmError::Configuration(error.to_string()))?;
        if material.public_key_bytes() != self.collective.pk.to_bytes() {
            return Err(CollectiveDarkAmmError::Configuration(
                "public host material is not under the configured collective key".to_string(),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PendingCandidate {
    request_wire: Vec<u8>,
    same_opening_claim_digest: [u8; 32],
    candidate_nonce: [u8; 32],
}

/// Public result of phase one. It names the candidate without carrying a
/// ciphertext, witness, reserve, or amount opening.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StagedCollectiveSwap {
    pub sequence: u64,
    pub new_root: [u32; 8],
    pub same_opening_claim_digest: [u8; 32],
    pub candidate_nonce: [u8; 32],
}

/// Public result of the atomic FHDAR commit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommittedCollectiveSwap {
    pub committed_sequence: u64,
    pub next_sequence: u64,
    pub new_root: [u32; 8],
    pub public_host_material_digest: [u8; 32],
    /// Tier-1 authority claim that bound HidingFri and BFV openings.
    pub same_opening_claim_digest: [u8; 32],
    /// Independent FHDAR authority claim that accepted the candidate.
    pub decision_claim_digest: [u8; 32],
}

/// Secretless host state. The optional pending carrier contains only the
/// canonical v3 request and public digests/nonces needed to reconstruct it.
pub struct CollectiveDarkAmmSession {
    config: CollectiveDarkAmmConfig,
    public_host_material: DarkPoolPublicHostMaterial,
    current_root: [u32; 8],
    next_sequence: u64,
    same_opening_replay: SnapshotReplayGuard,
    decision_replay: SnapshotReplayGuard,
    pending: Option<PendingCandidate>,
}

impl CollectiveDarkAmmSession {
    pub fn new(
        config: CollectiveDarkAmmConfig,
        public_host_material: DarkPoolPublicHostMaterial,
        current_root: [u32; 8],
        next_sequence: u64,
    ) -> Result<Self, CollectiveDarkAmmError> {
        validate_root(current_root)?;
        config.validate_material(&public_host_material)?;
        let same_opening_replay = SnapshotReplayGuard::new(config.same_opening_replay_context);
        let decision_replay = SnapshotReplayGuard::new(config.decision_replay_context);
        let session = Self {
            config,
            public_host_material,
            current_root,
            next_sequence,
            same_opening_replay,
            decision_replay,
            pending: None,
        };
        session.public_session()?;
        Ok(session)
    }

    pub const fn current_root(&self) -> [u32; 8] {
        self.current_root
    }

    pub const fn next_sequence(&self) -> u64 {
        self.next_sequence
    }

    pub fn has_pending_candidate(&self) -> bool {
        self.pending.is_some()
    }

    pub fn same_opening_replay_revision(&self) -> u64 {
        self.same_opening_replay.revision()
    }

    pub fn decision_replay_revision(&self) -> u64 {
        self.decision_replay.revision()
    }

    pub fn public_host_material(&self) -> &DarkPoolPublicHostMaterial {
        &self.public_host_material
    }

    /// Deliberately abandon a staged candidate. Phase one has not consumed the
    /// same-opening replay slot, so the request or a same-sequence replacement
    /// may be staged after restart. All committed pool/root/sequence and both
    /// replay guards remain untouched.
    pub fn abandon_pending(&mut self) -> Result<StagedCollectiveSwap, CollectiveDarkAmmError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or(CollectiveDarkAmmError::NoPendingCandidate)?;
        let request = decode_request(&pending.request_wire)?;
        let abandoned = StagedCollectiveSwap {
            sequence: self.next_sequence,
            new_root: request.proved_request().statement().new_root,
            same_opening_claim_digest: pending.same_opening_claim_digest,
            candidate_nonce: pending.candidate_nonce,
        };
        self.pending = None;
        Ok(abandoned)
    }

    /// Producer view for the current root/sequence under the real collective
    /// key and public DKG identity.
    pub fn public_session(&self) -> Result<DarkAmmPublicSession, CollectiveDarkAmmError> {
        DarkAmmPublicSession::try_from_collective(
            self.config.hosted_session,
            &self.config.params,
            &self.config.keygen,
            &self.config.collective,
            self.public_host_material.k(),
            self.public_host_material.cap_x(),
            self.public_host_material.cap_y(),
            self.next_sequence,
            self.current_root,
        )
        .map_err(|error| CollectiveDarkAmmError::Configuration(error.to_string()))
    }

    /// Phase one: fully verify the collective Tier-1 receipt and stage exactly
    /// one encrypted candidate. No pool/root/sequence mutation occurs here.
    pub fn stage_same_opening_request(
        &mut self,
        request_wire: &[u8],
    ) -> Result<StagedCollectiveSwap, CollectiveDarkAmmError> {
        if self.pending.is_some() {
            return Err(CollectiveDarkAmmError::PendingCandidateExists);
        }
        let request = decode_request(request_wire)?;
        let mut replay_probe = self.same_opening_replay.clone();
        let (candidate_nonce, claim_digest) =
            self.verify_and_reconstruct(&request, &mut replay_probe)?;
        let staged = StagedCollectiveSwap {
            sequence: self.next_sequence,
            new_root: request.proved_request().statement().new_root,
            same_opening_claim_digest: claim_digest,
            candidate_nonce,
        };
        self.pending = Some(PendingCandidate {
            request_wire: request_wire.to_vec(),
            same_opening_claim_digest: claim_digest,
            candidate_nonce,
        });
        Ok(staged)
    }

    /// Phase two: verify an independently configured FHDAR decision against a
    /// freshly reconstructed candidate and commit into a detached pool. Every
    /// fallible step finishes before the authoritative fields are replaced.
    pub fn commit_attested_decision(
        &mut self,
        transcript: &DecisionTranscript,
        receipt: &AttestedDecisionReceipt,
    ) -> Result<CommittedCollectiveSwap, CollectiveDarkAmmError> {
        let pending = self
            .pending
            .as_ref()
            .ok_or(CollectiveDarkAmmError::NoPendingCandidate)?;
        let request = decode_request(&pending.request_wire)?;
        self.validate_request_bindings(&request)?;
        let mut staged_same_opening_replay = self.same_opening_replay.clone();
        let (reverified_nonce, reverified_claim_digest) =
            self.verify_and_reconstruct(&request, &mut staged_same_opening_replay)?;
        if reverified_nonce != pending.candidate_nonce
            || reverified_claim_digest != pending.same_opening_claim_digest
        {
            return Err(CollectiveDarkAmmError::Refused(
                "pending candidate no longer matches its Tier-1 authority claim".to_string(),
            ));
        }
        let (dx, dy) = request
            .proved_request()
            .bounded_ciphertexts(self.config.params.arc())
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let mut detached_pool =
            DarkPool::restore_public_host(self.config.params.arc(), &self.public_host_material)
                .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let candidate = detached_pool
            .try_private_swap_proposed(&dx, &dy)
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        if candidate.decision_session_nonce() != pending.candidate_nonce {
            return Err(CollectiveDarkAmmError::Refused(
                "pending candidate no longer reconstructs against the committed pre-state"
                    .to_string(),
            ));
        }
        let mut staged_replay = self.decision_replay.clone();
        commit_attested_private_decision(
            &mut detached_pool,
            &candidate,
            &self.config.decision_policy,
            transcript,
            receipt,
            &mut staged_replay,
        )
        .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let next_material = detached_pool
            .public_host_material()
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let committed_sequence = self.next_sequence;
        let next_sequence = committed_sequence
            .checked_add(1)
            .ok_or(CollectiveDarkAmmError::SequenceExhausted)?;
        let new_root = request.proved_request().statement().new_root;
        let public_host_material_digest = next_material.material_digest();
        let same_opening_claim_digest = pending.same_opening_claim_digest;
        let decision_claim_digest = receipt.claim_digest();

        // Atomic authoritative replacement: all parsing, FHE, FHDAR, replay,
        // serialization, and sequence checks above operated on detached state.
        self.public_host_material = next_material;
        self.current_root = new_root;
        self.next_sequence = next_sequence;
        self.same_opening_replay = staged_same_opening_replay;
        self.decision_replay = staged_replay;
        self.pending = None;

        Ok(CommittedCollectiveSwap {
            committed_sequence,
            next_sequence,
            new_root,
            public_host_material_digest,
            same_opening_claim_digest,
            decision_claim_digest,
        })
    }

    /// Strict public restart carrier. Persist this in the same transaction as
    /// an accepted stage or commit. Its checksum detects corruption, not
    /// rollback; production storage still needs a monotonic/consensus anchor.
    pub fn checkpoint_wire_bytes(&self) -> Vec<u8> {
        let material = self.public_host_material.to_wire_bytes();
        let same_replay = self.same_opening_replay.to_wire_bytes();
        let decision_replay = self.decision_replay.to_wire_bytes();
        let mut out = Vec::new();
        out.extend_from_slice(CHECKPOINT_MAGIC);
        out.extend_from_slice(&self.config.hosted_session);
        for lane in self.current_root {
            out.extend_from_slice(&lane.to_le_bytes());
        }
        put_u64(&mut out, self.next_sequence);
        put_bytes(&mut out, &material);
        put_bytes(&mut out, &same_replay);
        put_bytes(&mut out, &decision_replay);
        match &self.pending {
            None => out.push(0),
            Some(pending) => {
                out.push(1);
                put_bytes(&mut out, &pending.request_wire);
                out.extend_from_slice(&pending.same_opening_claim_digest);
                out.extend_from_slice(&pending.candidate_nonce);
            }
        }
        let checksum = checkpoint_checksum(&out);
        out.extend_from_slice(&checksum);
        out
    }

    /// Restore committed material, both replay sets, and—when present—the
    /// strict public pending carrier. Pending restoration re-verifies the full
    /// proof/signatures against a clone of the durable replay guard and thus
    /// requires its sequence slot to remain fresh until phase two commits.
    pub fn restore_from_checkpoint(
        config: CollectiveDarkAmmConfig,
        bytes: &[u8],
    ) -> Result<Self, CollectiveDarkAmmError> {
        let decoded = DecodedCheckpoint::parse(bytes)?;
        if decoded.hosted_session != config.hosted_session {
            return Err(CollectiveDarkAmmError::Configuration(
                "checkpoint names a different hosted session".to_string(),
            ));
        }
        validate_root(decoded.current_root)?;
        let material =
            DarkPoolPublicHostMaterial::from_wire_bytes(decoded.material_wire, config.params.arc())
                .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        config.validate_material(&material)?;
        let same_opening_replay = SnapshotReplayGuard::from_wire_bytes(
            config.same_opening_replay_context,
            decoded.same_opening_replay_wire,
        )
        .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let decision_replay = SnapshotReplayGuard::from_wire_bytes(
            config.decision_replay_context,
            decoded.decision_replay_wire,
        )
        .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
        let pending = decoded.pending.map(|pending| PendingCandidate {
            request_wire: pending.request_wire.to_vec(),
            same_opening_claim_digest: pending.same_opening_claim_digest,
            candidate_nonce: pending.candidate_nonce,
        });
        let session = Self {
            config,
            public_host_material: material,
            current_root: decoded.current_root,
            next_sequence: decoded.next_sequence,
            same_opening_replay,
            decision_replay,
            pending,
        };
        session.public_session()?;
        if let Some(pending) = &session.pending {
            let request = decode_request(&pending.request_wire)?;
            let mut replay_probe = session.same_opening_replay.clone();
            let (candidate_nonce, claim_digest) =
                session.verify_and_reconstruct(&request, &mut replay_probe)?;
            if candidate_nonce != pending.candidate_nonce
                || claim_digest != pending.same_opening_claim_digest
            {
                return Err(CollectiveDarkAmmError::Malformed(
                    "pending carrier digests do not reconstruct".to_string(),
                ));
            }
        }
        if session.checkpoint_wire_bytes() != bytes {
            return Err(CollectiveDarkAmmError::Malformed(
                "checkpoint is not canonically encoded".to_string(),
            ));
        }
        Ok(session)
    }

    fn verify_and_reconstruct<R: ReplayGuard>(
        &self,
        request: &SameOpeningProvedEncryptedSwapRequest,
        replay: &mut R,
    ) -> Result<([u8; 32], [u8; 32]), CollectiveDarkAmmError> {
        self.validate_request_bindings(request)?;
        let proved = request.proved_request();
        let (dx, dy) = proved
            .bounded_ciphertexts(self.config.params.arc())
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let proof = proved
            .decoded_private_amm_proof()
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let context = AmmSameOpeningContext {
            privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
            hosted_session: self.config.hosted_session,
            sequence: self.next_sequence,
            dx_bound: proved.dx_bound(),
            dy_bound: proved.dy_bound(),
            params: &self.config.params,
            keygen: &self.config.keygen,
            collective: &self.config.collective,
            dx_ciphertext: &dx.ct,
            dy_ciphertext: &dy.ct,
            proof: &proof,
            statement: proved.statement(),
        };
        let verified = request
            .same_opening_receipt()
            .verify(&context, &self.config.same_opening_verifier, replay)
            .map_err(|error| {
                CollectiveDarkAmmError::Refused(format!(
                    "collective Tier-1 same-opening verification failed: {error}"
                ))
            })?;
        let pool =
            DarkPool::restore_public_host(self.config.params.arc(), &self.public_host_material)
                .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        let candidate = pool
            .try_private_swap_proposed(&dx, &dy)
            .map_err(|error| CollectiveDarkAmmError::Refused(error.to_string()))?;
        Ok((candidate.decision_session_nonce(), verified.claim_digest()))
    }

    fn validate_request_bindings(
        &self,
        request: &SameOpeningProvedEncryptedSwapRequest,
    ) -> Result<(), CollectiveDarkAmmError> {
        let proved = request.proved_request();
        if proved.hosted_session() != self.config.hosted_session {
            return Err(CollectiveDarkAmmError::Refused(
                "request names a different hosted session".to_string(),
            ));
        }
        if proved.public_key_digest() != self.config.public_key_digest() {
            return Err(CollectiveDarkAmmError::Refused(
                "request names a different collective public key".to_string(),
            ));
        }
        if proved.sequence() != self.next_sequence {
            return Err(CollectiveDarkAmmError::Refused(format!(
                "request sequence {} is stale or skipped; expected {}",
                proved.sequence(),
                self.next_sequence
            )));
        }
        let statement = proved.statement();
        let public = self.public_session()?;
        let proof_context = public.proof_context().ok_or_else(|| {
            CollectiveDarkAmmError::Configuration(
                "collective public session unexpectedly lacks a proof context".to_string(),
            )
        })?;
        if statement.session != proof_context.receipt_session()
            || statement.rule != proof_context.rule()
            || statement.rule != PRIVATE_AMM_RULE_ID
            || u64::from(statement.k) != self.public_host_material.k()
            || statement.old_root != self.current_root
        {
            return Err(CollectiveDarkAmmError::Refused(
                "HidingFri statement does not name the exact session/rule/k/current root"
                    .to_string(),
            ));
        }
        validate_root(statement.new_root)?;
        Ok(())
    }
}

fn decode_request(
    bytes: &[u8],
) -> Result<SameOpeningProvedEncryptedSwapRequest, CollectiveDarkAmmError> {
    let request = SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(bytes)
        .map_err(|error| CollectiveDarkAmmError::Malformed(error.to_string()))?;
    if request.to_wire_bytes() != bytes {
        return Err(CollectiveDarkAmmError::Malformed(
            "strict-v3 request is not canonical".to_string(),
        ));
    }
    Ok(request)
}

fn validate_root(root: [u32; 8]) -> Result<(), CollectiveDarkAmmError> {
    if root.iter().any(|lane| *lane >= BABYBEAR_P) {
        return Err(CollectiveDarkAmmError::Configuration(
            "HidingFri root contains a noncanonical BabyBear element".to_string(),
        ));
    }
    Ok(())
}

fn replay_context(
    lane: &[u8],
    hosted_session: &[u8; 32],
    verifier_id: &[u8; 32],
    collective_identity_digest: &[u8; 32],
) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(REPLAY_CONTEXT_DOMAIN);
    hash.update(&(lane.len() as u64).to_le_bytes());
    hash.update(lane);
    hash.update(hosted_session);
    hash.update(verifier_id);
    hash.update(collective_identity_digest);
    *hash.finalize().as_bytes()
}

fn collective_identity_digest(
    params: &BfvParams,
    keygen: &KeygenSession,
    collective: &CollectivePublicKey,
) -> [u8; 32] {
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-dark-amm-collective-bfv-public-identity-v2");
    hash.update(&canonical_bfv_parameters_digest(params.arc()));
    hash.update(&(keygen.n_parties() as u64).to_le_bytes());
    hash.update(&keygen.crp_seed());
    let public_key = collective.pk.to_bytes();
    hash.update(&(public_key.len() as u64).to_le_bytes());
    hash.update(&public_key);
    *hash.finalize().as_bytes()
}

fn checkpoint_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(CHECKPOINT_DOMAIN);
    hash.update(&(content.len() as u64).to_le_bytes());
    hash.update(content);
    *hash.finalize().as_bytes()
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_u64(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

struct PendingRef<'a> {
    request_wire: &'a [u8],
    same_opening_claim_digest: [u8; 32],
    candidate_nonce: [u8; 32],
}

struct DecodedCheckpoint<'a> {
    hosted_session: [u8; 32],
    current_root: [u32; 8],
    next_sequence: u64,
    material_wire: &'a [u8],
    same_opening_replay_wire: &'a [u8],
    decision_replay_wire: &'a [u8],
    pending: Option<PendingRef<'a>>,
}

impl<'a> DecodedCheckpoint<'a> {
    fn parse(bytes: &'a [u8]) -> Result<Self, CollectiveDarkAmmError> {
        if bytes.len() > MAX_CHECKPOINT_BYTES || bytes.len() < 8 + 32 + 32 + 8 + 3 * 8 + 1 + 32 {
            return Err(CollectiveDarkAmmError::Malformed(
                "checkpoint size is outside fixed bounds".to_string(),
            ));
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != checkpoint_checksum(&bytes[..content_end]) {
            return Err(CollectiveDarkAmmError::Malformed(
                "checkpoint checksum mismatch".to_string(),
            ));
        }
        let mut reader = CheckpointReader::new(&bytes[..content_end]);
        if reader.array::<8>()? != *CHECKPOINT_MAGIC {
            return Err(CollectiveDarkAmmError::Malformed(
                "wrong checkpoint version".to_string(),
            ));
        }
        let hosted_session = reader.array()?;
        let mut current_root = [0u32; 8];
        for lane in &mut current_root {
            *lane = u32::from_le_bytes(reader.array()?);
        }
        let next_sequence = reader.u64()?;
        let material_wire = reader.bytes(MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES)?;
        let same_opening_replay_wire = reader.bytes(MAX_REPLAY_WIRE_BYTES)?;
        let decision_replay_wire = reader.bytes(MAX_REPLAY_WIRE_BYTES)?;
        let pending = match reader.byte()? {
            0 => None,
            1 => Some(PendingRef {
                request_wire: reader.bytes(MAX_DARK_AMM_REQUEST_BYTES)?,
                same_opening_claim_digest: reader.array()?,
                candidate_nonce: reader.array()?,
            }),
            other => {
                return Err(CollectiveDarkAmmError::Malformed(format!(
                    "unknown pending tag {other}"
                )));
            }
        };
        reader.finish()?;
        Ok(Self {
            hosted_session,
            current_root,
            next_sequence,
            material_wire,
            same_opening_replay_wire,
            decision_replay_wire,
            pending,
        })
    }
}

struct CheckpointReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CheckpointReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], CollectiveDarkAmmError> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| CollectiveDarkAmmError::Malformed("truncated checkpoint".to_string()))?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| CollectiveDarkAmmError::Malformed("invalid fixed field".to_string()))?;
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, CollectiveDarkAmmError> {
        Ok(self.array::<1>()?[0])
    }

    fn u64(&mut self) -> Result<u64, CollectiveDarkAmmError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], CollectiveDarkAmmError> {
        let len = usize::try_from(self.u64()?).map_err(|_| {
            CollectiveDarkAmmError::Malformed("checkpoint length overflow".to_string())
        })?;
        if len > max {
            return Err(CollectiveDarkAmmError::Malformed(format!(
                "checkpoint field length {len} exceeds maximum {max}"
            )));
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| CollectiveDarkAmmError::Malformed("truncated checkpoint".to_string()))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> Result<(), CollectiveDarkAmmError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(CollectiveDarkAmmError::Malformed(
                "trailing checkpoint bytes".to_string(),
            ))
        }
    }
}
