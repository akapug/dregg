//! Tier-1 exact-opening authority for the private Dark AMM.
//!
//! The HidingFri proof hides its AMM witness from proof consumers, while BFV
//! keeps `dx` and `dy` encrypted from the host that evaluates the transition.
//! Those facts do not, by themselves, prove that both representations contain
//! the same amounts.  This module supplies an explicit intermediate authority:
//! each configured issuer sees `x/y/dx/dy`, both commitment blinds, and the BFV
//! encryption seeds; deterministically re-encrypts `dx` and `dy` under the exact
//! collective public key; reconstructs the exact Lean-authored private-AMM
//! statement from that same witness; verifies the supplied HidingFri proof; and
//! only then signs one canonical cross-representation claim.
//!
//! A receipt binds the complete BFV public identity, exact ciphertext digests,
//! the two public no-wrap amount caps, HidingFri statement/proof/descriptor
//! digests, hosted session, proof session, roots, invariant `k`, sequence,
//! declared privacy tier, and threshold issuer roster. Issuers additionally
//! refuse a cap below its opening or outside `0 < bound < plaintext_modulus`.
//! Verification reconstructs that claim from independently supplied objects,
//! verifies threshold Ed25519 evidence and the proof again, then burns the
//! hosted `(session, sequence)` replay slot.
//!
//! # Exact trust statement
//!
//! This is authenticated Tier-1 same-opening, not lattice zero knowledge and
//! not no-viewer witness production. Every issuer asked to endorse learns the
//! full witness and both encryption seeds. Threshold evidence proves that the
//! configured issuer quorum endorsed the exact claim; it does not prove that a
//! malicious quorum ran this reference implementation. The deterministic seed
//! codec is pinned to fhe.rs 0.1.1 + `rand_09::rngs::StdRng`; changing either is
//! a protocol-version migration. The reference path refuses an all-zero seed
//! and cross-amount seed reuse, but cannot certify that caller-supplied seeds
//! had uniform entropy. Durable replay snapshots still require a
//! rollback-resistant transactional storage anchor.

use dregg_circuit_prove::dark_amm_private::{
    self, DarkAmmPrivateZkProof, PrivateAmmWitness, PublicStatement,
};
use ed25519_dalek::SigningKey;
use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;
use sha2::{Digest, Sha256};

use crate::attestation::{
    AuthenticatedQuorumVerifier, BfvPublicIdentity, ComputationIntegrityVerifier, Digest32,
    PartyClaimSignature, QuorumVerifierError, ReplayGuard,
};
use crate::threshold::{BfvParams, CollectivePublicKey, KeygenSession};

const CLAIM_MAGIC: &[u8; 8] = b"FHASO003";
const ENDORSEMENT_MAGIC: &[u8; 8] = b"FHASE003";
const RECEIPT_MAGIC: &[u8; 8] = b"FHASR003";
const PROTOCOL_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/tier1/v3";
const CLAIM_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/claim/v3";
const PARAMETERS_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/bfv-parameters/v3";
const CIPHERTEXT_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/bfv-ciphertext/v1";
const STATEMENT_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/hidingfri-statement/v1";
const PROOF_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/hidingfri-proof/v1";
const DESCRIPTOR_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/descriptor/v1";
const REPLAY_CONTEXT_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/replay-context/v1";
const REPLAY_SLOT_DOMAIN: &[u8] = b"fhegg/dark-amm/same-opening/replay-slot/v1";

pub const MAX_AUTHORITY_PARTIES: usize = 16;
pub const SAME_OPENING_CLAIM_WIRE_LEN: usize = 8
    + 1
    + 32
    + 8
    + (3 * 4)
    + (2 * 8)
    + (2 * 8 * 4)
    + (4 * 8)
    + (3 * 32)
    + 32
    + (5 * 32)
    + (2 * 32)
    + (2 * 4);
const SIGNATURE_RECORD_LEN: usize = 4 + 64;
pub const SAME_OPENING_ENDORSEMENT_WIRE_LEN: usize =
    8 + SAME_OPENING_CLAIM_WIRE_LEN + SIGNATURE_RECORD_LEN;

pub type Result<T> = std::result::Result<T, AmmSameOpeningError>;

/// Digest fhe.rs's complete canonical BFV parameter encoding. Unlike the
/// legacy evaluation identity `(degree, moduli, plaintext modulus)`, this also
/// binds the encryption error variance and any future serialized parameter.
pub fn canonical_bfv_parameters_digest(params: &BfvParameters) -> Digest32 {
    let bytes = params.to_bytes();
    domain_digest(PARAMETERS_DOMAIN, &[&bytes])
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AmmAmount {
    Dx,
    Dy,
}

/// The only privacy tier this authority is permitted to attest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum AmmPrivacyTier {
    /// Proof consumers do not see the witness, but each issuer does.
    Tier1IssuerVisible = 1,
}

impl AmmPrivacyTier {
    fn from_byte(value: u8) -> Result<Self> {
        match value {
            1 => Ok(Self::Tier1IssuerVisible),
            _ => Err(AmmSameOpeningError::MalformedWire),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AmmSameOpeningError {
    InvalidContext,
    InvalidEncryptionSeed { amount: AmmAmount },
    ReusedEncryptionSeed,
    InvalidAmountBound { amount: AmmAmount },
    WitnessOpeningMismatch { amount: AmmAmount },
    BfvReencryptionMismatch { amount: AmmAmount },
    BfvOperation { amount: AmmAmount },
    StatementMismatch,
    ProofRejected,
    ProofEncoding,
    BfvEncryption,
    BindingMismatch,
    AuthorityMismatch,
    EndorsementClaimMismatch,
    EmptyEndorsements,
    ReplayDetected,
    MalformedWire,
    NonCanonicalSignerOrder,
    Quorum(QuorumVerifierError),
}

impl std::fmt::Display for AmmSameOpeningError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for AmmSameOpeningError {}

impl From<QuorumVerifierError> for AmmSameOpeningError {
    fn from(value: QuorumVerifierError) -> Self {
        Self::Quorum(value)
    }
}

fn domain_digest(domain: &[u8], parts: &[&[u8]]) -> Digest32 {
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    for part in parts {
        hasher.update((part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn protocol_id() -> Digest32 {
    domain_digest(PROTOCOL_DOMAIN, &[b"fhe.rs-0.1.1", b"rand-0.9-StdRng"])
}

/// The operator-visible preimage of one exact BFV amount ciphertext.
///
/// It deliberately has no `Debug`, `Clone`, serialization, or seed accessor.
/// The authority consumes it by reference and retains only a ciphertext digest.
pub struct ExactBfvAmountOpening {
    value: u16,
    encryption_seed: [u8; 32],
}

impl ExactBfvAmountOpening {
    pub fn new(value: u16, encryption_seed: [u8; 32]) -> Self {
        Self {
            value,
            encryption_seed,
        }
    }

    pub fn value(&self) -> u16 {
        self.value
    }

    /// Deterministically construct the exact ciphertext the authority will
    /// later reproduce. The seed remains caller/issuer private.
    pub fn encrypt(
        &self,
        params: &BfvParams,
        collective: &CollectivePublicKey,
    ) -> Result<Ciphertext> {
        deterministic_encrypt(params, collective, self)
            .map_err(|_| AmmSameOpeningError::BfvEncryption)
    }
}

fn deterministic_encrypt(
    params: &BfvParams,
    collective: &CollectivePublicKey,
    opening: &ExactBfvAmountOpening,
) -> std::result::Result<Ciphertext, ()> {
    let plaintext =
        Plaintext::try_encode(&[u64::from(opening.value)], Encoding::simd(), params.arc())
            .map_err(|_| ())?;
    let mut rng = StdRng::from_seed(opening.encryption_seed);
    collective
        .pk
        .try_encrypt(&plaintext, &mut rng)
        .map_err(|_| ())
}

/// Independently supplied public objects from which every verifier rebuilds
/// the exact claim. References keep proof and ciphertext bodies outside the
/// retained receipt.
#[derive(Clone, Copy)]
pub struct AmmSameOpeningContext<'a> {
    pub privacy_tier: AmmPrivacyTier,
    pub hosted_session: Digest32,
    pub sequence: u64,
    /// Public BFV no-wrap cap used by the host evaluator for `dx`.
    pub dx_bound: u64,
    /// Public BFV no-wrap cap used by the host evaluator for `dy`.
    pub dy_bound: u64,
    pub params: &'a BfvParams,
    pub keygen: &'a KeygenSession,
    pub collective: &'a CollectivePublicKey,
    pub dx_ciphertext: &'a Ciphertext,
    pub dy_ciphertext: &'a Ciphertext,
    pub proof: &'a DarkAmmPrivateZkProof,
    pub statement: PublicStatement,
}

/// Fixed canonical public claim endorsed by the authority quorum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmmSameOpeningClaim {
    pub privacy_tier: AmmPrivacyTier,
    pub hosted_session: Digest32,
    pub sequence: u64,
    pub proof_session: u32,
    pub rule: u32,
    pub k: u32,
    pub dx_bound: u64,
    pub dy_bound: u64,
    pub old_root: [u32; 8],
    pub new_root: [u32; 8],
    pub bfv: BfvPublicIdentity,
    /// Complete canonical fhe.rs parameter identity, including error variance.
    pub parameter_digest: Digest32,
    pub dx_ciphertext_digest: Digest32,
    pub dy_ciphertext_digest: Digest32,
    pub hidingfri_statement_digest: Digest32,
    pub hidingfri_proof_digest: Digest32,
    pub descriptor_digest: Digest32,
    pub issuer_roster_digest: Digest32,
    pub issuer_verifier_id: Digest32,
    pub issuer_threshold: u32,
    pub issuer_roster_len: u32,
}

impl AmmSameOpeningClaim {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SAME_OPENING_CLAIM_WIRE_LEN);
        out.extend_from_slice(CLAIM_MAGIC);
        out.push(self.privacy_tier as u8);
        out.extend_from_slice(&self.hosted_session);
        out.extend_from_slice(&self.sequence.to_be_bytes());
        out.extend_from_slice(&self.proof_session.to_be_bytes());
        out.extend_from_slice(&self.rule.to_be_bytes());
        out.extend_from_slice(&self.k.to_be_bytes());
        out.extend_from_slice(&self.dx_bound.to_be_bytes());
        out.extend_from_slice(&self.dy_bound.to_be_bytes());
        for value in self.old_root.into_iter().chain(self.new_root) {
            out.extend_from_slice(&value.to_be_bytes());
        }
        out.extend_from_slice(&self.bfv.n_parties.to_be_bytes());
        out.extend_from_slice(&self.bfv.opening_threshold.to_be_bytes());
        out.extend_from_slice(&self.bfv.degree.to_be_bytes());
        out.extend_from_slice(&self.bfv.moduli_digest);
        out.extend_from_slice(&self.bfv.plaintext_modulus.to_be_bytes());
        out.extend_from_slice(&self.bfv.crp_seed);
        out.extend_from_slice(&self.bfv.collective_public_key_digest);
        out.extend_from_slice(&self.parameter_digest);
        for digest in [
            self.dx_ciphertext_digest,
            self.dy_ciphertext_digest,
            self.hidingfri_statement_digest,
            self.hidingfri_proof_digest,
            self.descriptor_digest,
            self.issuer_roster_digest,
            self.issuer_verifier_id,
        ] {
            out.extend_from_slice(&digest);
        }
        out.extend_from_slice(&self.issuer_threshold.to_be_bytes());
        out.extend_from_slice(&self.issuer_roster_len.to_be_bytes());
        debug_assert_eq!(out.len(), SAME_OPENING_CLAIM_WIRE_LEN);
        out
    }

    pub fn digest(&self) -> Digest32 {
        domain_digest(CLAIM_DOMAIN, &[&protocol_id(), &self.canonical_bytes()])
    }

    /// One replay slot per hosted transition, independent of which competing
    /// ciphertext/proof claim reaches verification first.
    pub fn replay_id(&self) -> Digest32 {
        domain_digest(
            REPLAY_SLOT_DOMAIN,
            &[
                &protocol_id(),
                &self.hosted_session,
                &self.sequence.to_be_bytes(),
            ],
        )
    }

    /// Context for a restartable [`crate::attestation::SnapshotReplayGuard`].
    pub fn replay_context(&self) -> Digest32 {
        domain_digest(
            REPLAY_CONTEXT_DOMAIN,
            &[
                &protocol_id(),
                &self.hosted_session,
                &self.issuer_verifier_id,
                &self.bfv.collective_public_key_digest,
                &self.parameter_digest,
            ],
        )
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != SAME_OPENING_CLAIM_WIRE_LEN {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let mut cursor = Cursor::new(bytes);
        if cursor.take::<8>()? != *CLAIM_MAGIC {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let privacy_tier = AmmPrivacyTier::from_byte(cursor.byte()?)?;
        let hosted_session = cursor.take::<32>()?;
        let sequence = u64::from_be_bytes(cursor.take::<8>()?);
        let proof_session = u32::from_be_bytes(cursor.take::<4>()?);
        let rule = u32::from_be_bytes(cursor.take::<4>()?);
        let k = u32::from_be_bytes(cursor.take::<4>()?);
        let dx_bound = u64::from_be_bytes(cursor.take::<8>()?);
        let dy_bound = u64::from_be_bytes(cursor.take::<8>()?);
        let old_root = core::array::from_fn(|_| {
            u32::from_be_bytes(cursor.take::<4>().expect("fixed claim length"))
        });
        let new_root = core::array::from_fn(|_| {
            u32::from_be_bytes(cursor.take::<4>().expect("fixed claim length"))
        });
        let statement = PublicStatement {
            session: proof_session,
            rule,
            k,
            old_root,
            new_root,
        };
        statement
            .validate()
            .map_err(|_| AmmSameOpeningError::MalformedWire)?;
        let bfv = BfvPublicIdentity {
            n_parties: u64::from_be_bytes(cursor.take::<8>()?),
            opening_threshold: u64::from_be_bytes(cursor.take::<8>()?),
            degree: u64::from_be_bytes(cursor.take::<8>()?),
            moduli_digest: cursor.take::<32>()?,
            plaintext_modulus: u64::from_be_bytes(cursor.take::<8>()?),
            crp_seed: cursor.take::<32>()?,
            collective_public_key_digest: cursor.take::<32>()?,
        };
        let parameter_digest = cursor.take::<32>()?;
        let dx_ciphertext_digest = cursor.take::<32>()?;
        let dy_ciphertext_digest = cursor.take::<32>()?;
        let hidingfri_statement_digest = cursor.take::<32>()?;
        let hidingfri_proof_digest = cursor.take::<32>()?;
        let descriptor_digest = cursor.take::<32>()?;
        let issuer_roster_digest = cursor.take::<32>()?;
        let issuer_verifier_id = cursor.take::<32>()?;
        let issuer_threshold = u32::from_be_bytes(cursor.take::<4>()?);
        let issuer_roster_len = u32::from_be_bytes(cursor.take::<4>()?);
        cursor.finish()?;
        if bfv.n_parties == 0
            || bfv.n_parties > MAX_AUTHORITY_PARTIES as u64
            || bfv.opening_threshold == 0
            || bfv.opening_threshold > bfv.n_parties
            || bfv.degree == 0
            || bfv.plaintext_modulus == 0
            || dx_bound == 0
            || dx_bound >= bfv.plaintext_modulus
            || dy_bound == 0
            || dy_bound >= bfv.plaintext_modulus
            || issuer_roster_len == 0
            || issuer_roster_len > MAX_AUTHORITY_PARTIES as u32
            || issuer_threshold == 0
            || issuer_threshold > issuer_roster_len
            || hidingfri_statement_digest != statement_digest(statement)
            || descriptor_digest
                != domain_digest(
                    DESCRIPTOR_DOMAIN,
                    &[dark_amm_private::DARK_AMM_PRIVATE_DESCRIPTOR_JSON.as_bytes()],
                )
        {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        Ok(Self {
            privacy_tier,
            hosted_session,
            sequence,
            proof_session,
            rule,
            k,
            dx_bound,
            dy_bound,
            old_root,
            new_root,
            bfv,
            parameter_digest,
            dx_ciphertext_digest,
            dy_ciphertext_digest,
            hidingfri_statement_digest,
            hidingfri_proof_digest,
            descriptor_digest,
            issuer_roster_digest,
            issuer_verifier_id,
            issuer_threshold,
            issuer_roster_len,
        })
    }
}

/// One issuer's endorsement, produced only after the full reference check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tier1SameOpeningEndorsement {
    pub claim: AmmSameOpeningClaim,
    pub signature: PartyClaimSignature,
}

impl Tier1SameOpeningEndorsement {
    /// Canonical, fixed-size artifact exchanged between one issuer and the
    /// receipt assembler. It contains no witness, encryption seed, or signing
    /// key material.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SAME_OPENING_ENDORSEMENT_WIRE_LEN);
        out.extend_from_slice(ENDORSEMENT_MAGIC);
        out.extend_from_slice(&self.claim.canonical_bytes());
        out.extend_from_slice(&self.signature.signer_index.to_be_bytes());
        out.extend_from_slice(&self.signature.signature);
        debug_assert_eq!(out.len(), SAME_OPENING_ENDORSEMENT_WIRE_LEN);
        out
    }

    /// Decode one strict endorsement. Cryptographic signature validation is
    /// intentionally performed by [`Tier1SameOpeningAuthority::assemble_receipt`],
    /// where the ordered public-key roster is available.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != SAME_OPENING_ENDORSEMENT_WIRE_LEN {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let mut cursor = Cursor::new(bytes);
        if cursor.take::<8>()? != *ENDORSEMENT_MAGIC {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let claim_bytes = cursor.take::<SAME_OPENING_CLAIM_WIRE_LEN>()?;
        let claim = AmmSameOpeningClaim::from_canonical_bytes(&claim_bytes)?;
        let signer_index = u32::from_be_bytes(cursor.take::<4>()?);
        let signature = cursor.take::<64>()?;
        cursor.finish()?;
        if signer_index >= claim.issuer_roster_len {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let endorsement = Self {
            claim,
            signature: PartyClaimSignature {
                signer_index,
                signature,
            },
        };
        if endorsement.to_wire_bytes() != bytes {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        Ok(endorsement)
    }
}

/// Configured threshold authority. Issuers sharing this public configuration
/// must call [`endorse`](Self::endorse) independently with their own key.
#[derive(Clone, Debug)]
pub struct Tier1SameOpeningAuthority {
    verifier: AuthenticatedQuorumVerifier,
}

impl Tier1SameOpeningAuthority {
    pub fn new(ordered_public_keys: Vec<[u8; 32]>, threshold: usize) -> Result<Self> {
        if ordered_public_keys.len() > MAX_AUTHORITY_PARTIES {
            return Err(AmmSameOpeningError::InvalidContext);
        }
        Ok(Self {
            verifier: AuthenticatedQuorumVerifier::new(ordered_public_keys, threshold)?,
        })
    }

    pub fn verifier(&self) -> &AuthenticatedQuorumVerifier {
        &self.verifier
    }

    /// Perform all opening and proof checks before creating any signature.
    #[allow(clippy::too_many_arguments)]
    pub fn endorse(
        &self,
        context: &AmmSameOpeningContext<'_>,
        witness: &PrivateAmmWitness,
        dx_opening: &ExactBfvAmountOpening,
        dy_opening: &ExactBfvAmountOpening,
        signer_index: usize,
        signing_key: &SigningKey,
    ) -> Result<Tier1SameOpeningEndorsement> {
        validate_amount_bound(
            AmmAmount::Dx,
            context.dx_bound,
            dx_opening.value,
            context.params.plaintext_modulus(),
        )?;
        validate_amount_bound(
            AmmAmount::Dy,
            context.dy_bound,
            dy_opening.value,
            context.params.plaintext_modulus(),
        )?;
        if dx_opening.encryption_seed == [0; 32] {
            return Err(AmmSameOpeningError::InvalidEncryptionSeed {
                amount: AmmAmount::Dx,
            });
        }
        if dy_opening.encryption_seed == [0; 32] {
            return Err(AmmSameOpeningError::InvalidEncryptionSeed {
                amount: AmmAmount::Dy,
            });
        }
        if dx_opening.encryption_seed == dy_opening.encryption_seed {
            return Err(AmmSameOpeningError::ReusedEncryptionSeed);
        }
        if witness.dx != dx_opening.value {
            return Err(AmmSameOpeningError::WitnessOpeningMismatch {
                amount: AmmAmount::Dx,
            });
        }
        if witness.dy != dy_opening.value {
            return Err(AmmSameOpeningError::WitnessOpeningMismatch {
                amount: AmmAmount::Dy,
            });
        }
        verify_reencryption(
            AmmAmount::Dx,
            context.params,
            context.collective,
            context.dx_ciphertext,
            dx_opening,
        )?;
        verify_reencryption(
            AmmAmount::Dy,
            context.params,
            context.collective,
            context.dy_ciphertext,
            dy_opening,
        )?;
        let reconstructed = dark_amm_private::statement(context.statement.session, witness)
            .map_err(|_| AmmSameOpeningError::StatementMismatch)?;
        if reconstructed != context.statement {
            return Err(AmmSameOpeningError::StatementMismatch);
        }
        dark_amm_private::verify_zk(context.proof, context.statement)
            .map_err(|_| AmmSameOpeningError::ProofRejected)?;
        let claim = claim_from_context(context, &self.verifier)?;
        let signature = self
            .verifier
            .sign_claim(&claim.digest(), signer_index, signing_key)?;
        Ok(Tier1SameOpeningEndorsement { claim, signature })
    }

    pub fn assemble_receipt(
        &self,
        endorsements: &[Tier1SameOpeningEndorsement],
    ) -> Result<AmmSameOpeningReceipt> {
        let first = endorsements
            .first()
            .ok_or(AmmSameOpeningError::EmptyEndorsements)?;
        if endorsements
            .iter()
            .any(|endorsement| endorsement.claim != first.claim)
        {
            return Err(AmmSameOpeningError::EndorsementClaimMismatch);
        }
        let mut signatures = endorsements
            .iter()
            .map(|endorsement| endorsement.signature.clone())
            .collect::<Vec<_>>();
        signatures.sort_by_key(|signature| signature.signer_index);
        self.verifier
            .assemble_evidence(&first.claim.digest(), &signatures)?;
        Ok(AmmSameOpeningReceipt {
            claim: first.claim.clone(),
            signatures,
        })
    }
}

fn validate_amount_bound(
    amount: AmmAmount,
    bound: u64,
    opening: u16,
    plaintext_modulus: u64,
) -> Result<()> {
    if bound == 0 || bound >= plaintext_modulus || u64::from(opening) > bound {
        return Err(AmmSameOpeningError::InvalidAmountBound { amount });
    }
    Ok(())
}

fn verify_reencryption(
    amount: AmmAmount,
    params: &BfvParams,
    collective: &CollectivePublicKey,
    ciphertext: &Ciphertext,
    opening: &ExactBfvAmountOpening,
) -> Result<()> {
    let reproduced = deterministic_encrypt(params, collective, opening)
        .map_err(|_| AmmSameOpeningError::BfvOperation { amount })?;
    if reproduced.to_bytes() != ciphertext.to_bytes() {
        return Err(AmmSameOpeningError::BfvReencryptionMismatch { amount });
    }
    Ok(())
}

fn statement_digest(statement: PublicStatement) -> Digest32 {
    let mut bytes = Vec::with_capacity(19 * 4);
    for value in statement.as_u32_array() {
        bytes.extend_from_slice(&value.to_be_bytes());
    }
    domain_digest(STATEMENT_DOMAIN, &[&bytes])
}

fn claim_from_context(
    context: &AmmSameOpeningContext<'_>,
    verifier: &AuthenticatedQuorumVerifier,
) -> Result<AmmSameOpeningClaim> {
    context
        .statement
        .validate()
        .map_err(|_| AmmSameOpeningError::InvalidContext)?;
    if context.keygen.n_parties() == 0
        || context.keygen.n_parties() > MAX_AUTHORITY_PARTIES
        || verifier.ordered_public_keys().is_empty()
        || verifier.ordered_public_keys().len() > MAX_AUTHORITY_PARTIES
        || context.dx_bound == 0
        || context.dx_bound >= context.params.plaintext_modulus()
        || context.dy_bound == 0
        || context.dy_bound >= context.params.plaintext_modulus()
    {
        return Err(AmmSameOpeningError::InvalidContext);
    }
    let proof_bytes = context
        .proof
        .to_postcard()
        .map_err(|_| AmmSameOpeningError::ProofEncoding)?;
    Ok(AmmSameOpeningClaim {
        privacy_tier: context.privacy_tier,
        hosted_session: context.hosted_session,
        sequence: context.sequence,
        proof_session: context.statement.session,
        rule: context.statement.rule,
        k: context.statement.k,
        dx_bound: context.dx_bound,
        dy_bound: context.dy_bound,
        old_root: context.statement.old_root,
        new_root: context.statement.new_root,
        bfv: BfvPublicIdentity::from_public(context.params, context.keygen, context.collective),
        parameter_digest: canonical_bfv_parameters_digest(context.params.arc()),
        dx_ciphertext_digest: domain_digest(
            CIPHERTEXT_DOMAIN,
            &[&context.dx_ciphertext.to_bytes()],
        ),
        dy_ciphertext_digest: domain_digest(
            CIPHERTEXT_DOMAIN,
            &[&context.dy_ciphertext.to_bytes()],
        ),
        hidingfri_statement_digest: statement_digest(context.statement),
        hidingfri_proof_digest: domain_digest(PROOF_DOMAIN, &[&proof_bytes]),
        descriptor_digest: domain_digest(
            DESCRIPTOR_DOMAIN,
            &[dark_amm_private::DARK_AMM_PRIVATE_DESCRIPTOR_JSON.as_bytes()],
        ),
        issuer_roster_digest: verifier.roster_digest(),
        issuer_verifier_id: verifier.verifier_id(),
        issuer_threshold: verifier.threshold() as u32,
        issuer_roster_len: verifier.ordered_public_keys().len() as u32,
    })
}

/// Quorum-authenticated exact-opening receipt. It carries no witness,
/// encryption seed, ciphertext, proof body, or secret issuer key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AmmSameOpeningReceipt {
    pub claim: AmmSameOpeningClaim,
    pub signatures: Vec<PartyClaimSignature>,
}

impl AmmSameOpeningReceipt {
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            8 + SAME_OPENING_CLAIM_WIRE_LEN + 4 + self.signatures.len() * SIGNATURE_RECORD_LEN,
        );
        out.extend_from_slice(RECEIPT_MAGIC);
        out.extend_from_slice(&self.claim.canonical_bytes());
        out.extend_from_slice(&(self.signatures.len() as u32).to_be_bytes());
        for signature in &self.signatures {
            out.extend_from_slice(&signature.signer_index.to_be_bytes());
            out.extend_from_slice(&signature.signature);
        }
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        const PREFIX: usize = 8 + SAME_OPENING_CLAIM_WIRE_LEN + 4;
        if bytes.len() < PREFIX || bytes[..8] != *RECEIPT_MAGIC {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let claim =
            AmmSameOpeningClaim::from_canonical_bytes(&bytes[8..8 + SAME_OPENING_CLAIM_WIRE_LEN])?;
        let count = u32::from_be_bytes(
            bytes[8 + SAME_OPENING_CLAIM_WIRE_LEN..PREFIX]
                .try_into()
                .map_err(|_| AmmSameOpeningError::MalformedWire)?,
        ) as usize;
        let expected_len = count
            .checked_mul(SIGNATURE_RECORD_LEN)
            .and_then(|records| PREFIX.checked_add(records))
            .ok_or(AmmSameOpeningError::MalformedWire)?;
        if count < claim.issuer_threshold as usize
            || count > claim.issuer_roster_len as usize
            || count > MAX_AUTHORITY_PARTIES
            || bytes.len() != expected_len
        {
            return Err(AmmSameOpeningError::MalformedWire);
        }
        let mut signatures = Vec::with_capacity(count);
        let mut previous = None;
        for record in bytes[PREFIX..].chunks_exact(SIGNATURE_RECORD_LEN) {
            let signer_index = u32::from_be_bytes(
                record[..4]
                    .try_into()
                    .map_err(|_| AmmSameOpeningError::MalformedWire)?,
            );
            if signer_index >= claim.issuer_roster_len
                || previous.is_some_and(|prior| prior >= signer_index)
            {
                return Err(AmmSameOpeningError::NonCanonicalSignerOrder);
            }
            previous = Some(signer_index);
            signatures.push(PartyClaimSignature {
                signer_index,
                signature: record[4..]
                    .try_into()
                    .map_err(|_| AmmSameOpeningError::MalformedWire)?,
            });
        }
        Ok(Self { claim, signatures })
    }

    /// Verify all public bindings/proof/evidence before atomically consuming
    /// the hosted sequence replay slot.
    pub fn verify<R: ReplayGuard>(
        &self,
        expected: &AmmSameOpeningContext<'_>,
        verifier: &AuthenticatedQuorumVerifier,
        replay: &mut R,
    ) -> Result<VerifiedAmmSameOpening> {
        let expected_claim = claim_from_context(expected, verifier)?;
        if self.claim != expected_claim {
            return Err(AmmSameOpeningError::BindingMismatch);
        }
        if self.claim.issuer_roster_digest != verifier.roster_digest()
            || self.claim.issuer_verifier_id != verifier.verifier_id()
            || self.claim.issuer_threshold != verifier.threshold() as u32
            || self.claim.issuer_roster_len != verifier.ordered_public_keys().len() as u32
        {
            return Err(AmmSameOpeningError::AuthorityMismatch);
        }
        dark_amm_private::verify_zk(expected.proof, expected.statement)
            .map_err(|_| AmmSameOpeningError::ProofRejected)?;
        verifier.assemble_evidence(&self.claim.digest(), &self.signatures)?;
        if !replay.check_and_record(self.claim.replay_id()) {
            return Err(AmmSameOpeningError::ReplayDetected);
        }
        Ok(VerifiedAmmSameOpening {
            claim_digest: self.claim.digest(),
            hosted_session: self.claim.hosted_session,
            sequence: self.claim.sequence,
            old_root: self.claim.old_root,
            new_root: self.claim.new_root,
            k: self.claim.k,
            dx_bound: self.claim.dx_bound,
            dy_bound: self.claim.dy_bound,
        })
    }
}

/// Unforgeable-by-construction host capability returned only after full proof,
/// threshold-evidence, binding, and replay verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedAmmSameOpening {
    claim_digest: Digest32,
    hosted_session: Digest32,
    sequence: u64,
    old_root: [u32; 8],
    new_root: [u32; 8],
    k: u32,
    dx_bound: u64,
    dy_bound: u64,
}

impl VerifiedAmmSameOpening {
    pub fn claim_digest(&self) -> Digest32 {
        self.claim_digest
    }

    pub fn hosted_session(&self) -> Digest32 {
        self.hosted_session
    }

    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    pub fn old_root(&self) -> [u32; 8] {
        self.old_root
    }

    pub fn new_root(&self) -> [u32; 8] {
        self.new_root
    }

    pub fn k(&self) -> u32 {
        self.k
    }

    pub fn dx_bound(&self) -> u64 {
        self.dx_bound
    }

    pub fn dy_bound(&self) -> u64 {
        self.dy_bound
    }
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N]> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(AmmSameOpeningError::MalformedWire)?;
        let out = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| AmmSameOpeningError::MalformedWire)?;
        self.offset = end;
        Ok(out)
    }

    fn byte(&mut self) -> Result<u8> {
        Ok(self.take::<1>()?[0])
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(AmmSameOpeningError::MalformedWire)
        }
    }
}
