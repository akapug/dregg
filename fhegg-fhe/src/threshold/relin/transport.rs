//! Authenticated transport control plane for multiparty relinearization.
//!
//! Each fixed-width [`SignedRelinEnvelope`] binds one sender to the exact
//! relinearization session, collective public key, ordered transport roster,
//! round, predecessor transcript, and a party-chosen public message ID.  The
//! coordinator accepts each sender once, in phase, and snapshots the complete
//! signed public transcript in canonical party order.  Snapshot decoding
//! checks exact EOF, a bounded roster, all signatures and phase transitions,
//! and recomputes both round transcript digests before exposing state.
//!
//! # Upstream codec boundary
//!
//! fhe.rs 0.1.1 deliberately exposes `RelinKeyShare<R1/R2>` as a typed public
//! value but exposes neither its fields nor `Serialize`/`Deserialize`.  This
//! module therefore does **not** pretend that a debug string, memory image, or
//! lossy hash is a canonical algebraic-share wire format.  The signed envelope
//! is a canonical public *manifest*.  A coordinator restart can restore its
//! authenticated state and require the live party to resend the opaque typed
//! share under exactly the recorded manifest via [`RelinCoordinator::verify_recorded_resend`].
//! Until upstream exposes a canonical share codec (or a proof/commitment to the
//! share), the message ID cannot cryptographically bind the opaque payload.
//! Party restart in the middle of R1/R2 is also unsupported because fhe.rs's
//! secret-dependent generator retains private ephemeral `u` across rounds.
//! The snapshot checksum detects corruption, not rollback: deployment must
//! transactionally anchor its digest/revision in monotonic durable state.
//!
//! This is honest n-of-n transport hardening.  It is not `t < n`, a
//! malicious-share correctness proof, or a verifiable-secret-sharing relin
//! protocol.

use std::collections::{BTreeMap, HashSet};

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use sha2::{Digest, Sha256};

use super::RelinKeySession;

const ENVELOPE_MAGIC: &[u8; 8] = b"FHRMv001";
const SNAPSHOT_MAGIC: &[u8; 8] = b"FHRCS001";
const ROSTER_DOMAIN: &[u8] = b"fhegg/relin/transport-roster/v1";
const SIGNATURE_DOMAIN: &[u8] = b"fhegg/relin/transport-signature/v1";
const TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/relin/transport-transcript/v1";
const SNAPSHOT_DOMAIN: &[u8] = b"fhegg/relin/coordinator-snapshot/v1";
const ZERO_DIGEST: [u8; 32] = [0; 32];

/// The Lean-pinned n-of-n threshold parameters permit at most 16 parties.
/// Keeping the same hard ceiling makes every snapshot allocation bounded.
pub const MAX_RELIN_PARTIES: usize = 16;

/// One envelope is fixed-width: magic + phase + party + five digests + Ed25519.
pub const RELIN_ENVELOPE_WIRE_LEN: usize = 8 + 1 + 4 + (5 * 32) + 64;
const SNAPSHOT_HEADER_LEN: usize = 8 + (5 * 32) + 1 + (3 * 4);
const SNAPSHOT_CHECKSUM_LEN: usize = 32;

pub type Result<T> = std::result::Result<T, RelinTransportError>;

/// Fail-closed transport and recovery errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelinTransportError {
    EmptyRoster,
    RosterTooLarge { have: usize, max: usize },
    RosterSizeMismatch { have: usize, need: usize },
    InvalidPublicKey { party: usize },
    DuplicatePublicKey { party: usize },
    InvalidParty { party: usize, n_parties: usize },
    SignerKeyMismatch { party: usize },
    SessionMismatch,
    PublicKeyMismatch,
    RosterMismatch,
    PhaseMismatch,
    PredecessorMismatch,
    ZeroMessageId,
    DuplicateMessage { phase: RelinPhase, party: usize },
    InvalidSignature { party: usize },
    MalformedWire,
    SnapshotChecksumMismatch,
    SnapshotInconsistent,
    NonCanonicalOrder,
    UnrecordedMessage { phase: RelinPhase, party: usize },
    SubstitutedMessage { phase: RelinPhase, party: usize },
}

impl std::fmt::Display for RelinTransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for RelinTransportError {}

/// The two public protocol rounds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum RelinPhase {
    Round1 = 1,
    Round2 = 2,
}

impl RelinPhase {
    fn from_byte(value: u8) -> Result<Self> {
        match value {
            1 => Ok(Self::Round1),
            2 => Ok(Self::Round2),
            _ => Err(RelinTransportError::MalformedWire),
        }
    }
}

/// Derived coordinator phase.  It is serialized but also recomputed from the
/// two canonical transcript prefixes during recovery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum CoordinatorPhase {
    CollectingRound1 = 1,
    CollectingRound2 = 2,
    Complete = 3,
}

impl CoordinatorPhase {
    fn from_byte(value: u8) -> Result<Self> {
        match value {
            1 => Ok(Self::CollectingRound1),
            2 => Ok(Self::CollectingRound2),
            3 => Ok(Self::Complete),
            _ => Err(RelinTransportError::MalformedWire),
        }
    }
}

fn digest(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    for part in parts {
        hasher.update((part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    hasher.finalize().into()
}

/// Exact ordered Ed25519 roster for one relinearization session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelinRoster {
    ordered_public_keys: Vec<[u8; 32]>,
    digest: [u8; 32],
}

impl RelinRoster {
    pub fn new(session: &RelinKeySession, ordered_public_keys: Vec<[u8; 32]>) -> Result<Self> {
        let have = ordered_public_keys.len();
        let need = session.keygen_session().n_parties();
        if have == 0 {
            return Err(RelinTransportError::EmptyRoster);
        }
        if have > MAX_RELIN_PARTIES {
            return Err(RelinTransportError::RosterTooLarge {
                have,
                max: MAX_RELIN_PARTIES,
            });
        }
        if have != need {
            return Err(RelinTransportError::RosterSizeMismatch { have, need });
        }
        let mut seen = HashSet::with_capacity(have);
        for (party, key) in ordered_public_keys.iter().enumerate() {
            let verifying = VerifyingKey::from_bytes(key)
                .map_err(|_| RelinTransportError::InvalidPublicKey { party })?;
            if verifying.is_weak() {
                return Err(RelinTransportError::InvalidPublicKey { party });
            }
            if !seen.insert(*key) {
                return Err(RelinTransportError::DuplicatePublicKey { party });
            }
        }

        let mut bytes = Vec::with_capacity(68 + have * 32);
        bytes.extend_from_slice(&session.session_id());
        bytes.extend_from_slice(&session.collective_public_key_digest());
        bytes.extend_from_slice(&(have as u32).to_be_bytes());
        for key in &ordered_public_keys {
            bytes.extend_from_slice(key);
        }
        let digest = digest(ROSTER_DOMAIN, &[&bytes]);
        Ok(Self {
            ordered_public_keys,
            digest,
        })
    }

    pub fn ordered_public_keys(&self) -> &[[u8; 32]] {
        &self.ordered_public_keys
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    pub fn len(&self) -> usize {
        self.ordered_public_keys.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ordered_public_keys.is_empty()
    }
}

/// Canonical authenticated manifest for one opaque public R1/R2 share.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedRelinEnvelope {
    phase: RelinPhase,
    party: u32,
    session_id: [u8; 32],
    collective_public_key_digest: [u8; 32],
    roster_digest: [u8; 32],
    predecessor_transcript_digest: [u8; 32],
    message_id: [u8; 32],
    signature: [u8; 64],
}

impl SignedRelinEnvelope {
    /// Sign a manifest, refusing a secret key that does not own `party`'s slot.
    pub fn sign(
        session: &RelinKeySession,
        roster: &RelinRoster,
        phase: RelinPhase,
        party: usize,
        predecessor_transcript_digest: [u8; 32],
        message_id: [u8; 32],
        signing_key: &SigningKey,
    ) -> Result<Self> {
        let expected =
            roster
                .ordered_public_keys
                .get(party)
                .ok_or(RelinTransportError::InvalidParty {
                    party,
                    n_parties: roster.len(),
                })?;
        if signing_key.verifying_key().to_bytes() != *expected {
            return Err(RelinTransportError::SignerKeyMismatch { party });
        }
        if message_id == ZERO_DIGEST {
            return Err(RelinTransportError::ZeroMessageId);
        }
        let party = u32::try_from(party).map_err(|_| RelinTransportError::InvalidParty {
            party,
            n_parties: roster.len(),
        })?;
        let mut envelope = Self {
            phase,
            party,
            session_id: session.session_id(),
            collective_public_key_digest: session.collective_public_key_digest(),
            roster_digest: roster.digest,
            predecessor_transcript_digest,
            message_id,
            signature: [0; 64],
        };
        envelope.signature = signing_key.sign(&envelope.signing_message()).to_bytes();
        Ok(envelope)
    }

    pub fn phase(&self) -> RelinPhase {
        self.phase
    }

    pub fn party(&self) -> usize {
        self.party as usize
    }

    pub fn message_id(&self) -> [u8; 32] {
        self.message_id
    }

    pub fn predecessor_transcript_digest(&self) -> [u8; 32] {
        self.predecessor_transcript_digest
    }

    fn unsigned_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(RELIN_ENVELOPE_WIRE_LEN - 64);
        out.extend_from_slice(ENVELOPE_MAGIC);
        out.push(self.phase as u8);
        out.extend_from_slice(&self.party.to_be_bytes());
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&self.collective_public_key_digest);
        out.extend_from_slice(&self.roster_digest);
        out.extend_from_slice(&self.predecessor_transcript_digest);
        out.extend_from_slice(&self.message_id);
        out
    }

    fn signing_message(&self) -> [u8; 32] {
        digest(SIGNATURE_DOMAIN, &[&self.unsigned_wire_bytes()])
    }

    /// Fixed-width canonical network representation.  All integers are big-endian.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = self.unsigned_wire_bytes();
        out.extend_from_slice(&self.signature);
        debug_assert_eq!(out.len(), RELIN_ENVELOPE_WIRE_LEN);
        out
    }

    /// Parse framing only.  A coordinator/roster must verify the signature and
    /// all contextual bindings before the message is accepted.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != RELIN_ENVELOPE_WIRE_LEN {
            return Err(RelinTransportError::MalformedWire);
        }
        let mut cursor = Cursor::new(bytes);
        if cursor.take::<8>()? != *ENVELOPE_MAGIC {
            return Err(RelinTransportError::MalformedWire);
        }
        let phase = RelinPhase::from_byte(cursor.byte()?)?;
        let party = u32::from_be_bytes(cursor.take::<4>()?);
        let session_id = cursor.take::<32>()?;
        let collective_public_key_digest = cursor.take::<32>()?;
        let roster_digest = cursor.take::<32>()?;
        let predecessor_transcript_digest = cursor.take::<32>()?;
        let message_id = cursor.take::<32>()?;
        let signature = cursor.take::<64>()?;
        cursor.finish()?;
        Ok(Self {
            phase,
            party,
            session_id,
            collective_public_key_digest,
            roster_digest,
            predecessor_transcript_digest,
            message_id,
            signature,
        })
    }
}

/// Public, bounded state machine for a single exact n-of-n ceremony.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelinCoordinator {
    session_id: [u8; 32],
    collective_public_key_digest: [u8; 32],
    roster: RelinRoster,
    round1: BTreeMap<usize, SignedRelinEnvelope>,
    round2: BTreeMap<usize, SignedRelinEnvelope>,
}

impl RelinCoordinator {
    pub fn new(session: &RelinKeySession, ordered_public_keys: Vec<[u8; 32]>) -> Result<Self> {
        let roster = RelinRoster::new(session, ordered_public_keys)?;
        Ok(Self {
            session_id: session.session_id(),
            collective_public_key_digest: session.collective_public_key_digest(),
            roster,
            round1: BTreeMap::new(),
            round2: BTreeMap::new(),
        })
    }

    pub fn roster(&self) -> &RelinRoster {
        &self.roster
    }

    pub fn phase(&self) -> CoordinatorPhase {
        if self.round1.len() < self.roster.len() {
            CoordinatorPhase::CollectingRound1
        } else if self.round2.len() < self.roster.len() {
            CoordinatorPhase::CollectingRound2
        } else {
            CoordinatorPhase::Complete
        }
    }

    pub fn accepted_in_current_phase(&self) -> usize {
        match self.phase() {
            CoordinatorPhase::CollectingRound1 => self.round1.len(),
            CoordinatorPhase::CollectingRound2 | CoordinatorPhase::Complete => self.round2.len(),
        }
    }

    pub fn round1_transcript_digest(&self) -> Option<[u8; 32]> {
        (self.round1.len() == self.roster.len())
            .then(|| transcript_digest(RelinPhase::Round1, &self.round1))
    }

    pub fn round2_transcript_digest(&self) -> Option<[u8; 32]> {
        (self.round2.len() == self.roster.len())
            .then(|| transcript_digest(RelinPhase::Round2, &self.round2))
    }

    /// Decode and atomically accept one signed envelope.
    pub fn accept_wire(&mut self, bytes: &[u8]) -> Result<()> {
        let envelope = SignedRelinEnvelope::from_wire_bytes(bytes)?;
        self.accept(envelope)
    }

    /// Atomically accept one envelope.  Every fallible check occurs before the
    /// canonical transcript map is changed.
    pub fn accept(&mut self, envelope: SignedRelinEnvelope) -> Result<()> {
        let expected_phase = match self.phase() {
            CoordinatorPhase::CollectingRound1 => RelinPhase::Round1,
            CoordinatorPhase::CollectingRound2 => RelinPhase::Round2,
            CoordinatorPhase::Complete => return Err(RelinTransportError::PhaseMismatch),
        };
        if envelope.phase != expected_phase {
            return Err(RelinTransportError::PhaseMismatch);
        }
        self.verify_static(&envelope)?;
        let expected_predecessor = match expected_phase {
            RelinPhase::Round1 => ZERO_DIGEST,
            RelinPhase::Round2 => self
                .round1_transcript_digest()
                .ok_or(RelinTransportError::SnapshotInconsistent)?,
        };
        if envelope.predecessor_transcript_digest != expected_predecessor {
            return Err(RelinTransportError::PredecessorMismatch);
        }
        let party = envelope.party();
        let target = match expected_phase {
            RelinPhase::Round1 => &mut self.round1,
            RelinPhase::Round2 => &mut self.round2,
        };
        if target.contains_key(&party) {
            return Err(RelinTransportError::DuplicateMessage {
                phase: expected_phase,
                party,
            });
        }
        target.insert(party, envelope);
        Ok(())
    }

    /// Verify that a live party's post-restart manifest is byte-for-byte the
    /// authenticated manifest already retained in the snapshot.  Only after
    /// this succeeds should the coordinator pair it with the party-resupplied
    /// opaque `RelinKeyShare<R1/R2>` typed value.
    pub fn verify_recorded_resend(&self, envelope: &SignedRelinEnvelope) -> Result<()> {
        self.verify_static(envelope)?;
        let expected_predecessor = match envelope.phase {
            RelinPhase::Round1 => ZERO_DIGEST,
            RelinPhase::Round2 => self
                .round1_transcript_digest()
                .ok_or(RelinTransportError::PredecessorMismatch)?,
        };
        if envelope.predecessor_transcript_digest != expected_predecessor {
            return Err(RelinTransportError::PredecessorMismatch);
        }
        let party = envelope.party();
        let recorded = match envelope.phase {
            RelinPhase::Round1 => self.round1.get(&party),
            RelinPhase::Round2 => self.round2.get(&party),
        }
        .ok_or(RelinTransportError::UnrecordedMessage {
            phase: envelope.phase,
            party,
        })?;
        if recorded != envelope {
            return Err(RelinTransportError::SubstitutedMessage {
                phase: envelope.phase,
                party,
            });
        }
        Ok(())
    }

    fn verify_static(&self, envelope: &SignedRelinEnvelope) -> Result<()> {
        let party = envelope.party();
        let key = self.roster.ordered_public_keys.get(party).ok_or(
            RelinTransportError::InvalidParty {
                party,
                n_parties: self.roster.len(),
            },
        )?;
        if envelope.session_id != self.session_id {
            return Err(RelinTransportError::SessionMismatch);
        }
        if envelope.collective_public_key_digest != self.collective_public_key_digest {
            return Err(RelinTransportError::PublicKeyMismatch);
        }
        if envelope.roster_digest != self.roster.digest {
            return Err(RelinTransportError::RosterMismatch);
        }
        if envelope.message_id == ZERO_DIGEST {
            return Err(RelinTransportError::ZeroMessageId);
        }
        let verifying = VerifyingKey::from_bytes(key)
            .map_err(|_| RelinTransportError::InvalidPublicKey { party })?;
        verifying
            .verify_strict(
                &envelope.signing_message(),
                &Signature::from_bytes(&envelope.signature),
            )
            .map_err(|_| RelinTransportError::InvalidSignature { party })
    }

    /// Canonical bounded coordinator snapshot.  It contains only public keys,
    /// signed manifests, and public transcript digests—never party generators,
    /// ephemeral `u`, secret shares, or opaque algebraic share payloads.
    pub fn to_snapshot_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            SNAPSHOT_HEADER_LEN
                + self.roster.len() * 32
                + (self.round1.len() + self.round2.len()) * RELIN_ENVELOPE_WIRE_LEN
                + SNAPSHOT_CHECKSUM_LEN,
        );
        out.extend_from_slice(SNAPSHOT_MAGIC);
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&self.collective_public_key_digest);
        out.extend_from_slice(&self.roster.digest);
        out.extend_from_slice(&self.round1_transcript_digest().unwrap_or(ZERO_DIGEST));
        out.extend_from_slice(&self.round2_transcript_digest().unwrap_or(ZERO_DIGEST));
        out.push(self.phase() as u8);
        out.extend_from_slice(&(self.roster.len() as u32).to_be_bytes());
        out.extend_from_slice(&(self.round1.len() as u32).to_be_bytes());
        out.extend_from_slice(&(self.round2.len() as u32).to_be_bytes());
        for key in &self.roster.ordered_public_keys {
            out.extend_from_slice(key);
        }
        for envelope in self.round1.values().chain(self.round2.values()) {
            out.extend_from_slice(&envelope.to_wire_bytes());
        }
        let checksum = digest(SNAPSHOT_DOMAIN, &[&out]);
        out.extend_from_slice(&checksum);
        out
    }

    /// Restore only under an independently supplied expected session.  Every
    /// envelope is replayed through the normal state machine, so duplicate,
    /// out-of-phase, forged, and substituted snapshot records cannot become
    /// live coordinator state.
    pub fn from_snapshot_bytes(bytes: &[u8], session: &RelinKeySession) -> Result<Self> {
        if bytes.len() < SNAPSHOT_HEADER_LEN + SNAPSHOT_CHECKSUM_LEN {
            return Err(RelinTransportError::MalformedWire);
        }
        let (body, checksum_bytes) = bytes.split_at(bytes.len() - SNAPSHOT_CHECKSUM_LEN);
        let checksum: [u8; 32] = checksum_bytes
            .try_into()
            .map_err(|_| RelinTransportError::MalformedWire)?;
        if digest(SNAPSHOT_DOMAIN, &[body]) != checksum {
            return Err(RelinTransportError::SnapshotChecksumMismatch);
        }
        let mut cursor = Cursor::new(body);
        if cursor.take::<8>()? != *SNAPSHOT_MAGIC {
            return Err(RelinTransportError::MalformedWire);
        }
        let session_id = cursor.take::<32>()?;
        let public_key_digest = cursor.take::<32>()?;
        let roster_digest = cursor.take::<32>()?;
        let encoded_r1_digest = cursor.take::<32>()?;
        let encoded_r2_digest = cursor.take::<32>()?;
        let encoded_phase = CoordinatorPhase::from_byte(cursor.byte()?)?;
        let n = cursor.u32_usize()?;
        let r1_count = cursor.u32_usize()?;
        let r2_count = cursor.u32_usize()?;
        if n == 0 || n > MAX_RELIN_PARTIES || r1_count > n || r2_count > n {
            return Err(RelinTransportError::SnapshotInconsistent);
        }
        let expected_remaining = n
            .checked_mul(32)
            .and_then(|keys| {
                (r1_count + r2_count)
                    .checked_mul(RELIN_ENVELOPE_WIRE_LEN)
                    .and_then(|messages| keys.checked_add(messages))
            })
            .ok_or(RelinTransportError::MalformedWire)?;
        if cursor.remaining() != expected_remaining {
            return Err(RelinTransportError::MalformedWire);
        }
        if session_id != session.session_id() {
            return Err(RelinTransportError::SessionMismatch);
        }
        if public_key_digest != session.collective_public_key_digest() {
            return Err(RelinTransportError::PublicKeyMismatch);
        }
        let mut keys = Vec::with_capacity(n);
        for _ in 0..n {
            keys.push(cursor.take::<32>()?);
        }
        let mut coordinator = Self::new(session, keys)?;
        if coordinator.roster.digest != roster_digest {
            return Err(RelinTransportError::RosterMismatch);
        }
        let mut previous_party = None;
        for index in 0..(r1_count + r2_count) {
            if index == r1_count {
                previous_party = None;
            }
            let wire = cursor.slice(RELIN_ENVELOPE_WIRE_LEN)?;
            let envelope = SignedRelinEnvelope::from_wire_bytes(wire)?;
            let section_phase = if index < r1_count {
                RelinPhase::Round1
            } else {
                RelinPhase::Round2
            };
            if envelope.phase != section_phase {
                return Err(RelinTransportError::SnapshotInconsistent);
            }
            if previous_party.is_some_and(|previous| envelope.party() <= previous) {
                return Err(RelinTransportError::NonCanonicalOrder);
            }
            previous_party = Some(envelope.party());
            coordinator.accept(envelope)?;
        }
        cursor.finish()?;
        if coordinator.phase() != encoded_phase
            || coordinator
                .round1_transcript_digest()
                .unwrap_or(ZERO_DIGEST)
                != encoded_r1_digest
            || coordinator
                .round2_transcript_digest()
                .unwrap_or(ZERO_DIGEST)
                != encoded_r2_digest
        {
            return Err(RelinTransportError::SnapshotInconsistent);
        }
        Ok(coordinator)
    }
}

fn transcript_digest(
    phase: RelinPhase,
    transcript: &BTreeMap<usize, SignedRelinEnvelope>,
) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(5 + transcript.len() * RELIN_ENVELOPE_WIRE_LEN);
    bytes.push(phase as u8);
    bytes.extend_from_slice(&(transcript.len() as u32).to_be_bytes());
    for envelope in transcript.values() {
        bytes.extend_from_slice(&envelope.to_wire_bytes());
    }
    digest(TRANSCRIPT_DOMAIN, &[&bytes])
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
            .ok_or(RelinTransportError::MalformedWire)?;
        let out = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| RelinTransportError::MalformedWire)?;
        self.offset = end;
        Ok(out)
    }

    fn slice(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(RelinTransportError::MalformedWire)?;
        let out = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(out)
    }

    fn byte(&mut self) -> Result<u8> {
        Ok(self.take::<1>()?[0])
    }

    fn u32_usize(&mut self) -> Result<usize> {
        usize::try_from(u32::from_be_bytes(self.take::<4>()?))
            .map_err(|_| RelinTransportError::MalformedWire)
    }

    fn remaining(&self) -> usize {
        self.bytes.len() - self.offset
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(RelinTransportError::MalformedWire)
        }
    }
}
