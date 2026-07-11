//! The pluggable [`RandomnessSource`] trait and its implementations.
//!
//! A source has two halves that must agree:
//! - a **producer** ([`RandomnessSource::evidence`]) that, given a request,
//!   emits the [`RandomnessEvidence`] a receipt would carry, and
//! - a pure **verifier** ([`RandomnessSource::seed`]) that re-derives the
//!   [`Seed`] from `(request, evidence)` and checks the evidence, returning the
//!   seed or a [`VerifyError`].
//!
//! The verifier is the trust surface: it is a pure function of public data and is
//! the same regardless of who produced the evidence.

use std::cell::RefCell;

use crate::draw::{DrawStream, Seed};
use crate::error::VerifyError;
use crate::event::EventId;
use crate::request::{DERIVATION_VERSION, EvidenceKind, RandomnessEvidence, RandomnessRequest};
use crate::util::absorb_len_prefixed;

/// Domain tag for the seed derivation.
pub const DOMAIN_SEED: &[u8] = b"dregg-dice/seed/v1";
/// Domain tag for the commit-reveal commitment.
pub const DOMAIN_COMMIT: &[u8] = b"dregg-dice/commit-reveal/commit/v1";

/// Derive a seed from the event id and a source output, domain-separated by a
/// per-source tag. Because the event id binds `draw_count`/`event_kind`/action,
/// the seed is unique to the finalized context.
fn derive_seed(event_id: &EventId, source_tag: &[u8], source_output: &[u8]) -> Seed {
    let mut h = blake3::Hasher::new();
    absorb_len_prefixed(&mut h, DOMAIN_SEED);
    absorb_len_prefixed(&mut h, source_tag);
    h.update(event_id.as_bytes());
    absorb_len_prefixed(&mut h, source_output);
    Seed::from_bytes(*h.finalize().as_bytes())
}

/// Recompute the transcript commitment for a seed under a request's draw count
/// and compare against the evidence. This is the shared grinding tooth every
/// verifier ends with.
fn check_transcript(
    seed: Seed,
    req: &RandomnessRequest,
    ev: &RandomnessEvidence,
) -> Result<Seed, VerifyError> {
    let stream = DrawStream::new(seed, req.draw_count);
    if stream.transcript_commitment() != ev.draw_transcript_commitment {
        return Err(VerifyError::TranscriptMismatch);
    }
    Ok(seed)
}

fn check_version(ev: &RandomnessEvidence) -> Result<(), VerifyError> {
    if ev.derivation_version != DERIVATION_VERSION {
        return Err(VerifyError::UnsupportedVersion {
            expected: DERIVATION_VERSION,
            found: ev.derivation_version,
        });
    }
    Ok(())
}

/// A pluggable source of verifiable randomness.
///
/// `evidence` produces; `seed` verifies. `seed` takes no `self` — verification is
/// a pure function of public data, so a light client checks a source it never
/// instantiated.
pub trait RandomnessSource {
    /// Produce the evidence a receipt would record for `req`.
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence;

    /// Re-derive and verify the seed from `(req, ev)`.
    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError>
    where
        Self: Sized;
}

// ─────────────────────────────────────────────────────────────────────────────
// Deterministic — the pure test/offline source.
// ─────────────────────────────────────────────────────────────────────────────

/// A deterministic source keyed on a caller-supplied 32-byte context. Fully
/// reproducible; used for tests and for offline sessions where no external
/// unpredictability source is available. Provides **no** unpredictability
/// guarantee on its own — whoever knows the context knows the seed.
#[derive(Clone, Debug)]
pub struct Deterministic {
    /// Context folded into the seed.
    pub context: [u8; 32],
}

impl Deterministic {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"deterministic";
}

impl RandomnessSource for Deterministic {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let seed = derive_seed(&req.event_id(), Self::TAG, &self.context);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::Deterministic {
                context: self.context,
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::Deterministic { context } = &ev.source else {
            return Err(VerifyError::SourceMismatch);
        };
        let seed = derive_seed(&req.event_id(), Self::TAG, context);
        check_transcript(seed, req, ev)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// CommitReveal — two-party, deterministic and testable.
// ─────────────────────────────────────────────────────────────────────────────

/// Two-party commit-reveal.
///
/// The server publishes `commit(server_reveal)` before the player's contribution
/// is bound; the seed folds both contributions with the event id. This prevents
/// either party from *unilaterally choosing* the outcome (the server is bound to
/// its committed reveal; the player cannot bias it without a matching change to
/// the server's committed value). It does **not** prevent a last-revealer
/// **selective abort** — see the crate docs.
#[derive(Clone, Debug)]
pub struct CommitReveal {
    /// The server's secret contribution (opened at reveal time).
    pub server_reveal: [u8; 32],
    /// The player's contribution.
    pub player_contribution: [u8; 32],
}

impl CommitReveal {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"commit-reveal";

    /// The commitment the server publishes before revealing: `H(DOMAIN || reveal)`.
    pub fn commit(server_reveal: &[u8; 32]) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_COMMIT);
        h.update(server_reveal);
        *h.finalize().as_bytes()
    }

    /// The source output feeding the seed: both contributions, length-prefixed.
    fn source_output(server_reveal: &[u8; 32], player_contribution: &[u8; 32]) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(server_reveal);
        out[32..].copy_from_slice(player_contribution);
        out
    }
}

impl RandomnessSource for CommitReveal {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let output = Self::source_output(&self.server_reveal, &self.player_contribution);
        let seed = derive_seed(&req.event_id(), Self::TAG, &output);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::CommitReveal {
                server_commitment: Self::commit(&self.server_reveal),
                server_reveal: self.server_reveal,
                player_contribution: self.player_contribution,
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::CommitReveal {
            server_commitment,
            server_reveal,
            player_contribution,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };
        // The reveal must open the commitment: a tampered reveal is rejected here.
        if Self::commit(server_reveal) != *server_commitment {
            return Err(VerifyError::CommitmentMismatch);
        }
        let output = Self::source_output(server_reveal, player_contribution);
        let seed = derive_seed(&req.event_id(), Self::TAG, &output);
        check_transcript(seed, req, ev)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// MockBeacon — a stand-in for a public randomness beacon (no signature check).
// ─────────────────────────────────────────────────────────────────────────────

/// A mock public-beacon source. Folds a caller-supplied beacon `output` into the
/// seed and round-trips through [`EvidenceKind::Beacon`]. It does **not** verify
/// the beacon's signature/finality — that needs the real beacon infra — so it is
/// suitable for tests and wiring, not for a non-grindability guarantee.
#[derive(Clone, Debug)]
pub struct MockBeacon {
    /// Beacon identity.
    pub beacon_id: Vec<u8>,
    /// The future round fixed by the request acknowledgement.
    pub round: u64,
    /// The beacon output for that round.
    pub output: [u8; 32],
}

impl MockBeacon {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"beacon";

    fn source_output(beacon_id: &[u8], round: u64, output: &[u8; 32]) -> Vec<u8> {
        let mut out = Vec::with_capacity(beacon_id.len() + 8 + 32);
        out.extend_from_slice(&(beacon_id.len() as u64).to_le_bytes());
        out.extend_from_slice(beacon_id);
        out.extend_from_slice(&round.to_le_bytes());
        out.extend_from_slice(output);
        out
    }
}

impl RandomnessSource for MockBeacon {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let output = Self::source_output(&self.beacon_id, self.round, &self.output);
        let seed = derive_seed(&req.event_id(), Self::TAG, &output);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::Beacon {
                beacon_id: self.beacon_id.clone(),
                round: self.round,
                output: self.output,
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::Beacon {
            beacon_id,
            round,
            output,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };
        let src = Self::source_output(beacon_id, *round, output);
        let seed = derive_seed(&req.event_id(), Self::TAG, &src);
        check_transcript(seed, req, ev)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ServerVrf — the real post-quantum LB-VRF source (`pqvrf`, Esgin et al. Set I).
// ─────────────────────────────────────────────────────────────────────────────

/// Domain tag for the per-event LB-VRF key commitment (the request-binding model).
pub const DOMAIN_LB_VRF_KEY_COMMITMENT: &[u8] = b"dregg-dice/lb-vrf/key-commitment/v1";

/// A producer-side error from [`ServerVrf::try_evidence`].
///
/// The trait's infallible [`RandomnessSource::evidence`] panics on these; real
/// producers call [`ServerVrf::try_evidence`] to handle them. Both are load-bearing
/// for the **one-time** discipline: Set I permits exactly one evaluation per key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VrfEvalError {
    /// This `ServerVrf`'s one-time key was already consumed by a prior evaluation.
    /// Set I is one-time; mint a fresh [`ServerVrf`] (a new key epoch) per event.
    KeyConsumed,
    /// The underlying `pqvrf::eval` failed (its one-time budget, or a sampling abort).
    Backend(pqvrf::EvalError),
}

impl core::fmt::Display for VrfEvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::KeyConsumed => f.write_str(
                "LB-VRF key already consumed — Set I is one-time; mint a fresh ServerVrf per event",
            ),
            Self::Backend(e) => write!(f, "LB-VRF eval failed: {e}"),
        }
    }
}

impl std::error::Error for VrfEvalError {}

/// A server randomness source backed by the one-time post-quantum **LB-VRF**
/// (`pqvrf`, Esgin et al. FC 2021, Set I).
///
/// # What it wraps
///
/// The VRF input is the draw's [`EventId`] bytes (which already bind
/// game/seq/pre-state/action/purpose/draw-count). Producing evidence runs one
/// `pqvrf::eval` over that input, yielding `(output, proof)`; the recorded
/// [`EvidenceKind::LbVrf`] carries the public key, output, and proof. The pure
/// [`RandomnessSource::seed`] verifier re-runs `pqvrf::verify(&pk, event_id,
/// &output, &proof)` and, only on success, derives the [`Seed`] over the
/// **verified** output via the same domain-separated [`derive_seed`] every source
/// ends with. A forged output or proof — one the LB-VRF secret never produced for
/// this input — fails `pqvrf::verify`; its uniqueness reduces to Module-SIS. That
/// is escape-hatch #4 (one-output-per-input) closed with a lattice primitive, in
/// place of the rejected classical ECVRF.
///
/// # The one-time key model (per-event key committed in the request)
///
/// Set I permits **one** evaluation per key ([`pqvrf::MAX_EVALUATIONS`] = 1), so
/// each random event needs its own key epoch. This crate uses the simpler of the
/// two correct models: a **per-event key committed in the request**. The event's
/// public key (or its [`ServerVrf::key_commitment`]) is bound into the request
/// *before the draw* — the request commitment is stored first — so a verifier
/// checks the proof under the key the request committed to and the server cannot
/// swap in a fresh, favourable key after seeing the outcome. It is simpler than a
/// genesis-committed key-chain (which needs a Merkle root + per-epoch membership
/// proof, indexed by `seq`) and needs no extra committed state: the existing
/// request/[`EventId`] binding carries the key. `ServerVrf` enforces the one-eval
/// rule two ways — `pqvrf::SecretKey`'s own budget counter, and by *burning* its
/// key on first use ([`ServerVrf::try_evidence`] returns [`VrfEvalError::KeyConsumed`]
/// on a second call).
///
/// **Assurance.** Output pseudorandomness rests on MLWE (assumed; `pqvrf`'s
/// undischarged `Pseudorandom` obligation). Uniqueness (the one-output tooth this
/// source uses) reduces to Module-SIS. Genesis key binding, a real delayed beacon,
/// and timeout-no-reroll (hatches #1/#2/#5) remain the [`Hybrid`] follow-up.
pub struct ServerVrf {
    /// The one-time LB-VRF secret key for this event epoch — consumed on first eval.
    key: RefCell<Option<pqvrf::SecretKey>>,
    /// The corresponding public key (the verification anchor recorded in evidence).
    public_key: pqvrf::PublicKey,
}

impl core::fmt::Debug for ServerVrf {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ServerVrf")
            .field("public_key", &self.public_key)
            .field("key_consumed", &self.key.borrow().is_none())
            .finish()
    }
}

impl ServerVrf {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"lb-vrf";

    /// Mint a fresh one-time key epoch from a 32-byte key seed (via `pqvrf::keygen`).
    ///
    /// Each event MUST use a distinct `ServerVrf` (a distinct key seed): Set I is
    /// one-time, and evaluating a key on a second input would break the scheme.
    pub fn from_key_seed(seed: &[u8; 32]) -> ServerVrf {
        let (public_key, secret_key) = pqvrf::keygen(seed);
        ServerVrf {
            key: RefCell::new(Some(secret_key)),
            public_key,
        }
    }

    /// This epoch's LB-VRF public key.
    pub fn public_key(&self) -> &pqvrf::PublicKey {
        &self.public_key
    }

    /// This epoch's LB-VRF public key in canonical bytes (as recorded in evidence).
    pub fn public_key_bytes(&self) -> Vec<u8> {
        encode_public_key(&self.public_key)
    }

    /// Whether this source's one-time key has already been consumed.
    pub fn key_consumed(&self) -> bool {
        self.key.borrow().is_none()
    }

    /// The domain-separated commitment to a public key, `H(DOMAIN || pk_bytes)` — the
    /// value a request binds (e.g. into `game_binding`) to pin THIS key epoch before
    /// the draw. A verifier that recomputes it from the evidence's public key and
    /// compares it to the request's committed value detects a swapped key.
    pub fn key_commitment(public_key_bytes: &[u8]) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_LB_VRF_KEY_COMMITMENT);
        absorb_len_prefixed(&mut h, public_key_bytes);
        *h.finalize().as_bytes()
    }

    /// Produce LB-VRF evidence for `req`, consuming this epoch's one-time key.
    ///
    /// Runs a single `pqvrf::eval` with VRF input = the request's [`EventId`] bytes,
    /// then derives the seed over the verified output and records the draw transcript.
    /// A second call returns [`VrfEvalError::KeyConsumed`] — the one-time guarantee.
    pub fn try_evidence(
        &self,
        req: &RandomnessRequest,
    ) -> Result<RandomnessEvidence, VrfEvalError> {
        let mut slot = self.key.borrow_mut();
        let secret_key = slot.as_mut().ok_or(VrfEvalError::KeyConsumed)?;
        let event_id = req.event_id();
        let (output, proof) =
            pqvrf::eval(secret_key, event_id.as_bytes()).map_err(VrfEvalError::Backend)?;
        // Burn the key: Set I is one-time. (pqvrf's own budget counter also refuses a
        // second eval; this additionally drops the secret and yields a crisp error.)
        *slot = None;

        let output_bytes = encode_output(&output);
        let seed = derive_seed(&event_id, Self::TAG, &output_bytes);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        Ok(RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::LbVrf {
                public_key: encode_public_key(&self.public_key),
                output: output_bytes,
                proof: encode_proof(&proof),
            },
            draw_transcript_commitment: commitment,
        })
    }
}

impl RandomnessSource for ServerVrf {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        self.try_evidence(req).expect(
            "ServerVrf::evidence: the one-time LB-VRF key is exhausted or eval aborted — \
             use ServerVrf::try_evidence to handle one-time exhaustion",
        )
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::LbVrf {
            public_key,
            output,
            proof,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };
        // Decode the untrusted byte fields into pqvrf structures (canonical lengths).
        let public_key = decode_public_key(public_key)?;
        let output = decode_output(output)?;
        let proof = decode_proof(proof)?;
        // THE ONE-OUTPUT TOOTH: re-run pqvrf::verify under the recorded key and the
        // request's event id. A forged output/proof (not the LB-VRF value for this
        // input) is rejected here — uniqueness reduces to Module-SIS.
        let event_id = req.event_id();
        if !pqvrf::verify(&public_key, event_id.as_bytes(), &output, &proof) {
            return Err(VerifyError::VrfProofInvalid);
        }
        // Only now — over the VERIFIED output — derive the seed and check the transcript.
        let seed = derive_seed(&event_id, Self::TAG, &encode_output(&output));
        check_transcript(seed, req, ev)
    }
}

// ── LB-VRF ⇄ bytes codec. pqvrf ships no wire format; these are canonical
//    little-endian encodings of its public structs, with strict length checks on
//    decode so a malformed evidence field is rejected before the proof check. ──

fn encode_public_key(pk: &pqvrf::PublicKey) -> Vec<u8> {
    let mut out = Vec::with_capacity(pqvrf::MSIS_RANK * pqvrf::DEGREE * 4);
    for poly in &pk.t {
        for &c in &poly.coefficients {
            out.extend_from_slice(&c.to_le_bytes());
        }
    }
    out
}

fn decode_public_key(bytes: &[u8]) -> Result<pqvrf::PublicKey, VerifyError> {
    let expected = pqvrf::MSIS_RANK * pqvrf::DEGREE * 4;
    if bytes.len() != expected {
        return Err(VerifyError::MalformedVrfEvidence(
            "LB-VRF public key has the wrong byte length",
        ));
    }
    let mut it = bytes.chunks_exact(4);
    let t = core::array::from_fn(|_| {
        let coefficients = core::array::from_fn(|_| {
            let c = it.next().expect("length checked above");
            u32::from_le_bytes([c[0], c[1], c[2], c[3]])
        });
        pqvrf::PublicPolynomial { coefficients }
    });
    Ok(pqvrf::PublicKey { t })
}

fn encode_output(output: &pqvrf::Output) -> Vec<u8> {
    let mut out = Vec::with_capacity(pqvrf::OUTPUT_DEGREE * 4);
    for &c in &output.coefficients {
        out.extend_from_slice(&c.to_le_bytes());
    }
    out
}

fn decode_output(bytes: &[u8]) -> Result<pqvrf::Output, VerifyError> {
    if bytes.len() != pqvrf::OUTPUT_DEGREE * 4 {
        return Err(VerifyError::MalformedVrfEvidence(
            "LB-VRF output has the wrong byte length",
        ));
    }
    let mut it = bytes.chunks_exact(4);
    let coefficients = core::array::from_fn(|_| {
        let c = it.next().expect("length checked above");
        u32::from_le_bytes([c[0], c[1], c[2], c[3]])
    });
    Ok(pqvrf::Output { coefficients })
}

fn encode_proof(proof: &pqvrf::Proof) -> Vec<u8> {
    let mut out = Vec::with_capacity(pqvrf::SECRET_WIDTH * pqvrf::DEGREE * 4 + pqvrf::DEGREE);
    for poly in &proof.response {
        for &c in &poly.coefficients {
            out.extend_from_slice(&c.to_le_bytes());
        }
    }
    for &c in &proof.challenge.coefficients {
        out.extend_from_slice(&c.to_le_bytes());
    }
    out
}

fn decode_proof(bytes: &[u8]) -> Result<pqvrf::Proof, VerifyError> {
    let response_len = pqvrf::SECRET_WIDTH * pqvrf::DEGREE * 4;
    let expected = response_len + pqvrf::DEGREE;
    if bytes.len() != expected {
        return Err(VerifyError::MalformedVrfEvidence(
            "LB-VRF proof has the wrong byte length",
        ));
    }
    let (response_bytes, challenge_bytes) = bytes.split_at(response_len);
    let mut it = response_bytes.chunks_exact(4);
    let response = core::array::from_fn(|_| {
        let coefficients = core::array::from_fn(|_| {
            let c = it.next().expect("length checked above");
            i32::from_le_bytes([c[0], c[1], c[2], c[3]])
        });
        pqvrf::ResponsePolynomial { coefficients }
    });
    let challenge = pqvrf::ChallengePolynomial {
        coefficients: core::array::from_fn(|i| challenge_bytes[i] as i8),
    };
    Ok(pqvrf::Proof {
        response,
        challenge,
    })
}

/// The recommended hybrid: a delayed public beacon plus a registered server VRF
/// (with commit-reveal only as an offline fallback).
///
/// TODO(hybrid-backend): the hybrid seed folds a finalized beacon round + output
/// and an LB-VRF output/proof (the [`ServerVrf`] leg is now real) over the
/// transition context. It still needs beacon verification and a genesis-committed
/// key-chain (hatches #1/#2/#5). The shape is fixed here; `seed` fails closed with
/// [`VerifyError::BackendUnavailable`].
#[derive(Clone, Debug, Default)]
pub struct Hybrid {
    /// The registered VRF public key.
    pub vrf_public_key: Vec<u8>,
    /// The beacon identity the hybrid draws from.
    pub beacon_id: Vec<u8>,
}

impl RandomnessSource for Hybrid {
    fn evidence(&self, _req: &RandomnessRequest) -> RandomnessEvidence {
        unimplemented!(
            "Hybrid::evidence requires a beacon + VRF backend; this slice fixes the shape only"
        )
    }

    fn seed(_req: &RandomnessRequest, _ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        Err(VerifyError::BackendUnavailable(
            "Hybrid: requires a delayed-beacon + registered-VRF backend — the recommended endpoint, a follow-up",
        ))
    }
}
