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
// ServerVrf / Hybrid — DESIGNED, not implemented. Shape is fixed; the backend
// (a registered-key VRF; the delayed-beacon hybrid seed) is a follow-up.
// ─────────────────────────────────────────────────────────────────────────────

/// A server VRF source with a registered key.
///
/// TODO(vrf-backend): verifying a VRF proof requires a VRF backend (e.g. an
/// ECVRF / RFC 9381 implementation over the registered key). The trait shape and
/// the [`EvidenceKind::Vrf`] evidence variant are fixed here so the backend drops
/// in without a redesign. `evidence` is unimplemented; `seed` returns
/// [`VerifyError::BackendUnavailable`] so downstream code fails closed.
#[derive(Clone, Debug, Default)]
pub struct ServerVrf {
    /// The registered VRF public key (verification anchor).
    pub public_key: Vec<u8>,
}

impl RandomnessSource for ServerVrf {
    fn evidence(&self, _req: &RandomnessRequest) -> RandomnessEvidence {
        unimplemented!(
            "ServerVrf::evidence requires a VRF backend (registered-key ECVRF); \
             this slice fixes the trait/evidence shape only"
        )
    }

    fn seed(_req: &RandomnessRequest, _ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        Err(VerifyError::BackendUnavailable(
            "ServerVrf: requires a registered-key VRF backend (ECVRF/RFC 9381) — a follow-up",
        ))
    }
}

/// The recommended hybrid: a delayed public beacon plus a registered server VRF
/// (with commit-reveal only as an offline fallback).
///
/// TODO(hybrid-backend): the hybrid seed folds a finalized beacon round + output
/// and a VRF output/proof over the transition context. It needs both the beacon
/// verification and the VRF backend. The shape is fixed here; `seed` fails closed
/// with [`VerifyError::BackendUnavailable`].
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
