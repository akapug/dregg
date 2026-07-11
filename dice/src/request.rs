//! Request / evidence structures and the receipt-shaped request commitment.

use serde::{Deserialize, Serialize};

use crate::event::EventId;
use crate::util::absorb_len_prefixed;

/// The derivation version this build produces. Bound into evidence so a verifier
/// rejects evidence from an incompatible derivation.
pub const DERIVATION_VERSION: u32 = 1;

/// Domain tag for the receipt-shaped request commitment.
pub const DOMAIN_REQUEST_COMMITMENT: &[u8] = b"dregg-dice/request-commitment/v1";

/// Everything that must be bound *before* the randomness result is known.
///
/// Mirrors the design's randomness-context inputs: the game/sequence/pre-state/
/// action, the purpose (`event_kind`), and how many draws (`draw_count`) the
/// event consumes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RandomnessRequest {
    /// The committed game identity (opaque bytes; production binds a VRF key
    /// epoch + ruleset hash into this).
    pub game_binding: Vec<u8>,
    /// Transition sequence number.
    pub seq: u64,
    /// Committed pre-state root this draw resolves against.
    pub pre_state_root: [u8; 32],
    /// Commitment to the finalized typed action.
    pub action_hash: [u8; 32],
    /// Purpose tag, domain-separating subsystems (`"combat/hit"`, `"loot"`, …).
    pub event_kind: String,
    /// Number of indexed draws this event consumes.
    pub draw_count: u32,
}

impl RandomnessRequest {
    /// The [`EventId`] this request derives — the seed's binding context.
    pub fn event_id(&self) -> EventId {
        EventId::derive(
            &self.game_binding,
            self.seq,
            &self.pre_state_root,
            &self.action_hash,
            &self.event_kind,
            self.draw_count,
        )
    }

    /// A receipt-shaped commitment the game engine would store **before** the
    /// result exists. It binds the full request (via its `EventId`) so the stored
    /// receipt fixes the game, sequence, pre-state, action, purpose, and draw
    /// count in advance.
    ///
    /// The actual `attested-dm` `LedgerEntry` integration — carrying this
    /// alongside the transition receipt — is a documented follow-up, not part of
    /// this crate.
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_REQUEST_COMMITMENT);
        h.update(self.event_id().as_bytes());
        *h.finalize().as_bytes()
    }
}

/// Source-specific evidence needed to re-derive and check a seed.
///
/// Each variant carries exactly what its verifier needs. This slice fully
/// implements [`Deterministic`](EvidenceKind::Deterministic),
/// [`CommitReveal`](EvidenceKind::CommitReveal), a mock
/// [`Beacon`](EvidenceKind::Beacon), and the real post-quantum
/// [`LbVrf`](EvidenceKind::LbVrf) (backed by the `pqvrf` LB-VRF).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EvidenceKind {
    /// A test/offline deterministic source keyed on a caller-supplied context.
    Deterministic {
        /// Contribution folded into the seed alongside the event id.
        context: [u8; 32],
    },
    /// Two-party commit-reveal. The server commits to `server_reveal` first, then
    /// both contributions feed the seed.
    CommitReveal {
        /// `H(DOMAIN_COMMIT || server_reveal)` — published before the reveal.
        server_commitment: [u8; 32],
        /// The opened server contribution.
        server_reveal: [u8; 32],
        /// The player's contribution.
        player_contribution: [u8; 32],
    },
    /// A public randomness beacon output (mocked here — this slice does not
    /// verify the beacon's own signature/finality; that needs the beacon infra).
    Beacon {
        /// Beacon identity.
        beacon_id: Vec<u8>,
        /// The future round fixed by the request acknowledgement.
        round: u64,
        /// The beacon's output for that round.
        output: [u8; 32],
    },
    /// A post-quantum **LB-VRF** output + proof (Esgin et al. FC 2021, Set I; the
    /// `pqvrf` crate). The VRF input is the draw's [`EventId`] bytes; the verifier
    /// re-runs `pqvrf::verify(&pk, event_id, &output, &proof)` and, on success,
    /// derives the seed over the *verified* output. Uniqueness of the accepted
    /// output for a given `(pk, input)` reduces to Module-SIS, so a forged output
    /// or proof is rejected — the one-output-per-input guarantee. All three fields
    /// are the `pqvrf` structures in their canonical little-endian byte encoding
    /// (see `ServerVrf`'s codec); a wrong length is rejected as malformed.
    LbVrf {
        /// The LB-VRF public key `t = A*s` (canonical LE bytes).
        public_key: Vec<u8>,
        /// The LB-VRF output `v` (canonical LE bytes).
        output: Vec<u8>,
        /// The LB-VRF proof `(z, c)` (canonical LE bytes), re-checked by `pqvrf::verify`.
        proof: Vec<u8>,
    },
}

/// The randomness evidence recorded alongside a transition, mirroring the
/// design's `randomness_context`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RandomnessEvidence {
    /// Derivation version the evidence was produced under.
    pub derivation_version: u32,
    /// The source-specific opening.
    pub source: EvidenceKind,
    /// A commitment to the exact draw transcript
    /// ([`DrawStream::transcript_commitment`](crate::DrawStream::transcript_commitment)).
    /// The verifier recomputes this from the re-derived seed and rejects a
    /// mismatch — the grinding tooth.
    pub draw_transcript_commitment: [u8; 32],
}
