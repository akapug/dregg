//! `EventId` — domain-separated binding of a randomness draw to its full context.
//!
//! The `EventId` is the single value the seed derivation is keyed on. Because it
//! binds `draw_count` and `event_kind` *before the seed exists*, neither party can
//! grind by changing how many draws are taken or which subsystem they feed: any
//! such change moves the `EventId`, hence the seed, hence every draw and the
//! transcript commitment — a detectable mismatch at verification.

use serde::{Deserialize, Serialize};

use crate::util::absorb_len_prefixed;

/// Domain tag for the `EventId` object. Distinct from every other hashed object
/// in the crate so an `EventId` preimage can never collide with a seed, a
/// request commitment, a draw, or a transcript.
pub const DOMAIN_EVENT_ID: &[u8] = b"dregg-dice/event-id/v1";

/// A 32-byte identifier binding a randomness draw to its game, sequence,
/// pre-state, action, purpose (`event_kind`), and draw count.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EventId([u8; 32]);

impl EventId {
    /// Derive the event id from the full transition context.
    ///
    /// - `game_binding` — the committed game identity (ideally already binding a
    ///   VRF key epoch and ruleset hash; opaque bytes here).
    /// - `seq` — the transition sequence number.
    /// - `pre_state_root` — the committed pre-state this draw resolves against.
    /// - `action_hash` — a commitment to the finalized typed action.
    /// - `event_kind` — a purpose tag (`"combat/hit"`, `"loot"`, …) so draws for
    ///   different subsystems are domain-separated and cannot influence one another.
    /// - `draw_count` — how many indexed draws this event consumes; bound here so
    ///   it cannot be varied after the fact.
    pub fn derive(
        game_binding: &[u8],
        seq: u64,
        pre_state_root: &[u8; 32],
        action_hash: &[u8; 32],
        event_kind: &str,
        draw_count: u32,
    ) -> EventId {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_EVENT_ID);
        absorb_len_prefixed(&mut h, game_binding);
        h.update(&seq.to_le_bytes());
        h.update(pre_state_root);
        h.update(action_hash);
        absorb_len_prefixed(&mut h, event_kind.as_bytes());
        h.update(&draw_count.to_le_bytes());
        EventId(*h.finalize().as_bytes())
    }

    /// The raw 32 bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl core::fmt::Debug for EventId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "EventId(")?;
        for b in &self.0[..4] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…)")
    }
}
