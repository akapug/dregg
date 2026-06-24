//! **The chat IS the dregg world** — the room↔cell, identity↔cell, and
//! send↔turn mappings that make deos-chat a *view over the one cell graph*, not a
//! Matrix silo that happens to render inside deos.
//!
//! This module is the typed realization of `docs/deos/APPS-AS-CELLS.md` §3 ("CHAT
//! — room = a cell, messages = its history"). It is deliberately
//! dependency-light: it does NOT pull the `cell`/`turn`/`world` crates into
//! deos-matrix's standalone tokio/gpui graph. Instead it defines the *shapes* the
//! deos side binds to (named per-field against the real machinery), so the seam is
//! a typed contract rather than prose. The host comms-PD — where the executor and
//! firmament caps live — supplies the live binding; deos-chat only ever holds
//! these serializable surfaces.
//!
//! ## The three weldpoints (census, not from-scratch)
//!
//! 1. **ROOM = a CELL** ([`RoomCell`]). A Matrix room's durable core — its
//!    membership, its "who may post" permission, and its message history — is a
//!    `Cell` (`cell/src/cell.rs`). The messages are the cell's *turn history* (the
//!    receipt chain, `turn/src/collapse.rs`); a send is a turn appending to the
//!    room cell. What stays ephemeral (rendered timeline, typing, draft) is NOT in
//!    the cell — only the durable object is.
//! 2. **IDENTITY = a CELL** ([`IdentityCell`]). A Matrix user `@user:server` ties
//!    to a deos `CellId`. The user's device keys (the E2E/vodozemac identity) are
//!    *caps* the identity cell holds — "device-keys-as-caps" (README). Verifying a
//!    person (nheko's "verify the person, not the device") is verifying the
//!    identity cell's root, under which every device cap hangs.
//! 3. **SEND = a TURN** ([`SendReceipt`]). Every message-send is *conceptually* a
//!    turn: it spends the sender's post-cap on the room cell and appends the
//!    message to the room's history, leaving a verifiable [`SendReceipt`]. The
//!    mock produces a sketch receipt (no live executor); the deos side produces a
//!    byte-identical `TurnReceipt`.

use serde::{Deserialize, Serialize};

/// A deos `CellId`: the 32-byte content-address of a cell in the ledger. Grounds
/// in `cell::CellId` (`cell/src/cell.rs`). Here it is just the bytes so the chat
/// client can name cells without depending on the cell crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CellId(pub [u8; 32]);

impl CellId {
    /// A deterministic, dependency-free cell id derived from a stable string key
    /// (a room id, a user id). The deos side uses the real content-address; this
    /// stand-in is stable across runs so the room↔cell mapping is testable and the
    /// UI can show a consistent short id. FNV-1a expanded to 32 bytes.
    pub fn derive(key: &str) -> Self {
        // Eight independent FNV-1a streams (different seeds) → 8×4 = 32 bytes, so
        // the whole id varies with the key (not just the first 4 bytes).
        let mut out = [0u8; 32];
        for (lane, chunk) in out.chunks_mut(4).enumerate() {
            let mut h: u32 = 2166136261u32.wrapping_add((lane as u32).wrapping_mul(0x9E3779B1));
            for b in key.bytes() {
                h = (h ^ b as u32).wrapping_mul(16777619);
            }
            chunk.copy_from_slice(&h.to_be_bytes());
        }
        CellId(out)
    }

    /// A short hex tag for display (`cell:abcd1234`).
    pub fn short(&self) -> String {
        let mut s = String::with_capacity(8);
        for b in &self.0[..4] {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }
}

/// **ROOM = a CELL.** The durable core of a Matrix room as a deos cell.
///
/// The room's `display_name`/`topic`/membership are *cell state*; the message
/// history is the cell's *turn history*; "who may post" is a *cap* in the cell's
/// c-list. This struct is the chat-side projection of that cell — what the UI
/// shows of the room's cell membership. The deos side resolves [`Self::cell_id`]
/// to the live `Cell` and folds its history.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoomCell {
    /// The cell this room IS. Derived from the Matrix room id (`!room:server`).
    pub cell_id: CellId,
    /// The Matrix room id this cell projects (`!room:server`).
    pub room_id: String,
    /// The number of turns committed against this room cell == the message count
    /// in the durable history (the receipt chain length). The mock tracks this so
    /// the UI can show "N turns" honestly.
    pub turn_count: u64,
    /// The room cell's current state root (the Merkle tooth a light client checks).
    /// Grounds in `World::state_root() -> [u8; 32]`. The mock recomputes it from
    /// the history so it is non-fabricated within the mock world.
    pub state_root: [u8; 32],
}

impl RoomCell {
    /// Map a Matrix room id to its room cell. The deos side resolves the live cell;
    /// this derives a stable id + zero history (filled as turns are observed).
    pub fn for_room(room_id: &str) -> Self {
        RoomCell {
            cell_id: CellId::derive(room_id),
            room_id: room_id.to_string(),
            turn_count: 0,
            state_root: [0u8; 32],
        }
    }
}

/// **IDENTITY = a CELL.** A Matrix user tied to a deos identity cell.
///
/// `@user:server` ↔ a `CellId`. The user's device keys are caps the identity cell
/// holds (device-keys-as-caps). "Verify the person, not the device" (nheko)
/// becomes: verify the *identity cell's root*, under which every device cap hangs
/// — so cross-signing one identity verifies all its devices at once.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentityCell {
    /// The cell this user IS.
    pub cell_id: CellId,
    /// The Matrix user id (`@user:server`).
    pub user_id: String,
    /// The person-level trust verdict (the identity cell root state), DERIVED from
    /// cross-signing — never the per-device key alone.
    pub trust: PersonTrust,
}

impl IdentityCell {
    /// Map a Matrix user id to its identity cell.
    pub fn for_user(user_id: &str, trust: PersonTrust) -> Self {
        IdentityCell {
            cell_id: CellId::derive(user_id),
            user_id: user_id.to_string(),
            trust,
        }
    }
}

/// Person-level trust — "verify the person, not the device" (nheko's correctness
/// principle). This is the identity *cell's* verdict, not a single device key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PersonTrust {
    /// Cross-signed and verified by us — the identity cell root is trusted; every
    /// device hanging under it inherits the trust.
    Verified,
    /// Known identity, not yet verified (we have their cross-signing master key but
    /// have not signed it).
    Unverified,
    /// A device or identity changed since last seen — a possible MITM; the UI must
    /// surface this loudly (fail-visible, never fail-silent).
    Changed,
}

impl PersonTrust {
    /// A compact glyph for the trust badge.
    pub fn glyph(self) -> &'static str {
        match self {
            PersonTrust::Verified => "✓",
            PersonTrust::Unverified => "?",
            PersonTrust::Changed => "⚠",
        }
    }

    /// A human label for a tooltip / status line.
    pub fn label(self) -> &'static str {
        match self {
            PersonTrust::Verified => "verified — identity cell root cross-signed",
            PersonTrust::Unverified => "unverified — identity known, not yet signed",
            PersonTrust::Changed => "CHANGED — identity/device changed since last seen",
        }
    }
}

/// **SEND = a TURN.** The receipt a message-send leaves.
///
/// On the deos side this is a real `TurnReceipt` (`turn/src/collapse.rs`): the
/// send spent the sender's post-cap on the room cell and appended the message to
/// the room's history, conserving (a message carries no value, so Σδ=0 trivially)
/// and leaving an independently verifiable receipt. The mock produces a sketch
/// receipt with the same *shape* (pre/post root, turn index) so the send path is
/// receipted end-to-end even offline.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SendReceipt {
    /// The room cell the turn committed against.
    pub room_cell: CellId,
    /// The identity cell that authored the turn (the sender).
    pub author_cell: CellId,
    /// The Matrix event id the send produced (the message's wire identity).
    pub event_id: String,
    /// This turn's index in the room cell's history (== prior turn_count).
    pub turn_index: u64,
    /// The room cell root after the turn (the new tooth).
    pub post_root: [u8; 32],
}

impl SendReceipt {
    /// A one-line human digest for the UI ("turn 4 · cell:abcd · root ef01…").
    pub fn digest(&self) -> String {
        let mut root = String::with_capacity(8);
        for b in &self.post_root[..4] {
            root.push_str(&format!("{b:02x}"));
        }
        format!(
            "turn {} · {} · root {}…",
            self.turn_index,
            self.room_cell.short(),
            root
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cell_id_is_stable_and_varies() {
        // Stable across calls.
        assert_eq!(
            CellId::derive("!room:server"),
            CellId::derive("!room:server")
        );
        // Different keys → different ids (the whole 32 bytes, not just a prefix).
        let a = CellId::derive("@ember:deos.local");
        let b = CellId::derive("@grok:deos.local");
        assert_ne!(a, b);
        assert_ne!(a.0, b.0);
        // And the full id varies, not only the leading word.
        assert_ne!(a.0[16..], b.0[16..]);
    }

    #[test]
    fn room_maps_to_a_cell() {
        let rc = RoomCell::for_room("!deoslab:deos.local");
        assert_eq!(rc.cell_id, CellId::derive("!deoslab:deos.local"));
        assert_eq!(rc.turn_count, 0);
    }

    #[test]
    fn identity_maps_to_a_cell_with_person_trust() {
        let id = IdentityCell::for_user("@ember:deos.local", PersonTrust::Verified);
        assert_eq!(id.cell_id, CellId::derive("@ember:deos.local"));
        assert_eq!(id.trust, PersonTrust::Verified);
        assert_eq!(id.trust.glyph(), "✓");
    }

    #[test]
    fn send_receipt_round_trips_and_digests() {
        let r = SendReceipt {
            room_cell: CellId::derive("!r:s"),
            author_cell: CellId::derive("@me:s"),
            event_id: "$evt1".into(),
            turn_index: 3,
            post_root: [0xef; 32],
        };
        let json = serde_json::to_string(&r).unwrap();
        let back: SendReceipt = serde_json::from_str(&json).unwrap();
        assert_eq!(r, back);
        assert!(r.digest().starts_with("turn 3 · "));
        assert!(r.digest().contains("efefefef"));
    }
}
