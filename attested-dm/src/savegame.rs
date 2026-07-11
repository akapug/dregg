//! # savegame — portable SAVE / LOAD persistence for an attested game session.
//!
//! A [`GameSession`] is a live thing: the static [`GameWorld`], the attested + cap-bounded DM,
//! the [`WorldCell`] state (scene / flags / inventory), the tamper-evident receipt ledger, and
//! the verifiable-randomness provider. This module serializes exactly what is needed to **replay
//! AND continue** a session to a portable [`SaveGame`] (JSON via serde), and [`GameSession::load`]
//! reconstructs the session and **re-verifies it fail-closed** before handing it back — a
//! tampered or corrupt save is REFUSED, never silently resumed.
//!
//! ## What a `SaveGame` captures, and why it suffices
//!
//! * **The world identity** — a [`SaveGame::world_fingerprint`] over the static map, so `load`
//!   can confirm the caller supplied the SAME [`GameWorld`] the session was played on (a
//!   [`LoadError::WorldMismatch`] otherwise). The map itself is NOT serialized: it is pure,
//!   immutable ruleset data reconstructed by the caller (a bundled constructor like
//!   [`crate::sunken_vault`], or [`crate::parse_dungeon`] over a `.dungeon` source). The
//!   fingerprint is the registry hook; the from-genesis replay (below) is the true correctness
//!   check that the provided map reproduces the recorded history.
//! * **The current [`WorldCell`] state** — `scene`, `flags` (the light budget, combat wounds,
//!   door/quest flags all live here), and `inventory`. Captured verbatim AND re-checked against
//!   the state the ledger reproduces on re-execution, so a tampered saved flag is caught.
//! * **The full receipt ledger** — every landed turn's `seq`, `prev`, `receipt`, narration,
//!   effect, prompt-binding, game-binding, and **verifiable-randomness record** (a loot draw's
//!   [`crate::RandomnessRecord`] rides through unchanged, so a mid-loot-game save re-verifies).
//!   The per-turn [`crate::ZkOracleAttestation`] is NOT stored; it is a deterministic function of
//!   the pinned notary seed + the recorded (already-cleaned) narration, so `load` re-derives the
//!   identical attestation. The 32-byte `receipt` id — the on-ledger fingerprint — IS captured
//!   and re-checked, so tampering any recorded field is caught fail-closed.
//! * **The DM notary seed + the randomness provider** — [`SaveGame::dm_seed`] pins the modeled
//!   attestation carrier (so re-derived attestations verify against the same anchor), and the
//!   [`SessionRandomness`] provider is carried so future loot draws continue identically.
//!
//! ## Load verifies on BOTH tiers (fail-closed)
//!
//! [`GameSession::load`] refuses a save unless, in order: (1) the map fingerprint matches; (2)
//! the rebuilt ledger passes [`WorldCell::verify_ledger`] — the **integrity tier**: the stored
//! receipts recompute and the (re-derived) attestations verify, so a tampered recorded field
//! (an effect, an action, a narration) that no longer recomputes its stored receipt is caught
//! ([`LoadError::ChainBroken`]); (3) the ledger passes [`crate::verify_ledger_replay`] against the
//! map — the **re-execution tier**: every recorded effect is the rule-correct resolution of its
//! bound action from genesis, so a rule-incorrect effect on a re-linked (chain-valid) forgery is
//! caught ([`LoadError::ReplayMismatch`]); (4) the saved `scene`/`flags`/`inventory` equal the
//! state that re-execution reproduces (a tampered saved flag → [`LoadError::WorldMismatch`]).
//!
//! ## Honest scope — deterministic-replay persistence, not a snapshot of external randomness
//!
//! This is **deterministic-replay** persistence. It captures everything a re-executor needs to
//! re-derive and re-check the whole history and to continue it identically — under the **default
//! modeled attestation carrier** (the pinned [`crate::FixtureNotary`]), whose attestations are a
//! pure function of `(seed, narration)`. A `tlsn-live` session's REAL MPC-TLS presentation bytes
//! are not reproducible from a seed and are not captured by this v1 format (they would ride as an
//! extra serialized `Vec<u8>` per entry — a named extension). The carried [`SessionRandomness`]
//! embeds the session's commit-reveal secrets so future draws stay reconstructible; a real
//! deployment re-establishes those per session from a fresh handshake rather than persisting them.
//! Federation routing ([`crate::WorldCell::node_target`]) is environment-configured, not part of a
//! save; a loaded session opens `Local` and can be re-pointed at a node by the caller.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::game::{GameWorld, ReplayMismatch, SessionRandomness};
use crate::{
    DmAttestationCarrier, GameBinding, LedgerBreak, LedgerEntry, PromptBinding, RandomnessRecord,
    WorldCell, WorldEffect,
};

/// The savegame wire-format version. Bumped on any incompatible change to [`SaveGame`]'s shape;
/// [`GameSession::load`] refuses a version it does not understand ([`LoadError::Decode`]).
pub const SAVEGAME_FORMAT_VERSION: u32 = 1;

/// Domain separator for [`world_fingerprint`] — the map-identity commitment a save records so
/// `load` can confirm the caller supplied the same ruleset. Distinct from every hashed object in
/// the engine so a fingerprint can never be mistaken for a receipt id or a state root.
const WORLD_FINGERPRINT_DOMAIN: &[u8] = b"attested-dm-savegame-world-fingerprint-v1";

/// **A serializable ledger entry** — one landed turn, minus its (re-derivable) attestation. It
/// captures the entry's position (`seq`, `prev`), its on-ledger `receipt` id, and every field the
/// chain link binds (narration / effect / prompt-binding / game-binding / randomness). On
/// [`GameSession::load`] the attestation is re-derived from the pinned notary seed + `narration`
/// and the entry is rebuilt with the STORED `receipt`, so [`WorldCell::verify_ledger`] recomputes
/// the link over exactly these fields and catches any tampering.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SavedEntry {
    /// The turn's sequence number (its index in the ledger).
    pub seq: u64,
    /// The predecessor's receipt id — the hash-chain back-link (or [`crate::genesis_prev`] for the
    /// first entry).
    pub prev: [u8; 32],
    /// The 32-byte receipt id ([`crate::chain_receipt_id`]) this turn landed with — re-checked on
    /// load (a tampered recorded field no longer recomputes it).
    pub receipt: [u8; 32],
    /// The narration the turn carried (the exact cleaned bound field). Re-attesting it reproduces
    /// the turn's attestation.
    pub narration: String,
    /// The world-effect the turn applied, if any.
    pub effect: Option<WorldEffect>,
    /// The input-side prompt binding, if the turn came from a player command.
    pub prompt_binding: Option<PromptBinding>,
    /// The closed typed game move the resolver admitted (the action + room).
    pub game_binding: Option<GameBinding>,
    /// The verifiable-randomness record a random turn (a loot draw) carried.
    pub randomness: Option<RandomnessRecord>,
}

impl SavedEntry {
    /// Project a live [`LedgerEntry`] into its serializable form (dropping the re-derivable
    /// attestation, keeping the receipt).
    fn from_entry(e: &LedgerEntry) -> SavedEntry {
        SavedEntry {
            seq: e.seq,
            prev: e.prev,
            receipt: e.receipt,
            narration: e.narration.clone(),
            effect: e.effect.clone(),
            prompt_binding: e.prompt_binding.clone(),
            game_binding: e.game_binding.clone(),
            randomness: e.randomness.clone(),
        }
    }
}

/// **A portable, serializable snapshot of a [`GameSession`]** — enough to REPLAY and CONTINUE it.
/// Round-trips through JSON ([`SaveGame::to_json`] / [`SaveGame::from_json`]); reconstructed +
/// re-verified by [`GameSession::load`]. See the module docs for exactly what it captures and why
/// that suffices.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SaveGame {
    /// The wire-format version ([`SAVEGAME_FORMAT_VERSION`]).
    pub format_version: u32,
    /// The identity of the static [`GameWorld`] the session was played on ([`world_fingerprint`]).
    pub world_fingerprint: [u8; 32],
    /// The modeled DM notary seed — pins the attestation carrier so re-derived attestations verify
    /// against the same anchor. (A [`GameSession`] uses the default carrier, so this is
    /// [`crate::DEFAULT_DM_SEED`]; recorded explicitly for forward-compatibility.)
    pub dm_seed: [u8; 32],
    /// The verifiable-randomness provider — carried so future loot draws continue identically.
    pub rng: SessionRandomness,
    /// The current scene / room id.
    pub scene: String,
    /// The world flags (light budget, combat wounds, quest flags, …).
    pub flags: BTreeMap<String, i64>,
    /// The held inventory.
    pub inventory: BTreeSet<String>,
    /// The full receipt ledger, in order.
    pub ledger: Vec<SavedEntry>,
}

impl SaveGame {
    /// Serialize to pretty JSON (for a human-readable save file / transcript).
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("a SaveGame is always serializable")
    }

    /// Serialize to compact JSON bytes (the portable wire form).
    pub fn to_json_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(self).expect("a SaveGame is always serializable")
    }

    /// Parse a [`SaveGame`] from JSON. A malformed / truncated save is a [`LoadError::Decode`].
    pub fn from_json(s: &str) -> Result<SaveGame, LoadError> {
        serde_json::from_str(s).map_err(|e| LoadError::Decode(e.to_string()))
    }

    /// The number of landed turns captured.
    pub fn len(&self) -> usize {
        self.ledger.len()
    }

    /// Whether the captured ledger is empty (a fresh, unplayed session).
    pub fn is_empty(&self) -> bool {
        self.ledger.is_empty()
    }
}

/// **Why a save could not be loaded** — each variant names the tooth that bit. Every one is
/// fail-closed: [`GameSession::load`] returns the session ONLY when all checks pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoadError {
    /// The save bytes did not decode into a [`SaveGame`], or carry an unsupported format version.
    Decode(String),
    /// The provided [`GameWorld`] is not the one the session was saved on (its [`world_fingerprint`]
    /// disagrees), OR the saved world state (scene/flags/inventory) does not match the state the
    /// recorded ledger reproduces on re-execution (a tampered saved flag/scene/inventory).
    WorldMismatch {
        /// A legible account of which world check failed.
        reason: String,
    },
    /// The **integrity tier** refused the rebuilt ledger: a stored receipt no longer recomputes, a
    /// chain link is broken, or an (re-derived) attestation fails to verify — a tampered recorded
    /// field. See [`WorldCell::verify_ledger`].
    ChainBroken(LedgerBreak),
    /// The **re-execution tier** refused the ledger: a recorded effect is not the rule-correct
    /// resolution of its bound action against the map (a rule-incorrect effect a chain-valid
    /// forgery carries, or a draw that does not reconstruct). See [`crate::verify_ledger_replay`].
    ReplayMismatch(ReplayMismatch),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Decode(m) => write!(f, "REFUSED (decode): {m}"),
            LoadError::WorldMismatch { reason } => write!(f, "REFUSED (world-mismatch): {reason}"),
            LoadError::ChainBroken(b) => write!(f, "REFUSED (chain integrity): {b}"),
            LoadError::ReplayMismatch(r) => write!(f, "REFUSED (re-execution): {r}"),
        }
    }
}

impl std::error::Error for LoadError {}

/// **A 32-byte identity of a static [`GameWorld`]** — a domain-separated hash over the map's
/// canonical debug encoding. Because the world is pure data whose fields all derive `Debug` and
/// whose maps/sets iterate in sorted order, this encoding is deterministic and covers EVERY rule
/// field (rooms, exits, gates, items, use-rules, hostiles, combat, npcs, dialogue, spells,
/// consumables, statuses, loot, objective, lose, light, start). It is the cheap early
/// [`LoadError::WorldMismatch`] signal on load; full-map correctness (that the provided map
/// actually reproduces the recorded history) is enforced by the from-genesis replay, so this is a
/// fast identity check, not the security boundary.
pub(crate) fn world_fingerprint(map: &GameWorld) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(WORLD_FINGERPRINT_DOMAIN);
    let repr = format!("{map:?}");
    h.update(&(repr.len() as u64).to_le_bytes());
    h.update(repr.as_bytes());
    *h.finalize().as_bytes()
}

/// Rebuild the live ledger from the saved entries: re-derive each turn's deterministic modeled
/// attestation from the pinned carrier + the recorded narration, and reassemble the [`LedgerEntry`]
/// with the STORED receipt. (The stored narration is already the cleaned bound field, and
/// `attest_narration` is idempotent on a cleaned field, so this reproduces the exact attestation
/// the turn carried.) An entry whose narration cannot be attested at all is a corrupt save.
pub(crate) fn rebuild_ledger(
    carrier: &DmAttestationCarrier,
    saved: &[SavedEntry],
) -> Result<Vec<LedgerEntry>, LoadError> {
    let mut ledger = Vec::with_capacity(saved.len());
    for se in saved {
        let (attestation, _field) = carrier.attest_narration(&se.narration).map_err(|e| {
            LoadError::Decode(format!(
                "turn #{}: recorded narration is not attestable ({e:?})",
                se.seq
            ))
        })?;
        ledger.push(LedgerEntry {
            seq: se.seq,
            prev: se.prev,
            narration: se.narration.clone(),
            effect: se.effect.clone(),
            prompt_binding: se.prompt_binding.clone(),
            game_binding: se.game_binding.clone(),
            randomness: se.randomness.clone(),
            attestation,
            receipt: se.receipt,
        });
    }
    Ok(ledger)
}

/// The world state a from-genesis re-execution of `ledger` reproduces — a fresh
/// [`GameWorld::new_world`] advanced by each entry's recorded effect in order. Called AFTER
/// [`crate::verify_ledger_replay`] has proved every effect rule-correct, so this is the honest
/// reference state the saved scene/flags/inventory must equal.
pub(crate) fn replay_final_state(map: &GameWorld, ledger: &[LedgerEntry]) -> WorldCell {
    let mut world = map.new_world();
    for entry in ledger {
        if let Some(effect) = &entry.effect {
            world.apply(effect);
        }
    }
    world
}

/// Project a live [`WorldCell`] ledger into serializable [`SavedEntry`]s.
pub(crate) fn save_ledger(ledger: &[LedgerEntry]) -> Vec<SavedEntry> {
    ledger.iter().map(SavedEntry::from_entry).collect()
}
