//! Table definitions for the redb database.
//!
//! Each table is defined as a constant with a fixed name and typed key/value pairs.
//! redb uses these definitions to enforce type safety at the database level.

use redb::TableDefinition;

/// Token chain storage: token_id (32 bytes) -> serialized TokenChain.
///
/// Key: 32-byte token identifier (fixed-size).
/// Value: postcard-serialized `TokenChain` struct.
pub const TOKEN_CHAINS: TableDefinition<&[u8; 32], &[u8]> = TableDefinition::new("token_chains");

/// Revocation set: token_id (string) -> revocation timestamp.
///
/// Key: token ID as a string (variable length).
/// Value: i64 timestamp when the revocation was recorded.
pub const REVOCATIONS: TableDefinition<&str, i64> = TableDefinition::new("revocations");

/// Attested roots: height (u64) -> serialized StoredAttestedRoot.
///
/// Key: block height (monotonically increasing).
/// Value: postcard-serialized `StoredAttestedRoot` struct.
pub const ATTESTED_ROOTS: TableDefinition<u64, &[u8]> = TableDefinition::new("attested_roots");

/// Signing keys (encrypted): name (string) -> encrypted key blob.
///
/// Key: human-readable key name.
/// Value: encrypted key blob (nonce || ciphertext || tag).
pub const SIGNING_KEYS: TableDefinition<&str, &[u8]> = TableDefinition::new("signing_keys");

/// Public keys: name (string) -> 32-byte public key.
///
/// Key: human-readable key name.
/// Value: 32-byte raw public key.
pub const PUBLIC_KEYS: TableDefinition<&str, &[u8; 32]> = TableDefinition::new("public_keys");

/// Audit log: sequence number (u64) -> serialized StoredAuditEvent.
///
/// Key: monotonically increasing sequence number (0-based).
/// Value: postcard-serialized `StoredAuditEvent` struct.
pub const AUDIT_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("audit_log");

/// Audit token index: composite key (token_id_hex + sequence) -> sequence number.
///
/// This is a secondary index for looking up audit events by token ID.
/// Key: "{token_id_hex}:{sequence}" (string for range scanning).
/// Value: the global sequence number in the audit log.
pub const AUDIT_TOKEN_INDEX: TableDefinition<&str, u64> = TableDefinition::new("audit_token_index");

/// Metadata table for store-level counters and configuration.
///
/// Key: metadata key name.
/// Value: u64 value (used for counters like audit_sequence).
pub const METADATA: TableDefinition<&str, u64> = TableDefinition::new("metadata");

/// Note commitment tree: position (u64) -> 32-byte commitment hash.
///
/// Key: position in the append-only tree (0-based, monotonically increasing).
/// Value: 32-byte note commitment.
pub const NOTE_COMMITMENTS: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("note_commitments");

/// Nullifier set: nullifier hash (32 bytes) -> unit (presence = spent).
///
/// Key: 32-byte nullifier hash.
/// Value: empty (presence in the table means the note is spent).
pub const NULLIFIERS: TableDefinition<&[u8; 32], ()> = TableDefinition::new("nullifiers");

/// Checkpoints: height (u64) -> serialized Checkpoint.
///
/// Key: checkpoint height (always a multiple of the checkpoint interval).
/// Value: postcard-serialized `dregg_federation::Checkpoint` struct.
pub const CHECKPOINTS: TableDefinition<u64, &[u8]> = TableDefinition::new("checkpoints");

/// Byte-blob metadata table for values that don't fit in a u64.
///
/// Key: metadata key name.
/// Value: arbitrary byte blob (e.g., cached Merkle roots).
pub const METADATA_BYTES: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata_bytes");

// Metadata key constants.

/// Key for the next audit sequence number.
pub const META_AUDIT_NEXT_SEQ: &str = "audit_next_sequence";

/// Key for the latest attested root height.
pub const META_LATEST_ROOT_HEIGHT: &str = "latest_root_height";

/// Key for the note tree size (number of commitments).
pub const META_NOTE_TREE_SIZE: &str = "note_tree_size";

/// Key for the cached note tree root (stored in METADATA_BYTES).
pub const META_NOTE_TREE_ROOT_CACHE: &str = "note_tree_root_cache";

/// Key for the cached Poseidon2 note tree root (stored in METADATA_BYTES).
///
/// Stored as 4 bytes (little-endian u32) representing the BabyBear field element.
/// Updated on every `store_note_commitment` / `spend_note_atomic` call.
pub const META_POSEIDON2_NOTE_TREE_ROOT_CACHE: &str = "poseidon2_note_tree_root_cache";

/// Key for the latest checkpoint height.
pub const META_LATEST_CHECKPOINT_HEIGHT: &str = "latest_checkpoint_height";

/// Ledger checkpoints: height (u64) -> serialized LedgerCheckpoint.
///
/// Key: block height at which the checkpoint was taken.
/// Value: postcard-serialized `LedgerCheckpoint` struct (full ledger state snapshot).
pub const LEDGER_CHECKPOINTS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("ledger_checkpoints");

/// Key for the latest ledger checkpoint height.
pub const META_LATEST_LEDGER_CHECKPOINT_HEIGHT: &str = "latest_ledger_checkpoint_height";

// ─── Blocklace Tables ──────────────────────────────────────────────────────

/// Blocklace blocks: block_id (32 bytes) -> serialized Block.
///
/// Key: 32-byte block ID (blake3 hash of signed content + signature).
/// Value: postcard-serialized `Block` struct.
pub const BLOCKLACE_BLOCKS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("blocklace_blocks");

/// Blocklace metadata: key (string) -> arbitrary bytes.
///
/// Stores tips, equivocators, ordering state, and other blocklace metadata.
/// Key: metadata key name (e.g., "meta").
/// Value: postcard-serialized `BlocklaceMeta` struct.
pub const BLOCKLACE_META: TableDefinition<&str, &[u8]> = TableDefinition::new("blocklace_meta");

/// Key for the blocklace metadata blob in the BLOCKLACE_META table.
pub const BLOCKLACE_META_KEY: &str = "meta";

/// Key for the executed_up_to index in the BLOCKLACE_META table.
pub const BLOCKLACE_EXECUTED_UP_TO_KEY: &str = "executed_up_to";

/// Node-local witnessed receipt artifacts.
///
/// Key: receipt hash.
/// Value: caller-owned serialized witness vector. The persist crate keeps this
/// table byte-oriented so it does not depend on `dregg-turn`.
pub const WITNESSED_RECEIPTS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("witnessed_receipts");

// ─── Durable Commit Log + Index (crash-consistency) ─────────────────────────
//
// The commit log is the authoritative, append-only record of finalized turns
// that THIS node has applied to its ledger. It is the recovery anchor: each
// record is written in the SAME redb transaction that advances the commit
// cursor (`META_COMMIT_CURSOR`), so the cursor and the per-turn record can
// never be torn against each other. The index tables below are secondary
// views derived from this log; every index write happens in that same
// transaction, so the "index entry exists iff the log has it" invariant holds
// by construction across crashes.

/// Commit log: commit ordinal (u64, 0-based, == position in the tau-finalized
/// order this node has applied) -> postcard-serialized `CommitRecord`.
///
/// Key: the commit ordinal (a dense, gap-free counter advanced by exactly one
/// per applied turn; equals the prior `executed_up_to` semantics but is now the
/// crash-consistent anchor written atomically with the record itself).
/// Value: postcard-serialized `commit_log::CommitRecord`.
pub const COMMIT_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("commit_log");

/// Index — receipt by hash: receipt_hash (32 bytes) -> commit ordinal (u64).
///
/// Lets a verifier/explorer resolve a receipt hash to its commit position in
/// O(1) without scanning. The pointed-to `CommitRecord` carries the full
/// coordinates (height, creator, turn hash, ledger root).
pub const IDX_RECEIPT_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_receipt_by_hash");

/// Index — turn by hash: turn_hash (32 bytes) -> commit ordinal (u64).
pub const IDX_TURN_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_turn_by_hash");

/// Index — turns by (height, creator): composite key -> commit ordinal (u64).
///
/// Key layout: 8-byte big-endian height ++ 32-byte creator. Big-endian height
/// makes redb's lexicographic range scan equal a height-ordered scan, so
/// "all turns at height H" and "all turns by creator C in height order" are
/// efficient range queries. A `(height, creator)` pair is unique per commit
/// because each finalized blocklace block carries exactly one turn and the
/// node assigns a fresh height per applied turn.
pub const IDX_TURN_BY_HEIGHT_CREATOR: TableDefinition<&[u8], u64> =
    TableDefinition::new("idx_turn_by_height_creator");

/// Index — cell by id (durable per-turn snapshot): cell_id (32 bytes) ->
/// postcard-serialized `dregg_cell::Cell`.
///
/// Updated atomically per applied turn from the executor's post-state so a
/// node can look up the current contents of ANY cell touched since the last
/// full ledger checkpoint, without replaying. Cells not touched since the last
/// checkpoint are served from the checkpoint; this table holds the deltas on
/// top of it. Rebuilt deterministically from the commit log on demand.
pub const IDX_CELL_BY_ID: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("idx_cell_by_id");

/// Key (in METADATA) for the durable commit cursor: the number of turns this
/// node has committed and indexed = the next free commit ordinal. This is the
/// crash-consistent replacement for the separately-written
/// `BLOCKLACE_EXECUTED_UP_TO_KEY`; recovery reads THIS value (advanced inside
/// the per-turn commit transaction) as the authoritative high-water mark.
pub const META_COMMIT_CURSOR: &str = "commit_cursor";
