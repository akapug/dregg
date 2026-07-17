//! `redb_store` — the persist-PD's REAL durable verified commit-log, in `redb`
//! ACID tables over a block-device `StorageBackend`. This is the §3 backend the
//! `commit_store.rs` gate logic was lifted to ride: it makes "durable" REAL.
//!
//! # The advance over `commit_store.rs`
//!
//! `commit_store.rs` carries the chain gate `no_std`+`alloc` over a `BTreeMap` —
//! the gate SEMANTICS, transport-free, ready to ride inside the PD. But a
//! `BTreeMap` is not durable: drop the process and the log is gone. THIS module is
//! the durable store the persist PD actually writes: the SAME `CommitRecord`, the
//! SAME chain gate (`commit_store::verify_chain_step`), the SAME idempotent-replay
//! / torn-state discipline — but committed into real `redb` tables in ONE write
//! transaction, byte-for-byte the `persist/src/commit_log.rs`
//! `commit_finalized_turn_with_burns` discipline:
//!
//!   1. open METADATA, read the durable cursor;
//!   2. torn-state / idempotent-replay guard against that durable cursor;
//!   3. the chain gate (`verify_chain_step`) — anti-substitution tooth;
//!   4. append the record to COMMIT_LOG + the two by-hash indices, ALL in the txn;
//!   5. advance META_COMMIT_CURSOR LAST, still in the txn;
//!   6. `write_txn.commit()` — the ONE fsync boundary (redb's WAL → `sync_data`).
//!
//! After `commit()` returns, the turn is durable: a crash cannot lose it and cannot
//! leave it half-written (redb is ACID — the txn either fully commits or not at
//! all). That is the `n = 1` synchronous commit (`.docs-history-noclaude/FIRMAMENT.md` §3) realized.
//!
//! # The block-device seam — WHY this ports to seL4 with the gate UNCHANGED
//!
//! redb stores through a [`redb::StorageBackend`] — a trait of exactly five ops:
//! `len` · `read(offset,len)` · `set_len` · `sync_data(eventual)` · `write(offset,
//! data)`. That is *precisely* a raw block device's interface. So the persist PD's
//! on-device backend is one `StorageBackend` impl whose five ops go through the
//! seL4 block cap it solely holds — and the entire durable-store logic above it
//! (this module) is unchanged. [`RegionBackend`] here is that impl over a fixed
//! byte region; the host realization ([`RegionBackend::file`]) backs the region
//! with an on-disk file (so the host witness proves REAL cross-process durability —
//! a commit survives the store being dropped and reopened from the bytes), and the
//! on-device realization (`BlockCapBackend`, the named rung) backs the SAME region
//! with the block cap. `read`/`write`/`sync_data` are the only methods that change;
//! the commit-log discipline does not.
//!
//! THE DISCIPLINE IS REUSED, NOT REINVENTED: the chain gate is
//! `commit_store::verify_chain_step` (itself `pg-dregg/src/mirror.rs`'s
//! `RootChain::extend`), the record is `commit_store::CommitRecord`, the
//! one-transaction ordering is `persist/src/commit_log.rs`'s. The ONLY new thing
//! here is the durable transport — and it is real redb, not a stand-in.

use std::io;
use std::sync::Mutex;

use redb::{Database, ReadableTable, StorageBackend, TableDefinition};

// The SAME record + the SAME pure chain gate the persist PD carries. This module
// stores `CommitRecord`s and gates them with `verify_chain_step` — identical to
// the BTreeMap store; only the medium (real redb over a block device) differs.
use crate::commit_store::{ChainRefusal, CommitRecord, GENESIS_ROOT};

// ── redb tables — the durable face of `commit_store`'s three maps ─────────────
// These mirror `persist/src/tables.rs`: COMMIT_LOG keyed by ordinal, the two
// by-hash indices, and the metadata cursor. The persist PD's on-device store
// opens these same tables over the block cap.

/// The commit log: ordinal -> postcard-free manually-encoded `CommitRecord`.
/// (`persist`'s `tables::COMMIT_LOG`.) Dense, gap-free: `ordinal == n` ⇒ exactly
/// `n` turns committed before it.
const COMMIT_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("commit_log");
/// turn_hash -> ordinal (`tables::IDX_TURN_BY_HASH`).
const IDX_TURN_BY_HASH: TableDefinition<&[u8; 32], u64> = TableDefinition::new("idx_turn_by_hash");
/// receipt_hash -> ordinal (`tables::IDX_RECEIPT_BY_HASH`).
const IDX_RECEIPT_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_receipt_by_hash");
/// Store-level counters (`tables::METADATA`). The durable cursor lives here.
const METADATA: TableDefinition<&str, u64> = TableDefinition::new("metadata");
/// 32-byte metadata (`tables::METADATA_BYTES`) — the durable chain head.
const METADATA_BYTES: TableDefinition<&str, &[u8; 32]> = TableDefinition::new("metadata_bytes");

/// The durable cursor key (`persist`'s `META_COMMIT_CURSOR`).
const META_COMMIT_CURSOR: &str = "commit_cursor";
/// The durable head-root key — the last committed `ledger_root` (None iff cursor 0).
const META_HEAD_ROOT: &str = "head_root";

// ── the block-device backend (the seL4-block-cap-shaped StorageBackend) ───────

/// A `redb` [`StorageBackend`] over a fixed byte region — the block-device shape.
///
/// redb stores through five ops (`len`/`read`/`set_len`/`sync_data`/`write`), which
/// is exactly a raw block device. This impl backs that region with an in-RAM
/// `Vec<u8>` mirror + (optionally) an on-disk file, so:
///
///   * the HOST witness ([`RegionBackend::file`]) gets REAL durability — the bytes
///     are an `mmap`-free `File` (`read`/`write` go to the file via positional I/O,
///     `sync_data` is an `fsync`), so a commit survives the `Database` being dropped
///     and a fresh `Database` opened over the SAME file (the cross-process crash);
///   * the ON-DEVICE persist PD (`BlockCapBackend`, the named rung) replaces the
///     `File` with the seL4 block cap — the SAME five ops, now `seL4_*` block
///     reads/writes; the durable-store logic above is byte-for-byte unchanged.
///
/// We hold the file behind a `Mutex` because `StorageBackend` requires
/// `Send + Sync` and takes `&self` for `write`/`set_len` (interior mutability) —
/// the same shape redb's own `FileBackend` has (it uses positional `FileExt`).
#[derive(Debug)]
pub struct RegionBackend {
    /// The durable medium. `Some` ⇒ an on-disk file (real durability); `None` ⇒ a
    /// pure in-RAM region (a volatile device — used only where durability across a
    /// *reopen of the same backend value* is not asserted).
    inner: Mutex<Region>,
}

#[derive(Debug)]
struct Region {
    /// The on-disk file backing the region (the host's durable device), if any.
    file: Option<std::fs::File>,
    /// The in-RAM mirror (always present; the authoritative length source).
    bytes: Vec<u8>,
}

impl RegionBackend {
    /// A durable region backed by a file on disk — the HOST realization. The file
    /// is the byte device redb reads/writes/fsyncs; reopening a `RegionBackend`
    /// over the SAME path recovers every committed turn (the crash test).
    ///
    /// (On-device this constructor is replaced by `BlockCapBackend::new(block_cap)`
    /// — the SAME `StorageBackend`, the bytes living on the block device the persist
    /// PD solely holds. The named rung is exactly that constructor + its five ops.)
    pub fn file(path: &std::path::Path) -> io::Result<Self> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        let len = file.metadata()?.len() as usize;
        let mut bytes = vec![0u8; len];
        if len > 0 {
            read_exact_at(&file, 0, &mut bytes)?;
        }
        Ok(RegionBackend {
            inner: Mutex::new(Region {
                file: Some(file),
                bytes,
            }),
        })
    }
}

impl StorageBackend for RegionBackend {
    fn len(&self) -> Result<u64, io::Error> {
        Ok(self.inner.lock().unwrap().bytes.len() as u64)
    }

    fn read(&self, offset: u64, len: usize) -> Result<Vec<u8>, io::Error> {
        let g = self.inner.lock().unwrap();
        let off = offset as usize;
        let end = off
            .checked_add(len)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "read overflow"))?;
        if end > g.bytes.len() {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "read past end of region",
            ));
        }
        Ok(g.bytes[off..end].to_vec())
    }

    fn set_len(&self, len: u64) -> Result<(), io::Error> {
        let mut g = self.inner.lock().unwrap();
        let len = len as usize;
        g.bytes.resize(len, 0); // new positions zero-initialized (the contract)
        if let Some(f) = g.file.as_ref() {
            f.set_len(len as u64)?;
        }
        Ok(())
    }

    fn sync_data(&self, _eventual: bool) -> Result<(), io::Error> {
        // The write barrier — redb calls this at the commit boundary. On the host
        // this is a real fsync of the file (so the commit is durable on disk); on
        // the block cap it is the device flush. After this returns, every write
        // before it is durable before any write after it.
        let g = self.inner.lock().unwrap();
        if let Some(f) = g.file.as_ref() {
            f.sync_data()?;
        }
        Ok(())
    }

    fn write(&self, offset: u64, data: &[u8]) -> Result<(), io::Error> {
        let mut g = self.inner.lock().unwrap();
        let off = offset as usize;
        let end = off
            .checked_add(data.len())
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "write overflow"))?;
        if end > g.bytes.len() {
            g.bytes.resize(end, 0);
        }
        g.bytes[off..end].copy_from_slice(data);
        // Mirror the write through to the durable device (positional, like redb's
        // own FileBackend — `write_all_at`). The bytes are not durable until
        // `sync_data`; that is the WAL barrier redb relies on.
        if let Some(f) = g.file.as_ref() {
            write_all_at(f, offset, data)?;
        }
        Ok(())
    }
}

// Positional file I/O — the same primitives redb's unix `FileBackend` uses
// (`read_exact_at` / `write_all_at`). Split out so the unix path is explicit and
// the on-device block-cap analogue (block read / block write at an LBA) is obvious.
#[cfg(unix)]
fn read_exact_at(f: &std::fs::File, offset: u64, buf: &mut [u8]) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    f.read_exact_at(buf, offset)
}
#[cfg(unix)]
fn write_all_at(f: &std::fs::File, offset: u64, data: &[u8]) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    f.write_all_at(data, offset)
}
#[cfg(not(unix))]
fn read_exact_at(f: &std::fs::File, offset: u64, buf: &mut [u8]) -> io::Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    let mut f = f.try_clone()?;
    f.seek(SeekFrom::Start(offset))?;
    f.read_exact(buf)
}
#[cfg(not(unix))]
fn write_all_at(f: &std::fs::File, offset: u64, data: &[u8]) -> io::Result<()> {
    use std::io::{Seek, SeekFrom, Write};
    let mut f = f.try_clone()?;
    f.seek(SeekFrom::Start(offset))?;
    f.write_all(data)
}

// ── the durable verified commit-log store ─────────────────────────────────────

/// Errors the durable store surfaces — the chain gate's [`ChainRefusal`] (a turn
/// refused at the gate) or a storage fault (the device failed). A storage fault is
/// a durability error, never silently swallowed.
#[derive(Debug)]
pub enum DurableError {
    /// The turn was refused at the chain gate (fail-closed; head did not move).
    Refused(ChainRefusal),
    /// The durable medium failed (redb / device error). The turn is NOT durable.
    Storage(String),
}

impl core::fmt::Display for DurableError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DurableError::Refused(r) => write!(f, "refused: {}", r.reason()),
            DurableError::Storage(m) => write!(f, "storage fault: {m}"),
        }
    }
}
impl std::error::Error for DurableError {}

impl From<redb::Error> for DurableError {
    fn from(e: redb::Error) -> Self {
        DurableError::Storage(e.to_string())
    }
}

/// The persist-PD's durable verified commit-log over real `redb`. The SAME spine
/// as [`crate::commit_store::CommitStore`] — reads are free, writes pass the chain
/// gate then commit in ONE redb transaction — but the store is now durable: a
/// commit survives the process, and a reopen recovers the head + cursor + log.
pub struct DurableCommitStore {
    db: Database,
}

impl DurableCommitStore {
    /// Open (or create) the durable store over a [`StorageBackend`]. On the host
    /// pass a [`RegionBackend::file`]; on-device the persist PD passes its
    /// block-cap backend. Initializes the tables on a fresh store; recovers the
    /// durable cursor + head on an existing one (nothing replayed — the cursor and
    /// head are read straight from METADATA, `persist`'s `commit_cursor()` recovery).
    pub fn open(backend: impl StorageBackend) -> Result<Self, DurableError> {
        let db = Database::builder()
            .create_with_backend(backend)
            .map_err(|e| DurableError::Storage(e.to_string()))?;
        // Ensure the tables exist (a fresh store) — one txn, like `persist`'s
        // `initialize_tables`. On an existing store this is a no-op open.
        let w = db.begin_write().map_err(se)?;
        {
            let _ = w.open_table(COMMIT_LOG).map_err(te)?;
            let _ = w.open_table(IDX_TURN_BY_HASH).map_err(te)?;
            let _ = w.open_table(IDX_RECEIPT_BY_HASH).map_err(te)?;
            let _ = w.open_table(METADATA).map_err(te)?;
            let _ = w.open_table(METADATA_BYTES).map_err(te)?;
        }
        w.commit().map_err(ce)?;
        Ok(DurableCommitStore { db })
    }

    // ---- reads are FREE (a redb read txn; no writer touched) -----------------

    /// The next free ordinal = number of durably committed turns
    /// (`persist`'s `commit_cursor()`). Read from durable METADATA.
    pub fn commit_cursor(&self) -> Result<u64, DurableError> {
        let r = self.db.begin_read().map_err(se)?;
        let meta = r.open_table(METADATA).map_err(te)?;
        Ok(meta
            .get(META_COMMIT_CURSOR)
            .map_err(ge)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// The current chain head (last committed `ledger_root`), or None at genesis.
    /// Read from durable METADATA_BYTES — this is `RootChain::head` made durable.
    pub fn head_root(&self) -> Result<Option<[u8; 32]>, DurableError> {
        let r = self.db.begin_read().map_err(se)?;
        let meta = r.open_table(METADATA_BYTES).map_err(te)?;
        Ok(meta.get(META_HEAD_ROOT).map_err(ge)?.map(|g| *g.value()))
    }

    /// Read a committed turn by its position (the `dregg.turns` row read; free).
    pub fn lookup_by_ordinal(&self, ordinal: u64) -> Result<Option<CommitRecord>, DurableError> {
        let r = self.db.begin_read().map_err(se)?;
        let log = r.open_table(COMMIT_LOG).map_err(te)?;
        match log.get(ordinal).map_err(ge)? {
            Some(g) => Ok(Some(decode_record(g.value())?)),
            None => Ok(None),
        }
    }

    /// Read a committed turn by its identity (the `IDX_TURN_BY_HASH` lookup; free).
    pub fn lookup_by_turn_hash(
        &self,
        turn_hash: &[u8; 32],
    ) -> Result<Option<CommitRecord>, DurableError> {
        let r = self.db.begin_read().map_err(se)?;
        let idx = r.open_table(IDX_TURN_BY_HASH).map_err(te)?;
        let Some(ord) = idx.get(turn_hash).map_err(ge)?.map(|g| g.value()) else {
            return Ok(None);
        };
        let log = r.open_table(COMMIT_LOG).map_err(te)?;
        match log.get(ord).map_err(ge)? {
            Some(g) => Ok(Some(decode_record(g.value())?)),
            None => Ok(None),
        }
    }

    /// Read a committed turn by its receipt (the `IDX_RECEIPT_BY_HASH` lookup; free).
    pub fn lookup_by_receipt_hash(
        &self,
        receipt_hash: &[u8; 32],
    ) -> Result<Option<CommitRecord>, DurableError> {
        let r = self.db.begin_read().map_err(se)?;
        let idx = r.open_table(IDX_RECEIPT_BY_HASH).map_err(te)?;
        let Some(ord) = idx.get(receipt_hash).map_err(ge)?.map(|g| g.value()) else {
            return Ok(None);
        };
        let log = r.open_table(COMMIT_LOG).map_err(te)?;
        match log.get(ord).map_err(ge)? {
            Some(g) => Ok(Some(decode_record(g.value())?)),
            None => Ok(None),
        }
    }

    /// The whole durable log in applied order — a light client walks this and
    /// re-checks the root chain (`prev_root[N+1] == ledger_root[N]`). The
    /// self-checking projection (§10), now over the durable rows.
    pub fn read_ordered(&self) -> Result<Vec<CommitRecord>, DurableError> {
        let r = self.db.begin_read().map_err(se)?;
        let log = r.open_table(COMMIT_LOG).map_err(te)?;
        let mut out = Vec::new();
        for entry in log.range(0u64..).map_err(ge)? {
            let (_k, v) = entry.map_err(ge)?;
            out.push(decode_record(v.value())?);
        }
        Ok(out)
    }

    /// Re-check the durable chain end-to-end — the "chain is self-checking" tooth
    /// (`.docs-history-noclaude/PG-DREGG.md` §15.1) over the on-store rows. Walks the log in ordinal
    /// order and asserts each `prev_root` equals the prior `ledger_root` (genesis
    /// carries `GENESIS_ROOT`), and that ordinals are dense. Returns `Ok(())` iff
    /// intact; `Err` names the first broken link (a tampered store fails closed).
    pub fn verify_chain_intact(&self) -> Result<(), DurableError> {
        let records = self.read_ordered()?;
        let mut prev_ledger: Option<[u8; 32]> = None;
        for (i, rec) in records.iter().enumerate() {
            if rec.ordinal != i as u64 {
                return Err(DurableError::Refused(ChainRefusal::Integrity(format!(
                    "ordinal hole: record {i} carries ordinal {}",
                    rec.ordinal
                ))));
            }
            let expected = prev_ledger.unwrap_or(GENESIS_ROOT);
            if rec.prev_root != expected {
                return Err(DurableError::Refused(ChainRefusal::RootMismatch {
                    head: expected,
                    prev: rec.prev_root,
                }));
            }
            prev_ledger = Some(rec.ledger_root);
        }
        Ok(())
    }

    // ---- the write: chain gate, then ONE redb transaction --------------------

    /// Commit a verified turn — the persist PD's `n = 1` synchronous commit, now
    /// DURABLE. The ONLY door state enters the store. Runs the SAME discipline
    /// `persist/src/commit_log.rs::commit_finalized_turn_with_burns` runs, in ONE
    /// redb write transaction (the fsync boundary):
    ///
    ///   1. read the durable cursor from METADATA;
    ///   2. torn-state / idempotent-replay guard against it (same `turn_hash` at a
    ///      taken ordinal ⇒ no-op success; different ⇒ Integrity refusal; a gap ⇒
    ///      refused);
    ///   3. the chain gate (`commit_store::verify_chain_step`) — `prev_root == head`;
    ///   4. append record + the two by-hash indices;
    ///   5. advance the durable cursor + head LAST;
    ///   6. `commit()` — durable. After this returns the turn cannot be lost.
    ///
    /// Returns the assigned ordinal. A refusal leaves the durable head UNMOVED (the
    /// txn is not committed). A device fault is a [`DurableError::Storage`].
    pub fn commit_verified_turn(&self, record: &CommitRecord) -> Result<u64, DurableError> {
        let w = self.db.begin_write().map_err(se)?;
        let assigned;
        {
            let mut meta = w.open_table(METADATA).map_err(te)?;
            let cursor = meta
                .get(META_COMMIT_CURSOR)
                .map_err(ge)?
                .map(|g| g.value())
                .unwrap_or(0);

            // (2) torn-state / idempotent-replay guard against the DURABLE cursor.
            if record.ordinal != cursor {
                if record.ordinal < cursor {
                    // Decode the stored record into an OWNED value so the redb
                    // AccessGuard + the table drop before we branch (the guard must
                    // not outlive the table).
                    let existing: Option<CommitRecord> = {
                        let log = w.open_table(COMMIT_LOG).map_err(te)?;
                        let v = match log.get(record.ordinal).map_err(ge)? {
                            Some(g) => Some(decode_record(g.value())?),
                            None => None,
                        };
                        v // owned; the guard + table drop here
                    };
                    match existing {
                        Some(existing) => {
                            if existing.turn_hash == record.turn_hash {
                                return Ok(record.ordinal); // already durable; no-op
                            }
                            return Err(DurableError::Refused(ChainRefusal::Integrity(format!(
                                "ordinal {} already holds a different turn",
                                record.ordinal
                            ))));
                        }
                        None => {
                            return Err(DurableError::Refused(ChainRefusal::Integrity(format!(
                                "cursor {cursor} > ordinal {} but no record there (corrupt log)",
                                record.ordinal
                            ))));
                        }
                    }
                }
                return Err(DurableError::Refused(ChainRefusal::Integrity(format!(
                    "expected ordinal {} != durable cursor {cursor}; refusing to write a gap",
                    record.ordinal
                ))));
            }

            // (3) THE CHAIN GATE — the anti-substitution tooth (byte-identical to
            //     the BTreeMap store; itself pg-dregg's `RootChain::extend`). The
            //     durable head lives in METADATA_BYTES (the `RootChain::head` made
            //     durable); read it inside this same txn.
            let head_root = {
                let mb = w.open_table(METADATA_BYTES).map_err(te)?;
                let v = mb.get(META_HEAD_ROOT).map_err(ge)?.map(|g| *g.value());
                v // owned [u8;32] copied out; the guard + table drop here
            };
            crate::commit_store::verify_chain_step(
                head_root,
                cursor,
                record.prev_root,
                record.ordinal,
            )
            .map_err(DurableError::Refused)?;

            // (4) THE ATOMIC APPEND — record + indices, then (5) cursor + head LAST,
            //     ALL in this one write txn (on-device: one block-cap commit()).
            assigned = cursor;
            let stored = CommitRecord {
                ordinal: assigned,
                ..record.clone()
            };
            let encoded = encode_record(&stored);
            {
                let mut log = w.open_table(COMMIT_LOG).map_err(te)?;
                log.insert(assigned, encoded.as_slice()).map_err(ge)?;
            }
            {
                let mut idx_turn = w.open_table(IDX_TURN_BY_HASH).map_err(te)?;
                idx_turn.insert(&stored.turn_hash, assigned).map_err(ge)?;
                let mut idx_receipt = w.open_table(IDX_RECEIPT_BY_HASH).map_err(te)?;
                idx_receipt
                    .insert(&stored.receipt_hash, assigned)
                    .map_err(ge)?;
            }
            // (5) advance the durable cursor + head LAST within the txn.
            meta.insert(META_COMMIT_CURSOR, assigned + 1).map_err(ge)?;
            {
                let mut mb = w.open_table(METADATA_BYTES).map_err(te)?;
                mb.insert(META_HEAD_ROOT, &stored.ledger_root).map_err(ge)?;
            }
        }
        // (6) ONE fsync boundary — the turn is durable iff this returns Ok.
        w.commit().map_err(ce)?;
        Ok(assigned)
    }
}

// ── record codec — manual, postcard-free (no extra dep; the store stays lean) ─
// A fixed-layout encoding of `CommitRecord`: the seven 32-byte/u64 scalar fields
// in declared order, then the length-prefixed `touched_cells` blob. Deterministic
// and self-describing enough for the store (redb gives us the value bytes; we own
// the encoding). On-device `persist` uses `postcard`; here we avoid the dep.

fn encode_record(r: &CommitRecord) -> Vec<u8> {
    let mut v = Vec::with_capacity(8 * 3 + 32 * 5 + 8 + r.touched_cells.len());
    v.extend_from_slice(&r.ordinal.to_le_bytes());
    v.extend_from_slice(&r.height.to_le_bytes());
    v.extend_from_slice(&r.block_id);
    v.extend_from_slice(&r.turn_hash);
    v.extend_from_slice(&r.creator);
    v.extend_from_slice(&r.receipt_hash);
    v.extend_from_slice(&r.prev_root);
    v.extend_from_slice(&r.ledger_root);
    v.extend_from_slice(&(r.touched_cells.len() as u64).to_le_bytes());
    v.extend_from_slice(&r.touched_cells);
    v
}

fn decode_record(b: &[u8]) -> Result<CommitRecord, DurableError> {
    let mut o = 0usize;
    let u64_at = |b: &[u8], o: &mut usize| -> Result<u64, DurableError> {
        let end = *o + 8;
        if end > b.len() {
            return Err(DurableError::Storage("short record (u64)".into()));
        }
        let mut a = [0u8; 8];
        a.copy_from_slice(&b[*o..end]);
        *o = end;
        Ok(u64::from_le_bytes(a))
    };
    let arr_at = |b: &[u8], o: &mut usize| -> Result<[u8; 32], DurableError> {
        let end = *o + 32;
        if end > b.len() {
            return Err(DurableError::Storage("short record ([u8;32])".into()));
        }
        let mut a = [0u8; 32];
        a.copy_from_slice(&b[*o..end]);
        *o = end;
        Ok(a)
    };
    let ordinal = u64_at(b, &mut o)?;
    let height = u64_at(b, &mut o)?;
    let block_id = arr_at(b, &mut o)?;
    let turn_hash = arr_at(b, &mut o)?;
    let creator = arr_at(b, &mut o)?;
    let receipt_hash = arr_at(b, &mut o)?;
    let prev_root = arr_at(b, &mut o)?;
    let ledger_root = arr_at(b, &mut o)?;
    let tc_len = u64_at(b, &mut o)? as usize;
    let end = o + tc_len;
    if end > b.len() {
        return Err(DurableError::Storage("short record (touched_cells)".into()));
    }
    let touched_cells = b[o..end].to_vec();
    Ok(CommitRecord {
        ordinal,
        height,
        block_id,
        turn_hash,
        creator,
        receipt_hash,
        prev_root,
        ledger_root,
        touched_cells,
    })
}

// redb error → DurableError adapters (kept terse so the commit reads as the
// discipline, not error plumbing). Each variant of redb's error tower maps to a
// storage fault — the device/store failed, so the turn is not durable.
fn se(e: redb::TransactionError) -> DurableError {
    DurableError::Storage(e.to_string())
}
fn te(e: redb::TableError) -> DurableError {
    DurableError::Storage(e.to_string())
}
fn ge(e: redb::StorageError) -> DurableError {
    DurableError::Storage(e.to_string())
}
fn ce(e: redb::CommitError) -> DurableError {
    DurableError::Storage(e.to_string())
}

// ============================================================================
// Tests — the SAME anti-substitution teeth as `commit_store`, now over REAL
// `redb` ACID storage, PLUS the durability-across-reopen tooth (the one a
// BTreeMap store cannot prove). The gate semantics are byte-identical; what is
// new here is that "durable" is real — a commit survives the store being dropped.
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic producer (the executor stand-in), identical in shape to the
    /// host witness's: stamps `(ordinal, prev_root)` and a stable post-state root.
    fn produce(turn_id: u64, ordinal: u64, prev_root: [u8; 32]) -> CommitRecord {
        let d = |tag: u8| {
            let mut out = [0u8; 32];
            let mut acc = 0x9e37_79b9_7f4a_7c15u64 ^ ((tag as u64) << 56) ^ turn_id;
            for (i, b) in prev_root.iter().enumerate() {
                acc = acc
                    .rotate_left(7)
                    .wrapping_add(*b as u64)
                    .wrapping_mul(0x0100_0000_01b3)
                    ^ (i as u64);
            }
            for (i, slot) in out.iter_mut().enumerate() {
                acc = acc
                    .rotate_left(11)
                    .wrapping_add(i as u64)
                    .wrapping_mul(0x0100_0000_01b3);
                *slot = (acc >> ((i % 8) * 8)) as u8;
            }
            out
        };
        CommitRecord {
            ordinal,
            height: ordinal,
            block_id: d(0x04),
            turn_hash: d(0x01),
            creator: [0xA1; 32],
            receipt_hash: d(0x02),
            prev_root,
            ledger_root: d(0x03),
            touched_cells: turn_id.to_le_bytes().to_vec(),
        }
    }

    fn fresh() -> (tempfile::TempDir, DurableCommitStore) {
        let dir = tempfile::tempdir().unwrap();
        let backend = RegionBackend::file(&dir.path().join("store.redb")).unwrap();
        let store = DurableCommitStore::open(backend).unwrap();
        (dir, store)
    }

    /// The spine over real redb: a verified turn commits durably and a read returns
    /// it (by ordinal / turn_hash / receipt_hash).
    #[test]
    fn commit_then_read_over_real_redb() {
        let (_d, store) = fresh();
        let t = produce(1, 0, GENESIS_ROOT);
        let ord = store.commit_verified_turn(&t).unwrap();
        assert_eq!(ord, 0);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(store.lookup_by_ordinal(0).unwrap(), Some(t.clone()));
        assert_eq!(
            store.lookup_by_turn_hash(&t.turn_hash).unwrap(),
            Some(t.clone())
        );
        assert_eq!(
            store.lookup_by_receipt_hash(&t.receipt_hash).unwrap(),
            Some(t)
        );
    }

    /// Turn N+1 chains onto N; the durable head IS N's ledger_root.
    #[test]
    fn turns_chain_through_the_durable_head() {
        let (_d, store) = fresh();
        let t0 = produce(1, 0, GENESIS_ROOT);
        store.commit_verified_turn(&t0).unwrap();
        let prev = store.head_root().unwrap().unwrap();
        assert_eq!(prev, t0.ledger_root);
        let t1 = produce(2, 1, prev);
        store.commit_verified_turn(&t1).unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 2);
        assert_eq!(store.head_root().unwrap(), Some(t1.ledger_root));
        store.verify_chain_intact().unwrap();
    }

    /// The anti-substitution tooth on the durable store: a wrong-prev_root turn is
    /// REFUSED and the durable head does not move (the txn is not committed).
    #[test]
    fn wrong_prev_root_is_refused_and_durable_head_unmoved() {
        let (_d, store) = fresh();
        store
            .commit_verified_turn(&produce(1, 0, GENESIS_ROOT))
            .unwrap();
        let mut forged = produce(2, 1, [0xEE; 32]);
        forged.prev_root = [0xEE; 32];
        let r = store.commit_verified_turn(&forged);
        assert!(matches!(
            r,
            Err(DurableError::Refused(ChainRefusal::RootMismatch { .. }))
        ));
        assert_eq!(
            store.commit_cursor().unwrap(),
            1,
            "durable cursor unmoved on refusal"
        );
        assert_eq!(
            store.lookup_by_ordinal(1).unwrap(),
            None,
            "the forgery did not persist"
        );
    }

    /// An ordinal gap is refused (no holes in the durable log).
    #[test]
    fn ordinal_gap_is_refused_durably() {
        let (_d, store) = fresh();
        store
            .commit_verified_turn(&produce(1, 0, GENESIS_ROOT))
            .unwrap();
        let head = store.head_root().unwrap().unwrap();
        let mut gapped = produce(2, 9, head);
        gapped.ordinal = 9;
        assert!(store.commit_verified_turn(&gapped).is_err());
        assert_eq!(store.commit_cursor().unwrap(), 1);
    }

    /// Replay of an already-committed turn is an idempotent no-op; a different turn
    /// at a taken ordinal is an Integrity refusal — over the durable store.
    #[test]
    fn replay_idempotent_collision_refused_durably() {
        let (_d, store) = fresh();
        let t0 = produce(1, 0, GENESIS_ROOT);
        store.commit_verified_turn(&t0).unwrap();
        store
            .commit_verified_turn(&produce(2, 1, store.head_root().unwrap().unwrap()))
            .unwrap();
        // replay t0 -> no-op success, cursor unchanged.
        assert_eq!(store.commit_verified_turn(&t0).unwrap(), 0);
        assert_eq!(store.commit_cursor().unwrap(), 2);
        // a DIFFERENT turn claiming ordinal 0 -> Integrity refusal.
        let mut collision = produce(999, 0, GENESIS_ROOT);
        collision.ordinal = 0;
        assert!(matches!(
            store.commit_verified_turn(&collision),
            Err(DurableError::Refused(ChainRefusal::Integrity(_)))
        ));
        assert_eq!(store.commit_cursor().unwrap(), 2);
    }

    /// THE DURABILITY TOOTH (the one a BTreeMap cannot prove): commit two turns,
    /// DROP the store + backend, reopen over the SAME file bytes — the durable head,
    /// cursor, log rows, and indices all recover, and the chain self-checks. A turn
    /// that committed is durable across a "persist-PD restart."
    #[test]
    fn commits_survive_drop_and_reopen_over_the_same_bytes() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("durable.redb");

        let (head, t0, t1);
        {
            let backend = RegionBackend::file(&path).unwrap();
            let store = DurableCommitStore::open(backend).unwrap();
            t0 = produce(1, 0, GENESIS_ROOT);
            store.commit_verified_turn(&t0).unwrap();
            t1 = produce(2, 1, store.head_root().unwrap().unwrap());
            store.commit_verified_turn(&t1).unwrap();
            head = store.head_root().unwrap();
            // store + backend dropped here — only the file bytes remain.
        }

        // Reopen over the SAME bytes (no replay — the cursor + head are read from
        // durable METADATA, and the rows are already in COMMIT_LOG).
        let backend = RegionBackend::file(&path).unwrap();
        let store = DurableCommitStore::open(backend).unwrap();
        assert_eq!(
            store.commit_cursor().unwrap(),
            2,
            "durable cursor recovered"
        );
        assert_eq!(store.head_root().unwrap(), head, "durable head recovered");
        assert_eq!(
            store.lookup_by_ordinal(0).unwrap(),
            Some(t0.clone()),
            "row 0 durable"
        );
        assert_eq!(
            store.lookup_by_ordinal(1).unwrap(),
            Some(t1.clone()),
            "row 1 durable"
        );
        assert_eq!(
            store.lookup_by_turn_hash(&t1.turn_hash).unwrap(),
            Some(t1.clone()),
            "the by-hash index is durable too"
        );
        store
            .verify_chain_intact()
            .expect("the recovered durable chain is intact");

        // And the recovered store enforces the chain from the durable head: the next
        // turn must chain onto exactly where the log left off.
        let t2 = produce(3, 2, store.head_root().unwrap().unwrap());
        assert_eq!(t2.prev_root, t1.ledger_root);
        assert_eq!(store.commit_verified_turn(&t2).unwrap(), 2);
    }

    /// `verify_chain_intact` catches a tampered durable store — fail-closed. We
    /// commit a clean chain, then write a bad record directly into the redb
    /// COMMIT_LOG (simulating on-disk tampering / corruption) and confirm the walk
    /// refuses it. (A real persist PD's store is cap-protected; this proves the
    /// SELF-CHECK tooth bites even if the bytes are altered out-of-band.)
    #[test]
    fn a_tampered_durable_chain_fails_the_self_check() {
        let (_d, store) = fresh();
        store
            .commit_verified_turn(&produce(1, 0, GENESIS_ROOT))
            .unwrap();
        store
            .commit_verified_turn(&produce(2, 1, store.head_root().unwrap().unwrap()))
            .unwrap();
        store.verify_chain_intact().expect("clean chain is intact");

        // Tamper: overwrite ordinal 1's record with one whose prev_root does NOT
        // chain onto ordinal 0's ledger_root.
        {
            let w = store.db.begin_write().unwrap();
            {
                let mut log = w.open_table(COMMIT_LOG).unwrap();
                let mut bad = produce(2, 1, [0x99; 32]); // prev_root no longer chains
                bad.prev_root = [0x99; 32];
                let encoded = encode_record(&bad);
                log.insert(1u64, encoded.as_slice()).unwrap();
            }
            w.commit().unwrap();
        }
        let r = store.verify_chain_intact();
        assert!(
            matches!(
                r,
                Err(DurableError::Refused(ChainRefusal::RootMismatch { .. }))
            ),
            "a tampered durable chain must fail the self-check closed, got {r:?}"
        );
    }

    /// The record codec round-trips (encode → decode is identity), including the
    /// variable-length touched_cells blob.
    #[test]
    fn record_codec_roundtrips() {
        let r = CommitRecord {
            ordinal: 42,
            height: 7,
            block_id: [0x11; 32],
            turn_hash: [0x22; 32],
            creator: [0x33; 32],
            receipt_hash: [0x44; 32],
            prev_root: [0x55; 32],
            ledger_root: [0x66; 32],
            touched_cells: vec![1, 2, 3, 4, 5, 250, 251],
        };
        let encoded = encode_record(&r);
        let decoded = decode_record(&encoded).unwrap();
        assert_eq!(decoded, r);
    }
}
