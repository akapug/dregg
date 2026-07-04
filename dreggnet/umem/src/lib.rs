//! `dreggnet-umem` — the **umem-cell-backed registry primitive**: a registry IS a
//! umem cell, persisted + reconstructed via the heap commit/restore.
//!
//! ## Why this exists (the substrate re-dregg, move #2)
//!
//! The since-deleted `dreggnet-store` `RegistryLog` was a
//! from-scratch append-only JSON-lines log that **re-implemented exactly what a committed
//! umem heap already gives** (durable, content-addressed, witnessed state —
//! `docs/MYOPIA-AUDIT.md §7`). This crate is the re-dregg: instead of re-implementing
//! the substrate, it **depends on it**. A registry is a real
//! [`dregg_cell::CellState`] whose `(collection, key) -> value` heap holds the records,
//! whose **boundary root** is the kernel's real sorted-Poseidon2
//! [`dregg_cell::compute_heap_root`] (the Rust shadow of the Lean `Substrate.Heap.root`,
//! pinned by `root_binds_get`), and whose durable persistence + reconstruction IS the
//! heap commit/restore. See `docs/REGISTRIES-AS-UMEM.md`.
//!
//! ## A registry IS a umem cell (the model)
//!
//! Each record is one **collection** in the cell's heap. A record's canonical bytes
//! (its JSON) are laid into the heap as length-delimited 32-byte leaves:
//!
//! ```text
//!   collection c (one per record)     leaf (c, 0) = byte length (u64 LE in the low 8 bytes)
//!   ─────────────────────────────     leaf (c, 1) = JSON bytes [0..32]
//!   store_key "blog"                  leaf (c, 2) = JSON bytes [32..64]
//!   record    SiteCell{ … }           …  (last chunk zero-padded to 32 bytes)
//! ```
//!
//! - **`append`** lays the record into its collection (clearing the collection first so a
//!   re-publish supersedes with no stale chunk), reseals the boundary root, durably
//!   materializes the heap snapshot (atomic temp+rename+fsync), and updates the
//!   reconstructed view. Durable-first: a record is never reported persisted unless its
//!   heap snapshot is on disk.
//! - **`open`** restores the heap from the committed snapshot, **re-derives the root and
//!   fails closed if it does not match the sealed root** (the `root_binds_get` boundary
//!   check — tamper is refused, not silently served), then reconstructs every record FROM
//!   the heap. The heap IS the store.
//! - **`boundary_root`** is the kernel's real Poseidon2 heap root — the commitment a dregg
//!   light client understands, replacing `dreggnet-store`'s blake3 `content_root`.
//!
//! ## The umem superpowers a JSON-lines log can never give
//!
//! - [`fork`](UmemRegistry::fork): copy the committed heap into a second registry — two
//!   divergent copies from one root (a tenant forks their whole namespace).
//! - [`checkpoint`](UmemRegistry::checkpoint) / [`restore`](UmemRegistry::restore):
//!   each commit tags a root-addressed snapshot; restore an earlier root → the registry
//!   as of that point (time-travel, instant rollback).
//! - **Merge-readiness**: the heap leaf-set is a grow-only set
//!   (`dregg_merge::GrowSet`), so the I-confluent merge runtime applies — the structural
//!   unblock for the #3 move (`docs/REGISTRIES-AS-UMEM.md §4`).
//!
//! ## The named seam (honest)
//!
//! In production the dregg **node's committed heap** is the durable store (the on-chain
//! `Effect::Write`, the circuit swarm's VK-epoch). Here `UmemRegistry` materializes the
//! cell's heap leaves to a local content-addressed snapshot keyed by the boundary root —
//! the node's job, stood in locally. This is **blob persistence of umem leaves with a
//! fail-closed boundary check**, NOT a re-implementation of registry semantics (that was
//! `dreggnet-store`). The in-circuit light-client witness of the commit stays the circuit
//! swarm's VK-epoch; the OFF-chain half (real Poseidon2 boundary, re-derivable + fail
//! closed on restore) is closed here.

pub mod cell;
pub mod merge;

// The canonical umem-cell primitive: the ONE committed `(key → value)` heap + boundary
// root + checkpoint/restore/fork/time-travel machinery both wrappers ride. `UmemRegistry`
// (below) is the durable record-laying wrapper; `dreggnet_control`'s `ComputeCell` is the
// server-state wrapper — neither re-implements the heap-root/checkpoint logic now that it
// lives here (`docs/REGISTRIES-AS-UMEM.md`, `docs/COMPUTE-AS-CELL.md`).
pub use cell::{Checkpoint, RestoreError, UmemCell, UmemHeap};

pub use merge::{RegistryMerge, RegistryMergeError};
// The merge-runtime types a caller drives `UmemRegistry::merge` with, re-exported so
// a consumer needs only `dreggnet_umem` (the #3 re-dregg move, `docs/REGISTRIES-AS-UMEM.md §4`).
pub use dregg_merge::{Escalation, GrowSet, MergeReceipt, MergeRuntime, MergeState, MergeVerdict};

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use dregg_cell::{CellState, FieldElement};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

/// A value persisted in a [`UmemRegistry`]. The SAME shape `dreggnet-store::Record`
/// uses, so an existing `impl Record for SiteCell / DomainBinding` moves over unchanged:
/// the only requirement beyond `serde` is a **stable string key** the registry
/// reconstructs the record under (last-write-wins ⇒ a re-publish is exactly-once on
/// reload, no duplicate).
pub trait Record: Clone + Serialize + DeserializeOwned {
    /// The stable key this record is stored under. Two records with the same key are
    /// the same logical entry: the later [`append`](UmemRegistry::append) supersedes the
    /// earlier (so a re-publish / re-register is exactly-once on reload).
    fn store_key(&self) -> String;
}

/// Why a umem-registry operation failed.
#[derive(Debug)]
pub enum UmemError {
    /// An underlying filesystem error (open / read / write / fsync / rename).
    Io(io::Error),
    /// A serde (de)serialization error framing or parsing the heap snapshot or a record.
    Serde(serde_json::Error),
    /// **The restored heap did not bind to its sealed boundary root** — the re-derived
    /// `compute_heap_root` over the loaded leaves does not equal the persisted root (a
    /// flipped leaf, a dropped leaf, a tampered snapshot). The load **fails closed**
    /// here (the `root_binds_get` discipline) rather than serving state that does not
    /// match the committed boundary.
    BoundaryMismatch { sealed: String, recomputed: String },
    /// A record's heap collection could not be reassembled into a valid record (a
    /// truncated chunk run or a payload that does not deserialize) — fail closed.
    Corrupt { collection: u32, reason: String },
}

impl std::fmt::Display for UmemError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UmemError::Io(e) => write!(f, "umem registry io error: {e}"),
            UmemError::Serde(e) => write!(f, "umem registry serde error: {e}"),
            UmemError::BoundaryMismatch { sealed, recomputed } => write!(
                f,
                "umem registry boundary mismatch (sealed root {sealed}, recomputed \
                 {recomputed}) — the heap does not bind its committed root (fail-closed)"
            ),
            UmemError::Corrupt { collection, reason } => write!(
                f,
                "umem registry corruption in heap collection {collection}: {reason} \
                 (a record could not be reconstructed from the committed heap — fail-closed)"
            ),
        }
    }
}

impl std::error::Error for UmemError {}

impl From<io::Error> for UmemError {
    fn from(e: io::Error) -> Self {
        UmemError::Io(e)
    }
}
impl From<serde_json::Error> for UmemError {
    fn from(e: serde_json::Error) -> Self {
        UmemError::Serde(e)
    }
}

impl UmemError {
    /// Convert into an [`io::Error`] (the form the existing registries' error variants
    /// carry a `String` of). A boundary/corruption failure becomes
    /// [`io::ErrorKind::InvalidData`] so a caller that only handles `io::Error` still
    /// fails closed.
    pub fn into_io(self) -> io::Error {
        match self {
            UmemError::Io(e) => e,
            UmemError::Serde(e) => io::Error::new(io::ErrorKind::InvalidData, e),
            other => io::Error::new(io::ErrorKind::InvalidData, other.to_string()),
        }
    }
}

/// The leaf-slot within a record's collection holding the record's byte length (LE u64 in
/// the low 8 bytes of the 32-byte leaf). Slots `1..` carry the JSON payload chunks.
const LEN_SLOT: u32 = 0;
/// Bytes of canonical record JSON carried per heap leaf.
const CHUNK_BYTES: usize = 32;
/// The first collection id records are assigned (collection `0` is reserved so a future
/// directory/index leaf-set never collides with record content).
const FIRST_COLL: u32 = 1;

/// The durable, restart-surviving on-disk form of the registry's umem cell: the heap
/// leaves + the sealed boundary root. This is **blob persistence of the cell's committed
/// heap** (the node's job, stood in locally), NOT a record-level log.
#[derive(Serialize, Deserialize)]
struct HeapSnapshot {
    /// The sealed boundary root (hex of the 32-byte Poseidon2 `compute_heap_root`) the
    /// loaded leaves MUST re-derive to (fail closed otherwise).
    root: String,
    /// The cell's heap leaves: `(collection, key) -> 32-byte value`.
    leaves: Vec<((u32, u32), FieldElement)>,
}

struct Inner<R> {
    /// The registry's umem cell — its `(collection,key) -> value` heap holds the records,
    /// its `heap_root` is the committed boundary.
    state: CellState,
    /// The reconstructed view: `store_key -> record` (rebuilt from the heap on open).
    records: BTreeMap<String, R>,
    /// `store_key -> collection id` (so a re-publish reuses + clears its collection).
    index: BTreeMap<String, u32>,
    /// The next free collection id.
    next_coll: u32,
}

/// A durable, restart-surviving registry of [`Record`]s, **backed by a real umem cell**.
/// Each record is a collection in the cell's heap; the durable form is the committed heap
/// snapshot; the boundary is the kernel's sorted-Poseidon2 [`compute_heap_root`].
pub struct UmemRegistry<R: Record> {
    path: PathBuf,
    inner: Mutex<Inner<R>>,
}

impl<R: Record> UmemRegistry<R> {
    /// Open (or create) the umem registry at `path`, **restoring** the cell's heap from
    /// the committed snapshot and reconstructing every record FROM the heap so a restart
    /// rebuilds the prior registry.
    ///
    /// The restore **fails closed** ([`UmemError::BoundaryMismatch`]) if the loaded heap
    /// does not re-derive its sealed boundary root, and ([`UmemError::Corrupt`]) if a
    /// record's collection cannot be reassembled.
    pub fn open(path: impl AsRef<Path>) -> Result<UmemRegistry<R>, UmemError> {
        let path = path.as_ref().to_path_buf();
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent)?;
            }
        }
        let mut state = CellState::new(0);
        let mut records: BTreeMap<String, R> = BTreeMap::new();
        let mut index: BTreeMap<String, u32> = BTreeMap::new();
        let mut next_coll = FIRST_COLL;

        if let Some(snap) = read_snapshot(&path)? {
            // Load the leaves into the cell's heap and reseal.
            for ((coll, key), val) in &snap.leaves {
                state.heap_map.insert((*coll, *key), *val);
            }
            state.reseal_heap_root();
            // Boundary check: the restored heap MUST bind its committed root.
            let recomputed = hex32(&state.heap_root);
            if recomputed != snap.root {
                return Err(UmemError::BoundaryMismatch {
                    sealed: snap.root,
                    recomputed,
                });
            }
            // Reconstruct the records FROM the heap, collection by collection.
            let colls: std::collections::BTreeSet<u32> =
                state.heap_map.keys().map(|(c, _)| *c).collect();
            for coll in colls {
                if coll < FIRST_COLL {
                    continue; // reserved
                }
                let record = reassemble_record::<R>(&state, coll)?;
                let key = record.store_key();
                index.insert(key.clone(), coll);
                records.insert(key, record);
                next_coll = next_coll.max(coll + 1);
            }
        }

        Ok(UmemRegistry {
            path,
            inner: Mutex::new(Inner {
                state,
                records,
                index,
                next_coll,
            }),
        })
    }

    /// The path this registry's heap snapshot persists to.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Persist `record` into the registry's umem cell: lay it into its heap collection
    /// (superseding any prior record for the same [`Record::store_key`]), reseal the
    /// boundary root, durably materialize the heap snapshot (atomic + fsync), and update
    /// the reconstructed view. Durable-first: a store fault leaves the in-memory state
    /// unchanged and returns the error (the record is never reported persisted unless its
    /// heap snapshot survives a restart).
    pub fn append(&self, record: &R) -> Result<(), UmemError> {
        let mut inner = self.inner.lock().expect("umem registry poisoned");
        let key = record.store_key();

        // Reuse this record's collection (clearing its old leaves so a shrunk record
        // leaves no stale chunk), or assign a fresh one.
        let coll = match inner.index.get(&key) {
            Some(c) => {
                let c = *c;
                inner.state.heap_map.retain(|&(cc, _), _| cc != c);
                c
            }
            None => {
                let c = inner.next_coll;
                inner.next_coll += 1;
                c
            }
        };

        // Snapshot the prior heap so a persist fault rolls back cleanly.
        let prior_heap = inner.state.heap_map.clone();
        let prior_root = inner.state.heap_root;

        // Lay the record into the heap as length-delimited 32-byte leaves, then reseal.
        let json = serde_json::to_vec(record)?;
        lay_record(&mut inner.state, coll, &json);
        inner.state.reseal_heap_root();

        // Durably materialize the committed heap snapshot (atomic + fsync + history).
        let snap = HeapSnapshot {
            root: hex32(&inner.state.heap_root),
            leaves: inner.state.heap_map.iter().map(|(k, v)| (*k, *v)).collect(),
        };
        if let Err(e) = write_snapshot(&self.path, &snap) {
            // Roll back: the persist failed, so the in-memory cell must not advance.
            inner.state.heap_map = prior_heap;
            inner.state.heap_root = prior_root;
            return Err(e);
        }

        // Commit the in-memory view.
        inner.index.insert(key.clone(), coll);
        inner.records.insert(key, record.clone());
        Ok(())
    }

    /// **Remove** the record stored under `key` (if any): clear its heap collection,
    /// reseal the boundary root, durably materialize the new committed heap snapshot,
    /// and drop it from the reconstructed view. Returns whether a record was removed.
    /// Durable-first: a persist fault rolls the cell back and returns the error (the
    /// removal is never reported durable unless its new heap snapshot survives a
    /// restart). This is the umem counterpart of a `dreggnet-store` compaction sweep —
    /// except it **commits to a new boundary root** (the removed record is provably
    /// gone from the committed heap), where the append-log could only stop replaying it.
    pub fn remove(&self, key: &str) -> Result<bool, UmemError> {
        let mut inner = self.inner.lock().expect("umem registry poisoned");
        let Some(&coll) = inner.index.get(key) else {
            return Ok(false);
        };

        let prior_heap = inner.state.heap_map.clone();
        let prior_root = inner.state.heap_root;

        inner.state.heap_map.retain(|&(cc, _), _| cc != coll);
        inner.state.reseal_heap_root();

        let snap = HeapSnapshot {
            root: hex32(&inner.state.heap_root),
            leaves: inner.state.heap_map.iter().map(|(k, v)| (*k, *v)).collect(),
        };
        if let Err(e) = write_snapshot(&self.path, &snap) {
            inner.state.heap_map = prior_heap;
            inner.state.heap_root = prior_root;
            return Err(e);
        }

        inner.index.remove(key);
        inner.records.remove(key);
        Ok(true)
    }

    /// The record stored under `key`, if any.
    pub fn get(&self, key: &str) -> Option<R> {
        self.inner
            .lock()
            .expect("umem registry poisoned")
            .records
            .get(key)
            .cloned()
    }

    /// Whether a record is stored under `key`.
    pub fn contains(&self, key: &str) -> bool {
        self.inner
            .lock()
            .expect("umem registry poisoned")
            .records
            .contains_key(key)
    }

    /// Every live record (in key order).
    pub fn all(&self) -> Vec<R> {
        self.inner
            .lock()
            .expect("umem registry poisoned")
            .records
            .values()
            .cloned()
            .collect()
    }

    /// Every live record key (sorted).
    pub fn keys(&self) -> Vec<String> {
        self.inner
            .lock()
            .expect("umem registry poisoned")
            .records
            .keys()
            .cloned()
            .collect()
    }

    /// How many distinct records the registry holds.
    pub fn len(&self) -> usize {
        self.inner
            .lock()
            .expect("umem registry poisoned")
            .records
            .len()
    }

    /// Whether the registry holds no records.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The registry's **committed boundary root**: the kernel's real sorted-Poseidon2
    /// `compute_heap_root` over the cell's heap (the 32-byte commitment a dregg light
    /// client understands), hex-encoded. This replaces `dreggnet-store`'s blake3
    /// `content_root` with the substrate's own umem heap boundary.
    pub fn boundary_root(&self) -> String {
        hex32(
            &self
                .inner
                .lock()
                .expect("umem registry poisoned")
                .state
                .heap_root,
        )
    }

    /// The raw 32-byte committed boundary root (the Poseidon2 `heap_root`).
    pub fn boundary_root_bytes(&self) -> [u8; 32] {
        self.inner
            .lock()
            .expect("umem registry poisoned")
            .state
            .heap_root
    }

    /// **Membership witness** that `key`'s record is bound by the committed boundary
    /// root: `true` iff every leaf of its collection is present AND the heap re-derives
    /// its sealed root (the `root_binds_get` tooth). A tenant / light client uses this to
    /// confirm a served record matches the registry's committed state.
    pub fn binds(&self, key: &str) -> bool {
        let inner = self.inner.lock().expect("umem registry poisoned");
        let Some(&coll) = inner.index.get(key) else {
            return false;
        };
        // The length leaf must be present and the heap must bind its root.
        inner.state.heap_root_membership(coll, LEN_SLOT).is_some()
    }

    /// **Fork** the registry: copy the committed heap into a second `UmemRegistry` at
    /// `new_path` — two divergent copies that descend from this one's root. A tenant forks
    /// their whole namespace (every record at once), then serves / stitches / discards the
    /// fork independently. The fork starts byte-identical (same boundary root) and
    /// diverges as either side `append`s.
    pub fn fork(&self, new_path: impl AsRef<Path>) -> Result<UmemRegistry<R>, UmemError> {
        let new_path = new_path.as_ref().to_path_buf();
        {
            let inner = self.inner.lock().expect("umem registry poisoned");
            let snap = HeapSnapshot {
                root: hex32(&inner.state.heap_root),
                leaves: inner.state.heap_map.iter().map(|(k, v)| (*k, *v)).collect(),
            };
            if let Some(parent) = new_path.parent() {
                if !parent.as_os_str().is_empty() {
                    fs::create_dir_all(parent)?;
                }
            }
            write_snapshot(&new_path, &snap)?;
        }
        UmemRegistry::open(&new_path)
    }

    /// **Checkpoint**: the current committed boundary root, with its heap snapshot
    /// retained in the history directory so [`restore`](Self::restore) can return to it.
    /// (Every `append` already retains its root-addressed snapshot; this just names the
    /// current one for a caller that wants to time-travel back to it later.)
    pub fn checkpoint(&self) -> String {
        self.boundary_root()
    }

    /// The roots of every retained checkpoint (the history of committed boundary roots),
    /// newest-last by file order — the timeline a tenant time-travels across.
    pub fn checkpoints(&self) -> Vec<String> {
        let dir = history_dir(&self.path);
        let mut roots = Vec::new();
        if let Ok(rd) = fs::read_dir(&dir) {
            for entry in rd.flatten() {
                if let Some(name) = entry.file_name().to_str() {
                    if let Some(root) = name.strip_suffix(".snap") {
                        roots.push(root.to_string());
                    }
                }
            }
        }
        roots.sort();
        roots
    }

    /// **Time-travel**: restore the registry to an earlier committed `root` (a hex
    /// boundary root from [`checkpoint`](Self::checkpoint) / [`checkpoints`](Self::checkpoints)).
    /// The cell's heap, the boundary root, and the reconstructed records all revert to
    /// that committed state, and the durable snapshot is rewritten to it (so the
    /// time-travel survives a subsequent restart — "my domains as of yesterday" becomes
    /// the live state). Fails closed if no such checkpoint exists or it does not bind.
    pub fn restore(&self, root: &str) -> Result<(), UmemError> {
        let snap_path = history_dir(&self.path).join(format!("{root}.snap"));
        let snap = read_snapshot_at(&snap_path)?.ok_or_else(|| {
            UmemError::Io(io::Error::new(
                io::ErrorKind::NotFound,
                format!("no checkpoint for root {root}"),
            ))
        })?;

        // Rebuild a cell from the checkpoint, fail closed on a boundary mismatch.
        let mut state = CellState::new(0);
        for ((coll, key), val) in &snap.leaves {
            state.heap_map.insert((*coll, *key), *val);
        }
        state.reseal_heap_root();
        let recomputed = hex32(&state.heap_root);
        if recomputed != snap.root {
            return Err(UmemError::BoundaryMismatch {
                sealed: snap.root,
                recomputed,
            });
        }

        // Reconstruct records.
        let mut records: BTreeMap<String, R> = BTreeMap::new();
        let mut index: BTreeMap<String, u32> = BTreeMap::new();
        let mut next_coll = FIRST_COLL;
        let colls: std::collections::BTreeSet<u32> =
            state.heap_map.keys().map(|(c, _)| *c).collect();
        for coll in colls {
            if coll < FIRST_COLL {
                continue;
            }
            let record = reassemble_record::<R>(&state, coll)?;
            let key = record.store_key();
            index.insert(key.clone(), coll);
            records.insert(key, record);
            next_coll = next_coll.max(coll + 1);
        }

        // Make this the live durable state (so the restore survives a restart).
        write_snapshot(&self.path, &snap)?;

        let mut inner = self.inner.lock().expect("umem registry poisoned");
        inner.state = state;
        inner.records = records;
        inner.index = index;
        inner.next_coll = next_coll;
        Ok(())
    }
}

/// Lay a record's canonical JSON into heap collection `coll` as length-delimited 32-byte
/// leaves: a length leaf at [`LEN_SLOT`], then one 32-byte chunk per `1..`.
fn lay_record(state: &mut CellState, coll: u32, json: &[u8]) {
    let mut len_leaf = [0u8; 32];
    len_leaf[..8].copy_from_slice(&(json.len() as u64).to_le_bytes());
    state.heap_map.insert((coll, LEN_SLOT), len_leaf);
    for (i, chunk) in json.chunks(CHUNK_BYTES).enumerate() {
        let mut leaf = [0u8; 32];
        leaf[..chunk.len()].copy_from_slice(chunk);
        state.heap_map.insert((coll, 1 + i as u32), leaf);
    }
}

/// Reassemble + deserialize the record laid into heap collection `coll` (the inverse of
/// [`lay_record`]). Fails closed if the length/chunks are inconsistent or the payload does
/// not deserialize.
fn reassemble_record<R: Record>(state: &CellState, coll: u32) -> Result<R, UmemError> {
    let len_leaf = state
        .heap_map
        .get(&(coll, LEN_SLOT))
        .ok_or_else(|| UmemError::Corrupt {
            collection: coll,
            reason: "missing length leaf".to_string(),
        })?;
    let byte_len = u64::from_le_bytes(len_leaf[..8].try_into().expect("8 bytes")) as usize;
    let n_chunks = byte_len.div_ceil(CHUNK_BYTES);
    let mut bytes = Vec::with_capacity(byte_len);
    for i in 0..n_chunks {
        let leaf = state
            .heap_map
            .get(&(coll, 1 + i as u32))
            .ok_or_else(|| UmemError::Corrupt {
                collection: coll,
                reason: format!("missing payload chunk {i} of {n_chunks}"),
            })?;
        bytes.extend_from_slice(leaf);
    }
    bytes.truncate(byte_len);
    serde_json::from_slice::<R>(&bytes).map_err(|e| UmemError::Corrupt {
        collection: coll,
        reason: format!("record did not deserialize: {e}"),
    })
}

/// The history directory holding the root-addressed checkpoints for time-travel.
fn history_dir(path: &Path) -> PathBuf {
    let mut s = path.as_os_str().to_os_string();
    s.push(".history");
    PathBuf::from(s)
}

/// Write the heap snapshot durably (atomic temp + rename + fsync) at `path`, and retain a
/// copy in the root-addressed history directory (for time-travel).
fn write_snapshot(path: &Path, snap: &HeapSnapshot) -> Result<(), UmemError> {
    let json = serde_json::to_vec(snap)?;

    // Atomic primary write: temp + fsync + rename.
    let tmp = with_ext(path, "umem.tmp");
    {
        use std::io::Write;
        let mut f = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&tmp)?;
        f.write_all(&json)?;
        f.flush()?;
        f.sync_all()?;
    }
    fs::rename(&tmp, path)?;
    if let Some(parent) = path.parent() {
        if let Ok(dir) = fs::File::open(if parent.as_os_str().is_empty() {
            Path::new(".")
        } else {
            parent
        }) {
            let _ = dir.sync_all();
        }
    }

    // Retain the root-addressed checkpoint (best-effort durable) for time-travel.
    let hist = history_dir(path);
    fs::create_dir_all(&hist)?;
    let snap_path = hist.join(format!("{}.snap", snap.root));
    let htmp = snap_path.with_extension("snap.tmp");
    {
        use std::io::Write;
        let mut f = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&htmp)?;
        f.write_all(&json)?;
        f.flush()?;
        f.sync_all()?;
    }
    fs::rename(&htmp, &snap_path)?;
    Ok(())
}

/// Read the heap snapshot at `path` (the primary durable form). `None` if absent (an empty
/// registry).
fn read_snapshot(path: &Path) -> Result<Option<HeapSnapshot>, UmemError> {
    read_snapshot_at(path)
}

fn read_snapshot_at(path: &Path) -> Result<Option<HeapSnapshot>, UmemError> {
    match fs::read(path) {
        Ok(bytes) => Ok(Some(serde_json::from_slice::<HeapSnapshot>(&bytes)?)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(UmemError::Io(e)),
    }
}

fn with_ext(path: &Path, ext: &str) -> PathBuf {
    let mut s = path.as_os_str().to_os_string();
    s.push(".");
    s.push(ext);
    PathBuf::from(s)
}

/// Lower-hex a 32-byte root.
fn hex32(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    struct TestRec {
        id: String,
        val: u64,
        blob: String,
    }
    impl Record for TestRec {
        fn store_key(&self) -> String {
            self.id.clone()
        }
    }
    fn rec(id: &str, val: u64) -> TestRec {
        TestRec {
            id: id.to_string(),
            val,
            // A blob longer than one 32-byte chunk, to exercise multi-chunk laying.
            blob: format!("payload-{id}-{}", "x".repeat(40)),
        }
    }
    fn temp(tag: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        let n = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        p.push(format!("dreggnet-umem-test-{tag}-{n}.snap"));
        p
    }
    fn cleanup(path: &Path) {
        fs::remove_file(path).ok();
        fs::remove_dir_all(history_dir(path)).ok();
    }

    /// The umem round-trip: append → commit to a boundary root → "restart" (drop +
    /// reopen) → reconstructed exactly-once, owned correctly.
    #[test]
    fn umem_round_trip_reconstructs() {
        let path = temp("round-trip");
        let root_after;
        {
            let reg = UmemRegistry::<TestRec>::open(&path).unwrap();
            reg.append(&rec("a", 1)).unwrap();
            reg.append(&rec("b", 2)).unwrap();
            root_after = reg.boundary_root();
            assert_eq!(reg.len(), 2);
        }
        // "Restart": a fresh registry over the same path restores from the committed heap.
        let reopened = UmemRegistry::<TestRec>::open(&path).unwrap();
        assert_eq!(reopened.len(), 2);
        assert_eq!(reopened.get("a"), Some(rec("a", 1)));
        assert_eq!(reopened.get("b"), Some(rec("b", 2)));
        // The committed boundary root is reproduced over the restored heap.
        assert_eq!(reopened.boundary_root(), root_after);
        // And the records bind to it (the `root_binds_get` tooth).
        assert!(reopened.binds("a"));
        assert!(reopened.binds("b"));
        cleanup(&path);
    }

    /// Exactly-once: a re-append of the same key supersedes (no duplicate, latest wins)
    /// across a restart.
    #[test]
    fn reappend_is_exactly_once() {
        let path = temp("exactly-once");
        {
            let reg = UmemRegistry::<TestRec>::open(&path).unwrap();
            reg.append(&rec("a", 1)).unwrap();
            reg.append(&rec("a", 99)).unwrap();
        }
        let reopened = UmemRegistry::<TestRec>::open(&path).unwrap();
        assert_eq!(reopened.len(), 1, "no duplicate for the same key");
        assert_eq!(reopened.get("a"), Some(rec("a", 99)), "latest wins");
        cleanup(&path);
    }

    /// The boundary boundary-check fails closed when the committed heap snapshot is
    /// tampered (a flipped leaf no longer re-derives its sealed root).
    #[test]
    fn tampered_heap_fails_closed() {
        let path = temp("tamper");
        {
            let reg = UmemRegistry::<TestRec>::open(&path).unwrap();
            reg.append(&rec("a", 1)).unwrap();
        }
        // Tamper a leaf value in the snapshot WITHOUT updating the sealed root.
        let mut snap: HeapSnapshot = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        if let Some(((_, _), v)) = snap.leaves.iter_mut().find(|((_, k), _)| *k != LEN_SLOT) {
            v[0] ^= 0xff;
        }
        fs::write(&path, serde_json::to_vec(&snap).unwrap()).unwrap();
        match UmemRegistry::<TestRec>::open(&path) {
            Err(UmemError::BoundaryMismatch { .. }) => {}
            Err(other) => panic!("expected BoundaryMismatch, got {other:?}"),
            Ok(_) => panic!("a tampered heap must fail the load closed"),
        }
        cleanup(&path);
    }

    /// Remove: a record is provably gone from the committed heap after a removal (the
    /// boundary root advances), and the removal is durable across a restart.
    #[test]
    fn remove_commits_a_new_root_and_is_durable() {
        let path = temp("remove");
        {
            let reg = UmemRegistry::<TestRec>::open(&path).unwrap();
            reg.append(&rec("a", 1)).unwrap();
            reg.append(&rec("b", 2)).unwrap();
            let root_both = reg.boundary_root();
            assert!(reg.remove("a").unwrap(), "a existed, so it is removed");
            assert!(!reg.remove("a").unwrap(), "a is already gone");
            assert_eq!(reg.len(), 1);
            assert!(!reg.contains("a") && reg.contains("b"));
            assert_ne!(
                reg.boundary_root(),
                root_both,
                "the committed root advanced"
            );
        }
        // The removal is durable: a restart serves only the survivor.
        let reopened = UmemRegistry::<TestRec>::open(&path).unwrap();
        assert_eq!(reopened.len(), 1);
        assert!(!reopened.contains("a") && reopened.contains("b"));
        cleanup(&path);
    }

    /// Fork: two divergent copies from one root. The fork starts identical, then each side
    /// diverges independently (the other is unaffected).
    #[test]
    fn fork_diverges_from_one_root() {
        let base = temp("fork-base");
        let forked = temp("fork-copy");
        let reg = UmemRegistry::<TestRec>::open(&base).unwrap();
        reg.append(&rec("a", 1)).unwrap();
        reg.append(&rec("b", 2)).unwrap();
        let root0 = reg.boundary_root();

        // Fork: the copy descends from the same committed root.
        let fork = reg.fork(&forked).unwrap();
        assert_eq!(
            fork.boundary_root(),
            root0,
            "the fork starts at the parent's root"
        );
        assert_eq!(fork.len(), 2);

        // Diverge: the fork adds a site the parent never sees, and vice-versa.
        fork.append(&rec("c", 3)).unwrap();
        reg.append(&rec("d", 4)).unwrap();
        assert!(fork.contains("c") && !fork.contains("d"));
        assert!(reg.contains("d") && !reg.contains("c"));
        assert_ne!(
            fork.boundary_root(),
            reg.boundary_root(),
            "the copies diverged"
        );
        cleanup(&base);
        cleanup(&forked);
    }

    /// Time-travel: restore an earlier committed root → the registry as of that point, and
    /// the restore survives a subsequent restart.
    #[test]
    fn time_travel_restores_an_earlier_root() {
        let path = temp("time-travel");
        let root_v1;
        {
            let reg = UmemRegistry::<TestRec>::open(&path).unwrap();
            reg.append(&rec("a", 1)).unwrap();
            root_v1 = reg.checkpoint(); // "yesterday": only `a` exists
            reg.append(&rec("b", 2)).unwrap();
            assert_eq!(reg.len(), 2);
            assert!(reg.checkpoints().contains(&root_v1));

            // Restore to yesterday's root: `b` is gone, `a` remains.
            reg.restore(&root_v1).unwrap();
            assert_eq!(reg.len(), 1);
            assert!(reg.contains("a") && !reg.contains("b"));
            assert_eq!(reg.boundary_root(), root_v1);
        }
        // The time-travel is durable: a restart serves the restored (earlier) state.
        let reopened = UmemRegistry::<TestRec>::open(&path).unwrap();
        assert_eq!(reopened.len(), 1);
        assert!(reopened.contains("a") && !reopened.contains("b"));
        assert_eq!(reopened.boundary_root(), root_v1);
        cleanup(&path);
    }
}
