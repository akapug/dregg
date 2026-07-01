//! `UmemCell` — the **canonical in-memory umem-cell primitive**: a committed
//! `(key → value)` heap whose boundary is the real sorted-Poseidon2
//! [`dregg_cell::compute_heap_root`], with checkpoint / restore / fork / time-travel.
//!
//! ## One umem heap, many wrappers
//!
//! This is the ONE umem-heap machinery the crate's wrappers ride — factored out so
//! neither re-implements it (`docs/REGISTRIES-AS-UMEM.md`, `docs/COMPUTE-AS-CELL.md`):
//!
//! - [`UmemRegistry`](crate::UmemRegistry) — the durable, record-laying wrapper
//!   (file-backed, the #2 re-dregg): a registry IS a umem cell whose records are laid
//!   into the heap as length-delimited leaves, persisted via the committed snapshot.
//! - `dreggnet_control::compute_cell::ComputeCell` — the server-state wrapper (the #1
//!   compute-as-cell lane): a persistent server's working state IS a umem cell whose
//!   sleep/wake/fork/rollback are operations over this heap's boundary root.
//!
//! Both hold a `(key → value)` heap, seal it to a `dregg_cell` boundary root, and
//! checkpoint / restore / fork / time-travel over that root. Before this primitive
//! existed, `ComputeCell` re-implemented the heap-root + checkpoint/restore/fork/
//! time-travel over `dregg-circuit` directly — the duplication this module retires.
//!
//! ## The boundary root (real, no stand-in)
//!
//! [`UmemHeap::boundary_root`] lays each `(key, value)` into a fresh
//! `(collection, slot) → 32-byte leaf` heap — a length-delimited header leaf binding
//! the key + value byte lengths, then the key bytes, then the value bytes, each as
//! 32-byte chunks at successive slots — and folds it through the kernel's real
//! sorted-Poseidon2 [`dregg_cell::compute_heap_root`] (the Rust shadow of the Lean
//! `Substrate.Heap.root`, pinned by `root_binds_get`). A `BTreeMap` canonicalizes key
//! order so the root is insertion-order-independent; the length-delimited laying binds
//! key + value injectively so a one-byte change to either moves the root. **The
//! boundary IS the state.**

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use dregg_cell::{FieldElement, compute_heap_root};

/// Bytes of key/value carried per heap leaf.
const CHUNK_BYTES: usize = 32;
/// The first collection id a heap entry is laid into (collection `0` is reserved so a
/// future directory/index leaf-set never collides with entry content).
const FIRST_COLL: u32 = 1;

/// A committed `(key → value)` umem heap. A `BTreeMap` canonicalizes key order so the
/// boundary root is insertion-order-independent.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct UmemHeap {
    /// The committed cells (key → value bytes).
    cells: BTreeMap<String, Vec<u8>>,
}

impl UmemHeap {
    /// An empty heap.
    pub fn new() -> UmemHeap {
        UmemHeap {
            cells: BTreeMap::new(),
        }
    }

    /// Write `value` at `key` (last-write-wins), returning the prior value if any.
    pub fn write(&mut self, key: impl Into<String>, value: impl Into<Vec<u8>>) -> Option<Vec<u8>> {
        self.cells.insert(key.into(), value.into())
    }

    /// Read the value at `key`.
    pub fn read(&self, key: &str) -> Option<&[u8]> {
        self.cells.get(key).map(|v| v.as_slice())
    }

    /// Remove the cell at `key`, returning its value if present.
    pub fn remove(&mut self, key: &str) -> Option<Vec<u8>> {
        self.cells.remove(key)
    }

    /// How many cells the heap holds.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the heap is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Iterate the committed cells (key order).
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.cells.iter().map(|(k, v)| (k.as_str(), v.as_slice()))
    }

    /// The **boundary root** of this heap — the kernel's real sorted-Poseidon2
    /// [`dregg_cell::compute_heap_root`] over a length-delimited laying of the cells
    /// (64-hex). A one-byte change to any key or value moves the root (injective,
    /// anti-vacuous); insertion order does not (the `BTreeMap` canonicalizes).
    pub fn boundary_root(&self) -> String {
        let mut map: BTreeMap<(u32, u32), FieldElement> = BTreeMap::new();
        for (i, (key, value)) in self.cells.iter().enumerate() {
            let coll = FIRST_COLL + i as u32;
            // Header leaf: key length ‖ value length (LE u64 each), so a server cannot
            // shift bytes between key and value without moving the root.
            let mut header = [0u8; 32];
            header[..8].copy_from_slice(&(key.len() as u64).to_le_bytes());
            header[8..16].copy_from_slice(&(value.len() as u64).to_le_bytes());
            map.insert((coll, 0), header);
            // Key bytes, then value bytes, each as 32-byte chunks at successive slots.
            let mut slot = 1u32;
            for chunk in key.as_bytes().chunks(CHUNK_BYTES) {
                let mut leaf = [0u8; 32];
                leaf[..chunk.len()].copy_from_slice(chunk);
                map.insert((coll, slot), leaf);
                slot += 1;
            }
            for chunk in value.chunks(CHUNK_BYTES) {
                let mut leaf = [0u8; 32];
                leaf[..chunk.len()].copy_from_slice(chunk);
                map.insert((coll, slot), leaf);
                slot += 1;
            }
        }
        hex32(&compute_heap_root(&map))
    }
}

/// A captured checkpoint: a committed boundary `root` and the reified `image` that
/// produced it. The commitment (`root`) is durable; the `image` is the reified state a
/// restore reproduces + re-witnesses before adopting.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Checkpoint {
    /// The committed boundary root (64-hex).
    pub root: String,
    /// The reified heap image that folds back to `root`.
    pub image: UmemHeap,
}

impl Checkpoint {
    /// **Honestly** reify `image` into a checkpoint: the root is computed FROM the
    /// image, so [`Checkpoint::verify`] is always true for one built this way.
    pub fn reify(image: UmemHeap) -> Checkpoint {
        let root = image.boundary_root();
        Checkpoint { root, image }
    }

    /// Re-witness this checkpoint: recompute the boundary root of the reified image and
    /// check it reproduces the committed `root`. A tampered image (one that no longer
    /// folds back to `root`) fails — the fail-closed gate a restore runs.
    pub fn verify(&self) -> bool {
        self.image.boundary_root() == self.root
    }
}

/// Why a restore / wake / time-travel refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RestoreError {
    /// The reified image does not reproduce the committed boundary root — the
    /// fail-closed gate: a wake never resumes from an image that is not the genuine
    /// committed state.
    ImageRootMismatch {
        /// The committed root the image was supposed to reproduce.
        committed: String,
        /// The root the (tampered) image actually folds to.
        reified: String,
    },
    /// No checkpoint for this boundary root was ever committed by this cell (time-travel
    /// to a root not in the log).
    UnknownRoot(String),
}

impl std::fmt::Display for RestoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RestoreError::ImageRootMismatch { committed, reified } => write!(
                f,
                "checkpoint image does not reproduce its committed boundary root \
                 (committed {committed}, reified {reified}): restore refused"
            ),
            RestoreError::UnknownRoot(root) => {
                write!(
                    f,
                    "no checkpoint for boundary root {root} in this cell's log"
                )
            }
        }
    }
}

impl std::error::Error for RestoreError {}

/// A **umem cell** — the canonical unit: a live witnessed `(key → value)` working-state
/// heap + a checkpoint log (the time-travel record). Checkpoint/restore/fork/time-travel
/// are operations over its boundary root. Wrappers add identity + domain semantics
/// (server state, registry records) on top.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct UmemCell {
    /// The live working state (mutating between checkpoints).
    live: UmemHeap,
    /// The committed checkpoints, oldest first — the time-travel log.
    checkpoints: Vec<Checkpoint>,
}

impl UmemCell {
    /// A fresh umem cell: an empty heap, an empty log.
    pub fn new() -> UmemCell {
        UmemCell::default()
    }

    /// The live working-state heap (read-only).
    pub fn live(&self) -> &UmemHeap {
        &self.live
    }

    /// The live working-state heap (mutable) — writes land here between checkpoints.
    pub fn live_mut(&mut self) -> &mut UmemHeap {
        &mut self.live
    }

    /// The boundary root of the **live** (uncommitted) state.
    pub fn live_root(&self) -> String {
        self.live.boundary_root()
    }

    /// The most recently committed boundary root, if the cell has checkpointed.
    pub fn latest_checkpoint_root(&self) -> Option<&str> {
        self.checkpoints.last().map(|cp| cp.root.as_str())
    }

    /// Every committed boundary root, oldest first (the time-travel log).
    pub fn checkpoint_roots(&self) -> Vec<String> {
        self.checkpoints.iter().map(|cp| cp.root.clone()).collect()
    }

    /// **Checkpoint.** Commit the live state to a [`Checkpoint`], append it to the log,
    /// and return the boundary root. Idempotent in value: two checkpoints of an
    /// unchanged heap yield the same root, and an identical trailing root is de-duped so
    /// a stop/stop does not bloat the log (while still guaranteeing the root is present
    /// for a later time-travel).
    pub fn checkpoint(&mut self) -> String {
        let cp = Checkpoint::reify(self.live.clone());
        let root = cp.root.clone();
        if self.checkpoints.last().map(|c| &c.root) != Some(&root) {
            self.checkpoints.push(cp);
        }
        root
    }

    /// **Restore from an explicit checkpoint**, verifying the reified image reproduces
    /// its committed root before adopting it. Fail-closed: a checkpoint whose image does
    /// not fold to its `root` is refused ([`RestoreError::ImageRootMismatch`]) and the
    /// live state is left untouched.
    pub fn restore_checkpoint(&mut self, cp: &Checkpoint) -> Result<(), RestoreError> {
        if !cp.verify() {
            return Err(RestoreError::ImageRootMismatch {
                committed: cp.root.clone(),
                reified: cp.image.boundary_root(),
            });
        }
        self.live = cp.image.clone();
        Ok(())
    }

    /// **Time-travel / rollback.** Restore the live state to an earlier committed
    /// boundary `root` from this cell's log. A root never committed by this cell is
    /// refused ([`RestoreError::UnknownRoot`]); a committed one is re-witnessed
    /// (fail-closed) and adopted.
    pub fn time_travel(&mut self, root: &str) -> Result<(), RestoreError> {
        let cp = self
            .checkpoints
            .iter()
            .rev()
            .find(|c| c.root == root)
            .cloned()
            .ok_or_else(|| RestoreError::UnknownRoot(root.to_string()))?;
        self.restore_checkpoint(&cp)
    }

    /// **Fork.** A second cell whose live state is a COPY of this cell's latest
    /// checkpoint image (or its current live state if it has never checkpointed) and
    /// whose log is seeded with that **fork-point** checkpoint. The two cells share a
    /// provable common ancestor (the fork-point root) and diverge independently — a
    /// write to one does not touch the other.
    pub fn fork(&self) -> UmemCell {
        let fork_point = self
            .checkpoints
            .last()
            .cloned()
            .unwrap_or_else(|| Checkpoint::reify(self.live.clone()));
        UmemCell {
            live: fork_point.image.clone(),
            checkpoints: vec![fork_point],
        }
    }
}

/// Lower-hex a 32-byte root (32 bytes → 64 hex chars).
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

    /// The boundary root is state-sensitive: a one-byte change to any value moves it, a
    /// changed key moves it, and it is insertion-order-independent (the `BTreeMap`
    /// canonicalizes).
    #[test]
    fn boundary_root_is_injective_and_order_independent() {
        let mut h1 = UmemHeap::new();
        h1.write("a", b"1".to_vec());
        h1.write("b", b"2".to_vec());

        let mut h2 = UmemHeap::new();
        h2.write("b", b"2".to_vec()); // inserted in the other order
        h2.write("a", b"1".to_vec());
        assert_eq!(h1.boundary_root(), h2.boundary_root(), "order-independent");

        let mut h3 = UmemHeap::new();
        h3.write("a", b"1".to_vec());
        h3.write("b", b"3".to_vec()); // one byte different
        assert_ne!(
            h1.boundary_root(),
            h3.boundary_root(),
            "a changed byte moves the root"
        );

        // A changed KEY (same values) moves the root too (the laying binds the key).
        let mut h4 = UmemHeap::new();
        h4.write("a", b"1".to_vec());
        h4.write("c", b"2".to_vec());
        assert_ne!(
            h1.boundary_root(),
            h4.boundary_root(),
            "a changed key moves the root"
        );

        // The empty heap has a stable, non-trivial 64-hex root.
        assert_eq!(UmemHeap::new().boundary_root().len(), 64);
    }

    /// Sleep/wake preserves state: write, checkpoint, mutate, restore ⇒ the original
    /// state is back, and it folds to the committed root.
    #[test]
    fn checkpoint_then_restore_preserves_state() {
        let mut cell = UmemCell::new();
        cell.live_mut().write("session", b"alpha".to_vec());
        cell.live_mut().write("counter", b"7".to_vec());

        let root = cell.checkpoint();
        assert_eq!(cell.latest_checkpoint_root(), Some(root.as_str()));

        cell.live_mut().write("counter", b"99".to_vec());
        cell.live_mut().remove("session");
        assert_ne!(cell.live_root(), root, "state diverged from the checkpoint");

        cell.time_travel(&root).unwrap();
        assert_eq!(cell.live().read("session"), Some(&b"alpha"[..]));
        assert_eq!(cell.live().read("counter"), Some(&b"7"[..]));
        assert_eq!(
            cell.live_root(),
            root,
            "restored state folds back to the root"
        );
    }

    /// Restore is fail-closed: a checkpoint whose reified image does not reproduce its
    /// committed root is REFUSED, leaving the live state untouched; an unknown root is
    /// refused too.
    #[test]
    fn restore_refuses_a_tampered_image() {
        let mut cell = UmemCell::new();
        cell.live_mut().write("k", b"genuine".to_vec());
        let root = cell.checkpoint();

        let mut forged_image = UmemHeap::new();
        forged_image.write("k", b"tampered".to_vec());
        let forged = Checkpoint {
            root: root.clone(),
            image: forged_image,
        };
        assert!(
            !forged.verify(),
            "the forged image does not fold to the root"
        );

        cell.live_mut().write("k", b"live".to_vec());
        let err = cell.restore_checkpoint(&forged).unwrap_err();
        assert!(matches!(err, RestoreError::ImageRootMismatch { .. }));
        assert_eq!(
            cell.live().read("k"),
            Some(&b"live"[..]),
            "live state untouched on refusal"
        );

        cell.time_travel(&root).unwrap();
        assert_eq!(cell.live().read("k"), Some(&b"genuine"[..]));

        assert!(matches!(
            cell.time_travel("00").unwrap_err(),
            RestoreError::UnknownRoot(_)
        ));
    }

    /// Fork diverges: two instances from one checkpoint, a write to one does not affect
    /// the other, and both descend from the same fork-point root.
    #[test]
    fn fork_diverges_independently_from_a_shared_ancestor() {
        let mut src = UmemCell::new();
        src.live_mut().write("shared", b"base".to_vec());
        let fork_point = src.checkpoint();

        let mut forked = src.fork();
        assert_eq!(
            src.latest_checkpoint_root(),
            forked.latest_checkpoint_root(),
            "both descend from the same fork-point root"
        );
        assert_eq!(
            forked.live().read("shared"),
            Some(&b"base"[..]),
            "fork inherits the image"
        );

        src.live_mut().write("shared", b"primary-only".to_vec());
        forked.live_mut().write("shared", b"replica-only".to_vec());
        assert_eq!(src.live().read("shared"), Some(&b"primary-only"[..]));
        assert_eq!(forked.live().read("shared"), Some(&b"replica-only"[..]));
        assert_ne!(
            src.live_root(),
            forked.live_root(),
            "the two cells diverged"
        );

        forked.time_travel(&fork_point).unwrap();
        assert_eq!(forked.live().read("shared"), Some(&b"base"[..]));
        assert_eq!(src.live().read("shared"), Some(&b"primary-only"[..]));
    }

    /// Time-travel restores an EARLIER root: checkpoint at t1, write more, checkpoint at
    /// t2, then roll back to t1's boundary root (and forward again to t2).
    #[test]
    fn time_travel_restores_an_earlier_boundary_root() {
        let mut cell = UmemCell::new();
        cell.live_mut().write("v", b"one".to_vec());
        let r1 = cell.checkpoint();

        cell.live_mut().write("v", b"two".to_vec());
        let r2 = cell.checkpoint();
        assert_ne!(r1, r2);

        cell.live_mut().write("v", b"three".to_vec());

        cell.time_travel(&r1).unwrap();
        assert_eq!(cell.live().read("v"), Some(&b"one"[..]));
        cell.time_travel(&r2).unwrap();
        assert_eq!(cell.live().read("v"), Some(&b"two"[..]));

        assert_eq!(cell.checkpoint_roots(), vec![r1, r2]);
    }
}
