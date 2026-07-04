//! `compute_cell` — **a persistent server / running workload is a umem cell**
//! (`docs/COMPUTE-AS-CELL.md`, the #1 re-dregg from `MYOPIA-AUDIT.md §3`).
//!
//! Where [`crate::server`] held a server's state as a fly.io-machine serde struct,
//! a [`ComputeCell`] is the **dregg-native** unit of compute: an identity-bearing
//! cell whose durable state is a **umem heap** with a committed **boundary root**.
//! The server lifecycle maps onto umem operations rather than a hypervisor's:
//!
//! ```text
//!   sleep  (stop)        = checkpoint              -> commit the boundary root
//!   wake   (wake)        = restore                 <- reproduce + verify the image
//!   scale  (fork)        = fork                    -> a second cell, diverging
//!   rollback             = restore an earlier root <- time-travel the boundary
//!   pay-only-while-awake = draw iff NOT checkpointed
//! ```
//!
//! ## ONE umem heap, two wrappers (the convergence)
//!
//! `ComputeCell` is a **thin wrapper** — server identity + lifecycle semantics — over
//! the canonical [`dreggnet_umem::UmemCell`] primitive: the ONE committed `(key→value)`
//! heap + boundary root + checkpoint/restore/fork/time-travel machinery. The registries
//! lane wraps the SAME primitive (a [`dreggnet_umem::UmemRegistry`] is its durable
//! record-laying wrapper). This module used to re-implement the heap-root + checkpoint
//! logic over `dregg-circuit` directly; that duplication is retired — it now delegates to
//! the shared primitive (`docs/REGISTRIES-AS-UMEM.md`, `docs/COMPUTE-AS-CELL.md`).
//!
//! ## The deployed substrate pieces this depends on (real, no stand-in)
//!
//! - The **boundary root** is the genuine kernel sorted-Poseidon2
//!   [`dregg_cell::compute_heap_root`] over the cell's `(key→value)` heap (the Rust
//!   shadow of the Lean `Substrate.Heap.root`, pinned by `root_binds_get`) — the SAME
//!   commitment the registries lane and a dregg light client understand. The umem
//!   keystone `boundary_init_root_bound` (`UniversalMemory.lean:475`) is "the boundary IS
//!   the state": a checkpoint is *taking the boundary root of your own cell*, and a
//!   restore reproduces the reified image and checks it folds back to that exact root.
//! - The **cell identity** is the genuine `dregg_types::CellId::derive_raw` — the
//!   same substrate cell-id `webauth/src/account_id.rs` anchors an account with.
//!
//! ## The named Stage-B seam (honest)
//!
//! The deployed pieces give the boundary-root commit/verify/fork/time-travel
//! semantics over the cell's **working-state heap** (the `(key→value)` cells a
//! workload reads/writes through the `exec/src/host_api.rs` seam). Two things wait
//! on the first-class **umem checkpoint/resume kernel-effect** (`UMEM-STAGE-B-DESIGN.md`,
//! designed-not-deployed): capturing a *live in-sandbox process image* into the
//! heap, and the on-chain umem-ref a light client witnesses + a node durably
//! materializes across a control-plane restart. Cross-restart image durability is
//! deliberately NOT re-implemented as a side store (that is the `dreggnet-store`
//! myopia, the #2 re-dregg). See `docs/COMPUTE-AS-CELL.md §3`.

use serde::{Deserialize, Serialize};

use dregg_types::CellId;

// The canonical umem-cell primitive (the shared heap + boundary root + checkpoint /
// restore / fork / time-travel machinery). `ComputeCell` wraps it with server identity +
// lifecycle semantics; `dreggnet_umem::UmemRegistry` wraps the same primitive with durable
// record semantics. `RestoreError` is re-exported below so callers keep using
// `crate::compute_cell::RestoreError`.
use dreggnet_umem::UmemCell;

pub use dreggnet_umem::{Checkpoint, RestoreError, UmemHeap};

/// The witnessed working-state heap of a compute cell — the canonical
/// [`dreggnet_umem::UmemHeap`]. (Kept as a local alias so the compute lane's name is
/// stable while the machinery is the shared primitive.)
pub type ComputeHeap = UmemHeap;

/// The published domain label whose blake3 hash binds a DreggNet compute cell to a
/// substrate identity cell. Deterministic + published (a domain separator, not a
/// secret) — the compute analog of `webauth`'s `dreggnet:account-identity:v1`.
pub const COMPUTE_ROOT_TOKEN_LABEL: &str = "dreggnet:compute-cell:v1";

/// The fixed 32-byte domain token binding a compute cell to its substrate identity
/// cell: `blake3(`[`COMPUTE_ROOT_TOKEN_LABEL`]`)`.
pub fn compute_root_token() -> [u8; 32] {
    blake3::hash(COMPUTE_ROOT_TOKEN_LABEL.as_bytes()).into()
}

/// Derive the stable [`CellId`] for a server from its `(lessee, app, name)` —
/// content-addressed, the way `webauth::account_id` derives an account cell. The
/// 32-byte derivation seed is `blake3("lessee\0app\0name")`, fed to the substrate
/// `CellId::derive_raw` under [`compute_root_token`]. The same triple always names
/// the same cell.
pub fn derive_cell_id(lessee: &str, app: &str, name: &str) -> CellId {
    let mut hasher = blake3::Hasher::new();
    hasher.update(lessee.as_bytes());
    hasher.update(&[0]);
    hasher.update(app.as_bytes());
    hasher.update(&[0]);
    hasher.update(name.as_bytes());
    let seed: [u8; 32] = hasher.finalize().into();
    CellId::derive_raw(&seed, &compute_root_token())
}

/// Lowercase hex of a 32-byte cell id.
fn hex32(bytes: &[u8; 32]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

/// The hex cell id for a server's `(lessee, app, name)` — the value the
/// [`crate::server::ServerRecord::cell_id`] field carries.
pub fn cell_id_hex(lessee: &str, app: &str, name: &str) -> String {
    hex32(derive_cell_id(lessee, app, name).as_bytes())
}

// ---------------------------------------------------------------------------
// The compute cell — a thin server-state wrapper over the shared umem cell.
// ---------------------------------------------------------------------------

/// A **compute cell** — the dregg-native unit of compute. Identity (a substrate
/// [`CellId`]) + a shared [`UmemCell`] (the live witnessed working-state heap + the
/// checkpoint log). Sleep/wake/fork/rollback are the umem cell's operations over its
/// boundary root; this wrapper adds the server's content-addressed identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComputeCell {
    /// The server's substrate cell id (hex of [`CellId`]).
    cell_id: String,
    /// The shared umem cell: working-state heap + the time-travel checkpoint log.
    cell: UmemCell,
}

impl ComputeCell {
    /// A fresh compute cell for a server `(lessee, app, name)` — its id derived via
    /// the substrate [`derive_cell_id`], its umem cell empty.
    pub fn new(lessee: &str, app: &str, name: &str) -> ComputeCell {
        ComputeCell {
            cell_id: cell_id_hex(lessee, app, name),
            cell: UmemCell::new(),
        }
    }

    /// The server's substrate cell id (hex).
    pub fn cell_id(&self) -> &str {
        &self.cell_id
    }

    /// The live working-state heap (read-only).
    pub fn live(&self) -> &ComputeHeap {
        self.cell.live()
    }

    /// The live working-state heap (mutable) — a workload's writes land here while
    /// the server is awake.
    pub fn live_mut(&mut self) -> &mut ComputeHeap {
        self.cell.live_mut()
    }

    /// The boundary root of the **live** (uncommitted) state.
    pub fn live_root(&self) -> String {
        self.cell.live_root()
    }

    /// The most recently committed boundary root, if the cell has checkpointed.
    pub fn latest_checkpoint_root(&self) -> Option<&str> {
        self.cell.latest_checkpoint_root()
    }

    /// Every committed boundary root, oldest first (the time-travel log).
    pub fn checkpoint_roots(&self) -> Vec<String> {
        self.cell.checkpoint_roots()
    }

    /// **Checkpoint (sleep).** Commit the live state, append it to the log, and return
    /// the boundary root. The server can now stop consuming compute; the cell persists
    /// as this 32-byte root. Idempotent in value: two checkpoints of an unchanged heap
    /// yield the same root.
    pub fn checkpoint(&mut self) -> String {
        self.cell.checkpoint()
    }

    /// **Restore (wake) from an explicit checkpoint**, verifying the reified image
    /// reproduces its committed root before adopting it. Fail-closed: a checkpoint whose
    /// image does not fold to its `root` is refused ([`RestoreError::ImageRootMismatch`])
    /// and the live state is left untouched.
    pub fn restore_checkpoint(&mut self, cp: &Checkpoint) -> Result<(), RestoreError> {
        self.cell.restore_checkpoint(cp)
    }

    /// **Time-travel / rollback (wake).** Restore the live state to an earlier committed
    /// boundary `root` from this cell's log. A root never committed by this cell is
    /// refused ([`RestoreError::UnknownRoot`]); a committed one is re-witnessed
    /// (fail-closed) and adopted.
    pub fn time_travel(&mut self, root: &str) -> Result<(), RestoreError> {
        self.cell.time_travel(root)
    }

    /// **Fork (scale / clone).** A second cell, identified by `(lessee, app, name)`
    /// (a distinct cell id), whose live state is a COPY of this cell's latest checkpoint
    /// image (or its current live state if it has never checkpointed) and whose log is
    /// seeded with that **fork-point** checkpoint. The two cells share a provable common
    /// ancestor (the fork-point root) and diverge independently — a write to one does not
    /// touch the other.
    pub fn fork(&self, lessee: &str, app: &str, name: &str) -> ComputeCell {
        ComputeCell {
            cell_id: cell_id_hex(lessee, app, name),
            cell: self.cell.fork(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The cell id IS the substrate cell id, and `(lessee, app, name)` content-
    /// addresses it: the same triple always names the same cell; a different triple
    /// names a different one.
    #[test]
    fn cell_id_is_the_substrate_cell_id_content_addressed() {
        let a = cell_id_hex("agent", "web", "srv");
        let b = cell_id_hex("agent", "web", "srv");
        assert_eq!(a, b, "deterministic over the same triple");
        assert_ne!(
            a,
            cell_id_hex("agent", "web", "other"),
            "name change ⇒ new cell"
        );
        assert_ne!(
            a,
            cell_id_hex("other", "web", "srv"),
            "lessee change ⇒ new cell"
        );

        // It agrees byte-for-byte with `CellId::derive_raw` over the same inputs (the
        // function the executor addresses cells with).
        let mut h = blake3::Hasher::new();
        h.update(b"agent");
        h.update(&[0]);
        h.update(b"web");
        h.update(&[0]);
        h.update(b"srv");
        let seed: [u8; 32] = h.finalize().into();
        let cell = CellId::derive_raw(&seed, &compute_root_token());
        assert_eq!(a, hex32(cell.as_bytes()));
    }

    /// The boundary root is state-sensitive: a one-byte change to any value moves it,
    /// and it is insertion-order-independent (the `BTreeMap` canonicalizes).
    #[test]
    fn boundary_root_is_injective_and_order_independent() {
        let mut h1 = ComputeHeap::new();
        h1.write("a", b"1".to_vec());
        h1.write("b", b"2".to_vec());

        let mut h2 = ComputeHeap::new();
        h2.write("b", b"2".to_vec()); // inserted in the other order
        h2.write("a", b"1".to_vec());
        assert_eq!(h1.boundary_root(), h2.boundary_root(), "order-independent");

        let mut h3 = ComputeHeap::new();
        h3.write("a", b"1".to_vec());
        h3.write("b", b"3".to_vec()); // one byte different
        assert_ne!(
            h1.boundary_root(),
            h3.boundary_root(),
            "a changed byte moves the root"
        );

        // The empty heap has a stable, non-trivial root (the substrate empty-heap root).
        assert_eq!(ComputeHeap::new().boundary_root().len(), 64);
    }

    /// TEETH — sleep/wake preserves state: write, checkpoint (sleep), mutate, restore
    /// (wake) ⇒ the original state is back, continuous.
    #[test]
    fn checkpoint_then_restore_preserves_state() {
        let mut cell = ComputeCell::new("agent", "web", "srv");
        cell.live_mut().write("session", b"alpha".to_vec());
        cell.live_mut().write("counter", b"7".to_vec());

        // Sleep: checkpoint commits the boundary root.
        let root = cell.checkpoint();
        assert_eq!(cell.latest_checkpoint_root(), Some(root.as_str()));

        // The server keeps running and mutates after the checkpoint…
        cell.live_mut().write("counter", b"99".to_vec());
        cell.live_mut().remove("session");
        assert_ne!(cell.live_root(), root, "state diverged from the checkpoint");

        // Wake: restore reproduces the committed state exactly.
        cell.time_travel(&root).unwrap();
        assert_eq!(cell.live().read("session"), Some(&b"alpha"[..]));
        assert_eq!(cell.live().read("counter"), Some(&b"7"[..]));
        assert_eq!(
            cell.live_root(),
            root,
            "restored state folds back to the root"
        );
    }

    /// TEETH — restore is fail-closed: a checkpoint whose reified image does not
    /// reproduce its committed root is REFUSED (a wake never resumes from a forged
    /// image), and the live state is left untouched.
    #[test]
    fn restore_refuses_a_tampered_image() {
        let mut cell = ComputeCell::new("agent", "web", "srv");
        cell.live_mut().write("k", b"genuine".to_vec());
        let root = cell.checkpoint();

        // Forge a checkpoint: claim the committed root but ship a different image.
        let mut forged_image = ComputeHeap::new();
        forged_image.write("k", b"tampered".to_vec());
        let forged = Checkpoint {
            root: root.clone(),
            image: forged_image,
        };
        assert!(
            !forged.verify(),
            "the forged image does not fold to the root"
        );

        // Set a live sentinel, then attempt the forged restore — it must refuse and
        // leave the live state untouched.
        cell.live_mut().write("k", b"live".to_vec());
        let err = cell.restore_checkpoint(&forged).unwrap_err();
        assert!(matches!(err, RestoreError::ImageRootMismatch { .. }));
        assert_eq!(
            cell.live().read("k"),
            Some(&b"live"[..]),
            "live state untouched on refusal"
        );

        // The genuine checkpoint still restores.
        cell.time_travel(&root).unwrap();
        assert_eq!(cell.live().read("k"), Some(&b"genuine"[..]));

        // Time-travel to a never-committed root is refused.
        assert!(matches!(
            cell.time_travel("00").unwrap_err(),
            RestoreError::UnknownRoot(_)
        ));
    }

    /// TEETH — fork diverges: two instances from one checkpoint, a distinct cell id
    /// each, and a write to one does not affect the other (the fork is real), while
    /// both descend from the same fork-point root (provable common ancestor).
    #[test]
    fn fork_diverges_independently_from_a_shared_ancestor() {
        let mut src = ComputeCell::new("agent", "web", "primary");
        src.live_mut().write("shared", b"base".to_vec());
        let fork_point = src.checkpoint();

        let mut forked = src.fork("agent", "web", "replica");
        assert_ne!(
            src.cell_id(),
            forked.cell_id(),
            "the fork has a distinct cell id"
        );
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

        // Diverge: write to each independently.
        src.live_mut().write("shared", b"primary-only".to_vec());
        forked.live_mut().write("shared", b"replica-only".to_vec());
        assert_eq!(src.live().read("shared"), Some(&b"primary-only"[..]));
        assert_eq!(forked.live().read("shared"), Some(&b"replica-only"[..]));
        assert_ne!(
            src.live_root(),
            forked.live_root(),
            "the two cells diverged"
        );

        // The fork can roll itself back to the shared ancestor independently.
        forked.time_travel(&fork_point).unwrap();
        assert_eq!(forked.live().read("shared"), Some(&b"base"[..]));
        // …without disturbing the source's divergence.
        assert_eq!(src.live().read("shared"), Some(&b"primary-only"[..]));
    }

    /// TEETH — time-travel restores an EARLIER root: checkpoint at t1, write more,
    /// checkpoint at t2, then roll back to t1's boundary root.
    #[test]
    fn time_travel_restores_an_earlier_boundary_root() {
        let mut cell = ComputeCell::new("agent", "web", "srv");
        cell.live_mut().write("v", b"one".to_vec());
        let r1 = cell.checkpoint();

        cell.live_mut().write("v", b"two".to_vec());
        let r2 = cell.checkpoint();
        assert_ne!(r1, r2);

        cell.live_mut().write("v", b"three".to_vec());

        // Roll back to t1.
        cell.time_travel(&r1).unwrap();
        assert_eq!(cell.live().read("v"), Some(&b"one"[..]));
        // And forward again to t2 (both roots remain in the log).
        cell.time_travel(&r2).unwrap();
        assert_eq!(cell.live().read("v"), Some(&b"two"[..]));

        assert_eq!(cell.checkpoint_roots(), vec![r1, r2]);
    }
}
