//! Resolution — collapsing a conflict's antichain with a later patch.
//!
//! A conflict is resolved by *just another edit* (DOCUMENT-LANGUAGE.md §2.3): a
//! patch that adds the order-edges (or the tombstones) that turn the antichain
//! into a chain — restoring a unique walk. Resolution is additive/monotone and
//! composes like any patch; it is *not* a special "finish the merge" operation
//! outside the algebra. Because resolution is itself a patch, two parties can
//! even concurrently propose different resolutions, yielding a smaller conflict
//! that is again a state — the model is closed under its own conflicts.

use crate::atom::AtomId;
use crate::patch::{Op, Patch};

/// Resolve a conflict by *ordering* the alternatives: emit `Connect` edges that
/// chain the given antichain heads in the supplied order (`heads[0]` before
/// `heads[1]` before ...). After this patch, the walk has a unique path and the
/// conflict is gone — every alternative is kept, just linearized.
///
/// `heads` are the fork-point atom ids from a [`crate::ConflictRegion`]'s
/// `alternatives`.
pub fn resolve_connect(heads: &[AtomId]) -> Patch {
    let mut ops = Vec::new();
    for w in heads.windows(2) {
        ops.push(Op::Connect {
            from: w[0],
            to: w[1],
        });
    }
    Patch::from_ops(ops)
}

/// Resolve a conflict by *choosing*: keep the `keep` alternative and tombstone
/// the head atom of every other alternative, killing those branches. After this
/// patch only one live alternative remains, so the antichain collapses to a
/// single walk.
///
/// `keep` and `drop` are fork-point atom ids from a
/// [`crate::ConflictRegion`]'s `alternatives` (`keep` is the chosen head; every
/// id in `drop` is tombstoned).
pub fn resolve_keep(keep: AtomId, drop: &[AtomId]) -> Patch {
    let _ = keep; // kept alive by simply not tombstoning it
    Patch::from_ops(drop.iter().map(|&id| Op::Delete { id }))
}
