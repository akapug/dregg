//! Resolution — collapsing a conflict with a later patch.
//!
//! A conflict is resolved by *just another edit* (DOCUMENT-LANGUAGE.md §2.3): a
//! patch that adds the order-edges, the tombstones, or the superseding
//! field-write that collapses the conflict. Resolution composes like any patch;
//! it is *not* a special "finish the merge" operation outside the algebra.
//! Because resolution is itself a patch, two parties can even concurrently
//! propose different resolutions, yielding a smaller conflict that is again a
//! state — the model is closed under its own conflicts.
//!
//! Each resolver is *authored*: a resolution leaves a receipt and is itself
//! witnessed and revertible (§3.5).

use crate::atom::{AtomId, Author};
use crate::patch::{Op, Patch};

/// Resolve a *prose* conflict by *ordering* the alternatives: emit `Connect`
/// edges that chain the antichain heads in the supplied order (`heads[0]` before
/// `heads[1]` ...). After this patch the walk has a unique path and the conflict
/// is gone — every alternative is kept, just linearized.
///
/// `heads` come from a [`crate::ConflictRegion::heads`].
pub fn resolve_connect(heads: &[AtomId]) -> Patch {
    resolve_connect_by(Author::SYSTEM, heads)
}

/// Authored variant of [`resolve_connect`].
pub fn resolve_connect_by(author: Author, heads: &[AtomId]) -> Patch {
    let ops = heads
        .windows(2)
        .map(|w| Op::Connect {
            from: w[0],
            to: w[1],
        })
        .collect::<Vec<_>>();
    Patch::by(author, ops)
}

/// Resolve a *prose* conflict by *choosing*: keep the `keep` alternative and
/// tombstone the head atom of every other alternative, killing those branches.
/// After this patch only one live alternative remains, so the antichain
/// collapses to a single walk.
pub fn resolve_keep(keep: AtomId, drop: &[AtomId]) -> Patch {
    resolve_keep_by(Author::SYSTEM, keep, drop)
}

/// Authored variant of [`resolve_keep`].
pub fn resolve_keep_by(author: Author, keep: AtomId, drop: &[AtomId]) -> Patch {
    let _ = keep; // kept alive by simply not tombstoning it
    Patch::by(author, drop.iter().map(|&id| Op::Delete { id }))
}

/// Resolve a *field* conflict (the conservation/authority regime) by choosing a
/// single canonical `value`. Emits a *superseding* `SetField` that collapses all
/// concurrent assignments. Because a field clash may require consensus
/// ([`crate::Regime::needs_consensus`]), the chosen `author` is recorded as the
/// settling authority.
pub fn resolve_field(author: Author, name: &str, value: &str) -> Patch {
    Patch::by(
        author,
        [Op::SetField {
            name: name.to_string(),
            value: value.to_string(),
            superseding: true,
        }],
    )
}
