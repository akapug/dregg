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
use crate::graph::DocGraph;
use crate::patch::{Op, Patch};
use std::collections::BTreeSet;

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
///
/// NOTE: this head-only form is sound **only when each dropped alternative is a
/// single atom**. For a multi-atom dropped branch the head's tail would survive
/// the tombstone and re-form a fresh antichain (the dropped content leaks and the
/// conflict is not collapsed). Prefer [`resolve_keep_in`], which is given the
/// graph and tombstones each dropped branch *whole*.
pub fn resolve_keep(keep: AtomId, drop: &[AtomId]) -> Patch {
    resolve_keep_by(Author::SYSTEM, keep, drop)
}

/// Authored variant of [`resolve_keep`]. See the head-only caveat there; use
/// [`resolve_keep_in`] for the graph-aware, branch-whole drop.
pub fn resolve_keep_by(author: Author, keep: AtomId, drop: &[AtomId]) -> Patch {
    let _ = keep; // kept alive by simply not tombstoning it
    Patch::by(author, drop.iter().map(|&id| Op::Delete { id }))
}

/// Resolve a prose conflict by *choosing*, tombstoning each dropped alternative
/// **whole** — its head AND every atom that branch exclusively owns (the atoms
/// the dropped head dominates, [`DocGraph::branch_atoms`]). This is the correct
/// keep-one resolution: a dropped *multi-atom* branch cannot leak its tail
/// through the head tombstone (which would re-form a fresh antichain and leave
/// the conflict un-collapsed), and a shared/rejoin atom reachable around the
/// dropped head is never tombstoned (it belongs to the kept reading too).
///
/// The `keep` head and any atom it owns are explicitly spared, so overlapping
/// branch cones (e.g. a dropped branch that rejoins the kept one) never tombstone
/// kept content.
pub fn resolve_keep_in(g: &DocGraph, author: Author, keep: AtomId, drop: &[AtomId]) -> Patch {
    // The atoms the KEPT branch owns — never tombstone these, even if a dropped
    // branch's cone happens to reach them (the kept reading must survive whole).
    let keep_owned = g.branch_atoms(keep);

    let mut to_drop: BTreeSet<AtomId> = BTreeSet::new();
    for &head in drop {
        for a in g.branch_atoms(head) {
            if a != keep && !keep_owned.contains(&a) {
                to_drop.insert(a);
            }
        }
    }
    // Deterministic op order (BTreeSet iterates sorted) so the resolution patch is
    // content-addressed stably regardless of input head order.
    Patch::by(author, to_drop.into_iter().map(|id| Op::Delete { id }))
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
