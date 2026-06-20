//! Three-way conflict rendering — the conflict region **plus the common
//! ancestor**, the way `diff3` / a merge-base view shows it.
//!
//! [`crate::content`] surfaces a conflict as a [`ConflictRegion`]: the live
//! alternatives, each tagged with who wrote it. That is the *two-way* view —
//! OURS vs THEIRS. A real merge tool shows a *third* column: the **BASE**, the
//! text that stood at that position in the common ancestor both sides forked
//! from. Seeing the base is what lets a reader resolve intelligently: "they both
//! replaced *this*; here's what it was".
//!
//! The common ancestor is the [`merge_base`] — the longest shared prefix of two
//! histories, the point at which they diverged. Replaying it yields the ancestor
//! graph; [`render_three_way`] reads, for each conflict region in the merged
//! document, the ancestor content that sat at that fork point, and pairs it with
//! every side's alternative. A clean merge has no conflict regions and so yields
//! no [`ThreeWayConflict`] entries.

use crate::atom::{AtomId, Author, PatchId};
use crate::content::{Segment, content};
use crate::graph::DocGraph;
use crate::history::History;
use crate::merge::merge;
use std::collections::BTreeSet;

/// One side of a three-way conflict: an alternative with its authorship.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConflictSide {
    /// Who authored this side.
    pub author: Author,
    /// The patch that introduced this side's diverging content.
    pub patch: PatchId,
    /// The side's rendered alternative text.
    pub text: String,
}

/// A three-way (diff3 / merge-base) view of one conflict region: the common
/// ancestor's content at that position, alongside every diverging side.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ThreeWayConflict {
    /// The common-ancestor content that stood at this fork point (the BASE
    /// column). Empty if the divergence was a pure concurrent *insert* (both
    /// sides added where the ancestor had nothing).
    pub base_text: String,
    /// The diverging sides (OURS, THEIRS, ... — generalized to N), in the
    /// region's canonical alternative order.
    pub sides: Vec<ConflictSide>,
}

/// The merge base of two histories: the longest common prefix of their patch
/// lists — the point at which they diverged (their common ancestor). Returns it
/// as a [`History`] so it can be [`History::replay`]ed into the ancestor graph.
pub fn merge_base(a: &History, b: &History) -> History {
    let shared = a
        .patches()
        .iter()
        .zip(b.patches())
        .take_while(|(x, y)| x == y)
        .count();
    let mut base = History::new();
    for p in &a.patches()[..shared] {
        base.commit(p.clone());
    }
    base
}

/// Merge two branches that forked from a common `base` (their merge base). This
/// is just [`merge`] of the two replayed folds — the value is the *render*
/// ([`render_three_way`]), which recovers the BASE column from the ancestor.
pub fn three_way(_base: &History, ours: &History, theirs: &History) -> DocGraph {
    merge(&ours.replay(), &theirs.replay())
}

/// Render every conflict region in `merged` as a three-way view, recovering the
/// BASE column from the `base` (common-ancestor) graph.
///
/// For each [`Segment::Conflict`], the fork point is the atom both alternatives
/// are ordered immediately after. We find that predecessor in `merged`, then read
/// the ancestor's content from that same fork point forward in `base` — the text
/// the common ancestor carried where the sides now diverge. A purely concurrent
/// insert (the ancestor had nothing after the fork) yields an empty `base_text`.
pub fn render_three_way(merged: &DocGraph, base: &DocGraph) -> Vec<ThreeWayConflict> {
    let mut out = Vec::new();
    for seg in &content(merged).segments {
        let Segment::Conflict(region) = seg else {
            continue;
        };
        let fork = fork_point(merged, region.heads());
        let base_text = fork
            .map(|f| ancestor_text_after(base, f, &region.heads()))
            .unwrap_or_default();
        let sides = region
            .alternatives
            .iter()
            .map(|alt| ConflictSide {
                author: alt.provenance.author,
                patch: alt.provenance.patch,
                text: alt.text.clone(),
            })
            .collect();
        out.push(ThreeWayConflict { base_text, sides });
    }
    out
}

/// Find the fork point of a conflict: the atom that every alternative head is an
/// immediate successor of (the shared predecessor the branches diverge from).
fn fork_point(g: &DocGraph, heads: Vec<AtomId>) -> Option<AtomId> {
    if heads.is_empty() {
        return None;
    }
    // The fork point is an atom `p` whose successor set contains every head.
    for atom in g.atoms() {
        let succ: BTreeSet<AtomId> = g.successors(atom.id).collect();
        if heads.iter().all(|h| succ.contains(h)) {
            return Some(atom.id);
        }
    }
    None
}

/// The ancestor's content from `fork` forward, following the linear order, until
/// the order ends or forks. Atoms that are themselves diverging heads (present
/// only in the merged doc) are absent from `base`, so this naturally yields just
/// the ancestor's own tail content after the fork point.
fn ancestor_text_after(base: &DocGraph, fork: AtomId, heads: &[AtomId]) -> String {
    // The fork point may not exist in the ancestor (e.g. it was itself added on a
    // branch); if so the ancestor carried nothing there.
    if base.atom(fork).is_none() {
        return String::new();
    }
    let mut out = String::new();
    let mut cursor = fork;
    let mut visited = BTreeSet::new();
    loop {
        // Live successors that exist in the ancestor and are not the diverging
        // heads (those belong to the branches, not the base).
        let next: Vec<AtomId> = base
            .successors(cursor)
            .filter(|s| !heads.contains(s))
            .filter(|s| base.atom(*s).map(|a| a.is_alive()).unwrap_or(false))
            .collect();
        let step = match next.as_slice() {
            [one] => *one,
            _ => return out, // end, or a fork in the ancestor itself: stop.
        };
        if !visited.insert(step) {
            return out;
        }
        if let Some(a) = base.atom(step) {
            out.push_str(&a.content);
        }
        cursor = step;
    }
}
