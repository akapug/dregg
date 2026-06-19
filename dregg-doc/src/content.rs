//! Linearization — folding the graph into rendered content, with conflicts
//! surfaced as first-class regions.
//!
//! The visible document is a topological walk over the *alive* atoms following
//! the order-edges (DOCUMENT-LANGUAGE.md §2.2-2.3). Where the walk reaches a
//! position with **two or more live successors and no order-edge among them** —
//! a genuine *antichain* in the order — it cannot linearize them, because the
//! order genuinely is not in the graph. That fork is a [`ConflictRegion`]: a
//! first-class STATE, surfaced (never a panic, never a failure), carried until a
//! later resolution patch collapses the antichain.

use crate::atom::AtomId;
use crate::graph::DocGraph;
use std::collections::BTreeSet;

/// One unit of rendered output.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Segment {
    /// A clean run of content with a unique order — the common case.
    Clean(String),
    /// A conflicted region: two-or-more live, mutually-unordered alternatives at
    /// one position. A first-class state, resolved by a later patch — *not* an
    /// error. Each alternative carries the id at which it forks so a resolution
    /// patch can address it.
    Conflict(ConflictRegion),
}

/// A first-class conflict: an antichain of >=2 live alternatives reachable at the
/// same position with no order-edge among them. The document carries this state
/// (it is part of a valid rendered document) until a resolution patch adds the
/// order-edges and/or tombstones that collapse the antichain to a single walk.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConflictRegion {
    /// The live alternatives, each a (head-atom-id, rendered-content) pair. The
    /// head id is the addressable fork point a resolution patch `Connect`s or
    /// `Delete`s. Sorted by id for a canonical form.
    pub alternatives: Vec<(AtomId, String)>,
}

/// The full rendered content of a document: a sequence of clean runs and
/// conflict regions, in document order.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Rendered {
    /// The segments in order.
    pub segments: Vec<Segment>,
}

impl Rendered {
    /// True iff the document currently carries at least one unresolved conflict.
    pub fn has_conflict(&self) -> bool {
        self.segments
            .iter()
            .any(|s| matches!(s, Segment::Conflict(_)))
    }

    /// All conflict regions, in document order.
    pub fn conflicts(&self) -> impl Iterator<Item = &ConflictRegion> {
        self.segments.iter().filter_map(|s| match s {
            Segment::Conflict(c) => Some(c),
            Segment::Clean(_) => None,
        })
    }

    /// A flat textual rendering for inspection/tests. Clean runs render as their
    /// content; a conflict renders its alternatives between markers, so a
    /// conflict is *legible* (the AOL-wonder bar: "two people wrote this
    /// differently — here's both") rather than swallowed.
    pub fn to_marked_string(&self) -> String {
        let mut out = String::new();
        for seg in &self.segments {
            match seg {
                Segment::Clean(s) => out.push_str(s),
                Segment::Conflict(c) => {
                    out.push_str("<<<conflict");
                    for (_, alt) in &c.alternatives {
                        out.push_str("\n|| ");
                        out.push_str(alt);
                    }
                    out.push_str("\nconflict>>>");
                }
            }
        }
        out
    }
}

/// Linearize a document graph into rendered content, surfacing antichains as
/// first-class conflict regions.
///
/// The walk starts at [`AtomId::ROOT`] and follows order-edges through *alive*
/// atoms. At each step we look at the alive successors reachable from the
/// current frontier:
/// - exactly one path forward => emit it as clean content;
/// - two-or-more mutually-unordered alive successors => emit a
///   [`ConflictRegion`] holding each alternative's linearization, then rejoin.
///
/// Dead atoms are skipped for content but still conduct order (you can walk
/// *through* a tombstone to its successors), which is what makes a delete
/// monotone and order-preserving.
pub fn content(g: &DocGraph) -> Rendered {
    let mut out = Rendered::default();
    let mut visited = BTreeSet::new();
    walk(g, AtomId::ROOT, &mut visited, &mut out.segments);
    coalesce(&mut out.segments);
    out
}

/// Live successors of `id`, walking *through* tombstones (a dead atom conducts
/// order but contributes no content). Returns alive atom ids, deduped + sorted.
fn live_successors(g: &DocGraph, id: AtomId) -> Vec<AtomId> {
    let mut seen = BTreeSet::new();
    let mut out = BTreeSet::new();
    let mut stack: Vec<AtomId> = g.successors(id).collect();
    while let Some(s) = stack.pop() {
        if !seen.insert(s) {
            continue;
        }
        match g.atom(s) {
            Some(a) if a.is_alive() => {
                out.insert(s);
            }
            // Tombstoned (or dangling): conduct order through to its successors.
            _ => stack.extend(g.successors(s)),
        }
    }
    out.into_iter().collect()
}

/// Recursive walk from `from`, appending segments. Detects antichains (>=2 live
/// successors with no order between them) and emits them as conflicts.
fn walk(g: &DocGraph, from: AtomId, visited: &mut BTreeSet<AtomId>, out: &mut Vec<Segment>) {
    let mut cursor = from;
    loop {
        let succ = live_successors(g, cursor);
        match succ.as_slice() {
            [] => return,
            [single] => {
                let id = *single;
                if !visited.insert(id) {
                    return;
                }
                if let Some(a) = g.atom(id) {
                    out.push(Segment::Clean(a.content.clone()));
                }
                cursor = id;
            }
            many => {
                // Filter the genuine antichain: keep only successors that are
                // not reachable-from another successor (those would be ordered,
                // not concurrent). Two inserts "after X" with no edge between
                // them are mutually unreachable => a real antichain.
                let antichain: Vec<AtomId> = many
                    .iter()
                    .copied()
                    .filter(|&a| {
                        !many
                            .iter()
                            .any(|&b| b != a && reachable(g, b, a))
                    })
                    .collect();
                if antichain.len() < 2 {
                    // Successors were actually ordered: follow the minimal one.
                    let next = many
                        .iter()
                        .copied()
                        .find(|&a| !many.iter().any(|&b| b != a && reachable(g, b, a)))
                        .unwrap_or(many[0]);
                    if !visited.insert(next) {
                        return;
                    }
                    if let Some(at) = g.atom(next) {
                        out.push(Segment::Clean(at.content.clone()));
                    }
                    cursor = next;
                    continue;
                }
                // A genuine conflict: each alternative is its own linearization
                // from its head until the branches rejoin (or end).
                let mut alternatives = Vec::new();
                for &head in &antichain {
                    let mut branch = Vec::new();
                    let mut bvisited = visited.clone();
                    if bvisited.insert(head) {
                        if let Some(a) = g.atom(head) {
                            branch.push(Segment::Clean(a.content.clone()));
                        }
                        walk(g, head, &mut bvisited, &mut branch);
                    }
                    coalesce(&mut branch);
                    let text = branch
                        .iter()
                        .map(|s| match s {
                            Segment::Clean(t) => t.clone(),
                            Segment::Conflict(_) => String::new(),
                        })
                        .collect::<String>();
                    alternatives.push((head, text));
                    visited.insert(head);
                }
                alternatives.sort_by_key(|(id, _)| *id);
                out.push(Segment::Conflict(ConflictRegion { alternatives }));
                return;
            }
        }
    }
}

/// Is `target` reachable from `start` by following order-edges (through any
/// atoms, alive or dead)? Used to tell "ordered" successors from a true
/// concurrent antichain.
fn reachable(g: &DocGraph, start: AtomId, target: AtomId) -> bool {
    if start == target {
        return true;
    }
    let mut seen = BTreeSet::new();
    let mut stack: Vec<AtomId> = g.successors(start).collect();
    while let Some(s) = stack.pop() {
        if s == target {
            return true;
        }
        if seen.insert(s) {
            stack.extend(g.successors(s));
        }
    }
    false
}

/// Merge adjacent `Clean` segments so the output is canonical (one run per
/// contiguous clean stretch).
fn coalesce(segs: &mut Vec<Segment>) {
    let mut out: Vec<Segment> = Vec::with_capacity(segs.len());
    for seg in segs.drain(..) {
        match (out.last_mut(), &seg) {
            (Some(Segment::Clean(prev)), Segment::Clean(cur)) => prev.push_str(cur),
            _ => out.push(seg),
        }
    }
    *segs = out;
}
