//! Linearization — folding the graph into rendered content, with conflicts
//! surfaced as first-class regions (carrying provenance).
//!
//! The visible document is a topological walk over the *alive* atoms following
//! the order-edges (DOCUMENT-LANGUAGE.md §2.2-2.3). Where the walk reaches a
//! position with **two or more live successors and no order-edge among them** —
//! a genuine *antichain* in the order — it cannot linearize them, because the
//! order genuinely is not in the graph. That fork is a [`ConflictRegion`] of
//! [`Regime::Prose`]: a first-class STATE, surfaced (never a panic, never a
//! failure), each alternative tagged with **who authored it** (§3.5), carried
//! until a later resolution patch collapses the antichain.
//!
//! Single-valued **field** clashes (§2.4) surface as [`Regime::Field`] conflict
//! regions too — the non-monotone boundary where consensus may be required.

use crate::atom::{AtomId, Provenance};
use crate::graph::DocGraph;
use crate::regime::Regime;
use std::collections::BTreeSet;

/// One live alternative within a conflict: its addressable head/field handle,
/// its rendered text, and its provenance (who wrote it — a *fact*, §3.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Alternative {
    /// For a prose conflict: the fork-point atom id a resolution patch
    /// `Connect`s or `Delete`s. For a field conflict: unused ([`AtomId::ROOT`]).
    pub head: AtomId,
    /// The rendered content / field value of this alternative.
    pub text: String,
    /// Who authored this alternative.
    pub provenance: Provenance,
}

/// One unit of rendered output.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Segment {
    /// A clean run of content with a unique order — the common case.
    Clean(String),
    /// A conflicted region: two-or-more live, mutually-unordered (or
    /// single-valued-clashing) alternatives at one position. A first-class
    /// state, resolved by a later patch — *not* an error.
    Conflict(ConflictRegion),
}

/// A first-class conflict: an antichain of two-or-more live alternatives (prose)
/// or a multi-valued field clash. The document carries this state (it is part of
/// a valid rendered document) until a resolution patch collapses it. Each
/// alternative carries its provenance, so the conflict view can attribute "who
/// wrote which alternative" as a fact.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConflictRegion {
    /// Which regime this conflict belongs to — the answer to "is this real?".
    pub regime: Regime,
    /// For a field clash, the field name; for a prose antichain, `None`.
    pub field: Option<String>,
    /// The live alternatives, sorted canonically.
    pub alternatives: Vec<Alternative>,
}

impl ConflictRegion {
    /// The fork-point heads (for a prose conflict, the addressable atom ids).
    pub fn heads(&self) -> Vec<AtomId> {
        self.alternatives.iter().map(|a| a.head).collect()
    }
}

/// The full rendered content of a document: a sequence of clean runs and
/// conflict regions, in document order, with field conflicts appended.
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

    /// All prose conflicts.
    pub fn prose_conflicts(&self) -> impl Iterator<Item = &ConflictRegion> {
        self.conflicts().filter(|c| c.regime == Regime::Prose)
    }

    /// All field conflicts.
    pub fn field_conflicts(&self) -> impl Iterator<Item = &ConflictRegion> {
        self.conflicts().filter(|c| c.regime == Regime::Field)
    }

    /// A flat textual rendering for inspection/tests. Clean runs render as their
    /// content; a conflict renders its alternatives (with author) between
    /// markers, so a conflict is *legible* (the AOL-wonder bar: "two people
    /// wrote this differently — here's both") rather than swallowed.
    pub fn to_marked_string(&self) -> String {
        let mut out = String::new();
        for seg in &self.segments {
            match seg {
                Segment::Clean(s) => out.push_str(s),
                Segment::Conflict(c) => {
                    out.push_str("<<<");
                    out.push_str(c.regime.label());
                    if let Some(f) = &c.field {
                        out.push('(');
                        out.push_str(f);
                        out.push(')');
                    }
                    for alt in &c.alternatives {
                        out.push_str("\n|| @");
                        out.push_str(&alt.provenance.author.0.to_string());
                        out.push_str(": ");
                        out.push_str(&alt.text);
                    }
                    out.push_str("\n>>>");
                }
            }
        }
        out
    }
}

/// Walk the *alive* atoms in document order, yielding `(id, content)` for each.
///
/// This is the per-atom companion to [`content`]: where `content` coalesces a
/// clean run into one `String` (losing the atom boundaries), `walk_atoms`
/// preserves the atom granularity so a caller can map "the token at position i"
/// back to "the atom id holding it" — which is exactly what the ergonomic
/// text-diff authoring path ([`crate::Doc`]) needs to MATCH kept tokens to their
/// existing atoms instead of re-minting them.
///
/// It follows the same walk as [`content`]: start at [`AtomId::ROOT`], step
/// through the single live successor, conducting order *through* tombstones. At
/// a genuine antichain (a conflict) the linear order is not in the graph, so the
/// branch-exclusive atoms cannot be linearized here — but a conflict is a
/// **local** state, not a wall (DREGG-DOCUMENT-DESIGN §3): the walk skips the
/// contested alternatives and **resumes at the rejoin point** (the atom the
/// branches reconverge into), so the document's clean tail past the conflict is
/// still authorable. For a clean linear document — the steady state of
/// single-author text editing — this yields every alive atom in order.
pub fn walk_atoms(g: &DocGraph) -> Vec<(AtomId, String)> {
    let mut out = Vec::new();
    let mut visited = BTreeSet::new();
    let mut cursor = AtomId::ROOT;
    loop {
        let succ = live_successors(g, cursor);
        // Mirror the [`content`] walk's order resolution: a single live successor
        // advances; multiple successors that are actually *ordered* (one
        // reachable from another — the insert-in-the-middle shape, where the
        // anchor keeps its old edge to the successor the insert threads before)
        // collapse to the minimal one; only a genuine antichain (>=2 mutually
        // unreachable) is a conflict with no linear order among them.
        let next = match succ.as_slice() {
            [] => return out,
            [single] => *single,
            many => {
                let antichain: Vec<AtomId> = many
                    .iter()
                    .copied()
                    .filter(|&a| !many.iter().any(|&b| b != a && reachable(g, b, a)))
                    .collect();
                if antichain.len() >= 2 {
                    // A genuine fork: the contested alternatives are not
                    // linearizable, but skip them and resume at the rejoin so the
                    // tail is not dropped. No rejoin => the branches are terminal
                    // tails; the clean prefix is all there is to walk.
                    for &head in &antichain {
                        for a in g.branch_atoms(head) {
                            visited.insert(a);
                        }
                    }
                    match rejoin_point(g, &antichain) {
                        Some(r) if visited.insert(r) => {
                            if let Some(a) = g.atom(r) {
                                out.push((r, a.content.render_text()));
                            }
                            cursor = r;
                            continue;
                        }
                        _ => return out,
                    }
                }
                antichain.first().copied().unwrap_or(many[0])
            }
        };
        if !visited.insert(next) {
            return out;
        }
        if let Some(a) = g.atom(next) {
            out.push((next, a.content.render_text()));
        }
        cursor = next;
    }
}

/// Linearize a document graph into rendered content, surfacing antichains and
/// field clashes as first-class conflict regions.
///
/// The walk starts at [`AtomId::ROOT`] and follows order-edges through *alive*
/// atoms. At each step we look at the alive successors reachable from the
/// current frontier:
/// - exactly one path forward => emit it as clean content;
/// - two-or-more mutually-unordered alive successors => emit a prose
///   [`ConflictRegion`], then end the walk at the fork.
///
/// Dead atoms are skipped for content but still conduct order (you can walk
/// *through* a tombstone to its successors), which is what makes a delete
/// monotone and order-preserving. Field clashes are appended after the prose
/// walk.
pub fn content(g: &DocGraph) -> Rendered {
    let mut out = Rendered::default();
    let mut visited = BTreeSet::new();
    walk(g, AtomId::ROOT, &mut visited, &mut out.segments);
    coalesce(&mut out.segments);
    append_field_conflicts(g, &mut out.segments);
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
/// successors with no order between them) and emits them as prose conflicts.
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
                    out.push(Segment::Clean(a.content.render_text()));
                }
                cursor = id;
            }
            many => {
                // Keep only successors not reachable-from another successor
                // (those would be ordered, not concurrent). Two inserts "after
                // X" with no edge between them are mutually unreachable => a
                // real antichain.
                let antichain: Vec<AtomId> = many
                    .iter()
                    .copied()
                    .filter(|&a| !many.iter().any(|&b| b != a && reachable(g, b, a)))
                    .collect();
                if antichain.len() < 2 {
                    // Successors were actually ordered: follow the minimal one.
                    let next = antichain.first().copied().unwrap_or(many[0]);
                    if !visited.insert(next) {
                        return;
                    }
                    if let Some(at) = g.atom(next) {
                        out.push(Segment::Clean(at.content.render_text()));
                    }
                    cursor = next;
                    continue;
                }
                // A genuine prose conflict: each alternative is its own
                // linearization from its head until the branches rejoin (or end).
                let mut alternatives = Vec::new();
                for &head in &antichain {
                    let mut branch = Vec::new();
                    let mut bvisited = visited.clone();
                    let prov = g
                        .atom(head)
                        .map(|a| a.provenance)
                        .unwrap_or(Provenance::GENESIS);
                    if bvisited.insert(head) {
                        if let Some(a) = g.atom(head) {
                            branch.push(Segment::Clean(a.content.render_text()));
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
                    alternatives.push(Alternative {
                        head,
                        text,
                        provenance: prov,
                    });
                    visited.insert(head);
                }
                alternatives.sort_by_key(|a| a.head);
                out.push(Segment::Conflict(ConflictRegion {
                    regime: Regime::Prose,
                    field: None,
                    alternatives,
                }));
                // A conflict is a LOCAL state, not a wall (DREGG-DOCUMENT-DESIGN
                // §3): do NOT stop here. Mark every branch-exclusive atom visited
                // (so the main walk never re-descends into an alternative), then
                // resume at the rejoin point — the atom the branches reconverge
                // into — so the document's tail past the conflict is rendered
                // (never silently dropped). No rejoin => the branches are terminal
                // tails and there is nothing after the fork.
                for &head in &antichain {
                    for a in g.branch_atoms(head) {
                        visited.insert(a);
                    }
                }
                match rejoin_point(g, &antichain) {
                    Some(r) if visited.insert(r) => {
                        if let Some(a) = g.atom(r) {
                            out.push(Segment::Clean(a.content.render_text()));
                        }
                        cursor = r;
                        continue;
                    }
                    _ => return,
                }
            }
        }
    }
}

/// Surface single-valued field clashes (>=2 live assignments) as `Regime::Field`
/// conflict regions, in field-name order.
fn append_field_conflicts(g: &DocGraph, out: &mut Vec<Segment>) {
    let names: Vec<String> = g.field_names().map(|s| s.to_string()).collect();
    for name in names {
        let assigns = g.field(&name);
        if assigns.len() >= 2 {
            let mut alternatives: Vec<Alternative> = assigns
                .iter()
                .map(|a| Alternative {
                    head: AtomId::ROOT,
                    text: a.value.clone(),
                    provenance: a.provenance,
                })
                .collect();
            alternatives.sort_by(|x, y| {
                x.text
                    .cmp(&y.text)
                    .then(x.provenance.patch.cmp(&y.provenance.patch))
            });
            out.push(Segment::Conflict(ConflictRegion {
                regime: Regime::Field,
                field: Some(name),
                alternatives,
            }));
        }
    }
}

/// The **rejoin point** of a set of conflicting branch heads: the nearest atom
/// the branches reconverge into — an alive atom reachable from *every* head
/// (excluding the heads themselves), minimal under reachability (no other common
/// atom precedes it). `None` when the branches never reconverge (each is a
/// terminal tail), i.e. there is genuinely nothing after the fork.
///
/// This is what lets the walk continue *past* a conflict (design §3): the
/// contested alternatives are skipped, and the shared tail resumes at the rejoin.
fn rejoin_point(g: &DocGraph, heads: &[AtomId]) -> Option<AtomId> {
    if heads.len() < 2 {
        return None;
    }
    let mut common: Option<BTreeSet<AtomId>> = None;
    for &h in heads {
        let cone = forward_reach(g, h);
        common = Some(match common {
            None => cone,
            Some(acc) => acc.intersection(&cone).copied().collect(),
        });
    }
    let mut common = common.unwrap_or_default();
    for &h in heads {
        common.remove(&h);
    }
    common.retain(|a| g.atom(*a).map(|x| x.is_alive()).unwrap_or(false));
    // The minimal common atom: one not reachable from any other common atom (the
    // nearest reconvergence). Falls back to the first by id if all incomparable.
    common
        .iter()
        .copied()
        .find(|&r| !common.iter().any(|&o| o != r && reachable(g, o, r)))
        .or_else(|| common.iter().copied().next())
}

/// Every atom reachable from `start` by following order-edges (inclusive of
/// `start`), through atoms alive or dead. The forward cone used to intersect
/// branch heads for [`rejoin_point`].
fn forward_reach(g: &DocGraph, start: AtomId) -> BTreeSet<AtomId> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(s) = stack.pop() {
        if seen.insert(s) {
            stack.extend(g.successors(s));
        }
    }
    seen
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
