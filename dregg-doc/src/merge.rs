//! `merge` — the categorical PUSHOUT, computed as a total graph union.
//!
//! Two patches made from the same starting state (a fork) are merged by taking
//! their **pushout** (Mimram–Di Giusto, DOCUMENT-LANGUAGE.md §2.1): the smallest
//! state containing the effect of both edits. In Pijul's graph model the pushout
//! is *just the union of the graphs* (§2.2): because every patch operation is
//! additive (add a vertex, add a tombstone, add an edge), the colimit is
//! computed by union — you never have to *decide* an order to take it, you only
//! have to *display* it (and where the order is genuinely undecided, the union
//! carries a first-class antichain that [`crate::content`] surfaces as a
//! conflict).
//!
//! This makes [`merge`]:
//! - **total** — the union always exists (no fork has "no merge"; the missing
//!   order becomes a representable antichain, not a failure);
//! - **commutative** — `merge(a, b) == merge(b, a)` (set/edge union and the
//!   `Dead`-wins status join are both commutative);
//! - **associative** — `merge(merge(a, b), c) == merge(a, merge(b, c))` (a finite
//!   colimit is the colimit of the whole diagram, however you bracket it);
//! - **idempotent** — `merge(a, a) == a`.
//!
//! The graph's canonical form (sorted atoms + sorted edge sets, [`DocGraph`]'s
//! `BTreeMap`/`BTreeSet`) makes these hold as `==` equalities, not merely
//! up-to-isomorphism.

use crate::graph::DocGraph;

/// The pushout/union merge of two document graphs. Total, commutative,
/// associative, idempotent. See the module docs.
pub fn merge(a: &DocGraph, b: &DocGraph) -> DocGraph {
    let mut out = a.clone();
    out.union_in_place(b);
    out
}

/// Merge a whole collection of graphs (the colimit of the diagram). The order of
/// the inputs does not matter — a direct consequence of merge's commutativity
/// and associativity.
pub fn merge_all<'a>(graphs: impl IntoIterator<Item = &'a DocGraph>) -> DocGraph {
    let mut it = graphs.into_iter();
    let mut acc = match it.next() {
        Some(g) => g.clone(),
        None => DocGraph::new(),
    };
    for g in it {
        acc.union_in_place(g);
    }
    acc
}
