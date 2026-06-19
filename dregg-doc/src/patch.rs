//! The patch grammar — `Add` / `Delete`(tombstone) / `Connect`.
//!
//! Every edit to a document is one of a tiny set of graph operations
//! (DOCUMENT-LANGUAGE.md §2.2). Each operation is *additive*: it adds a vertex,
//! adds a tombstone, or adds an order-edge. Nothing is ever subtracted. This is
//! the whole reason patches commute (when they touch disjoint parts of the
//! graph) and the reason `apply` is order-independent up to the partial order on
//! patches.
//!
//! A [`Patch`] is a sequence of [`Op`]s applied in order; on the substrate a
//! patch *is* a turn whose effects write these leaves and tombstones.

use crate::atom::{Atom, AtomId, Status};
use crate::graph::DocGraph;

/// A single graph operation — the atom of the patch grammar.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Op {
    /// Introduce a fresh atom `id` carrying `content`, ordered immediately
    /// after `after`. Emits the vertex *and* the order-edge `after -> id`. To
    /// insert at the document start, use [`AtomId::ROOT`] as `after`.
    Add {
        /// The new atom's content-addressed id.
        id: AtomId,
        /// Its content span.
        content: String,
        /// The existing atom this new atom is ordered after.
        after: AtomId,
    },
    /// Tombstone an existing atom (monotone `Alive -> Dead`). Retained for
    /// provenance; excluded from rendered content.
    Delete {
        /// The atom to tombstone.
        id: AtomId,
    },
    /// Add an order-edge `from -> to` ("`from` comes before `to`"). The
    /// resolution primitive: connecting two unordered alternatives collapses an
    /// antichain (a conflict) into a chain.
    Connect {
        /// The earlier atom.
        from: AtomId,
        /// The later atom.
        to: AtomId,
    },
}

/// A patch: an ordered bundle of [`Op`]s. Applying a patch applies its ops in
/// sequence. A patch is the unit an author commits; on the substrate it is a
/// turn leaving a receipt.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Patch {
    /// The ops, applied left-to-right.
    pub ops: Vec<Op>,
}

impl Patch {
    /// An empty patch (the identity).
    pub fn new() -> Self {
        Patch { ops: Vec::new() }
    }

    /// Build a patch from a list of ops.
    pub fn from_ops(ops: impl IntoIterator<Item = Op>) -> Self {
        Patch {
            ops: ops.into_iter().collect(),
        }
    }

    /// Convenience: an `Add` op inserting a content span after `after`, with a
    /// content-addressed id derived from `seed` + `content`. Returns the new
    /// atom's id alongside the op so callers can chain.
    pub fn add(seed: u64, content: &str, after: AtomId) -> (AtomId, Op) {
        let id = AtomId::derive(seed, content);
        (
            id,
            Op::Add {
                id,
                content: content.to_string(),
                after,
            },
        )
    }

    /// Push an op onto the patch (builder style).
    pub fn push(&mut self, op: Op) -> &mut Self {
        self.ops.push(op);
        self
    }

    /// Apply this patch to a graph, mutating it in place. Total and monotone:
    /// every op only ever *adds*, so apply never fails and never destroys.
    pub fn apply(&self, g: &mut DocGraph) {
        for op in &self.ops {
            match op {
                Op::Add { id, content, after } => {
                    g.insert_atom(Atom {
                        id: *id,
                        content: content.clone(),
                        status: Status::Alive,
                    });
                    // Anchor the order. If `after` does not yet exist we still
                    // record the edge; a later patch (or merge) may introduce
                    // it — edges are additive and tolerate dangling endpoints,
                    // which is what keeps merge total.
                    g.connect(*after, *id);
                }
                Op::Delete { id } => g.tombstone(*id),
                Op::Connect { from, to } => g.connect(*from, *to),
            }
        }
    }

    /// Apply to a fresh clone, returning the new graph (non-mutating).
    pub fn apply_to(&self, g: &DocGraph) -> DocGraph {
        let mut out = g.clone();
        self.apply(&mut out);
        out
    }

    /// Compose two patches into one whose effect is "apply `self`, then
    /// `other`". Because ops are additive, composition is just concatenation.
    pub fn compose(&self, other: &Patch) -> Patch {
        let mut ops = self.ops.clone();
        ops.extend(other.ops.iter().cloned());
        Patch { ops }
    }
}
