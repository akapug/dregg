//! The patch grammar — `Add` / `Delete`(tombstone) / `Connect` / `SetField`,
//! plus the inverse ops the RCCS-reversibility face needs.
//!
//! Every edit to a document is one of a tiny set of operations
//! (DOCUMENT-LANGUAGE.md §2.2). The forward graph ops (`Add`/`Delete`/`Connect`)
//! are *additive*: they add a vertex, add a tombstone, or add an order-edge.
//! Nothing is ever subtracted. This is the whole reason patches commute (when
//! they touch disjoint parts of the graph) and the reason `apply` is
//! order-independent up to the partial order on patches.
//!
//! `SetField` is the *non-monotone* op (§2.4): a write to a single-valued field
//! (a canonical title, a pinned authority). Two concurrent `SetField`s to one
//! field do not union away — they leave a first-class clash the
//! [`crate::Regime`] classifier flags as a *real* conflict.
//!
//! A [`Patch`] is authored (it carries an [`Author`]) and has a content-derived
//! [`PatchId`]; on the substrate a patch *is* a turn whose effects write these
//! leaves, tombstones, and fields, leaving a receipt. Patches are **invertible**
//! ([`Patch::invert`], §4.1) — the inverse undoes the patch on the graph the
//! patch acted on (`Resurrect`/`Disconnect`/`RetractField` are the inverse ops).

use crate::atom::{Atom, AtomContent, AtomId, Author, PatchId, Provenance, Status};
use crate::graph::DocGraph;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A single document operation — the atom of the patch grammar.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    /// Introduce a fresh atom `id` carrying `content`, ordered immediately
    /// after `after`. Emits the vertex *and* the order-edge `after -> id`. To
    /// insert at the document start, use [`AtomId::ROOT`] as `after`.
    Add {
        /// The new atom's content-addressed id.
        id: AtomId,
        /// Its typed content ([`AtomContent`]): a text run or a structural node.
        content: AtomContent,
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
    /// resolution primitive for prose conflicts: connecting two unordered
    /// alternatives collapses an antichain into a chain.
    Connect {
        /// The earlier atom.
        from: AtomId,
        /// The later atom.
        to: AtomId,
    },
    /// Assign a single-valued field (the non-monotone op). Concurrent assigns to
    /// one field clash; `superseding = true` collapses the clash (a resolution).
    SetField {
        /// The field name.
        name: String,
        /// The value to assign.
        value: String,
        /// If true, this assignment *supersedes* all concurrent ones (it is a
        /// resolution by a patch causally after the clash); if false, it is a
        /// fresh assignment that may clash with a concurrent one.
        superseding: bool,
    },

    // ── inverse ops (used by `invert`; sound against the producing graph) ─────
    /// Resurrect a tombstoned atom (`Dead -> Alive`) — the inverse of `Delete`.
    Resurrect {
        /// The atom to bring back to life.
        id: AtomId,
    },
    /// Remove an order-edge — the inverse of `Connect` / the edge half of `Add`.
    Disconnect {
        /// The earlier atom.
        from: AtomId,
        /// The later atom.
        to: AtomId,
    },
    /// Drop all assignments to a field — the inverse of a non-superseding
    /// `SetField`.
    RetractField {
        /// The field name.
        name: String,
    },
}

/// A patch: an authored, content-addressed bundle of [`Op`]s. Applying a patch
/// applies its ops in sequence with the patch's provenance. On the substrate it
/// is a turn leaving a receipt.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Patch {
    /// Who authored this patch.
    pub author: Author,
    /// The ops, applied left-to-right.
    pub ops: Vec<Op>,
}

impl Default for Patch {
    fn default() -> Self {
        Patch::new()
    }
}

impl Patch {
    /// An empty patch authored by [`Author::SYSTEM`] (the identity).
    pub fn new() -> Self {
        Patch {
            author: Author::SYSTEM,
            ops: Vec::new(),
        }
    }

    /// Build a patch from a list of ops, authored by [`Author::SYSTEM`].
    pub fn from_ops(ops: impl IntoIterator<Item = Op>) -> Self {
        Patch {
            author: Author::SYSTEM,
            ops: ops.into_iter().collect(),
        }
    }

    /// Build an authored patch.
    pub fn by(author: Author, ops: impl IntoIterator<Item = Op>) -> Self {
        Patch {
            author,
            ops: ops.into_iter().collect(),
        }
    }

    /// Set the author (builder).
    pub fn authored_by(mut self, author: Author) -> Self {
        self.author = author;
        self
    }

    /// This patch's stable, content-derived identity (over its ops + author).
    /// The same edit by the same author has the same id (patch-level
    /// idempotence). On the substrate this is the turn's receipt id.
    pub fn id(&self) -> PatchId {
        let mut h = DefaultHasher::new();
        0x9A7C_0AFEu64.hash(&mut h);
        self.author.hash(&mut h);
        self.ops.hash(&mut h);
        let lo = h.finish();
        let mut h2 = DefaultHasher::new();
        self.ops.hash(&mut h2);
        self.author.hash(&mut h2);
        0x0D0C_001Du64.hash(&mut h2);
        let hi = h2.finish();
        let v = ((hi as u128) << 64) | (lo as u128);
        PatchId(if v == 0 { 1 } else { v })
    }

    /// The provenance this patch stamps onto the atoms/fields it writes.
    fn provenance(&self) -> Provenance {
        Provenance {
            author: self.author,
            patch: self.id(),
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
                content: AtomContent::Text(content.to_string()),
                after,
            },
        )
    }

    /// Convenience: an `Add` op inserting an arbitrary typed [`AtomContent`] after
    /// `after`. The id is content-addressed over `seed` + a canonical key derived
    /// from the content's kind (so a structural node and a text run seeded the
    /// same never collide). Returns the new atom's id alongside the op.
    pub fn add_content(seed: u64, content: AtomContent, after: AtomId) -> (AtomId, Op) {
        // Derive over a hex of the type-tagged canonical bytes so the id binds the
        // kind, not just a rendered projection.
        let key: String = content
            .canonical_bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let id = AtomId::derive(seed, &key);
        (id, Op::Add { id, content, after })
    }

    /// Push an op onto the patch (builder style).
    pub fn push(&mut self, op: Op) -> &mut Self {
        self.ops.push(op);
        self
    }

    /// Apply this patch to a graph, mutating it in place. The forward graph ops
    /// only ever *add*, so apply never fails and never destroys.
    pub fn apply(&self, g: &mut DocGraph) {
        let prov = self.provenance();
        for op in &self.ops {
            match op {
                Op::Add { id, content, after } => {
                    g.insert_atom(Atom {
                        id: *id,
                        content: content.clone(),
                        status: Status::Alive,
                        provenance: prov,
                    });
                    // Anchor the order. If `after` does not yet exist we still
                    // record the edge; a later patch (or merge) may introduce
                    // it — edges are additive and tolerate dangling endpoints,
                    // which is what keeps merge total.
                    g.connect(*after, *id);
                }
                Op::Delete { id } => g.tombstone(*id),
                Op::Connect { from, to } => g.connect(*from, *to),
                Op::SetField {
                    name,
                    value,
                    superseding,
                } => {
                    if *superseding {
                        g.supersede_field(name, value.clone(), prov);
                    } else {
                        g.assign_field(name, value.clone(), prov);
                    }
                }
                Op::Resurrect { id } => g.resurrect(*id),
                Op::Disconnect { from, to } => g.disconnect(*from, *to),
                Op::RetractField { name } => g.retract_field(name),
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
    /// `other`". Because forward graph ops are additive, composition is
    /// concatenation. The composite inherits `self`'s author.
    pub fn compose(&self, other: &Patch) -> Patch {
        let mut ops = self.ops.clone();
        ops.extend(other.ops.iter().cloned());
        Patch {
            author: self.author,
            ops,
        }
    }

    /// The inverse patch (RCCS reversibility, §4.1): applied to the graph *this*
    /// patch produced, it restores the prior graph. The ops are reversed in
    /// order; each forward op maps to its undo:
    /// - `Add{id, after}`  => `Disconnect{after, id}` then the atom is left
    ///   tombstone-free but unreachable (a fresh add introduced a new atom + a
    ///   new edge; dropping the edge removes it from the walk);
    /// - `Delete{id}`      => `Resurrect{id}`;
    /// - `Connect{f, t}`   => `Disconnect{f, t}`;
    /// - `SetField`(fresh) => `RetractField`.
    ///
    /// `invert` is *contextual* (the standard RCCS caveat): sound against the
    /// graph the original patch acted on. For the common edit/undo pair on one
    /// graph it round-trips exactly.
    pub fn invert(&self) -> Patch {
        let mut ops = Vec::with_capacity(self.ops.len());
        for op in self.ops.iter().rev() {
            match op {
                Op::Add { id, after, .. } => {
                    ops.push(Op::Disconnect {
                        from: *after,
                        to: *id,
                    });
                }
                Op::Delete { id } => ops.push(Op::Resurrect { id: *id }),
                Op::Connect { from, to } => ops.push(Op::Disconnect {
                    from: *from,
                    to: *to,
                }),
                Op::SetField {
                    name, superseding, ..
                } => {
                    if !*superseding {
                        ops.push(Op::RetractField { name: name.clone() });
                    }
                }
                // Inverting an inverse op: the natural dual.
                Op::Resurrect { id } => ops.push(Op::Delete { id: *id }),
                Op::Disconnect { from, to } => ops.push(Op::Connect {
                    from: *from,
                    to: *to,
                }),
                Op::RetractField { .. } => {}
            }
        }
        Patch {
            author: self.author,
            ops,
        }
    }
}
