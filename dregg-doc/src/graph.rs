//! The document graph — a graph of alive/dead atoms with order-edges.
//!
//! This is Pijul's concrete data model (DOCUMENT-LANGUAGE.md §2.2): a document
//! is *not* a string of lines but a directed graph whose vertices are content
//! atoms and whose edges encode the order "this atom comes before that one".
//! The visible document is a topological walk over the *alive* atoms following
//! the order-edges (see [`crate::content`]).
//!
//! Every primitive here is *additive* (add a vertex, add a tombstone, add an
//! edge), so the graph at any moment is the **union** of all applied patches'
//! vertices and edges — the colimit, computed by union. That additivity is why
//! [`crate::merge`] is total: you never have to *decide* an order to take the
//! union; you only have to *display* it.

use crate::atom::{Atom, AtomId, Status};
use std::collections::{BTreeMap, BTreeSet};

/// A document as a graph of alive/dead atoms with order-edges.
///
/// `atoms` is the vertex set keyed by id; `edges` is the order relation, stored
/// as an adjacency map `from -> {after...}` meaning "`from` comes before each
/// atom in the set". The graph always contains the [`AtomId::ROOT`] sentinel.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DocGraph {
    atoms: BTreeMap<AtomId, Atom>,
    /// Order-edges: `edges[&a]` is the set of atoms that come strictly *after*
    /// `a`. Stored sorted (BTreeSet) so the graph has a canonical form and
    /// `==` is order-insensitive — load-bearing for the merge-equality tests.
    edges: BTreeMap<AtomId, BTreeSet<AtomId>>,
}

impl Default for DocGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl DocGraph {
    /// A fresh, empty document: just the [`AtomId::ROOT`] sentinel, alive, with
    /// no content and no successors.
    pub fn new() -> Self {
        let mut atoms = BTreeMap::new();
        atoms.insert(
            AtomId::ROOT,
            Atom {
                id: AtomId::ROOT,
                content: String::new(),
                status: Status::Alive,
            },
        );
        DocGraph {
            atoms,
            edges: BTreeMap::new(),
        }
    }

    /// Look up an atom by id.
    pub fn atom(&self, id: AtomId) -> Option<&Atom> {
        self.atoms.get(&id)
    }

    /// Whether an atom with this id exists (alive or dead).
    pub fn contains(&self, id: AtomId) -> bool {
        self.atoms.contains_key(&id)
    }

    /// The number of atoms (including tombstoned ones and the ROOT sentinel).
    pub fn atom_count(&self) -> usize {
        self.atoms.len()
    }

    /// Iterate over all atoms (alive and dead) in id order.
    pub fn atoms(&self) -> impl Iterator<Item = &Atom> {
        self.atoms.values()
    }

    /// The set of atoms ordered strictly after `id` (its successors in the
    /// order relation), in id order.
    pub fn successors(&self, id: AtomId) -> impl Iterator<Item = AtomId> + '_ {
        self.edges.get(&id).into_iter().flatten().copied()
    }

    // ── Additive primitives (the only mutators; each is monotone) ────────────

    /// Add a vertex. Idempotent: re-adding the same id is a no-op (the same
    /// content-addressed atom authored twice is one atom). Re-adding an id that
    /// already exists never *resurrects* a tombstone and never overwrites
    /// content — additivity means an add only ever introduces a *new* vertex.
    pub(crate) fn insert_atom(&mut self, atom: Atom) {
        self.atoms.entry(atom.id).or_insert(atom);
    }

    /// Tombstone a vertex (flip its status to [`Status::Dead`]). Monotone: a
    /// live atom becomes dead; a dead atom stays dead; a missing atom is
    /// ignored (you can only delete what some add introduced).
    pub(crate) fn tombstone(&mut self, id: AtomId) {
        if let Some(a) = self.atoms.get_mut(&id) {
            a.status = Status::Dead;
        }
    }

    /// Add an order-edge `from -> to` ("`from` comes before `to`"). Additive
    /// and idempotent. Self-loops are dropped (an atom never precedes itself).
    pub(crate) fn connect(&mut self, from: AtomId, to: AtomId) {
        if from == to {
            return;
        }
        self.edges.entry(from).or_default().insert(to);
    }

    // ── Union (the colimit) ──────────────────────────────────────────────────

    /// Fold another graph's atoms and edges into this one by union: atom
    /// statuses join (`Dead` wins, monotone), content of an already-present id
    /// is kept (content-addressing guarantees same id => same content), and the
    /// edge sets union. This is the engine of [`crate::merge`].
    pub(crate) fn union_in_place(&mut self, other: &DocGraph) {
        for (id, atom) in &other.atoms {
            self.atoms
                .entry(*id)
                .and_modify(|a| a.status = a.status.join(atom.status))
                .or_insert_with(|| atom.clone());
        }
        for (from, tos) in &other.edges {
            let slot = self.edges.entry(*from).or_default();
            for to in tos {
                slot.insert(*to);
            }
        }
    }
}
