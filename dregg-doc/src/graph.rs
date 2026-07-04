//! The document graph — a graph of alive/dead atoms with order-edges, plus the
//! single-valued field store (the non-monotone fragment).
//!
//! This is Pijul's concrete data model (DOCUMENT-LANGUAGE.md §2.2): a document
//! is *not* a string of lines but a directed graph whose vertices are content
//! atoms and whose edges encode the order "this atom comes before that one".
//! The visible document is a topological walk over the *alive* atoms following
//! the order-edges (see [`crate::content`]).
//!
//! Every *graph* primitive here is additive (add a vertex, add a tombstone, add
//! an edge), so the graph at any moment is the **union** of all applied patches'
//! vertices and edges — the colimit, computed by union. That additivity is why
//! [`crate::merge`] is total on the prose fragment.
//!
//! Alongside the monotone graph sits the **field store** (§2.4): single-valued
//! fields (a canonical title, a pinned authority, a conserved quantity) that are
//! *not* grow-only. Concurrent writes to one field do not union silently — they
//! produce a first-class conflict at the *non-monotone boundary the
//! [`crate::Regime`] classifier draws*. Each field assignment is recorded with
//! its provenance so the conflict can attribute the clashing values.

use crate::atom::{Atom, AtomId, Provenance, Status};
use std::collections::{BTreeMap, BTreeSet};

/// One assignment to a single-valued field, retained for conflict detection +
/// attribution. The store keeps *all* concurrent assignments to a field (it does
/// not overwrite), so a clash is representable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FieldAssign {
    /// The assigned value.
    pub value: String,
    /// Who assigned it.
    pub provenance: Provenance,
}

/// A document as a graph of alive/dead atoms with order-edges, plus a
/// single-valued field store.
///
/// `atoms` is the vertex set keyed by id; `edges` is the order relation, stored
/// as an adjacency map `from -> {after...}` meaning "`from` comes before each
/// atom in the set". The graph always contains the [`AtomId::ROOT`] sentinel.
///
/// `fields` maps a field name to the *set* of concurrently-assigned values
/// (kept all, sorted) so a single-valued field clash is a first-class state.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DocGraph {
    atoms: BTreeMap<AtomId, Atom>,
    /// Order-edges: `edges[&a]` is the set of atoms that come strictly *after*
    /// `a`. Stored sorted (BTreeSet) so the graph has a canonical form and
    /// `==` is order-insensitive — load-bearing for the merge-equality tests.
    edges: BTreeMap<AtomId, BTreeSet<AtomId>>,
    /// Single-valued fields: name -> the set of concurrently-live assignments.
    /// More than one => a non-monotone field conflict (§2.4).
    fields: BTreeMap<String, Vec<FieldAssign>>,
}

impl Default for DocGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl DocGraph {
    /// A fresh, empty document: just the [`AtomId::ROOT`] sentinel, alive, with
    /// no content, no successors, no fields.
    pub fn new() -> Self {
        let mut atoms = BTreeMap::new();
        atoms.insert(
            AtomId::ROOT,
            Atom {
                id: AtomId::ROOT,
                content: String::new(),
                status: Status::Alive,
                provenance: Provenance::GENESIS,
            },
        );
        DocGraph {
            atoms,
            edges: BTreeMap::new(),
            fields: BTreeMap::new(),
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

    /// The live assignments to a single-valued field (>=2 means a clash).
    pub fn field(&self, name: &str) -> &[FieldAssign] {
        self.fields.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// The set of atoms that belong *exclusively* to the branch starting at
    /// `head` — every atom reachable from `head` whose every path from
    /// [`AtomId::ROOT`] passes through `head` (the atoms `head` *dominates*).
    ///
    /// This is exactly the content a prose conflict's alternative carries: the
    /// head and the tail atoms `content`'s walk attributes to that side, up to
    /// (but not including) the rejoin point where the branches converge — those
    /// rejoin/shared atoms are reachable without `head` and so are NOT dominated.
    ///
    /// Tombstoning this whole set is what makes a *keep-one* resolution sound: it
    /// drops the entire dropped alternative (head AND its tail), not just the head
    /// — so the dropped content cannot leak through the tombstone and re-form a
    /// fresh antichain. A single-atom branch yields just `{head}`.
    pub(crate) fn branch_atoms(&self, head: AtomId) -> BTreeSet<AtomId> {
        // 1. Everything reachable from `head` (the branch's forward cone),
        //    including `head` itself.
        let cone = self.forward_cone(head);
        // 2. Everything reachable from ROOT WITHOUT ever stepping onto `head`
        //    (the rest of the document — the shared prefix, the sibling
        //    alternatives, and the common tail past the rejoin point).
        let without_head = self.reachable_avoiding(AtomId::ROOT, head);
        // 3. The dominated set: in the cone, but not reachable around `head`.
        //    `head` itself is dominated by construction (it is the cut vertex).
        cone.into_iter()
            .filter(|a| *a == head || !without_head.contains(a))
            .collect()
    }

    /// All atoms reachable from `start` by following order-edges (inclusive of
    /// `start`), through atoms alive or dead.
    fn forward_cone(&self, start: AtomId) -> BTreeSet<AtomId> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![start];
        while let Some(s) = stack.pop() {
            if seen.insert(s) {
                stack.extend(self.successors(s));
            }
        }
        seen
    }

    /// All atoms reachable from `start` by following order-edges WITHOUT ever
    /// stepping onto `avoid` (and not through it). `start` is included unless it
    /// equals `avoid`. Used to find the document reachable *around* a branch head,
    /// so the head's dominated (branch-exclusive) atoms can be told apart from the
    /// shared/rejoin atoms.
    fn reachable_avoiding(&self, start: AtomId, avoid: AtomId) -> BTreeSet<AtomId> {
        let mut seen = BTreeSet::new();
        if start == avoid {
            return seen;
        }
        let mut stack = vec![start];
        while let Some(s) = stack.pop() {
            if !seen.insert(s) {
                continue;
            }
            for t in self.successors(s) {
                if t != avoid {
                    stack.push(t);
                }
            }
        }
        seen
    }

    /// Structural equality *ignoring provenance*: two graphs agree iff they have
    /// the same atoms (by id, content, status), the same order-edges, and the
    /// same field *values* (regardless of which patch/author wrote them).
    ///
    /// This is the equality the content-addressed algebraic laws live in: the
    /// same edit authored by differently-shaped patches yields the same
    /// *document* even though provenance differs (provenance is metadata bound
    /// for the conflict view, not part of the content-addressed identity).
    pub fn structural_eq(&self, other: &DocGraph) -> bool {
        if self.atoms.len() != other.atoms.len() {
            return false;
        }
        for (id, a) in &self.atoms {
            match other.atoms.get(id) {
                Some(b) if a.content == b.content && a.status == b.status => {}
                _ => return false,
            }
        }
        if self.edges != other.edges {
            return false;
        }
        let field_values = |g: &DocGraph| -> BTreeMap<String, BTreeSet<String>> {
            g.fields
                .iter()
                .map(|(k, v)| (k.clone(), v.iter().map(|a| a.value.clone()).collect()))
                .collect()
        };
        field_values(self) == field_values(other)
    }

    /// All field names that carry at least one assignment, in name order.
    pub fn field_names(&self) -> impl Iterator<Item = &str> {
        self.fields.keys().map(|s| s.as_str())
    }

    /// TEST-ONLY forge hook: rewrite one field-assignment's provenance to a new
    /// author, leaving its *value* unchanged. Used to prove the anti-forge tooth
    /// (a forged alternative renders identically but changes the commitment).
    /// Gated `#[cfg(test)]` — provenance is NEVER publicly mutable, because a
    /// public setter would itself be a forge vector.
    #[cfg(test)]
    pub(crate) fn forge_field_provenance(
        &mut self,
        name: &str,
        value: &str,
        new_author: crate::atom::Author,
    ) {
        if let Some(slot) = self.fields.get_mut(name)
            && let Some(a) = slot.iter_mut().find(|a| a.value == value)
        {
            a.provenance.author = new_author;
        }
    }

    /// TEST-ONLY forge hook: drop one field-assignment entirely (hiding an
    /// alternative). Used to prove a dropped alternative changes the commitment.
    #[cfg(test)]
    pub(crate) fn drop_field_assignment(&mut self, name: &str, value: &str) {
        if let Some(slot) = self.fields.get_mut(name) {
            slot.retain(|a| a.value != value);
        }
    }

    // ── Additive graph primitives (monotone) ─────────────────────────────────

    /// Add a vertex. Idempotent: re-adding the same id is a no-op (the same
    /// content-addressed atom authored twice is one atom). Additivity means an
    /// add only ever introduces a *new* vertex — never resurrects a tombstone,
    /// never overwrites content/provenance.
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

    /// Resurrect a tombstone (`Dead -> Alive`). NOT part of the monotone patch
    /// grammar — used only by [`crate::Patch::invert`] to undo a delete, where
    /// the inverse is applied to the *same* graph the delete acted on.
    pub(crate) fn resurrect(&mut self, id: AtomId) {
        if let Some(a) = self.atoms.get_mut(&id) {
            a.status = Status::Alive;
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

    /// Remove an order-edge. NOT part of the monotone grammar — used only by
    /// [`crate::Patch::invert`].
    pub(crate) fn disconnect(&mut self, from: AtomId, to: AtomId) {
        if let Some(s) = self.edges.get_mut(&from) {
            s.remove(&to);
            if s.is_empty() {
                self.edges.remove(&from);
            }
        }
    }

    // ── Non-monotone field primitive ─────────────────────────────────────────

    /// Assign a single-valued field. Records the assignment *additively* (keeps
    /// it alongside any concurrent assignment) so a clash is representable; a
    /// later assignment by a patch causally after both collapses them via
    /// [`Self::supersede_field`]. Duplicate (value, provenance) pairs dedupe.
    pub(crate) fn assign_field(&mut self, name: &str, value: String, provenance: Provenance) {
        let slot = self.fields.entry(name.to_string()).or_default();
        // A field is single-VALUED: the same value is not a clash, regardless of
        // who wrote it (the I-confluent case). Dedup on value; keep the
        // lexicographically-first provenance so the merge is order-independent.
        if let Some(existing) = slot.iter_mut().find(|a| a.value == value) {
            if (provenance.patch, provenance.author)
                < (existing.provenance.patch, existing.provenance.author)
            {
                existing.provenance = provenance;
            }
            return;
        }
        slot.push(FieldAssign { value, provenance });
        slot.sort_by(|a, b| {
            a.value
                .cmp(&b.value)
                .then(a.provenance.patch.cmp(&b.provenance.patch))
        });
    }

    /// Collapse a field's clashing assignments to a single chosen value (a
    /// resolution). Replaces the whole assignment set with the one chosen value.
    pub(crate) fn supersede_field(&mut self, name: &str, value: String, provenance: Provenance) {
        self.fields
            .insert(name.to_string(), vec![FieldAssign { value, provenance }]);
    }

    /// Drop all assignments to a field. NOT part of the monotone grammar — used
    /// only by [`crate::Patch::invert`] to undo a fresh `SetField`.
    pub(crate) fn retract_field(&mut self, name: &str) {
        self.fields.remove(name);
    }

    // ── Union (the colimit) ──────────────────────────────────────────────────

    /// Fold another graph's atoms, edges, and field-assignments into this one by
    /// union: atom statuses join (`Dead` wins, monotone), content/provenance of
    /// an already-present id is kept (content-addressing guarantees same id =>
    /// same content), edge sets union, and field assignment *sets* union (so two
    /// concurrent assignments to one field both survive as a clash). This is the
    /// engine of [`crate::merge`].
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
        for (name, assigns) in &other.fields {
            for a in assigns {
                self.assign_field(name, a.value.clone(), a.provenance);
            }
        }
    }
}
