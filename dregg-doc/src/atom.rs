//! Atoms — the vertices of a [`crate::DocGraph`].
//!
//! An atom is a span of document content with a stable, content-derived
//! identity, an alive/dead status, and **provenance** (who authored it, in which
//! patch). Following Pijul (DOCUMENT-LANGUAGE.md §2.2), an atom is *never
//! physically removed*: a delete only flips its status to [`Status::Dead`] (a
//! tombstone). Because deletion is therefore additive (you add a tombstone, you
//! never subtract a vertex), deletes commute with everything — which is what
//! makes the union-merge total.
//!
//! The provenance is load-bearing for the conflict view (§3.5): each alternative
//! in a conflict carries *who wrote it*, so "who authored which alternative" is a
//! fact, not a guess. On the substrate this becomes the receipt + authoring
//! branch; here it is an [`Author`] + a [`PatchId`].

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A stable, content-derived identifier for an atom (a graph vertex).
///
/// On the substrate this becomes a content-addressed heap-leaf id; here it is a
/// plain 128-bit value. [`AtomId::ROOT`] is the reserved sentinel that anchors
/// the start of the document — every inserted atom is ordered *after* some
/// existing atom, and the first real atom is ordered after `ROOT`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct AtomId(pub u128);

impl AtomId {
    /// The sentinel start-of-document vertex. It is always alive and carries no
    /// content; it exists so that "insert at the beginning" is uniformly
    /// "insert after `ROOT`".
    pub const ROOT: AtomId = AtomId(0);

    /// Derive a content-addressed id from an author-chosen seed and the atom's
    /// content. Distinct (seed, content) pairs get distinct ids with
    /// overwhelming probability; identical pairs collide *deliberately* (the
    /// same edit authored twice is the same atom — idempotence).
    ///
    /// This is a stand-in for the substrate's real content-addressing; the
    /// *shape* (id derived from content) is what the patch algebra relies on.
    pub fn derive(seed: u64, content: &str) -> AtomId {
        let mut h = DefaultHasher::new();
        0xD0Cu64.hash(&mut h);
        seed.hash(&mut h);
        content.hash(&mut h);
        let lo = h.finish();
        let mut h2 = DefaultHasher::new();
        content.hash(&mut h2);
        seed.hash(&mut h2);
        0xA70Du64.hash(&mut h2);
        let hi = h2.finish();
        // Never collide with the ROOT sentinel.
        let v = ((hi as u128) << 64) | (lo as u128);
        AtomId(if v == 0 { 1 } else { v })
    }
}

/// Who authored an edit. On the substrate this is a cap-holder / cell identity
/// carried by the turn's receipt; here it is an opaque label so the conflict
/// view can attribute each alternative.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Author(pub u64);

impl Author {
    /// The anonymous/system author (e.g. the genesis ROOT atom).
    pub const SYSTEM: Author = Author(0);
}

/// A patch's stable identity — content-addressed over its ops + author. On the
/// substrate this is the turn's receipt id; here it derives from the patch
/// content so the same edit has the same id (idempotence at the patch level).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct PatchId(pub u128);

impl PatchId {
    /// The genesis "patch" that the ROOT sentinel belongs to.
    pub const GENESIS: PatchId = PatchId(0);
}

/// Provenance carried by every atom: who authored it and in which patch. The
/// document's commitment binds this (a light client cannot be shown an
/// alternative whose author is forged — the conflict-as-state soundness goal of
/// DOCUMENT-LANGUAGE.md §4.4 RESEARCH).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Provenance {
    /// The authoring identity.
    pub author: Author,
    /// The patch that introduced this atom.
    pub patch: PatchId,
}

impl Provenance {
    /// The genesis provenance for the ROOT sentinel.
    pub const GENESIS: Provenance = Provenance {
        author: Author::SYSTEM,
        patch: PatchId::GENESIS,
    };
}

/// The liveness status of an atom. Monotone: an atom may only travel
/// `Alive -> Dead`, never back. The join (used by [`crate::merge`]) is therefore
/// "dead wins" — if either branch tombstoned the atom, the merged atom is dead.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Status {
    /// The atom is live: it participates in the rendered content.
    Alive,
    /// The atom is tombstoned: it is retained in the graph (for provenance and
    /// commutation) but excluded from the rendered content.
    Dead,
}

impl Status {
    /// The monotone join of two statuses: `Dead` absorbs `Alive`.
    pub fn join(self, other: Status) -> Status {
        match (self, other) {
            (Status::Alive, Status::Alive) => Status::Alive,
            _ => Status::Dead,
        }
    }
}

/// A vertex of the document graph: a content span with identity, status, and
/// provenance.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Atom {
    /// The atom's stable identity.
    pub id: AtomId,
    /// The atom's content span (coarse-grained by default — DOCUMENT-LANGUAGE.md
    /// §4.4 leaves the atom granularity an empirical design choice).
    pub content: String,
    /// Alive or tombstoned.
    pub status: Status,
    /// Who authored this atom and in which patch.
    pub provenance: Provenance,
}

impl Atom {
    /// True iff this atom currently participates in the rendered content.
    pub fn is_alive(&self) -> bool {
        self.status == Status::Alive
    }
}
