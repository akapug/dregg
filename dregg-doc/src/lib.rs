//! # dregg-doc — the Pijul-shaped patch-theory core for the dreggverse document language
//!
//! A dreggverse hypermedia document is a *patch-theoretic object*: a document is
//! a **graph of alive/dead content atoms** with order-edges; an edit is a
//! **patch** (`Add` / `Delete`(tombstone) / `Connect`); two concurrent edits are
//! reconciled by **merge**, the categorical **pushout** computed as a total
//! graph union; and a **conflict** — two live, mutually-unordered alternatives
//! at one position — is a *first-class STATE* the document carries until a later
//! patch resolves it, **never a merge failure**.
//!
//! This is the math of Mimram–Di Giusto's *A Categorical Theory of Patches*
//! (repositories = objects, patches = morphisms, merge = pushout) realized in
//! Pijul's concrete graph-of-atoms model. The companion spec is
//! `docs/deos/DOCUMENT-LANGUAGE.md`.
//!
//! ## The shape
//!
//! - [`DocGraph`] — the graph of atoms ([`Atom`]: an [`AtomId`], content, an
//!   alive/dead [`Status`], and [`Provenance`]) plus order-edges, *plus* the
//!   single-valued field store (the non-monotone fragment).
//! - [`Patch`] — the authored grammar ([`Op::Add`] / [`Op::Delete`] /
//!   [`Op::Connect`] / [`Op::SetField`]) with [`Patch::apply`],
//!   [`Patch::compose`], and [`Patch::invert`] (RCCS reversibility).
//! - [`History`] — a document *as* its patch-history; content is
//!   [`History::replay`] / [`History::replay_to`] (time-travel), and
//!   [`History::branch`] / [`History::stitch`] are the branch-and-stitch faces.
//! - [`merge`] — the pushout/union: total, commutative, associative, idempotent.
//! - [`content`] — the fold/linearization, with conflicts surfaced as
//!   [`ConflictRegion`]s ([`Segment::Conflict`]), each [`Alternative`] tagged
//!   with its [`Provenance`] ("who wrote which alternative" is a fact).
//! - [`Regime`] — the two-regime classifier: a [`Regime::Prose`] antichain
//!   (illusory / unilaterally resolvable) vs a [`Regime::Field`] conservation /
//!   authority clash (a *real* conflict that may need consensus).
//! - [`resolve_connect`] / [`resolve_keep`] / [`resolve_field`] — resolution
//!   patches that collapse a conflict (order / choose / settle a field).
//!
//! ## What this crate is NOT (deliberately deferred — "let it breathe")
//!
//! This is a STANDALONE, dependency-free core: pure data structures and
//! algorithms, fast and `cargo test`-able in isolation. It does **not** yet ride
//! the cell substrate (atoms = content-addressed heap leaves, [`Patch`] = turn,
//! [`Provenance`] = receipt + branch, the `ConfluenceClassifier` standing in for
//! [`Regime`]) — that weld is the NEXT step (DOCUMENT-LANGUAGE.md §4.1). The atom
//! granularity, the surface syntax, and the conflict-view UX are left to emerge
//! from authoring real documents on this core (§4.4, §5).
//!
//! ## Example
//!
//! ```
//! use dregg_doc::{DocGraph, History, Patch, Author, AtomId, content, merge};
//!
//! // A document is its patch-history; content is the fold.
//! let mut h = History::new();
//! let (hello, add) = Patch::add(1, "Hello, ", AtomId::ROOT);
//! let (world, add2) = Patch::add(2, "world.", hello);
//! h.commit(Patch::by(Author(1), [add]));
//! h.commit(Patch::by(Author(1), [add2]));
//! assert_eq!(content(&h.replay()).to_marked_string(), "Hello, world.");
//!
//! // Two authors append concurrently at the tail => a first-class conflict
//! // (not a failure), each alternative tagged with who wrote it.
//! let base = h.replay();
//! let a = Patch::by(Author(1), [Patch::add(3, " A", world).1]).apply_to(&base);
//! let b = Patch::by(Author(2), [Patch::add(4, " B", world).1]).apply_to(&base);
//! let merged = merge(&a, &b);
//! let r = content(&merged);
//! assert!(r.has_conflict());
//! // "world." is still clean; the rest of the doc is fully usable.
//! assert!(r.to_marked_string().starts_with("Hello, world."));
//! ```

mod atom;
mod content;
mod graph;
mod history;
mod merge;
mod patch;
mod regime;
mod resolve;

pub use atom::{Atom, AtomId, Author, PatchId, Provenance, Status};
pub use content::{Alternative, ConflictRegion, Rendered, Segment, content};
pub use graph::{DocGraph, FieldAssign};
pub use history::History;
pub use merge::{merge, merge_all};
pub use patch::{Op, Patch};
pub use regime::Regime;
pub use resolve::{
    resolve_connect, resolve_connect_by, resolve_field, resolve_keep, resolve_keep_by,
};

#[cfg(test)]
mod tests;
