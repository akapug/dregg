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
//!   alive/dead [`Status`]) plus order-edges.
//! - [`Patch`] — the grammar ([`Op::Add`] / [`Op::Delete`] / [`Op::Connect`])
//!   with [`Patch::apply`].
//! - [`merge`] — the pushout/union: total, commutative, associative, idempotent.
//! - [`content`] — the fold/linearization, with conflicts surfaced as
//!   [`ConflictRegion`]s ([`Segment::Conflict`]).
//! - [`resolve_connect`] / [`resolve_keep`] — resolution patches that collapse a
//!   conflict's antichain.
//!
//! ## What this crate is NOT (deliberately deferred — "let it breathe")
//!
//! This is a STANDALONE, dependency-free core: pure data structures and
//! algorithms, fast and `cargo test`-able in isolation. It does **not** yet ride
//! the cell substrate (atoms = content-addressed heap leaves, patches = turns,
//! content = the patch-history fold, the `ConfluenceClassifier` regime gate) —
//! that weld is the NEXT step (DOCUMENT-LANGUAGE.md §4.1). The atom granularity
//! and the surface syntax are left to emerge from authoring real documents on
//! this core (§4.4, §5).
//!
//! ## Example
//!
//! ```
//! use dregg_doc::{DocGraph, Patch, Op, AtomId, content, merge};
//!
//! // An empty document, then an insert at the start.
//! let mut g = DocGraph::new();
//! let (hello, add) = Patch::add(1, "Hello, ", AtomId::ROOT);
//! let (world, add2) = Patch::add(2, "world.", hello);
//! Patch::from_ops([add, add2]).apply(&mut g);
//! assert_eq!(content(&g).to_marked_string(), "Hello, world.");
//!
//! // Two concurrent inserts at the same position => a first-class conflict,
//! // not a failure.
//! let base = g.clone();
//! let a = Patch::from_ops([Patch::add(3, "A", hello).1]).apply_to(&base);
//! let b = Patch::from_ops([Patch::add(4, "B", hello).1]).apply_to(&base);
//! let merged = merge(&a, &b);
//! assert!(content(&merged).has_conflict());
//! ```

mod atom;
mod content;
mod graph;
mod merge;
mod patch;
mod resolve;

pub use atom::{Atom, AtomId, Status};
pub use content::{ConflictRegion, Rendered, Segment, content};
pub use graph::DocGraph;
pub use merge::{merge, merge_all};
pub use patch::{Op, Patch};
pub use resolve::{resolve_connect, resolve_keep};

#[cfg(test)]
mod tests;
