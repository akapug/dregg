//! # deos-reflect — cap-bounded, attested reflection over the deos substance.
//!
//! The gpui-free reflective substrate the scripting env (and, in time, a de-bloated
//! cockpit) binds to. Reflection here is **cap-bounded and attested, not omniscient**
//! (SCRIPTING-AND-DISTRIBUTED-DOM.md §3): crawling is a per-viewer READ (you observe
//! only what your authority reaches; `Committed` fields show their commitment, never
//! the value), distinct from driving (productions / verified turns, which live in
//! `dregg-turn` + the executor).
//!
//! Everything is a pure function of a [`dregg_cell::Ledger`] + receipts — NO gpui, NO
//! starbridge-v2. The algorithms are ported from starbridge-v2's gpui-free
//! `reflect`/`graph`/`affordance` modules, rebased off the cockpit `World` onto the
//! bare substance.
//!
//! ## The reflective surface
//!
//! - [`substance`] — the four substances + the uniform [`substance::Inspectable`]
//!   view ([`substance::reflect_cell`]); reads fields PUBLICLY (attested redaction).
//! - [`graph`] — the ocap graph ([`graph::OcapGraph`]): nodes = cells, edges = caps,
//!   multi-hop reachability (the blast radius), layered delegation depth.
//! - [`frustum`] — the cap-bounded per-viewer crawl ([`frustum::Frustum`]): what a
//!   principal MAY observe (reachability closure + attested reads). "Cap-gated Pharo."
//! - [`affordances`] — a cell's cap-gated message set
//!   ([`affordances::AffordanceSurface`]), projected per-viewer by `is_attenuation`.
//! - [`present`] — the moldable `present()` faces ([`present::ReflectedCell`]):
//!   RawFields · Graph · DomainVisual · Provenance (the substrate-pure subset).

pub mod affordances;
pub mod frustum;
pub mod graph;
pub mod present;
pub mod substance;

pub use affordances::{Affordance, AffordanceSurface, EffectSummary};
pub use frustum::Frustum;
pub use graph::{GraphEdge, GraphLayer, GraphNode, OcapGraph};
pub use present::{
    Presentation, PresentationBody, PresentationKind, ReflectedCell, StateMachineView, TimelineView,
};
pub use substance::{reflect_cell, short_hex, Field, FieldValue, Inspectable, ObjectKind};
