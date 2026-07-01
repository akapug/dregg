//! # `conformance-kit` — the artifact-agnostic conformance / test / perf kit (SKELETON)
//!
//! The test/perf suite is the **FOURTH consumer** of the one DSL description
//! (`docs/engine/20-ARCHITECTURE.md:24-48`): the verified compiler we own emits
//! machine code, the formal model, ~90% of the proofs — and THIS KIT runs one
//! content-addressed corpus of vectors against every backend through ONE uniform
//! surface, the [`SutAdapter`]. Today's `net/` Rust is merely *oracle backend #1*
//! ([`BackendId::CurrentNet`]); the real system-under-test is the future
//! [`BackendId::GeneratedEngine`], which plugs in **for free** because the four
//! adapter methods ARE the four lowered DSL primitives (ADR-7).
//!
//! ## What this skeleton pins
//!
//! - the spine vocabulary ([`ids`]): [`BackendId`], [`Primitive`], [`UnitId`],
//!   [`LedgerKey`], [`CaseKey`], [`Kind`], content addressing ([`hash`]).
//! - the universal adapter surface ([`adapter`]): [`SutAdapter`] (per-`(unit,
//!   primitive)` support), [`Support`], the 9-flag [`ObservedFields`] mask, the
//!   typed absence taxonomies.
//! - the [`observation`] vocabulary: [`Observation`]/[`Produced`] with the
//!   dedicated `linear_trace`/`linearization` fields (48 C-3), the per-primitive
//!   projections, [`Event`] (enum: `Wire | Timer`, 48 C-18), [`ErrorClass`] (48
//!   C-7), [`Status`], [`HeaderSet`], [`Spec`].
//! - the [`provenance`] layer: [`ProvenancedAdapter`], [`AdapterProvenance`], the
//!   [`DslUnit`]/[`GeneratedAdapter`] codegen hook (the engine plugs in for free),
//!   the [`FormalModelAdapter`] wrapper, [`nway_has_independent_witness`].
//! - the [`vector`] record: [`Vector`] = `{ core, meta }` (48 C-1) with accessor
//!   methods, [`Expectation`] (4 variants incl. `Budget(GateRef)`, 48 C-9/C-10).
//! - the [`corpus`] loader + ledger-keying [`CoverageMatrix`] skeleton.
//! - the N-way [`differential`] runner shell: [`DiffRunner`] → [`Verdict`] (the
//!   6-way total partition, 48 C-5) with the {agree / diverge / absent}
//!   non-vacuity accounting (CR-6).
//! - the [`perf`] gate surface skeleton: [`PerfSut`], [`GateRegistry`],
//!   [`GateOutcome`] (the perf channel is *parallel* to the diff, 48 C-11).
//!
//! ## Authoritative source
//!
//! Where any signature here and the prose in `42`–`47` disagree,
//! `docs/engine/48-SEAM-AUDIT.md` **governs** — this crate implements `48` §4.
//!
//! ( ⌐■_■ ) one corpus · one adapter · one observation · the generated engine
//! still plugs in for free — and now it links.
#![allow(dead_code)]
// The skeleton intentionally carries unused type params/fields and `todo!()`
// bodies for surfaces the engine/oracle units will wire later.

pub mod adapter;
pub mod corpus;
pub mod current_net;
pub mod differential;
pub mod hash;
pub mod ids;
pub mod observation;
pub mod perf;
pub mod provenance;
pub mod vector;

// ── the reconciled-spine prelude: re-export the load-bearing names at the root so
//    downstream units read `conformance_kit::SutAdapter`, not the module path. ──
pub use adapter::{BackendAbsentReason, ObservedFields, Support, SutAdapter};
pub use differential::{DiffRunner, FieldPath, RunPolicy, RunReport, VectorReport, Verdict};
pub use hash::{ContentHash, HashDomain, VectorId};
pub use ids::{BackendId, CaseKey, Kind, LedgerKey, Primitive, UnitId};
pub use observation::{
    ArenaView, ErrorClass, Event, HeaderSet, LinearTrace, Linearization, Observation, Produced,
    ResourceOp, Schedule, SmuggleClass, Spec, Status, Trace,
};
pub use provenance::{
    AdapterProvenance, DslUnit, EmittedAdapterCert, FormalModelAdapter, GeneratedAdapter,
    ModelBridgeFn, ProvenancedAdapter, nway_has_independent_witness,
};
pub use vector::{Acceptance, Expectation, Input, Vector, VectorCore, VectorMeta};
