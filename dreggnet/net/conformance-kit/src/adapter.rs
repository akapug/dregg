//! The universal adapter surface — [`SutAdapter`] (48 §4 "the universal adapter
//! surface"; 42 §1).
//!
//! Every backend implements [`SutAdapter`] exactly once. The four methods ARE the
//! four lowered DSL primitives (ADR-7), so the [`GeneratedEngine`](crate::BackendId::GeneratedEngine)
//! adapter is compiler-emitted, not hand-written. Support is genuinely
//! per-`(unit, primitive)` (48 C-14): the oracle supports a unit's `region`
//! surface over the wire but is `Absent` for that same unit's `linear` discipline.

use crate::ids::{BackendId, Primitive, UnitId};
use crate::observation::{Observation, ResourceOp, Schedule, Spec};
use crate::provenance::ObservationMode;

/// The universal sans-IO surface. A **unit** = one DSL unit-under-test (e.g.
/// `h1-request-parse`), mapping 1:1 to a `40-LEDGER` row.
pub trait SutAdapter {
    fn backend(&self) -> BackendId;

    /// CR-6 non-vacuity pre-probe, per-`(unit, primitive)` (48 C-14). `Absent`
    /// here NEVER counts as agreement.
    fn supports(&self, unit: UnitId, prim: Primitive) -> Support;

    /// region/view: bytes → arena-view (H1 `from_httparse` / H2 `from_h2_headers`
    /// / H3 `from_h3_decode`; QPACK/HPACK arena decode).
    fn decode_region(&self, unit: UnitId, input: &[u8], spec: &Spec) -> Observation;

    /// machine: sans-IO FSM fed an event/byte sequence; observed as a folded
    /// trace (the adapter owns the incremental feed loop — 42 tension #4).
    fn run_machine(
        &self,
        unit: UnitId,
        spec: &Spec,
        events: &[crate::observation::Event],
    ) -> Observation;

    /// linear: acquire → use → release-once (the X-4 exactly-once token
    /// discipline).
    fn run_linear(&self, unit: UnitId, ops: &[ResourceOp]) -> Observation;

    /// shared: a schedule → linearization (Iris logical-atomicity;
    /// loom/shuttle-shaped).
    fn run_shared(&self, unit: UnitId, schedule: &Schedule) -> Observation;
}

/// CR-6 non-vacuity probe result. `Absent` is NEVER a match.
pub enum Support {
    Supported {
        observes: ObservedFields,
    },
    /// Typed (48 C-19), not free-text: the CR-6 classifier must not mis-bucket an
    /// *unproven* adapter as a benign skip.
    Absent {
        reason: BackendAbsentReason,
    },
}

bitflags::bitflags! {
    /// Which [`Observation`] fields a `(backend, unit, primitive)` cell can
    /// populate. ONE type, 9 flags, spine-owned (48 C-8 — `43`'s 7-flag
    /// `ObsFieldSet` is an alias that gains `LINEAR_TRACE | LINEARIZATION`). The
    /// differ ranges over the INTERSECTION of these across genuine producers,
    /// never over the whole record.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct ObservedFields: u16 {
        const STATUS        = 1 << 0;
        const HEADERS       = 1 << 1;
        const BODY          = 1 << 2;
        const ARENA_VIEW    = 1 << 3;
        const STATE_TRACE   = 1 << 4;
        const ERROR_CLASS   = 1 << 5;
        const CONSUMED      = 1 << 6;
        const LINEAR_TRACE  = 1 << 7;
        const LINEARIZATION = 1 << 8;
    }
}

/// `43`'s `ObsFieldSet` name yields to [`ObservedFields`] but is kept as an alias
/// so corpus-unit prose (`Projection.fields: ObsFieldSet`) reads unchanged (48 C-8).
pub type ObsFieldSet = ObservedFields;

/// Backend/observation-scope absence (48 C-19; `46`'s variants). Used by
/// [`Support::Absent`] and [`Observation::Absent`](crate::Observation).
pub enum BackendAbsentReason {
    /// Bootstrap: the `GeneratedEngine` has no `EmittedKitBundle` yet.
    EngineNotYetEmitted,
    /// Proof gate failed ⇒ no bundle ⇒ uncounted (NOT a benign skip).
    ProjectionClauseUndischarged { unit: UnitId },
    /// The unit's primitive is not expressible on this backend.
    PrimitiveNotApplicable,
    /// A wire-only oracle cannot furnish (e.g.) `arena_view`.
    ObservationModeTooNarrow { have: ObservationMode },
    /// The out-of-process oracle refused / errored.
    OracleRefused { detail: String },
}
