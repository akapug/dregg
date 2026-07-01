//! Identity & keys — the spine vocabulary (48 §4 "identity & keys").
//!
//! These are the content-addressable, copyable keys every other module is keyed
//! to. They are deliberately tiny and `Copy` so vectors/reports can fan them out
//! cheaply. `Bytes`/`SmolStr` are skeleton aliases (see [`crate::observation`]).

/// One DSL unit-under-test, e.g. `UnitId("h1-request-parse")`. Maps 1:1 to a
/// `40-LEDGER` row (a unit IS the granularity at which the compiler emits the
/// {code, model, proofs, adapter} quadruple).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct UnitId(pub &'static str);

/// The four DSL primitives (ADR-7; `10-DECISIONS.md:53-55`). The four
/// [`crate::SutAdapter`] methods are exactly these four lowered primitives.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Primitive {
    /// bytes → arena-view (region/view; `decode_region`).
    Region,
    /// `(state, event|bytes) → (state', events, out)` sans-IO FSM (`run_machine`).
    Machine,
    /// acquire → use → release-once, the X-4 token discipline (`run_linear`).
    Linear,
    /// schedule → linearization under interleaving, Iris ranks 5-7 (`run_shared`).
    Shared,
}

/// The four backends one corpus runs against. `CurrentNet` is oracle #1 (the only
/// backend today); `GeneratedEngine` is the real SUT (does not exist yet).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum BackendId {
    /// Today's `net/` Rust, direct in-process call. Oracle #1 / the SUT slot today.
    CurrentNet,
    /// An external reference HTTP engine, out-of-process over IPC (CR-3: read/diff, NEVER linked).
    ExternalOracle,
    /// HOL4/CakeML-extracted pure function (itself a compiler output).
    FormalModel,
    /// Compiler-emitted from the same DSL description. Plugs in for free (§7).
    GeneratedEngine,
}

impl BackendId {
    /// The emitted/non-emitted partition, made **spine-visible** (48 C-16) so
    /// [`crate::nway_has_independent_witness`] is not re-deriving it ad hoc: an
    /// all-emitted agreement is a compiler monoculture and must score zero.
    pub fn is_emitted(self) -> bool {
        matches!(self, BackendId::FormalModel | BackendId::GeneratedEngine)
    }
}

/// A `40-LEDGER` row key, e.g. `LedgerKey("A.1")` (one formal obligation).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct LedgerKey(pub &'static str);

/// A `41-SUITE` case key, e.g. `CaseKey("E.1/zero_per_packet_alloc_datapath")`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct CaseKey(pub &'static str);

/// The reclassifiable kind of a vector (lives in [`crate::VectorMeta`], NOT the
/// hashed core — re-kinding a vector must not change its [`crate::VectorId`]).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    Conformance,
    Behavioral,
    Security,
    Perf,
    Differential,
}
