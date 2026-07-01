//! The [`Vector`] record (48 §4 "the Vector record"; 43 §9 authoritative on shape).
//!
//! `Vector = { core, meta }` (48 C-1): a hashed semantic [`VectorCore`] (the
//! [`VectorId`] preimage) vs an unhashed reclassifiable [`VectorMeta`] (keys +
//! provenance). Re-keying a vector (changing its `kind`/`ledger_rows`) must NOT
//! change its `VectorId` — that is the whole replayability spine. The accessor
//! methods keep `44`/`47`'s `v.unit()` field-access prose valid over the split.
//!
//! Per-doc note: `43` specifies `#[derive(serde::Serialize, …)]` on these types
//! (the dCBOR hash preimage). The skeleton carries the SHAPES; the serde derives
//! and the frozen dCBOR `Canonical` impl are a deferred seam owned by the
//! spec/orchestrator unit (so [`Vector::compute_id`] is `todo!()` for now).

use crate::adapter::ObservedFields;
use crate::hash::{GoldenHash, InputHash, SpecId, VectorId};
use crate::ids::{BackendId, CaseKey, Kind, LedgerKey, Primitive, UnitId};
use crate::observation::{ErrorClass, Event, ResourceOp, Schedule, Spec};
use crate::perf::GateId;

/// The pinned format tag folded into the `VectorId` preimage. Bumping `version`
/// forces a migration that preserves `legacy_ids`.
#[derive(Clone, Copy)]
pub struct FormatTag {
    pub magic: [u8; 4],
    pub version: u16,
}

// ── payload enums ───────────────────────────────────────────────────────────────
/// The driving input. Bytes inputs are stored as a CAS ref (never inline) so the
/// `VectorId` stays small and the blob deduplicates; the runner resolves them to a
/// [`ResolvedInput`](crate::corpus::ResolvedInput) before calling the adapter.
pub enum Input {
    Bytes(InputHash),             // region + machine(parse): CAS ref, NEVER inline
    EventSeq(Vec<Event>),         // machine FSM driving (incl. Event::Timer)
    ResourceOps(Vec<ResourceOp>), // linear: acquire/use/release-once (X-4)
    Schedule(Schedule),           // shared: interleaving (loom/shuttle)
}

/// `Spec` is large; stored either inline or as a CAS ref. The runner resolves to
/// `&Spec` at the call boundary (48 §4 "Spec / SpecRef boundary").
pub enum SpecRef {
    Inline(Spec),
    Cas(SpecId),
}

/// The expected result (48 C-9/C-10: 4 variants). `NwayAgree` has no golden — its
/// quorum lives in [`Acceptance`]; it is REJECTED at registration for any unit
/// whose seam-table row has `<2` Supported producers on the keyed field.
pub enum Expectation {
    Golden(GoldenRef),
    NwayAgree,
    /// A pass REQUIRES a reject (48 C-9: a predicate, not a scalar).
    MustReject(RejectPredicate),
    /// `Kind::Perf` (48 C-10): the "expected" is a budget, held by ref into `45`'s
    /// `GateRegistry`/`perf-budgets/*.toml` (HW-relative numbers cannot be
    /// content-addressed into the core).
    Budget(GateRef),
}

pub struct GoldenRef {
    pub observation: GoldenHash,
    pub backend: BackendId,
}

/// A reference into the perf [`GateRegistry`](crate::perf::GateRegistry) — the
/// `GateId` and the silicon-relative number live in the ratcheted budget file, not
/// the content-addressed core (48 C-10).
pub struct GateRef(pub GateId);

pub enum RejectPredicate {
    /// CVE corpus: must surface a declared reject + no forbidden effect.
    Refuse(RejectSpec),
    /// Fuzz: terminate, no panic, bounded mem/steps.
    Total(TotalityBound),
}

pub struct RejectSpec {
    pub error_class: Vec<ErrorClass>, // >=1 must match (empty = any error)
    pub status_in: Vec<u16>,          // e.g. [400, 431, 501]
    pub must_not: Vec<Effect>,        // negative egress obligation
}

pub enum Effect {
    ForwardedUpstream,
    EgressTo(String),
    ServedPathOutsideRoot,
    EmittedPlaintext,
}

pub struct TotalityBound {
    pub mem_bound: Option<u64>,
    pub step_bound: Option<u64>,
}

// ── acceptance: the pass-predicate (separate from the "right answer") ────────────
pub struct Acceptance {
    pub projection: ProjectionRef, // which Observation fields are compared
    pub quorum: Quorum,            // CR-6: only non-Absent backends count
}

pub enum ProjectionRef {
    Cas(crate::hash::ProjectionId),
    Inline(Projection),
}

/// `fields: ObservedFields` (48 C-8 — `43`'s `ObsFieldSet` unified to the 9-flag
/// spine type).
pub struct Projection {
    pub fields: ObservedFields,
    pub normalize: Vec<Normalizer>,
}

pub enum Normalizer {
    DropDateHeader,
    DropHeader(String),
    MaskServerVersion,
    MaskEphemeralPort,
    SortMultiHeaders,
    LowercaseHeaderNames,
}

/// CR-6: default `min_agree = 2`; counts only non-Absent backends.
pub struct Quorum {
    pub min_agree: u8,
}

impl Default for Quorum {
    fn default() -> Self {
        Quorum { min_agree: 2 }
    }
}

// ── declared replay determinism (lifted nondeterminism) ─────────────────────────
pub struct ReplayNeeds {
    pub clock: ClockMode,
    pub rng_seed: Option<u64>,
    pub tls_key: Option<FixtureRef>,
    pub bind: Option<BindHint>,
}

pub enum ClockMode {
    None,
    FixedEpoch(u64),
    TickDriven,
}

pub struct FixtureRef(pub String);

pub struct BindHint {
    pub host: String,
    pub port_placeholder: u16,
}

// ── the serialized vector: HASHED core + UNHASHED meta ──────────────────────────
/// Exactly the [`VectorId`] preimage — the SEMANTIC core only. Excludes
/// `ledger_rows`/`suite_cases`/`kind`/meta so re-keying is identity-stable.
pub struct VectorCore {
    pub format: FormatTag,
    pub primitive: Primitive,
    pub unit: UnitId,
    pub input: Input,
    pub spec: SpecRef,
    pub expect: Expectation,
    pub acceptance: Acceptance,
    pub replay: ReplayNeeds,
}

/// NOT in the hash preimage. The reclassifiable keys + provenance.
pub struct VectorMeta {
    pub id: VectorId, // == hash(core); verified on load, NEVER trusted
    pub kind: Kind,
    pub ledger_rows: Vec<LedgerKey>, // >=1 (48 C-2: plural)
    pub suite_cases: Vec<CaseKey>,   // >=1
    pub validates: String,
    pub provenance: Provenance,
    pub recorded_at: Option<u64>,
    pub legacy_ids: Vec<VectorId>,
    pub notes: String,
}

pub enum Provenance {
    Authored,
    ImportedCurl { test: u32 },
    BridgedFuzz { target: String, file: String },
    Rfc(String),
    NeedsAuthoring,
}

pub struct Vector {
    pub core: VectorCore,
    pub meta: VectorMeta,
}

impl Vector {
    // ── accessors: keep 44/47's `v.unit()` prose valid over the core/meta split ──
    pub fn unit(&self) -> UnitId {
        self.core.unit
    }
    pub fn primitive(&self) -> Primitive {
        self.core.primitive
    }
    pub fn expectation(&self) -> &Expectation {
        &self.core.expect
    }
    pub fn acceptance(&self) -> &Acceptance {
        &self.core.acceptance
    }
    pub fn kind(&self) -> Kind {
        self.meta.kind
    }
    pub fn ledger_rows(&self) -> &[LedgerKey] {
        &self.meta.ledger_rows
    }
    pub fn suite_cases(&self) -> &[CaseKey] {
        &self.meta.suite_cases
    }

    /// `of_dcbor(Vector, &self.core)` — hash of the SEMANTIC CORE only (43 §2).
    /// Requires the frozen dCBOR `Canonical` impl for `Spec` (48 residual #1).
    /// Deferred seam.
    pub fn compute_id(&self) -> VectorId {
        todo!(
            "of_dcbor(HashDomain::Vector, &self.core) — needs the frozen Spec Canonical impl (43 §2, 48 residual #1)"
        )
    }

    /// Loaders MUST NOT trust the stored id; it is recomputed and verified.
    pub fn verify_id(&self) -> Result<(), IdMismatch> {
        let recomputed = self.compute_id();
        if recomputed == self.meta.id {
            Ok(())
        } else {
            Err(IdMismatch {
                stored: self.meta.id,
                recomputed,
            })
        }
    }
}

#[derive(Debug)]
pub struct IdMismatch {
    pub stored: VectorId,
    pub recomputed: VectorId,
}
