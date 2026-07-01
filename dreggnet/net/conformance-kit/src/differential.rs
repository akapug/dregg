//! The N-way differential runner shell (44; 48 §4 "the runner output").
//!
//! The runner is the N-way generalization of `41-SUITE`'s three-way runner. It
//! holds `&dyn ProvenancedAdapter` (NOT bare `&dyn SutAdapter`, 48 C-16) so it can
//! apply [`nway_has_independent_witness`](crate::nway_has_independent_witness):
//! coverage counts ONLY a [`Verdict::Agree`] whose agreeing set has ≥1
//! non-compiler-emitted witness. Every `(vector × present-backend-set)` lands in
//! **exactly one** [`Verdict`] bucket (a total partition,
//! [`NonVacuityLedger::partition_is_total`]).
//!
//! This skeleton implements the **witness-admission + quorum + independence**
//! accounting for real (the {agree / insufficient / absent} CR-6 firewall). The
//! field-level projection/comparison (turning two `Produced` records into a named
//! [`FieldDivergence`]) is delegated to the [`Projector`] seam, whose bodies the
//! per-primitive units author — `todo!()` here.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;

use crate::adapter::Support;
use crate::hash::ContentHash;
use crate::ids::{BackendId, CaseKey, Kind, LedgerKey, Primitive, UnitId};
use crate::observation::{Bytes, ErrorClass, Observation, OutcomeSet, SmolStr};
use crate::perf::{GateOutcome, GateRegistry};
use crate::provenance::{AdapterProvenance, ProvenancedAdapter, nway_has_independent_witness};
use crate::vector::Vector;

// ===================== the runner =====================
pub struct DiffRunner<'a> {
    backends: Vec<&'a dyn ProvenancedAdapter>, // 48 C-16: provenanced, not bare SutAdapter
    projector: Box<dyn Projector>,
    minimizer: Box<dyn Minimizer>,
    perf: GateRegistry, // 48 C-12: the runner holds a handle into 45's registry
    policy: RunPolicy,
}

impl<'a> DiffRunner<'a> {
    pub fn new(
        backends: Vec<&'a dyn ProvenancedAdapter>,
        projector: Box<dyn Projector>,
        minimizer: Box<dyn Minimizer>,
        perf: GateRegistry,
        policy: RunPolicy,
    ) -> Self {
        DiffRunner {
            backends,
            projector,
            minimizer,
            perf,
            policy,
        }
    }

    /// One vector, all backends. The skeleton classifies by the CR-6 admission
    /// firewall (`supports()` pre-probe + quorum + independence); the field-level
    /// divergence pass is the [`Projector`] seam (deferred).
    pub fn run_vector(&self, v: &Vector) -> VectorReport {
        let unit = v.unit();
        let prim = v.primitive();

        // ── witness admission (CR-6 backend granularity) ──
        let mut witnesses = Vec::new();
        let mut present_provs: Vec<AdapterProvenance> = Vec::new();
        let mut present_backends: Vec<BackendId> = Vec::new();
        let mut absent: Vec<(BackendId, AbsentSummary)> = Vec::new();

        for b in &self.backends {
            let id = b.backend();
            match b.supports(unit, prim) {
                Support::Supported { .. } => {
                    // A real run additionally collects the Observation and projects
                    // it (Produced+wf-ok => Present, wf-fail => Malformed,
                    // Observation::Absent => Absent). That feed loop is the
                    // resolved-input + Projector path, deferred here.
                    witnesses.push(WitnessSummary {
                        backend: id,
                        presence: PresenceTag::Present,
                    });
                    present_provs.push(b.provenance());
                    present_backends.push(id);
                }
                Support::Absent { reason } => {
                    let s = AbsentSummary::from(&reason);
                    witnesses.push(WitnessSummary {
                        backend: id,
                        presence: PresenceTag::Absent {
                            reason: s.text.clone(),
                        },
                    });
                    absent.push((id, s));
                }
            }
        }

        // ── required-backend gate (CR-6) ──
        for req in &self.policy.required {
            if !present_backends.contains(req) {
                let reason = absent
                    .iter()
                    .find(|(b, _)| b == req)
                    .map(|(_, s)| s.text.clone())
                    .unwrap_or_else(|| "not configured".to_string());
                return self.finish(
                    v,
                    witnesses,
                    Verdict::RequiredBackendAbsent {
                        backend: *req,
                        reason,
                    },
                );
            }
        }

        // ── quorum gate (CR-6 field/witness granularity) ──
        let present = present_backends.len();
        if present < self.policy.min_witnesses {
            return self.finish(
                v,
                witnesses,
                Verdict::InsufficientWitnesses {
                    present,
                    required: self.policy.min_witnesses,
                },
            );
        }

        // ── independence gate (48 C-16): an all-emitted agreement scores zero ──
        // Divergence detection itself is the Projector's job; the skeleton reports
        // Agree on a met quorum and lets `counts_as_coverage` enforce independence.
        let verdict = Verdict::Agree { witnesses: present };
        self.finish(v, witnesses, verdict)
    }

    /// Folds the [`NonVacuityLedger`] over a corpus.
    pub fn run_corpus(&self, vs: &[Vector]) -> RunReport {
        let mut vectors = Vec::with_capacity(vs.len());
        let mut ledger = NonVacuityLedger::empty();
        for v in vs {
            let report = self.run_vector(v);
            ledger.fold(&report);
            vectors.push(report);
        }
        RunReport { vectors, ledger }
    }

    fn finish(&self, v: &Vector, witnesses: Vec<WitnessSummary>, verdict: Verdict) -> VectorReport {
        // coverage counts ONLY a genuine, independent Agree (48 C-16).
        let counts_as_coverage = match &verdict {
            Verdict::Agree { .. } => {
                let provs: Vec<AdapterProvenance> = self
                    .backends
                    .iter()
                    .filter(|b| {
                        matches!(
                            b.supports(v.unit(), v.primitive()),
                            Support::Supported { .. }
                        )
                    })
                    .map(|b| b.provenance())
                    .collect();
                nway_has_independent_witness(&provs)
            }
            _ => false,
        };
        let severity = match &verdict {
            Verdict::Divergence { security: true, .. }
            | Verdict::RejectionEscaped { .. }
            | Verdict::Malformed { .. }
            | Verdict::RequiredBackendAbsent { .. } => Severity::Red,
            Verdict::Divergence { .. } => Severity::Red,
            Verdict::Agree { .. } | Verdict::InsufficientWitnesses { .. } => Severity::Recorded,
        };
        let perf = if matches!(v.kind(), Kind::Perf) {
            // 48 C-11: the perf channel is PARALLEL — Some(..) iff Kind::Perf. The
            // actual gate evaluation is the GateRegistry path (deferred).
            None
        } else {
            None
        };
        let _ = &self.perf; // held for the parallel perf channel (48 C-12)
        let _ = &self.projector; // the field-projection seam (deferred)
        let _ = &self.minimizer; // the shrink seam (deferred)
        VectorReport {
            vector: v.meta.id.0,
            unit: v.unit(),
            primitive: v.primitive(),
            ledger_rows: v.ledger_rows().to_vec(),
            suite_cases: v.suite_cases().to_vec(),
            kind: v.kind(),
            witnesses,
            verdict,
            counts_as_coverage,
            severity,
            perf,
        }
    }
}

pub struct RunPolicy {
    /// CR-6 quorum; default 2 for `NwayAgree`.
    pub min_witnesses: usize,
    /// Backends that MUST be Present; default `{CurrentNet}`.
    pub required: BTreeSet<BackendId>,
    /// OOS rows excused from the coverage gate.
    pub waived_rows: BTreeSet<LedgerKey>,
    /// Minimize divergences (off in the fast PR lane).
    pub shrink: bool,
}

impl Default for RunPolicy {
    fn default() -> Self {
        let mut required = BTreeSet::new();
        required.insert(BackendId::CurrentNet);
        RunPolicy {
            min_witnesses: 2,
            required,
            waived_rows: BTreeSet::new(),
            shrink: false,
        }
    }
}

// ===================== witness admission =====================
pub struct WitnessSummary {
    pub backend: BackendId,
    pub presence: PresenceTag,
}
pub enum PresenceTag {
    Present,
    Absent { reason: String },
    Malformed { violation: WfViolation },
}

/// Internal: a flattened absent reason for the per-vector summary.
struct AbsentSummary {
    text: String,
}
impl AbsentSummary {
    fn from(reason: &crate::adapter::BackendAbsentReason) -> Self {
        use crate::adapter::BackendAbsentReason as R;
        let text = match reason {
            R::EngineNotYetEmitted => "engine not yet emitted".to_string(),
            R::ProjectionClauseUndischarged { unit } => {
                format!("projection clause undischarged for {:?}", unit)
            }
            R::PrimitiveNotApplicable => "primitive not applicable".to_string(),
            R::ObservationModeTooNarrow { have } => {
                format!("observation mode too narrow: {:?}", have)
            }
            R::OracleRefused { detail } => format!("oracle refused: {detail}"),
        };
        AbsentSummary { text }
    }
}

/// 21-FORMAL X-2 / X-4 + `wf_parsed_request` violations the wf-gate detects.
pub enum WfViolation {
    ArenaRangeOutOfBounds {
        off: u32,
        len: u32,
        arena_len: usize,
    },
    NonUtf8ArenaRange {
        off: u32,
        len: u32,
    },
    TraceNonMonotone {
        step: usize,
    },
    ConsumedExceedsInput {
        consumed: usize,
        input_len: usize,
    },
    TokenUsedTwice {
        handle: crate::observation::HandleId,
    },
    InvariantBreach,
}

// ===================== per-primitive wf-checked normal form =====================
pub enum Projection {
    Region(RegionProj),
    Machine(MachineProj),
    Linear(LinearProj),
    Shared(SharedProj),
}

pub struct RegionProj {
    pub status: u16,
    pub error_class: Option<ErrorClass>,
    pub consumed: ConsumedCell,
    pub headers: CanonHeaders,
    pub body: Bytes,
    pub arena: Option<ArenaLayout>, // None for layout-opaque backends (oracle)
}
pub struct ArenaLayout {
    pub bytes: Bytes,
    pub triples: Vec<(crate::observation::NameTag, u32, u32)>,
    pub sidecar: Bytes,
}
pub enum ConsumedCell {
    Count(usize),
    NotApplicable, // tri-state Incomplete
}
/// Resolved name → value(s), dup-preserving (48 residual #3 pins the join rule).
pub struct CanonHeaders(pub Vec<(HeaderName, Vec<Bytes>)>);
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HeaderName(pub Bytes);

pub struct MachineProj {
    pub trace: Vec<StepTag>,
    pub emitted: Bytes,
    pub events: Vec<crate::observation::Event>,
    pub error_class: Option<ErrorClass>,
}
pub enum StepTag {
    Complete { consumed: usize },
    Incomplete,
    Error,
}

pub enum LinearProj {
    Clean,
    Violation(DisciplineVerdict),
}

pub struct SharedProj {
    pub linearizable: bool,
    pub invariant_held: bool,
    pub observed: OutcomeSet,
    pub model_allowed: Option<OutcomeSet>,
}

// ===================== field & cell vocabulary =====================
pub enum FieldPath {
    // region/view
    ErrorClass,
    Status,
    Consumed,
    Body,
    Header(HeaderName),
    ArenaBytes,
    ArenaTriple { tag: crate::observation::NameTag },
    Sidecar { tag: crate::observation::NameTag },
    // machine
    TriState,
    StateLabel { step: usize },
    Emitted { step: usize },
    EmittedTotal,
    // linear / shared
    Discipline,
    Linearizable,
    InvariantHeld,
}

impl FieldPath {
    /// Headline ordering (`ErrorClass`/`Status` first).
    pub fn ordinal(&self) -> u16 {
        match self {
            FieldPath::ErrorClass => 0,
            FieldPath::Status => 1,
            FieldPath::Consumed => 2,
            FieldPath::Body => 3,
            FieldPath::Header(_) => 4,
            FieldPath::ArenaBytes => 5,
            FieldPath::ArenaTriple { .. } => 6,
            FieldPath::Sidecar { .. } => 7,
            FieldPath::TriState => 8,
            FieldPath::StateLabel { .. } => 9,
            FieldPath::Emitted { .. } => 10,
            FieldPath::EmittedTotal => 11,
            FieldPath::Discipline => 12,
            FieldPath::Linearizable => 13,
            FieldPath::InvariantHeld => 14,
        }
    }
    pub fn applicability(&self) -> BackendApplicability {
        match self {
            FieldPath::ArenaBytes | FieldPath::ArenaTriple { .. } | FieldPath::Sidecar { .. } => {
                BackendApplicability::ZeroCopyLayout
            }
            _ => BackendApplicability::All,
        }
    }
}

pub enum Cell {
    Status(u16),
    Bytes(Bytes),
    HeaderValue(Bytes),
    ErrorClass(ErrorClass),
    Consumed(usize),
    Tri(StepTagKind),
    StateLabel(SmolStr),
    Discipline(DisciplineVerdict),
    Bool(bool),
    /// `!= any Cell`, including another `Absent` (CR-6).
    Absent {
        reason: CellAbsentReason,
    },
}
pub enum StepTagKind {
    Complete,
    Incomplete,
    Error,
}

/// Cell/field-scope absence (48 C-19; `44`'s variants).
pub enum CellAbsentReason {
    TriStateIncomplete,
    FieldNotProduced,
    NotApplicableToBackend,
}

pub enum DisciplineVerdict {
    Clean,
    DoubleRelease {
        handle: crate::observation::HandleId,
        first: OpIndex,
        second: OpIndex,
    },
    UseAfterRelease {
        handle: crate::observation::HandleId,
        released_at: OpIndex,
        used_at: OpIndex,
    },
    Leak {
        handle: crate::observation::HandleId,
        acquired_at: OpIndex,
    },
    UseWithoutAcquire {
        handle: crate::observation::HandleId,
        used_at: OpIndex,
    },
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OpIndex(pub u32);

// ===================== projection + comparison seam =====================
pub trait Projector {
    /// Runs the wf-gate: `Produced`+wf-ok → `Present(Projection)`, wf-fail →
    /// `Malformed`, `Observation::Absent` → `Absent`. NEVER panics.
    fn project(&self, obs: &Observation, p: Primitive) -> Presence;
    /// Flatten a wf-checked projection into comparison cells.
    fn fields(&self, proj: &Projection) -> Vec<(FieldPath, Cell)>;
    fn field_spec(&self, field: &FieldPath) -> FieldSpec;
}
pub enum Presence {
    Present(Projection),
    Absent { reason: String },
    Malformed { violation: WfViolation },
}
pub struct FieldSpec {
    pub comparator: Comparator,
    pub applicability: BackendApplicability,
}
pub enum Comparator {
    StatusExact,
    BytesExact,
    HeaderMultiset,
    ErrorClassEq,
    Exact,
    Predicate,
}
pub enum BackendApplicability {
    All,
    /// `{CurrentNet, FormalModel, GeneratedEngine}`.
    ZeroCopyLayout,
    Custom(BTreeSet<BackendId>),
}

// ===================== minimization seam =====================
pub trait Minimizer {
    fn shrink(
        &self,
        input: &crate::vector::Input,
        spec: &crate::observation::Spec,
        target: &FieldPath,
        still_diverges: &dyn Fn(&crate::vector::Input) -> bool,
    ) -> MinimalRepro;
}
pub struct MinimalRepro {
    pub still_diverges_on: FieldPath,
    pub shrink_steps: u32,
}

// ===================== verdict (a TOTAL partition) =====================
pub enum Verdict {
    /// `counts_as_coverage` iff independence holds (48 C-16).
    Agree {
        witnesses: usize,
    },
    Divergence {
        primary: FieldPath,
        fields: Vec<FieldDivergence>,
        security: bool,
    },
    /// `< quorum`; never coverage.
    InsufficientWitnesses {
        present: usize,
        required: usize,
    },
    RequiredBackendAbsent {
        backend: BackendId,
        reason: String,
    },
    RejectionEscaped {
        accepting: Vec<BackendId>,
        minimal_repro: Option<MinimalRepro>,
    },
    Malformed {
        backend: BackendId,
        violation: WfViolation,
    },
}
pub struct FieldDivergence {
    pub field: FieldPath,
    pub clustering: Clustering,
    pub per_backend: BTreeMap<BackendId, Cell>,
    pub minimal_repro: Option<MinimalRepro>,
}
pub enum Clustering {
    Outlier {
        outlier: BackendId,
        majority: BTreeSet<BackendId>,
        majority_value: CellDigest,
    },
    Schism {
        clusters: Vec<(CellDigest, BTreeSet<BackendId>)>,
    },
    AgainstGolden {
        dissenting: BTreeSet<BackendId>,
    },
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CellDigest(pub ContentHash);
pub enum Severity {
    Red,
    Recorded,
}

// ===================== reports =====================
pub struct VectorReport {
    pub vector: ContentHash,
    pub unit: UnitId,
    pub primitive: Primitive,
    pub ledger_rows: Vec<LedgerKey>, // 48 C-2: plural
    pub suite_cases: Vec<CaseKey>,
    pub kind: Kind,
    pub witnesses: Vec<WitnessSummary>,
    pub verdict: Verdict,
    /// true ⟺ a genuine, independent `Verdict::Agree`.
    pub counts_as_coverage: bool,
    pub severity: Severity,
    /// `Some(..)` iff `Kind::Perf` (the parallel perf channel, 48 C-11).
    pub perf: Option<GateOutcome>,
}
pub struct RunReport {
    pub vectors: Vec<VectorReport>,
    pub ledger: NonVacuityLedger,
}

// ===================== non-vacuity ledger (CR-6 honesty surface) =====================
pub struct NonVacuityLedger {
    pub total: usize,
    pub genuine_agreements: usize,
    pub divergences: usize,
    pub insufficient: usize,
    pub required_absent: usize,
    pub rejection_escaped: usize,
    pub malformed: usize,
    pub absent_by_backend: BTreeMap<BackendId, usize>,
    pub per_row: BTreeMap<LedgerKey, RowAccounting>,
}
#[derive(Default)]
pub struct RowAccounting {
    pub vectors: usize,
    pub genuine_agreements: usize,
    pub present_by_backend: BTreeMap<BackendId, usize>,
    pub absent_by_backend: BTreeMap<BackendId, usize>,
}

impl NonVacuityLedger {
    fn empty() -> Self {
        NonVacuityLedger {
            total: 0,
            genuine_agreements: 0,
            divergences: 0,
            insufficient: 0,
            required_absent: 0,
            rejection_escaped: 0,
            malformed: 0,
            absent_by_backend: BTreeMap::new(),
            per_row: BTreeMap::new(),
        }
    }

    fn fold(&mut self, r: &VectorReport) {
        self.total += 1;
        match &r.verdict {
            Verdict::Agree { .. } if r.counts_as_coverage => self.genuine_agreements += 1,
            Verdict::Agree { .. } => self.insufficient += 1, // non-independent ⇒ not coverage
            Verdict::Divergence { .. } => self.divergences += 1,
            Verdict::InsufficientWitnesses { .. } => self.insufficient += 1,
            Verdict::RequiredBackendAbsent { .. } => self.required_absent += 1,
            Verdict::RejectionEscaped { .. } => self.rejection_escaped += 1,
            Verdict::Malformed { .. } => self.malformed += 1,
        }
        for w in &r.witnesses {
            if !matches!(w.presence, PresenceTag::Present) {
                *self.absent_by_backend.entry(w.backend).or_default() += 1;
            }
        }
        for row in &r.ledger_rows {
            let acc = self.per_row.entry(*row).or_default();
            acc.vectors += 1;
            if matches!(r.verdict, Verdict::Agree { .. }) && r.counts_as_coverage {
                acc.genuine_agreements += 1;
            }
            for w in &r.witnesses {
                match w.presence {
                    PresenceTag::Present => {
                        *acc.present_by_backend.entry(w.backend).or_default() += 1
                    }
                    _ => *acc.absent_by_backend.entry(w.backend).or_default() += 1,
                }
            }
        }
    }

    /// Buckets sum == total (asserted by the runner's self-check).
    pub fn partition_is_total(&self) -> bool {
        self.genuine_agreements
            + self.divergences
            + self.insufficient
            + self.required_absent
            + self.rejection_escaped
            + self.malformed
            == self.total
    }

    /// The keying half of `41:345-347`: every non-OOS row owns ≥1 genuinely
    /// covered vector.
    pub fn coverage_gate(&self, non_oos: &BTreeSet<LedgerKey>) -> GateResult {
        let mut empty_rows = Vec::new();
        for row in non_oos {
            match self.per_row.get(row) {
                Some(acc) if acc.genuine_agreements >= 1 => {}
                _ => empty_rows.push(*row),
            }
        }
        // `oracle_dark_rows` derivability is 48 residual open question #7.
        if empty_rows.is_empty() {
            GateResult::Pass
        } else {
            GateResult::Fail {
                empty_rows,
                oracle_dark_rows: Vec::new(),
            }
        }
    }

    /// Non-zero iff any Red severity (the CI gate).
    pub fn ci_exit(&self) -> ExitCode {
        if self.divergences + self.required_absent + self.rejection_escaped + self.malformed > 0 {
            ExitCode::FAILURE
        } else {
            ExitCode::SUCCESS
        }
    }
}

pub enum GateResult {
    Pass,
    Fail {
        empty_rows: Vec<LedgerKey>,
        oracle_dark_rows: Vec<LedgerKey>,
    },
}
