//! The perf gate surface skeleton (45; 48 C-10..C-13).
//!
//! Perf is **not** N-way: conformance asks "do all backends produce the same
//! bytes?", perf asks "does THIS one artifact meet ITS budget?" — the observable
//! is backend-shaped even though the input ([`Vector`](crate::Vector)) is shared.
//! The perf channel runs **parallel** to the functional diff, never instead of it
//! (48 C-11): a fast wrong answer is [`GateOutcome::WrongAnswer`], a hard fail —
//! perf cannot launder a correctness regression.
//!
//! A later merge agent authors the bodies (`objdump`/`nm` region extraction, the
//! `CountingAllocator` wire-up, the `perf-budgets/*.toml` ratchet). This module
//! pins the names the rest of the kit references: [`ArtifactInstrumentation`]
//! (emitted by the compiler, 48 C-13), [`PerfSut`], [`GateId`], [`GateOutcome`],
//! [`GateRegistry`].

use crate::adapter::Support;
use crate::hash::ContentHash;
use crate::ids::UnitId;
use crate::observation::Observation;
use crate::provenance::ProvenancedAdapter;
use crate::vector::Input;

// ── the compiler-emitted instrumentation contract (48 C-13: this name wins) ─────
/// The ABI the verified codegen emits an impl of for every artifact. CR-6: a
/// backend that cannot count allocations cannot *pass* a zero-alloc gate by
/// reporting a convenient zero — [`probe_support`](ArtifactInstrumentation::probe_support)
/// reports which probes the codegen ACTUALLY emitted.
pub trait ArtifactInstrumentation {
    /// Identity of the verified build that emitted this artifact.
    fn build_id(&self) -> BuildId;
    /// CR-6 non-vacuity: which probes the codegen ACTUALLY emitted (not-emitted ==
    /// Absent).
    fn probe_support(&self) -> ProbeSupport;
    /// Arm probes for the next measured region; the guard disarms on drop.
    fn arm(&self, probes: ProbeMask) -> ProbeGuard<'_>;
    /// Snapshot armed counters; unarmed/unsupported fields read `None`.
    fn read(&self) -> InstrumentReadings;
    /// The signed hot-path symbol manifest (perf-by-verified-means). `None` for
    /// hand-written backends.
    fn hot_path_digest(&self) -> Option<HotPathDigest>;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BuildId(pub ContentHash);
#[derive(Clone)]
pub struct HotPathDigest(pub ContentHash);

// ── the perf adapter extension (reuses the correctness vectors) ─────────────────
/// `PerfSut: ProvenancedAdapter` — an *optional* capability the [`GateRegistry`]
/// downcasts to (48 C-16). `measure()` RETAINS the functional [`Observation`]
/// (still diffed — 48 C-11).
pub trait PerfSut: ProvenancedAdapter {
    fn instruments(&self, unit: UnitId) -> ProbeSupport;
    fn measure(&self, unit: UnitId, run: &PerfRun) -> MeasuredObservation;
    fn static_query(&self, unit: UnitId, q: StaticQuery) -> StaticAnswer;
}

// ── instruments & readings (the measurement side-channel, 48 C-20) ──────────────
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum InstrumentKind {
    Alloc,
    Cycle,
    Syscall,
    CacheMiss,
    BranchMiss,
    InstrStream,
    Throughput,
    Latency,
}

/// Bitset over [`InstrumentKind`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ProbeMask(pub u32);

/// Reuses the spine's [`Support`] per instrument.
pub struct ProbeSupport(pub Vec<(InstrumentKind, Support)>);

pub struct ProbeGuard<'a> {
    _armed: ProbeMask,
    _art: &'a dyn ArtifactInstrumentation,
}

/// All-`Option` (CR-6): an unobserved instrument is `None`, never a laundered
/// zero. 48 C-20 folds `47`'s fuzz `ResourceSample` into this ONE side-channel:
/// `wall`/`expansion` added here, `peak_rss` aliases `AllocReading.peak_bytes`.
#[derive(Clone, Default)]
pub struct InstrumentReadings {
    pub alloc: Option<AllocReading>,
    pub cycles: Option<CycleReading>,
    pub syscalls: Option<SyscallReading>,
    pub cache_miss: Option<u64>,
    pub branch_miss: Option<u64>,
    pub instr_stream: Option<InstrStreamHash>,
    pub throughput: Option<Throughput>,
    pub latency: Option<LatencyHist>,
    /// Fuzz-facing (48 C-20): wall-clock of the measured region.
    pub wall: Option<core::time::Duration>,
    /// Fuzz-facing (48 C-20): output/input size expansion ratio (bomb detection).
    pub expansion: Option<f64>,
}

#[derive(Clone, Copy)]
pub struct AllocReading {
    pub alloc_count: u64,
    pub dealloc_count: u64,
    pub total_bytes: u64,
    pub peak_bytes: u64, // == the fuzz `peak_rss` alias (48 C-20)
}
#[derive(Clone, Copy)]
pub struct CycleReading {
    pub cycles: u64,
    pub units: u64,
}
#[derive(Clone, Copy)]
pub struct SyscallReading {
    pub count: u64,
    pub units: u64,
}
#[derive(Clone, Copy)]
pub struct Throughput {
    pub value: f64,
    pub unit: ThroughputUnit,
}
#[derive(Clone, Copy)]
pub enum ThroughputUnit {
    Pps,
    ReqPerSec,
    GiBPerSec,
    LookupsPerSec,
    FramesPerSec,
    DecisionsPerSec,
}
#[derive(Clone)]
pub struct LatencyHist {
    pub p50: f64,
    pub p99: f64,
    pub p999: f64,
}
#[derive(Clone)]
pub struct InstrStreamHash(pub ContentHash);

pub struct PerfRun {
    pub input: Input,
    pub warmup: u32,
    pub iters: u32,
    pub concurrency: u32,
    pub probes: ProbeMask,
}

/// `measure()` RETAINS the functional `Observation` (48 C-11) plus the readings +
/// env provenance — the canonical cost side-channel BESIDE `Observation`, never
/// inside it (keeps `VectorId` correctness-only, 48 C-20).
pub struct MeasuredObservation {
    pub observation: Observation,
    pub readings: InstrumentReadings,
    pub env: EnvProvenance,
    pub digest: Option<HotPathDigest>,
}

pub struct EnvProvenance {
    pub host_tag: String,
    pub nic: Option<String>,
    pub pmu: bool,
    pub numa_pinned: bool,
    pub busy_poll: bool,
    pub captured_at: u64,
}

pub struct SkipTicket {
    pub reason: String,
    pub required_env: String,
    pub must_run_in: String,
    pub waiver_expiry: Option<u64>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HwRequirement {
    None,
    Pmu,
    MultiQueueNic,
    Dpdk,
    AfXdp,
}

// ── static (IR/model) queries ───────────────────────────────────────────────────
pub enum StaticQuery {
    AllocNodesReachableOnHotPath,
    SyscallNodesReachableOnBypassPath,
    SyncResolveReachableFromReactor,
    ObservabilityGateDominatesProbe,
    InstrStreamIdentityVsObsCompiledOut,
}
pub enum StaticAnswer {
    Holds,
    Violated { witness: String },
    NotExpressible { reason: String },
}

// ── the gate model (env-independent budget vs env-dependent reading) ────────────
/// e.g. `GateId("zero_per_packet_alloc_datapath")`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct GateId(pub String);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PfLever {
    Substrate,
    Pf1,
    Pf2,
    Pf3,
    Pf4,
    Pf5,
    Pf6,
    Pf7,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GateClass {
    StaticProperty,
    RuntimeProperty,
    HwExecution,
    Methodology,
}

/// The env-independent budget (the number). Variants cover every shape in `41 §E`.
pub enum Budget {
    AbsoluteCeiling {
        metric: InstrumentKind,
        max: f64,
    },
    Floor {
        metric: InstrumentKind,
        min: f64,
    },
    Ratio {
        metric: InstrumentKind,
        baseline: BaselineRef,
        relation: Relation,
    },
    LatencyCeil {
        quantiles: Vec<(f64, core::time::Duration)>,
    },
    StaticPredicate {
        query: StaticQuery,
    },
}
pub enum Relation {
    GreaterEqualMultiple(f64),
    BeatOrMatch,
}
pub struct BaselineRef {
    pub name: String,
    pub source: BaselineSource,
}
/// `ExternalOracle` provides only a baseline NUMBER (never co-linked, CR-3).
pub enum BaselineSource {
    OracleNumber,
    PriorBuildBaseline,
    ConfigOff,
}

// ── the five outcomes (CR-6 + honest env-skip + anti-launder) ───────────────────
pub enum GateOutcome {
    Met {
        readings: InstrumentReadings,
        margin: f64,
    },
    Missed {
        readings: InstrumentReadings,
        budget_kind: InstrumentKind,
        by: f64,
    },
    /// CR-6: a missing counter is NOT a pass.
    InstrumentAbsent {
        instrument: InstrumentKind,
        reason: String,
    },
    /// Recorded, never faked: no NIC/PMU in CI is not "green".
    HwUnavailable {
        requirement: HwRequirement,
        declared_skip: SkipTicket,
    },
    /// A fast WRONG answer (48 C-11): the parallel functional diff failed.
    WrongAnswer,
}

/// The perf runner shell. A later agent authors `run_gate` (drives `measure()`
/// under a reset/snapshot bracket, evaluates the budget, ratchets the
/// `perf-budgets/*.toml`).
pub struct GateRegistry {
    pub gates: std::collections::BTreeMap<String, GateEntry>,
}

/// One registered gate (the env-independent half; the silicon-relative number
/// lives in the budget file, 48 C-10).
pub struct GateEntry {
    pub id: GateId,
    pub lever: PfLever,
    pub class: GateClass,
    pub ledger_row: crate::ids::LedgerKey,
    pub suite_case: crate::ids::CaseKey,
    pub budget: Budget,
}

impl GateRegistry {
    pub fn new() -> Self {
        GateRegistry {
            gates: std::collections::BTreeMap::new(),
        }
    }

    pub fn run_gate(
        &self,
        _gate: &GateId,
        _sut: &dyn PerfSut,
        _unit: UnitId,
        _run: &PerfRun,
    ) -> GateOutcome {
        todo!("drive measure() under bracket, evaluate Budget, ratchet — perf unit (45 §10)")
    }

    pub fn check_verified_means(&self, _sut: &dyn PerfSut, _unit: UnitId) -> GateOutcome {
        todo!("bind measured artifact to a proven build (45 §6 perf-by-verified-means)")
    }
}

impl Default for GateRegistry {
    fn default() -> Self {
        Self::new()
    }
}
