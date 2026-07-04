# 45 — THE PERF-GATE HARNESS (artifact-agnostic)

> **UNIT 4** of the conformance kit. Makes `22-PERFORMANCE` and `41-TEST-AND-PERF-SUITE` §E
> (the substrate budget + `PF-1…PF-7`) **artifact-agnostic**. The load-bearing reframe: a perf
> gate is **a property of the emitted artifact**, measured through instrumentation *the verified
> compiler emits* (alloc-counter · cycle-counter · syscall-counter · instruction-stream hook),
> evaluated against a budget fixed **independent of any machine**. It is **not** a `#[bench]`
> bolted onto whichever Rust happens to exist today. The same gate definition runs against
> `current-net-rust` now and against the `generated-engine` for free — because both satisfy one
> instrumentation contract. This doc fixes that contract, the gate model, the budget-file format,
> the four classes of gate, and the `perf-by-verified-means` check. It layers on the fixed
> `SutAdapter` spine (units 1–3); the perf-specific friction with the spine is reported in `Seams`.

---

## 0. The reframe — why `#[bench]` is the wrong shape

`22-PERFORMANCE.md:3-5` fixes line-rate as a **done-criterion**, *not* an aspiration, achieved
**by verified means** (`:126-134`, never by dropping to unverified code). `41 §E:264-267` makes
each gate an **acceptance gate that states its own number**, component-by-component, with no
aggregate roll-up that can hide a regressed component.

A bench bolted onto today's Rust measures the **baseline oracle** (`current-net-rust`, oracle
backend #1) — *not* the system under test, which is the future generated engine. So the perf
suite must be artifact-agnostic the same way the conformance suite is: **one gate definition, run
against whichever backend exposes the instruments.** The unit of measurement is a **counter the
artifact exposes**, where the counter source is `alloc | cycle | syscall | instruction-stream`.
Today `current-net-rust` already satisfies that contract with in-tree machinery
(`net/httpe/benches/alloc_count.rs:57-105` `CountingAllocator`/`AllocStats`;
`net/sys/src/seccomp.rs` `SECCOMP_RET_LOG` audit counter; `perf_event_open` for cycles).
Tomorrow the verified compiler emits the same probes as a **domain pass**
(`22-PERFORMANCE.md:126-136`). One contract, both backends — that is the artifact-agnosticism.

The deepest move, made checkable here: **the same machine code that ships is the code measured.**
A perf win that needed an unverified fast path is a `verified-but-slow-shipped` /
`unverified-fast-path` bug (`22-PERFORMANCE.md:148-151`, `41 §E:302`). We make that a predicate
(§6), not a slogan — and every probe is itself **PF-6-gated**, so arming instrumentation does not
perturb the artifact (§2).

---

## 1. The four gate classes

The charge split gates into (a) gate-definition, (b) HW-free property assertions, (c) HW-execution
gates. In practice the **property** tier bifurcates, because `PF-6`/`PF-7` are *IR properties*
checkable with **no running artifact at all** — they are graph queries on the emitted IR/model.
So the kit names **four** classes:

| class | asserts | substrate | special HW? | runnable when |
|---|---|---|---|---|
| **StaticProperty** | a call-graph / dominance / reachability fact on the **emitted IR or model** | formal-model · engine IR | none | **NOW** (against `formal-model`) |
| **RuntimeProperty** | `alloc_count==0`, `syscalls==0`, instr-stream identity on a **running artifact** | running artifact | none | **NOW** (`current-net-rust` today) |
| **HwExecution** | line-rate pps, splice GB/s, GSO-2×, cycle/cache-miss budget, p99/p999 | real NIC/DPDK · PMU | **yes** (declared, env-gated) | where the HW exists; else **declared-skipped** |
| **Methodology** | the harness itself is configured (NUMA pin, busy-poll, ratchet wired) | the harness | none | NOW |

**StaticProperty is the deepest "by verified means" check and is real *today* against the
formal-model backend.** `PF-6` gate-dominance is "checkable as a domain pass — the probe body is
unreachable when the gate is false" (`22-PERFORMANCE.md:114-116`); `PF-7` is "assert there is no
synchronous `getaddrinfo`/blocking resolve reachable from the request hot path"
(`22-PERFORMANCE.md:117-124,161-163`). Both are reachability/dominance queries on the IR
(`StaticQuery` / `PerfSut::static_query`) — runnable against the `formal-model` backend and the
generated-engine IR **before any NIC exists**. Crucially, **zero-alloc and zero-syscall are
checkable BOTH ways**: statically (no alloc/syscall node reachable on the hot/bypass path) AND at
runtime (the counters read 0). A divergence between the two is itself a finding.

The charge's **"Counter" tier** (needs `perf_event` but any commodity core) is folded into
**HwExecution** as the lightest hardware requirement, `HwRequirement::Pmu` — it gates on
`CAP_PERFMON` and runs in much of CI, distinct from the real-NIC requirements
(`MultiQueueNic`/`Dpdk`/`AfXdp`). The distinction is preserved; the class count stays at four.

**EMPHASIS A (the charge's property-level assertions that need NO special HW) lands entirely in
StaticProperty + RuntimeProperty and is real today.** Do not wait for 100GbE HW to start gating —
the alloc/syscall/instruction-stream/symbol properties are measurable on a laptop and CI-ratcheted
immediately.

---

## 2. The instrumentation contract (EMPHASIS B — what the artifact must expose)

`trait ArtifactInstrumentation` is the ABI the **verified codegen emits an impl of** for every
hot-path artifact. The four probe families map directly to the per-packet budget
(`22-PERFORMANCE.md:14-17`):

- **Alloc** — `malloc ~100 ns ⇒ no per-packet allocation.` Backed by the *existing*
  `CountingAllocator`/`AllocStats` (`net/httpe/benches/alloc_count.rs:42-105`: `alloc_count`,
  `dealloc_count`, `total_bytes`, `peak_bytes`, `reset()`, `stats()`). The codegen binds the
  swappable global allocator at the seam already present for the mimalloc shim
  (`net/core/src/allocator.rs:28-98`): the ship build binds a pass-through, the measure build binds
  the counter — **same hot path**. The kit promotes `CountingAllocator` from a bench-local module
  (`net/httpe/benches/alloc_count.rs`) to `conformance-kit::perf::alloc`.
- **Cycle** — `few-hundred cycles/packet.` `rdtsc`/PMU fences the codegen emits around the sans-IO
  call boundary `(state, bytes) -> (state', events, out)` (`20-ARCHITECTURE.md:170`), exposed as
  `CycleReading { cycles, units }`. Needs PMU ⇒ `HwExecution{Pmu}`.
- **Syscall** — `syscall ~1 µs ⇒ no per-packet syscall.` Backed by the seccomp-BPF allow-list +
  `SECCOMP_RET_LOG` audit counter (`net/sys/src/seccomp.rs` — `SeccompMode::Log`): on the
  kernel-bypass path the audit counter must read **0 amortized**. For an out-of-process subject an
  `strace -fc` wrapper is the fallback counter.
- **InstrStream** — not a runtime counter; a basic-block trace digest the codegen emits, used for
  the `PF-6` instruction-stream-identity check (§5.3). For `current-net-rust` it is approximated by
  `objdump -d`/`nm` over a named hot-region symbol.

**The probes are themselves PF-6-gated.** `arm()` flips a probe gate that *dominates* every probe
point; disarmed, each probe is a relaxed-load + not-taken branch — so arming instrumentation does
**not** change the hot instruction stream. This dissolves the "measured a different binary than we
shipped" lie at the type level, grounding directly on the in-tree pattern
`if !tap.is_enabled() { return; }` (`net/httpe/src/cq/packet_tap.rs:71,710,737,763,794,825,855`).

**CR-6 rides along.** Every field of `InstrumentReadings` is `Option`: `None` ≠ `0`. A `None`
counter means *this backend did not report it*, so any gate keyed to that counter returns
`InstrumentAbsent` — never a silent zero-pass. `probe_support()` reports which probes the codegen
*actually emitted*. A backend that cannot count allocations cannot *pass* a zero-alloc gate by
reporting a convenient zero. This is the conformance non-vacuity gate
(`41 §F.1:336 diff-nonvacuity-gate`, CR-6) pushed down to counter granularity.

```rust
pub trait ArtifactInstrumentation {
    /// Identity of the verified build that emitted this artifact; matches the
    /// HotPathDigest manifest and is what unit-5's provenance firewall checks.
    fn build_id(&self) -> BuildId;
    /// CR-6 non-vacuity: which probes the codegen ACTUALLY emitted. Not-emitted == Absent.
    fn probe_support(&self) -> ProbeSupport;
    /// Arm probes for the next measured region; the guard disarms on drop.
    /// Arming flips the (PF-6-dominated) probe gate; the hot stream is unchanged.
    fn arm(&self, probes: ProbeMask) -> ProbeGuard<'_>;
    /// Snapshot armed counters. Defined for all artifacts; unarmed/unsupported fields read None.
    fn read(&self) -> InstrumentReadings;
    /// The signed hot-path symbol manifest (perf-by-verified-means). None for hand-written backends.
    fn hot_path_digest(&self) -> Option<HotPathDigest>;
}
```

---

## 3. The artifact-agnostic seam — reuse the correctness vectors

A perf gate does **not** invent inputs. It reuses the spine: the same content-addressed `Vector`
(`UnitId`, `Input`, `Spec`) that feeds the correctness diff feeds the perf budget. The perf adapter
extends `SutAdapter`:

```rust
pub trait PerfSut: SutAdapter {
    /// CR-6 perf non-vacuity: which instruments this backend exposes for this unit.
    fn instruments(&self, unit: UnitId) -> ProbeSupport;
    /// Run under measurement. Returns the FUNCTIONAL Observation (still diffed — a fast
    /// wrong answer is NOT a pass) PLUS the instrument readings + env provenance.
    fn measure(&self, unit: UnitId, run: &PerfRun) -> MeasuredObservation;
    /// Static (IR/model) query for StaticProperty gates — no input run needed.
    fn static_query(&self, unit: UnitId, q: StaticQuery) -> StaticAnswer;
}
```

`measure()` drives the normal `decode_region`/`run_machine` under a reset/snapshot bracket
(mirroring the in-tree `measure()` warmup→reset→stats discipline at
`net/httpe/benches/http_alloc.rs:47-63`), but — unlike a naive "discard the value" decorator — it
**keeps the functional output**: `MeasuredObservation` embeds the spine's `Observation`, which the
three-way runner still diffs. A fast wrong answer is `GateOutcome::WrongAnswer`, a hard fail. **Perf
cannot launder a correctness regression.** Because the protocol core is sans-IO
(`20-ARCHITECTURE.md:170`), the metered drive is just the normal call under a bracket; the arena
seam (`net/httpe/src/parsed_request.rs` — `ParsedRequest` = flat byte arena, header values borrowed
via `(off, len)`, zero `String` allocs) is what makes the zero-alloc gate *meaningful*: a region
decode should add **0** to `alloc_count` after warmup, exactly as the in-tree
`parse_accept_encoding` assertion does.

A thin `MeteredAdapter<A: PerfSut>` decorator is the canonical impl of `measure()` for any backend
that is both a `SutAdapter` and an `ArtifactInstrumentation`.

### Per-backend reality (the honest part — perf is NOT N-way)

| backend | StaticProperty | RuntimeProperty | HwExecution | verified-means |
|---|---|---|---|---|
| `current-net-rust` | partial (symbol-graph approx) | **Supported** (alloc/syscall/instr-stream) | Skipped unless HW/PMU | **InstrumentAbsent** (no verified build to match yet) |
| `external-oracle` (CR-3, subprocess) | Absent (not linked) | **Absent** (can't instrument its allocator op-granular) | end-to-end throughput only | Absent |
| `formal-model` (HOL4/CakeML) | **Supported** (IR is the substrate) | Absent (pure fn, no machine code) | Absent | defines *which* ops are hot |
| `generated-engine` | **Supported** | Supported (compiler emits probes) | Supported on HW | **Supported** (manifest emitted by same compiler) |

This is why perf is **not N-way**: conformance asks "do all backends produce the same bytes?";
perf asks "does **this one** artifact meet **its** budget?" The observable is **backend-shaped**
even though the input is shared. The `external-oracle` is out-of-process (CR-3, `10-DECISIONS.md`,
`41 §F.1`: *read via subprocess, never linked*) so it cannot be co-measured for allocs/cycles — it
serves only as a **baseline number** for `PF-5` beat-or-match ratio gates (vs `moka`/`governor`/
`h2`), via `BaselineRef`, never an `Observation` diff. The `formal-model` is a pure extracted
function with no machine-code identity, but it is *exactly* the right substrate for StaticProperty
gates. The "one vector, all backends" thesis holds for **inputs**; the perf **observable** is
per-backend. The runner counts only genuine `Met`; `HwUnavailable`/`InstrumentAbsent` are surfaced,
never laundered.

---

## 4. The five outcomes (CR-6 + honest env-skip + anti-launder)

`GateOutcome` extends the conformance runner's `{three-way-agree, divergence, oracle-absent}`
classifier (`41 §F.1:336`):

```rust
pub enum GateOutcome {
    Met          { readings: InstrumentReadings, margin: f64 },
    Missed       { readings: InstrumentReadings, budget: Budget, by: f64 },
    InstrumentAbsent { instrument: InstrumentKind, reason: String },        // CR-6: NOT a pass
    HwUnavailable    { requirement: HwRequirement, declared_skip: SkipTicket }, // recorded, never faked
    WrongAnswer      { divergence: String },                                // fast-but-wrong = hard fail
}
```

- **Met / Missed** — genuine measurement vs budget.
- **InstrumentAbsent** — the backend cannot read this probe at all (the cycle/syscall probe on
  `formal-model`; the `HotPathDigest` on `current-net-rust`). **Never a pass.**
- **HwUnavailable** — a `HwExecution` gate with no NIC/PMU in normal CI: recorded with a
  `SkipTicket` (`reason`, `required_env`, `must_run_in`, `waiver_expiry`). **Declared-skipped,
  surfaced in the report, never counted as a pass.** Faking an `HwUnavailable` gate as `Met` —
  i.e. an HW-`Met` with no `EnvProvenance` — is a **build failure**, the perf analogue of laundered
  vacuity (`22-PERFORMANCE.md:148-151`: a perf win on an unverified path is not a pass).
- **WrongAnswer** — fast but functionally diverged. Hard fail. (Welds perf to the correctness
  spine; perf can never trade correctness for speed.)

The distinction between `InstrumentAbsent` and `HwUnavailable` is load-bearing: without a separate
HW-skip outcome, the runner would launder "no 100GbE in CI" into green.

---

## 5. The property gates that are REAL NOW (StaticProperty + RuntimeProperty)

### 5.1 Zero-alloc steady-state — `Budget::AbsoluteCeiling{ Alloc, 0 }` (RuntimeProperty)
Canonical, exists today. Warmup K iters (lazy init), `reset()`, measure window, assert
`alloc_count == 0` (`Aggregate::SteadyStateMax`). Ratcheted: the budget file records the baseline;
any regression `> 0` is a **hard CI fail** (`41 §E.1` `zero_per_packet_alloc_datapath` /
`perf-zero-alloc-steady-state`; `§E.5 ci_alloc_ratchet_methodology`). Covers
`parse_path_throughput_6_5M_rps`'s 0-heap clause (`41 §E.4`, the httpz 6.5M-req/s bar) and
`qpack`-arena zero-copy decode. **Also expressible statically:**
`StaticQuery::AllocNodesReachableOnHotPath ⇒ none`.

### 5.2 Zero-syscall on bypass — `Budget::AbsoluteCeiling{ Syscall, 0 }` (RuntimeProperty)
Amortized syscalls/op `== 0` on the kernel-bypass path (`41 §E.1`
`zero_per_packet_syscall_kernel_bypass`). seccomp `SECCOMP_RET_LOG` counter
(`net/sys/src/seccomp.rs`) or `strace -fc` for out-of-process subjects. Static twin:
`StaticQuery::SyscallNodesReachableOnBypassPath ⇒ none`.

### 5.3 Instruction-stream identity (PF-6) — `Budget::InstrStreamIdentity{ region, ObservabilityCompiledOut }`
The observability gate must be **provably free when off** (`22-PERFORMANCE.md:107-116`;
`41 §E.3 observability_disabled_same_instruction_stream`): the disabled tap path must be the *same
instructions* as a build with observability compiled out. HW-free, in CI: build the hot region
twice (feature `tap` enabled-but-runtime-disabled vs compiled-out), `objdump -d` the named region
symbol, and assert the streams differ by **at most** a relaxed atomic load + a not-taken branch.
Grounds directly on the in-tree pattern `if !tap.is_enabled() { return; }`
(`net/httpe/src/cq/packet_tap.rs:71,710,737,763,794,825,855,877`): the gate asserts that shape
dominates every probe and the disabled body emits nothing more. Static twin (engine IR):
`StaticQuery::ObservabilityGateDominatesProbe` — the `PF-6` "domain pass" (`22-PERFORMANCE.md:114`).

### 5.4 Symbol-absent (PF-7, PF-3) — `Budget::SymbolAbsent{ region, forbidden }`
Static call-graph reachability over the hot region: `getaddrinfo`/any blocking resolve MUST be
unreachable from the request path (`22-PERFORMANCE.md:117-124`; `41 §E.3
no_getaddrinfo_on_proxy_hot_path`; ledger row `40-LEDGER:171`, `PF-7: no getaddrinfo on hot path`);
an unverified-ChaCha symbol MUST be unreachable from the WireGuard datapath
(`22-PERFORMANCE.md:79-86`, `PF-3 wireguard_reject_unverified_crypto_path`). HW-free linker/
symbol-graph check. Static twin: `StaticQuery::SyncResolveReachableFromReactor ⇒ none`.

### 5.5 Component-budget-not-just-aggregate (structural)
Gates carry `lever: PfLever` (`PF-1…PF-7` or `Substrate`); the runner asserts **each** PF gate
passes. There is no aggregate roll-up that can hide a regressed component
(`22-PERFORMANCE.md:152`, `41 §E:267 component_budgets_met_not_just_aggregate`).

---

## 6. Perf by verified means — `HotPathDigest` + `SymbolHashMatch`

The deepest gate (`22-PERFORMANCE.md:148-151`; `41 §E.4 perf_by_verified_means_same_artifact`):
the shipped hot-path code **is** the proven artifact. `HotPathDigest` is the manifest the
**verified build signs**: hot-path `SymbolName -> CodeHash` (over machine code) + a `manifest_hash`.
The gate `Budget::SymbolHashMatch{ region, manifest }`:

1. symbolize the hot instruction sample taken during `measure()`;
2. assert executed-hot-symbols ⊆ manifest;
3. assert each executed symbol's runtime code-hash `==` its manifest hash;
4. assert no `forbidden` (unverified-fast-path) symbol is in the region link set.

An unverified fast path shows up as a symbol **not in the manifest** in the hot sample ⇒
`unverified-fast-path` hard fail. Unit 5's `oracle-provenance-firewall` (`41 §F.1`) already gates
the verified-build set; this reuses `HotPathDigest.build_id` to bind the **measured** artifact to a
**proven** build. This is HW-free but **dormant for `current-net-rust`** — there is no verified
build to hash-match until roadmap R1.1 emits the first artifact (the engine is greenfield). So it
reports `InstrumentAbsent` on the baseline today and `Met` once the generated-engine exists.
**Designed now, runnable later — flagged, not faked, never green-by-omission.**

```rust
pub struct BuildId(pub ContentHash);
pub struct SymbolName(pub String);
pub struct CodeHash(pub ContentHash);
pub struct HotPathDigest {
    pub build_id: BuildId,
    pub symbols: std::collections::BTreeMap<SymbolName, CodeHash>, // hot-path symbol -> code hash
    pub manifest_hash: ContentHash,                                // signed by the verified build
}
```

---

## 7. The gate model (env-independent, designable NOW)

A `PerfGate` separates the **env-independent budget** (the number) from the **env-dependent
reading** (the measurement). `Budget` variants cover every shape in `41 §E`:

```rust
pub struct GateId(pub String);                  // e.g. "zero_per_packet_alloc_datapath"
pub enum PfLever { Substrate, Pf1, Pf2, Pf3, Pf4, Pf5, Pf6, Pf7 }
pub enum GateClass { StaticProperty, RuntimeProperty, HwExecution, Methodology }

pub struct PerfGate {
    pub id: GateId,
    pub lever: PfLever,
    pub class: GateClass,
    pub ledger_row: LedgerKey,                   // 40-LEDGER row (PF-* / device-axiom / machine)
    pub suite_case: CaseKey,                      // 41 §E case
    pub budget: Budget,
    pub measurement: MeasurementContract,
    pub acceptance: GateAcceptance,
    pub by_verified_means: Option<HotPathDigest>, // §6: bind measured artifact to a proven build
}

pub enum Budget {
    AbsoluteCeiling { metric: InstrumentKind, max: f64 },     // alloc_count==0; cycles<=300
    Floor           { metric: InstrumentKind, min: f64 },     // >=6.5M rps; >=250 settles/s
    Ratio           { metric: InstrumentKind, baseline: BaselineRef, relation: Relation }, // GSO 2x; beat-or-match
    LatencyCeil     { quantiles: Vec<(Quantile, core::time::Duration)> }, // p50/p99/p999 (41 §E.4)
    InstrStreamIdentity { region: HotRegionId, against: BuildVariant },   // PF-6 (§5.3)
    SymbolHashMatch { region: HotRegionId, manifest: VerifiedManifestRef }, // verified-means (§6)
    SymbolAbsent    { region: HotRegionId, forbidden: Vec<SymbolPattern> }, // PF-7/PF-3 (§5.4)
    StaticPredicate { query: StaticQuery },                  // PF-6 dominance / PF-7 reachability
}
pub enum Relation { GreaterEqualMultiple(f64), BeatOrMatch }
pub struct BaselineRef { pub name: String, pub source: BaselineSource } // moka/governor/h2/GSO-off
pub enum BaselineSource { OracleNumber, PriorBuildBaseline, ConfigOff }  // ExternalOracle never co-linked (CR-3)
pub enum BuildVariant { ObservabilityCompiledOut, GateDisabledAtRuntime }

pub struct MeasurementContract {
    pub instrument: InstrumentKind,
    pub aggregate: Aggregate,        // SteadyStateMax | PerUnitMean | P99 | P999 | Total | Identity
    pub window: Window,              // { warmup, iters } — mirrors http_alloc::measure
    pub repeats: u32,
    pub requires_hw: HwRequirement,  // None | Pmu | MultiQueueNic | Dpdk | AfXdp
    pub determinism: Determinism,    // Exact (allocs==0) | Statistical{ tolerance }
}
pub enum GateAcceptance { HardFailOnMiss, RatchetOnly, MustRejectUnverifiedPath }

pub enum StaticQuery {
    AllocNodesReachableOnHotPath,          // zero-alloc as an IR property
    SyscallNodesReachableOnBypassPath,     // zero-syscall as an IR property
    SyncResolveReachableFromReactor,       // PF-7 (22-PERFORMANCE.md:117-124)
    ObservabilityGateDominatesProbe,       // PF-6 domain pass (22-PERFORMANCE.md:114-116)
    InstrStreamIdentityVsObsCompiledOut,   // PF-6 instruction-stream identity (22-PERFORMANCE.md:158-160)
}
pub enum StaticAnswer { Holds, Violated { witness: String }, NotExpressible { reason: String } }
```

### `InstrumentReadings` — the measurement channel (all-Option, CR-6)

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstrumentKind { Alloc, Cycle, Syscall, CacheMiss, BranchMiss, InstrStream, Throughput, Latency }
pub struct ProbeMask(pub u32);                          // bitset over InstrumentKind
pub struct ProbeSupport(pub Vec<(InstrumentKind, Support)>); // reuse the spine's Support
pub struct ProbeGuard<'a> { _armed: ProbeMask, _art: &'a dyn ArtifactInstrumentation }

#[derive(Clone, Default)]
pub struct InstrumentReadings {
    pub alloc:        Option<AllocReading>,    // CountingAllocator (alloc_count.rs:42-105)
    pub cycles:       Option<CycleReading>,    // rdtsc/PMU around the sans-IO call boundary
    pub syscalls:     Option<SyscallReading>,  // seccomp SECCOMP_RET_LOG counter
    pub cache_miss:   Option<u64>,             // perf_event PMU (HwExecution{Pmu})
    pub branch_miss:  Option<u64>,             // perf_event PMU (HwExecution{Pmu})
    pub instr_stream: Option<InstrStreamHash>, // basic-block trace digest (PF-6 identity)
    pub throughput:   Option<Throughput>,      // pps / req-s / GB-s (HW load gen)
    pub latency:      Option<LatencyHist>,     // p50/p99/p999
}
#[derive(Clone, Copy)] pub struct AllocReading   { pub alloc_count: u64, pub dealloc_count: u64, pub total_bytes: u64, pub peak_bytes: u64 }
#[derive(Clone, Copy)] pub struct CycleReading   { pub cycles: u64, pub units: u64 } // units = packets/reqs in window
#[derive(Clone, Copy)] pub struct SyscallReading { pub count: u64, pub units: u64 }
#[derive(Clone, Copy)] pub struct Throughput     { pub value: f64, pub unit: ThroughputUnit }
#[derive(Clone, Copy)] pub enum   ThroughputUnit { Pps, ReqPerSec, GiBPerSec, LookupsPerSec, FramesPerSec, DecisionsPerSec }
#[derive(Clone)]       pub struct LatencyHist    { pub p50: f64, pub p99: f64, pub p999: f64 }
#[derive(Clone)]       pub struct InstrStreamHash(pub ContentHash);

pub struct PerfRun { pub input: Input, pub warmup: u32, pub iters: u32, pub concurrency: u32, pub probes: ProbeMask }
pub struct MeasuredObservation { pub observation: Observation, pub readings: InstrumentReadings, pub env: EnvProvenance, pub digest: Option<HotPathDigest> }
pub struct EnvProvenance { pub host_tag: String, pub nic: Option<String>, pub pmu: bool, pub numa_pinned: bool, pub busy_poll: bool, pub captured_at: u64 }
pub struct SkipTicket { pub reason: String, pub required_env: String, pub must_run_in: String, pub waiver_expiry: Option<u64> }
pub enum HwRequirement { None, Pmu, MultiQueueNic, Dpdk, AfXdp }
```

---

## 8. The budget file (content-addressed, CI-ratcheted)

Per-unit `perf-budgets/<unit>.toml` is the single source of budgets, content-addressable like the
corpus. It generalizes the **already-shipping** JSON alloc-baseline ratchet
(`net/httpe/benches/http_alloc.rs:14-22` JSON-line format; `41 §E.5 ci_alloc_ratchet_methodology`)
to **every** instrument — so the ratchet tooling is a continuation, not a rewrite.

```toml
schema = "dreggnet.perf-gate/1"
unit   = "h1-request-parse"

[[gate]]
id         = "zero_per_packet_alloc_datapath"
suite_case = "E.1/zero_per_packet_alloc_datapath"   # 41 §E key
ledger_row = "A.1"                                  # 40-LEDGER key
lever      = "Substrate"
class      = "RuntimeProperty"
budget     = { kind = "absolute_ceiling", metric = "alloc", max = 0 }
measurement = { instrument = "alloc", aggregate = "steady_state_max",
                window = { warmup = 100, iters = 10000 }, determinism = "exact",
                requires_hw = "none" }
acceptance = "hard_fail_on_miss"

[gate.ratchet]
number          = 0            # CI fails if measured exceeds this past the ratchet direction
rule            = "monotone_down"   # ceilings only tighten; floors "monotone_up"; identity "pinned"
baseline_hash   = ""          # pinned baseline this number was set against
recorded_at     = "2026-06-30"
recorded_build  = "<git-sha>"
env_tag         = ""          # property tier: env-independent; HwExecution: cpu/nic/kernel fingerprint
```

```rust
#[derive(serde::Serialize, serde::Deserialize)]
pub struct BudgetFile { pub schema: u32, pub unit: String, pub gates: Vec<GateBudgetEntry> }
#[derive(serde::Serialize, serde::Deserialize)]
pub struct GateBudgetEntry {
    pub gate: String, pub ledger_row: String, pub suite_case: String, pub class: String,
    pub number: f64, pub instrument: String,
    pub baseline_hash: Option<String>,    // pinned baseline this number was set against
    pub ratchet: Ratchet,
    pub env_tag: Option<String>,          // HwExecution: where it was last genuinely Met
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum Ratchet { MonotoneDown, MonotoneUp, Pinned } // ceiling tightens / floor rises / identity
```

**Ratchet semantics:** `AbsoluteCeiling`/`LatencyCeil` ⇒ `MonotoneDown` (move only in the improving
direction); `Floor`/`Ratio` ⇒ `MonotoneUp`; `InstrStreamIdentity`/`SymbolHashMatch` ⇒ `Pinned`. A
measurement worse than the recorded number beyond declared slack is a **hard fail**. **HwExecution**
gates additionally record `env_tag`/`EnvProvenance` (cpu/nic/kernel) because the measured number is
silicon-relative and cannot be content-addressed to a single golden — the budget is a **floor plus
a recorded env-fingerprint**, the one place perf breaks the clean content-addressing the spine
assumes.

---

## 9. Keying & coverage (every non-OOS perf row owns ≥1 gate)

Each `PerfGate` carries `(lever: PfLever, ledger_row: LedgerKey, suite_case: CaseKey,
class: GateClass)` — the same keel as the conformance spine. The `41 §F.2
ledger-keying-coverage-meta` extends: every `PF`-named `40-LEDGER` row owns ≥1 `PerfGate`, and a
hot-path row with zero gates is flagged. Concretely:

- `40-LEDGER:138` eBPF/AF_XDP CID-steering (`PF-4`), `:140` GSO/GRO/ECN/pktinfo (`PF-2`), `:141`
  UDP send-side fast paths (`PF-2`) → `HwExecution` gates;
- `40-LEDGER:166,168` deep packet tap / DNS tap (`PF-6`, marked **GAP ⚠ info-leak if gate
  unproven**) → the `StaticProperty` gate-dominance pass **is** the proof (§5.3);
- `40-LEDGER:171` CQ DNS resolver (`PF-7: no getaddrinfo on hot path`) → `SymbolAbsent` (§5.4).

The 71-strong `performance` NEW-authoring backlog (`41 §E:442-470`, G.4) is the gate inventory this
format populates. `StaticProperty` gates discharge the rows the running-artifact gates cannot reach
yet — letting unit 5 prove every non-OOS perf row has empirical coverage **before the HW lab runs**.
An artifact is "done" only when its perf gate is **met by verified means** (`41 §H:498-514`): both
the CI static/runtime green **and** the HW-lab green, tracked by unit 5's coverage-meta.

---

## 10. The runner & what a later agent builds

```rust
pub struct GateRegistry { pub gates: std::collections::BTreeMap<String, PerfGate> }
impl GateRegistry {
    pub fn run_gate(&self, gate: &GateId, sut: &dyn PerfSut, unit: UnitId, run: &PerfRun) -> GateOutcome;
    pub fn check_verified_means(&self, sut: &dyn PerfSut, unit: UnitId) -> GateOutcome;
}
```

A later merge agent authors `net/conformance-kit::perf` from these signatures: the
`ArtifactInstrumentation` trait + `InstrumentReadings`/`ProbeSupport`; the `PerfSut` extension +
`MeteredAdapter`; the `PerfGate`/`Budget`/`GateClass`/`MeasurementContract`/`HotPathDigest` model;
the `perf-budgets/*.toml` loader + ratchet checker; the five-way `GateOutcome` classifier; and the
`objdump`/`nm` region-extractor for §5.3/§5.4/§6. The RuntimeProperty tier wires to the existing
`CountingAllocator` immediately; `HwExecution` gates gate on `HwRequirement` and emit `SkipTicket`s
where the HW is absent. Unit 5 (the unified runner, `41 §F`) consumes `GateOutcome` for its
classification, runs the `BudgetFile` ratchet per-PR, and checks each `HotPathDigest.build_id`
against the verified-build set the provenance-firewall already gates.

---

## Seams

### Provides (to `net/conformance-kit::perf`, for a later author)
1. `trait ArtifactInstrumentation` — the compiler-emitted instrumentation contract (`build_id` ·
   `probe_support` · `arm`/`read` · `hot_path_digest`); every probe PF-6-gated so the measured
   artifact == the shipped artifact.
2. `InstrumentReadings` (all-`Option`, CR-6) + `AllocReading`/`CycleReading`/`SyscallReading`/
   `Throughput`/`LatencyHist`/`InstrStreamHash`; `InstrumentKind`/`ProbeMask`/`ProbeSupport`/
   `ProbeGuard`.
3. `trait PerfSut: SutAdapter` — `instruments()` · `measure() -> MeasuredObservation` (functional
   `Observation` retained + diffed) · `static_query() -> StaticAnswer`; `PerfRun`,
   `MeasuredObservation`, `EnvProvenance`.
4. The gate model: `PerfGate`, `Budget` (8 variants), `GateClass` (4 classes), `PfLever`,
   `MeasurementContract`, `GateAcceptance`, `StaticQuery`/`StaticAnswer`, `BaselineRef`,
   `HwRequirement`, `SkipTicket`.
5. `GateOutcome` (5-way: `Met` | `Missed` | `InstrumentAbsent` | `HwUnavailable` | `WrongAnswer`)
   + `GateRegistry`/`run_gate`/`check_verified_means`.
6. `HotPathDigest` (`BuildId` · `SymbolName -> CodeHash` · `manifest_hash`) for perf-by-verified-means.
7. The `perf-budgets/<unit>.toml` schema + `BudgetFile`/`GateBudgetEntry`/`Ratchet` serde types +
   ratchet semantics.
8. `MeteredAdapter<A: PerfSut>` decorator.

### Consumes (from the fixed spine, units 1–3, and real code)
- **Spine:** `SutAdapter`, `BackendId`, `UnitId`, `Primitive`, `Support` (`Supported | Absent`),
  `Observation`, `Vector`, `Input`, `Spec`, `Expectation`, `Acceptance`, `Kind::Perf`, `LedgerKey`,
  `CaseKey`, `ContentHash`. `PerfSut` **extends** `SutAdapter`; `MeasuredObservation` **embeds**
  `Observation` (functional diff reused, not reimplemented).
- **Real code:** `CountingAllocator`/`AllocStats` (`net/httpe/benches/alloc_count.rs:42-105`) backs
  the `Alloc` probe; the `measure()` warmup→reset→stats→JSON pattern
  (`net/httpe/benches/http_alloc.rs:47-63`) is the RuntimeProperty window + ratchet seed; the
  seccomp `SECCOMP_RET_LOG` counter (`net/sys/src/seccomp.rs`) backs the `Syscall` probe; the
  global-allocator shim seam (`net/core/src/allocator.rs:28-98`) is where codegen binds the
  swappable counting allocator; `if !tap.is_enabled() { return; }`
  (`net/httpe/src/cq/packet_tap.rs:71,710…877`) is the PF-6 probe-gate shape; `ParsedRequest`
  (`net/httpe/src/parsed_request.rs`) makes the zero-alloc gate meaningful.
- **Other units:** Unit 1 (corpus) — the content-addressed `Vector` is the single input source.
  Unit 5 (runner/CI/coverage-meta/provenance-firewall, `41 §F`) — consumes `GateOutcome`, runs the
  `BudgetFile` ratchet, checks `HotPathDigest.build_id` against the verified-build set.

### Tensions with the fixed spine
1. **`Observation` has no cost channel.** It carries `arena_view`/`state_trace`/`consumed` — all
   correctness fields. Perf measurement needs a side-band; I add `InstrumentReadings` and wrap both
   in `MeasuredObservation { observation, readings, env }` rather than widening `Observation`. A
   backend must implement **both** `SutAdapter` and `ArtifactInstrumentation` to be perf-eligible —
   the spine's single-trait assumption does not cover perf. *The spine should acknowledge
   measurement as a first-class observation channel.*
2. **`Support` is binary; perf has a third honest outcome.** `supports(unit) -> Supported | Absent`
   cannot express *measurable-in-principle-but-no-HW-here*. The kit carries this as the distinct
   `GateOutcome::HwUnavailable{ SkipTicket }`; without it the runner would launder an HW skip as a
   pass. A real extension to the spine's vocabulary.
3. **`Expectation` has no budget arm.** It is `Golden | NwayAgree | MustReject`; perf is
   budget-vs-measured, not agreement-defined. I extend it with `Expectation::MeetsGate { gate:
   GateId }` and push the number into a side `GateRegistry`/`BudgetFile` so the corpus `Vector`
   stays uniform. If unit 5 wants `Expectation` closed, the budget predicate must live somewhere —
   I chose a content-addressed registry; an honest divergence from a self-contained `Expectation`.
4. **Perf is structurally NOT N-way.** The input is shared but the observable is backend-shaped:
   `external-oracle` is out-of-process (CR-3) ⇒ `InstrumentAbsent` for alloc/syscall; `formal-model`
   is a pure function ⇒ `InstrumentAbsent` for cycle/instr-stream/symbol but the *substrate* for
   StaticProperty. The spine's symmetric multi-backend agreement model does not fit perf; I report
   it rather than force it. `BaselineRef` is a reference **value**, not an `Observation` diff.
5. **`perf-by-verified-means` is unrunnable for the only backend that exists today.** There is no
   verified build to hash-match until R1.1 emits the first artifact, so `SymbolHashMatch` reports
   `InstrumentAbsent` on `current-net-rust` — designed, dormant, honestly flagged, never
   green-by-omission.
6. **HW-tier gates cannot be content-addressed to a deterministic golden.** The measured number is
   silicon-relative; `Vector.id` hashes input+spec but not the environment. The budget must be a
   floor plus a recorded `EnvProvenance`/`env_tag`, breaking the clean content-addressing the spine
   assumes for the HwExecution class only.
7. **`Input` is single-shot; perf needs a warmed, looped, possibly-concurrent workload.** I wrap it
   as `PerfRun { input, warmup, iters, concurrency, probes }` (and optionally `Input::Workload`). If
   units 1–3 keep `Input` single-shot, the perf workload notion lives in `PerfRun` — a duplicated
   "the input" across the two layers.
8. **StaticProperty gates have no input.** They are per-**artifact** IR queries
   (`PerfSut::static_query`), a shape the per-input `SutAdapter::run_*` surface does not natively
   express. Resolved by the separate `static_query` method, but it is a genuinely different adapter
   shape from the spine's `(input) -> Observation`.

( ⌐■_■ ) the gate measures the artifact that ships — or it isn't a gate.
