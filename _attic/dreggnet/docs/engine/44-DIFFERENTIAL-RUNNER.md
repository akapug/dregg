# 44 — THE N-WAY DIFFERENTIAL RUNNER

> Unit 3 of `net/conformance-kit`. Takes one `Vector` + a set of `SutAdapter`
> backends, runs the vector against each, lowers each result to a per-primitive
> **projection**, and diffs the projections **field by field** — naming the exact
> diverging field, the outlier backend, and a minimal reproducer. It is the
> generalization of the doc's "three-way runner" (`41-TEST-AND-PERF-SUITE.md:324-338`,
> §F.1) from `{engine, oracle, model}` to N backends
> `{CurrentNet, ExternalOracle, FormalModel, GeneratedEngine}` (the spine's
> `BackendId`), and it makes the CR-6 non-vacuity gate (`41:336`, `40-LEDGER:9-12`)
> load-bearing rather than aspirational.
>
> `CurrentNet` is just "oracle backend #1." The runner has **no privileged
> backend** except whichever the run policy names `required`. `GeneratedEngine`
> — the real future SUT (`20-ARCHITECTURE.md:170`, the sans-IO signature that *is*
> the universal adapter surface) — plugs in for free as one more `&dyn SutAdapter`
> in the backend set, with zero new wiring.

---

## 0. What this runner is (and is not)

It is the **comparison engine**, not the corpus (Unit 1) and not the adapters
(Unit 2). It consumes the fixed spine — `SutAdapter`, `Observation`, `Vector`,
`Expectation`, `Support` — and produces a `VectorReport` per vector and a
`RunReport` (folding a `NonVacuityLedger`) per corpus run.

Two non-negotiable design moves anchor everything below:

1. **The runner never diffs two `Observation`s as blobs.** It lowers each
   admitted witness to a per-primitive `Projection` (the equivalence-relevant
   normal form), then diffs projections cell-by-cell keyed by `FieldPath`. A
   divergence therefore *is* a `FieldPath` by construction — "exactly which field"
   is structural, not a post-hoc heuristic. This is forced by the codebase: a
   parsed request's arena is physically different across protocols for the *same
   logical request* — H1's arena **is** the wire buffer (offsets via pointer
   arithmetic), HPACK/QPACK **copy** decoded values into a fresh arena, with a
   high-bit sidecar union at `SIDECAR_OFFSET_BASE = 0x8000_0000`
   (`net/httpe/src/parsed_request.rs:6-12,685-706`). Raw-arena equality would be a
   false divergence on every cross-protocol vector; *resolved* `(name,value,body)`
   equality is the real relation.

2. **A witness must be well-formed BEFORE it can agree.** Every Present witness is
   gated through its own well-formedness predicate (the wf-gate, §3) before it is
   admitted as a comparison participant. A backend can return
   `Observation::Produced` that is internally malformed and still happen to
   field-match another backend; counting that as agreement is exactly the "agree on
   garbage" laundering CR-6 forbids. The spine's `Observation` has no `Malformed`
   state, so this is a runner-side invariant (see Seams/tensions).

---

## 1. The pipeline of one vector

```
run_vector(vector, backends) -> VectorReport
  0. ROUTE      Kind::Perf  -> PerfGate (§5), bypasses the diff engine entirely
                otherwise    -> the diff pipeline below
  1. PROBE      each backend: supports(vector.unit) -> Support       (CR-6 gate, 41:336)
  2. OBSERVE    each Supported backend, dispatched by vector.primitive:
                   Region -> decode_region   Machine -> run_machine
                   Linear -> run_linear      Shared  -> run_shared
                -> Observation (Produced | Absent)
  3. ADMIT      Observation -> Presence:
                   Absent{r}                       -> Presence::Absent
                   Produced & wf-gate fails (§3)   -> Presence::Malformed{violation}
                   Produced & wf-gate passes       -> Presence::Present(Projection)
  4. PROJECT    each Present projection -> Vec<(FieldPath, Cell)>     (per-primitive)
  5. ALIGN      group cells by FieldPath -> BTreeMap<FieldPath, BTreeMap<BackendId,Cell>>
  6. CLASSIFY   per field (Comparator + applicability + Expectation), then roll up
                to a total-partition Verdict (§4)
  7. ROLL UP    VectorReport + CoverageContribution + Severity
  8. ON FAIL    minimize each Divergence / RejectionEscaped (§6, if policy.shrink)
```

The runner is **backend-set-parametric** and **corpus-subset-parametric**: one
engine; CI varies only which adapters register and which vectors run (§7).

---

## 2. The per-primitive diff (what each `Projection` compares)

The `Projector` is primitive-specific. It first produces a wf-checked `Projection`
(§3), then `fields(&Projection)` flattens it into `(FieldPath, Cell)` pairs. Each
`FieldPath` carries a `FieldSpec { comparator, applicability }`.

### 2.1 region/view (`decode_region`)

Grounded in `parsed_request.rs` (flat `Bytes` arena + `(name_tag, off, len)`
triples, sidecar at `SIDECAR_OFFSET_BASE`) and `21-FORMAL-MODEL.md:19-27` (Rank 1,
`wf_parsed_request`). Projected cells:

| FieldPath | Comparator | applicability |
|---|---|---|
| `ErrorClass` | `ErrorClassEq` (kit taxonomy, §4.1) | All |
| `Status` | `StatusExact` | All |
| `Consumed` | `Exact` — **`Cell::Absent` when tri-state is `Incomplete`** (no consumed exists) | All |
| `Body` | `BytesExact` | All |
| `Header(name)` | `HeaderMultiset` (name-canonicalized via `resolve_bytes`, dup-preserving) | All — **incl. ExternalOracle** |
| `ArenaBytes` | `BytesExact` | `ZeroCopyLayout` = `{CurrentNet, FormalModel, GeneratedEngine}` |
| `ArenaTriple{tag}` | `Exact` over `(off,len)` | `ZeroCopyLayout` |
| `Sidecar{tag}` | `BytesExact` | `ZeroCopyLayout` |

The **semantic** `Header`/`Status`/`Body`/`ErrorClass` cells bind *all* backends,
so the out-of-process Elide oracle (CR-3) confirms the *meaning*. The **byte-layout**
`ArenaBytes`/`ArenaTriple`/`Sidecar` cells bind only the three layout-true backends,
so the oracle's different internal representation is never a spurious divergence.
This is how `wf_parsed_request` (every `off+len ≤ arena.len()` or in-sidecar)
becomes a byte-exact differential among the layout-true backends while the oracle
still pins the resolved semantics.

### 2.2 machine (`run_machine`)

Grounded in the sans-IO `step : State × Input → State × Output*` (`20:170`) and
the tri-state parse step `Complete{body_offset} | Incomplete | Error`
(`21:29` Rank 2; the convention lives in `net/httpe/src/cq/response_parser.rs:41-48`
and `net/httpe/src/protocol/socks.rs:84-91`). Projected cells:

| FieldPath | Comparator | meaning |
|---|---|---|
| `TriState` | `Exact` | overall `Complete | Incomplete | Error` tag |
| `StateLabel{step}` | `Exact` (canonical state name) | the FSM state at trace step `step` |
| `Emitted{step}` | `BytesExact` | bytes emitted at step `step` |
| `EmittedTotal` | `BytesExact` | concatenated emitted bytes |
| `ErrorClass` | `ErrorClassEq` | terminal error class, if any |

The step index is the precision lever: backends "agree through step 4, diverge at
`StateLabel{step:5}`." The trace is compared **element-wise**, not as a string, so
a one-state divergence is one field, not a whole-trace blob.

### 2.3 linear (`run_linear`)

The X-4 exactly-once token discipline shared by `BufRingLease` / `PooledBuf` /
`DispatchDecision` (`21-FORMAL-MODEL.md:95-97`, `X-4`). One projected cell
`Discipline` (`Comparator::Exact` over `DisciplineVerdict`):

```
Clean
| DoubleRelease   { handle, first, second }
| UseAfterRelease { handle, released_at, used_at }
| Leak            { handle, acquired_at }
| UseWithoutAcquire { handle, used_at }
```

A divergence is one backend reporting `Clean` while another reports a violation;
the report names the violation kind, the handle, and the op indices. Because
linear is a **predicate** expectation (`MustReject`-shaped), the classifier holds
*every* Present backend to "exhibits the same discipline outcome" rather than
voting (§4.3).

### 2.4 shared (`run_shared`)

Iris logical-atomicity, loom/shuttle-shaped (`21:52-72` Ranks 5-7;
`41-SUITE:230-234` standing concurrency harnesses). The `Schedule` *is* the input,
so the run is deterministic given the seed — essential for non-flaky CI. Projected
cells (`Comparator::Predicate`):

| FieldPath | meaning |
|---|---|
| `Linearizable` | ∃ a valid linearization of the observed history |
| `InvariantHeld` | the object invariant held at every observed step |

Critically the runner does **not** byte-compare the `state_trace` here: two correct
backends may pick different valid linearization orders. Agreement is over the
*predicates* and over `observed ⊆ model_allowed` (the `OutcomeSet` the FormalModel
witness emits), never the concrete order (Seams/tension #1).

### 2.5 Field ordinal (which field is `primary`)

`FieldPath::ordinal()` imposes a total order used only to pick the `primary` named
field when several diverge at once. **`ErrorClass` and `Status` rank first**: an
accept-vs-reject disagreement is the most security-relevant divergence and should
headline the report. Layout/trace fields rank last. Every diverging field is
*reported*; the ordinal only decides the headline.

---

## 3. The wf-gate (CR-6 hardening — a witness must be well-formed to agree)

Before a `Produced` observation becomes a comparison participant, it is run through
its primitive's well-formedness predicate. Failure yields
`Presence::Malformed { violation }` — a **hard FAIL**, never an agreement
participant.

- **region** — `wf_parsed_request` (`21:23-24`, `X-2`): every `(off,len)` has
  `off+len ≤ arena.len()` OR is in-sidecar (`off ≥ SIDECAR_OFFSET_BASE`), and every
  resolved range is valid UTF-8. Fail →
  `ArenaRangeOutOfBounds{off,len,arena_len}` or `NonUtf8ArenaRange{off,len}`.
- **machine** — the tri-state trace is **monotone** (never regresses
  `Complete → Incomplete`) and `consumed` is non-decreasing and `≤ input.len()`.
  Fail → `TraceNonMonotone{step}` or `ConsumedExceedsInput{consumed,input_len}`.
- **linear** — the X-4 token is used at most once (the projection itself encodes
  this; a witness that internally double-counts is malformed, distinct from one
  that *reports* a `DoubleRelease` verdict). Fail → `TokenUsedTwice{handle}`.
- **shared** — `invariant_held` at every observed step. Fail → `InvariantBreach`.

The wf-gate is the closure on "backends agree on garbage": a malformed witness
cannot launder into coverage, even if its malformed bytes happen to match another
backend's malformed bytes.

---

## 4. Classification — a total partition, divergence NAMES the field

Admitted witnesses partition into `Present(Projection)` / `Absent` (from
`supports()==Absent` **or** `Observation::Absent`) / `Malformed`. The vector then
lands in **exactly one** `Verdict` bucket; `partition_is_total()` asserts the
buckets sum to `total` so no vector is silently dropped.

### 4.1 The ErrorClass taxonomy (a precision prerequisite)

Error-class divergence is meaningless across free text. The kit **owns** a
canonical `ErrorClass` enum (seeded by `net/httpe` `SmuggleViolation`,
`parsed_request.rs:27-46`, and `status_code()` near `:91`). Each adapter implements
`classify_error(native) -> ErrorClass`, mapping its native error into the shared
vocabulary. Only then does "backend X says `Smuggling(DuplicateContentLength)`,
backend Y says `Smuggling(ChunkedNotLast)`" become a *real* named divergence rather
than a vocabulary artifact, and only then can "both rejected" (`MustReject`) be
checked across heterogeneous backends.

### 4.2 Pre-checks (Red regardless of expectation)

1. Any `required` backend (default `{CurrentNet}`) not Present →
   `RequiredBackendAbsent { backend, reason }`. Can't even baseline.
2. Any witness `Malformed` → `Malformed { backend, violation }`.

### 4.3 Expectation dispatch

- **`Golden(g)`** — inject `g` as a synthetic immutable witness
  `BackendId::Reference`, then fall through to the equality diff (§4.4). A mismatch
  surfaces as a `Divergence` whose `Clustering::AgainstGolden` names the dissenting
  backends — golden mismatch and N-way divergence are *the same* code path, no
  voting against the golden.
- **`MustReject`** (almost all of `41-SUITE §C` security cases, plus the `linear`
  discipline checks) — a **predicate**, not equality: every Present witness must
  independently exhibit rejection (a rejecting `ErrorClass`/status, or a
  `DisciplineVerdict` violation for linear). Any *accepting* witness →
  `RejectionEscaped { accepting, minimal_repro }` — a hard security FAIL, never a
  divergence to be voted on. Security never tolerates "handled gracefully"
  (`41:36`).
- **`NwayAgree`** — pure equality diff over Present projections (§4.4).

### 4.4 The equality diff (the precision core)

For each `FieldPath` in ordinal order, partition the Present *applicable* witnesses
(per the field's `applicability` set) into equivalence groups by that field's
`Comparator`. Recall a `Cell::Absent` (e.g. `Consumed` under `Incomplete`) equals
**nothing**, including another `Absent`; field agreement requires ≥2 *present*
cells that match.

- **If any field has >1 group →** collect a `FieldDivergence { field, clustering,
  per_backend, minimal_repro }` for it. The vector verdict is
  `Divergence { primary = lowest-ordinal diverging field, fields = all of them,
  security }`. Each `FieldDivergence.clustering` is:
  - `Outlier { outlier, majority, majority_value }` — a clear majority agrees and a
    minority (often singleton) differs; the outlier backend is named.
  - `Schism { clusters }` — an even split (e.g. 2-2 among 4 backends) with no
    majority; both value-clusters and their backends are named. Honest precision
    ceiling: with exactly four backends a 2-2 split *has* no single outlier, so
    single-outlier identification degrades to cluster identification, but the
    diverging **field** is always named (Seams/tension #5).
  - `AgainstGolden { dissenting }` — under a `Golden` expectation, the backends
    differing from `Reference`.
- **Else (all applicable fields single-group) → quorum check.** If
  `present < policy.min_witnesses` (default 2) →
  `InsufficientWitnesses { present, required }` — **never** a pass, **never**
  counted as coverage. Otherwise → `Agree { witnesses }`,
  `counts_as_coverage = true`.

`InsufficientWitnesses` is the honest answer for a row whose only Present backend
today is `CurrentNet`: with `min_witnesses = 2` such a `NwayAgree` vector scores
**zero** coverage until the FormalModel and/or GeneratedEngine land. This must not
be "fixed" by lowering the quorum (Seams/tension #6).

---

## 5. Perf is not a diff (routed out)

`Kind::Perf` vectors never enter the equality engine: numbers differ by
construction, and `PF-5` demands `GeneratedEngine` **beat-or-match** a named
baseline (`41-SUITE:294`, the `PF-1…PF-7` levers), an inequality, not agreement.
The runner forwards `Kind::Perf` to a separate `PerfGate` evaluator whose
cross-backend relation is *per-backend threshold satisfaction* plus the beat-or-match
inequality. Its `PerfOutcome` joins the `VectorReport` as a parallel channel, never
a `Verdict`. (The spine's `Observation` models no latency/throughput/alloc-count —
flagged in Seams/tension #4.)

---

## 6. Divergence precision & minimal repro

A `FieldDivergence` (and a `RejectionEscaped`) carries an optional `MinimalRepro`,
produced by `Minimizer::shrink` when `policy.shrink` is set (on for nightly and for
fuzz-minted regressions; off in the fast per-PR lane to keep it cheap). `shrink` is
a ddmin loop over the per-primitive `Input` shrinker (reused from Unit 1) with the
invariant **"the shrunk input still diverges on THIS field"**:

- **region** — shrink the `Bytes` (drop headers/bytes): a 4 KB request diverging
  only on `content-length` collapses to the minimal header set reproducing it.
- **machine** — truncate the `EventSeq` at the first diverging step.
- **linear** — truncate the `ResourceOps` prefix at the diverging op.
- **shared** — the seeded `Schedule` is minimal-by-replay; shrink to the prefix of
  interleavings that still violates the predicate.

Multiple fields can diverge at once; each is an independent `FieldDivergence`,
independently minimized — "status agrees, content-length and body diverge" is two
precise findings, not one blob. Every `MinimalRepro` is a deterministic, replayable,
content-addressable artifact (region/machine/linear are pure functions of
`(input, spec)`; shared replays by `Schedule` seed) — so no nondeterministic flake
reaches CI.

---

## 7. The non-vacuity ledger (the CR-6 honesty surface)

`run_corpus` folds every `VectorReport` into a `NonVacuityLedger`. The accounting
makes "we tested N rows but M were oracle-absent" structurally impossible to hide
(`40-LEDGER:9-12`, `41:336,345-347`):

- **Coverage numerator = `genuine_agreements` ONLY.** `InsufficientWitnesses`,
  `Divergence`, `Malformed`, `RequiredBackendAbsent`, and `RejectionEscaped`
  contribute **zero**. `Absent` is partitioned out *before* the quorum is computed,
  so an oracle skip can never be laundered into a pass. A `Golden`-only run with one
  present backend is recorded but never credited as N-way coverage.
- **`absent_by_backend`** — total vectors each backend declined, globally.
- **`per_row: LedgerKey → RowAccounting`** — for each `40-LEDGER` row: `vectors`,
  `genuine_agreements`, and `present_by_backend` / `absent_by_backend`. This is the
  *printed line*: e.g. *"§A.1 h1-request-parse — 17 vectors; ExternalOracle present 17,
  FormalModel present 0 (model-absent), GeneratedEngine present 0 (not-built);
  genuine agreements 0."* A row that *looks* covered but whose oracle/model witnessed
  nothing is loud, not silent.
- **`coverage_gate(non_oos)`** — the `F.2 ledger-keying-coverage-meta`
  (`41:345-347`): `Fail { empty_rows, oracle_dark_rows }` if any non-OOS `40-LEDGER`
  row has `genuine_agreements == 0` (`empty_rows`), or if a row the oracle/model
  could *in principle* witness but didn't lacks an explicit waiver
  (`oracle_dark_rows`). OOS rows are excused via `policy.waived_rows`.

---

## 8. CI integration (`F.2`, `41-SUITE:341-347`)

`Severity` is computed per verdict; `ci_exit()` is non-zero iff any `Red` exists.

- **Per-PR (blocks on red).** `run_corpus` over the committed corpus against the
  registered backends (today `{CurrentNet}` + `ExternalOracle`/`FormalModel` where
  present; `GeneratedEngine` joins the moment it exists). `Red` =
  `{ Divergence, RequiredBackendAbsent, RejectionEscaped, Malformed }` **plus**
  `InsufficientWitnesses` for any vector that declared `NwayAgree` (you promised a
  differential and could not deliver one). A *non-required* `Absent` (ExternalOracle
  down, GeneratedEngine not yet built) is `Recorded`, **not** `Red` — it degrades
  coverage and shows in the ledger, but does not block a PR that did not touch that
  surface. A regressed *component* fails the gate even if the aggregate is green
  (`41:342`). The fast lane runs with `policy.shrink = false`.
- **Nightly.** Full `h2spec` / Autobahn / curl conformance, the continuous fuzz-net
  (`41:349-357`, §F.3) which mints new content-addressed vectors into the corpus
  (Unit 2) — those flow back through *this same runner*, now with
  `policy.shrink = true`, and any divergence's `MinimalRepro` is content-addressed
  and added to the corpus as a permanent regression vector — plus the perf benches
  via the `PerfGate`. Nightly divergences file issues / drop the nightly badge; they
  do not retro-block merged PRs.

---

## 9. Worked failure shape

`diff/h2-frames-hpack-flowctl` over `{CurrentNet, ExternalOracle, FormalModel}`, an
HPACK-decoded request. FormalModel projects `Consumed(41)`, the other two
`Consumed(39)`:

```
Verdict::Divergence {
  primary: FieldPath::Consumed,
  fields: [ FieldDivergence {
    field: Consumed,
    clustering: Outlier {
      outlier: FormalModel,
      majority: {CurrentNet, ExternalOracle},
      majority_value: digest("39"),
    },
    per_backend: { CurrentNet: Consumed(39), ExternalOracle: Consumed(39),
                   FormalModel: Consumed(41) },
    minimal_repro: Some(MinimalRepro { still_diverges_on: Consumed, shrink_steps: 12, .. }),
  } ],
  security: false,
}
severity: Red,  counts_as_coverage: false
```

The CI line reads: *"divergence on field `Consumed`: FormalModel=41 vs
{CurrentNet, ExternalOracle}=39"* — the diverging field **and** the dissenting backend
are both named, with a minimized reproducer attached.

---

## 10. Exact Rust signatures contributed to `net/conformance-kit`

```rust
// crate net/conformance-kit  ::  module `differential`
// Consumes the fixed spine: SutAdapter / Observation / Vector / Expectation /
// Support / BackendId / Primitive / Kind / Input / Spec / LedgerKey / CaseKey /
// UnitId / ContentHash / HeaderName / Event / Schedule / ResourceOp.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;

// ===================== the runner =====================
pub struct DiffRunner<'a> {
    backends:  Vec<&'a dyn SutAdapter>,
    projector: Box<dyn Projector>,
    minimizer: Box<dyn Minimizer>,
    perf_gate: Box<dyn PerfGate>,
    policy:    RunPolicy,
}
impl<'a> DiffRunner<'a> {
    pub fn new(
        backends: Vec<&'a dyn SutAdapter>,
        projector: Box<dyn Projector>,
        minimizer: Box<dyn Minimizer>,
        perf_gate: Box<dyn PerfGate>,
        policy: RunPolicy,
    ) -> Self;
    pub fn run_vector(&self, v: &Vector) -> VectorReport;     // one vector, all backends
    pub fn run_corpus(&self, vs: &[Vector]) -> RunReport;     // folds the NonVacuityLedger
}

pub struct RunPolicy {
    pub min_witnesses: usize,            // CR-6 quorum; default 2 for NwayAgree
    pub required:      BTreeSet<BackendId>, // backends that MUST be Present; default {CurrentNet}
    pub waived_rows:   BTreeSet<LedgerKey>, // OOS rows excused from the coverage gate
    pub shrink:        bool,             // minimize divergences (off in the fast PR lane)
}

// ===================== witness admission =====================
pub enum Presence {
    Present(Projection),
    Absent    { reason: String },                 // supports()==Absent OR Observation::Absent
    Malformed { violation: WfViolation },         // failed the wf-gate (§3)
}
pub struct WitnessSummary { pub backend: BackendId, pub presence: PresenceTag }
pub enum PresenceTag {                              // serializable summary (Projection elided)
    Present,
    Absent    { reason: String },
    Malformed { violation: WfViolation },
}
pub enum WfViolation {                              // 21-FORMAL X-2 / X-4 + wf_parsed_request
    ArenaRangeOutOfBounds { off: u32, len: u32, arena_len: usize },
    NonUtf8ArenaRange     { off: u32, len: u32 },
    TraceNonMonotone      { step: usize },
    ConsumedExceedsInput  { consumed: usize, input_len: usize },
    TokenUsedTwice        { handle: HandleId },
    InvariantBreach,
}

// ===================== per-primitive wf-checked normal form =====================
pub enum Projection { Region(RegionProj), Machine(MachineProj), Linear(LinearProj), Shared(SharedProj) }

pub struct RegionProj {
    pub status:      u16,
    pub error_class: Option<ErrorClass>,
    pub consumed:    ConsumedCell,                 // NotApplicable when tri-state is Incomplete
    pub headers:     CanonHeaders,                 // resolved name -> value(s), dup-preserving
    pub body:        Bytes,
    pub arena:       Option<ArenaLayout>,          // None for layout-opaque backends (oracle)
}
pub struct ArenaLayout {
    pub bytes:   Bytes,
    pub triples: Vec<(NameTag, u32, u32)>,         // (name_tag, off, len) — parsed_request.rs
    pub sidecar: Bytes,                            // values at off >= SIDECAR_OFFSET_BASE
}
pub enum ConsumedCell { Count(usize), NotApplicable }

pub struct MachineProj {
    pub trace:       Vec<StepTag>,                 // per-step tri-state
    pub emitted:     Bytes,
    pub events:      Vec<Event>,
    pub error_class: Option<ErrorClass>,
}
pub enum StepTag { Complete { consumed: usize }, Incomplete, Error }  // response_parser.rs:41-48

pub enum LinearProj  { Clean, Violation(DisciplineVerdict) }

pub struct SharedProj {
    pub linearizable:  bool,
    pub invariant_held: bool,
    pub observed:       OutcomeSet,
    pub model_allowed:  Option<OutcomeSet>,        // FormalModel emits the allowed set
}

// ===================== field & cell vocabulary =====================
pub enum FieldPath {
    // region/view
    ErrorClass, Status, Consumed, Body,
    Header(HeaderName),                            // semantic resolved header   (All)
    ArenaBytes,                                    // whole arena byte-view      (ZeroCopyLayout)
    ArenaTriple { tag: NameTag },                  // (name_tag, off, len)       (ZeroCopyLayout)
    Sidecar     { tag: NameTag },                  // values >= 0x8000_0000      (ZeroCopyLayout)
    // machine
    TriState, StateLabel { step: usize }, Emitted { step: usize }, EmittedTotal,
    // linear / shared
    Discipline, Linearizable, InvariantHeld,
}
impl FieldPath {
    pub fn ordinal(&self) -> u16;                  // ErrorClass/Status first -> headline order
    pub fn applicability(&self) -> BackendApplicability;
}

pub enum Cell {
    Status(u16), Bytes(Bytes), HeaderValue(Bytes), ErrorClass(ErrorClass),
    Consumed(usize), Tri(StepTagKind), StateLabel(SmolStr),
    Discipline(DisciplineVerdict), Bool(bool),
    Absent { reason: AbsentReason },               // != any Cell, incl. another Absent
}
pub enum StepTagKind { Complete, Incomplete, Error }
pub enum AbsentReason { TriStateIncomplete, FieldNotProduced, NotApplicableToBackend }

pub enum DisciplineVerdict {                       // X-4 exactly-once token discipline
    Clean,
    DoubleRelease     { handle: HandleId, first: OpIndex, second: OpIndex },
    UseAfterRelease   { handle: HandleId, released_at: OpIndex, used_at: OpIndex },
    Leak              { handle: HandleId, acquired_at: OpIndex },
    UseWithoutAcquire { handle: HandleId, used_at: OpIndex },
}

pub enum ErrorClass {                              // kit-owned; adapters map into it
    Smuggling(SmuggleClass), ProtocolError(ProtoCode), FlowControl,
    HeaderListTooLarge, DecompressionBomb, BadVarint, MalformedFrame,
    PathEscape, TlsDowngradeRefused, ReplayRejected, Timeout(Phase), Other(SmolStr),
}
pub enum SmuggleClass {                            // mirrors parsed_request.rs:27-46
    ContentLengthAndTransferEncoding, DuplicateContentLength, ChunkedNotLast,
    NullByteInHeader, UnsupportedTransferEncoding, InvalidContentLength,
}

// ===================== projection + comparison seam =====================
pub trait Projector {
    // Runs the wf-gate (§3); Produced+wf-ok -> Present(Projection), wf-fail -> Malformed,
    // Observation::Absent -> Absent. Never panics.
    fn project(&self, obs: &Observation, p: Primitive) -> Presence;
    // Flatten a wf-checked projection into comparison cells.
    fn fields(&self, proj: &Projection) -> Vec<(FieldPath, Cell)>;
    fn field_spec(&self, field: &FieldPath) -> FieldSpec;
}
pub struct FieldSpec { pub comparator: Comparator, pub applicability: BackendApplicability }
pub enum Comparator { StatusExact, BytesExact, HeaderMultiset, ErrorClassEq, Exact, Predicate }
pub enum BackendApplicability {
    All,
    ZeroCopyLayout,                                // {CurrentNet, FormalModel, GeneratedEngine}
    Custom(BTreeSet<BackendId>),
}

// ===================== minimization seam =====================
pub trait Minimizer {
    fn shrink(&self, input: &Input, spec: &Spec, target: &FieldPath,
              still_diverges: &dyn Fn(&Input) -> bool) -> MinimalRepro;
}
pub struct MinimalRepro {
    pub input: Input, pub spec: Spec,
    pub still_diverges_on: FieldPath, pub shrink_steps: u32,
}

// ===================== perf seam =====================
pub trait PerfGate {
    fn evaluate(&self, v: &Vector, backends: &[&dyn SutAdapter]) -> PerfOutcome;
}
pub enum PerfOutcome {
    Pass,
    ThresholdMissed   { backend: BackendId, metric: SmolStr, got: f64, floor: f64 },
    BaselineRegression{ backend: BackendId, baseline: SmolStr, got: f64, baseline_value: f64 }, // PF-5
}

// ===================== verdict (a TOTAL partition) =====================
pub enum Verdict {
    Agree                 { witnesses: usize },
    Divergence            { primary: FieldPath, fields: Vec<FieldDivergence>, security: bool },
    InsufficientWitnesses { present: usize, required: usize },   // < quorum; never coverage
    RequiredBackendAbsent { backend: BackendId, reason: String },
    RejectionEscaped      { accepting: Vec<BackendId>, minimal_repro: Option<MinimalRepro> },
    Malformed             { backend: BackendId, violation: WfViolation },
}
pub struct FieldDivergence {
    pub field:         FieldPath,                  // EXACTLY which field
    pub clustering:    Clustering,
    pub per_backend:   BTreeMap<BackendId, Cell>,  // each backend's concrete value
    pub minimal_repro: Option<MinimalRepro>,
}
pub enum Clustering {
    Outlier      { outlier: BackendId, majority: BTreeSet<BackendId>, majority_value: CellDigest },
    Schism       { clusters: Vec<(CellDigest, BTreeSet<BackendId>)> },
    AgainstGolden{ dissenting: BTreeSet<BackendId> },
}
pub enum Severity { Red, Recorded }

// ===================== reports =====================
pub struct VectorReport {
    pub vector: ContentHash, pub unit: UnitId, pub primitive: Primitive,
    pub ledger_row: LedgerKey, pub suite_case: CaseKey, pub kind: Kind,
    pub witnesses: Vec<WitnessSummary>,            // per backend: Present|Absent|Malformed
    pub verdict: Verdict,
    pub counts_as_coverage: bool,                  // true  <=>  Verdict::Agree (>=2 present)
    pub severity: Severity,
    pub perf: Option<PerfOutcome>,                 // Some(..) iff Kind::Perf
}
pub struct RunReport { pub vectors: Vec<VectorReport>, pub ledger: NonVacuityLedger }

// ===================== non-vacuity ledger (CR-6 honesty surface) =====================
pub struct NonVacuityLedger {
    pub total: usize, pub genuine_agreements: usize, pub divergences: usize,
    pub insufficient: usize, pub required_absent: usize,
    pub rejection_escaped: usize, pub malformed: usize,
    pub absent_by_backend: BTreeMap<BackendId, usize>,
    pub per_row: BTreeMap<LedgerKey, RowAccounting>,
}
pub struct RowAccounting {
    pub vectors: usize, pub genuine_agreements: usize,
    pub present_by_backend: BTreeMap<BackendId, usize>,
    pub absent_by_backend:  BTreeMap<BackendId, usize>,   // the "oracle witnessed 0 of N" line
}
impl NonVacuityLedger {
    pub fn partition_is_total(&self) -> bool;            // buckets sum == total (asserted)
    pub fn coverage_gate(&self, non_oos: &BTreeSet<LedgerKey>) -> GateResult; // F.2
    pub fn ci_exit(&self) -> ExitCode;                  // non-zero iff any Red severity
}
pub enum GateResult {
    Pass,
    Fail { empty_rows: Vec<LedgerKey>, oracle_dark_rows: Vec<LedgerKey> },
}
```

---

## 11. Determinism

`region` / `machine` / `linear` projections are pure functions of `(input, spec)`
— reproducible by construction. `shared` is reproducible by `Schedule` seed replay.
No nondeterministic flake reaches CI; a divergence's `MinimalRepro` is a
deterministic, replayable, content-addressable artifact.

---

## Seams

### Provides (to `net/conformance-kit` + CI + the ledger-keying meta)
- The runner crate-surface `differential::DiffRunner::{run_vector, run_corpus}` and
  `RunPolicy` (the CR-6 quorum, the `required` set, OOS waivers, the shrink toggle).
- The total-partition `Verdict` (`Agree | Divergence | InsufficientWitnesses |
  RequiredBackendAbsent | RejectionEscaped | Malformed`), with `FieldDivergence` +
  `Clustering` (`Outlier | Schism | AgainstGolden`) naming the exact diverging field
  and outlier/clusters, and `MinimalRepro`.
- The projection/comparison seam `trait Projector` (runs the wf-gate, lowers
  `Observation -> Presence`, flattens to `(FieldPath, Cell)`), the kit-owned
  `FieldPath` / `Cell` (incl. `Cell::Absent`) / `ErrorClass` taxonomy /
  `DisciplineVerdict` / `Comparator` / `BackendApplicability`, and the per-primitive
  `Projection` normal forms + `WfViolation`.
- The minimization seam `trait Minimizer` and the perf seam `trait PerfGate` +
  `PerfOutcome`.
- The CI + coverage surface: `Severity`, `VectorReport.counts_as_coverage`,
  `RunReport`, `NonVacuityLedger::{partition_is_total, coverage_gate, ci_exit}`,
  `RowAccounting`, `GateResult` — consumed by the CI driver (Unit 5 / `F.2`) and the
  ledger-keying-coverage-meta.

### Consumes
- **From the fixed spine:** `SutAdapter` (`backend`, `supports -> Support`, the four
  `decode_region`/`run_machine`/`run_linear`/`run_shared` methods),
  `Observation { Produced{status,headers,body,arena_view,state_trace,error_class,consumed}
  | Absent{reason} }`, `BackendId`, `Primitive`, `Vector{id,primitive,unit,ledger_row,
  suite_case,kind,input,spec,expected,acceptance}`, `Expectation { Golden | NwayAgree |
  MustReject }`, `Support { Supported | Absent{reason} }`, `Kind`.
- **From Unit 1 (corpus):** the `Corpus`/`Vector` container, `ContentHash` keying,
  `Input { Bytes | EventSeq | ResourceOps | Schedule }`, `Spec`, and the per-primitive
  `Input` shrinkers the `Minimizer` reuses.
- **From Unit 2 (adapters):** each adapter's `classify_error() -> ErrorClass`; a
  seedable schedule-deterministic `run_shared`; an `Event` channel able to carry a
  `VirtualClock` tick (time-as-input, `40-LEDGER §198`); **and** — to compute the
  region wf-gate and byte-layout fields — the raw `(name_tag, off, len)` triples +
  `arena_view` + `sidecar` inside `Observation::Produced`, plus the FormalModel's
  `OutcomeSet` for `shared`.
- **From the ledger meta:** the `40-LEDGER` row set with OOS flags for `coverage_gate`.

### Tensions with the fixed spine
1. **shared is a predicate, not a value.** The spine's `Observation::Produced` is
   value-shaped (`status/headers/body/arena_view/state_trace`), but `shared`
   agreement is "∃ a valid linearization ∧ invariant held," not trace-byte equality
   (`21:52-72`, Ranks 5-7). Comparing `state_trace` bytes would flag false
   divergences when two correct backends pick different valid orders. The runner
   compares predicates (`Comparator::Predicate` over `Linearizable`/`InvariantHeld`
   + `observed ⊆ model_allowed`), diverging from the value-shaped spine for `shared`.
2. **The oracle cannot bind byte-layout.** The spine implies all backends produce a
   comparable `arena_view`, but the out-of-process Elide oracle (CR-3) has a
   different internal layout (`parsed_request.rs:6-12`; sidecar union at `:685`). The
   runner adds a per-field `applicability` (`ZeroCopyLayout`) the spine does not
   model, restricting `ArenaBytes`/`ArenaTriple`/`Sidecar` to the three layout-true
   backends and holding the oracle only to resolved `Header`/`Status`/`Body` cells.
3. **`Incomplete` has no `consumed`.** The tri-state `Incomplete`
   (`socks.rs:84-91`, `response_parser.rs:41-48`) carries no consumed count, but the
   spine's `Observation::Produced.consumed: usize` is always present. The runner
   projects `Consumed` as `Cell::Absent` (not `0`) whenever the tri-state is
   `Incomplete`; the spine flattens this.
4. **The spine has no `Malformed` state.** A `Produced` whose `arena_view` violates
   `wf_parsed_request` (`21:23-24`) or whose trace regresses would, under the spine,
   be eligible to "agree." The runner adds the wf-gate and `Presence::Malformed` /
   `Verdict::Malformed` — a runner-side invariant the spine does not name.
5. **`MustReject` / `linear` are predicate-shaped, not equality-shaped.** Two
   backends could "agree" on *accepting* an attack. The runner special-cases these to
   "every present witness must independently reject," with `RejectionEscaped` (not a
   votable divergence); the single `Observation` equality surface does not distinguish
   this.
6. **No single outlier under an even split.** Emphasis A asks to name *the* outlier,
   but with exactly four backends a 2-2 split has none. The runner always names the
   diverging *field*, but outlier identification honestly degrades to
   `Clustering::Schism{clusters}` under an even split — a precision ceiling, not a
   guarantee.
7. **Perf is unmodeled by the spine.** `Kind::Perf` cannot be field-diffed; `PF-5`
   beat-or-match (`41:294`) is an inequality. The runner routes `Kind::Perf` to a
   `PerfGate`; the unified `Observation` models no latency/throughput/alloc-count, so
   this is a parallel observation channel the spine omits.
8. **Machine traces need time-as-input.** Timeout-driven transitions diverge
   spuriously unless the spine's `Event` carries a `VirtualClock` tick (`40-LEDGER
   §198`): the FormalModel injects clock ticks while CurrentNet/oracle read a real
   clock. This is a constraint the runner imposes back on Unit 2's machine adapter,
   not satisfiable within the runner alone.
9. **Early-state coverage is structurally low — and must stay honest.** With
   `min_witnesses = 2` and only `CurrentNet` present today, most `NwayAgree` vectors
   score `InsufficientWitnesses` (zero coverage) until the extracted FormalModel and
   the GeneratedEngine land. That is the correct CR-6 answer; the headline coverage
   number must NOT be inflated by lowering the quorum.

( ⌐■_■ ) every disagreement names its field, its outlier, and the smallest input
that still breaks — and no skipped oracle is ever counted as a friend.
