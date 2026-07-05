# 42 — THE CONFORMANCE / TEST / PERF KIT (THE MASTER — the `SutAdapter` keystone)

> **The keystone the other suite docs hang off.** `40-LEDGER` is the *formal-coverage*
> map (one row = one HOL4 obligation); `41-SUITE` is the *empirical-coverage* map (one
> row's cases = the gauntlet the running artifact survives). **This** file (`42`) is the
> *machine* that runs `41`'s corpus against every backend through **one uniform surface** —
> the `SutAdapter`. It defines that surface authoritatively.
>
> The test/perf suite is the **FOURTH consumer** of the one DSL description
> (`20-ARCHITECTURE.md:24-48`), not a pile of `#[test]`s bolted onto whichever Rust
> happens to exist today. Today's `net/` Rust is **oracle backend #1**: a swappable
> baseline, **NOT** the system under test. The real SUT is the future generated engine,
> which must plug in **for free**. ( ⌐■_■ )

---

## 0. The one load-bearing insight — the adapter surface IS the sans-IO core

The protocol core is **sans-IO**: `(state, bytes) → (state', events, out)`
(`20-ARCHITECTURE.md:170`). That signature is the universal adapter. It is not invented
here — it already exists in today's code as a **convention**: every parser returns a
tri-state result.

- `ParseResult<T> { Complete { value, consumed } | Incomplete | Error(&str) }` —
  `net/httpe/src/protocol/socks.rs:84-92`
- `ResponseParseResult { Complete { body_offset } | Incomplete | Error }` —
  `net/httpe/src/cq/response_parser.rs:41-49`
- `ArenaDecodeResult` from `decode_into_arena` — `net/httpe/src/protocol/h3/qpack.rs:107,1685`

We are **formalizing a seam the code already grew**, not inventing one. The four
`SutAdapter` methods are exactly the four lowered DSL primitives (ADR-7,
`10-DECISIONS.md:53-55`): `decode_region` · `run_machine` · `run_linear` · `run_shared`.
Because the verified compiler emits one sans-IO entry per primitive per unit, **the
`GeneratedEngine` adapter is compiler-emitted, not hand-written** (§7) — that is the whole
point of shaping the surface this way.

```
                 ONE DSL description
                        │ compiled by the verified compiler (CR-4)
        ┌───────────────┼───────────────┬─────────────────────┐
        ▼               ▼               ▼                     ▼
   machine code     formal model     ~90% proofs          THIS KIT
   (line-rate)      (HOL4/CakeML)    (auto-discharged)     runs ONE corpus
        │               │                                  through ONE seam
        ▼               ▼                                          │
  GeneratedEngine   FormalModel  ◄────  SutAdapter  ────►  CurrentNet · ExternalOracle
   (free, §7)       (extracted)        (the seam)          (#1 today)  (IPC, CR-3)
```

---

## Reconciled Seam Contract (see 48-SEAM-AUDIT)

> **This doc is the keystone, but it is NOT the final word on the cross-unit seams.**
> Docs `43`–`47` were each written against their own reading of the spine below, and
> they diverge in detail (record shape, the runner output type, the error taxonomy,
> the field mask, perf routing, support arity, absence reasons). The adversarial
> synthesis **`docs/engine/48-SEAM-AUDIT.md`** reconciles all twenty contradictions
> and pins the **single authoritative `SutAdapter` + `Vector` + `Observation`** all
> six units conform to. Where the signatures in §1–§9 below contradict `48`, **`48`
> governs.** The load-bearing deltas `48` fixes against *this* doc:
>
> - the runner output is `44`'s **`Verdict`** (6-way total partition), **not** the
>   `Outcome`/`DivergingField` in §3 — both are deleted (48 C-5/C-6);
> - the backend trait object the runner holds is **`ProvenancedAdapter: SutAdapter`**
>   (`46`), perf-extended by **`PerfSut`** (`45`); `Verdict::Agree` counts as coverage
>   **only** if `nway_has_independent_witness` holds (48 C-16);
> - `Vector` is `43`'s **`{ core, meta }`** split with plural `ledger_rows`/`suite_cases`
>   and accessor methods, **not** the flat re-export in §6 (48 C-1/C-2);
> - `Expectation::MustReject` carries a **`RejectPredicate`** and a 4th
>   **`Budget(GateRef)`** variant exists (48 C-9/C-10);
> - this doc's `linear_trace`/`linearization` `Produced` fields (§2) **are**
>   authoritative — `44`/`46`'s "smuggle into `state_trace`" is deleted, and
>   `Linearization` is widened with `observed`/`model_allowed` (48 C-3/C-4);
> - `ErrorClass` adopts `44`'s richer enumeration; `ObservedFields` (this doc's
>   9-flag type) is canonical and absorbs `43`'s `ObsFieldSet`; `Event` becomes an
>   enum `{ Wire, Timer(VirtualClock) }`; absence reasons split into
>   `BackendAbsentReason` (46) and `CellAbsentReason` (44) (48 C-7/C-8/C-18/C-19).
>
> The migration story, the four `BackendId` mappings, the seam table, and the
> two-granularity CR-6 mechanism in this doc are **unchanged** by `48`.

---

## 1. The `SutAdapter` trait (refined from the fixed spine)

Every backend implements `SutAdapter` exactly once. A **unit** = one DSL
unit-under-test (e.g. `h1-request-parse`), mapping 1:1 to a `40-LEDGER` row. Two
refinements over the North-Star spine, both load-bearing and explained in §10:

1. **`supports(unit, primitive) → Support`** — widened from the spine's `supports(unit)`.
   Support is genuinely per-`(unit, primitive)`: the oracle supports a unit's `region`
   surface (over the wire) but is `Absent` for that same unit's `linear` discipline.
2. **`ObservedFields` bitmask** on both `Support` and `Produced`. The spine's
   `Observation::Produced` has non-optional `status`/`arena_view`/`state_trace`, but **no
   `(primitive × backend)` cell populates all of them** (a pure request-parse has no
   status; the wire oracle has no `arena_view`; `shared` has neither). The differ ranges
   over the **field-intersection** of the genuine producers — an unobserved field is
   *excluded*, never laundered as equal. This is the field-granular CR-6 mechanism.

```rust
/// crate net/conformance-kit — src/adapter.rs  (UNIT 1 OWNS these signatures)
pub trait SutAdapter {
    fn backend(&self) -> BackendId;

    /// CR-6 non-vacuity pre-probe, per-(unit, primitive), with field granularity.
    /// `Absent` here NEVER counts as agreement.
    fn supports(&self, unit: UnitId, prim: Primitive) -> Support;

    /// region/view: bytes -> arena-view. (H1 from_httparse / H2 from_h2_headers /
    /// H3 from_h3_decode; QPACK/HPACK arena decode.)
    fn decode_region(&self, unit: UnitId, input: &[u8], spec: &Spec) -> Observation;

    /// machine: sans-IO FSM fed an event/byte sequence; observed as a folded trace
    /// (the adapter, not this signature, owns the incremental feed loop — see §10).
    fn run_machine(&self, unit: UnitId, init: &Spec, events: &[Event]) -> Observation;

    /// linear: acquire -> use -> release-once (the X-4 exactly-once token discipline).
    fn run_linear(&self, unit: UnitId, ops: &[ResourceOp]) -> Observation;

    /// shared: a schedule -> linearization (Iris logical-atomicity; loom/shuttle-shaped).
    fn run_shared(&self, unit: UnitId, schedule: &Schedule) -> Observation;
}
```

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BackendId { CurrentNet, ExternalOracle, FormalModel, GeneratedEngine }

/// The four DSL primitives (ADR-7; 10-DECISIONS.md:53-55).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Primitive { Region, Machine, Linear, Shared }

/// One DSL unit-under-test, e.g. UnitId("h1-request-parse"). Maps 1:1 to a 40-LEDGER row.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct UnitId(pub &'static str);

/// CR-6 non-vacuity probe result. `Absent` is NEVER a match.
pub enum Support {
    Supported { observes: ObservedFields },
    Absent { reason: String },
}

bitflags::bitflags! {
    /// Which Observation fields a (backend, unit, primitive) cell can populate.
    /// The differ ranges over the INTERSECTION of these across genuine producers,
    /// never over the whole record (§3).
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
```

---

## 2. The `Observation` type

`Observation = Produced(Produced) | Absent { reason }`. The `Absent` variant is the
runtime CR-6 firewall (§3). `Produced` carries every projection any cell might observe;
the `fields` mask says which are meaningful, so absent fields are never compared.

```rust
pub enum Observation {
    Produced(Produced),
    Absent { reason: String },   // not a match; the runner counts it separately
}

pub struct Produced {
    pub fields: ObservedFields,            // which Option<_> below carry signal
    pub status: Option<Status>,            // None for region/request, linear, shared
    pub headers: HeaderSet,                // canonical sorted; empty unless HEADERS set
    pub body: Bytes,
    pub arena_view: Option<ArenaView>,     // region/view
    pub state_trace: Option<Trace>,        // machine (and linear's op-trace rides here)
    pub error_class: Option<ErrorClass>,
    pub consumed: Option<usize>,           // bytes advanced (socks.rs:87 / body_offset)
    pub linear_trace: Option<LinearTrace>, // linear (X-4)
    pub linearization: Option<Linearization>, // shared (Iris)
}
```

### 2.1 Per-primitive projection types

```rust
// ── region/view ──────────────────────────────────────────────────────────────
// Normalizes ParsedRequest (parsed_request.rs:611-667, 896) and the HOL4
// wf_parsed_request predicate (21-FORMAL-MODEL.md:19-28) to the SAME value:
// "immutable byte arena + (name_tag, off, len) triples", identical across H1
// pointer-arithmetic, HPACK copy, and QPACK arena (the Rank-1 unification).
pub struct ArenaView {
    pub arena: Bytes,
    pub method: Method,
    pub uri: (u32, u32),                   // (off, len) into arena
    pub fields: Vec<ArenaField>,           // header (name_tag, val_off, val_len) triples
    pub sidecar: Bytes,                    // mutation union; offsets >= SIDECAR_OFFSET_BASE
    pub wf: WellFormed,                    // mirrors wf_parsed_request
}
pub struct ArenaField { pub name: NameTag, pub off: u32, pub len: u32 }
/// Mirrors HeaderName (parsed_request.rs:554-559). An `off >= SIDECAR_OFFSET_BASE`
/// (0x8000_0000) points into `sidecar` at `off - SIDECAR_OFFSET_BASE`.
pub enum NameTag { WellKnown(u16), StaticStr(&'static str), Custom { off: u32, len: u32 } }
/// The arena's only open hypothesis (every off+len <= arena.len() or in-sidecar,
/// all ranges valid UTF-8 — discharged by the EverParse parser proof, 21-FORMAL X-2).
pub enum WellFormed { Yes, No { violated: &'static str } }

// ── machine ──────────────────────────────────────────────────────────────────
// The (state, event|bytes) -> (state', events, out) trace (20-ARCHITECTURE.md:170).
// Observed as a FOLD of the incremental tri-state, not a single call (§10 tension).
pub struct Trace { pub steps: Vec<Step> }
pub struct Step { pub state: StateLabel, pub parse: ParseClass, pub emitted: Bytes, pub events: Vec<Event> }
/// The universal tri-state (socks.rs:84-92; response_parser.rs:41-49).
pub enum ParseClass { Complete { consumed: usize }, Incomplete, Error }
pub struct StateLabel(pub &'static str); // e.g. ProtocolState variant name (21-FORMAL Rank-2)
pub struct Event(pub Bytes);             // refined per-protocol by the machine unit (unit 3)

// ── linear ───────────────────────────────────────────────────────────────────
// acquire -> use -> release-once (X-4: BufRingLease / PooledBuf / DispatchDecision,
// 21-FORMAL-MODEL.md:95-97). Observe: release-once held, no use-after-release.
pub struct LinearTrace { pub events: Vec<LinearEvent> }
pub enum LinearEvent { Acquire(HandleId), Use(HandleId), Release(HandleId) }
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct HandleId(pub u64);

// ── shared ───────────────────────────────────────────────────────────────────
// schedule -> linearization under interleaving (Iris ranks 5-7, 21-FORMAL:54-72).
pub struct Linearization { pub order: Vec<OpId>, pub invariant_held: bool }
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct OpId(pub u32);
pub struct Schedule { pub threads: Vec<Vec<OpId>>, pub seed: u64 }
pub enum ResourceOp { Acquire(HandleId), Use(HandleId), Release(HandleId) }

// ── shared scalar vocabulary ─────────────────────────────────────────────────
pub struct Status(pub u16);
/// Canonical comparison form: lowercased names, value bytes, sorted. Order-defined
/// per unit so HeaderSet equality is well-defined across backends.
pub struct HeaderSet(pub Vec<(Bytes, Bytes)>);

/// Unified error taxonomy so error_class is comparable across backends. Grounded in
/// the real `SmuggleViolation` (parsed_request.rs:27-46) and the protocol error sites.
pub enum ErrorClass {
    Smuggle(SmuggleKind),     // mirrors SmuggleViolation
    Protocol(&'static str),   // socks.rs:91 Error(&str) / H3Error / h2 PROTOCOL_ERROR
    Reject { code: u16, reason: &'static str }, // 400/501/431/414/413 ...
    Truncated, Oversized, Bomb,
}
pub enum SmuggleKind { ClTe, DupCl, ChunkedNotLast, NullByte, UnsupportedTe, InvalidCl }

/// The driving input for a unit run. The corpus unit selects the variant per primitive.
pub enum Input { Bytes(Bytes), Events(Vec<Event>), ResourceOps(Vec<ResourceOp>), Schedule(Schedule) }
pub struct Spec;  // per-unit configuration (the 40-LEDGER row config); authored by the spec unit.
```

---

## 3. Non-vacuity — the CR-6 firewall (sacred)

CR-6 (`40-LEDGER.md:10-11`; `41-SUITE.md:336-338`): *a backend that cannot run a unit
NEVER counts as a match.* Enforced at **two granularities**:

1. **Backend-level (`Observation::Absent { reason }`).** `supports()` is the cheap
   pre-probe; `Observation::Absent` is the **authoritative** classification — even if
   `supports()` said yes, a backend that errors / refuses / times out yields `Absent`,
   and the runner records it as a `BackendAbsent` context, never as `Agree`.
2. **Field-level (`ObservedFields`).** An `Agree` on a given field requires **≥2**
   backends that both `Produced` **and** whose `ObservedFields` intersection includes
   that field. `<2` genuine producers for the keyed field ⇒ `InsufficientProducers` ⇒
   **NOT coverage**.

Coverage counts **only** `Outcome::Agree`. Laundering an oracle/model skip as a pass is
a **build failure** (`harness/diff-nonvacuity-gate`, `41-SUITE.md:336`). The runner is
the N-way generalization of the three-way runner (`41-SUITE.md:328-331`):

```rust
/// The N-way differential verdict for one (vector × present-backend-set).
/// coverage counts ONLY Agree. (Generalizes harness/three-way-runner, 41-SUITE F.1.)
pub enum Outcome {
    /// >=2 genuine producers agree on a non-empty observed-field intersection.
    Agree { backends: Vec<BackendId>, on: ObservedFields },
    /// A named diverging field between two producing backends. (41-SUITE.md:331:
    /// "any pairwise divergence fails and names the diverging field".)
    Divergence { field: DivergingField, left: BackendId, right: BackendId },
    /// <2 genuine producers for the keyed field => NOT coverage (CR-6).
    InsufficientProducers { absent: Vec<(BackendId, String)> },
}
pub enum DivergingField {
    Status, Headers, Body, ArenaView, StateTrace, ErrorClass, Consumed, LinearTrace, Linearization,
}
```

---

## 4. The four `BackendId` mappings — HOW each presents each primitive

- **`CurrentNet` — direct in-process call (oracle #1; the ONLY backend today).**
  - *region* → feed `input` to `httparse::Request` → `validate_h1_smuggling`
    (`parsed_request.rs:119`) → `ParsedRequest::from_httparse` (`:1010`) /
    `from_h2_headers` (`:1107`) / `from_h3_decode` (`:1417`), then project `arena()`
    (`:896`) + the `HeaderEntry` `(name, val_off, val_len)` triples (`:592-599`) + sidecar
    into `ArenaView`; map `SmuggleViolation` (`:27`, `status_code()` `:91`) → `ErrorClass`.
  - *machine* → drive `h1_response_try_parse` (`response_parser.rs:58`) / the per-protocol
    FSM in a feed loop, recording each tri-state as a `Step`; project `ProtocolState`
    (21-FORMAL Rank-2) → `StateLabel`.
  - *linear* → instrument acquire/use/drop on `BufRingLease`/`PooledBuf` (miri/loom) into
    `LinearTrace`.
  - *shared* → loom/shuttle interleaving into `Linearization`.
- **`ExternalOracle` — out-of-process IPC shim (CR-3).** `OracleHandle` is a subprocess/IPC
  client to the running internal Elide HTTP-engine source tree (`41-SUITE.md:329`); **read/diff, NEVER linked**
  (`oracle/PROVENANCE.md:9`). The oracle is a *whole server*, so the shim lifts
  **wire → sans-IO only where reachable**: it writes request bytes to a socket and reads
  response bytes back.
  - *region* / *machine* → Supported; observes `STATUS`/`HEADERS`/`BODY`/`ERROR_CLASS`
    (and `CONSUMED` where the wire defines it), but **never** `ARENA_VIEW` or
    `STATE_TRACE` — those are process-internal, invisible across the IPC boundary.
  - *linear* / *shared* → **`Absent`**: lease recycle-order and `Ring` head/tail atomics
    are not observable over the wire.
  - Enforcement: `harness/oracle-provenance-firewall` (`41-SUITE.md:332-333`) is a link-set
    symbol scan; the build **fails** if any oracle symbol enters the engine link set.
- **`FormalModel` — HOL4/CakeML-extracted pure function.** Each `modeled` `40-LEDGER`
  row's theory is extracted to a runnable fn (`harness/executable-model-bridge`,
  `41-SUITE.md:334`); a non-extractable model ⇒ the row cannot be diffed ⇒ **fail** (never
  a silent pass).
  - *region* → the extracted decode fn returns the `ArenaView` + the `wf_parsed_request`
    witness (`21-FORMAL.md:19-28`).
  - *machine* → the Rank-2 `step` fn IS the model; observes the full `STATE_TRACE`.
  - *linear* → the X-4 token relation as an executable trace check (`21-FORMAL.md:95-97`).
  - *shared* → **`Absent`**: Iris logical-atomicity (ranks 5-7, `21-FORMAL.md:54-64`) is a
    hand-proof, **not extraction-executable** as a runtime schedule enumerator. The proof
    stands *beside* the runner, not inside it (§10 tension).
- **`GeneratedEngine` — compiler-emitted shim (does NOT exist yet; forward-ref unit 5).**
  Until unit 5's compiler emits it, `supports()` returns `Absent { reason: "engine not yet
  emitted" }` for every `(unit, primitive)`. When emitted, the compiler produces the
  sans-IO entry per primitive and `GeneratedAdapter<U>` wraps it (§7); `supports()` then
  returns `Supported { observes: ALL }` by the compiler-correctness theorem (the emitted
  code is total + `wf`-preserving, so every field is populated and trustworthy). It slots
  in with **zero corpus change** (§8).

---

## 5. THE SEAM TABLE — `(primitive × backend)`: Supported / Absent + meaningful fields

Legend: **●** Supported · **◐** Supported but some fields Absent · **○** Absent. The
listed fields are the `ObservedFields` that carry signal for that cell; the differ uses
the field-intersection (§3), so cells with disjoint field sets simply do not constrain
each other.

| primitive \ backend | **CurrentNet** (oracle #1) | **ExternalOracle** (IPC, CR-3) | **FormalModel** (extracted) | **GeneratedEngine** (emitted) |
|---|---|---|---|---|
| **region/view** | ● `ARENA_VIEW`, `ERROR_CLASS`, `CONSUMED` (+`STATUS`/`HEADERS`/`BODY` if the unit emits a response) | ◐ `STATUS`, `HEADERS`, `BODY`, `ERROR_CLASS` — **no `ARENA_VIEW`** | ● `ARENA_VIEW` (+`wf`), `ERROR_CLASS`, `CONSUMED` | ○ until unit 5; then ● **ALL** |
| **machine** | ● `STATE_TRACE` (from `ProtocolState`), `BODY`, `ERROR_CLASS`, `CONSUMED` | ◐ `STATUS`, `BODY`, `ERROR_CLASS` — **no `STATE_TRACE`** (wire round-trip) | ● `STATE_TRACE` (the `step` fn), emitted `BODY`, `ERROR_CLASS` | ○ → ● **ALL** |
| **linear** | ● `LINEAR_TRACE` (miri/loom) | ○ lease discipline is process-internal | ● `LINEAR_TRACE` (X-4 token relation) | ○ → ● `LINEAR_TRACE` |
| **shared** | ● `LINEARIZATION`, `invariant_held` (loom/shuttle) | ○ cannot inject schedules over IPC | ○ Iris proof not extraction-executable | ○ → ● `LINEARIZATION` |

**Reading the table is the whole CR-6 point.** Today (no `GeneratedEngine`):

- a `region` vector's `arena_view` field can `Agree` only among `{CurrentNet, FormalModel}`
  (oracle `Absent` on that field); its `status/headers/body` fields *also* include the
  oracle — the field-intersection rule makes this automatic.
- a `linear` vector can `Agree` only among `{CurrentNet, FormalModel}`.
- a `shared` vector has a **single** producer (`CurrentNet`) until the engine lands — so
  it **cannot** use `NwayAgree`; it must be `Golden(...)` or it is rejected at registration
  (§6, §10). The Iris proof stands beside the runner.

Two of four primitives (`linear`, `shared`) have **no out-of-process oracle** — stated
honestly, not papered over.

---

## 6. Keying & the ledger-coverage meta

Every vector is keyed to **(a)** a `Primitive`, **(b)** a `40-LEDGER` row (`ledger_row`),
**(c)** a `41-SUITE` case (`suite_case`), **(d)** a `Kind`. The corpus record is the
North-Star spine vocabulary, **re-exported by the master crate** but **authored by the
corpus unit (unit 5)** — UNIT 1 owns `SutAdapter`/`Support`/`Observation` and only *names*
`Vector` for coherence:

```rust
// Re-exported at the crate root; field types owned as noted. (Corpus unit authors the body.)
pub struct Vector {
    pub id: ContentHash,          // content-addressed (harness/vector-corpus-format)
    pub primitive: Primitive,     // UNIT 1
    pub unit: UnitId,             // UNIT 1
    pub ledger_row: LedgerKey,    // 40-LEDGER §A.x
    pub suite_case: CaseKey,      // 41-SUITE case id
    pub kind: Kind,               // Conformance | Behavioral | Security | Perf | Differential
    pub input: Input,             // UNIT 1
    pub spec: Spec,               // spec unit
    pub expected: Expectation,    // Golden | NwayAgree | MustReject
    pub acceptance: Acceptance,
}
pub enum Kind { Conformance, Behavioral, Security, Perf, Differential }
pub struct ContentHash(pub [u8; 32]);
pub struct LedgerKey(pub &'static str);
pub struct CaseKey(pub &'static str);
pub enum Expectation { Golden(Box<Observation>), NwayAgree, MustReject { error_class: ErrorClass } }
pub enum Acceptance { ExactObservation, FieldsMatch(Vec<DivergingField>), RejectionOnly, NoPanicNoAlloc }
```

`harness/ledger-keying-coverage-meta` (`41-SUITE.md:345-347`) proves every non-OOS
`40-LEDGER` row owns ≥1 vector whose runner `Outcome` is `Agree`; `GAP`/`OOS` rows are
explicitly excused. **Registration-time guard:** a `NwayAgree` expectation is **rejected**
for any unit whose seam-table row has `<2` Supported producers on the keyed field (§5,
§10) — such a unit must use `Golden(...)`, otherwise `InsufficientProducers` would silently
mark it uncovered. The existing data-file replay `net/httpe/tests/curl_test_vectors.rs`
(`CurlTestCase`, `:107`) is the shape this generalizes: one case =
`{wire bytes, spec, expected arena + status + bytes}`.

---

## 7. EMPHASIS A — the generated engine plugs in for FREE

The four `SutAdapter` methods are the four lowered DSL primitives, so the
`GeneratedEngine` adapter is **a ~12-line newtype the compiler emits**, not hand-written
glue. The verified compiler implements `DslUnit` per unit; `GeneratedAdapter<U>` is the
blanket adapter:

```rust
/// The codegen hook the verified compiler implements (forward-ref unit 5). Each method
/// is the compiler-emitted sans-IO entry for one primitive of one unit.
pub trait DslUnit {
    const UNIT: UnitId;
    fn region(input: &[u8], spec: &Spec) -> Produced;
    fn machine(init: &Spec, events: &[Event]) -> Produced;
    fn linear(ops: &[ResourceOp]) -> Produced;
    fn shared(schedule: &Schedule) -> Produced;
}

pub struct GeneratedAdapter<U: DslUnit>(core::marker::PhantomData<U>);
// blanket impl SutAdapter for GeneratedAdapter<U>:
//   backend()  => BackendId::GeneratedEngine
//   supports() => Supported { observes: ObservedFields::all() }  (compiler-correctness thm)
//   the four methods delegate to U::region/machine/linear/shared, wrapping Produced.
```

```rust
/// CR-3 firewall handle: the oracle is out-of-process, NEVER linked (oracle/PROVENANCE.md:9;
/// 41-SUITE.md:332). No oracle symbols appear in the engine link set.
pub struct OracleHandle { /* subprocess/IPC client to the internal Elide HTTP-engine source tree */ }
```

---

## 8. The migration story — oracle #1 today, generated engine for free tomorrow

`CurrentNet` and `GeneratedEngine` are **time-exclusive occupants of one slot** (the
system-under-test / "engine" leg of the runner, `41-SUITE.md:328`), not two simultaneous
peers — this is the friction the flat 4-enum hides (§10).

- **TODAY:** `CurrentNet` fills the SUT slot (oracle #1) and the runner's engine leg;
  `ExternalOracle` + `FormalModel` are the cross-checks where the seam table says Supported.
  The three-way runner is `(CurrentNet-as-SUT, ExternalOracle, FormalModel)`.
- **LATER:** a unit's `GeneratedEngine` adapter is compiler-emitted from the same DSL
  description (§7). It takes the SUT slot; `CurrentNet` demotes to a cross-check (and may
  retire per-unit once the generated engine N-way-agrees). **No vector changes** — the
  corpus is content-addressed and backend-agnostic (`41-SUITE.md:325`). The runner's
  `Outcome` turns the engine from "all `Absent`" into a live N-way participant **with no
  vector authoring** — the acceptance gate of `41-SUITE §H` made operational.

---

## 9. Seams

**This unit (`net/conformance-kit::adapter`) PROVIDES:**

- `trait SutAdapter` (the universal sans-IO surface: `backend`, `supports`, the four
  primitive methods); `enum BackendId`; `enum Primitive`; `struct UnitId`.
- `enum Support`; `bitflags ObservedFields`; `enum Observation { Produced | Absent }` with
  `struct Produced`.
- the projection types — region: `ArenaView`/`ArenaField`/`NameTag`/`WellFormed`; machine:
  `Trace`/`Step`/`ParseClass`/`StateLabel`/`Event`; linear: `LinearTrace`/`LinearEvent`/
  `HandleId`; shared: `Linearization`/`OpId`/`Schedule`/`ResourceOp`.
- the scalar vocabulary `Status`/`HeaderSet`/`ErrorClass`/`SmuggleKind`/`Input`.
- the runner contract `enum Outcome { Agree | Divergence | InsufficientProducers }` +
  `enum DivergingField`, with the CR-6 field-intersection classification rule (§3).
- the codegen hook `trait DslUnit` + `struct GeneratedAdapter<U>` (Emphasis A); the CR-3
  `OracleHandle` marker.

**This unit CONSUMES:**

- *From the fixed spine:* the `Vector` record + `Kind`/`Expectation`/`Acceptance`/`Spec`
  vocabulary (re-exported here, authored by the corpus unit 5 + the spec unit).
- *From the docs:* the sans-IO contract (`20-ARCHITECTURE.md:170`); ADR-7's four
  primitives (`10-DECISIONS.md:53-55`); the tri-state convention (`socks.rs:84-92`,
  `response_parser.rs:41-49`); the arena model + `SIDECAR_OFFSET_BASE` + `wf_parsed_request`
  (`parsed_request.rs:611-667,896`, `21-FORMAL.md:19-28`); the X-4 token discipline
  (`21-FORMAL.md:95-97`); Iris ranks 5-7 (`21-FORMAL.md:54-72`); the three-way runner +
  diff fields + non-vacuity gate + executable-model-bridge + ledger-keying-coverage-meta
  (`41-SUITE.md:324-347`).
- *From other units (downstream):* units 2-4 author the per-primitive adapter bodies
  against these signatures; unit 5 authors the corpus + the unified crate + the
  `GeneratedAdapter` codegen; the model-bridge unit makes each HOL4 theory extractable to
  the `decode_region`/`run_machine`/`run_linear` entry points.

**Tension with the fixed spine (reported, not silently diverged):**

1. **The spine's flat 4-backend enum hides a time-exclusive slot.** The `41-SUITE` runner
   is three-way (engine, oracle, model); `CurrentNet` is not a fourth peer — it *currently
   fills the engine/SUT slot* because `GeneratedEngine` does not exist (§8). Resolved by the
   migration story + an N-way `Outcome`, but the enum itself is mildly misleading and this
   doc says so.
2. **The spine's `Produced` has non-optional `status`/`arena_view`/`state_trace`, but no
   cell populates all of them.** Added `ObservedFields` + made the fields `Option<_>`;
   without it, diffing the whole record would either false-diverge on absent fields or
   launder them as equal — both CR-6 violations (§1, §3).
3. **The spine's `supports(unit)` is too coarse.** Real support is per-`(unit, primitive)`
   (the oracle supports `region` but not `linear` for the same unit). Widened to
   `supports(unit, primitive) -> Support { observes }` (§1).
4. **The spine's `run_machine(events) -> Observation` implies single-shot execution, but the
   real FSM is incremental** (`h1_response_try_parse` returns `Incomplete` and is re-fed,
   `response_parser.rs:58`; socks returns `consumed` to advance an offset, `socks.rs:87`).
   Resolution: the adapter (not the trait signature) owns the feed loop and reports the run
   as a folded `Trace` of per-step tri-states — the signature stays single-call, the
   *observation* is a fold.
5. **`shared` breaks the uniform-execution assumption for `FormalModel`.** Iris
   logical-atomicity (ranks 5-7) is not extraction-executable as a runtime schedule
   enumerator, so `FormalModel.run_shared` is honestly `Absent`; the model contributes the
   invariant predicate at proof time, not a runtime `Observation`. `shared` is the one
   primitive where the formal leg cannot diff (§5).
6. **`ExternalOracle` is a server, not a sans-IO function.** The uniform four-method trait
   over-promises for it: only `region`/`machine`-via-wire are reachable; `linear`/`shared`
   are `Absent`, and even where Supported it observes no `arena_view`/`state_trace`. Uniform
   in *shape*, sparse in *content* for this backend (§4, §5).
7. **`Expectation::NwayAgree` is undefined when `<2` backends produce a field.** For a
   `region` `arena_view` (only `CurrentNet`+`FormalModel`+`GeneratedEngine` produce it) or a
   pre-engine `shared` vector (one producer), "agreement" is vacuous. The kit **rejects**
   `NwayAgree` at registration for such units and forces `Golden(...)` — closing a latent
   CR-6 footgun the spine's `expected` enum otherwise allows (§6).

---

( ⌐■_■ ) one corpus · four backends · the generated engine plugs in for free · the oracle
never touches the link set.
