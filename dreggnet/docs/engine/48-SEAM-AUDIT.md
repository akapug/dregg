# 48 — THE SEAM AUDIT (adversarial synthesis; the reconciled contract)

> **Status: AUTHORITATIVE over the spine details in 42–47.** Six design docs
> (`42-CONFORMANCE-KIT` adapter · `43-VECTOR-CORPUS` corpus · `44-DIFFERENTIAL-RUNNER`
> runner · `45-PERF-GATE-HARNESS` perf · `46-ADR-COMPILER-EMITS-ADAPTER` compiler ·
> `47-FUZZ-NET` fuzz) each specified Rust signatures against *its own reading* of the
> fixed seam spine. They do **not** all read it the same way. This file is the
> reconciliation: it finds every place two units assume an incompatible interface,
> says which unit yields and why, and pins the **one** `SutAdapter` + `Vector` +
> `Observation` all six must conform to. Where a seam only *appeared* to agree (same
> name, different shape; or a consumer reading a type the producer never finalized),
> it is surfaced, not smoothed over. ( ⌐■_■ )
>
> **Numbering note (resolves 47's open question).** North-Star unit numbers and the
> in-doc references in `42` disagree (`42` calls the corpus "unit 5"). This audit
> refers to units by **doc number** only: `42`=adapter, `43`=corpus, `44`=runner,
> `45`=perf, `46`=compiler, `47`=fuzz. The crate-authoring agent uses these.

---

## 1. How the six are *supposed* to weld (the load-bearing equalities)

The charge fixes three equalities the suite stands or falls on:

1. **Emitted adapter surface (`46`) ≡ expected adapter surface (`42`) ≡ what the
   runner calls (`44`) ≡ what vectors are keyed to (`43`).** One `SutAdapter`, one
   `Vector`, one `Observation`.
2. **Perf instrumentation contract (`45`) ≡ the compiler-emitted hooks (`46`).** The
   thing `compile(D)` hands the perf layer must be the trait the perf layer reads.
3. **Fuzz-as-vector (`47`) ≡ corpus (`43`) + runner (`44`).** A fuzz input is an
   un-golden `Vector` read straight through the runner's classifier.

All three are **violated in detail** by the as-written docs, even though every doc
*claims* to consume the spine verbatim. The violations are below.

---

## 2. Contradictions found, and the resolution

Severity tags: **STRUCTURAL** = the types do not compose and code would not link;
**SILENT** = same name / plausible prose but divergent shape, the dangerous kind;
**NAMING** = same concept, two names. Resolution names the yielding unit.

### C-1 (STRUCTURAL) — `Vector` is flat in `42`/`44`/`47`, split in `43`
`42` §6 and `44` (Consumes, line 665) and `47` (line 40, `Vector{ expected: … }`)
all read a **flat** record `Vector { id, primitive, unit, ledger_row, suite_case,
kind, input, spec, expected, acceptance }`. `43` §9 **restructures** it into
`Vector { core: VectorCore, meta: VectorMeta }` — hashed semantic core vs unhashed
reclassifiable keys — which is load-bearing for content-addressing (re-keying must
not change `VectorId`, `43` §2). **Resolution: `43` wins the record shape** (the
core/meta split is the whole replayability spine); `42`/`44`/`47` yield. The reconciled
`Vector` carries **accessor methods** (`unit()`, `primitive()`, `expectation()`,
`acceptance()`, `kind()`, `ledger_rows()`, `suite_cases()`) so the field-access prose
in `44`/`47` reads unchanged (`v.unit()` not `v.core.unit`). §4 pins it.

### C-2 (STRUCTURAL) — singular vs plural ledger/suite keys
`42`/`44` key `ledger_row: LedgerKey` / `suite_case: CaseKey` **singular**; `43`
§0/§9 pluralizes to `Vec<…>` because one curl replay covers both the parse row and
the response-writer row. **Resolution: plural** (`43` wins; a vector legitimately
covers ≥1 row). `44`'s `RowAccounting`/`coverage_gate` already fold per-row, so it
absorbs the plural with no logic change.

### C-3 (SILENT, dangerous) — `Observation::Produced` already has linear/shared fields, but `44` and `46` think it doesn't
`44` tension #1/#5 and `46` tension #3 both argue that `linear` (release-once) and
`shared` (linearizability) "have no dedicated field" and must be "smuggled into
`state_trace`." **That is stale.** `42` §2 (lines 153-154) **already added**
`linear_trace: Option<LinearTrace>` and `linearization: Option<Linearization>`. So
two units designed workarounds for a problem the keystone had already fixed — and
their `project_u` / `SharedProj` logic would have written to the wrong field.
**Resolution: `42` wins; the dedicated fields are authoritative.** `44`'s `LinearProj`
projects from `linear_trace`, `SharedProj` from `linearization`; `46`'s projection
theorem targets those fields directly (its tension #3 dissolves). The "smuggle into
state_trace" path is **deleted**, not kept as an alternative.

### C-4 (SILENT) — `Linearization` is too thin for the runner's predicate diff
Having won C-3, `42`'s `Linearization { order, invariant_held }` still does not carry
what `44` §2.4 needs: `SharedProj` requires `observed: OutcomeSet` and
`model_allowed: Option<OutcomeSet>` so the `Comparator::Predicate` can check
`observed ⊆ model_allowed`. **Resolution: `42` yields the payload**; the reconciled
`Linearization` is widened to `{ order, linearizable, invariant_held, observed,
model_allowed }`. The `FormalModel` fills `model_allowed`; non-model backends leave it
`None` (and the predicate degrades to "invariant held ∧ linearizable", never
byte-equality of `order` — `44` tension #1 stands and is correct).

### C-5 (STRUCTURAL) — two runner-output types: `Outcome` (3-way, `42`/`47`) vs `Verdict` (6-way, `44`)
`42` §3 defines `enum Outcome { Agree | Divergence | InsufficientProducers }` and `47`
**consumes `Outcome` by name** (lines 333, 396: `Differential(Outcome)`,
`Outcome::Divergence`, `Outcome::InsufficientProducers`). But `44` — the unit that
actually *is* the comparison engine — emits `enum Verdict { Agree | Divergence |
InsufficientWitnesses | RequiredBackendAbsent | RejectionEscaped | Malformed }` (a
total partition, asserted by `partition_is_total()`). `47` would not compile against
the real runner: it never handles `Malformed` / `RejectionEscaped` / `RequiredBackendAbsent`,
yet a fuzz input absolutely can produce all three. **Resolution: `44` wins the runner
output (`Verdict`); `42`'s `Outcome` is removed.** `47` yields: `FuzzOutcome::Differential`
wraps `Verdict`, and `RejectionEscaped`/`Malformed` are first-class fuzz findings (they
*are* bugs to freeze). `InsufficientProducers` → `InsufficientWitnesses` (naming unified
to `44`).

### C-6 (SILENT) — `DivergingField` (`42`) vs `FieldPath` (`44`)
`42` names the diverging field with a flat `enum DivergingField { Status, Headers,
Body, … }`; `44` names it with `enum FieldPath` carrying `Header(HeaderName)`,
`StateLabel{ step }`, `Emitted{ step }`, `ArenaTriple{ tag }`, etc. — strictly more
precise (per-step, per-header, per-tag). **Resolution: `44` wins (`FieldPath`);
`DivergingField` is removed.** A divergence that can only say "Headers diverge" instead
of "`Header("content-length")` diverges at the multiset level" is a regression the
runner explicitly designed away.

### C-7 (SILENT, dangerous) — **two** `ErrorClass` enums claim to be kit-owned
`42` §2.1: `ErrorClass { Smuggle(SmuggleKind) | Protocol(&str) | Reject{code,reason}
| Truncated | Oversized | Bomb }`. `44` §10: a *different* `ErrorClass { Smuggling(SmuggleClass)
| ProtocolError(ProtoCode) | FlowControl | HeaderListTooLarge | DecompressionBomb |
BadVarint | MalformedFrame | PathEscape | TlsDowngradeRefused | ReplayRejected |
Timeout(Phase) | Other }`. `47`'s `reject_equiv(&ErrorClass, &ErrorClass)` and `43`'s
`RejectSpec.error_class: Vec<ErrorClass>` both depend on *which one*. They are
incompatible. **Resolution: `44`'s enum wins** — it covers the transport/TLS/PKI
surfaces the 58-target fuzz inventory (`47` §4.1) actually needs, where `42`'s six
HTTP-shaped variants do not. `42` "owns the slot" but adopts `44`'s contents.
`SmuggleKind`(`42`)/`SmuggleClass`(`44`) unify to **`SmuggleClass`** with the six
`parsed_request.rs` `SmuggleViolation` names (`ContentLengthAndTransferEncoding`,
`DuplicateContentLength`, `ChunkedNotLast`, `NullByteInHeader`,
`UnsupportedTransferEncoding`, `InvalidContentLength`).

### C-8 (SILENT, dangerous) — `ObservedFields` (`42`, 9 flags) vs `ObsFieldSet` (`43`, 7 flags)
`42` §1 bitflags `ObservedFields` includes `LINEAR_TRACE | LINEARIZATION`; `43` §9's
`ObsFieldSet` (used by `Projection.fields` and `Acceptance`) **drops both**. `47`
consumes `ObservedFields` by name and leans on it being the canonical mask (§47.1 "no
`ObsMask` is needed"). A corpus `Projection` over `ObsFieldSet` literally cannot select
the `linear`/`shared` observation. **Resolution: one type, `ObservedFields` (9 flags),
spine-owned.** `43`'s `ObsFieldSet` is an alias that yields its name and gains the two
flags; `Projection.fields: ObservedFields`.

### C-9 (STRUCTURAL) — `MustReject` is a scalar in `42`, a predicate in `43`
`42`: `Expectation::MustReject { error_class: ErrorClass }` (one class). `43`:
`Expectation::MustReject(RejectPredicate)` where `RejectPredicate = Refuse(RejectSpec{
Vec<ErrorClass>, status_in, must_not: Vec<Effect> }) | Total(TotalityBound)`. `47`'s
fuzz totality net **requires** `Total(TotalityBound)` (no-panic / bounded mem+steps)
and security cases need the `must_not` egress obligations. `42`'s scalar cannot express
either. **Resolution: `43` wins (`RejectPredicate`); `42` yields.** `47`'s `reject_equiv`
operates over `ErrorClass` (unchanged) and its mint produces `Refuse{…}` or `Total{…}`.

### C-10 (STRUCTURAL) — perf `Expectation`: `Budget(PerfBudget)` (`43`) vs `MeetsGate{GateId}` (`45`) vs absent (`42`/`44`)
`42`/`44` give `Expectation` three variants (no perf). `43` adds a 4th
`Budget(PerfBudget)` (number inline). `45` instead proposes a 5th
`MeetsGate{ gate: GateId }`, pushing the number into a side `GateRegistry`/`BudgetFile`
because HW-tier numbers are silicon-relative and cannot be content-addressed (`45`
tension #6). **Resolution: a single 4th variant `Budget(GateRef)`** — the *shape* is
`43`'s (one `Expectation::Budget`, keeps the `Vector` self-contained) but the *payload*
is `45`'s indirection (`GateRef` = a `GateId` into the perf `GateRegistry`/`perf-budgets/*.toml`),
so HW-relative budgets and `env_tag` live in the ratcheted budget file, not in the
content-addressed core. Both yield half. (Rationale: an inline `PerfBudget` would force
the silicon-relative HW number into `VectorId`, which `45` tension #6 proves is
unsound; a bare `MeetsGate` with no `Budget` variant leaves `43`'s enum unable to round-trip
perf vectors.)

### C-11 (STRUCTURAL) — perf is "routed out, bypasses the diff" (`44`) but "retains the Observation and is still diffed" (`45`)
`44` §1 step 0: `Kind::Perf` "bypasses the diff engine entirely." `45` §3: `measure()`
**keeps** the functional `Observation`, which the runner **still diffs** — a fast wrong
answer is `GateOutcome::WrongAnswer`, a hard fail; "perf cannot launder a correctness
regression." These are directly opposed. **Resolution: `45` wins.** A `Kind::Perf`
vector runs the normal functional diff (correctness `Verdict`) **and** the budget gate;
green requires both. `44`'s "bypasses entirely" is wrong and yields — the perf channel
is *parallel*, not *exclusive*.

### C-12 (STRUCTURAL) — two perf outcome/gate types: `PerfGate`+`PerfOutcome` (`44`, 3-way) vs `GateRegistry`+`GateOutcome` (`45`, 5-way)
`44` §10 declares its own `trait PerfGate { evaluate(&Vector, &[&dyn SutAdapter]) ->
PerfOutcome }` with `PerfOutcome { Pass | ThresholdMissed | BaselineRegression }`. `45`
authors the actual perf layer: `GateRegistry::run_gate(…) -> GateOutcome { Met | Missed
| InstrumentAbsent | HwUnavailable | WrongAnswer }` over a `PerfSut`. `44`'s 3-way
outcome has no `InstrumentAbsent` (CR-6 launders a missing counter as a pass) and no
`HwUnavailable` (launders "no NIC in CI" as green). **Resolution: `45` wins the perf
surface; `44`'s `PerfGate`/`PerfOutcome` are removed.** `44`'s `DiffRunner` holds a
handle into `45`'s `GateRegistry` and surfaces `GateOutcome` on the `VectorReport`'s
parallel perf channel.

### C-13 (NAMING, dangerous) — the compiler-emitted hooks: `ArtifactInstrumentation` (`45`) vs `PerfHookTable` (`46`)
`46`'s `EmittedKitBundle.perf_hooks: PerfHookTable` references "unit-4's `PerfHookTable`
contract" — but `45` never defines `PerfHookTable`; it defines
`trait ArtifactInstrumentation`. The thing the compiler emits and the trait the perf
layer reads have **different names** and would not connect. **Resolution: `45` owns the
contract; the name is `ArtifactInstrumentation`.** `46` yields:
`EmittedKitBundle.perf_hooks: Box<dyn ArtifactInstrumentation>`. (The PF-6 gate-dominance
property both docs assert — `22-PERF:107-116` — genuinely agrees; only the name was
split.)

### C-14 (STRUCTURAL) — `supports(unit)` (single-arg, `44` prose; `realized_units` per-unit, `46`) vs `supports(unit, prim)` (`42`/`47`)
`42` §1 widened support to per-`(unit, primitive)` (the oracle supports `region` but not
`linear` for the *same* unit). `47` consumes the wide form correctly. But `44` §1 step 1
still writes `supports(vector.unit)` (single-arg), and `46`'s `realized_units(&self) ->
&[UnitId]` (per-unit) drives `supports()` — neither can express "this unit, but not its
`linear` primitive." **Resolution: `42` wins (`supports(unit, prim)`).** `44` yields
(pass the primitive). `46` yields: `realized()` returns **`&[(UnitId, Primitive)]`**, and
the `GeneratedEngine`'s `supports()` consults that pair-set rather than `42`'s blanket
`ObservedFields::all()` (which `42`'s own open question already flags as wrong for partial
early emissions). This also fixes C-15.

### C-15 (SILENT) — `GeneratedAdapter` blanket `supports() => ObservedFields::all()` (`42` §7) vs realized-set-driven (`46`)
`42` §7's `GeneratedAdapter<U: DslUnit>` blanket-impls `supports() => Supported{ observes:
ObservedFields::all() }`, "by the compiler-correctness theorem." `46` §Independence and
`42`'s own open question both say this is unsound for partial emissions (an early engine
realizing `region` but not `shared` for a unit would falsely claim `LINEARIZATION`).
**Resolution: `46`'s realized-set discipline wins.** `DslUnit` exposes a per-primitive
capability (`fn realizes(p: Primitive) -> Option<ObservedFields>`); `GeneratedAdapter`'s
`supports()` returns that, never blanket `all()`. The `GeneratedAdapter`/`DslUnit`
codegen hook (`42`) and the `EmittedKitBundle`/`ProvenancedAdapter` cert (`46`) are the
**same emission**: `GeneratedAdapter<U>` *is* the `Box<dyn ProvenancedAdapter>` in the
bundle, with `provenance() = CompilerEmitted(cert)`.

### C-16 (STRUCTURAL) — the runner holds `&dyn SutAdapter`, but independence (`46`) and perf (`45`) need richer trait objects
`44`'s `DiffRunner.backends: Vec<&dyn SutAdapter>`. `46` requires the runner to call
`nway_has_independent_witness(agreeing: &[AdapterProvenance])` before crediting an
`Agree` as coverage — an **all-emitted** agreement is non-independent and must score
zero. A bare `&dyn SutAdapter` cannot yield provenance, so `44` as-written would credit
a compiler-monoculture agreement. Separately `45` needs `&dyn PerfSut`. **Resolution:
the runner holds `&dyn ProvenancedAdapter`** (= `SutAdapter` + provenance; `46` wins the
base trait object). `PerfSut: ProvenancedAdapter` is an *optional* capability the
`GateRegistry` downcasts to. `44` yields: `Verdict::Agree` ⇒ `counts_as_coverage` **only
if** `nway_has_independent_witness` holds over the agreeing set — the independence gate
becomes a hard precondition of coverage, not an afterthought.

### C-17 (STRUCTURAL) — `FormalModel` is a `SutAdapter` (`42`/`44`) but emitted as a bare `ModelBridgeFn` (`46`)
`44` calls every backend, `FormalModel` included, through `&dyn SutAdapter`. `46` emits
the model leg as `type ModelBridgeFn = fn(UnitId, Primitive, &Input, &Spec) ->
Observation` — a free function over the *untyped* `Input` sum, not a four-method adapter.
**Resolution: both are right at different layers.** `46`'s `ModelBridgeFn` is the
*extraction* signature `compile(D)` produces; the kit wraps it in a `FormalModelAdapter:
ProvenancedAdapter` whose four methods dispatch the typed args back into `&Input` and
call the `ModelBridgeFn` (`provenance() = ModelExtracted{…}`). The runner sees uniform
`&dyn ProvenancedAdapter`; the bundle ships the bare fn. No type loses; the wrapper is named.

### C-18 (STRUCTURAL) — `Event` is opaque `struct Event(Bytes)` (`42`) but needs a `Timer`/`VirtualClock` variant (`43`/`44`)
`42` §2.1 makes `Event` an opaque byte wrapper "refined by unit 3." But `43` §3 needs
`Event::TimerTick` (timeouts as input) and `44` tension #8 needs `Event` to carry a
`VirtualClock` tick so the `FormalModel` injects clock ticks while `CurrentNet` reads a
real clock — otherwise timeout transitions diverge spuriously. An opaque `Bytes` cannot
hold a typed tick. **Resolution: `Event` is an enum** `{ Wire(Bytes), Timer(VirtualClock)
}` (machine-unit may extend), spine-hosted. `42` yields the opaque form.

### C-19 (SILENT) — two `AbsentReason` enums (`44` cell-scope vs `46` backend-scope) + free-text String (`42`)
`42` uses `reason: String` on both `Support::Absent` and `Observation::Absent`. `46`
proposes typed `AbsentReason { EngineNotYetEmitted | ProjectionClauseUndischarged | … }`
for the **backend** absence (so the CR-6 classifier cannot mis-bucket an *unproven*
adapter as a benign skip). `44` independently defines `AbsentReason { TriStateIncomplete
| FieldNotProduced | NotApplicableToBackend }` for **cell** absence (`Cell::Absent`).
Same name, different scope, different variants. **Resolution: split by scope, both
adopted, renamed to avoid the collision.** Backend/observation absence →
`BackendAbsentReason` (`46`'s variants); cell/field absence → `CellAbsentReason` (`44`'s
variants). `42`'s free-text `String` yields to `BackendAbsentReason` (its open question
about laundered mis-bucketing is thereby closed).

### C-20 (SILENT) — resource/cost side-channel: `45`'s `InstrumentReadings` vs `47`'s `ResourceSample`, both escaping `Observation`
`42`'s `Observation` is value-only (no cost). `45` adds `InstrumentReadings`
(alloc/cycle/syscall/…, all-`Option`) wrapped in `MeasuredObservation`. `47` *separately*
adds `ResourceBudget`/`ResourceSample` (wall, peak_rss, expansion) for fuzz totality.
These overlap (`peak_rss` ≈ `AllocReading.peak_bytes`) and are two parallel cost
side-bands for one conceptual channel. **Resolution: one side-band.** `45`'s
`MeasuredObservation { observation, readings, env }` is the canonical cost channel;
`47`'s `ResourceSample` is the **fuzz-facing projection** of `InstrumentReadings`
(`wall` and `expansion` are added as fields of `InstrumentReadings`, `peak_rss` aliases
`AllocReading.peak_bytes`). `47` yields the standalone struct; the spine acknowledges
**measurement as a first-class side-channel beside `Observation`**, never inside it
(keeping `VectorId` correctness-only). This is the one genuine spine *extension* all of
`44`/`45`/`47` were independently reaching for.

---

## 3. Seams that genuinely agree (verified, not assumed)

- **Tri-state parse class.** `42`'s `ParseClass`, `44`'s `StepTag`, `43`'s `Input`
  notes, `46`/`47`'s `ParseClass` reference all bottom out in the same
  `Complete{consumed} | Incomplete | Error` (`socks.rs:84-92`,
  `response_parser.rs:41-49`). Real agreement.
- **Arena model.** `ArenaView` + `(name_tag, off, len)` triples + sidecar at
  `SIDECAR_OFFSET_BASE=0x8000_0000` + `wf_parsed_request` is read identically by `42`,
  `43`, `44`, `46` (`parsed_request.rs:685`, `21-FORMAL:19-27`). Real agreement.
- **CR-6 two-granularity firewall.** `42` §3 (backend-level `Absent` + field-level
  `ObservedFields` intersection) is consumed verbatim by `47` §47.3 and is compatible
  with `44`'s `wf-gate` + quorum (the wf-gate *adds* a third closure — "agree on
  garbage" — that the others do not contradict). Real agreement, with `44`'s `Malformed`
  as a strict additive hardening.
- **CR-3 oracle firewall.** `42` `OracleHandle` / `46` `engine_link_set_excludes_oracle`
  / `47` "Elide read via IPC, never linked" / `45` "never co-linked." Real agreement.
- **PF-6 gate-dominance.** `45` §2 (probes PF-6-gated) and `46` (emitted hooks
  gate-dominated) cite the same `22-PERF:107-116` and mean the same property. Agreement
  (only the trait *name* split — C-13).

---

## 4. THE RECONCILED CONTRACT (authoritative)

All six units conform to exactly these signatures. Where a doc's prose contradicts
this, **this file governs.**

```rust
// ===================== net/conformance-kit :: the reconciled spine =====================
// Owns: identity/keys, SutAdapter (+ ProvenancedAdapter, + PerfSut), Observation,
// ObservedFields, ErrorClass, Event, the runner Verdict, the absence taxonomies.
// The Vector record is owned by 43 (corpus) and shown here in its reconciled shape.

// ---- identity & keys (spine) ----
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] pub struct UnitId(pub &'static str);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] pub enum Primitive { Region, Machine, Linear, Shared }
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] pub enum BackendId { CurrentNet, ExternalOracle, FormalModel, GeneratedEngine }
impl BackendId {
    /// C-16/C-from-46#4: the emitted/non-emitted partition is spine-visible, so
    /// `nway_has_independent_witness` is not re-deriving it ad hoc.
    pub fn is_emitted(self) -> bool { matches!(self, BackendId::FormalModel | BackendId::GeneratedEngine) }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct LedgerKey(pub &'static str);
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct CaseKey(pub &'static str);
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)] pub struct ContentHash([u8; 32]);
pub enum Kind { Conformance, Behavioral, Security, Perf, Differential }

// ---- the universal adapter surface (C-14: per-(unit, primitive) support) ----
pub trait SutAdapter {
    fn backend(&self) -> BackendId;
    fn supports(&self, unit: UnitId, prim: Primitive) -> Support;          // C-14
    fn decode_region(&self, unit: UnitId, input: &[u8], spec: &Spec) -> Observation;
    fn run_machine (&self, unit: UnitId, spec: &Spec, events: &[Event]) -> Observation;
    fn run_linear  (&self, unit: UnitId, ops: &[ResourceOp]) -> Observation;
    fn run_shared  (&self, unit: UnitId, schedule: &Schedule) -> Observation;
}
pub enum Support {
    Supported { observes: ObservedFields },
    Absent    { reason: BackendAbsentReason },                             // C-19 (typed, not String)
}

// ---- the trait object the RUNNER actually holds (C-16, C-17) ----
pub trait ProvenancedAdapter: SutAdapter {
    fn provenance(&self) -> AdapterProvenance;
    fn cert(&self) -> Option<&EmittedAdapterCert>;
    fn realized(&self) -> &[(UnitId, Primitive)];                          // C-14/C-15: per-(unit,primitive)
}

// ---- optional perf capability (C-12, C-16): the GateRegistry downcasts to this ----
pub trait PerfSut: ProvenancedAdapter {
    fn instruments(&self, unit: UnitId) -> ProbeSupport;
    fn measure(&self, unit: UnitId, run: &PerfRun) -> MeasuredObservation; // C-11: RETAINS Observation
    fn static_query(&self, unit: UnitId, q: StaticQuery) -> StaticAnswer;
}

// ---- observed-field mask (C-8: ONE type, 9 flags, spine-owned; 43's ObsFieldSet is an alias) ----
bitflags::bitflags! {
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct ObservedFields: u16 {
        const STATUS=1<<0; const HEADERS=1<<1; const BODY=1<<2; const ARENA_VIEW=1<<3;
        const STATE_TRACE=1<<4; const ERROR_CLASS=1<<5; const CONSUMED=1<<6;
        const LINEAR_TRACE=1<<7; const LINEARIZATION=1<<8;
    }
}

// ---- the Observation (C-3: dedicated linear/shared fields are authoritative) ----
pub enum Observation { Produced(Produced), Absent { reason: BackendAbsentReason } }
pub struct Produced {
    pub fields:        ObservedFields,           // which Option<_> below carry signal
    pub status:        Option<Status>,
    pub headers:       HeaderSet,                // C-7-adjacent: dup-preserving multiset, lc names, sorted
    pub body:          Bytes,
    pub arena_view:    Option<ArenaView>,        // region
    pub state_trace:   Option<Trace>,            // machine
    pub error_class:   Option<ErrorClass>,
    pub consumed:      Option<usize>,            // Absent (None) under tri-state Incomplete
    pub linear_trace:  Option<LinearTrace>,      // linear (NOT smuggled into state_trace — C-3)
    pub linearization: Option<Linearization>,    // shared (NOT smuggled into state_trace — C-3)
}
// C-4: widened so 44's SharedProj predicate diff has its inputs.
pub struct Linearization {
    pub order:         Vec<OpId>,
    pub linearizable:  bool,
    pub invariant_held: bool,
    pub observed:      OutcomeSet,
    pub model_allowed: Option<OutcomeSet>,       // FormalModel fills; others None
}

// ---- absence taxonomies, split by scope (C-19) ----
pub enum BackendAbsentReason {                   // Support::Absent / Observation::Absent  (from 46)
    EngineNotYetEmitted,
    ProjectionClauseUndischarged { unit: UnitId },
    PrimitiveNotApplicable,
    ObservationModeTooNarrow { have: ObservationMode },
    OracleRefused { detail: String },
}
pub enum CellAbsentReason { TriStateIncomplete, FieldNotProduced, NotApplicableToBackend } // Cell::Absent (from 44)

// ---- ONE error taxonomy (C-7: 44's enum wins, spine-hosted) ----
pub enum ErrorClass {
    Smuggling(SmuggleClass), ProtocolError(ProtoCode), FlowControl,
    HeaderListTooLarge, DecompressionBomb, BadVarint, MalformedFrame,
    PathEscape, TlsDowngradeRefused, ReplayRejected, Timeout(Phase), Other(SmolStr),
}
pub enum SmuggleClass {                           // the six parsed_request.rs SmuggleViolation names
    ContentLengthAndTransferEncoding, DuplicateContentLength, ChunkedNotLast,
    NullByteInHeader, UnsupportedTransferEncoding, InvalidContentLength,
}

// ---- Event is an ENUM (C-18): wire bytes OR a virtual-clock tick ----
pub enum Event { Wire(Bytes), Timer(VirtualClock) }
pub struct VirtualClock(pub u64);

// ---- the runner output (C-5/C-6: Verdict + FieldPath win; Outcome + DivergingField removed) ----
pub enum Verdict {
    Agree                 { witnesses: usize },          // counts_as_coverage iff independence holds (C-16)
    Divergence            { primary: FieldPath, fields: Vec<FieldDivergence>, security: bool },
    InsufficientWitnesses { present: usize, required: usize },
    RequiredBackendAbsent { backend: BackendId, reason: BackendAbsentReason },
    RejectionEscaped      { accepting: Vec<BackendId>, minimal_repro: Option<MinimalRepro> },
    Malformed             { backend: BackendId, violation: WfViolation },
}
// FieldPath / FieldDivergence / Clustering / Cell (with CellAbsentReason) / Projector /
// Comparator / BackendApplicability / WfViolation / Minimizer / MinimalRepro
// are exactly as in 44 §10 (authoritative there). `42`'s `Outcome`/`DivergingField` are deleted.

// ---- the Vector record (C-1/C-2/C-9/C-10: 43 owns the shape; accessors keep 44/47 prose valid) ----
pub struct Vector { pub core: VectorCore, pub meta: VectorMeta }   // 43 §9 authoritative
impl Vector {
    pub fn unit(&self) -> UnitId;
    pub fn primitive(&self) -> Primitive;
    pub fn expectation(&self) -> &Expectation;
    pub fn acceptance(&self) -> &Acceptance;
    pub fn kind(&self) -> Kind;
    pub fn ledger_rows(&self) -> &[LedgerKey];     // C-2: plural
    pub fn suite_cases(&self) -> &[CaseKey];       // C-2: plural
    pub fn compute_id(&self) -> VectorId;          // hash of core only (43 §2)
    pub fn verify_id(&self) -> Result<(), IdMismatch>;
}
pub enum Expectation {                              // C-9/C-10: 4 variants
    Golden(GoldenRef),
    NwayAgree,
    MustReject(RejectPredicate),                    // C-9: predicate, not scalar
    Budget(GateRef),                                // C-10: ref into 45's GateRegistry/BudgetFile
}
pub struct GateRef(pub GateId);                     // 45 owns GateId + the number
// VectorCore { format, primitive, unit, input, spec: SpecRef, expect, acceptance, replay }
// VectorMeta { id, kind, ledger_rows: Vec<LedgerKey>, suite_cases: Vec<CaseKey>, provenance, .. }
// Acceptance { projection: ProjectionRef, quorum: Quorum }   // 43 §9 authoritative (struct, not enum)
// Input { Bytes(InputHash) | EventSeq(Vec<Event>) | ResourceOps(Vec<ResourceOp>) | Schedule(Schedule) }
//   -- stored form; the runner resolves to ResolvedInput before calling SutAdapter (decode_region
//      takes &[u8], run_machine takes &[Event], etc.). Spec likewise: SpecRef in the core,
//      resolved to &Spec at the call boundary.
```

**Spec / SpecRef boundary (resolves the only non-contradiction friction, H).** The
`Vector` stores `spec: SpecRef { Inline(Spec) | Cas(SpecId) }` (`43`); the runner
resolves it to `&Spec` before dispatch. The adapter surface takes resolved `&Spec` /
`&[u8]` / `&[Event]`, never the stored sum. `Spec`'s dCBOR `Canonical` impl is owned by
the spec/orchestrator unit and gates `VectorId` stability (`43` open question — still open).

---

## 5. Residual open questions (not resolved by reconciliation)

1. **`Spec` canonicalization owner.** `VectorId` stability needs a frozen dCBOR
   `Canonical` impl for `Spec`, owned by the spec/orchestrator unit, which does not yet
   exist. Until pinned, every `VectorId` referencing a `Spec` is at risk of drift
   (`43` open q). Not a seam contradiction — a missing unit.
2. **dCBOR cross-language determinism.** The JVM (Elide) and CakeML (model) recompute
   of `VectorId` (`43` §2) presumes a dCBOR impl whose canonicalization provably matches
   across all three languages. This is itself a conformance obligation and may warrant
   its own ledger row (`43` open q).
3. **`HeaderSet` canonical form, now pinned-as-decided but not specified.** This audit
   fixes "dup-preserving multiset, lowercased names, sorted by (name, value)" (C-7
   adjacent), but the exact multi-value join / obs-fold rule for `Header(name)` cells
   under `Comparator::HeaderMultiset` must be written by the corpus/spec unit before
   cross-backend equality is byte-deterministic.
4. **Constructive simulation witness `R`.** `46`'s faithful-projection clause assumes
   the compiler-correctness proof materializes `R` *executably* (so `obs_M = obs_Φ ∘ R`
   runs). Where a refinement is non-constructive, the emitted adapter needs a separate
   executability obligation (`46` tension #6). A proof-engineering open item, not a
   type seam.
5. **A fifth emitted backend would shift the independence math.** `is_emitted()` (added
   here, C-16) makes the partition spine-visible, but `nway_has_independent_witness`
   and `44`'s `BackendApplicability::ZeroCopyLayout = {CurrentNet, FormalModel,
   GeneratedEngine}` both still *enumerate* backends. Adding a backend means editing
   both sites; nothing yet forces that edit. Left as a known maintenance coupling.
6. **`exec_cost` / `CostClass` for the fuzz scheduler** (`47` tension #1). The
   out-of-process Elide oracle cannot ride the 10⁴–10⁶ exec/s mutation loop. This audit
   does **not** add `SutAdapter::exec_cost()`; the fuzz scheduler carries cost-class
   out-of-band in the `FuzzTarget` registry (`47` may keep it local) until there is a
   second out-of-process backend that would justify spine-hosting it.
7. **`oracle_dark_rows` derivability** (`44` open q). Whether "a row the oracle/model
   *could* witness but didn't" is mechanically derivable or needs a per-row capability
   annotation in the `40-LEDGER` / the `realized()` table. The reconciled `realized() ->
   &[(UnitId, Primitive)]` makes it *more* derivable but does not fully close it.

---

## 6. Verdict

The six docs **do not** silently agree — they share a vocabulary while diverging on
record shape (Vector flat-vs-split), output type (Outcome-vs-Verdict), error taxonomy
(two `ErrorClass`), field mask (two bitflag types), perf routing (bypass-vs-retain),
perf outcome (two enums), the emitted-hook name (`PerfHookTable`-vs-`ArtifactInstrumentation`),
support arity (`supports(unit)`-vs-`supports(unit,prim)`), and absence reasons (two
`AbsentReason` + free-text). The most dangerous were the **silent** ones: `44`/`46`
designing `state_trace`-smuggling workarounds for `linear`/`shared` fields the keystone
had *already added* (C-3), and `47` consuming an `Outcome` type the real runner never
emits (C-5). Twenty contradictions are reconciled into one `SutAdapter` (held as
`ProvenancedAdapter`, perf-extended by `PerfSut`), one `Vector` (`43`'s core/meta split
with accessors), one `Observation` (dedicated linear/shared fields, widened
`Linearization`, typed absence), one runner `Verdict`/`FieldPath`, one `ErrorClass`, one
`ObservedFields`, an enum `Event`, and a single measurement side-channel beside (never
inside) `Observation`. Each yield is to the unit that **owns** the surface: `43` for the
record, `44` for the comparison engine, `45` for perf, `46` for provenance/emission,
`42` for the adapter shape and the field-granular CR-6 mask. Seven residual open
questions remain — all of them *missing units* or *proof obligations*, none of them
unresolved type seams.

( ⌐■_■ ) one corpus · one adapter · one observation · the generated engine still plugs
in for free — and now it links.
