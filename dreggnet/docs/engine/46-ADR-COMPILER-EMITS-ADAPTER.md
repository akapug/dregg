# 46 — ADR: THE VERIFIED COMPILER EMITS THE CONFORMANCE ADAPTER

*Status: **PROPOSED** (keystone). Inherits CR-1…CR-6 (`00-CHARTER.md`) and ADR-1/3/4/7
(`10-DECISIONS.md`). Serves the conformance/perf kit's "fourth-consumer" thesis
(North Star) and welds the proof gate to the test gate.*

---

## Context

The engine is **one source → three outputs**. A DSL description `D` over four
primitives — `region`/`view` · `machine` · `linear` · `shared` (ADR-7,
`10-DECISIONS.md:53-58`) — is lowered by **a verified compiler we own** (CR-4,
`00-CHARTER.md:66-70`) which *"emits, all three from one description"*: **(1)** line-rate
machine code, **(2)** the formal model (HOL4/Isabelle), **(3)** ~90% of the proofs, the
routine obligations auto-discharged (`20-ARCHITECTURE.md:24-30`). The compiler is the
*"proof-producing translator"* whose correctness theorem *"turns the routine per-instance
obligations into consequences of the compiler-correctness theorem"*
(`20-ARCHITECTURE.md:44-48`). Formal-first is non-negotiable: we *"never hand-write an
implementation and verify it after the fact"* (CR-1, `00-CHARTER.md:39-42`).

The conformance/perf kit (the North Star; `41-TEST-AND-PERF-SUITE.md`) is the
**fourth consumer** of that *same* `D`. Its load-bearing surface is the **sans-IO core**
`(state, bytes) → (state', events, out)` (`20-ARCHITECTURE.md:170`) — which already exists
as a *convention* in today's code: parsers uniformly return the tri-state
`ParseResult<T> { Complete{value, consumed} | Incomplete | Error }`
(`net/httpe/src/protocol/socks.rs:84-89`, `net/httpe/src/cq/response_parser.rs:43-47`), and
the `region`/`view` observable is the flat-arena + `(name_tag, off, len)` representation
with the high-bit sidecar union `SIDECAR_OFFSET_BASE = 0x8000_0000`
(`net/httpe/src/parsed_request.rs:685`; model `wf_parsed_request`,
`21-FORMAL-MODEL.md:19-27`). The kit runs **ONE** content-addressed corpus of vectors
(`harness/vector-corpus-format`, `41-TEST-AND-PERF-SUITE.md:325`) against **FOUR** backends
through a uniform `SutAdapter`:

- `CurrentNet` — the hand-written baseline (oracle backend #1; a swappable control, **NOT**
  the system under test);
- `ExternalOracle` — the internal Elide HTTP-engine source tree, **out-of-process**, read via subprocess/IPC,
  **never linked** (CR-3, `00-CHARTER.md:58-64`; `harness/oracle-provenance-firewall`,
  `41-TEST-AND-PERF-SUITE.md:332-333`);
- `FormalModel` — the HOL4/CakeML-extracted runnable function
  (`harness/executable-model-bridge`, `41-TEST-AND-PERF-SUITE.md:334-335`);
- `GeneratedEngine` — **does not exist yet** (first stone is roadmap R1.1, the
  `region`/`view` pass lowering to CakeML/Pancake with a preservation theorem).

The three-way runner diffs `(status, header-set, body, arena byte-view, error-class)` and
**fails on any pairwise divergence** (`41-TEST-AND-PERF-SUITE.md:328-331`); the
non-vacuity gate (CR-6) forbids counting an oracle/model *skip* as a match
(`41-TEST-AND-PERF-SUITE.md:336-338`).

**The unanswered question this ADR settles:** *where does the `SutAdapter` for the
generated engine come from?* — the thing that marshals a `Vector` into engine calls and
reads engine state/output back into an `Observation`. If it is **hand-written per
artifact**, that adapter is a second, *unproven* transcription of "how to call this engine
and read its state," and it sits **inside the CR-6 arbiter itself**.

---

## The defect a hand-written adapter introduces

A per-artifact adapter is the `impl-first-bolt-on-proof` shape CR-1 outlaws, reincarnated
at the test boundary. A hand adapter maintains two hand-edited mappings — marshal
`Input → engine calls`, and read `engine state/output → Observation` — and the failure
modes are concrete:

1. **Wrong entry point.** The adapter drives a debug/convenience path rather than the
   proven run-to-completion entry. Then *the thing tested ≠ the thing proven*: the proof is
   about `M`, the test exercises `M'`. Silent.
2. **Wrong readout, drifting toward laundered vacuity.** When the engine evolves (a new
   `arena_view` field, a renamed FSM state in `state_trace`, a changed `error_class`
   variant), a human updates the read-back mapping *by reading the current engine* — i.e.
   edits the adapter to make the differential go green, teaching it the engine's **new**
   behavior even when that new behavior is the bug. The differential then passes because the
   adapter was taught to mirror the buggy engine. At that moment the test no longer
   witnesses the proof; it witnesses the adapter-author's belief about the engine. That is
   **laundered vacuity at the adapter layer** (CR-6, `00-CHARTER.md:81-86`) — the precise
   bug the suite exists to prevent.
3. **Lying `supports()`.** A hand-written `supports(unit)` is a *guess*; marking an
   unrealized unit `Supported` counts a vacuous pass.

A hand-written adapter is therefore **unnamed trusted glue inside the validation TCB** —
which CR-2's honesty clause classes as an `unnamed-trusted-engine` violation
(`00-CHARTER.md:50-56`), not a mere convenience.

---

## Decision

**The verified compiler emits the conformance adapter — a fourth output group, from the
same `D`, under the same correctness theorem.** Concretely, `compile(D)` additionally emits,
per realized DSL unit, an **`EmittedKitBundle`** keyed to the *same* `DslUnitHash` as the
`{code, model, proofs}` triple, carrying:

- **(i) the generated-engine `SutAdapter` shim.** A thin **generated** marshalling layer:
  `Vector.input → engine-ABI call → engine-observable → Observation`. Both endpoints are
  compiler artifacts; the entry points it drives **are** the engine's hot-path entry points
  (same codegen, same symbols); the state it reads **is** the observable projection defined
  in the formal model. It is `obs_Φ ∘ (decode-and-run)` made executable — a *projection*,
  not a re-description. Its `Observation` codomain is fixed to the model projection's range,
  so it **structurally cannot describe an observable the core does not produce**.

- **(ii) the formal-model bridge** (`ModelBridgeFn`). The CakeML-extracted runnable
  `obs_Φ ∘ step_Φ` the differential runner calls as backend (c). Because `Φ(D)` is *already*
  a compiler output (`20-ARCHITECTURE.md:27`) and the HOL4→CakeML path gives verified
  extraction (ADR-3, `10-DECISIONS.md:24-32`), the *"each modeled row's HOL4 theory is
  extractable to a runnable function; non-extractable = fail"* obligation
  (`41-TEST-AND-PERF-SUITE.md:334-335`) becomes a **compiler obligation**: a well-formed
  unit is extractable by construction.

- **(iii) the perf-instrumentation hooks** (unit-4's `PerfHookTable` contract). The compiler
  knows the run-to-completion lowering (`22-PERFORMANCE.md:132`), so it brackets the *actual*
  per-packet span rather than an arbitrary point, and emits the probes **gate-dominated** so
  PF-6 (*"the probe body is unreachable when the gate is false"*, `22-PERFORMANCE.md:107-116`)
  makes the measured binary bit-identical to the shipped one modulo a proven-dead branch —
  the only way to honor *"the perf was achieved by verified means — the generated code on the
  hot path is the same artifact as the proven one"* (`22-PERFORMANCE.md:148-151`).

The **`ExternalOracle` adapter stays hand-written and wire-level** — we do not own its compiler,
and CR-3 forbids linking it, so it can only be *read*. Its observation gaps are reported
`Absent`, never laundered. The asymmetry is principled: **you emit the adapter for the
artifact you compile; you hand-write a wire adapter for the artifact you can only read.**
`CurrentNet` likewise stays hand-written **by design** — it is the deliberate non-emitted
control (see Independence, below).

---

## The formal core — what the correctness theorem must add, and why no axiom is smuggled in

Let the existing compiler-correctness theorem be the refinement

> ⟦machine_code(D)⟧ ⊑ Φ(D),  witnessed by a simulation relation `R` (engine-state `s`
> simulated by model-state `σ`, written `s ~R~ σ`).

Define `obs_Φ : ModelState → ModelObservable` — the canonical projection onto the kit's
`Observation::Produced` record `(status, headers, body, arena_view, state_trace,
error_class, consumed)`. For `region`/`view` this is exactly the Rank-1 arena observable
(`21-FORMAL-MODEL.md:19-27`); for `machine` it is the tri-state step output
`Complete{value,consumed} | Incomplete | Error`
(`net/httpe/src/cq/response_parser.rs:43-47`, `net/httpe/src/protocol/socks.rs:84-89`).

**The one new clause — the faithful-projection obligation.** For the emitted adapter `A_u`
of unit `u`:

```
∀ admissible i.   A_u.observe( run(artifact_u, i) )  =  lift( obs_Φ( step_Φ(u, decode(i)) ) )
```

i.e. the adapter **projects, it does not recompute** — it commutes the refinement square
(run on `M`, then read out) with (decode, step on `Φ`, then project). Composed with the
*existing* refinement `run(artifact_u) ⊑ step_Φ`, this yields

```
A_u.observe(run(artifact_u, i))  =  lift(obs_Φ(model_run(i)))  =  ModelBridgeFn(u, …, i)
```

— **the `GeneratedEngine` and `FormalModel` observations are equal by theorem, not by
coincidence.**

**Why this adds no new axiom — it is a corollary.** The refinement already supplies `R`:
every reachable engine state is simulated by a model state. Define `obs_M := obs_Φ ∘ R`
(read the engine state, map it through the simulation witness, project). `obs_M` is
computable from artifacts the proof *already produced* — `R` is the very thing the
compiler-correctness proof constructs. So the faithful-projection clause **reuses the
simulation witness**; it does not assume a new fact about the world. We *extend the theorem*
(prove more), we do **not** *extend the axiom set* (assume more). The clause has two halves:
**(a) faithfulness** (the equation above) and **(b) observation-purity** — observing must
not perturb the engine onto a different code path; this is the same property PF-6 already
checks for taps (the readout, like the disabled tap, is a gate-dominated pure projection,
`22-PERFORMANCE.md:107-116`). The clause is registered as **one more routine obligation
class** alongside in-bounds / totality / determinism / `wf`-preservation / exactly-once
(`21-FORMAL-MODEL.md:299-302`); the residual is small and structural.

**TCB impact — it narrows, not widens.** The compiler was *already* trusted (CR-4). Adding
one more emitted artifact under the same correctness theorem reuses the existing trust anchor
and introduces **no new axiom**. Against the hand-written baseline this is strictly better:
the adapter moves from *unbounded trusted glue inside the CR-6 arbiter* to *verified compiler
output*. The **only** residual trusted surface is a single shared, total, decidable
`lift : ModelObservable → Observation` marshalling — *one* `lift`, shared across all units and
backends, **not** one-per-artifact. It is named here per CR-2's honesty clause; ideally it too
is emitted/verified, in which case the trusted residual is empty.

**CR-6 becomes a compile-time fact, and a localizer.** `realized_units()` is **derived from
`D`**, so the generated-engine adapter reports `Supported` for exactly the units `D` realizes
and `Absent` otherwise — it **structurally cannot** mark an unrealized unit `Supported`.
Non-vacuity stops being a runtime hope (did the hand `supports()` tell the truth?) and becomes
a property of the emission. Further, the proof gate and the test gate are **welded** through
`supports()`: an emitted adapter is `Supported` for `u` **iff** its bundle was emitted, which
requires the projection clause to discharge. No proof ⇒ no bundle ⇒ `Absent {
ProjectionClauseUndischarged{u} }` — which the CR-6 classifier
(`harness/diff-nonvacuity-gate`, `41-TEST-AND-PERF-SUITE.md:336-338`) counts as
backend-absent, never a pass. **You cannot launder an unproven adapter into coverage.** And a
red differential becomes a *trusted localizer*: the projection theorem eliminates the adapter
as a suspect, so a divergence is an artifact refinement bug or a vector bug — never harness
noise. The hand-adapter world has three suspects (engine / adapter / vector); the emitted
world has two.

---

## Independence — the residual risk is compiler monoculture, addressed head-on

Both `FormalModel` (via `ModelBridgeFn`) and `GeneratedEngine` are compiler-emitted, so their
agreement is the **executable shadow of the refinement proof** — near-tautological where the
refinement is complete, and valuable chiefly at the **named-axiom boundaries** (F-6 QUIC, F-12
TLS-record/H2; CR-2 honesty clause, `00-CHARTER.md:50-56`) where the residual is carried by
the continuous fuzz-net (`41-TEST-AND-PERF-SUITE.md:349-357`). Critically, a **common-mode
compiler bug** could corrupt artifact + model + adapter *consistently*; an N-way "agreement"
among emitted-only backends would then be vacuous.

Mitigation is **mandatory, not optional.** The two **non-emitted** backends — `CurrentNet`
(hand-written baseline) and `ExternalOracle` (out-of-process, never-linked, CR-3) — are the
independent witnesses. The runner MUST call `nway_has_independent_witness(agreeing)`: a unit
whose agreement set is **entirely compiler-emitted** is flagged **non-independent** and does
**not** count toward coverage. The emitted adapter removes per-artifact drift; the non-emitted
witnesses remove compiler-monoculture risk; they are **complementary**, and CR-6 forbids
dropping either. This is why `CurrentNet` and `ExternalOracle` are kept alive for the life of the
project — they are *not* scaffolding to delete once the engine exists.

---

## Bootstrapping — the kit works TODAY with zero engine, then gains the adapter for free

The engine does not exist (roadmap Phase 0 / R1.1). The ADR is realized incrementally and the
kit's **shape never changes** — only the `supports()` matrix fills in:

- **R0 / today:** the kit runs `CurrentNet` (hand adapter — fine, it is explicitly oracle
  backend #1, a swappable baseline) + `ExternalOracle` (out-of-process wrapper).
  `GeneratedEngine.supports(u) = Absent{EngineNotYetEmitted}` for every `u` → CR-6 counts it
  backend-absent, never a pass. `FormalModel` lights up per ledger row as that row's HOL4
  theory becomes CakeML-extractable. Differentials run `CurrentNet`-vs-`Elide`-vs-`Model`
  (where extractable). Coverage accrues honestly with **no engine in the room**.
- **R1.1** (first `region`/`view` pass, lowering to CakeML/Pancake with a preservation
  theorem): the compiler emits its **first** `EmittedKitBundle` — for `h1-request-parse`
  (`40-COMPLETENESS-LEDGER.md:36`, §A, `region`, R1.2). `GeneratedEngine.supports(h1-request-parse)`
  flips to `Supported`; the bundle's adapter plugs into the existing runner; the N-way for
  that one unit becomes four-way with `nway_has_independent_witness` satisfied (`CurrentNet`
  present). Nothing in the kit is rewritten.
- **R1.1+ … R8:** each new emitted unit flips one more cell `Absent → Supported`,
  monotonically, tracking the emit order exactly.
- **SW → FPGA → silicon retarget** (`20-ARCHITECTURE.md:178-181`): the correctness theorem
  holds across the retarget, so does its projection clause — the bundle is **re-emitted** for
  the new target under the same theorem, and the adapter retargets *with* the artifact. The
  kit does not notice the substrate changed.

The payoff — *"the generated engine plugs in for FREE"* — is literal: the cost of onboarding
the engine into the kit is **zero per-artifact human work**, paid once in the codegen pass.

---

## Consequences

**Positive.** Zero per-artifact adapter drift; `GeneratedEngine` plugs in free at R1.1+; *the
thing tested IS the thing proven*; a red differential localizes to the artifact by theorem;
perf hooks are gate-dominated and same-artifact by construction; the kit is genuinely
artifact-agnostic and substrate-portable (retarget re-emits the bundle); the suite's green
ceases to be a spot-check and the proof's green ceases to be vacuous — **each is the other's
witness**.

**Costs / obligations.** (1) The compiler gains a codegen pass — the "fourth-output" pass
emitting `EmittedKitBundle`. (2) The compiler-correctness theorem gains the per-primitive
faithful-projection clause (a routine obligation class; small structural residual). (3) Every
emitted model theory must be CakeML-extractable to a `ModelBridgeFn` (now a *hard* requirement:
non-extractable ⇒ the row cannot be diffed ⇒ fail). (4) The runner MUST enforce
`nway_has_independent_witness`; an all-emitted agreement is non-independent and uncounted.
(5) `CurrentNet` and `ExternalOracle` are kept as non-emitted witnesses for the life of the
project. (6) Where the refinement holds only *modulo* a named crypto axiom (F-6/F-12), the
emitted adapter is faithful **to the axiomatized model**, not to a fully-proven one — an
honest gap flagged via `ProjectionTheoremRef::holds_modulo`, with the residual carried by the
fuzz-net (`41-TEST-AND-PERF-SUITE.md:349-357`).

---

## Alternatives considered

- **Alt A — hand-written adapter per artifact (status-quo-by-default).** Rejected — the
  drift-to-laundered-vacuity story above (CR-6, CR-1). Its one virtue (no compiler work) is
  exactly its defect: the adapter is maintained by *reading the engine*, so it converges on
  mirroring the engine rather than policing it. Retained **only** for `CurrentNet`, where being
  hand-written and non-emitted is the *point* (the independent control witness).
- **Alt B — wire-level-only black box.** Drive every backend solely through a real socket;
  observe only wire bytes. Pro: maximally artifact-agnostic, needs no internal coupling, works
  for the opaque oracle. Con: it **cannot observe** the per-primitive observables the kit is
  *for* — the `region` arena byte-view (`net/httpe/src/parsed_request.rs:685`,
  `21-FORMAL-MODEL.md:19-27`), the `machine` state-trace, and — critically — `linear`
  (release-once) and `shared` (linearizability) have **no wire manifestation** at all. A
  backend could emit the right bytes via a non-zero-copy, non-proven internal path and the
  black box would bless it (defeating CR-1's "fastest shape = provable shape" cross-check).
  **Resolution:** wire-level is the *fallback* observation mode for backends we cannot
  instrument (the oracle furnishes the `WireOnly` subset and `Absent` for the rest — honest,
  not laundered); the **emitted** adapter is the rich mode for the artifact we generate. The
  kit supports both; `Observation` is the common type; `ObservationMode` records which.
- **Alt C — one hand adapter shared across artifacts (parameterized).** Rejected — it still
  must read each artifact's state back into `Observation`, so it drifts per artifact through
  its parameterization; it merely hides the drift behind a config table.

---

## What this unit contributes to `net/conformance-kit`

> Implemented by **generated** code (the emitted bundles) and by the kit's runner; authored
> here only as **signatures**. All types are *additive over* the fixed spine — no spine type
> is mutated. (`PerfHookTable`/`PerfInstrumentationManifest` are owned by unit-4; referenced
> here as a consumed contract.)

```rust
// ── net/conformance-kit :: provenance.rs  (UNIT 5 contribution) ───────────────

/// Where a SutAdapter implementation came from. The runner records this per backend
/// so an emitted adapter and a hand-written one are NEVER conflated. (CR-6: provenance
/// is evidence, not metadata; it drives the TCB ledger AND the non-vacuity gate.)
pub enum AdapterProvenance {
    /// Emitted by the verified compiler from the SAME DSL description as the artifact
    /// under test. Covered by the faithful-projection clause (this ADR). NOT trusted glue.
    CompilerEmitted(EmittedAdapterCert),
    /// CakeML-extracted runnable model fn `obs_Φ ∘ step_Φ`. Also a compiler artifact.
    ModelExtracted { theory: &'static str, extract_rev: ContentHash },
    /// Hand-written for a backend the compiler does not emit (the CurrentNet baseline —
    /// the deliberate non-emitted control witness). Named-trusted (CR-2 honesty clause).
    HandWritten { crate_path: &'static str, reviewed_rev: &'static str },
    /// Out-of-process oracle wrapper (Elide). CR-3: read via IPC, NEVER linked.
    OracleWrapper { transport: OracleTransport, observed: ObservationMode },
}

pub enum OracleTransport { Subprocess { argv0: &'static str }, UnixIpc { sock: &'static str } }

/// Which slice of `Observation` a backend can furnish. Wire-only oracle ⇒ `WireOnly`;
/// gaps are reported `Absent`, never laundered. The emitted engine adapter is `Full`.
pub enum ObservationMode { Full, WireOnly }

/// Binds an emitted adapter to BOTH the artifact and the proof. The `dsl_unit` is the
/// SAME content hash the {code, model, proofs} triple is keyed to (20-ARCHITECTURE.md:24).
pub struct EmittedAdapterCert {
    pub dsl_unit:      DslUnitHash,   // content hash of the DSL unit description
    pub artifact_hash: ArtifactHash,  // hash of the emitted machine-code artifact (the SUT identity)
    pub model_hash:    ModelHash,     // hash of the emitted HOL4 theory
    pub compiler_rev:  CompilerRev,
    pub projection:    ProjectionTheoremRef, // the faithful-projection theorem handle
}

/// Handle to the lemma (in the emitted HOL4 theory) stating that the adapter is a faithful
/// projection of the sans-IO core: observe(U,i) == lift(obs_Φ(step_Φ(U, decode(i)))).
/// `holds_modulo` names any axioms the refinement leans on (F-6/F-12) — an honest gap,
/// surfaced, never hidden. `None` projection handle ⇒ NOT covered ⇒ treat as trusted glue.
pub struct ProjectionTheoremRef {
    pub theory:       &'static str,
    pub theorem:      &'static str,
    pub unit:         UnitId,
    pub holds_modulo: &'static [AxiomId],
}

// content-addressed identities (newtypes over the kit's `ContentHash`)
pub struct DslUnitHash(pub ContentHash);
pub struct ArtifactHash(pub ContentHash);
pub struct ModelHash(pub ContentHash);
pub struct CompilerRev(pub &'static str);

/// Additive SUPERTRAIT over the FIXED `SutAdapter` spine — does NOT mutate it. The runner
/// requires this supertrait to read provenance, the cert, and the compile-time realized set.
pub trait ProvenancedAdapter: SutAdapter {
    fn provenance(&self) -> AdapterProvenance;
    /// `Some` iff this adapter is a verified compiler output. `None` ⇒ trusted glue.
    fn cert(&self) -> Option<&EmittedAdapterCert>;
    /// Compile-time-known realized set, DERIVED FROM `D` (not a runtime guess). Drives the
    /// spine's `supports()`: `Supported` iff `unit ∈ realized_units()`. CR-6-by-construction.
    fn realized_units(&self) -> &[UnitId];
}

/// The compiler's FOURTH output group for one DSL unit: shim + bridge + hooks, all keyed
/// to one `DslUnitHash`. `compile(D)` emits one of these per realized unit, ALONGSIDE the
/// status-quo {machine_code, formal_model, proofs} (20-ARCHITECTURE.md:24-30).
pub struct EmittedKitBundle {
    pub unit:         UnitId,
    pub dsl_unit:     DslUnitHash,
    pub adapter:      Box<dyn ProvenancedAdapter>, // (i)   the generated-engine SUT shim
    pub model_bridge: ModelBridgeFn,               // (ii)  extracted runnable model fn
    pub perf_hooks:   PerfHookTable,               // (iii) unit-4's instrumentation contract
}

/// The `FormalModel` backend's runnable step — the extracted `obs_Φ ∘ step_Φ` the
/// differential runner calls (harness/executable-model-bridge, 41:334). Its result IS an
/// `Observation`, so it is comparable field-for-field against the engine adapter.
pub type ModelBridgeFn =
    fn(unit: UnitId, prim: Primitive, input: &Input, spec: &Spec) -> Observation;

/// CR-6 INDEPENDENCE gate the runner MUST apply (consumed by harness/diff-nonvacuity-gate):
/// an N-way agreement is a genuine match ONLY if ≥1 agreeing backend is NOT compiler-emitted
/// (i.e. a `HandWritten` or `OracleWrapper`). All-emitted agreement ⇒ non-independent ⇒
/// uncounted. Guards against compiler monoculture.
pub fn nway_has_independent_witness(agreeing: &[AdapterProvenance]) -> bool;

/// Build-time CR-3 firewall predicate (consumed by harness/oracle-provenance-firewall,
/// 41:332): the engine link set must be disjoint from oracle symbols. Err = the offending
/// symbols. A non-empty Err FAILS THE BUILD.
pub fn engine_link_set_excludes_oracle(link_syms: &[&str]) -> Result<(), Vec<String>>;

// ── proposed, offered to the spine owner (resolves a spine tension) ───────────
/// Typed replacement for `Support::Absent { reason: String }` so the CR-6 classifier can
/// machine-bucket an UNPROVEN adapter distinctly from a benign absence (a free-text typo
/// must not silently mis-bucket `ProjectionClauseUndischarged` as `PrimitiveNotApplicable`).
pub enum AbsentReason {
    EngineNotYetEmitted,                          // bootstrap: GeneratedEngine has no bundle yet
    ProjectionClauseUndischarged { unit: UnitId }, // proof gate failed ⇒ no bundle ⇒ uncounted
    PrimitiveNotApplicable,                        // unit's primitive not expressible here
    ObservationModeTooNarrow { have: ObservationMode }, // wire-only oracle cannot furnish arena_view
    OracleRefused { detail: String },
}

/// The single SHARED, total, decidable marshalling — the named residual trust surface
/// (CR-2 honesty clause). One `lift`, not one-per-artifact; ideally itself emitted/verified.
pub fn lift(obs: ModelObservable) -> Observation;
```

---

## Seams

**Provides (to the rest of `net/conformance-kit`):**
- `trait ProvenancedAdapter: SutAdapter` — the additive supertrait carrying `provenance()`,
  `cert()`, `realized_units()`; lets the runner distinguish verified compiler outputs from
  trusted glue and account the TCB/CR-6 ledgers correctly.
- `enum AdapterProvenance` + `EmittedAdapterCert` + `ProjectionTheoremRef` — the provenance/
  attestation layer; the handle certifying an adapter is a faithful projection.
- `enum ObservationMode { Full, WireOnly }` — the rich-vs-wire observation distinction the
  bare spine lacks.
- `struct EmittedKitBundle` + `ModelBridgeFn` — the per-unit fourth-output contract
  `compile(D)` satisfies (shim + bridge + hooks).
- `fn nway_has_independent_witness` — the CR-6 monoculture/independence gate.
- `fn engine_link_set_excludes_oracle` — the build-time CR-3 firewall predicate.
- `enum AbsentReason` + `fn lift` — proposed typed-absence and the named residual trust shim.
- **The keystone claim** the rest of the kit stands on: *for any artifact we compile, the
  adapter is a compiler output, so the thing tested IS the thing proven; the suite's green and
  the proof's green are each the other's witness.*

**Consumes:**
- *From the fixed spine:* `trait SutAdapter`, `enum Observation { Produced | Absent }`,
  `enum Support`, `struct Vector`, `UnitId`, `BackendId`, `Primitive`, `Spec`, `Input`,
  `Event`, `ResourceOp`, `Schedule`, `ArenaView`, `Trace`, `ErrorClass`, `ContentHash`.
  `lift`'s codomain and the projection theorem's target are exactly `Observation::Produced`.
- *From unit-4 (perf):* `PerfHookTable` and the PF-6 gate-dominance contract
  (`22-PERFORMANCE.md:107-116`); this ADR defines what the compiler hands it.
- *From the harness unit (41 §F.1):* `harness/three-way-runner` (`41:328`) and
  `harness/diff-nonvacuity-gate` (`41:336`) consume `AdapterProvenance` and call
  `nway_has_independent_witness`; `harness/executable-model-bridge` (`41:334`) is the
  extraction contract `ModelBridgeFn` realizes; `harness/oracle-provenance-firewall`
  (`41:332`) is realized by `engine_link_set_excludes_oracle`.
- *From the compiler/formal layer (ADR-3, CR-4):* the existing compiler-correctness theorem
  `⟦machine_code(D)⟧ ⊑ Φ(D)` and its simulation witness `R` (reused, not re-authored); the
  per-primitive proof schema (`21-FORMAL-MODEL.md:299-302`) into which the faithful-projection
  clause is registered as one more routine obligation class.
- *From the DSL (ADR-7):* the four primitives and the content-addressing of a DSL unit
  (`DslUnitHash`).

**Tensions with the fixed spine (reported, not silently diverged):**
1. **No provenance on the spine.** `SutAdapter` carries no provenance method, but CR-6
   independence requires the runner to know emitted-vs-hand-vs-oracle per backend. Resolved
   **additively** via `ProvenancedAdapter: SutAdapter`; the runner must require/downcast to the
   supertrait, which the bare spine does not advertise.
2. **`Support::Absent { reason: String }` is free-text.** The proof/test weld needs a
   *machine-keyable* reason: `ProjectionClauseUndischarged` must round-trip into the classifier
   distinctly from `EngineNotYetEmitted` and `PrimitiveNotApplicable`. A typo in free-text can
   silently mis-bucket an *unproven* adapter as a benign absence. Offered: typed `AbsentReason`.
   (This also subsumes Draft-A's observation that the spine conflates two absences — *DSL did
   not realize this unit* vs *backend cannot express this observable*; both are non-matches but
   only the former is laundering-proof-by-construction. `AbsentReason` separates them.)
3. **`Observation::Produced` is HTTP-response-shaped.** Its `(status, headers, body)` fields
   serve `region`/`machine` directly, but `linear` (release-once / no-use-after-release) and
   `shared` (linearizability under interleaving) have no dedicated field — the projection
   theorem must smuggle them into `state_trace`, making `project_u` awkward to state for two of
   the four ADR-7 primitives. Recommend the spine owner add explicit `linear`/`shared`
   observation fields (or a typed `state_trace` sum) so `project_u` is total and direct.
4. **`BackendId` is a closed enum and does not encode the emitted/non-emitted partition.** Two
   of the four backends (`FormalModel` via `ModelBridgeFn`, `GeneratedEngine`) are compiler-
   emitted from the *same* compiler, but the closed enum does not say so;
   `nway_has_independent_witness` must re-derive the partition from `AdapterProvenance`. If a
   fifth emitted backend is ever added, the independence math silently shifts and nothing in
   the spine flags it. Recommend the spine carry an `is_emitted()` projection on `BackendId`.
5. **Identity-of-the-tested-thing is `artifact_hash`, not `UnitId`.** The spine keys on
   `UnitId`; an emitted bundle is keyed on content hashes, and a recompile can change
   `artifact_hash` while `UnitId` is stable. The spine needs the rule *the `artifact_hash` (not
   `UnitId`) is the identity of what was tested* so `supports(unit)` and the cert cannot
   silently disagree across a recompile.
6. **The constructive-witness assumption.** The projection clause assumes the simulation
   witness `R` is materialized **executably** by the correctness proof (so `obs_M = obs_Φ ∘ R`
   is runnable). Where a refinement is by a non-constructive/abstract simulation, the emitted
   adapter needs an extra *executability* obligation the spine does not mention — flagged here
   as an emission precondition.
