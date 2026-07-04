# 43 — THE VECTOR CORPUS FORMAT

> **UNIT 2 of the artifact-agnostic conformance/test/perf kit.** The single,
> content-addressed, primitive-keyed **and** `40-LEDGER`-keyed **and** `41-SUITE`-keyed
> source of every test input. A vector = `{input, spec, expected}`. **No inline
> ad-hoc bytes live anywhere else** (`41-TEST-AND-PERF-SUITE.md:327`).
>
> **Status: DESIGNED-NOT-IMPLEMENTED.** Zero engine code exists; the first stone is
> roadmap R1.1. This format is GREENFIELD and lands **before** the engine — it is
> the gate the first emitted artifact's vectors pass through. This doc specifies the
> exact Rust signatures `net/conformance-kit` contributes for Unit 2; a later merge
> agent authors the unified crate. We do **not** write the crate here.

This file realizes `harness/vector-corpus-format` (`41-TEST-AND-PERF-SUITE.md:325-327`):
> *"a case = `{wire-input bytes, config/spec, expected arena-view + status +
> emitted-bytes}`, serializable, content-addressed, replayable across all three
> backends. The corpus is the single source of inputs (no inline ad-hoc bytes)."*

It is optimized, in priority order, for **(A) replayability + content-addressing +
reproducibility across all four backends and across time** — a vector recorded today
must replay byte-identically against the generated engine next year — and **(B)
authorability + ledger-keying coverage** — adding a ledger-keyed vector is one
hand-written file, and the suite can *prove* every non-OOS ledger row owns ≥1 vector.

---

## 0. What a vector is keyed to

A vector is the atom both the **formal ledger** and the **empirical suite** point at.
`40-COMPLETENESS-LEDGER.md:24-28` keys every byte-path to a DSL primitive
(`region`/`machine`/`linear`/`shared`, ADR-7 / `10-DECISIONS.md`) with status
`modeled | GAP | OOS`. `41-SUITE` keys every case to `validates / kind / source /
ledger_link / acceptance`. A vector therefore carries **four keys** plus its payload:

- **`primitive: Primitive`** — one of the four DSL primitives; *chooses the adapter
  surface* (`decode_region` / `run_machine` / `run_linear` / `run_shared`).
- **`ledger_rows: Vec<LedgerKey>`** — the `40-LEDGER` §A–J row(s) it empirically
  covers. "The keel of completeness: every non-OOS ledger row must own ≥1 vector."
- **`suite_cases: Vec<CaseKey>`** — the `41-SUITE` case id(s) (e.g. `h1-get-200-body`,
  `smug-cl-te-reject`).
- **`kind: Kind`** — `Conformance | Behavioral | Security | Perf | Differential`.

> **Spine note (tension #1).** The fixed seam spine declares these *singular*
> (`ledger_row: LedgerKey`, `suite_case: CaseKey`). A single vector legitimately
> covers multiple rows — a curl replay exercises both the §A HTTP/1.1-request-parse
> row **and** the response-writer row. We **pluralize** to `Vec<…>` (≥1 each) and
> recommend the spine pluralize. See §10.

---

## 1. Three layers: authoring · canonical · artifact

The format has three representations, and the layering *is* the design.

| layer | representation | purpose | codec |
|---|---|---|---|
| **(A) Authoring** | directory of TOML manifests + raw byte blobs | human-writable, PR-diffable | TOML + raw bytes |
| **(B) Canonical / replay** | the *semantic core* of each vector | content-hashing + cross-process/cross-language replay | **deterministic CBOR (dCBOR)** |
| **(C) Artifact** | one content-addressed `corpus.pack` | the runner/CI `mmap`s it; out-of-process backends receive individual cores over IPC | postcard index + dCBOR records + CAS region |

`Corpus::compile` lowers authoring → canonical → artifact, computes all content ids,
absorbs inline-authored bytes into the CAS, and writes the index. The flow is
one-directional: the canonical store is the source of truth. This mirrors the
engine's own one-source-three-outputs discipline (`20-ARCHITECTURE.md:24-48`).

### Why a directory-of-files for authoring (EMPHASIS B)
Direct continuity with the two formats we migrate, both already directory-shaped:
the curl corpus is a directory of pseudo-XML files
(`net/httpe/tests/curl_test_vectors.rs:21-24`) and every fuzz corpus is a directory of
raw blobs (`net/*/fuzz/corpus/<target>/*` — **193** files under `net/httpe/fuzz`,
**323** across `net/*`). TOML is hand-writable and diffs cleanly; raw inputs live as
separate blob files so binary payloads never pollute a manifest. The chosen format is
strictly *better* than the curl pseudo-XML it replaces, which is parsed *at test time*
inside the test body — exactly the ad-hoc coupling this unit removes.

### Why deterministic CBOR (not postcard) for the canonical/hash codec — the decisive call
The two drafts split here; this is the load-bearing decision. **The hash preimage
codec must be recomputable cross-language**, because the three-way runner crosses a
**language boundary**: the Rust engine, the **JVM** Elide oracle (an internal Elide HTTP-engine source tree,
read out-of-process per CR-3, `10-DECISIONS.md`), and the **CakeML-extracted** formal
model must *each independently recompute the same `VectorId`* to prove they replayed
the same input — the anti-laundering check behind `harness/diff-nonvacuity-gate`
(CR-6, `41-TEST-AND-PERF-SUITE.md:336-338`). postcard is positional/Rust-decoder-shaped
and would lock the oracle and model into a Rust-only decoder; it has no cross-language
canonical-determinism spec. **dCBOR (RFC 8949 §4.2.1 core-deterministic: definite
lengths, smallest-int encoding, bytewise-sorted map keys)** has a published, language-
neutral canonicalization that a JVM and a CakeML extractee can both implement.

postcard is *not* discarded — it remains the codec for the **Rust-internal pack
index** (layer C), where there is no language boundary and where it is already the
repo's deterministic wire framing (`40-COMPLETENESS-LEDGER.md:181` —
`postcard WireMessage framing | region | F-8 | R4.1 | modeled`). So: **dCBOR for the
cross-language hash preimage, postcard for the Rust-only artifact framing.** Take the
stronger codec on each layer rather than one codec everywhere.

Because dCBOR is not self-describing at the schema level, the schema is pinned: a
`FormatTag { magic: b"DNVC", version: u16 }` is prepended to every hash preimage, so
two format versions are hash-disjoint by construction.

### Authoring layout
```
net/conformance-kit/corpus/
  ledger.toml         # machine-readable mirror of 40-LEDGER rows {key, section, status, reason}
  suite.toml          # machine-readable mirror of 41-SUITE cases {id, kind, category}
  units.toml          # unit -> { primitive, default ledger_rows[], default suite_cases[] }
  projections/<ProjectionId>.toml
  _blobs/<hh>/<ContentHash>          # content-addressed inputs/goldens/specs (deduped CAS)
  region/  h1-request-parse/         vectors/*.toml
           qpack-decode/             ...
  machine/ h2-frames-hpack-flowctl/  ...
           router-first-match/       ...
  linear/  bufring-lease/            ...
  shared/  sse-broadcaster-fanout/   ...
  _imported/ curl/ ...               _bridged/ fuzz/ ...
```
Partition is **primitive → unit**, because *one ledger row = one DSL unit = one HOL4
theory* (`40-COMPLETENESS-LEDGER.md:13-14`); a unit directory is the natural home for
all its vectors and is exactly the granularity the three-way-runner sweeps.

### Dir-inherited keying (EMPHASIS B)
`units.toml` maps each unit → `{primitive, default ledger_rows[], default
suite_cases[]}`. **Every vector dropped into `corpus/<primitive>/<unit>/vectors/`
inherits that dir's keying**; a vector TOML only *adds/overrides*. Adding a
ledger-keyed vector is one TOML file and zero Rust.

A golden conformance vector:
```toml
kind   = "conformance"
input  = { kind = "bytes", blob = "blobs/aa3f…" }   # or inline_hex / inline_text (absorbed at compile)
spec   = { ref = "specs/static-site.toml" }
expect = { golden = "golden/3a7b…", backend = "current-net" }   # backend that recorded it
ledger_rows = ["A.http1-request-parse"]             # extends unit default
suite_cases = ["h1-get-200-body"]
[acceptance]
projection = ["status","headers","body","consumed","error_class"]
normalize  = ["drop-header:date","drop-header:server"]
[replay]
clock = { fixed_epoch = 1735689600 }
```

A golden-free differential vector:
```toml
kind   = "differential"
input  = { kind = "bytes", blob = "blobs/…" }
expect = "nway-agree"
[acceptance]
projection = ["status","headers","body","error_class"]   # arena_view/state_trace projected away (not portable)
quorum     = 2                                            # CR-6: >=2 GENUINE (non-Absent) backends
normalize  = ["drop-header:date"]
```

A security `MustReject`:
```toml
kind   = "security"
input  = { kind = "bytes", blob = "blobs/4c1f…" }
suite_cases = ["smug-cl-te-reject"]
[expect.must-reject.refuse]
error_class   = ["SmuggleViolation::ContentLengthAndTransferEncoding"]
status_in     = [400]
must_not      = ["forwarded-upstream"]      # negative obligation; see §5 + tension #4
[acceptance]
projection = ["status","error_class"]
```

`inline_text` / `inline_hex` are an ergonomic escape hatch only; `compile` hashes them
into the CAS so even authored-inline bytes become content-addressed and the
single-source-of-inputs invariant holds **at the artifact**.

---

## 2. Content addressing (the replayability spine, EMPHASIS A)

All hashing is **BLAKE3-256**, deliberately reusing the **dregg receipt** hash family
(`40-COMPLETENESS-LEDGER.md:185` receipts; `:207` total-accounting) so a `VectorId` can
be witnessed in a receipt. Two hash *roles*:

- **CAS blob key** = `BLAKE3(raw file bytes)`, *no domain tag*, so a blob file equals
  `b3sum < file` and external tooling can verify it. Used for `Input::Bytes`, stored
  goldens-as-bytes, and stored specs-as-bytes. Identical inputs dedup across vectors —
  the 323 fuzz files become CAS blobs for free.
- **Structured content id** = domain-separated `BLAKE3(domain_tag ‖ magic ‖
  version_le ‖ dCBOR(value))`, where `HashDomain ∈ {Input, Vector, Golden, Projection,
  Spec}`. Domain separation means an `Input` and a `Vector` with coincidentally equal
  bytes can never collide.

### What `VectorId` commits to — the **semantic core only** (tension #2)
```
VectorId = H_vector( dCBOR{ format, primitive, unit, input, spec, expect, acceptance, replay } )
   ├── Input::Bytes  → InputHash = b3sum(raw bytes)        # CAS ref folded in
   ├── EventSeq/ResourceOps/Schedule → folded inline       # structured + small
   ├── spec  → SpecId  (or inline structured Spec, folded)
   └── expect
         ├── Golden.observation = GoldenHash (CAS ref)
         ├── NwayAgree          → marker (quorum lives in Acceptance)
         └── MustReject         → inline RejectPredicate
```
`VectorId` **excludes** `ledger_rows`, `suite_cases`, `kind`, and all `VectorMeta`
(provenance, prose, timestamps). **Rationale:** re-keying a vector to additional
ledger rows — a routine authoring act — must *not* change its identity. The spine's
single `id: ContentHash` "over the whole struct" is underspecified about *what* is
hashed; we pin it to the semantic core. (`acceptance` and `replay` **are** in the
core: they change replay semantics, so they must change identity.)

### The id is **derived, never trusted** (tension #2, fail-closed)
`VectorMeta.id` is an index/cache key only. `CorpusStore::verify()` recomputes
`H(core)` for every vector on load and **fails closed** on mismatch
(`CorpusIntegrityError`). That recompute-and-verify is what turns "replays identically
next year" into a *checked fact*: tamper with any byte of input/spec/expect/acceptance/
replay and the id no longer matches. Across a format bump, the prior id is preserved in
`VectorMeta.legacy_ids` so cross-references survive.

---

## 3. Lifting nondeterminism out of the vector (EMPHASIS A)

Replayability fails the moment a vector embeds a runtime value. The current curl
harness does exactly this: it substitutes a runtime ephemeral port into the request
bytes (`curl_test_vectors.rs:319` `substitute_vars`, `:635` `build_request`). In this
format the input bytes carry a **placeholder** and the binding moves into a declared
`ReplayNeeds`, injected by the runner's `ReplayEnv` at replay time:

- `ClockMode::{None, FixedEpoch(t0), TickDriven}` — timeouts ride as
  `Event::TimerTick` inside the `EventSeq` ("time-as-input"); no wall-clock ever
  enters an `Observation`.
- `rng_seed: Option<u64>`, `tls_key: Option<FixtureRef>` (e.g.
  `fixtures/ed25519_private.pem`, under `net/httpe/tests/fixtures/`),
  `bind: Option<BindHint>` (host + port *placeholder*).

So the **hashed input is stable** while the live port/clock/keys are injected. Volatile
*output* fields are normalized away by a content-addressed `Projection`
(`DropDateHeader`, `MaskServerVersion`, `MaskEphemeralPort`, …) **before** a golden is
hashed or a diff is taken — over exactly the five diff fields the three-way-runner
compares (`41-TEST-AND-PERF-SUITE.md:331`: status, header-set, body, arena byte-view,
error-class).

---

## 4. Per-primitive input/observation shape

| primitive | `Input` variant | observed (Acceptance projects onto these) | grounding |
|---|---|---|---|
| **region** | `Bytes(InputHash)` | arena byte-view + status + error_class + consumed | `parsed_request.rs:685` `SIDECAR_OFFSET_BASE`; `wf_parsed_request` `21-FORMAL-MODEL.md:22-23` |
| **machine** | `EventSeq(Vec<Event>)` (or `Bytes` for a pure parse step) | state-trace + emitted bytes + error_class | tri-state `Complete{value,consumed}\|Incomplete\|Error` `socks.rs:84-91`, `cq/response_parser.rs:43-47`, `21-FORMAL-MODEL.md:31` |
| **linear** | `ResourceOps(Vec<ResourceOp>)` | release-once / no-use-after-release | X-4 exactly-once recycle, `21-FORMAL-MODEL.md:95` |
| **shared** | `Schedule(Schedule)` | invariant held under interleaving (loom/shuttle) | linearizability, `21-FORMAL-MODEL.md:182` |

`Input::Bytes` is **always** a CAS ref (never inline). The structured variants
(`EventSeq`/`ResourceOps`/`Schedule`) ride inline in the dCBOR core (they are small,
structured, and themselves fold into `VectorId`). The `shared` schedule never takes a
`Golden` — its expectation is an invariant predicate, not a value (tension #6).

`Acceptance.projection: ObsProjection` selects which `Observation` fields are compared,
so the spine's HTTP-response-shaped `Observation::Produced` is **not** vacuously
over-specified for `linear`/`shared`: those vectors project onto `STATE_TRACE`/
`ARENA_VIEW` and ignore status/headers/body (tension #3).

---

## 5. Expectation: golden · golden-free · must-reject · budget

One enum covers all four kinds. The *projection* and *quorum* live in `Acceptance`
(single home — avoids the redundancy of duplicating a projection id inside the
Expectation variant).

```rust
enum Expectation {
    Golden(GoldenRef),              // backend-pinned recorded Observation (CAS ref)
    NwayAgree,                      // no golden; agreement-defined; quorum in Acceptance
    MustReject(RejectPredicate),    // security/fuzz; a pass REQUIRES a reject
    Budget(PerfBudget),             // Kind::Perf; "expected" is a budget, not a value
}
```

- **`Golden(GoldenRef{ observation: GoldenHash, backend: BackendId })`** — a CAS ref to
  a recorded `Observation` snapshot, already normalized under `Acceptance.projection`.
  The `backend` field records *which* backend produced it: non-portable fields
  (`arena_view`, `state_trace`) may be pinned in a golden **only** for that one named
  backend; cross-backend agreement on them is impossible (tension #3). The spine's
  inline `Golden(...)` becomes a CAS ref so large snapshots never bloat records.

- **`NwayAgree`** — **no golden**. Correctness = all non-`Absent` backends agree under
  `Acceptance.projection` + `normalize`, with `Acceptance.quorum.min_agree` **genuine**
  (non-`Absent`) backends. **This is where CR-6 lives:** a backend that reports
  `Absent{reason}` (cannot run the unit) is excluded from the quorum and **never**
  counts as a match (`41-TEST-AND-PERF-SUITE.md:336-338`). The golden-free differential
  path for the `diff/*` vectors.

- **`MustReject(RejectPredicate)`** — security/fuzz. A pass *requires* a reject;
  "handled gracefully" is never a pass. Most §C security cases are `MUST REJECT`.
  ```rust
  enum RejectPredicate {
      Refuse(RejectSpec),     // CVE corpus: must surface a declared reject + no forbidden effect
      Total(TotalityBound),   // fuzz: terminate, no panic, bounded mem/steps
  }
  struct RejectSpec {
      error_class: Vec<ErrorClass>,   // >=1 must match (empty = any error); e.g. SmuggleViolation::*
      status_in:   Vec<u16>,          // e.g. [400, 431, 501]
      must_not:    Vec<Effect>,       // negative obligation: ForwardedUpstream/EgressTo/ServedPathOutsideRoot/EmittedPlaintext
  }
  struct TotalityBound { mem_bound: Option<u64>, step_bound: Option<u64> }
  ```
  `error_class` entries are the concrete enums the parsers already emit (e.g.
  `SmuggleViolation::ContentLengthAndTransferEncoding` with `.status_code()` 400/501).
  `Total` is the fuzz invariant: ASAN/UBSan-clean, no-panic ∀ input, `Complete ⇒
  0 < consumed ≤ input.len()`, no OOM/hang.

- **`Budget(PerfBudget)`** — `Kind::Perf`. The "expected" is a budget (e.g.
  ≥6.5M req/s/core, **0 heap alloc**, p99/p999 bounds), not a value or agreement. We
  add this as a **clean 4th variant** rather than smuggling it into `Acceptance`; the
  spine's three-variant `Expectation` does not anticipate perf. The *measurement
  semantics* of `PerfBudget` belong to the runner/perf unit, not this one (tension #5).

`Absent` from a backend is **never** a match under *any* mode — it is classified
separately by the runner and excluded from coverage.

---

## 6. Discovery & the ledger-keying coverage meta (EMPHASIS B)

`CorpusIndex` (built from the artifact, integrity-verified on build) answers
`by_primitive / by_unit / by_ledger / by_suite / by_kind`. The load-bearing query is
the coverage meta — `harness/ledger-keying-coverage-meta`
(`41-TEST-AND-PERF-SUITE.md:345-347`) — realized as `CoverageMatrix` with **two tiers**:

- **Static keying:** `assert_every_non_oos_row_covered()` — every `40-LEDGER` row with
  status ≠ `OOS` owns ≥1 *authored* vector; `Err(Vec<LedgerKey>)` names the naked rows
  and **fails the build**.
- **Runtime non-vacuity (CR-6):** the runner reports `(VectorId, VectorOutcome)`;
  `fold_runtime` ingests them and `assert_every_non_oos_row_genuinely_covered()`
  requires ≥1 vector per row that actually `Agree`d — `Absent`/`Divergence`/`Rejected`
  excluded. `render_markdown()` emits the generated coverage matrix doc. This is the
  difference between "a vector *exists* for this row" and "a vector for this row was
  *genuinely N-way agreed*", and it is exactly the anti-laundering gate CR-6 demands.

`ledger.toml` is the machine-readable mirror of `40-COMPLETENESS-LEDGER.md`
(`status ∈ {Modeled, Gap, Oos}`), generated from / checked against the markdown table,
so the prover never re-parses prose at runtime. The routine-obligation classes the
corpus exercises (in-bounds, totality, determinism, wf-preservation, exactly-once —
`21-FORMAL-MODEL.md:300-301`) map onto `Kind` + `ObsProjection`, so the index also
reports which obligation class each unit's vectors cover.

---

## 7. Migration path

The unified corpus becomes **the** single source of inputs; inline ad-hoc bytes retire.

**A. `curl_test_vectors.rs` → vectors.** `import_curl` reuses the existing parser logic
(`extract_section:134`, `parse_curl_test:354`) but synthesizes the raw HTTP/1.1 request
**once, at import** (the current `build_request:635`) with the **port frozen to a
placeholder** and the binding moved into `ReplayNeeds.bind` — *deleting* the in-test
request synthesis and the runtime-port substitution that makes today's bytes
non-reproducible. Each runnable test emits one Vector: `primitive=region`
(`unit=h1-request-parse`) or `machine` for the full request→response cycle;
`input=Bytes(...)`; `spec`=the catch-all route; `expect=NwayAgree` (curl tests assert
only "valid server behavior, status < 500", `:780` — genuinely golden-free);
`ledger_rows=["A.http1-request-parse"]`; `suite_cases=["h1-curl-vector-replay"]`;
`provenance=ImportedCurl{test}`. A strict reproducibility upgrade. *(The curl data
files remain Elide-proprietary; only synthesized request bytes + keys enter the corpus,
respecting the file header's confidentiality.)*

**B. fuzz corpora → vectors.** `bridge_fuzz_corpus` adopts every file under
`net/*/fuzz/corpus/<target>/*` as a `Bytes` vector, storing its bytes once in the CAS
(dedup by `b3sum`): `expect=MustReject(Total{..})`, `kind=Security`, acceptance = the
fuzz invariant. The `(primitive, ledger_rows, suite_cases)` come from an **exhaustive,
checked `FuzzKeyMap`** (e.g. `h1_request_parse → (region, ["A.http1-request-parse"],
[fuzz-no-panic-no-alloc-spike])`). **A missing/wrong entry is a hard error, never a
silent mis-key** — because a mis-key launders coverage (CR-6); this is the one place
the format demands a hand-maintained, totality-checked table (tension #7). Two
directions are supported and both matter:
  - **bridge (fuzz → corpus):** keys live fuzz dirs *by reference* (path + b3hash) so
    newly-discovered `cargo fuzz` inputs **auto-enroll** on the next bridge run — no
    copy-divergence with the live-growing corpus.
  - **export (corpus → fuzz):** `export_fuzz_view` regenerates a minimized libFuzzer
    seed set *from* the canonical store, so `cargo fuzz` keeps working and CI seeds are
    reproducible.
  The `NEW=needs-authoring` empty fuzz targets simply have empty bridge sets until
  authored, surfaced by the coverage meta as uncovered rows
  (`meta/gap-row-needs-authoring-tracker`).

**C. inline test bytes → vectors.** The proptest/integration suites that embed literal
request/frame bytes migrate case-by-case to reference `VectorId`s; a lint forbidding
inline byte literals in the kit's test bodies enforces "no inline ad-hoc bytes".

---

## 8. Reproducibility-across-time checklist (what the format guarantees)

1. Frozen schema + `FormatTag{magic,version}` in every preimage → identical bytes forever; versions hash-disjoint.
2. dCBOR core-deterministic codec → no map/field-ordering drift, **cross-language** recompute (Rust / JVM oracle / CakeML model).
3. Domain-separated BLAKE3 (receipt family) → no cross-type collision; receipt-witnessable.
4. `VectorId` over the **semantic core only** → re-keying is identity-stable.
5. Derived-and-verified ids (`CorpusStore::verify`, fail-closed) → tamper-evident.
6. Nondeterminism declared in `ReplayNeeds`, injected by the runner; volatile outputs normalized by a content-addressed `Projection` → stable inputs, stable comparisons.
7. Format bumps preserve `legacy_ids` → cross-references never break.

---

## 9. Rust signatures contributed to `net/conformance-kit`

Spine types (`Primitive`, `UnitId`, `LedgerKey`, `CaseKey`, `Kind`, `Vector`,
`Observation` + its fields `Status`/`HeaderSet`/`Bytes`/`ArenaView`/`Trace`/
`ErrorClass`/`consumed`, `Event`, `ResourceOp`, `Schedule`, `Spec`, `Support`,
`BackendId`) are **consumed**; where the spine names a type, the corpus adopts it.

```rust
// ===== net/conformance-kit :: corpus format (UNIT 2) =====
// Pinned forever; bumping forces a migration that preserves legacy_ids.
pub const CORPUS_MAGIC: [u8; 4] = *b"DNVC";
pub const CORPUS_FORMAT_VERSION: u16 = 1;

// ---- content addressing (hash.rs) ----
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ContentHash([u8; 32]);                       // BLAKE3-256
#[derive(Clone, Copy)]
pub enum HashDomain { Input, Vector, Golden, Projection, Spec }
impl ContentHash {
    /// CAS blob key: raw bytes, no domain tag => equals `b3sum < file`.
    pub fn of_bytes(b: &[u8]) -> Self;
    /// Structured id: H(domain_tag ++ CORPUS_MAGIC ++ version_le ++ dcbor(value)).
    pub fn of_dcbor<T: serde::Serialize>(d: HashDomain, v: &T) -> Self;
    pub fn to_hex(&self) -> String;                     // 64-char lowercase
    pub fn from_hex(s: &str) -> Result<Self, HashParseError>;
    pub fn short(&self) -> &str;                         // first 12 hex, for filenames
}
pub type InputHash  = ContentHash;   // == of_bytes(raw input)
pub type GoldenHash = ContentHash;   // == of_bytes(dcbor(Observation))
pub type SpecId     = ContentHash;
pub type ProjectionId = ContentHash;
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VectorId(pub ContentHash); // of_dcbor(Vector, semantic-core); EXCLUDES keys/meta

// ---- canonical codec ----
/// dCBOR (RFC 8949 §4.2.1 core-deterministic) — the CROSS-LANGUAGE hash preimage codec.
pub fn to_dcbor<T: serde::Serialize>(v: &T) -> Vec<u8>;
#[derive(serde::Serialize, serde::Deserialize, Clone, Copy)]
pub struct FormatTag { pub magic: [u8; 4], pub version: u16 }

// ---- payload enums ----
#[derive(serde::Serialize, serde::Deserialize)]
pub enum Input {
    Bytes(InputHash),                 // region + machine(parse): CAS ref, NEVER inline
    EventSeq(Vec<Event>),             // machine FSM driving (incl. Event::TimerTick)
    ResourceOps(Vec<ResourceOp>),     // linear: acquire/use/release-once (X-4)
    Schedule(Schedule),               // shared: interleaving (loom/shuttle)
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum SpecRef { Inline(Spec), Cas(SpecId) }

#[derive(serde::Serialize, serde::Deserialize)]
pub enum Expectation {
    Golden(GoldenRef),
    NwayAgree,                        // quorum lives in Acceptance
    MustReject(RejectPredicate),
    Budget(PerfBudget),               // Kind::Perf (measurement semantics owned elsewhere)
}
#[derive(serde::Serialize, serde::Deserialize)]
pub struct GoldenRef { pub observation: GoldenHash, pub backend: BackendId }
#[derive(serde::Serialize, serde::Deserialize)]
pub enum RejectPredicate { Refuse(RejectSpec), Total(TotalityBound) }
#[derive(serde::Serialize, serde::Deserialize)]
pub struct RejectSpec {
    pub error_class: Vec<ErrorClass>, // >=1 must match (empty = any error)
    pub status_in:   Vec<u16>,        // e.g. [400, 431, 501]
    pub must_not:    Vec<Effect>,     // negative obligation (tension #4)
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum Effect { ForwardedUpstream, EgressTo(String), ServedPathOutsideRoot, EmittedPlaintext }
#[derive(serde::Serialize, serde::Deserialize)]
pub struct TotalityBound { pub mem_bound: Option<u64>, pub step_bound: Option<u64> }

// ---- acceptance: the pass-predicate (separate from the "right answer") ----
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Acceptance {
    pub projection: ProjectionRef,    // which Observation fields are compared
    pub quorum:     Quorum,           // CR-6: only non-Absent backends count
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum ProjectionRef { Cas(ProjectionId), Inline(Projection) }
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Projection { pub fields: ObsFieldSet, pub normalize: Vec<Normalizer> }
bitflags::bitflags! {
    #[derive(serde::Serialize, serde::Deserialize)]
    pub struct ObsFieldSet: u16 {
        const STATUS=1; const HEADERS=2; const BODY=4; const ARENA_VIEW=8;
        const STATE_TRACE=16; const ERROR_CLASS=32; const CONSUMED=64;
    }
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum Normalizer { DropDateHeader, DropHeader(String), MaskServerVersion,
                      MaskEphemeralPort, SortMultiHeaders, LowercaseHeaderNames }
#[derive(serde::Serialize, serde::Deserialize)]
pub struct Quorum { pub min_agree: u8 }   // CR-6: default 2; counts only non-Absent backends

// ---- declared replay determinism (lifted nondeterminism) ----
#[derive(serde::Serialize, serde::Deserialize)]
pub struct ReplayNeeds {
    pub clock: ClockMode, pub rng_seed: Option<u64>,
    pub tls_key: Option<FixtureRef>, pub bind: Option<BindHint>,
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum ClockMode { None, FixedEpoch(u64), TickDriven }
#[derive(serde::Serialize, serde::Deserialize)]
pub struct FixtureRef(pub String);                 // e.g. "fixtures/ed25519_private.pem"
#[derive(serde::Serialize, serde::Deserialize)]
pub struct BindHint { pub host: String, pub port_placeholder: u16 }

// ---- the serialized vector: HASHED core + UNHASHED meta ----
#[derive(serde::Serialize, serde::Deserialize)]
pub struct VectorCore {                            // exactly the VectorId preimage
    pub format:     FormatTag,
    pub primitive:  Primitive,
    pub unit:       UnitId,
    pub input:      Input,
    pub spec:       SpecRef,
    pub expect:     Expectation,
    pub acceptance: Acceptance,
    pub replay:     ReplayNeeds,
}
#[derive(serde::Serialize, serde::Deserialize)]
pub struct VectorMeta {                            // NOT in the hash preimage
    pub id:          VectorId,                     // == hash(core); verified on load
    pub kind:        Kind,                          // reclassifiable
    pub ledger_rows: Vec<LedgerKey>,               // >=1 (spine is singular — tension #1)
    pub suite_cases: Vec<CaseKey>,                 // >=1
    pub validates:   String,                        // 41-SUITE 'validates' prose
    pub provenance:  Provenance,
    pub recorded_at: Option<u64>,                  // unix secs, provenance only
    pub legacy_ids:  Vec<VectorId>,                // pre-format-bump ids
    pub notes:       String,
}
#[derive(serde::Serialize, serde::Deserialize)]
pub enum Provenance {
    Authored, ImportedCurl { test: u32 },
    BridgedFuzz { target: String, file: String }, Rfc(String), NeedsAuthoring,
}
pub struct Vector { pub core: VectorCore, pub meta: VectorMeta }
impl Vector {
    pub fn compute_id(&self) -> VectorId;          // of_dcbor(Vector, &self.core)
    pub fn verify_id(&self) -> Result<(), IdMismatch>;
}

// ---- CAS + corpus discovery ----
pub trait CasStore {
    fn get(&self, h: ContentHash) -> Option<&[u8]>;
    fn contains(&self, h: ContentHash) -> bool;
    fn put(&mut self, bytes: &[u8]) -> ContentHash;     // == of_bytes
}
pub struct DirCasStore;            // _blobs/<hh>/<hash> on disk
pub struct PackCasStore<'a>(&'a [u8]);                 // mmap'd CAS region of corpus.pack

pub trait CorpusStore {
    fn get_vector(&self, id: VectorId) -> Option<Vector>;
    fn resolve_input(&self, v: &Vector) -> ResolvedInput<'_>;
    fn resolve_golden(&self, h: GoldenHash) -> Option<Observation>;
    fn get_projection(&self, id: ProjectionId) -> Option<Projection>;
    fn get_spec(&self, id: SpecId) -> Option<Spec>;
    fn verify(&self) -> Result<(), CorpusIntegrityError>;   // recompute ALL ids, fail-closed
}
pub enum ResolvedInput<'a> {
    Bytes(&'a [u8]), EventSeq(&'a [Event]),
    ResourceOps(&'a [ResourceOp]), Schedule(&'a Schedule),
}
pub struct CorpusIntegrityError { pub id: VectorId, pub stored: ContentHash, pub recomputed: ContentHash }

pub struct Corpus;                 // owns a CorpusStore + a CorpusIndex
impl Corpus {
    pub fn load_authored(root: &std::path::Path) -> Result<Corpus, CorpusError>;
    pub fn load_pack(pack: &std::path::Path)     -> Result<Corpus, CorpusError>;
    pub fn compile(root: &std::path::Path, out: &std::path::Path) -> Result<PackStats, CorpusError>;
    pub fn vectors(&self) -> impl Iterator<Item = &Vector>;
    pub fn by_id(&self, id: VectorId) -> Option<&Vector>;
    pub fn by_primitive(&self, p: Primitive) -> &[VectorId];
    pub fn by_unit(&self, u: &UnitId)        -> &[VectorId];
    pub fn by_ledger(&self, k: &LedgerKey)   -> &[VectorId];
    pub fn by_suite(&self, c: &CaseKey)      -> &[VectorId];
    pub fn by_kind(&self, k: Kind)           -> &[VectorId];
}

// ---- ledger/suite models + the coverage meta ----
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RowStatus { Modeled, Gap, Oos }
pub struct LedgerRow { pub key: LedgerKey, pub section: char, pub status: RowStatus, pub reason: Option<String> }
pub struct Ledger; pub struct Suite;
impl Ledger {
    pub fn load(path: &std::path::Path) -> Result<Ledger, CorpusError>;
    pub fn rows(&self) -> impl Iterator<Item = &LedgerRow>;
    pub fn non_oos(&self) -> impl Iterator<Item = &LedgerRow>;
}
pub enum VectorOutcome { Agree { backends: u8 }, Divergence, AllAbsent, Rejected }
pub struct CoverageMatrix;
impl CoverageMatrix {
    pub fn build(corpus: &Corpus, ledger: &Ledger, suite: &Suite) -> CoverageMatrix;
    pub fn vectors_for(&self, k: &LedgerKey) -> &[VectorId];
    /// STATIC keying half of 41:345-347 — every non-OOS row owns >=1 authored vector.
    pub fn assert_every_non_oos_row_covered(&self) -> Result<(), Vec<LedgerKey>>;
    pub fn rows_without_vectors(&self) -> Vec<LedgerKey>;
    /// RUNTIME non-vacuity half (CR-6) — fold the runner's per-vector outcomes in.
    pub fn fold_runtime(&mut self, results: &[(VectorId, VectorOutcome)]);
    pub fn assert_every_non_oos_row_genuinely_covered(&self) -> Result<(), Vec<LedgerKey>>;
    pub fn render_markdown(&self) -> String;
}

// ---- migration tooling ----
pub fn import_curl(curl_data_dir: &std::path::Path, out_root: &std::path::Path)
    -> Result<ImportStats, CorpusError>;
pub struct FuzzRoot { pub crate_dir: std::path::PathBuf }   // e.g. net/httpe/fuzz
/// EXHAUSTIVE, totality-checked: a missing target => hard error (anti-launder).
pub struct FuzzKeyMap(pub std::collections::BTreeMap<String, (Primitive, UnitId, Vec<LedgerKey>, Vec<CaseKey>)>);
pub fn bridge_fuzz_corpus(roots: &[FuzzRoot], map: &FuzzKeyMap, out_root: &std::path::Path)
    -> Result<ImportStats, CorpusError>;
pub fn export_fuzz_view(corpus: &Corpus, fuzz_root: &std::path::Path) -> Result<ExportStats, CorpusError>;
```

---

## 10. Seams

### Provides (to `net/conformance-kit` and downstream units)
- The **on-disk corpus schema**: `ledger.toml` / `suite.toml` / `units.toml` + dir-inherited keying + `_blobs/` CAS + `projections/`, and the `corpus/<primitive>/<unit>/` partition.
- **Content addressing**: `ContentHash`, `HashDomain`, `VectorId`/`InputHash`/`GoldenHash`/`SpecId`/`ProjectionId`; the dual hash roles (`of_bytes` = `b3sum`, `of_dcbor` = domain-separated); `to_dcbor` cross-language codec; `FormatTag` magic/version.
- The **hashed/unhashed split**: `VectorCore` (the `VectorId` preimage — semantic core only) vs `VectorMeta` (reclassifiable keys + provenance), and `Vector` pairing them with `compute_id`/`verify_id`.
- The payload/expectation types: `Input`, `SpecRef`, `Expectation` (incl. the 4th `Budget` variant), `GoldenRef`, `RejectPredicate`/`RejectSpec`/`Effect`/`TotalityBound`, `Acceptance`, `Projection`/`ObsFieldSet`/`Normalizer`, `Quorum`, `ReplayNeeds`.
- The **store + discovery**: `CasStore`/`DirCasStore`/`PackCasStore`, `CorpusStore` (with `verify` fail-closed), `Corpus` (`load_authored`/`load_pack`/`compile` + `by_*`), `ResolvedInput`, `CorpusIntegrityError`.
- The **coverage meta**: `Ledger`/`Suite`/`LedgerRow`/`RowStatus`, `CoverageMatrix` (static `assert_every_non_oos_row_covered` + `rows_without_vectors`; runtime `fold_runtime` + `assert_every_non_oos_row_genuinely_covered`; `render_markdown`).
- **Migration tooling**: `import_curl`, `bridge_fuzz_corpus` (+`FuzzKeyMap`/`FuzzRoot`), `export_fuzz_view`; and the binaries `corpus-build`/`corpus-import-curl`/`corpus-bridge-fuzz`/`corpus-export-fuzz`.

### Consumes
- **From the fixed seam spine (Unit 1):** `Primitive`, `UnitId`, `LedgerKey`, `CaseKey`, `Kind`, `BackendId`, `Support`, `Spec`, and the whole `Observation` surface (`Status`/`HeaderSet`/`Bytes`/`ArenaView`/`Trace`/`ErrorClass`/`consumed`). `Input` variants consume `Event`, `ResourceOp`, `Schedule`.
- **From the three-way-runner unit:** it drives `SutAdapter` over `resolve_input`-ed vectors, classifies each `{Agree, Divergence, AllAbsent, Rejected}` (= `VectorOutcome`), and feeds those into `CoverageMatrix::fold_runtime` for the CR-6 runtime gate.
- **From the spec/orchestrator unit:** a **frozen `Canonical`/dCBOR impl for `Spec`** — `SpecId` stability gates `VectorId` stability (see open question).
- **From the executable-model-bridge + oracle-IPC units:** they recompute `VectorId` from the dCBOR core to prove the same input was replayed (anti-laundering, `41:336-338`).
- **External crates:** `blake3`, a dCBOR codec, `postcard` (artifact index only), `bitflags`, `serde`; fixtures under `net/httpe/tests/fixtures` for `ReplayNeeds.tls_key`.

### Tensions with the fixed spine
1. **`ledger_row`/`suite_case` are singular in the spine**, but one vector legitimately covers multiple rows (a curl replay → §A parse + response-writer). We **pluralize** (`Vec<…>`, ≥1). *Recommend the spine pluralize.*
2. **`Vector.id` is a single `ContentHash` "over the whole struct"**, underspecified about *what* is hashed. We hash the **semantic core only** (`VectorCore`), excluding `ledger_rows`/`suite_cases`/`kind`/meta, so re-keying is identity-stable; and we make the id **derived + verified-on-load**, not trusted. *The spine should document loaders MUST NOT trust the stored id.*
3. **`Observation::Produced` is HTTP-response-shaped**, vacuous for `linear` (X-4 release-once) and `shared` (linearizability), and `arena_view`/`state_trace` are not portable across the JVM oracle / CakeML model / current-net. We add `ObsFieldSet` projection + `Normalizer` normal form; `NwayAgree` projects non-portable fields away; `Golden` may pin them only for one named `backend`. *The spine should acknowledge a normal form / projection on `Observation`.*
4. **MustReject negative obligations (`must_not: ForwardedUpstream`, no-undeclared-egress) are NOT observable** in the spine's `Observation` (only `Produced`/`Absent`): a forwarded smuggle shows up as `Produced{success}`, indistinguishable from a legitimate 200. Detecting non-forwarding needs an **effects/egress-tap channel the spine omits** — and the out-of-process Elide oracle may not expose it at all. *The spine's `Observation` needs an `effects`/handler-invocation tap, or these obligations are unverifiable on some backends.*
5. **`Expectation` has no home for `Kind::Perf`** (its "expected" is a budget). We add a 4th `Expectation::Budget(PerfBudget)` variant; this diverges from the spine's three-variant enum. *Cleaner than parking perf inside `Acceptance`; measurement semantics belong to the perf/runner unit.*
6. **`shared` schedules never take a `Golden`** — their expectation is an invariant predicate (linearizability under X-4), not value bytes. The flat `{Golden|NwayAgree|MustReject|Budget}` enum expresses this only via `NwayAgree`-of-invariant-trace; a dedicated `Invariant` variant would be cleaner but is deferred to the runner unit's predicate vocabulary.
7. **Fuzz import can launder coverage** if `FuzzKeyMap` mis-keys a target: a wrong/missing entry silently mis-attributes a vector to a ledger row (CR-6 violation). We mandate an **exhaustive, totality-checked** `FuzzKeyMap` (missing target = hard error) — a maintenance burden the spine's clean keying model hides.

### Open questions
- **Spec canonicalization ownership.** `VectorId` stability is only as strong as `Spec`'s dCBOR `Canonical` impl. `Spec` (server-node spec / ConfigIR) is large and owned by the spec/orchestrator unit; if its serialization is not schema-stable, every `VectorId` referencing it drifts. We quarantine this by hashing `SpecId` separately and storing specs in the CAS, but the cross-unit stability contract must be made explicit by that unit.
- **dCBOR crate selection.** Needs a Rust dCBOR impl whose canonicalization provably matches what a JVM (Elide) and a CakeML extractee implement; this is a cross-language conformance obligation in its own right and may warrant its own tiny ledger row.

( ⌐■_■ ) one corpus · four primitives · four keys · four backends · every year the same bytes.
