# 47 — THE CONTINUOUS FUZZ-NET (artifact-agnostic, differential-as-vector)

> **The standing successor-rung evidence rail.** Where `40-COMPLETENESS-LEDGER`
> proves a machine *cannot* misbehave and `41-TEST-AND-PERF-SUITE` validates the shipped
> artifact on a frozen corpus, this file specifies the **continuously-running** net that
> keeps every axiomatized / not-yet-proven attacker-facing surface honest *between*
> proofs. CR-2 honesty clause: every axiomatized surface (TLS record-FSM, QUIC engine,
> mesh-crypto, every attacker-facing parser) carries a continuously-run differential
> fuzz net — **subsumed-by-proof OR ported-and-fuzz-netted, no third option, surfaced
> never hidden** (`41-TEST-AND-PERF-SUITE.md:349-357`, `40-COMPLETENESS-LEDGER.md:197`).
>
> The single load-bearing move: **the fuzz-net is not a second machine bolted onto the
> suite. A fuzz input is an un-golden `Vector` run N-way through the same `SutAdapter`;
> divergence = bug.** ( ⌐■_■ )

---

## 47.1 The unification — a fuzz input is an un-golden N-way `Vector`

The fuzz-net introduces **no new observation surface and no new comparison machinery.**
It reuses the fixed seam spine (`42-CONFORMANCE-KIT.md`) verbatim — `SutAdapter`,
`Observation`, the field-intersection differ — and the corpus/runner units, and adds
exactly four things:

1. a **driver** (`FuzzHarness::lift` + `FuzzHarness::drive`) — raw bytes → `Vector` → N-way run,
2. a **classifier** that is a thin reading of the spine's own `Outcome`
   (`42-CONFORMANCE-KIT.md:250-262`) plus the single-backend property arm,
3. a **minter** (`RegressionMint::freeze`) — the *sole* write-path from fuzz-net into the
   corpus, and
4. a build-failing **parity tracker** (`ParityLedger`) that makes the CR-2 "no third
   option" clause computable.

A fuzz iteration is:

```
raw &[u8]
  │  Arbitrary / decode
  ▼
Input (Bytes | Events | ResourceOps | Schedule)          // spine Input, 42:223
  │  FuzzHarness::lift  →  Vector{ expected: NwayAgree | MustReject }   // NO golden
  ▼
FuzzHarness::drive
  │  for each backend b where b.supports(unit, prim) == Supported:
  │      Observation = b.decode_region | run_machine | run_linear | run_shared   // 42:70-90
  ▼
spine differ  →  Outcome { Agree | Divergence | InsufficientProducers }   // 42:250
  │
  ├─ Agree                 → Clean
  ├─ Divergence(field)     → BUG   ─────────────────────┐
  ├─ InsufficientProducers → CR-6 non-match (counted     │  RegressionMint::freeze
  │                          separately, feeds assurance) │      ▼
  └─ (N=1 property mode)   → PropertyViolation ──────────┘  permanent corpus Vector
```

This is the empirical mirror of the ledger: a theorem says the machine *cannot*
misbehave; the fuzz-net is the standing evidence that the **un-proven** surfaces don't —
*and* that an un-covered surface cannot hide. It is the FOURTH consumer of the one DSL
description (`20-ARCHITECTURE.md`), not a pile of `#[test]`s.

### Why the spine already fits — no `ObsMask` is needed

A naive differential fuzzer would diff whole records and false-positive on always-empty
fields (a `varint` parser has no `status`/`headers`/`body`). The spine **already solved
this**: `Produced.fields: ObservedFields` (`42-CONFORMANCE-KIT.md:116-127,145`) plus the
rule that *the differ ranges over the INTERSECTION of `ObservedFields` across genuine
producers, never the whole record* (`42:113-114,238-241`). So the per-target field mask
that both this unit's drafters reached for is **subsumed by `ObservedFields`** — the
fuzz-net contributes *zero* masking logic. A `qpack` target observes
`ARENA_VIEW | ERROR_CLASS | CONSUMED`; an HTTP request target adds
`STATUS | HEADERS | BODY`; the intersection rule makes the diff correct for free.

---

## 47.2 Two regimes, two assurance levels (never conflated)

Conflating "panic-netted" with "differentially-netted" is laundered vacuity (CR-6). The
fuzz-net keeps them as distinct first-class facts.

- **Property mode (N = 1)** — the classic single-backend liveness/safety net every one of
  the 58 existing targets already encodes: *no panic / no over-read / no OOM / no hang /
  `0 < consumed ≤ input` / bounded decompression expansion*. Grounded today, e.g.
  `net/httpe/fuzz/fuzz_targets/chunked_decode.rs:13-20` asserts `consumed > 0` and
  `consumed ≤ data.len()`. These run against `CurrentNet` via the existing
  `pub mod fuzz_api` re-export convention (`net/httpe/src/lib.rs:374`).
- **Differential mode (N ≥ 2)** — fan the *same* raw input to every backend whose
  `supports(unit, prim) == Supported` (`42:75`), and let the spine differ produce an
  `Outcome`. A `Divergence` names the field (`42:255,259`) and is the bug oracle; an
  `Agree` is clean; an `InsufficientProducers` is the CR-6 non-match.

A target's **declared regime** is its `FuzzMode`. Its **assurance level** is *computed at
runtime*, not merely declared:

- `PanicNetted` — ran against one genuine producer.
- `DifferentialNetted { supporting }` — ≥2 genuine producers actually `Produced` on the
  keyed field across the campaign.

This split is load-bearing because **today only `CurrentNet` exists** (`42:268,327-335`).
For most surfaces the differential net degrades toward N=1 right now; `FormalModel` joins
for `region`/`machine`/`linear` units as their HOL4 theories become extraction-executable
(`harness/executable-model-bridge`, `41:334`), and `ExternalOracle` joins for the
wire-reachable `region`/`machine` units (`42:285,322-323`). The parity ledger records the
*actual* level so a panic-only target can never be reported as differential evidence.

---

## 47.3 CR-6 at the fuzz classifier (sacred)

CR-6 is enforced by **consuming**, not re-implementing, the spine's two-granularity
firewall (`42:229-245`):

1. **Backend-level** — `Observation::Absent { reason }` (`42:141`) drops a backend from
   the comparison set; it *never* masks a disagreement among the rest.
2. **Field-level** — `Agree` on a field requires ≥2 backends that both `Produced` *and*
   whose `ObservedFields` intersection includes that field (`42:238-241`).

A `Divergence` therefore already requires ≥2 *genuine producers*; fewer ⇒
`Outcome::InsufficientProducers { absent }` (`42:257`), which is counted separately and
**never as agreement**. The fuzz-net adds one fuzz-specific guard the spine does not name:

> **Absent-density demotion.** If a `Differential` target's partner backend reports
> `Absent` for an overwhelming fraction of random inputs (e.g. `FormalModel` only models
> the happy path), the differential oracle silently degenerates to N=1 while coverage
> *looks* healthy. `ParityReport.absent_density` accumulates the per-`(target, backend)`
> Absent rate across the campaign; a target whose differential partner exceeds the
> threshold is **demoted to `PanicNetted`** in the report. It cannot claim differential
> coverage while its oracle is silently skipping the input space.

**`MustReject` is not byte-equality.** Two backends may both *correctly* reject a smuggling
vector with different `error_class` (400 vs 501; `41:179`). The classifier compares under
an `ErrorClass` *reject-class equivalence* — both rejecting is agreement; only
`RejectVsAccept` (one backend lets the input through where another rejects) is a hard
security divergence. The spine's `ErrorClass` (`42:214-220`) and
`Expectation::MustReject { error_class }` (`42:368`) carry the taxonomy; this unit defines
the equivalence relation over it (see §47.8 `reject_equiv`).

---

## 47.4 The fuzz-target inventory

### 47.4.1 Existing — 58 targets (all Property mode today; attacker-facing ones upgrade to Differential)

Counts verified against the tree (`ls net/*/fuzz/fuzz_targets`):

| dir | count | targets |
|---|---:|---|
| `net/httpe/fuzz` | 23 | `h1_request_parse`, `h1_response_parse`, `header_parse`, `chunked_decode`, `h2_frame_parse`, `h2_hpack_decode`, `h2_settings_parse`, `huffman_decode`, `h3_frame_parse`, `h3_qpack_decode`, `websocket_frame_parse`, `websocket_frame`, `url_routing`, `basic_auth_parse`, `jwt_parse`, `html_rewriter_parse`, `auth_request_url_parse`, `rate_limit_key_parse`, `cgi_response_parse`, `sse_event_parse`, `accept_encoding_parse`, `grpc_timeout_parse`, `connect_target_parse` |
| `net/transport/fuzz` | 18 | `varint`, `packet_parse`, `quic_packet_parse`, `quic_initial_parse`, `frame_decode`, `transport_params`, `ack_ranges`, `datagram_decode`, `engine_datagram`, `version_negotiation`, `connection_id_parse`, `fuzz_loss_detection`, `fuzz_stream_reassembly`, `fuzz_crypto_reassembly`, `fuzz_engine_handshake`, `fuzz_congestion_control`, `cqe_processing`, `sqe_construction` |
| `net/wireguard/fuzz` | 6 | `wg_packet_dispatch`, `noise_handshake`, `wg_config_parse`, `allowed_ips`, `derp_frame_parse`, `derp_http_response` |
| `net/tailscale/fuzz` | 6 | `ts2021_frame_parse`, `netmap_parse`, `disco_message_parse`, `stun_message_parse`, `derp_frame_parse`, `acl_rule_parse` |
| `net/dns/fuzz` | 2 | `dns_message_parse`, `svcb_rdata_parse` |
| `net/pki/fuzz` | 3 | `pem_parse`, `x509_cert_parse`, `sct_parse` |
| **TOTAL** | **58** | matches `41-TEST-AND-PERF-SUITE.md:199-222` |

Each becomes a `FuzzTarget { status: Existing }` in `registry()`, keyed to its `41` C.2
fuzz row and its `40-LEDGER` row. **Migration is mechanical:** each `fuzz_target!` body is
rewritten to call `FuzzHarness::drive`. The property assertions that are *already inline*
(see `chunked_decode.rs`) become the `Property` arm's `StructuralInvariant`s; for
attacker-facing targets the regime becomes
`Differential { backends: [CurrentNet, FormalModel, ExternalOracle] }` and the inline
assertions become `Observation` fields the spine differ compares — so the per-backend
assertion logic is written once, not duplicated.

### 47.4.2 The 15 NEW = needs-authoring targets (the CR-2 backlog, mostly GAP rows)

These are disproportionately the **GAP / un-proven** ledger rows — that is the whole CR-2
point made concrete: a row with no theorem MUST be fuzz-netted *now*, because a continuous
fuzz-net is its **only** standing successor-rung evidence until the proof lands.

| NEW target | primitive | `40-LEDGER` row | `41` C.2 case | status |
|---|---|---|---|---|
| `proxy_protocol_parse` | region | PROXY v1/v2 (`40:123`, F-8, modeled-spoof-defense) | `NEW_fuzz_proxy_protocol_v1v2` | NeedsAuthoring |
| `socks_parse` | machine | SOCKS 4/4a/5 server (`40:71`, F-8, region+machine) | `NEW_fuzz_socks_parse` | NeedsAuthoring |
| `static_files_resolve` | region | static serve / path-traversal (§A; sec `41:182`) | `NEW_fuzz_static_files_path` | NeedsAuthoring |
| `fastcgi_record` | region | FastCGI (`40:73`, F-8, region+machine) | `NEW_fuzz_fastcgi_record` | NeedsAuthoring |
| `clienthello_sni` | region | ALPN/SNI (`40:113`) + L4 SNI extract (`40:69`) | `NEW_fuzz_tls_clienthello_sni` | NeedsAuthoring |
| `connect_ip_capsule` | machine | MASQUE CONNECT-IP + Capsule (`40:66`, F-4) | `NEW_fuzz_connect_ip_capsule` | NeedsAuthoring |
| `cookie_parse` | machine | cookie jar RFC 6265bis (`40:174`, F-11, modeled) | `NEW_fuzz_cookie_jar_parse` | NeedsAuthoring |
| `ocsp_response_parse` | region | **OCSP stapling (`40:117`, GAP ⚠)** | `NEW_fuzz_ocsp_response_parse` | NeedsAuthoring |
| `mtls_client_cert` | machine | **mTLS / client-cert (`40:118`, GAP ⚠)** | `NEW_fuzz_mtls_client_cert_chain` | NeedsAuthoring |
| `trace_context_parse` | region | **W3C trace-context (`40:169`, GAP)** | `NEW_fuzz_w3c_trace_context` | NeedsAuthoring |
| `grpc_web_frame` | machine | gRPC-Web transcode (`40:74`, modeled) | `NEW_fuzz_grpc_web_transcode` | NeedsAuthoring |
| `acme_state` | machine | **ACME DNS-01/HTTP-01 FSM (`40:115`, GAP)** | `NEW_fuzz_acme_challenge_state` | **NeedsSansIoRefactor** |
| `ct_proof_verify` | region | **CT-log RFC 6962 Merkle proof (`40:119`, GAP ⚠)** | `NEW_ct_log_merkle_proof_verify` | NeedsAuthoring |
| `l4_udp_forward` | machine | **L4 per-client UDP forward (`40:70`, GAP)** | `NEW_l4_udp_forward_fuzz` | **NeedsSansIoRefactor** |
| `upstream_proxy_chain` | machine | **upstream-proxy chaining HTTP/SOCKS (`40:64`, GAP)** | `NEW_upstream_proxy_chain_fuzz` | **NeedsSansIoRefactor** |

Most NEW targets are thin `fuzz_target!` bodies over an *existing* sans-IO parser that
already returns the tri-state `ParseResult<T> { Complete { value, consumed } | Incomplete
| Error }` (`net/httpe/src/protocol/socks.rs:84-92`) — that convention is *exactly* the
spine's `ParseClass` (`42:188`), so they plug into `SutAdapter` for free.

**Three targets carry a distinct, honestly-surfaced status — `NeedsSansIoRefactor`** — not
merely `NeedsAuthoring`: `acme_state` (an orchestrator FSM, IO-coupled), `l4_udp_forward`
(a datapath), and `upstream_proxy_chain` (a multi-hop egress resolver). These have **no
`ParseResult`-shaped sans-IO entrypoint today**; a pure `(state, bytes) → (state', events,
out)` seam (`20-ARCHITECTURE.md:170`) must be *carved out of the IO-coupled code* before a
fuzz body can ride `SutAdapter`. They are blocked on a refactor, not on writing a target,
and `meta/gap-row-needs-authoring-tracker` (`41:356`) surfaces that distinction rather than
hiding it.

A `NeedsAuthoring` / `NeedsSansIoRefactor` target is **not `Live`** and therefore **does
not satisfy parity** (§47.6) — the 15 NEW rows correctly read as *not-yet-fuzz-netted*
until landed, and cannot be laundered as covered.

---

## 47.5 Divergence / crash → permanent regression `Vector` (the ratchet)

A finding is promoted into the corpus unit's content-addressed corpus
(`harness/vector-corpus-format`, `42:352-369`) via **one** write-path,
`RegressionMint::freeze` — there is no separate regression harness:

1. **Minimize** — `cargo fuzz tmin` for a crash/property violation; bisection on the raw
   input for a `Divergence`, shrinking to the smallest input that preserves the verdict.
2. **Freeze** — `ContentHash(minimized)` becomes the corpus key (`42:353,365`).
3. **Classify & pin `expected`** — a crash / over-read / property violation →
   `Vector { kind: Security, expected: MustReject { error_class } }`; a cross-backend
   `Divergence` → `Vector { kind: Differential, expected: NwayAgree }` pinned to the agreed
   `Observation` once resolved. `FuzzProvenance` (target, original + minimized hash,
   discovering backends, date, `Resolution`) rides alongside.
4. **Replay forever** — per-PR runs the frozen vector through the *same* N-way runner
   (`41:342`), deterministic and blocking-on-red. The `ParsedRequest` flat-arena / sidecar
   invariants (`net/httpe/src/parsed_request.rs:685`, `SIDECAR_OFFSET_BASE = 0x8000_0000`)
   are re-asserted on it on every CI run.

The corpus is the cumulative memory; the fuzz-net is therefore a **ratchet**, never a flaky
one-shot. `FuzzFinding::into_vector` / `RegressionMint::freeze` is the only new code on this
path.

---

## 47.6 The parity meta-gate — `meta/orb-14-fuzz-target-parity`

The CR-2 honesty clause is made **computable rather than curated**: the gate is a
*set-difference over the ledger's attacker-facing rows*, not a hand-maintained list. For
every `40-LEDGER` row flagged `attacker_facing`, `ParityLedger::gate()` requires exactly
one of:

| `ParityCoverage` | meaning | gate |
|---|---|---|
| `SubsumedByProof { theory }` | a discharged HOL4 theorem proves no-misbehavior | fuzz optional |
| `FuzzNetted { target, assurance, last_run }` | a `Live` registry target binds this `LedgerKey`; standing evidence | must be fresh |
| `Uncovered { reason }` | **the forbidden THIRD option — neither proof nor fuzz** | **hard build failure** |

`gate()` returns `Err(Vec<ParityRow>)` listing every `Uncovered` attacker-facing surface —
the un-hideable gap list. A `FuzzNetted` row whose `last_run` is stale also fails. The
report is a surfaced table (`ParityReport.rows`), never a silent skip.

**The axiom rows that MUST carry a fuzz-net are enumerable straight from the ledger** — and
this *is* CR-2:

- **TLS record-FSM** — `40:112` (axiom→R5.4, ADR-N4) → `meta/fuzz-net-tls-axiom-NEW`
- **crypto primitives (AEAD/KDF/sig)** — `40:114` (modeled-as-axiom, retire at R5.4) →
  fuzz-netted until then
- **WireGuard / DISCO / DERP mesh-crypto** — `40:102,104,105` →
  `meta/fuzz-net-mesh-crypto-axiom`
- **QUIC engine** — `40:132` → `meta/fuzz-net-quic-axiom`
- **kTLS / NIC-inline TLS** — `40:126` (device-axiom) → fuzz-netted at the boundary
- **TCP/IP (HTTP/1/2 + CapTP-over-TCP legacy)** — `40:197` (ADR-N6): *a named CR-2 axiom
  with NO successor rung — never proven*, so it must be **fuzz-netted forever**. This is the
  purest instance of the meta-gate.

`harness/continuous-fuzz-net` and `meta/gap-row-needs-authoring-tracker` (`41:355-356`) are
the standing harness rows this gate drives.

---

## 47.7 The `shared` / `linear` primitives — concurrency-fuzz as `Vector` generators

The `shared` oracle is **not** cross-backend byte-agreement — it is an **invariant
predicate under an interleaving** (linearizability / no-lost-wakeup / refcount-conserved /
no-use-after-release / no-UB). The spine confirms this structural asymmetry: for `shared`,
`ExternalOracle` is `Absent` ("cannot inject schedules over IPC") and `FormalModel` is
`Absent` ("Iris logical-atomicity is a hand-proof, **not extraction-executable** as a
runtime schedule enumerator") — leaving `CurrentNet` as the *single* producer until the
engine lands (`42:300-302,324-335`). A `shared` vector therefore **cannot** use `NwayAgree`
and is rejected at registration if it tries (`42:374-376`); its evidence is the Iris proof
standing *beside* the runner, plus the concurrency-fuzz net standing *in front* of it.

So `shared`/`linear` are fuzzed by a **different engine class** — loom (exhaustive),
shuttle (randomized, scales past 4 threads), miri (UB) — but presented through the **same
`Vector` surface** by treating the concurrency engine as a **`Vector` generator**:

- `ConcurrencyHarness::explore` lets loom/shuttle pick interleavings *internally* and
  checks a `SharedInvariant` per schedule.
- On `ConcVerdict::Violated { schedule, invariant }`, the discovered interleaving is
  *frozen* into a deterministic `Schedule` — the spine's `Schedule { threads: Vec<Vec<OpId>>,
  seed }` (`42:203`) is expressive enough to pin a concrete thread-op order — and emitted as
  `Vector { primitive: Shared, input: Input::Schedule, expected: MustReject }` replayable via
  `SutAdapter::run_shared` (`42:89`), promoted identically to a byte divergence.

Existing harnesses become `ConcurrencyHarness` / `ConcurrencyTarget` instances discharging
the X-4 exactly-once token discipline and the Iris obligations on the hot path
(`41:229-234`, `21-FORMAL-MODEL.md:54-72,95-97`):
`net/httpe/tests/loom_generation_counter.rs`, `loom_notifying_sender.rs`,
`loom_response_handle.rs`, `loom_channel_notifier.rs`,
`net/transport/tests/loom_cq_wakeup.rs`, `shuttle_cq.rs`,
`net/transport/tests/miri_uring.rs`. The standing meta is
`meta/concurrency-model-loom-shuttle` (`41:354`).

---

## 47.8 CI cadence — continuous ≠ per-PR (`41` F.2)

- **Per-PR (blocks on red):** replay the frozen regression corpus N-way + run the property
  targets on their seed corpora + targeted loom/miri runs. Deterministic, fast
  (`41:342`).
- **Nightly / standing:** unbounded coverage-guided libFuzzer + shuttle-random exploration
  under time/total budgets; new crashes/divergences auto-minimize, auto-file, and
  auto-promote via `RegressionMint`.
- **`ExternalOracle` cadence:** out-of-process (CR-3, `42:280-284`), it **cannot ride the
  10⁴–10⁶ exec/s hot mutation loop** (IPC round-trip per input is fatal). It runs at a
  *sampled/batched* cadence, or only against the *minimized finding*. The per-PR frozen
  corpus replays its findings N-way at normal test speed. The provenance firewall still
  holds: Elide is *read* via subprocess/IPC, **never linked**
  (`harness/oracle-provenance-firewall`, `42:290-291`).
- **Gate:** `ParityLedger::gate()` runs in CI; any `Uncovered` attacker-facing surface, or
  any `FuzzNetted` target whose `last_run` is stale, **fails the build**.

---

## 47.9 Rust signatures contributed to `net/conformance-kit`

```rust
// ── net/conformance-kit/src/fuzznet.rs — UNIT 6 contribution. ─────────────────
// Rides the FIXED spine (42-CONFORMANCE-KIT): SutAdapter, Observation, Support,
// ObservedFields, Outcome, DivergingField, BackendId, Primitive, UnitId, Schedule,
// ResourceOp, ErrorClass — and the corpus unit's Vector / Expectation / Input / Spec /
// LedgerKey / CaseKey / Kind / ContentHash. It adds the driver + classifier + minter +
// parity tracker, and the resource sidecar — NOTHING the spine already provides.

use net_conformance_kit::{
    SutAdapter, Observation, Support, ObservedFields, Outcome, DivergingField, BackendId,
    Primitive, UnitId, Schedule, ErrorClass, // spine (unit 1)
    Vector, Expectation, Input, Spec, LedgerKey, CaseKey, Kind, ContentHash, // corpus unit
};
use std::time::Duration;

/// One registered continuous-fuzz target. Binds a libFuzzer entrypoint to the
/// ledger/suite keying so the parity gate is a computable set-difference (§47.6).
pub struct FuzzTarget {
    pub name:            &'static str,   // "h1_request_parse" .. "upstream_proxy_chain"
    pub primitive:       Primitive,      // Region | Machine | Linear | Shared
    pub unit:            UnitId,          // the DSL unit it drives (1:1 with a 40-LEDGER row)
    pub ledger_row:      LedgerKey,      // 40-LEDGER row this attacker surface covers
    pub suite_case:      CaseKey,        // 41 C.2 fuzz row (NEW_fuzz_* for the 15)
    pub attacker_facing: bool,           // drives the parity meta-gate (§47.6)
    pub mode:            FuzzMode,
    pub seed:            CorpusRef,       // content-addressed seed-corpus dir
    pub status:          TargetStatus,
}
pub struct CorpusRef(pub &'static str);
pub fn registry() -> &'static [FuzzTarget];   // all 58 existing + 15 NEW

/// `Live` is the ONLY status that satisfies parity. The two NEW statuses surface the
/// authoring-vs-refactor distinction (§47.4.2) instead of hiding it.
pub enum TargetStatus { Live, NeedsAuthoring, NeedsSansIoRefactor }

pub enum FuzzMode {
    /// N=1 single-backend invariant net (the 58 legacy libfuzzer targets).
    Property    { invariants: &'static [StructuralInvariant], budget: ResourceBudget },
    /// N>=2 cross-backend; the spine differ (ObservedFields intersection) does the masking.
    Differential { backends: &'static [BackendId] },
}
pub enum StructuralInvariant { NoPanic, NoOob, BoundedConsumed, NoHang, BoundedExpansion(u32), NoOom }

/// The resource sidecar the spine's value-only `Observation` cannot carry (§47.10 tension).
/// no-hang / no-OOM / decompression-bomb ratio (41 C.1:186) live here, not in Observation.
pub struct ResourceBudget { pub wall: Duration, pub peak_rss: u64, pub max_expansion: u32 }
pub struct ResourceSample { pub wall: Duration, pub peak_rss: u64, pub expansion: u32 }

/// The single entrypoint every `fuzz_target!(|data: &[u8]| ...)` body calls.
pub trait FuzzHarness {
    /// raw fuzz bytes -> candidate Vector (expected = NwayAgree | MustReject; never Golden).
    fn lift(&self, target: &FuzzTarget, raw: &[u8]) -> Vector;
    /// run one iteration N-way over every backend whose supports(unit,prim)==Supported,
    /// then classify by reading the spine's Outcome. `sample` carries the sidecar.
    fn drive(
        &self,
        target:   &FuzzTarget,
        raw:      &[u8],
        backends: &[&dyn SutAdapter],
        sample:   &ResourceSample,
    ) -> FuzzOutcome;
}

/// The classifier output — a THIN reading of the spine `Outcome` plus the property arm.
pub enum FuzzOutcome {
    Clean,
    /// N=1 invariant breach (panic caught by libfuzzer/ASAN is reported here post-hoc).
    PropertyViolation { kind: StructuralInvariant, backend: BackendId, detail: String },
    /// Differential verdict, consumed verbatim from the spine differ (42:250):
    ///   Outcome::Divergence            -> the bug
    ///   Outcome::InsufficientProducers -> CR-6 non-match (feeds absent-density demotion)
    ///   Outcome::Agree                 -> normalized to Clean by drive()
    Differential(Outcome),
}

/// SOLE write-path from fuzz-net into the corpus unit's corpus (§47.5).
pub struct RegressionMint;
impl RegressionMint {
    pub fn freeze(target: &FuzzTarget, raw: &[u8], outcome: &FuzzOutcome) -> RegressionVector;
}
pub struct RegressionVector { pub vector: Vector, pub provenance: FuzzProvenance }
pub struct FuzzProvenance {
    pub target:       &'static str,
    pub original:     ContentHash,
    pub minimized:    ContentHash,
    pub discovered:   Timestamp,
    pub finding_kind: FindingKind,
    pub backends:     Vec<BackendId>,   // who produced / diverged
    pub resolution:   Resolution,
}
pub enum FindingKind { Crash, PropertyViolation, Divergence, ConcurrencyViolation }
pub enum Resolution { FixedInBackend(BackendId), PinnedNwayAgree, PinnedMustReject, AcceptedTolerance }
pub struct Timestamp(pub u64);

/// `MustReject` reject-class equivalence (§47.3): both-reject == agreement; only
/// one-rejects-one-accepts is a hard security divergence.
pub fn reject_equiv(left: &ErrorClass, right: &ErrorClass) -> bool;

// ── 'shared' / 'linear': concurrency-fuzz presented as Vector generators (§47.7) ──
pub struct ConcurrencyTarget {
    pub name:       &'static str,
    pub engine:     ConcEngine,
    pub invariant:  SharedInvariant,
    pub unit:       UnitId,
    pub ledger_row: LedgerKey,
}
pub enum ConcEngine { Loom, Shuttle, Miri }
pub enum SharedInvariant { Linearizable, RefcountConserved, NoLostWakeup, NoUseAfterRelease, NoUb }
pub trait ConcurrencyHarness {
    fn engine(&self) -> ConcEngine;
    /// loom/shuttle/miri pick interleavings INTERNALLY; on Violated, `schedule` pins a
    /// deterministic interleaving replayable via SutAdapter::run_shared.
    fn explore(&self, target: &ConcurrencyTarget, backend: &dyn SutAdapter) -> ConcVerdict;
}
pub enum ConcVerdict {
    Held     { schedules_explored: u64 },
    Violated { schedule: Schedule, invariant: SharedInvariant },
    Ub       { detail: String },   // miri
}
// Violated.schedule -> Vector{ primitive: Shared, input: Input::Schedule, expected: MustReject }

// ── the parity meta-gate (CR-2: subsumed-by-proof OR fuzz-netted, surfaced) (§47.6) ──
pub struct ParityLedger { pub rows: Vec<ParityRow> }
pub struct ParityRow { pub surface: &'static str, pub ledger_row: LedgerKey, pub coverage: ParityCoverage }
pub enum ParityCoverage {
    SubsumedByProof { theory: TheoryRef },
    FuzzNetted      { target: &'static str, assurance: FuzzAssurance, last_run: RunRecord },
    Uncovered       { reason: String },   // THE FORBIDDEN STATE
}
pub struct TheoryRef(pub &'static str);
pub struct RunRecord { pub at: Timestamp, pub iterations: u64 }

/// Computed at runtime, never merely declared (§47.2): a Differential target whose
/// partner Absent-rate exceeds threshold is demoted to PanicNetted.
pub enum FuzzAssurance { PanicNetted, DifferentialNetted { supporting: Vec<BackendId> } }

pub struct ParityReport {
    pub rows:           Vec<ParityRow>,
    pub absent_density: Vec<(/*target*/ &'static str, BackendId, /*absent_rate*/ f64)>,
}
impl ParityLedger {
    /// Any Uncovered attacker-facing surface (or stale FuzzNetted) => Err(gaps):
    /// the un-hideable list. Hard build failure in CI.
    pub fn gate(&self) -> Result<ParityReport, Vec<ParityRow>>;
}

// ── proposed spine addition (see §47.10 tension #1), NOT owned here ──
// trait SutAdapter { fn exec_cost(&self) -> CostClass; }
// enum CostClass { InProcess, Subprocess, Extracted }
```

---

## 47.10 Seams

### Provides (to `net/conformance-kit` and the rest of the kit)

- `FuzzTarget` + `registry()` — the inventory of all 58 existing + 15 NEW targets, each
  keyed to `(Primitive, UnitId, LedgerKey, CaseKey, attacker_facing, FuzzMode, TargetStatus)`;
  this keying is what makes the parity gate a computable set-difference.
- `FuzzMode` / `StructuralInvariant` / `ResourceBudget` / `ResourceSample` — the two-regime
  declaration + the resource sidecar.
- `FuzzHarness::{lift, drive}` — raw bytes → un-golden `Vector` → N-way run; the single
  function every `fuzz_target!` body calls.
- `FuzzOutcome` + `reject_equiv` — the classifier (a thin reading of the spine `Outcome`)
  and the `MustReject` reject-class equivalence.
- `RegressionMint::freeze` → `RegressionVector` + `FuzzProvenance` — the *sole* write-path
  from fuzz-net into the corpus (the ratchet).
- `ConcurrencyHarness` / `ConcurrencyTarget` / `ConcVerdict` / `SharedInvariant` — the
  loom/shuttle/miri net for `shared` + `linear`, presented as `Vector` generators.
- `ParityLedger` / `ParityCoverage` / `ParityReport` / `FuzzAssurance` /
  `ParityLedger::gate()` — the CR-2 build-failing parity meta-gate, with the absent-density
  demotion that keeps differential assurance honest.

### Consumes

- **From the fixed spine (unit 1, `42-CONFORMANCE-KIT`):** `SutAdapter` (all four
  `run_*`/`decode_region` + `supports(unit, prim)`), `Observation::{Produced, Absent}`,
  `Support`, **`ObservedFields`** (subsumes any per-target field mask), **`Outcome`** +
  `DivergingField` (the fuzz classifier *is* a reading of these — zero new comparison
  logic), `BackendId`, `Primitive`, `UnitId`, `Schedule`, `ResourceOp`, `ErrorClass`.
- **From the corpus unit** (Unit 2 in the North-Star numbering; "unit 5 / corpus unit" in
  `42`): `Vector`, `ContentHash`, `Input`, `Spec`, `Expectation::{NwayAgree, MustReject}`
  (fuzz Vectors are precisely the golden-less ones), `LedgerKey`, `CaseKey`, `Kind`, and the
  corpus writer/loader `RegressionMint` calls.
- **From the N-way runner** (`harness/three-way-runner` generalized, `41:328-338`,
  `42:247-262`): the differ that produces `Outcome` and the `{Agree | Divergence |
  InsufficientProducers}` classification — fed un-golden Vectors and read straight.
- **From the ledger:** the `attacker_facing` flag per row and the `subsumed_by_proof`
  linkage; from the proof index, `TheoryRef`s.

### Tensions with the fixed spine

1. **No backend cost class (`ExternalOracle` is out-of-process).** The spine assumes a backend
   is re-enterable per-input cheaply, but CR-3 makes Elide subprocess/IPC (`42:280-284`). At
   libFuzzer rates an IPC round-trip per input is fatal. **Resolution:** the standing
   differential fuzz runs Elide sampled/batched or only on minimized findings; the per-PR
   frozen corpus replays N-way at test speed. **Proposed spine addition:**
   `SutAdapter::exec_cost(&self) -> CostClass { InProcess | Subprocess | Extracted }` so the
   fuzz scheduler can pick which backends ride the hot mutation loop. Flagged, not silently
   diverged.

2. **Resource invariants escape `Observation`.** no-hang (wall-clock), no-OOM (peak RSS),
   bounded decompression-expansion (HPACK/QPACK bomb ratio, `41:186`) are *cost*
   observations the spine's value-only `Observation` (`42:144-155`) cannot carry. This unit
   adds `ResourceBudget` / `ResourceSample` as a sidecar threaded through `drive`; the spine
   may want to acknowledge a resource projection rather than leave it adapter-side.

3. **`shared`/`linear` differential is structurally asymmetric, by the spine's own table.**
   For `shared`, both `ExternalOracle` and `FormalModel` are `Absent` (`42:324-325,300-302`),
   so it is never N-way byte-diffed — it is *Iris-proven OR loom/shuttle-netted*, a
   per-primitive instance of the parity meta-gate, not a differential vector. The spine's
   `run_shared(schedule)` implies a *caller-chosen* schedule, but loom/shuttle choose
   internally. **Resolution:** model the concurrency engine as a `Vector` *generator* whose
   per-schedule failure freezes a concrete `Schedule` replayable via `run_shared`; this is
   sound only because `Schedule { threads, seed }` (`42:203`) can pin a deterministic
   interleaving — which it can for an enumerated thread-op order.

4. **CR-6 has a fuzz-specific silent-degradation mode the spine doesn't name.** `Support` is
   per-unit, not per-input; a backend that is `Absent` for the *overwhelming majority* of
   random inputs degenerates the differential to N=1 while coverage looks healthy. Handled
   here by `ParityReport.absent_density` + the `FuzzAssurance` demotion, but the spine may
   want a `differential_density` meta the runner accumulates natively.

5. **Coverage-guided mutation instruments one in-process backend.** libFuzzer/SanitizerCoverage
   sees only `CurrentNet`'s coverage map; the out-of-process Elide and the HOL4-extracted
   model cannot share it. The mutator optimizes `CurrentNet`'s coverage while divergence is
   checked N-way — a structural blind spot where a bug lives only in an *uncovered* path of
   an oracle the mutator can't see. The harness accepts driving-backend asymmetry and (later)
   cross-pollinates per-backend corpora; flagged, not resolved.

6. **Three NEW targets need a sans-IO refactor before they can ride `SutAdapter` at all.**
   `acme_state`, `l4_udp_forward`, `upstream_proxy_chain` (`40:115,70,64`) have no
   `ParseResult`-shaped entrypoint; a pure `(state, bytes) → (state', events, out)` seam
   must be carved out of IO-coupled code first. Surfaced as `TargetStatus::NeedsSansIoRefactor`,
   distinct from `NeedsAuthoring`, in `meta/gap-row-needs-authoring-tracker`.

---

```
poem:
one corpus, four machines, a thousand random bytes —
where they disagree, the truth was never proven.
freeze the witness, keep it forever; the ledger
makes the third option impossible. ( ⌐■_■ )
```
