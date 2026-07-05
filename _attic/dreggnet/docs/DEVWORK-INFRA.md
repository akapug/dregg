# DEVWORK-INFRA — the prioritized infra / ops / maturity dev-work list

A grounded sweep of DreggNet's **infrastructure, operations, quality, and
maturity** for dev work. Read-only census; every item is tied to actual
file:line / path at HEAD (`dev`, 2026-06-30). Honest about real state — a "named
seam" is classified, not laundered. Out of scope (a parallel swarm owns them):
`circuit/`, `metatheory/`, the substrate/VK epoch.

This is the **ops/maturity companion** to `docs/MATURATION-PLAN.md` (which
sequences the whole DreggNet+dregg roadmap across five axes). Where MATURATION
already names an item (§2 deploy, §3 measure/o11y) this doc grounds it to code
and re-ranks by *value ÷ effort*; it does not restate the plan.

**Effort:** S = <1 day · M = 1–5 days · L = 1–2 weeks.
**Autonomy:** SAFE = green-gated + reversible, no prod/money/key/VK touch ·
REVIEWED-GO = live-edge / registry-creds / license flip · DECISION = needs an
ember architectural call first.

---

## TOP 10 — ranked by leverage (highest value ÷ lowest effort first)

| # | Item | Path | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| 1 | **Commit + wire the 8 service-layer benches into CI/Makefile** (they exist, are real, are *untracked* + run nowhere) | `*/benches/*.rs`, `Makefile`, `.github/workflows/ci.yml` | S | HIGH | SAFE |
| 2 | **Rev-pin the branch-floated forks** (rustls / ntex×16 / hickory) — reproducibility hazard | `Cargo.toml:140-161` | S | HIGH | SAFE |
| 3 | **node-agent tests** — the live compute backend, 311 LOC, ZERO tests | `deploy/node-agent/src/main.rs` | S | HIGH | SAFE |
| 4 | **Structured logging across the control-plane core** — scheduler/provider/orchestrator-tick emit ~nothing | `control/src/{scheduler,provider,orchestrator}.rs` | M | CRITICAL | SAFE |
| 5 | **Run + calibrate the workload-simulation suite** — the only place concurrency + economy invariants are exercised; never runs in CI | `tests/workload/tests/*` | M | CRITICAL | SAFE |
| 6 | **Control-plane `/metrics` + orchestrator counters** (placement latency, unplaced depth, lapse-by-reason) | `control/src/orchestrator.rs`, new `metrics.rs` | M | HIGH | SAFE |
| 7 | **Gateway test lane** — CI only `cargo build`s the gateway/net; routing/TLS/vhost untested anywhere | `.github/workflows/ci.yml`, `gateway/tests/` | M | HIGH | SAFE |
| 8 | **Orchestrator dispatch timeout + stuck-`Running`/orphaned-work reaper** | `control/src/orchestrator.rs:296,336,348` | M | HIGH | SAFE |
| 9 | **Harden `deploy-edge.sh` + Postgres-service CI lane** (the manual redeploy is the #1 ops drag) | `deploy/staging/deploy.sh`, `.github/workflows/ci.yml` | M | HIGH | SAFE (author/dry-run); REVIEWED-GO (live ship) |
| 10 | **receipt + sandstorm-bridge e2e tests** — correctness/security boundaries with 0 integration tests | `receipt/tests/`, `sandstorm-bridge/tests/` | M | MED-HIGH | SAFE |

**The highest-leverage maturity moves**, in one breath: the *measurement* and
*observability* substrate is built but not wired (benches uncommitted, control
plane metrics-blind and log-silent) — closing that is mostly plumbing, not
research, and it is what turns "it runs" into "we can operate it." The biggest
*reliability* truth to face is a decision, not a fix: durability is host-local,
so there is **no exactly-once across node loss** (item R1). The biggest *ops*
drag is the hand-cranked redeploy; its automation is SAFE to author.

---

## 1. TESTING / QUALITY

CI (`.github/workflows/ci.yml`) runs four jobs: macOS `cargo test` over **7**
service crates (cli/durable/exec/bridge/control/webapp + the macOS job omits
`ops`), a Linux `cargo build` of the gateway, a hard `fmt` gate, and an
**advisory** clippy. That leaves real surface untested.

### 1.1 Untested / thinly-tested high-risk code

| Item | Path | State | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **T1** node-agent (live backend) has **0 tests** | `deploy/node-agent/src/main.rs` (311 LOC) | HTTP weld + server loop unproven offline | S | HIGH | SAFE |
| **T2** receipt: **0 integration tests** (6 shallow unit) | `receipt/` | tamper/witness/chain-of-custody untested e2e | M | MED-HIGH | SAFE |
| **T3** sandstorm-bridge: **0 integration tests** (67 unit) | `sandstorm-bridge/src/` | security-boundary weld untested end-to-end | M | MED-HIGH | SAFE |
| **T4** gateway tested only by `cargo build` in CI | `gateway/` (59 unit + 1 integ, Linux-only) | routing/TLS/vhost edges (slow-loris, header-injection, chunked bombs) only found post-deploy | M | HIGH | SAFE |
| **T5** net/ stack (~4,300 unit tests) is **built, never run** in CI | `net/*` | platform-specific bugs invisible | M-L | MED | SAFE (Linux CI test job) |
| **T6** scheduler: 4 good unit tests, **no concurrency stress** | `control/src/scheduler.rs` (333 LOC) | race safety under N-concurrent `place()` unproven | M | MED | SAFE |
| **T7** `ops` not in CI matrix (36 unit tests, runs only locally) | `ops/` | dashboard regressions slip | S | MED | SAFE |
| **T8** Postgres durable-resume gated out of CI | `durable/tests/durable_resume_pg.rs` (3 `#[ignore]`) | SQL txn / recovery / idempotency under load only tested by hand | M | HIGH | SAFE (CI pg service container) |

### 1.2 The workload-simulation suite — the system-level blind spot

`tests/workload/tests/*` drives the **real** `Orchestrator` / `ConservingLedger`
under multi-tenant, concurrent, fault-injected load (6 scenarios: scale_load,
multi_tenant_isolation, failure_injection, economy_under_load, durability,
endurance_soak). It is **scaffolded + partially filled** — `scale_load` has real
SLO assertions (≥250/s, p99 ≤2s); several others carry TODO calibration (the
multi-tenant adversarial isolation asserts, failure-injection SLO thresholds,
the concurrent-settle race constructor, the 8-hour soak leak ceilings). It is
deliberately out of `make test` (every scenario `#[ignore]`d, 1M-second
timeouts) and **never runs in CI**.

This is the single largest quality gap: **the economy conservation/exactly-once
invariants are otherwise only exercised at 1-2 leases in isolation.** Running it
once overnight (already a `make test-workload` target), filling the TODO
asserts, and calibrating thresholds is item #5 in the top-10.

### 1.3 Doc accuracy

`docs/TESTING.md` is accurate to CI; one correction worth landing: it says the
net stack is "build and test on Linux only" but **CI only builds, never tests**
it — make that explicit (T5 follows from it).

---

## 2. OBSERVABILITY / TRACING / METRICS

**What is real + live:** `gateway/src/metrics.rs` (203 LOC, hand-rolled
Prometheus: requests/bytes/duration/errors, `/metrics` exposition); the native
`dregg_*` node series; the full `deploy/observability/` Grafana stack (9
dashboards + Prometheus rules + node/blackbox/json/thermal exporters); and the
`ops/` admin portal (read-only aggregation of node/gateway/postgres/bot/bridge
JSON surfaces). The *infrastructure* is robust.

**The hole:** the control-plane services do not emit into it. The orchestrator's
scheduling loop, the scheduler, the provider, the durable meter, and the bridge
fulfill path are a **black box** — a lease is placed, run, metered, and settled
with ~no structured logs and no service-level metrics. An operator debugging a
lease stuck `Unplaced`/`Running`, or a rising lapse rate, has nothing to
root-cause with. (`a3b395e` added *some* control-plane tracing; the core loop is
still sparse.)

| Item | Path | Gap | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **O1** orchestrator `tick()`/`run_until_shutdown` emit nothing | `control/src/orchestrator.rs:249,296` | no per-tick watched/settled/reaped/unplaced counts; runs forever silently | M | CRITICAL | SAFE |
| **O2** scheduler `place()`/`reap()` zero tracing | `control/src/scheduler.rs` | can't distinguish provision-fail vs fulfill-fail vs timeout | M | CRITICAL | SAFE |
| **O3** provider trait + impls zero tracing | `control/src/provider.rs` | backend op success/fail rate opaque | M | HIGH | SAFE |
| **O4** lease-lapse reason not logged on transition | `control/src/orchestrator.rs:348` | `Lapsed(detail)` only in snapshot, no log | S | HIGH | SAFE |
| **O5** durable settlement/charge zero tracing | `durable/src/` | meter stalls invisible; must read pg directly | M | HIGH | SAFE |
| **O6** bridge fulfill path zero production tracing | `bridge/src/` | where work actually runs is unobserved | M | HIGH | SAFE |
| **O7** no control-plane `/metrics` (placement-latency histogram, unplaced gauge, lapse-by-reason, dispatch-attempts) | new `control/src/metrics.rs` | Grafana shows backend `up=1` but not `dispatch_latency_p99` | M | HIGH | SAFE |
| **O8** `node_api.rs` uses `eprintln!` not tracing | `control/src/node_api.rs:436,720` | unstructured | S | MED | SAFE |
| **O9** named Grafana panels still missing (turn-throughput, per-tier proof latency, end-to-end finality, per-lease settlement latency) + finality-latency has no alert | `deploy/observability/` | per MATURATION §3.3 | M | MED | SAFE |
| **O10** registered-but-0 metrics (`dregg_sandbox_denials_total`) + bridge-relayer source unwired | exec plane, `OPS_BRIDGE_URL` | per MATURATION §3.3 | S-M | MED | SAFE |

**Sequence:** O1→O2→O3→O8 first (unblocks operational debugging), then O4-O7
(metering/metrics visibility), then O9-O10 (dashboard polish).

---

## 3. DEPLOY / AUTOMATION

The manual redeploy is the single biggest ops drag (MATURATION §2 agrees).
Today: cross-build gateway/cli/ops/webauth off-box (`cargo zigbuild`), build the
node + bot natively on node-a (the node links `libdregg_lean.a` and **cannot**
be cross-compiled), ship via `docker save|gzip|scp|docker load` + rsync, then
on-box `docker compose up -d` one service at a time
(postgres→node→gateway→bot→ops). `deploy/staging/deploy.sh` covers
`build|ship|up` for the cross-buildable half; the node is a manual `build_node`
stub that just prints instructions. CI does **no** deploy, image bake, registry
push, multi-node test, or rolling-upgrade validation.

| Item | Path | Work | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **D1** Harden `deploy.sh` → `deploy-edge.sh {build,ship,up,upgrade,verify}` + post-deploy smoke (`curl /health /status`, cross-node faucet) | `deploy/staging/deploy.sh` | one command, no surprises | M | HIGH | SAFE (author/dry-run); REVIEWED-GO (live ship) |
| **D2** Image registry (GHCR), tag by git short-sha; rollback = prior tag (replaces `docker save/load`) | new CI workflow | versioned/rollback-able artifacts | M | HIGH | SAFE (author); REVIEWED-GO (push creds) |
| **D3** Postgres-service CI lane (run the 3 `#[ignore]` pg tests in a service container, not skip) | `.github/workflows/ci.yml` | closes T8 | M | HIGH | SAFE |
| **D4** Multi-node CI harness (n=2 committee, finality + verified-read against live nodes) | new CI | proves federation in CI | L | HIGH | SAFE (author/local) |
| **D5** Orchestrated rolling-upgrade encode (`UPGRADE.md` order, graceful SIGTERM, healthcheck waits, STORE-INTEGRITY grep, keep prior tag) | `deploy-edge.sh upgrade` | a human can't fumble the order | M | MED | SAFE (author); REVIEWED-GO (live) |
| **D6** clippy is **advisory-only**; the macOS CI job omits `ops`; net never test-run | `.github/workflows/ci.yml` | close the CI matrix gaps | S | MED | SAFE |

The node-image build (host-native Lean) is the long pole and not cross-buildable
— D1/D2 cover the cross-buildable half; the node image remains a
node-a/CI-Linux-builder step (REVIEWED-GO, names in MATURATION as NAMED-RUNGS
#4).

---

## 4. RELIABILITY / RECOVERY

Two real fixes landed recently and are confirmed: the SQLite `SQLITE_LOCKED`
deadlock storm (`723a20e` — on-disk WAL store per fulfill) and the settlement
double-charge race (`288ad37` — atomic check+move; the workload suite caught 218
charges where 200 were expected). Crash-resume *within a single host* is proven
(duroxide replays the on-disk SQLite history exactly-once). What remains:

| Item | Path | Risk | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **R1** **No exactly-once across node loss** — durability is host-local; a backend crash mid-workflow loses the durable store, the instance re-runs fresh on failover | `control/orchestrator` + duroxide; `docs/DBOS-DURABLE-LAYER.md` | HIGH | L | CRITICAL | DECISION (wire `duroxide-pg` / Postgres HA — architected, not wired) |
| **R2** Lease can stick in `Running` forever on a deep network hang — orchestrator has no timeout wrapper around the dispatch task (only `post_fulfill` is timed) | `control/src/orchestrator.rs:336,348` | MED | M | HIGH | SAFE |
| **R3** Orphaned work on backend-unhealthy transition — no reaper for in-flight work; the backend keeps running it while control gives up (resource leak) | `control/src/fleet.rs` + orchestrator | MED | M | HIGH | SAFE |
| **R4** Durable-store corruption is unrecoverable + undocumented (no auto-detect, no runbook for DreggNet's durable layer — runbooks cover only the federation/node layer) | `bridge` fulfill + `runbooks/DISASTER-RECOVERY.md` | MED | M (S for the runbook) | MED | SAFE |
| **R5** In-process meter counter not crash-durable (observability-only; real accounting is duroxide history) — fully resolved only when MeterTick→Payable wires the pg outbox | `durable/src/lib.rs:268-290` | LOW | M | LOW | SAFE |

R1 is the headline reliability truth and a deliberate boundary: the current
SQLite/host-local model is right for the single-backend node-a staging
deployment, **insufficient for a redundant production fleet**. It is a design
decision (cost + topology), not an overnight fix — surface it to ember.

---

## 5. PERFORMANCE

**Good news:** all 8 service-layer benches **exist and are real** (not stubs) —
hand-rolled (`harness = false`, no criterion), offline, each independently
runnable. They measure the right things and even instrument the named contention
points (the `webapp` `Mutex<Meter>`, the `scheduler` `workloads` `HashMap`
lock). **The catch:** the bench `.rs` files are **untracked** (uncommitted) and
wired into neither `make` nor CI — so they capture no baseline and ratchet
nothing.

| Item | Path | Work | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **P1** Commit the benches + add a `make bench` + a CI bench step (or nightly) + a `docs/PERF.md` with p50/p99 SLO baselines (referenced by `durable_bench.rs:15` but **missing**) | `*/benches/*.rs`, `Makefile`, `.github/workflows/ci.yml`, new `docs/PERF.md` | establish + ratchet a baseline | S | HIGH | SAFE |
| **P2** Profile the two known lock-contention hot paths once a baseline exists: `Mutex<Meter>` per `serve()` and the scheduler `workloads` `HashMap` lock | `webapp/src/router.rs:159`, `control/src/scheduler.rs:106` | confirm before optimizing (don't pre-optimize) | M | MED | SAFE |
| **P3** Add the two missing micro-benches: storage `Account::charge` concurrent throughput + receipt-chain (blake3+ed25519) throughput | new `storage/benches/`, `receipt/benches/` | close measured-path gaps | M | MED | SAFE |
| **P4** Measure the gated paths (Postgres durable, verified on-chain read) once their lanes exist | rides D3 / live node | unknown today | M | MED | SAFE / REVIEWED-GO (live node) |
| **P5** Evaluate `lto = "off"` → `"thin"` (release profile explicitly disables LTO) — measure runtime gain vs build cost + binary size | `Cargo.toml:114` | possible cross-crate win | S | LOW | SAFE |
| **P6** Gateway is thread-per-connection, 1024-conn Semaphore, hand-rolled HTTP parse over untrusted input — characterize the saturation ceiling + fuzz the parser | `gateway/src/main.rs:237-250,710+` | unknown ceiling + attack surface | M | MED | SAFE |

Optimization waits on measurement — P1 unblocks everything else here.

---

## 6. DEPENDENCIES / CROSS-BUILD

The service layer's dep hygiene is solid (1,031 crates in lock, no problematic
duplicates, no unmaintained/suspicious crates). The net/ Elide stack carries the
liabilities.

| Item | Path | Issue | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **C1** **Branch-floated forks** — rustls (`elide/zero-copy-plaintext`), ntex×16 (`elide/scatter-gather-write`), hickory×2 (`compio`) are **branch-pinned, not rev-pinned**; `cargo update`/a lockless CI build silently floats them to branch tips | `Cargo.toml:140-161` | reproducibility hazard (committed lock pins *today* only) | S | HIGH | SAFE |
| **C2** **net/ stack is end-of-life upstream** (`origin/main` deleted httpe/tailscale/wireguard/iocoreo/pki) — DreggNet is now its de-facto home; bundle is 6 commits behind `main-catastrophe` but carries 4 commits upstream lacks (a reviewed three-way merge, not a copy; preserve the 2 local `build.rs` mods) | `net/*`, `docs/NET-CRATES-STALENESS.md` | maintenance debt | L | MED | REVIEWED-GO |
| **C3** Cherry-pick the aarch64 **seccomp fix** (`6f3182589`) + **prebugger-disable-in-release** (`68ac98825`) — security/correctness, urgent if any arm64 or public deploy | `net/{nodeapi,sys,httpe,pki,base}` | hardening | S | MED | SAFE |
| **C4** Remove 3 unused `[patch]` entries (compio-signal/tls/ws — `cargo tree` warns "not used") | `Cargo.toml:173-175` | cosmetic noise | S | LOW | SAFE |
| **C5** Document the nightly (`nightly-2026-03-24`) + edition-2024 debt — required by net/ `#![feature(linkage)]` + `cfg_sanitize`; not droppable without re-architecting the net symbol-visibility model | `rust-toolchain.toml`, `ARCHITECTURE.md` | visibility | S | LOW | SAFE |

**Cross-build:** the gateway/net stack is Linux-only by design (epoll/io_uring +
`SOCK_NONBLOCK`/`SOCK_CLOEXEC` used unconditionally in
`net/nodeapi/src/http.rs:1107`). Cross-build from macOS via `cargo zigbuild`
(`Makefile:71`, glibc-2.31 floor) is reliable and documented — **not a bug**.
(Note: an earlier "multiple-workspace-roots" symptom is **resolved** —
`sandstorm-bridge` is now a proper member, `cargo metadata` resolves clean.)

---

## 7. DOCS COMPLETENESS

Docs are unusually thorough (44 in `docs/`, 18 runbooks, a full MATURATION
plan + 3 under-wired catalogs + 2 red-team passes + a stand-ins census). The
gaps are accuracy/drift, not absence:

| Item | Path | Issue | Effort | Value | Autonomy |
|---|---|---|---|---|---|
| **DOC1** `docs/PERF.md` referenced (`durable_bench.rs:15`) but **does not exist** | — | dangling ref + missing SLO baselines | S | MED | SAFE (rides P1) |
| **DOC2** Caddy basic-auth drift — `runbooks/DEPLOY.md` notes `USING-STAGING.md` still lists two per-user accounts but the live Caddyfile carries a single `operator` account | `deploy/staging/USING-STAGING.md` vs `Caddyfile` | reconcile to source-of-truth | S | LOW | SAFE |
| **DOC3** Runbooks cover the federation/node layer but **not** DreggNet's durable-store-loss / orphaned-workflow / stuck-state recovery | `runbooks/DISASTER-RECOVERY.md`, `INCIDENT-RESPONSE.md` | rides R2-R4 | S | MED | SAFE |
| **DOC4** `docs/TESTING.md` implies net is "tested on Linux" — clarify CI only *builds* it | `docs/TESTING.md` | rides T5 | S | LOW | SAFE |

---

## 8. Through-line

The criticals are closed and two real concurrency/durability bugs were just
fixed; the residue is **maturity plumbing, not research**. The measurement and
observability *substrate* is built but unwired — committing the benches (P1) and
making the control plane emit logs + metrics (O1-O7) is the highest-leverage,
lowest-risk work and is what makes DreggNet *operable*. The reproducibility
hazard (C1) is a 30-minute SAFE fix. The node-agent test gap (T1) and the
workload-suite calibration (§1.2) close the two scariest blind spots. The
deploy automation (D1-D3) retires the #1 ops drag and is SAFE to author. The one
item that is genuinely a **decision, not a task** is R1 — durability is
host-local, so there is no exactly-once across node loss; the cure
(`duroxide-pg` / Postgres HA) is architected, costed, and ember's call. Nothing
here crosses into the VK/substrate epoch (the parallel swarm's lane).
