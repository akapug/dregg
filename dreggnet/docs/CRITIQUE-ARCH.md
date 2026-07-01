# Architecture & code-quality critique — the seams the other two reviews didn't grade

*A read-only, adversarial architecture/quality review of `~/dev/DreggNet` at HEAD
(branch `dev`, 2026-06-30). Scope: the orchestration/hosting/economy product crates.
`circuit/` and `metatheory/` are out of scope (the parallel swarm; read-only).*

This review is deliberately **complementary** to the two existing critiques and does
not restate them:

- `docs/ARCHITECTURE-CRITIQUE.md` grades the **thesis drift** (receipts-as-logs,
  per-op settlement cadence, bridge over-relay, the missing offchain merge runtime).
- `docs/RED-TEAM-FINDINGS-2.md` grades **security** of the grown featureset (mostly
  ✅ fixed).

What follows is the third axis: **structural debt, duplication, coupling, fragile
seams, and code-quality consistency** — the things that bite at scale or confuse a
new contributor, regardless of whether the thesis or the security posture is right.
Honest both ways: §9 credits what is genuinely solid.

Severity legend: **S1** = fix first (systemic / load-bearing-and-thin /
supply-chain). **S2–S4** = real structural debt. **S5–S7** = consistency / clarity.
**S8** = minor / debris.

---

## S1 — The vendored Elide `net/` stack is an abandoned, proprietary, single-maintainer dependency the entire public surface rests on

**Evidence:** root `Cargo.toml:13–35` makes 18 `net/*` crates workspace members
(~397K LOC — `find net -name '*.rs' | wc -l`), bundled byte-for-byte from the Elide
`dhttp` tree. `docs/NET-CRATES-STALENESS.md` is candid about the situation, and it is
severe:

- **The stack is end-of-life upstream.** `origin/main` (`a38e9e0d0`, 2026-04-22) has
  **deleted** httpe, tailscale, wireguard, iocoreo, pki, foreign-gai, jvm-stubs
  (NET-CRATES-STALENESS §TL;DR, §1). "There is no future upstream for the HTTP engine
  — DreggNet is now its de-facto home." A product's entire public HTTP surface now
  rests on ~400K LOC of code that has no maintainer but ember.
- **It once forced the whole product proprietary (now resolved).** The `net/*` sources carry the Elide
  proprietary header and are **not relicensable** (NET-CRATES-STALENESS §5,
  `ARCHITECTURE.md:99–102`) — which is why DreggNet could not be open-sourced until the
  Elide net stack was ejected (now done, `ELIDE-NET-EJECTION.md`; DreggNet is AGPL-3.0).
  The HTTP engine choice used to dictate the license of the entire product.
- **It pins the whole repo to one old nightly.** `rust-toolchain.toml` pins
  `nightly-2026-03-24` solely because the net crates use `cfg_sanitize`/`linkage`.
  Every other crate in the workspace inherits that pin.
- **It is Linux-only.** `ARCHITECTURE.md:54–67`: `net/nodeapi`/`net/transport` use
  Linux-only socket primitives; the stack does not compile on the macOS dev host.
  This is *why* sibling services (ops, webauth) were written as "pure-std HTTP" to
  dodge httpe (root `Cargo.toml:61–64`) — see S6.
- **Supply-chain reproducibility hazard, unaddressed.** The `[patch.crates-io]` set
  (root `Cargo.toml:122–175`) branch-pins (not rev-pins) `rustls`, **16** `ntex`
  crates, and `hickory` (NET-CRATES-STALENESS §3). The committed `Cargo.lock` makes
  *today* reproducible, but a `cargo update` silently floats the engine to a branch
  tip. The doc calls rev-pinning "the highest-leverage supply-chain fix" — it is not
  done.
- **Already behind on security fixes.** The bundle is 6 commits behind the last whole
  upstream snapshot, missing a **seccomp aarch64 syscall-guard fix** and a
  **prebugger-disable** hardening commit (NET-CRATES-STALENESS §2) — both relevant to
  a crate that serves untrusted hosting on arm64.

**Why this is S1:** it is the single largest liability in the repo and it is
load-bearing for the gateway. It also has the cheapest highest-leverage fix.

**Fix direction (in order):**
1. **Rev-pin the forks to the lock SHAs now** (NET-CRATES-STALENESS §3 lists them).
   One `Cargo.toml` edit, eliminates the float hazard. Do this independent of
   everything else.
2. **Decide explicitly whether `httpe` is load-bearing.** ops/webauth already serve
   real traffic on pure-std HTTP. If the gateway's needs (HTTP/2, TLS, proxying) truly
   require httpe, fine — but shrink the vendored surface to *what is actually linked*
   (much of the 18-crate closure — jvm-stubs, jni, the JVM-binding patches — is inert
   for a serving stack). Drop the inert crates from `members`.
3. **Treat `net/` as a frozen internal fork**, not a tracked upstream: a small,
   reviewed local-patch set (the 2 `build.rs` mods + the seccomp/prebugger
   cherry-picks) on a recorded base SHA, documented as "maintained here forever."

---

## S2 — Two parallel control loops over two infra abstractions; no single canonical path

The control plane has **two independent engines** that both do
refuse-unfunded → acquire-machine → dispatch → meter → reap, over **different**
abstractions and **different** lifecycle state machines:

| | `Scheduler` (`control/src/scheduler.rs`) | `Orchestrator` (`control/src/orchestrator.rs`) |
|---|---|---|
| infra abstraction | `VmProvider` + `Machine` (`provider.rs`) | `BackendRegistry` + `Backend` (`fleet.rs`) + `Mesh` |
| concrete backends | `LocalProvider`, `Ec2Provider` | mesh-dispatched persvati agents |
| lifecycle enum | `WorkloadState` (`scheduler.rs:49`) | `OrchestratedWorkload` (`orchestrator.rs`) |
| dispatch | `VmProvider::run_lease` | `dispatch_lease_over_mesh` |
| entry | `Scheduler::place` | `Orchestrator::tick` / `run_until_shutdown` |

Both refuse unfunded leases up front, both meter per period, both settle via the
`Settlement` trait, both reap on lapse. The doc-comments each claim to be *the* loop
("the loop that makes DreggNet an actual cloud" — `orchestrator.rs:1–24`; "places a
funded lease … tracks the lifecycle" — `scheduler.rs:1–17`). A new contributor cannot
tell which is canonical or when to use which.

Compounding it: **four distinct "a thing the control plane runs work on" types** —
`provider::Machine` (`provider.rs:108`), `fleet::Backend` (`fleet.rs:45`),
`mesh::MeshNode` (`mesh.rs:147`), and `server::ServerRecord` (`server.rs:118`, the
persistent-server fleet) — plus `ServerFleet` as a *fifth* lifecycle manager. Each
carries its own id type, status enum, and registry.

**Fix direction:** designate the `Orchestrator` as the one control loop (it is the
"real daemon"); express the `VmProvider` (`Local`/`Ec2`) as one `Backend` kind behind
the `BackendRegistry`, so EC2 scale-out and mesh dispatch share one fleet view and one
`WorkloadState`. Fold `ServerFleet`'s persistent-server lifecycle into the same state
machine (a persistent server is a workload whose lease never completes). Collapse
`Machine`/`Backend`/`MeshNode` to one node type with optional fields.

---

## S3 — The "ONE receipt" crate is ~40% adopted and its verifier has no production consumer

The `receipt` crate (commit `f249fc7`) is exactly the ARCHITECTURE-CRITIQUE §5.1
recommendation made real — a length-prefixed, domain-separated, prev-hash-chained,
ed25519-signed `ReceiptBody`/`ReceiptAttestation`/`ReceiptChain` (`receipt/src/lib.rs`).
The *design* is right (see §9). But the rollout is half-finished, which creates an
**N+1 problem** rather than closing N:

- **Only webapp + storage consume it** (`grep dreggnet-receipt */Cargo.toml`). Still
  bespoke and *not* on the contract: `HostingReceipt` (`control/src/hosting_meter.rs:186`),
  `DeployReceipt` (`dregg-deploy/src/workflow.rs:115`), `BindReceipt`
  (`dregg-domains/src/lib.rs:243`), `SettleReceipt` (`durable/src/settle.rs:105`). So
  there are now the old ad-hoc receipts *plus* a new canonical one — more notions, not
  fewer, until adoption finishes.
- **`verify_chain` is consumed only in tests.** Every non-test reference is the
  *producer* side (`SiteRegistry`/`BucketRegistry` seal on publish/put —
  `webapp/src/hosting.rs:619`, `storage/src/registry.rs:138/197/288`). The only callers
  of `verify_chain` are unit tests (`webapp/src/hosting.rs:934/943`). The crate's whole
  promise — "re-witnessable by a non-witness" (`receipt/src/lib.rs:50–51`) — has **no
  live verifier**: nothing in the CLI, gateway, or a client path verifies a deploy or
  publish without trusting the host. A signed receipt nobody verifies is ceremony.

**Fix direction:** (a) finish adoption — make `HostingReceipt`/`DeployReceipt`/
`BindReceipt` typed *views* over a sealed `ReceiptBody` (the crate's own §1 model), and
either lift `SettleReceipt` onto it or document why settlement keeps its own; (b) ship
**one** real verifier consumer (a `dregg receipt verify <chain>` CLI, or the gateway
exposing the chain so a client checks a publish) — without it the crate doesn't pay for
itself.

---

## S4 — Metering is re-implemented 5–6 times; only the settlement *sink* is abstracted

The `Settlement` trait (`durable/src/settle.rs:179`) cleanly abstracts *where value
lands*. But the *meter* — period cursor, per-period charge, dedup, lapse — is
hand-rolled per surface, each re-deriving the same exactly-once logic:

- `GpuMeter` (`exec/src/lib.rs:1272`) — compute-fraction ticks against a budget.
- durable `MeterCharge`/`MeterRow` + `meter_units` (`durable/src/lib.rs:142/287/343`).
- `HostingMeter` with `meter_publish`/`meter_uptime`/`meter_cert`/`meter_build`/
  `tick_bandwidth`/`tick_all_bandwidth` (`control/src/hosting_meter.rs:384–551`).
- `ServerFleet::meter_period`/`tick_uptime` (`control/src/server.rs:880/950`).
- webapp `Meter` + `BandwidthMeter` (`webapp/src/router.rs:173`, `webapp/src/hosting.rs:364`).

This is not benign duplication: **the exactly-once / lapse logic is exactly where the
red-team bugs lived** (HB-4 reset-cursor free-replay, SRV-2 abort-on-error,
SRV-3 tick-not-wallclock). Each was fixed *in its own copy*; the next meter surface
will re-introduce the same class. The `(lease, period)` idempotency key, the
write-ahead-then-charge order, and the "fail before commit" rule are re-stated in prose
in 5 modules instead of enforced by one type.

**Fix direction:** a `Meter` trait paralleling `Settlement` — a durable period cursor +
`charge(resource, period) -> Outcome{Charged|Replayed|Lapsed}` with the wall-clock and
fail-before-commit discipline implemented once. Each surface supplies only its pricing
(`HostingPricing` is already the right shape). This is where the meter-layer bugs stop
recurring.

---

## S5 — The data plane is non-durable in-memory state while the settlement plane is durable

A systematic durability asymmetry: the things being *billed for* are the least durable
layer, while the *billing* is fsync-hardened.

- **In-memory `Mutex<…>` (lost on restart), yet authoritative:** published sites
  (`webapp/src/hosting.rs:527` `SiteRegistry.sites`), the bandwidth meter
  (`hosting.rs:366`), domain bindings (`dregg-domains/src/lib.rs:389`), storage buckets
  (`storage/src/registry.rs:42`), the hosting roll-up cursors
  (`control/src/hosting_meter.rs:230/232` `accounts` + `bw_periods`).
- **Durable:** the persistent-server store (`control/src/server.rs`), the settlement
  dedup (`control/src/settle_ledger.rs`), the durable workflow + pg outbox
  (`durable/src/`).

So a control-plane restart **loses every published site, every domain binding, and
every bucket**, while the settlement ledger that charges for them survives. RED-TEAM
HB-4 caught the narrow billing consequence (cursor reset → free replay); the broader
architectural point is the inversion itself. The STAND-INS census frames these maps as
"in-process stand-ins for `Effect::Write`-to-node" (#4/#5) — true, but until that flip
lands, the product's user-facing state has *no* durability story, not even local.

**Fix direction:** the data plane needs a durable store now (even a local append-only
one, as `server.rs`/`settle_ledger.rs` already demonstrate the pattern), not only after
the node-write flip. At minimum, make the durability boundary explicit and symmetric:
don't ship exactly-once billing for state that evaporates on restart.

---

## S6 — Three hand-rolled HTTP request/response models atop the heavy httpe, plus a bespoke node client

Because httpe is heavy and Linux-only (S1), the product grew **multiple** HTTP layers:

- `gateway/src/http.rs` (474 lines) + `gateway/src/webresp.rs` (106) — the httpe-side
  model.
- `webapp/src/http.rs` (221) — its **own** `WebRequest`/`WebResponse`
  (`webapp/src/http.rs:63/98`), used by the std-socket `dreggnet-serve`/`dreggnet-host`
  binaries.
- ops, webauth, `control/src/node_api.rs`, `gateway/src/status.rs` each hand-parse HTTP
  off a raw `std::net::TcpListener` (ARCHITECTURE.md/root Cargo.toml even advertise ops
  + webauth as "pure-std HTTP … cross-builds trivially" — i.e. deliberately bypassing
  the gateway's own HTTP layer).
- the node JSON-RPC **client** in `control/src/node_api.rs` is hand-rolled too — no
  `reqwest` anywhere in the product except `ops/src/client.rs`.

So "how do I serve/parse HTTP here?" has three answers and "how do I call the dregg
node?" is bespoke. That httpe cannot be reused by the sibling services is the
abstraction leak: the heavy choice didn't actually become the shared one. Hand-rolled
HTTP parsing is also a recurring bug/security surface (the red-team's 404-reflection
and continue-on-error fixes were in these paths).

**Fix direction:** extract one tiny `http-types`-style crate (`WebRequest`/
`WebResponse` + a minimal std server loop) that gateway, webapp, ops, and webauth all
share; keep httpe strictly as the *transport* under the gateway, not as a type source.
One node-client type (over `reqwest`, which is already a workspace dep) for node_api +
ops.

---

## S7 — Error handling is inconsistent across the workspace

24 hand-rolled `pub enum …Error` definitions with **29 manual `Display` impls**, and
only **one** crate (webauth) uses `thiserror` — despite `thiserror = "2"` being in
`[workspace.dependencies]`. Meanwhile exec/durable/ops/dregg-deploy mix `anyhow` and
`Result<_, String>` *with* the typed enums (the error census: exec 5 String sites + 1
anyhow file, durable 8 + 3, ops 9 String sites, dregg-deploy 8 + 5).

Two distinct problems:
1. **Boilerplate + drift:** 29 hand-written `Display` impls that `#[derive(Error)]`
   would generate, with no `#[from]`/`source()` wiring (so error chains are flattened).
2. **Stringly-typed cross-crate seams (abstraction leak):** the inter-crate error
   variants collapse a structured cause to a string — `SettleError::Backend(String)`
   (`durable/src/settle.rs:141`), `ProviderError::Aws(String)`/`Bridge(String)`
   (`control/src/provider.rs:131/134`), `BridgeError`, `NodeApiError`. A caller cannot
   match on *why* the node refused; it can only re-print prose.

**Fix direction:** adopt `thiserror` uniformly for library crates (delete the 29
`Display` impls); reserve `anyhow` for binaries/tests; replace the `…(String)`
cross-crate variants with `#[from]` typed sources so error chains survive the crate
boundary. Pure mechanical cleanup, large clarity payoff.

---

## S7b — Runtime/backend choices hidden behind cargo features (against the house rule)

The codebase has a stated rule — *no reflexive cargo features*: don't feature-gate
runtime choices or load-bearing backends; use a trait + runtime select. One feature
still violates it, one now obeys it (was a violation, now resolved), and one is the
legitimate exception:

- **Compute engine — RESOLVED.** The old critique here was that `exec`'s execution
  engine was a default-on feature over an external submodule. That is gone: compute is
  now **owned and in-crate** (`exec/Cargo.toml`, `default = []`). The `Sandboxed` tier
  runs on the owned pure-Rust `wasmi` interpreter (a normal crates.io dep, zero
  `unsafe`), and which engine serves a workload is chosen at **runtime** by the lease's
  `CapTier`. Every stronger tier (JIT/`Caged`/`MicroVm`/GPU/native/python/node) is an
  honest fail-closed seam (`ExecError::TierNotServed` / `NotWired`) — not a feature
  toggle and never a silent downgrade. This is exactly the runtime-select shape the
  rule asks for.
- **`pg` (vs default `sqlite`) gates the durable backend** — `durable/Cargo.toml:42–51`.
  A silent SQLite↔Postgres swap behind a feature, with the pg test `#[ignore]`d +
  `DATABASE_URL`-gated. Backend selection belongs at runtime (config), not in the
  feature set. This one remains to fix.
- **Contrast — `dregg-verify` is correct.** `bridge/Cargo.toml:30/71` keeps it
  off-by-default purely as an **AGPL link-isolation** boundary (the one legitimate use
  of a feature here), with explicit FLIP-ON docs. Keep this; fix `pg`.

The old **fragile submodule seam** is likewise gone: there is no compute submodule and
no external compute dependency, so no `[patch.crates-io]` path-dep into an untracked
external HEAD can vanish under the durable build path.

**Fix direction:** make durable's store **runtime-selected** (a provider trait + a
config enum, as `VmProvider`/`Settlement` already do elsewhere); reserve features for
true link-isolation (`dregg-verify`). The exec-engine half of this is already done
(owned, in-crate, runtime-selected by tier).

## S8 — Smaller debt: god-crate, stale lock debris, deep re-export coupling, sibling-path drift

- **`control` is a 9K-LOC god-crate** (14 modules — provider, scheduler, orchestrator,
  fleet, mesh, node_api, hosting_meter, server, settle_ledger, config, ec2, local). It
  fuses provisioning, networking (mesh/WireGuard), HTTP (node_api), billing
  (hosting_meter), and lifecycle in one crate. `server.rs` alone is 1536 lines.
  Splitting along the S2 unification (one fleet/lifecycle crate, one mesh crate, one
  billing crate) would localize change.
- **`sandstorm-bridge` carries a stale own `Cargo.lock`** even though it was "promoted
  from a detached prototype to a wired workspace member" (root `Cargo.toml:88–89`). A
  workspace member uses the root lock; the leftover `sandstorm-bridge/Cargo.lock` is
  dead debris that will confuse (and can silently diverge if anyone builds it
  standalone). Delete it. (By contrast `demo/stripe-receiver/Cargo.lock` is a
  *deliberate* standalone — correctly out of the workspace so it never links dregg —
  that one is sound.)
- **Deep re-export coupling:** `gateway` depends on bridge+control+webapp+webauth;
  `control` re-exports the entire `dreggnet_bridge`/`dreggnet_durable`/`dreggnet_exec`
  vocabulary (`control/src/lib.rs:104–110`); `cli` path-deps six crates. The dependency
  fan-out is a straight tower (no cycles — good), but the blanket re-exports mean a
  change to a leaf type ripples to the public API of every crate above it.
- **`demo/stripe-receiver` path-deps the breadstuffs sibling** (`../../../breadstuffs/bridge`,
  `demo/stripe-receiver/Cargo.toml:45`). Its standalone-workspace isolation is sound
  (it keeps AGPL dregg out of the DreggNet default dependency graph — a deliberate boundary), but the
  raw sibling path means a breadstuffs update silently pulls untested dregg internals
  into the demo, and the AGPL-compliance story rides on a local checkout. Pin it (git
  rev) rather than a floating sibling path.
- **Zero `TODO`/`FIXME` markers in the code** — debt lives entirely in `docs/*.md`.
  This is admirable discipline for outward cleanliness, but it means a contributor
  reading the *code* cannot see the seams; the stand-ins/under-wired catalogs are the
  only map, and they drift from HEAD (several already carry "verify against HEAD"
  caveats). Consider lightweight in-code `// STAND-IN:` markers at the actual fake
  sites, linking the census row.

---

## 9 — What is genuinely solid (a real critic credits the wins)

- **Durable exactly-once settlement is correct and well-reasoned.**
  `control/src/settle_ledger.rs` is the high-water mark of the product layer:
  write-ahead reservation → fsync → submit, with the **safe direction deliberate**
  (a crash between reserve and commit is treated as already-settled — under-charge,
  never double-charge — `settle_ledger.rs:26–33`). Backed by the pg outbox's
  `(lease,period)` unique constraint and the in-process dedup. The property is stated,
  justified, and tested. This is the part to build *more* like.
- **The `Settlement` trait is a clean, honest sink seam** (`durable/src/settle.rs:179`):
  conserving (Σδ=0), exactly-once on `(lease,period)`, with a **fail-closed
  `funded_balance` default of `0`** (`settle.rs:195`) so a backend that can't read a
  balance authorizes no up-front-charged work. Backend-swappable in-process ↔ node
  without touching the orchestrator. Exactly the right shape (S4 asks for its twin on
  the meter side).
- **The host-API spine is sound** (RED-TEAM Surface 4 HOLDS): per-broker isolation,
  cap-gate before any commit, charge-before-effect under one lock, no zero-cost path,
  host-built receipt chain the guest can't forge. The trait seams generally
  (`VmProvider`, `Mesh`, `LeaseSource`, `DnsResolver`, `AwsCli`) are clean abstraction
  points — the duplication in S2/S6 is *around* good seams, not for lack of them.
- **The `receipt` crate's design is the right primitive** — length-prefixed,
  domain-separated `BodyHasher` (`receipt/src/lib.rs:97–119`), prev-hash + ed25519
  attestation, the "typed view over a turn receipt" model. It only needs the S3 finish
  (full adoption + a live verifier).
- **Honest labeling is a genuine asset.** The stand-ins / under-wired-features /
  under-wired-circuit / under-wired-parity catalogs distinguish *deliberate sound
  boundaries* (license isolation, dev defaults, trait test-instances) from *debt* with
  file:line precision, and name every fake's real impl and effort. Most codebases this
  size hide their seams; this one maps them.

---

## Appendix · ranked one-liner scorecard

| # | Weakness | Severity | First move |
|---|---|---|---|
| S1 | EOL proprietary Linux-only `net/` stack (~397K LOC) under the whole gateway | **S1** | rev-pin forks; drop inert crates; freeze as internal fork |
| S2 | Two control loops (Scheduler vs Orchestrator) + 4–5 node abstractions | **S2** | Orchestrator canonical; VmProvider → a Backend kind |
| S3 | `receipt` crate ~40% adopted; `verify_chain` test-only (no live verifier) | **S3** | finish views; ship one real verifier |
| S4 | Metering re-implemented 5–6× (where the meter bugs live) | **S4** | a `Meter` trait, twin of `Settlement` |
| S5 | Data plane in-memory (sites/domains/buckets) vs durable settlement | **S5** | durable data-plane store before exactly-once billing |
| S6 | 3 hand-rolled HTTP models atop httpe + bespoke node client | **S6** | one shared `http-types` + one node client |
| S7 | 24 hand-rolled error enums, 1 thiserror; stringly cross-crate seams | **S7** | thiserror everywhere; `#[from]` typed sources |
| S7b | `pg` feature gates the durable backend choice (compute-engine + submodule halves now RESOLVED — owned/in-crate) | **S7** | runtime-select durable store via trait |
| S8 | 9K control god-crate; stale sandstorm lock; blanket re-exports; sibling-path drift | **S8** | split control; delete dead lock; pin sibling |
| ✓ | durable exactly-once · Settlement seam · host-API spine · receipt design · honest catalogs | **solid** | build more like settle_ledger.rs |
