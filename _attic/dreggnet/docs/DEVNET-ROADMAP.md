# DEVNET-ROADMAP — the one prioritized roadmap

*Synthesis of five scout reports (2026-06-30) into one durable, ranked plan.
Sources: `docs/VISION.md` (the Verifiable Agent Cloud frontier + 3 bold bets),
`docs/DEVWORK-PRODUCT.md` (product top-10), `docs/DEVWORK-INFRA.md` (infra/ops
top-10 + R1 the durability decision), `docs/CRITIQUE-ARCH.md` (S1–S8 structural
debt), `docs/CRITIQUE-PRODUCT.md` (the stranger-usability frictions). Out of
scope by design: `circuit/`, `metatheory/`, the VK/substrate epoch (a parallel
swarm owns them). Read this for the SHAPE and the order; verify any file:line
against HEAD before relying on it — the scouts already did, this ranks them.*

**The thesis this roadmap serves** (from VISION): *the unit of compute, the unit
of account, and the unit of authority are the same verified object — a cell.* The
reachable epic is the **Verifiable Agent Cloud, end-to-end on the devnet path**:
hand an agent a budget and a cap, it runs / serves / transacts / delegates in the
cloud, and hands back a receipt chain a light client re-verifies. Every cluster
below is grouped by what it does for that epic.

**Effort:** S = <1 day · M = 1–5 days · L = 1–2 weeks.
**Disposition:** **safe-autonomous** (green-gated, reversible, no live/money/
hardware/AGPL touch — build now) · **reviewed-go** (live edge / real money /
hardware / registry-creds / AGPL flip — code it, gate the ship) ·
**NEEDS-EMBER-DECISION** (an irreversible topology/architecture call precedes the
code — framed short below).

---

## 1. The convergences — where 2+ scouts independently agree (highest-leverage signal)

Ranked by leverage (how many downstream items each unblocks × tractability).
Independent agreement across lenses is the strongest prioritization signal we
have; these are the spine of the do-next list.

### C1 — Rev-pin the Elide forks (the 30-minute supply-chain fix) · **3 scouts**
ARCH **S1** (the EOL Linux-only `net/` stack is the repo's largest liability and
has the *cheapest highest-leverage fix*) + INFRA **#2 / C1** (reproducibility
hazard) — and it underlies VISION's "serving spine." **Verified at HEAD:**
`Cargo.toml` rev-pins `compio`/`jni`/`ark`, but `rustls`, **16× `ntex`**, and
`hickory` are **branch-pinned** (`branch = "…"`) — a `cargo update` or lockless CI
build silently floats the gateway's whole transport to a branch tip. One
`Cargo.toml` edit pins them to the lock SHAs. **Effort S · safe-autonomous.** (The
*bigger* net/ question — freeze-as-fork vs decouple httpe — is D2 below, a
decision.)

### C2 — The observability/measurement substrate is built but unwired · **2 scouts, many items**
INFRA **#1/#4/#5/#6 + O1–O10 + P1** (benches uncommitted, control plane
metrics-blind and log-silent, the workload-sim suite never runs) + DEVWORK-PRODUCT
cross-cutting (per-resource metrics; no per-route/per-site labels). **Verified:**
`durable/`, `exec/`, `webapp/` benches are **untracked**; no `trait Meter`, no
control-plane `/metrics`. This is plumbing, not research, and it is what turns "it
runs" into "we can operate it." The orchestrator is where the logging lands (ties
to S2). **Effort S–M each · safe-autonomous.**

### C3 — Finish the receipt crate + ship ONE live verifier · **3 scouts**
ARCH **S3** (the `receipt` crate is ~40% adopted; `verify_chain` has **no
production caller**) + INFRA **T2** (receipt: 0 integration tests) + CRITIQUE-PRODUCT
("the most compelling property is invisible at the surface a developer touches
first" — `deploy` produces a real verify manifest but never tells the user it
exists). **Verified:** `verify_chain` is referenced only by producers
(webapp/storage/domains seal on publish) + unit tests. This *is* VISION superpower
#1 ("you verify the operated result"). A signed receipt nobody verifies is
ceremony. **Effort M · safe-autonomous.**

### C4 — Make the data plane durable · **3 scouts + a decision tail**
ARCH **S5** (in-memory `Mutex<…>` sites/domains/buckets are authoritative yet lost
on restart, while the *billing* is fsync-hardened — the durability inversion) +
INFRA **R1** (no exactly-once across node loss; durability is host-local) +
DEVWORK-PRODUCT (the daemon loses workload tracking on restart; SQLite→Postgres
rung). **Two layers, two dispositions:** (a) a *local* durable data-plane store —
the `server.rs`/`settle_ledger.rs` append-only pattern already in tree — is
**safe-autonomous**; (b) *cross-node* HA (duroxide-pg / Postgres HA) is **R1, an
ember decision** (cost + topology). Do (a) now; surface (b).

### C5 — Unify metering on the replenishing-budget cell (the `Meter` trait) · **3 scouts + the in-flight lane**
ARCH **S4** (metering is hand-rolled 5–6× — `GpuMeter`, durable `MeterCharge`,
`HostingMeter`, `ServerFleet::meter_period`, webapp `Meter` — *exactly where the
red-team meter bugs lived*; only the settlement *sink* is abstracted) + VISION
reachable-epic #2 (the replenishing budget as the meter, a near-pure reuse with a
copyable Lean rung) + `docs/REPLENISHING-BUDGET.md` (the budget primitive **is**
the `Meter` trait — widen `allowance.rs`'s refill model + put three control-plane
uses on it) + DEVWORK-PRODUCT (durable `MeterTick`→`Payable`, the named single
seam). **Verified:** no `trait Meter` exists yet — greenfield, but with a clean
template (`Settlement`) and a copyable Lean skeleton. The `Meter` trait is the
twin of `Settlement` and stops the recurring meter-bug class. **Effort M ·
safe-autonomous** (the trait) / reviewed-go (the on-chain `Payable` tail).

> **LANDED (2026-06-30, green):** the keystone + the most-duplicated decision migrated.
> - **The replenishing-budget cell** — `exec/src/budget.rs`: `ReplenishingBudget`
>   `(budget, period, refill_amount, refill_max, start)` + cursors `(consumed,
>   refilled, last_block, queue)`, ONE `check_draw` core (non-vacuity by
>   construction). Teeth proven: over-draw, backdated-draw (monotone `last_block`),
>   early-refill-inexpressible (the refill block is *derived* `at_block + period`),
>   forged-down-counter-contradicts-the-monotones, lazy `mature` (stalled-then-resumed
>   bills identically), draws commute at one block, `refill_max` coalescing leaks no
>   headroom, `attenuate` narrows only. Std-only (no crypto dep).
> - **The `Meter` trait** (`exec/src/meter.rs`) — the twin of `Settlement`:
>   `draw(key, units, at_block)` fail-closed over matured headroom (the in-band 402),
>   exactly-once per `(subject, period)`, `attenuate_child`. `ReplenishingMeter` is
>   the backing. Proven: exactly-once, in-band over-budget, replenishment at the
>   derived block, the settlement-contention child split (Use B), and the
>   **agent-budget-bounding (VAC)** — an agent's invoke budget IS a replenishing-budget
>   cell, a runaway is rate-bounded + attenuates to a sub-agent.
> - **Migrated onto the one verified core** (`budget::lease_budget_admits`, the
>   lease-budget ceiling decision that was hand-rolled `period * per_period_units >
>   budget`): `control/src/server.rs` (bring-up SRV-4 pre-pay + `meter_period` lapse,
>   both sites) and the `durable` `WorkloadRun` orchestration step gate (replay-safe).
>   All existing tests + red-team refusals preserved (exec 60, control 78, durable +
>   integration, webapp 40 — green; SRV-1 quota / SRV-4 pre-pay / HB-1 / the host-API
>   sign-cast untouched).
> - **Named seams (next rung):** (1) the `webapp::BandwidthMeter` *byte* budget +
>   `control::HostingMeter` bandwidth roll-up want the cell's lazy-refill
>   generalization but have a genuine impedance mismatch (infallible `record` +
>   `Option`/uncapped); migrate by sourcing the owner's bandwidth coverage from a
>   replenishing-budget cell (a control-plane change, the doc's "incremental, behind
>   the seams"). (2) the `exec::host_api` concurrent CAS call-meter + `u64::MAX`
>   uncapped value-budget — adopt the cell under the broker's existing lock. (3) **The
>   Lean seam (verifiability):** the substrate home is breadstuffs `cell/src/budget.rs`
>   (a widening of `allowance.rs`), proven by reuse of
>   `metatheory/Dregg2/Deos/StandingObligation.lean`'s skeleton (the derived refill
>   clock + the `StrictMonotonic` `consumed`/`refilled` + `root_binds_get` anti-ghost);
>   the one VK-affecting weld is the circuit/light-client binding
>   (`SettleEscrowSatDescriptor.lean`'s staged-no-routing shape). The executor core
>   here is the load-bearing forge-detector; the circuit tooth is its named shadow.
>   **No `circuit/` or `metatheory/` edited (the parallel swarm owns those).**

### C6 — Mount the data plane in the gateway (one real local serving round-trip) · **2 scouts**
DEVWORK-PRODUCT **#1** (the tested storage core has **no gateway mount** —
`gateway/src/storage.rs` does not exist; `LeasedRouter` built but the gateway
serves the *unmetered* `Router`; publish lands in a throwaway in-process registry)
+ CRITIQUE-PRODUCT **finding 2** (`deploy` prints a live `https://<name>.example.com`
URL that **nothing serves** — the keystone DX looks finished and 404s). The fix is
one thing seen from two angles: connect the published/stored cells to a gateway
the process actually serves, so `curl` works on the spot. **Effort M ·
safe-autonomous** (local round-trip) / reviewed-go (public `*.example.com` edge).

### C7 — The stranger's first hour: CLI honesty + discoverability · **2 scouts**
CRITIQUE-PRODUCT **findings 1/3/4/8** (the binary is `dreggnet` but every printed
next-step says `dregg` — which collides with the *substrate* CLI in the sibling
repo; `run --source X` runs a hardcoded demo instead; the CLI is absent from
onboarding; `ls` presents a local JSON notebook as cloud state) + DEVWORK-PRODUCT
CLI items (**#4** `--owner` ignores login, **#2** `--dry-run`, **#3** capture
build output on failure). The codebase's honesty register is excellent in docs and
comments; it just hasn't reached `argv[0]` and the runtime output. **Effort S–M ·
safe-autonomous.**

### C8 — One canonical control loop · **2 scouts (structural + reliability)**
ARCH **S2** (two parallel engines — `Scheduler`/`VmProvider` vs
`Orchestrator`/`BackendRegistry` — both refuse-unfunded→dispatch→meter→reap over
different abstractions + 4–5 node types; a contributor can't tell which is
canonical) + INFRA **R2/R3** (the orchestrator lacks a dispatch timeout and an
orphaned-work reaper — leases stick in `Running`). Designating the `Orchestrator`
as the one loop is where the observability work (C2) and the reliability fixes
both land. The *small* fixes (R2/R3) are safe-autonomous; the *unification* (fold
`VmProvider`/`ServerFleet` into one `Backend`/state machine) is an architectural
call. **R2/R3: M · safe-autonomous. The unification: NEEDS-EMBER-DECISION.**

---

## 2. The work, grouped by what it does for the Verifiable Agent Cloud

Four clusters map to the four properties the epic needs. Each names the VISION
reachable-epic-next it advances.

### Cluster A — SOLID FOUNDATION (the floor everything else stands on)
*The cheapest, highest-leverage, do-first plumbing. Mostly safe-autonomous.*
- **C1** rev-pin forks · **C2** benches→CI + structured logging + control `/metrics`
  + workload-sim calibration · INFRA **T1** node-agent tests (live backend, 0
  tests) · INFRA **D3** Postgres-service CI lane + **#7** gateway test lane · INFRA
  **C3** cherry-pick the seccomp-aarch64 + prebugger hardening commits.
- *Advances:* the operational floor under "5-node finality" — you cannot run a
  fleet you cannot observe or reproduce.

### Cluster B — STRANGER-USABLE (a real developer completes the marquee flow)
*The agent onramp's first mile.*
- **C7** CLI honesty/naming/discoverability · **C6** mount the data plane (one
  local serving round-trip; make `deploy` honest *or* live) · DEVWORK-PRODUCT
  **#5/#6** path params + request-body→handler ABI (gate "real apps") · **#3**
  capture build output · a self-contained DreggNet quickstart (today onboarding
  points into the `breadstuffs/` sibling repo).
- *Advances:* VISION reachable-epic #1, **the agent onramp** (`dregg-cloud agent deploy`
  → cap-account + budget + served API + receipt). Bet #1.

### Cluster C — OPERABLE (we can run it in production without SSH-and-pray)
*The reliability + economy floor.*
- **C4** durable data-plane store (local now; HA = R1 decision) · **C5** the
  `Meter` trait on the replenishing-budget cell · **C8** orchestrator timeout +
  orphaned-work reaper (R2/R3) · DEVWORK-PRODUCT **#9** real server health probe ·
  INFRA **D1** harden `deploy-edge.sh` + post-deploy smoke.
- *Advances:* VISION reachable-epic #2, **the replenishing budget as the meter**
  (a runaway agent rate-bounded *by construction*), and #5 sustained finality.

### Cluster D — FRONTIER-BUILDING (the category nobody else can assemble)
*The bets. Mostly reviewed-go / decision; sequence after the floor is solid.*
- **C3** finish receipts + a live verifier (VISION superpower #1) · **real
  verifiable hosting** — the on-chain `Effect::Write` that replaces the FNV
  `content_root` stand-in with the real Poseidon2 heap root (VISION reachable-epic
  #3; rides the `dregg-verify` AGPL flip — reviewed-go) · **the merge runtime's
  first production path** — two providers reconcile a lease at the boundary as one
  netted `Transfer` (VISION bet #2 rung 1; reviewed-go on the local path) · **wire
  `invoke` to the real ToolGateway** (DEVWORK-PRODUCT #10) · the **agent-onramp
  braid** + **sub-agent split** (Stingray) into one `dregg-cloud agent deploy` (bet #1).
- *Advances:* VISION reachable-epic #3 (real verifiable hosting) and #4 (merge-
  runtime first path) — the differentiators that are files in this tree, needing
  the braid, not new engines.

---

## 3. Decisions needed from ember (short — answer fast, unblock the rest)

Each is irreversible-ish or a topology/architecture call the code can't make
itself. Framed for a quick yes/pick.

| # | Decision | The fork | Recommendation |
|---|---|---|---|
| **D-DURABILITY (R1)** | Data-plane durability across **node loss** | Stay host-local SQLite (right for single-backend node-a staging) **vs** wire `duroxide-pg` / Postgres HA (cost + a redundant fleet) | Do the *local* durable store now (safe); pick HA when a 2nd backend is real. **Pick: defer HA to fleet-grows, or greenlight now?** |
| **D-NET (S1)** | The EOL Elide `net/` stack | Freeze `net/` as a maintained-here-forever internal fork **vs** decide `httpe` is *not* load-bearing and shrink to the pure-std HTTP that ops/webauth already use (drop inert crates: jvm-stubs/jni/JVM patches) | Rev-pin now regardless (C1). **Is httpe load-bearing for the gateway (HTTP/2/TLS/proxy), or do we shrink the vendored surface?** |
| **D-CONTROL (S2)** | Two control loops → one | Make `Orchestrator` canonical; fold `VmProvider`/`ServerFleet` into one `Backend` + one `WorkloadState` (collapse `Machine`/`Backend`/`MeshNode`) | **Greenlight the unification direction?** (the small R2/R3 fixes proceed regardless) |
| **D-CLI-NAME** | The binary-name collision | Sweep prints/docs `dregg`→`dreggnet` **vs** deliberately brand the CLI `dregg-cloud` / `dregg cloud` (never bare `dregg` — collides with the substrate) | **Pick the name.** Then derive prompt strings from the real bin name so it can't drift. |
| **D-VERIFY-FLIP** | Real verifiable hosting (Poseidon2) | The on-chain `Effect::Write` rides the `dregg-verify` **AGPL link-isolation** flip + a live node — an irreversible license/ops boundary | **Greenlight the AGPL-isolated verify path + a live node** when ready for reachable-epic #3. |
| **D-PARADIGM** | `lease`+`run` vs `deploy` | Two unconnected paradigms today (can't `deploy` onto a pre-funded lease) | **Product call:** unify the funding model, or document the split. |

---

## 4. The do-next 8 (dependency / leverage order)

Each item: what · effort · which scout(s) flagged it · disposition. Ordered so
each unblocks the next; the first three are the foundation, then the stranger
mile, then operability.

1. **Rev-pin the Elide forks** (rustls + 16× ntex + hickory → lock SHAs in
   `Cargo.toml`). · **S** · ARCH-S1 + INFRA-#2/C1 · **safe-autonomous.**
   *(C1 — reproducibility floor under everything; 30 minutes.)*

2. **Commit the 8 benches into CI/Makefile + write `docs/PERF.md` SLO baselines +
   add node-agent tests + the Postgres-service & gateway CI lanes.** · **S–M**
   · INFRA-#1/#3/#7/D3/P1 · **safe-autonomous.**
   *(C2 — measurement substrate; the dangling `docs/PERF.md` ref dies here.)*

3. **Structured logging + a control-plane `/metrics` on the orchestrator** (O1–O7:
   per-tick watched/settled/reaped/unplaced, placement-latency, lapse-by-reason).
   · **M** · INFRA-#4/#6/O-series · **safe-autonomous.**
   *(C2 + lands on the canonical loop, C8.)*

4. **CLI honesty pass:** binary-name sweep (`dregg`→`dreggnet`, derived from
   `argv[0]`), `--owner` defaults to login, `--dry-run`, capture build/workload
   output on failure, tag local-vs-network state in `ls`/`deploy`/`run`, fix
   `run --source` to do-or-say. · **M** · CRITIQUE-PRODUCT-1/3/4/8 +
   DEVWORK-PRODUCT-2/3/4 · **safe-autonomous.**
   *(C7 — the stranger's first hour; no architecture touched.)*

5. **Mount the data plane in the gateway** — the storage core (`PUT/GET/DELETE`),
   the `LeasedRouter`, and a `deploy --serve` so a published site is reachable
   locally (`curl -H Host:`). Make `deploy`'s URL honest until the public edge. ·
   **M** · DEVWORK-PRODUCT-#1 + CRITIQUE-PRODUCT-#2 · **safe-autonomous** (local)
   / reviewed-go (public edge).
   *(C6 — turns the keystone promise into a real round-trip.)*

6. **The `Meter` trait** (twin of `Settlement`: durable period cursor +
   `charge(resource, period) -> {Charged|Replayed|Lapsed}`, wall-clock +
   fail-before-commit once) on the replenishing-budget cell; migrate the 5–6
   hand-rolled meters; wire `MeterTick`→`Payable`. · **M** · ARCH-S4 + VISION +
   REPLENISHING-BUDGET + DEVWORK-PRODUCT · **safe-autonomous** (trait) /
   reviewed-go (`Payable` tail).
   *(C5 — stops the recurring meter-bug class; the budget primitive itself.)*

7. **Durable data-plane store** for sites/domains/buckets (the append-only
   `server.rs`/`settle_ledger.rs` pattern, locally) + orchestrator dispatch
   timeout & orphaned-work reaper (R2/R3). · **M** · ARCH-S5 + INFRA-R1/R2/R3 +
   DEVWORK-PRODUCT · **safe-autonomous** (local store + reapers).
   *(C4 + C8 — closes the durability inversion locally; HA is D-DURABILITY.)*

8. **Finish receipt adoption + ship one live verifier** — make
   `HostingReceipt`/`DeployReceipt`/`BindReceipt` typed views over a sealed
   `ReceiptBody`; ship `dregg receipt verify <chain>` (and/or the gateway exposes
   the chain) so a deploy/publish is re-witnessable without trusting the host; add
   receipt e2e tests; print the verify command after `deploy`. · **M** · ARCH-S3 +
   INFRA-T2 + CRITIQUE-PRODUCT · **safe-autonomous.**
   *(C3 — makes VISION superpower #1 real at the surface; the strongest hook.)*

**After the 8 (frontier, sequenced behind the floor + their decisions):** real
verifiable hosting (FNV→Poseidon2, D-VERIFY-FLIP) · the merge-runtime first
production path (bet #2 rung 1) · `invoke`→ToolGateway (DEVWORK-PRODUCT #10) · the
`dregg-cloud agent deploy` braid + sub-agent Stingray split (bet #1) · sustained
finality on the 5-node federation.

---

## 5. The through-line

The convergences cluster cleanly: **the floor** (rev-pin + observability + tests:
C1, C2), **the stranger mile** (CLI honesty + a real serving round-trip: C7, C6),
**the operability spine** (durable data plane + the one `Meter` trait + one
control loop: C4, C5, C8), and **the frontier** (live verifier + real Poseidon2
hosting + the merge runtime: C3 + the bets). Nine of the do-next-eight steps are
safe-autonomous; the six ember decisions are topology/branding/license calls that
gate only the irreversible frontier, not the floor. Build the floor and the
stranger mile now; surface the six decisions; the Verifiable Agent Cloud is the
braid of primitives that already exist in this tree.

---

*Dated 2026-06-30. Synthesized from five scout reports; load-bearing claims
spot-verified against HEAD (forks branch-pinned, no `trait Meter`, `verify_chain`
producer-only, data-plane registries in-memory). Verify a specific file:line
before relying on it.*
