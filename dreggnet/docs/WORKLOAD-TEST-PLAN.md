# WORKLOAD-TEST-PLAN — simulating cloud workloads against DreggNet

This is the plan + the scaffold for a **workload-simulation test suite**: a harness
that drives DreggNet the way a real multi-tenant cloud is driven — many tenants,
each opening funded execution-leases, running workloads at a tier, metered and
settled — concurrently, at scale, under failure, over time — and *measures* what
happens (throughput, latency, finality, economy conservation, resource use).

It is the system-level companion to the two test bodies that already exist:

- **The functional gauntlet** (`make test`, `scripts/test.sh`) — the offline-green
  correctness suite over the seven service crates (the orchestration loop, durable
  crash-resume, the lease→durable workflow, the publish/serve round-trip). It proves
  *the loop is correct on one or two leases*.
- **The micro-benches** (`cargo bench` in `durable/`, `exec/`, `webapp/`) — per-step
  latency + single/wide-thread throughput characterization of individual layers
  (the durable checkpoint tax, per-cap-tier `run_workload` latency, the router rps).
  They prove *each layer's per-operation cost*.

The workload suite is the missing third body: **the whole system under realistic,
concurrent, multi-tenant, adversarial, sustained load**. Where the gauntlet asserts
*correctness on a handful of leases* and the benches measure *one layer in isolation*,
the workload suite asserts *the invariants still hold and the SLOs are met when N
tenants pound the orchestration loop at once* — and it injects failures and runs for
hours to find what only breaks at scale or over time.

Status: **scaffolded**. The harness compiles and the six scenario classes are present
as `#[ignore]`d skeletons (an explicit assertion-free body + a `TODO(overnight)`
marker). An overnight run fills the bodies in and runs them; see
[§7 The fill-in plan](#7-the-fill-in-plan-overnight).

---

## 1. What we simulate — the cloud workload model

A DreggNet cloud is, at the load level, four nouns and one loop:

| noun | what it is in the model | grounded in |
|---|---|---|
| **tenant** | an independent lessee cell (a holder + a funded balance in an asset) | `ConservingLedger::fund(asset, holder, …)`, `Lease::funded(holder, …)` |
| **lease** | a funded `execution-lease`: holder, `CapGrade`, asset, budget, per-period rent | `dreggnet_bridge::Lease`, `CapGrade` |
| **workload** | a unit of metered compute at a cap-tier (a durable, multi-step run) | `dreggnet_exec::run_workload` / `dreggnet_durable::WorkloadRun` |
| **backend** | a capacity-bounded compute node the loop dispatches to | `control::{Backend, BackendRegistry}` |
| **the loop** | watch → schedule → dispatch → meter → settle → reap, per tick | `control::orchestrator::Orchestrator` (see `docs/ORCHESTRATION-LOOP.md`) |

The simulator drives **all five** through their real public surfaces. It does *not*
re-implement the loop or the economy; it feeds the real `Orchestrator` a population
of real `Lease`s from real (channel or node-API) `LeaseSource`s, dispatches to
loopback `:8021/fulfill` backends that speak the real node-agent contract
(budget-gated exactly like the real agent), and settles on the real
`ConservingLedger` (the faithful in-process twin of the dregg `Payable`). The only
things mocked are the things the offline gauntlet already mocks: the lease *source*
and the compute *backend* — and they are mocked at the same contract boundary, so a
scenario that passes here is meaningful for the live deploy.

### The load-generation model

A run is parameterized by a **load profile** — the knobs a scenario sets:

| knob | meaning | env override |
|---|---|---|
| `tenants` | number of distinct lessee cells | `DREGGNET_WL_TENANTS` |
| `leases_per_tenant` | how many leases each tenant opens over the run | `DREGGNET_WL_LEASES_PER_TENANT` |
| `arrival` | lease arrival process: `Poisson(λ)` / `Constant(rate)` / `Burst(n, gap)` | `DREGGNET_WL_ARRIVAL` |
| `tier_mix` | distribution over `CapTier` (the realistic mix below) | `DREGGNET_WL_TIER_MIX` |
| `steps_per_workload` | durable steps per run (the per-workload metering depth) | `DREGGNET_WL_STEPS` |
| `budget_model` | `Funded` (covers all steps) / `Tight` (lapses mid-run) / `Mixed(p)` | `DREGGNET_WL_BUDGET` |
| `backends` | fleet size + per-backend capacity | `DREGGNET_WL_BACKENDS` |
| `duration` | wall-clock for soak; or `until N leases settle` | `DREGGNET_WL_DURATION` |

The **realistic tier mix** (from `docs/COMPUTE-TIERS.md`, the four wired tiers) the
default profile draws from:

- **40 % `Sandboxed`** — lightweight trusted wasm (pure arithmetic, bounded), the
  cheapest real sandbox (`polyana-wasmi`).
- **30 % `JitSandboxed`** — untrusted wasm needing a runaway bound (`wasmtime`, fuel).
- **20 % `Caged`** — interpreted polyglot (Python/Node subprocess), semi-trusted.
  *Skips cleanly when `python3`/`node` are absent — the harness records SKIPPED, never
  a false pass, mirroring the exec crate's own tests.*
- **10 % `MicroVm`** — strong isolation (Firecracker). *Skips when `/dev/kvm` is
  absent (macOS, CI), recorded SKIPPED.*

On a host without the native runtimes/KVM, a scenario degrades to the wasm tiers and
records the skipped fraction — the wasm tiers run everywhere, so every scenario has a
non-empty load even on a bare macOS box.

### Tenant identity (the isolation substrate)

Each tenant is `tenant-{i}`, a distinct holder funded in its own asset balance, and
each lease carries a `CapGrade` and a per-tenant lease id (`lease-{tenant}-{seq}`).
Isolation is asserted on this identity: a tenant's cap authorizes only its own
lease's workload at its own grade; its budget debits only its own balance; its meter
charges key on `(its lease, period)`. The simulator constructs these distinctly and
the isolation scenario (§5.2) probes that one tenant cannot read, affect, or be billed
for another's.

---

## 2. The harness architecture

The harness lives in `tests/workload/` as the `dreggnet-workload` crate (a workspace
member, **not** in the `make test` service-crate set, so it never runs in the default
gauntlet). Three pieces:

```
  tests/workload/
    Cargo.toml                  # dreggnet-workload — dev-deps the real service crates
    src/
      lib.rs                    # re-exports: Simulator, Scenario, LoadProfile, Metrics
      profile.rs                # LoadProfile + the env-override parsing + tier mix sampler
      tenant.rs                 # Tenant, the lessee population + funding
      simulator.rs              # Simulator: builds the fleet, the ledger, the loop; runs a profile
      backends.rs               # spawn_fulfill_fleet(): loopback :8021/fulfill stubs (real contract)
      metrics.rs                # Metrics: latency histogram, throughput, conservation, resource
      faults.rs                 # FaultPlan: node-down / backend-down / partition / crash / lapse
      report.rs                 # the run report: SLO table + Prometheus exposition text
    tests/
      scale_load.rs             # §5.1
      multi_tenant_isolation.rs # §5.2
      failure_injection.rs      # §5.3
      economy_under_load.rs     # §5.4
      durability.rs             # §5.5
      endurance_soak.rs         # §5.6
```

### `Simulator` (the core)

```rust
pub struct Simulator {
    registry: Arc<BackendRegistry>,     // the fleet
    ledger:   Arc<ConservingLedger>,    // the Payable twin (settlement rail)
    mesh:     Arc<TailscaleMesh>,
    profile:  LoadProfile,
    metrics:  Arc<Metrics>,
    faults:   FaultPlan,
}

impl Simulator {
    pub fn new(profile: LoadProfile) -> Self;            // build fleet+ledger+mesh from the profile
    pub fn with_faults(self, plan: FaultPlan) -> Self;   // inject a fault schedule
    pub async fn run(&self) -> RunReport;                // drive the loop to drain/duration
    pub fn metrics(&self) -> &Metrics;
}
```

`run()` stands up a real `Orchestrator::new(registry, mesh, ledger)`, feeds it leases
from a `ChannelLeaseSource` at the profile's arrival rate from a population of
`Tenant`s, and either runs the daemon (`run_until_shutdown`) under a stop signal
(soak) or pumps `tick(&mut source)` to drain (scale). Every lease's lifecycle
(`watched → scheduled → dispatched → metered → settled | lapsed | reaped`) is timed
and recorded into `Metrics`. The economy invariants are checked against the live
`ConservingLedger` (`balance`, `total_supply`).

### `Scenario` (the trait the six classes implement)

```rust
#[async_trait]
pub trait Scenario {
    fn name(&self) -> &str;
    fn profile(&self) -> LoadProfile;             // the load this scenario drives
    fn faults(&self) -> FaultPlan { FaultPlan::none() }
    async fn run(&self, sim: &Simulator) -> RunReport;
    fn check(&self, report: &RunReport) -> Vec<SloResult>;   // the SLO + invariant assertions
}
```

A scenario is *fill-in-the-blank*: `profile()`/`faults()` declare the load, `run()` is
usually `sim.run().await` (the default), and `check()` is the scenario-specific SLO +
invariant table. The skeletons ship `check()` returning `TODO(overnight)` placeholders
the overnight run replaces with real thresholds.

### `Metrics` (the measurement core)

A lock-light collector (atomic counters + an HDR-style latency histogram per phase):

```rust
pub struct Metrics { /* per-phase histograms, counters, conservation snapshots */ }
impl Metrics {
    pub fn observe_lease(&self, ev: LeaseEvent);    // record a lifecycle transition + timestamp
    pub fn snapshot(&self) -> MetricSnapshot;       // p50/p99 per phase, throughput, in-flight
    pub fn prometheus(&self) -> String;             // exposition format (see §6)
}
```

### `FaultPlan` (failure injection)

A schedule of faults applied to the live fleet/ledger/loop during a run:

```rust
pub enum Fault {
    BackendDown { backend: String, at: Duration },        // mark a fulfill stub unreachable
    NodeDown { at: Duration, for_: Duration },             // the lease-source node stops answering
    Partition { backend: String, at: Duration, for_: Duration },  // transient transport fault
    SettlerRestart { at: Duration },                       // tear down + reopen the durable store
    LeaseLapse { fraction: f64 },                          // a fraction of leases go over-budget mid-run
}
pub struct FaultPlan(Vec<Fault>);
```

---

## 3. The invariants every scenario upholds

These are checked in **every** scenario's `check()` (a shared `assert_invariants`),
because they must hold under *all* load and *all* faults — they are the floor:

1. **Conservation (Σδ = 0).** For every asset, `ledger.total_supply(asset)` is
   constant across the entire run — no value created or destroyed by any settlement,
   concurrent or not. (The dregg value model; `ConservingLedger`'s core property.)
2. **Meter = settle.** For every settled lease, `settled_units == meter_units`, and
   `Σ settled(period) == Σ metered(period) ≤ budget`. The three-ledger fold is
   coherent at scale (`docs/ORCHESTRATION-LOOP.md` §"Metering → Payable coherence").
3. **No double-charge.** `(lease, period)` is the idempotency key; a re-poll /
   re-dispatch / crash-replay settles nothing new. Asserted by replaying ticks and
   confirming balances do not move.
4. **No unpaid work billed.** A lapsed/reaped lease leaves the lessee's balance
   exactly as funded — the backend is never credited for refused work.
5. **No phantom credit.** `Σ over all backends credited == Σ over all tenants debited`,
   per asset.

A scenario that injects faults additionally asserts the *recovery* invariant for that
fault class (§5.3, §5.5).

---

## 4. Measurement — what we measure and how

### The metrics

| metric | definition | where it comes from |
|---|---|---|
| **throughput** | settled leases / sec (and metered units / sec) | `Metrics` counters / wall-clock |
| **lease latency p50/p99** | time `watched → settled` | per-lease timestamps |
| **phase latency** | `schedule`, `dispatch`, `meter`, `settle` each, p50/p99 | per-phase histograms |
| **finality latency** | time `metered → settled` (the Payable settle leg) | settle-phase histogram |
| **in-flight / queue depth** | leases `watched` but not yet terminal, sampled per tick | gauge |
| **conservation** | `total_supply(asset)` over time (must be flat) | `ledger.total_supply` snapshots |
| **lapse rate** | reaped leases / watched leases | counters |
| **failover rate** | dispatches that retried to another backend | `BackendRegistry` status deltas |
| **resource use** | RSS, open fds, tokio task count, durable-store size on disk | sampled via `/proc` (Linux) or `getrusage`; durable file `stat` |
| **recovery time** | fault-injected → back to healthy throughput | fault timestamp vs throughput recovery |

### How it ties to the live o11y (`docs/MONITORING.md`)

The same quantities the `dreggnet-ops` dashboard watches on the live deploy are the
ones the harness measures, so a simulated regression maps to a real alert:

- **conservation** ↔ the ops `bridge_conservation_breach` PAGE (`live ≤ locked`,
  per asset). The harness asserts the in-process equivalent (`total_supply` flat).
- **backend down / lease lapse** ↔ ops `backend_down` WARN (the dominant lease-lapse
  cause). §5.3 injects exactly this and asserts the lapse-then-recover signal.
- **durable / postgres** ↔ ops `postgres_down` / "durable jobs in flight". §5.5
  asserts in-flight recovers after a settler restart.
- **queue depth / in-flight** ↔ the ops "durable jobs in flight" tile.

`Metrics::prometheus()` emits the run's series in Prometheus exposition format
(`dreggnet_wl_lease_latency_seconds`, `dreggnet_wl_settled_total`,
`dreggnet_wl_conservation_supply`, `dreggnet_wl_inflight`, …) so a soak run can be
scraped into the same Grafana that watches the deploy — the harness produces the
*same shape of series* the node/ops layer produces, never adding metrics to the node
(the MONITORING.md principle: the orchestration lane owns the metrics; this lane
consumes/produces the same shape). The run report (`report.rs`) prints an SLO table to
stdout and writes the exposition text to `target/workload/<scenario>.prom`.

---

## 5. The six scenario classes

Each: **goal**, **load**, **what it asserts** (the SLO + which §3 invariants), and
**what is scaffolded vs the overnight fill-in**.

### 5.1 Scale / load — `scale_load.rs`

**Goal.** Many concurrent leases/workloads drained through one loop over a small
fleet; measure throughput + latency and confirm the loop and the economy hold under
concurrency.

**Load.** `tenants = 100`, `leases_per_tenant = 10` (1 000 leases), `arrival =
Burst`, `backends = 4 × capacity 16`, tier mix = default, `budget = Funded`.

**Asserts.** §3 invariants (1,2,3,4,5) hold across all 1 000 settlements; throughput
≥ an SLO floor; lease-latency p99 ≤ an SLO ceiling; no backend exceeds its capacity
bound (the round-robin spreads load); in-flight never grows unbounded (the loop keeps
up). Sweeps `backends ∈ {1,2,4,8}` to show the failover/capacity scaling curve.

**Scaffolded:** the profile, the 1 000-lease drive via `Simulator::run`, the
invariant assertions. **Overnight:** the throughput/p99 SLO thresholds (calibrate from
a first run), the `{1,2,4,8}` sweep table, the latency-vs-fleet-size curve.

### 5.2 Multi-tenant isolation — `multi_tenant_isolation.rs`

**Goal.** Tenants cannot see, affect, or be billed for each other — the cap bound, the
sandbox, the metering separation.

**Load.** `tenants = 50`, each one lease, deliberately adversarial: tenant A's
workload attempts to address tenant B's lease id / cap / balance.

**Asserts.** (a) **cap bound** — a workload presented under tenant A's `CapGrade`
cannot be dispatched against tenant B's lease (the loop refuses; cross-tenant dispatch
never settles). (b) **metering separation** — A's settlement debits only A's balance;
`ledger.balance(asset, B)` is untouched by A's activity. (c) **sandbox isolation** — a
`Sandboxed`/`JitSandboxed` workload cannot escape its tier (it observes only its own
inputs; no shared mutable state across tenants' runs). (d) **no cross-bill** — the
`(lease, period)` key is per-tenant, so A's periods never settle to B's backend
credit nor charge B. Negative tests: a forged cross-tenant lease/cap is *refused*, not
silently executed.

**Scaffolded:** the 50-tenant population, the per-tenant distinct funding + caps, the
adversarial cross-address attempts (constructed but assertions are `TODO`).
**Overnight:** wire each refusal assertion to the real refusal path (the bridge's
cap-grade gate + the ledger's per-holder debit), confirm each cross-tenant attempt
yields a refusal/lapse and zero balance movement on the victim.

### 5.3 Failure injection — `failure_injection.rs`

**Goal.** The system recovers or degrades correctly under: a node down, a compute
backend down, a network partition, a settler restart, a lease lapse mid-workload.

**Load.** `tenants = 30`, steady arrival, fleet of 3 backends; a `FaultPlan` schedules
each fault during the run.

**Asserts, per fault:**
- **backend down** (`Fault::BackendDown`) — dispatches **fail over** to a healthy
  backend (no lease stuck), the dead backend is marked `Unhealthy`, throughput dips
  then recovers, conservation holds. (The grounded `orchestration_loop` failover path,
  now under concurrent load.)
- **network partition** (`Fault::Partition`) — a *transient* transport fault marks the
  backend down then it rejoins on the next health-check; leases in flight retry, none
  lost, none double-settled.
- **node down** (`Fault::NodeDown`, the lease source stops answering) — the loop reads
  no new leases while down (no crash, no spurious settlement), and resumes watching
  when the source returns.
- **settler restart** (`Fault::SettlerRestart`) — tear down + reopen the durable store
  mid-run; in-flight workflows resume **exactly-once** (no double-charge), settlement
  continues. (The durable crash-resume guarantee under load — see §5.5.)
- **lease lapse mid-workload** (`Fault::LeaseLapse`) — a fraction go over-budget
  mid-run; each lapses cleanly (the over-budget tick fails *before* commit), is reaped,
  and bills nothing for the unpaid remainder (§3 inv 4).

**Scaffolded:** `FaultPlan` + the five `Fault` injectors wired to the live fleet/ledger
(`BackendDown` flips a stub to refuse, `SettlerRestart` reopens the store), the
scenario harness applies the plan on schedule. **Overnight:** the recovery-time SLO per
fault, the assertion that post-recovery throughput returns to within X % of baseline,
and the partition/node-down rejoin assertions.

### 5.4 Economy correctness under load — `economy_under_load.rs`

**Goal.** Conservation, no double-charge, and meter=settle hold under *concurrent*
settlement — the economy is the thing most likely to corrupt under races.

**Load.** `tenants = 200`, high concurrency (`backends = 8`, settlement from many
in-flight leases at once), `budget = Mixed(0.2)` (20 % lapse), tier mix = default.

**Asserts.** The §3 invariants, but specifically *under contention*: many concurrent
`Settlement::settle` calls against one `ConservingLedger`; assert `total_supply`
constant at every sampled instant (not just at the end); assert per-`(lease,period)`
dedup holds when the same period is settled from two racing code paths (a re-poll
during an in-flight settle); assert the sum of all debits equals the sum of all
credits per asset at the end. A stress variant deliberately re-drives already-settled
leases to prove the dedup is a hard idempotency key, not a timing artifact.

**Scaffolded:** the 200-tenant high-concurrency drive, the conservation sampler, the
re-drive (double-settle attempt). **Overnight:** the concurrent-settle race
construction (spawn racing settles on the same key), the per-instant conservation
assertion at a sampling cadence, the final debit==credit reconciliation table.

### 5.5 Durability — `durability.rs`

**Goal.** Crash-resume across the workload (the durable SQLite layer), exactly-once,
under a population of in-flight workflows.

**Load.** `tenants = 20`, each running a multi-step durable `WorkloadRun` on an on-disk
store; a crash (runtime teardown) is injected with workflows parked mid-run.

**Asserts.** Each parked workflow resumes over the *same* on-disk store with its
completed steps **replayed, never re-executed** (`metrics::run_calls` flat across the
crash), its meter charged **exactly once per step** (no double-charge), and its final
output correct. At scale: *all* in-flight workflows resume correctly, not just one;
the aggregate meter total equals `Σ steps` with no duplication. (Generalizes
`durable/tests/durable_resume.rs` from one workflow to a population.)

**Scaffolded:** the population of on-disk durable workflows, the crash (teardown +
reopen), the resume drive, the exactly-once assertions per workflow.
**Overnight:** scale the population to N, assert the aggregate exactly-once meter total,
add the pg-store variant behind `DATABASE_URL` (mirrors `durable_resume_pg.rs`), and
measure resume time as a function of in-flight count.

### 5.6 Endurance / soak — `endurance_soak.rs`

**Goal.** Sustained load over time surfaces leaks, resource exhaustion, and unbounded
queue growth.

**Load.** `tenants = 50`, steady `arrival = Constant`, `duration` = hours (overnight),
fleet of 4, continuous lease churn (open → run → settle → close, repeat).

**Asserts.** Over the whole duration: RSS does not grow unboundedly (a leak ceiling),
open-fd count is bounded, tokio task count returns to baseline between bursts (no task
leak), the durable-store file size is bounded (checkpoints are reaped, not appended
forever), in-flight/queue depth is bounded (the loop keeps up — no runaway backlog),
and conservation holds for the *entire* run (the strongest conservation test: millions
of settlements, `total_supply` still flat). Throughput is stable (no degradation over
time).

**Scaffolded:** the steady-state churn loop, the periodic resource sampler
(RSS/fds/tasks/store-size), the duration gate (`DREGGNET_WL_DURATION`).
**Overnight:** run it for the full overnight window, set the leak/bound SLO ceilings
from the observed steady state, plot the resource-vs-time series into the `.prom`
output, and flag any monotonic growth.

---

## 6. Running it — gating + `make test-workload`

The suite is **gated out of the default gauntlet** two ways, so `make test` never runs
it: (a) the `dreggnet-workload` crate is *not* in `scripts/test.sh`'s explicit
`SERVICE_CRATES` `-p` list, and (b) every scenario test is `#[ignore]`d. It is run
explicitly:

```make
## test-workload: the workload-simulation suite (gated — not in `make test`)
test-workload:
	cargo test -p dreggnet-workload --release -- --ignored --nocapture --test-threads=1
```

- `--ignored` runs the `#[ignore]`d scenarios; `--release` because load/soak want the
  optimized build; `--test-threads=1` so the scenarios (each saturates the fleet) do
  not contend.
- **Env knobs** (all default to the modest values above so the suite is runnable on a
  laptop; the overnight run scales them up): `DREGGNET_WL_TENANTS`,
  `DREGGNET_WL_DURATION`, `DREGGNET_WL_BACKENDS`, etc. (see §1).
- A single scenario: `cargo test -p dreggnet-workload --release scale_load -- --ignored
  --nocapture`.
- The soak is duration-gated: `DREGGNET_WL_DURATION=8h cargo test -p dreggnet-workload
  --release endurance_soak -- --ignored --nocapture`.

The harness **lib** compiles in the default workspace build (so `cargo build` / `cargo
check` keep it green), but its *scenarios never run* unless invoked with `--ignored`.
This matches the repo's gated-lane convention (`docs/TESTING.md`): a lane that needs a
resource (here: time + concurrency budget) is present, compiling, and SKIPPED-by-default,
never failing the offline run.

---

## 7. The fill-in plan (overnight)

What is **done** (compiles + green today):

- The `dreggnet-workload` crate skeleton: `Simulator`, `Scenario`, `LoadProfile`,
  `Metrics`, `FaultPlan`, `Tenant`, the loopback fulfill-fleet, the run report.
- The six scenario files, each with its `profile()`/`faults()` declared and a `run()`
  that drives the real loop; the **shared §3 invariant assertions** wired.
- The `make test-workload` target + the env-knob parsing.
- This plan.

What the **overnight run fills in** (each marked `TODO(overnight)` at its site):

1. **Calibrate the SLOs** — run each scenario once, read the observed throughput /
   p50 / p99 / resource baselines, and write them in as the assertion thresholds
   (`check()` returns real `SloResult`s instead of placeholders).
2. **The adversarial isolation assertions** (§5.2) — wire each cross-tenant refusal to
   its real refusal path and assert zero victim-balance movement.
3. **The fault recovery SLOs** (§5.3) — recovery-time-to-baseline per fault; the
   partition/node-down rejoin assertions.
4. **The concurrent-settle race** (§5.4) — the racing-settle-on-one-key construction +
   the per-instant conservation sampler.
5. **The durable population** (§5.5) — scale to N in-flight workflows; the aggregate
   exactly-once meter total; the optional pg variant.
6. **The soak run** (§5.6) — run the full overnight window; set the leak/bound ceilings
   from steady state; emit the resource-vs-time `.prom` series.
7. **Run the whole suite**, collect the `.prom` outputs + the SLO tables, and write a
   short results note (throughput curves, the failover/recovery numbers, any leak
   flagged by the soak).

The acceptance bar for the overnight run: every scenario green with *real* (calibrated)
SLO thresholds, the §3 invariants asserted under every load and fault, and a results
note with the measured throughput/latency/finality/conservation/resource numbers.

---

*Dated 2026-06-29. The harness drives the real `Orchestrator` / `ConservingLedger` /
`run_workload` surfaces; the only mocks are the lease source + the compute backend, at
the same contract boundary the offline gauntlet mocks them. Verify type signatures
against HEAD before relying on a specific one.*
