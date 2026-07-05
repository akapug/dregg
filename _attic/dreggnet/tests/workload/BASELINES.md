# Workload-simulation BASELINES

Measured baselines from the first calibrated run of the six `dreggnet-workload`
scenarios (`docs/WORKLOAD-TEST-PLAN.md` §7). The harness drives the REAL
`Orchestrator` loop + `ConservingLedger` settlement rail + the durable layer; only
the lease source (a channel) and the compute backend (the `:8021/fulfill` loopback
stub) are mocked. Run them: `make test-workload` (or
`cargo test -p dreggnet-workload --release -- --ignored --nocapture --test-threads=1`).

- **Host:** macOS (Darwin 25.5, Apple Silicon), `--release`. No `python3`/`node`/
  `/dev/kvm`, so the Caged/MicroVm compute tiers degrade to the wasm path (the
  loopback fulfill stub is tier-agnostic; the tier mix shapes the lease grades, not
  the mocked backend). The numbers are characterization, not an SLA — µs/throughput
  are machine-dependent; the SLO thresholds below carry margin so they stay green
  across machines and CI.
- **Invariants asserted under every load + fault** (the §3 floor): conservation
  Σδ=0 (`total_supply` flat at every sampled instant), meter==settle, exactly-once
  per `(lease,period)`, no unpaid work billed, no phantom credit (Σ debits == Σ
  credits). All held in every scenario.

The Prometheus exposition series for a run is written to
`target/workload/<scenario>.prom` (the soak emits the resource-vs-time series).

---

## §5.1 Scale / load — `scale_load.rs`

1 000 leases (100 tenants × 10), 4×16 fleet, Burst arrival, realistic tier mix,
Funded budget, drain-to-terminal.

| metric | measured |
|---|---|
| throughput | **~2 800–3 000 settles/s** |
| watch→settle p50 / p99 | **~332 / ~356 ms** (queue-wait under a 1 000-lease burst) |
| conservation | flat (`total_supply` constant), meter==settle = 2 000 |
| terminal | 1 000 / 1 000 settled, 0 lapsed |
| max in-flight | 0 (the in-process loop dispatches+settles within a tick) |

**Fleet-size sweep** (1 000 leases each, capacity 16):

| fleet | throughput/s | p50 ms | p99 ms |
|---|---|---|---|
| 1 | ~3 200 | ~312 | ~312 |
| 2 | ~3 260 | ~307 | ~307 |
| 4 | ~3 390 | ~295 | ~295 |
| 8 | ~3 340 | ~299 | ~299 |

(The loopback fulfill stub is not capacity-bound, so throughput is loop+settlement
bound and roughly flat across fleet size; the sweep confirms conservation +
all-terminal hold at every fleet size.)

**Calibrated SLOs:** `throughput_floor` ≥ 250/s · `lease_p99_ceiling` ≤ 2.0 s ·
`capacity_bound` max_inflight ≤ fleet×cap. (Floors/ceilings with ~10× margin over
the observed baseline.)

## §5.2 Multi-tenant isolation — `multi_tenant_isolation.rs`

50 tenants, 1 lease each, distinct funded holders.

- throughput ~1 600 settles/s, conservation flat, meter==settle = 100.
- **metering separation:** each tenant debited EXACTLY its own settled work;
  Σ tenant debits (100) == Σ backend credits (100). No cross-tenant balance move.
- **3 adversarial cross-tenant vectors refused, victim balance flat:**
  (a) a forged re-settle on a victim's already-settled `(lease,period)` key by an
  adversary → **replayed**, no value moved; (b) a forged different-terms charge on a
  victim key → **`SettleError::Conflict`**, victim untouched; (c) an unfunded forged
  cross-tenant lease → refused by the bridge funded-lease gate (no work authorized).

## §5.3 Failure injection — `failure_injection.rs`

30 tenants × 2 leases, 3×8 fleet, a `FaultPlan` per fault. All recover; conservation
holds throughout; no double-settle across any fault.

| fault | recovery observed |
|---|---|
| **backend down** (`BackendDown` @ t=0) | backend-0 marked **Unhealthy**, work fails over to survivors (credit=120), all 60 settle |
| **transient partition** (`Partition` 20–60 ms) | backend-1 **rejoins Healthy** after the window, no lease lost / double-settled |
| **node down** (`NodeDown` 400 ms outage, 400/s Constant arrival) | source down → no new leases read, **no crash, no spurious settle**; resumes → 600 watched / 600 settled |
| **settler restart** (re-drive over the same ledger) | **120 periods replayed**, zero balance movement (exactly-once across restart) |
| **lease lapse** (`Mixed(0.3)`) | 12 of 40 lapsed, each **billed nothing** (balance == funding), clean reap |

## §5.4 Economy correctness under load — `economy_under_load.rs`

200 tenants × 4 leases, 8×16 fleet, `Mixed(0.2)` budget.

- watched 800, settled 625, lapsed 175, throughput ~2 450/s, p99 ~255 ms.
- conservation flat, meter==settle = 1 250, **Σ debits == Σ credits = 1 250**.
- re-drive of all settled leases → 1 250 replays, supply unchanged (dedup is a hard
  idempotency key, not a timing artifact).
- **racing settle:** 12 800 concurrent settles (64 racers × 200 keys) on one
  `ConservingLedger` → **exactly 200 fresh charges**, the beneficiary credited once
  per key, Σδ=0. (This is the test that found + now guards the double-charge bug —
  see *Bug surfaced* below.)

## §5.5 Durability — `durability.rs`

Real on-disk duroxide SQLite stores, exactly-once per step.

- **straight population:** 20 workflows run to completion → aggregate meter 40
  (exactly `N×steps×cost`), each step `run_calls == 1`.
- **crash-resume population:** 12 in-flight workflows parked after step1, the
  runtime torn down (the crash), the SAME stores reopened, all resumed → step1
  **replayed** (`run_calls` flat across the crash), step2 ran once, aggregate meter
  24 (exactly-once). Resume time **~12.3 s for 12 workflows (~1 027 ms/workflow)** —
  dominated by SQLite WAL `database is locked` backoff under 12 concurrent stores on
  one runtime (retryable; not a failure). Resume time will be far lower per-workflow
  with fewer concurrent stores or the pg provider.
- **pg variant:** SKIPPED-clean when `DATABASE_URL` is unset (the norm); the sqlite
  path covers the guarantee. The live-pg drive needs the durable `pg` feature +
  `durable/tests/durable_resume_pg.rs`.

## §5.6 Endurance / soak — `endurance_soak.rs`

50 tenants, Constant 250/s arrival (a sustainable rate — the loop drains ~3 000/s),
4×16 fleet, 20 s default (`DREGGNET_WL_DURATION=8h` for the overnight window).

- throughput tracks the ~250/s arrival (the loop keeps up, no runaway backlog),
  in-flight bounded.
- **conservation flat across the ENTIRE soak** — thousands of `total_supply` samples,
  all equal (the strongest conservation test: every metered unit settled, supply
  constant).
- **resource series** (`target/workload/endurance_soak.prom`, sampled every 500 ms):
  RSS first-third vs last-third stays well under the leak ceiling, open fds bounded
  (≤ 4096). No leak at the 20 s steady state.

**Calibrated leak SLOs:** `rss_no_leak` last-third ≤ first-third×1.5 + 64 MB ·
`fds_bounded` ≤ 4096. These catch *runaway* growth — e.g. an overdriven 2 000/s run
(arrival far above the drain rate) grew RSS 46→384 MB as the backlog exploded; the
calibrated profile drives a sustainable rate and stays flat. Note the steady-state
ceiling assumes the retained working set is bounded by the run length — see the
scaling note below.

The arrival rate is held modest (250/s) for a second reason: each dispatch is a
short-lived loopback TCP connection (`Connection: close`), so a high sustained rate
churns the host's ephemeral-port / TIME_WAIT pool. At an overdriven rate the soak
exhausted the pool and starved the binary that runs *next* in the gated suite
(`failure_injection` follows `endurance_soak` alphabetically) — its loopback
connects failed, so leases did not settle. TIME_WAIT pressure is rate-bounded (not
duration-bounded), so the modest rate keeps the cross-binary handoff clean at any
duration. (A test-infra artifact of the loopback transport, not a product bug.)

---

## Bug surfaced by the load tests (a win — found + fixed)

**`ConservingLedger::settle` double-charged under concurrent settle of the same
`(lease,period)` key.** The §5.4 racing-settle scenario (12 800 concurrent settles
on 200 keys) measured **218 fresh charges where exactly 200 were expected** — 18
keys charged twice. Root cause: the exactly-once dedup check (the `settled` map
lock) was released *before* the conserving value move (the `balances` lock), so two
racers could both pass the not-yet-settled check and both move value. Conservation
(Σδ=0) still held, but the documented exactly-once guarantee did not.

**Fix** (`durable/src/settle.rs`): the dedup check, the value move, and the record
insert are now one atomic critical section — the `settled` lock is held across all
three (lock order `settled` → `balances`, no inverse path, deadlock-free). After the
fix the race lands exactly 200 charges. The racing-settle scenario is the standing
regression.

## Scaling note (queued, out of harness scope)

The orchestrator's in-memory `workloads` tracking map is **never reaped** — it grows
with the cumulative number of leases processed. The short default soak stays under
the RSS ceiling because the retained set is bounded by the 20 s duration; an 8 h
overnight soak at a sustained rate would grow the map (and RSS) without bound. This
is an orchestrator design property, not a harness or settlement bug; it is the kind
of long-run growth the soak is built to flag. Reaping terminal workloads from the
tracking map (a retention/TTL policy) is the follow-up — outside `tests/workload/`,
so it is recorded here rather than fixed in this pass.

---

*Dated 2026-06-29. Regenerate by re-running the suite; the `.prom` series land in
`target/workload/`.*
