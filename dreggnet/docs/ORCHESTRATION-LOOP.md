# The autonomous lease-orchestration loop

The loop is the control-plane daemon that turns DreggNet from "a lease runs when
someone calls the create-API" into a continuous cloud: it watches for funded
execution-leases and runs each to settlement by itself, across a multi-backend
fleet.

```
  ┌──────────────────── Orchestrator::run_until_shutdown ─────────────────────┐
  │  every tick:                                                               │
  │   1. WATCH    — poll the LeaseSource for funded/active execution-leases    │
  │   2. SCHEDULE — BackendRegistry::pick a healthy backend (round-robin,      │
  │                 capacity-bounded)                                          │
  │   3. DISPATCH — dispatch_lease_over_mesh → the durable metered workload    │
  │                 runs on the backend's :8021/fulfill bridge agent           │
  │                 (failover to the next healthy backend if one is down)      │
  │   4. METER    — the durable run ticks per-period against the lease budget  │
  │   5. SETTLE   — Payable: each metered period → one conserving Transfer     │
  │                 lessee → backend, EXACTLY-ONCE                             │
  │   6. REAP     — a lapsed / refused lease yields no billable work; reaped   │
  │  on a cadence: health-check the whole fleet so pick draws from a fresh view│
  └────────────────────────────────────────────────────────────────────────────┘
```

It is a real daemon, not a one-shot: `Orchestrator::run_until_shutdown` loops on a
`tokio` interval until a shutdown future fires; `Orchestrator::tick` runs one
iteration (the unit the tests drive).

## The pieces

| concern | type | crate |
|---|---|---|
| the daemon loop | `orchestrator::Orchestrator` | `dreggnet-control` |
| where leases come from | `orchestrator::LeaseSource` (+ `ChannelLeaseSource`) | `dreggnet-control` |
| multi-backend scheduling | `fleet::BackendRegistry` (`register`/`health_check_all`/`pick`/`dispatch`) | `dreggnet-control` |
| reaching a backend | `mesh::dispatch_lease_over_mesh` (the proven `:8021/fulfill` POST) | `dreggnet-control` |
| the durable metered run | `WorkloadRun` + `MeterTick` | `dreggnet-durable` |
| settlement (the Payable rail) | `settle::Settlement` (+ `ConservingLedger`) | `dreggnet-durable` |

## Multi-backend scheduling

`BackendRegistry` is the live set of compute backends — node-a today, the homelab
boxes as they join. Each `Backend` is a named, capacity-bounded `MeshNode`.

- **health-check** — `health_check_all` connects to each backend over the mesh and
  probes its bridge-agent port; a node that does not answer is marked unhealthy and
  skipped.
- **pick** — `pick` chooses the next healthy backend with spare capacity,
  round-robin, so load spreads across the fleet.
- **dispatch + failover** — `dispatch` picks a backend and POSTs the lease to it;
  on a transport fault it marks that backend down and tries the next healthy one,
  until one succeeds or the fleet is exhausted. A lease *lapse* (the bridge refusing
  an over-budget lease) is not a failover — it is the lease's fault, surfaced for the
  orchestrator to reap.

## Metering → Payable coherence (the three ledgers, folded into one)

A leased durable run touches three quantities; the loop keeps them one coherent
ledger rather than three independent counters:

```
  lease budget    (the RESERVE)  — budget_units the funded lease proves was paid in.
    └─ durable meter (the TICK)  — each step's MeterTick charges per_period_units
       │                           against the reserve; an over-budget tick fails the
       │                           workflow BEFORE it commits (lapse → reap). The
       │                           per-(lease,period) charge rows are the meter outbox.
       └─ Payable settle (PAY)   — each metered period is settled as one conserving
                                   transfer lessee → backend, EXACTLY-ONCE keyed by
                                   (lease, period).
```

The invariant the fold upholds (and the tests prove): for any lease,
`Σ settled(period) == Σ metered(period) ≤ budget`, and **every transfer conserves**
(the payer is debited exactly what the beneficiary is credited, so per-asset Σδ = 0
— the dregg value model). Re-running a period (a crash re-dispatch, a daemon
re-poll) settles nothing new: `(lease, period)` is the idempotency key, so the meter
is exactly-once (duroxide replay / the pg outbox `ON CONFLICT DO NOTHING`) and the
settlement is exactly-once (`ConservingLedger`'s dedup), and the two never
double-count each other.

`ConservingLedger` is the faithful in-process twin of the dregg `Payable`. The named
on-chain wire: breadstuffs' `dregg-payable` `Payable.pay(asset, amount, to)` desugars
to ONE kernel `Effect::Transfer` (a `LinearityClass::Conservative` effect — per-asset
Σδ = 0, checked across the app boundary), whose receipt a light client witnesses. The
seam is exactly `Settlement::settle` — the orchestrator drives it identically over
either backend.

The pg fold path is `settle::settle_meter_outbox` (feature `pg`): it reads the
`dreggnet_meter` outbox rows a durable run committed and settles each through a
`Settlement` — the literal "the Payable settlement reads the meter outbox" path. The
fully shared-transaction settlement (the meter write, the checkpoint, and the dregg
`Payable` in one Postgres transaction with breadstuffs' `pg-dregg`) is the next rung.

## What is live vs mocked vs the on-chain gap

- **Live (real):** the loop; the multi-backend pick / health / failover; the dispatch
  (the proven `:8021/fulfill` POST over the mesh — the same path the node-a deploy
  uses); the conserving, exactly-once settlement.
- **Mocked offline:** the lease source (`ChannelLeaseSource`) and, in tests, the
  compute backend (a loopback server speaking the node-agent's `/fulfill`
  contract, budget-gated exactly like the real agent).
- **The named on-chain gap — reading funded leases from a live dregg node:** the
  verified decode is real behind `dreggnet-bridge`'s `dregg-verify` feature
  (`DreggNodeFeed` / `dregg_verify::read_funded_leases` — it attests a node's whole
  receipt log and decodes each funded execution-lease grant). The remaining step is
  the light-client RPC transport that fetches the receipt-log records. Flipping
  `dregg-verify` on is a workspace-lock change (the arkworks `serde_with` fork patch +
  the vendored lockstitch — see `bridge/Cargo.toml`'s FLIP-ON note) and makes the
  build a derivative work of AGPL code, so it is the deliberate flip-on step, not the
  default. Until then the daemon reads leases from a `LeaseSource` the operator feeds
  (the gateway create-API, a fixture, or — feature-on — the node feed).
