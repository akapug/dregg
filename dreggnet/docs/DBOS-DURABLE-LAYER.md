# DBOS-style durable execution for DreggNet

The layer **between** the two halves of DreggNet:

```
  dregg (breadstuffs, AGPL)  — meters / pays / verifies the execution-lease
    └─ dreggnet-durable       — THIS layer: durable, transactional, recoverable workflow
       └─ dreggnet-exec       — run_workload → polyana
          └─ polyana          — the sandboxed execution engine (rung 2 landed)
```

polyana *executes*; dregg *meters and pays*; this layer makes a workload a **durable
workflow** — one that survives a crash and resumes exactly-once from its last checkpoint,
with the work and the meter committed together-or-not.

## What the two external libraries actually are (grounded)

Cloned and read at `github.com/microsoft/duroxide` and `github.com/microsoft/pg_durable`.

### duroxide — MIT

A lightweight, **embeddable durable-execution runtime for Rust** (the Durable-Task /
Temporal lineage). You write ordinary `async` Rust; duroxide makes it durable across
process crashes and restarts. The model:

- An **orchestration** (workflow) is *deterministic coordination* — it only decides what
  to do next from results it already holds. It must not do I/O directly, and must use
  `ctx.schedule_*` / `ctx.join` / `ctx.select2` (not `tokio::*`, `std::time`, `rand`) so
  it is replay-deterministic.
- An **activity** is where side effects happen. Each runs **at most once per logical
  step**; its result is recorded as a durable history event.
- **Replay** is the durability mechanism: on restart the runtime replays the recorded
  history — a completed step returns its recorded result *without re-executing* — and
  resumes from the first unfinished step. Crash anywhere → resume exactly-once.
- Persistence is behind a **`Provider` trait** (storage-agnostic). A **SQLite provider**
  is bundled (in-memory or on-disk, WAL). A PostgreSQL provider ships as the separate
  `duroxide-pg` crate. It runs in-process on tokio — no separate server.

API touched here: `Runtime::start_with_store(store, activities, orchestrations)`,
`Client::{start_orchestration, raise_event, wait_for_orchestration, get_orchestration_status}`,
`OrchestrationContext::{schedule_activity, schedule_wait}`,
`ActivityRegistry`/`OrchestrationRegistry` builders, `providers::sqlite::SqliteProvider`.

### pg_durable — PostgreSQL License

A **PostgreSQL extension** (pgrx `cdylib`) that brings durable execution **inside
Postgres**: you define a workflow in SQL (`df.start(...)`, composable `~>` / `|=>`
operators), and Postgres checkpoints each step into tables like `df.instances`. It
*embeds duroxide + duroxide-pg inside the database* — the durable store is the same
Postgres you keep your data in, with the same auth/backup model and no extra service.

Important consequence for us: pg_durable is **not** an in-process Rust library to depend
on — it is a database extension. So the durable *runtime* dependency for a Rust service
like DreggNet is **duroxide**, with a store provider chosen per deployment. pg_durable is
the **in-database composition target**: run it in the same Postgres as breadstuffs'
`pg-dregg` (dregg-in-Postgres, Tier-C) and the lease, the meter, and the workflow
checkpoints share one transactional boundary.

| library    | what it is                         | license          | role here                          |
|------------|------------------------------------|------------------|------------------------------------|
| duroxide   | Rust durable-execution runtime     | MIT              | **the durable runtime** (dep)      |
| duroxide-pg| Postgres `Provider` for duroxide   | (sibling crate)  | in-process Postgres store (next)   |
| pg_durable | durable execution *inside* Postgres| PostgreSQL Lic.  | in-DB composition w/ pg-dregg (next)|

Both licenses are permissive (MIT, PostgreSQL/BSD-style) — clean for the moat.

## The design: a polyana workload as a durable workflow

A DreggNet durable workload is a duroxide orchestration (`ORCHESTRATION_NAME =
"DreggNetDurableWorkload"`) whose steps are activities that run real polyana workloads:

1. **`RunWorkload`** activity — decodes a `WorkloadSpec { label, lang, source, cap_tier }`,
   runs it through `dreggnet_exec::run_workload` (real wasmi execution on polyana),
   returns the first output value. `run_workload` drives its own current-thread tokio
   runtime, so the activity offloads it via `tokio::task::spawn_blocking` (it is already
   inside duroxide's runtime). The result is a durable history event → replayed, never
   re-run, after a crash.

2. **`MeterTick`** activity — charges `cost_per_step` units against the lease meter for
   this instance and returns the running total. This is the **transactional twin** of the
   work: a step's polyana effect and its meter tick are both durable history events, so on
   replay they are recovered together-or-not. This is the DBOS shape — *durable steps + a
   transactional outbox* — with the duroxide store as the outbox.

The orchestration chains them into a real dependency:

```
step1 = RunWorkload(add(40,2))   → "42"   ;  MeterTick           (budget check)
  └─ [optional park point for crash testing]
step2 = RunWorkload(42 * 2)      → "84"   ;  MeterTick           (budget check)
return { step1, step2, meter_units }
```

step2's WAT embeds step1's durably-recorded result, so the chain is genuine.

### Map to the dregg execution-lease

A funded dregg `execution-lease` authorizes a durable workflow. `WorkflowInput` carries
`budget_units` and `cost_per_step`:

- each step's `MeterTick` accumulates against the budget;
- a tick that would exceed the budget **fails the workflow** — the lease has lapsed, the
  workload is reaped rather than run-and-not-paid;
- because the ticks are durable history, **crash-recovery resumes within the same
  budget** — re-running never double-charges, and a workflow that already exhausted its
  budget stays failed across restarts.

The meter tick currently updates an in-process ledger (`dreggnet_durable::metrics`,
keyed per workflow instance — observable and concurrency-safe). The **bridge-rung step**
is to make the `MeterTick` activity a real dregg `Payable` charge so the meter tick and
the polyana effect commit in one transaction against `pg-dregg`. `MeterTick` is the
single seam where that charge lands — nothing else in the workflow changes.

## Durability boundary (honest)

Durability is exactly the durability of the duroxide `Provider` store.

- **Wired here:** the bundled SQLite provider on an **on-disk** DB. Single-host,
  WAL-durable. It survives **process crash and restart on the same host** — which is
  precisely what the recovery test exercises. It does **not** survive host loss.
- **Multi-region / replicated** durability is a property of a *different store*, not of
  this layer: the `duroxide-pg` Postgres provider (in-process), or `pg_durable` running
  inside a replicated Postgres. Swapping the store changes **no line** of the workflow.
- The exactly-once guarantee is duroxide's replay: a recorded step result is returned, not
  recomputed. The in-process meter *counter* used by the test is process-local (it cannot
  itself survive an OS-level process kill); the **durable store** is what carries the
  checkpoint across the restart, and the test asserts the recorded result is replayed
  rather than the activity re-executed.

## What is proven (the scaffold)

`durable/` (`dreggnet-durable`) with `cargo test -p dreggnet-durable` green:

- **`durable_workflow_resumes_exactly_once_across_a_simulated_crash`** — runs the 2-step
  workflow on polyana over an on-disk SQLite store; parks after step1's checkpoint; tears
  the **entire duroxide runtime down** (the simulated crash); creates a **fresh runtime
  over the same on-disk store** and resumes. Asserts: step1's activity ran **exactly once**
  across the crash (replayed, not re-run), step2 runs once in the second runtime and
  consumes step1's recorded result (`"84"`), and the meter charged **exactly twice**
  (never doubled by the crash).
- **`lease_budget_exhaustion_fails_the_workflow`** — a lease whose budget cannot cover
  both steps fails rather than running unpaid work.

The full DreggNet workspace builds green with the crate added.

## Next steps (named)

1. **Real durable Postgres store** — swap the SQLite provider for `duroxide-pg` so the
   checkpoints live in Postgres (the multi-host/replicated durability boundary). Same
   workflow code.
2. **Real meter wire** — make `MeterTick` a dregg `Payable` charge so the polyana effect
   and the lease meter-tick commit in one transaction; in the `pg-dregg` deployment that
   transaction is the same Postgres transaction as the duroxide checkpoint (true
   together-or-not), and `pg_durable` becomes the in-database composition.
3. **Lease-driven entrypoint** — generalize the fixed 2-step demo to a workflow described
   by the funded lease (workload graph, cap-tier, budget), wired through the bridge rung
   (`dreggnet-bridge`) that watches dregg for funded/active leases.
