# Execution models — the model-space, not a fixed paradigm list

DreggNet runs several *kinds* of workload: a request-scoped lease, a persistent
server, a deploy, an agent loop, an autonomous orchestrator. The question this
document answers is whether those are a **fixed menu of paradigms** (each its own
hand-written code path) or **points in one declarable space** (each a value over
shared primitives). A substrate should be the latter: an arbitrary execution
model expressed as a *declaration*, so a new model is data, not a new subsystem.

This is now made explicit. The descriptor lives in
[`exec/src/model.rs`](../exec/src/model.rs) (`dreggnet_exec::model::ExecutionModel`);
the five existing paths are recovered as named points and three new models drop in
as declarations that run over the same meter, proven by the tests in that file.

## The space

An execution model is four orthogonal choices:

```
ExecutionModel  =  lifecycle  ×  funding  ×  authority  ×  trigger
```

| Axis          | Variants                                                                              | The primitive it lowers to |
|---------------|---------------------------------------------------------------------------------------|----------------------------|
| **lifecycle** | run-to-completion · persistent-served · scheduled · streaming · reactive               | the run loop (how often it draws) |
| **funding**   | prepaid · metered · refilling · escrow-bonded                                          | **one** `BudgetTerms` → `ReplenishingBudget` cell, drawn through the one `Meter` |
| **authority** | cap-grade (sandboxed/caged/microvm) · cap-bundle (`dga1_` powerbox, attenuable)        | `webauth` credential / the polyana tier |
| **trigger**   | invoke · push-deploy · cron · event · agent-brain · watch                              | the entry that starts a run |

The load-bearing fact is the **funding** column: every funding variant lowers to a
single `BudgetTerms` (`Funding::terms()`), so the funding axis is genuinely one
verified primitive parameterized four ways — not four metering mechanisms. The
budget cell is the seL4-MCS replenishing-budget shape
([`exec/src/budget.rs`](../exec/src/budget.rs)) drawn through the unified `Meter`
trait ([`exec/src/meter.rs`](../exec/src/meter.rs)), which is forge-detectable,
exactly-once, and attenuable.

## The five existing paths, as points

Each existing path is recovered by a constructor on `ExecutionModel`. The point is
not the constructor — it is that each path's *funding* lowers to the same cell, so
they already live in one space along that axis.

| Path | File | lifecycle | funding | authority | trigger |
|------|------|-----------|---------|-----------|---------|
| **lease** (request-scoped) | [`control/src/scheduler.rs:145`](../control/src/scheduler.rs) `Scheduler::place_workload` | run-to-completion | prepaid (`Lease.budget_units`) | cap-grade (`Lease.cap_grade`) | invoke |
| **persistent server** | [`control/src/server.rs:1`](../control/src/server.rs) `ServerFleet` | persistent-served | metered per **uptime period** | cap-grade | invoke (create/launch) |
| **deploy** | [`dregg-deploy/src/workflow.rs:383`](../dregg-deploy/src/workflow.rs) `ORCH_DEPLOY` | run-to-completion (clone→build→publish) | prepaid (`DeploySpec.budget_units`) | cap-bundle (`deploy`) | push-deploy |
| **agent** | [`exec/src/agent.rs:704`](../exec/src/agent.rs) `AgentCloud::run` | run-to-completion | **refilling** (`ReplenishingBudget` cell) | cap-bundle (`dga1_`) | agent-brain |
| **orchestrated** | [`control/src/orchestrator.rs:174`](../control/src/orchestrator.rs) `Orchestrator::tick` | run-to-completion (per dispatch) | metered per period | cap-grade | watch |

Constructors: `ExecutionModel::lease`, `::persistent_server`, `::deploy`,
`::agent`, `::orchestrated`.

## The three new models, as declarations

These were never written as code paths. Each is a declaration over the existing
primitives; each runs over the same `ReplenishingMeter`, proven by a test in
[`exec/src/model.rs`](../exec/src/model.rs). They drop in cheap — which is the
flexibility, demonstrated rather than asserted.

### 1. Cron / scheduled

```rust
let cron = ExecutionModel::cron("nightly", "DREGG", /*budget*/ 30, /*every_blocks*/ 86_400, "caged");
//  lifecycle = Scheduled { every_blocks }   funding = Metered { period = every_blocks }
//  authority = cap-grade                     trigger  = Cron { schedule_blocks }
```

A firing is just `charge_run` at the schedule block. A well-funded schedule (one
chunk refilled per window) runs every firing; an underfunded one throttles to its
per-window budget. Exactly-once per firing ordinal, so a retried schedule tick
charges nothing.
**Verdict: drops in cheap.** The replenishing budget's `period` already *is* a
schedule; cron is that period surfaced as a lifecycle. Tests:
`cron_fires_on_schedule_and_each_run_is_metered_exactly_once`,
`an_underfunded_cron_throttles_to_its_window_budget`.

### 2. Streaming / long-lived

```rust
let stream = ExecutionModel::streaming("feed",
    BudgetTerms::new("DREGG", /*budget*/ 10, /*period*/ 1000, /*refill*/ 10, /*refill_max*/ 1, /*start*/ 0),
    vec!["invoke:emit".into()]);
//  lifecycle = Streaming   funding = Refilling { terms }   trigger = invoke
```

A long life is many draws against a refilling budget. When a burst exhausts the
window the stream is **throttled** (an in-band `402`), not killed — and it
**resumes** when the refill matures. That throttle-then-resume is exactly what
distinguishes a streaming lifecycle from a run-to-completion one, and it falls out
of the budget cell's lazy refill with no new mechanism.
**Verdict: drops in cheap.** Test:
`a_streaming_workload_is_throttled_then_resumes_as_the_budget_refills`.

### 3. Escrow-bonded compute market

```rust
let job = ExecutionModel::escrow_bonded("render-job", "DREGG", /*bond*/ 100, "buyer", "worker", caps);
//  funding = EscrowBonded { bond, payer, worker }   lifecycle = run-to-completion
let settlement = settle_escrow(&job, &meter, "escrow:render-job", at_block, verified_ok)?;
```

A party hires the run; the payer bonds the price up front. The run executes as a
genuine receipted agent run, and its **verified verdict** (`verify_agent_run` on
the receipt chain) decides the payout: a verified-ok result **releases** the bond
to the worker (a real committed draw from the escrow cell); a failed/forged result
**refunds** it (the bond is left undrawn, the payer keeps full headroom). Release
is exactly-once, so a bond cannot be double-paid. This composes three existing
primitives — the budget cell (the bond), the model's authority (who may hire), and
the receipt-chain verdict (did the work verify) — into the market payout.
**Verdict: drops in cheap.** Tests:
`an_escrow_bond_is_released_on_a_verified_result`,
`an_escrow_bond_is_refunded_when_the_result_does_not_verify`,
`escrow_cannot_double_release_a_bond`.

## Are we thinking flexibly enough? The honest answer

**The primitives are flexible.** The replenishing-budget `Meter`, the `dga1_` cap
bundle, the receipt chain, and the cap-tiered workload-run are genuinely
composable: three execution models that were never coded fall out as declarations
that run over them, with no new mechanism. Along the funding axis the space is
real — one verified cell under every model.

**The existing paths do not yet share one descriptor — this is the named seam.**
The flexibility lives in the primitives, but the five existing paths were each
written as bespoke code with their own lifecycle state-machine and their own
funding call site:

- **Three separate lifecycle enums** encode the same axis:
  `scheduler::WorkloadState` (Running/Completed/Lapsed/Reaped),
  `server::ServerState` (Created/Running/Stopped/Lapsed/Destroyed),
  `orchestrator::WorkloadState` (Running/Settled/Lapsed/Unplaced/SettleFailed).
- **Funding's headroom decision is now ONE verified primitive across the in-process
  paths.** The unification named in [`exec/src/meter.rs`](../exec/src/meter.rs) ("the
  control plane re-implemented metering 5–6×; `Meter` collapses that to ONE interface
  over ONE verified primitive") is now done for every path whose meter lives in-process:
  - the **agent** path draws against the verified `ReplenishingBudget`/`Meter`;
  - the **server** routes both its bring-up pre-pay (SRV-4) and per-period ceiling
    decision through `lease_budget_admits` → `BudgetState::check_draw` (the `Settlement`
    sink stays — `Meter` is its source twin — but the headroom call is verified);
  - the **deploy** path's hand-rolled `gate()` + **process-local, non-verified** counter
    are *gone*: each step draws against the one verified cell through the `Meter` trait
    (exactly-once per `(instance, period)`, fail-closed) and the gate routes through
    `prepaid_ceiling_admits` → `check_draw`. `meter::units` reads the verified cell's
    drawn total; no side-counter survives in the funding path.

  The scheduler/orchestrator meter *through the bridge*'s durable workflow (`MeterTick` +
  `dreggnet_durable::Settlement`), which is the bridge's own verified rail — out of this
  crate's scope; their headroom is the bridge's concern, not a fourth re-implementation here.

So the answer to "are we boxing into fixed lease/deploy paradigms" is: **no in the
primitives, and increasingly no in the paths.** The substrate can already *express*
arbitrary models (this descriptor + the three new ones prove it), the funding axis is
now one verified decision across the in-process paths, and the deploy + agent paths
*consume* the descriptor (sourcing their funding / recovering as exact points). The
three new models are real, receipted entry points, not demos. The one remaining shared
structure is the **three lifecycle enums** — the documented last step.

## The refactor toward the abstraction (the burn-down)

`ExecutionModel` is the shared vocabulary the paths migrate onto. The tractable,
green sequence — each step independently shippable, none requiring a VK/kernel
change:

1. **Done.** Land `ExecutionModel` (the descriptor) + `Funding::terms()` (the one
   lowering) + the three new models running over `ReplenishingMeter`. The existing
   five are recovered as points (constructors), proving they are one space along the
   funding axis.
2. **Done.** Collapse the funding *headroom decision* onto the verified `Meter` /
   `check_draw`. The deploy path's process-local non-verified counter is gone — each
   step draws against the one verified cell through the `Meter` trait, and the gate
   routes through `prepaid_ceiling_admits`; the server already routes bring-up + every
   uptime period through `lease_budget_admits`; the agent path draws the verified cell.
   The `Settlement` sink stays — `Meter` is its source twin. (The scheduler/orchestrator
   meter through the bridge's own verified rail, out of scope here.)
3. **The remaining documented step.** Collapse the three lifecycle enums
   (`scheduler::WorkloadState`, `server::ServerState`, `orchestrator::WorkloadState`)
   onto one `Lifecycle`-driven run-tracker parameterized by `ExecutionModel.lifecycle`.
   This is the one invasive structural merge left; it is deliberately *not* bundled with
   the funding collapse, to keep each change green and reviewable.
4. **Largely done.** Make the paths take / recover an `ExecutionModel`. The deploy path
   sources its funding from `DeploySpec::execution_model()`; the agent path recovers
   exactly as `AgentSpec::execution_model()`; the server is recovered by
   `ExecutionModel::persistent_server` over its already-verified funding core. The three
   new models — **cron**, **streaming**, **escrow-bonded** — are first-class CLI verbs
   (`dregg-cloud model {cron,stream,escrow,run <json>}`) producing a receipted `ModelRun`
   over the unified meter, and a model loaded from JSON runs the same way (the model is
   data). The full driving of each existing path's *lifecycle* off the descriptor lands
   with step 3 (the enum merge).

This file is the map; steps 1, 2, and 4 are landed, and step 3 (the lifecycle-enum
merge) is the single remaining structural step.
