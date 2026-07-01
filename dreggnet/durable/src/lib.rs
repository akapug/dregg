//! `dreggnet-durable` — DBOS-style durable, transactional, recoverable workflows
//! over polyana execution.
//!
//! This is the layer BETWEEN the two halves of DreggNet:
//!
//! ```text
//!   dregg (meters / pays / verifies the lease — breadstuffs, AGPL)
//!     └─ dreggnet-durable (THIS crate — durable workflow, exactly-once, crash-resume)
//!        └─ dreggnet-exec  (run_workload → polyana)
//!           └─ polyana     (the sandboxed execution engine)
//! ```
//!
//! ## The model (duroxide / Durable-Task / Temporal lineage)
//!
//! A **workflow** (duroxide *orchestration*) is *deterministic coordination*: it only
//! decides what to do next from results it already has. The *side effects* live in
//! **activities**, which run **at most once per logical step** and whose results are
//! durably checkpointed to a `Provider` store. On restart the runtime **replays** the
//! recorded history: a completed step returns its recorded result *without re-running*,
//! and execution resumes from the first unfinished step. That replay is the durability
//! guarantee — a crash mid-workflow resumes **exactly-once** from the last checkpoint.
//!
//! A DreggNet durable workload is therefore:
//! - a [`WorkflowInput`]-parameterized orchestration ([`ORCHESTRATION_NAME`]) whose
//!   steps are [`ACTIVITY_RUN_WORKLOAD`] activities, each of which runs a real polyana
//!   workload via [`dreggnet_exec::run_workload`];
//! - a [`ACTIVITY_METER_TICK`] activity per step that ticks the lease meter — the
//!   transactional twin of the work: a step's polyana effect and its meter tick are
//!   both durable history events, so they are recovered together-or-not on replay
//!   (the DBOS "durable step + transactional outbox" shape, with the duroxide store as
//!   the outbox).
//!
//! ## Map to the dregg lease
//!
//! A funded dregg `execution-lease` authorizes a durable workflow. [`WorkflowInput`]
//! carries the lease `budget_units`; each step's meter tick accumulates against it, and
//! a tick that would exceed the budget **fails the workflow** (the lease has lapsed →
//! the workload is reaped). Because the meter ticks are durable history, crash-recovery
//! resumes *within the same budget* — re-running never double-charges, and a workflow
//! that already exhausted its budget stays failed across restarts.
//!
//! The meter tick lands in one of two backends ([`MeterBackend`], selected when the
//! registries are built):
//!
//! - **in-process** (default, [`build_registries`]) — a process-local [`metrics`] ledger;
//!   the always-on offline proof runs over it.
//! - **Postgres** (feature `pg`, [`build_registries_with_pg_meter`]) — the
//!   **transactional outbox**: each tick writes a charge row `(lease_id, period, amount,
//!   running_total)` to the `dreggnet_meter` table on the *same `PgPool` duroxide
//!   checkpoints into* (the `duroxide-pg` `PostgresProvider`'s pool). The row is keyed
//!   `PRIMARY KEY (lease_id, period)` and inserted `ON CONFLICT DO NOTHING`, so the charge
//!   is **idempotent**: a crash that re-runs the activity before its completion was
//!   checkpointed never double-writes the row, and a checkpointed step replays its
//!   recorded result without re-charging. That is the DBOS transactional-outbox shape —
//!   charge ⟺ durable step, exactly-once across a crash — realized over the same database
//!   that carries the duroxide checkpoints.
//!
//! ### What is atomic-in-one-transaction, precisely (honest)
//!
//! duroxide's checkpoint is its internal `Provider::ack_orchestration_item` transaction
//! (history append + queue enqueues), run by the *orchestrator* after the *worker* has
//! already run the activity body. The public API does not hand the activity that internal
//! transaction, so the meter write cannot literally share the exact `ack` transaction
//! through `duroxide-pg`. What this layer guarantees instead, and proves:
//!
//! - the charge write is its **own one Postgres transaction** on the shared pool — the
//!   budget-checked `running_total` and the inserted row commit together-or-not;
//! - the charge commit *happens-before* the activity returns the value duroxide then
//!   checkpoints, so a durable checkpoint *implies* a durable charge;
//! - idempotency on `(lease_id, period)` makes the reverse safe: a charge that committed
//!   without its checkpoint is reconciled on replay (the re-run is a no-op insert),
//!   never a second charge.
//!
//! The *literal* single-transaction-with-the-history-append is what `pg_durable` provides
//! by running the duroxide step **inside** Postgres; this outbox is the in-process-runtime
//! twin that shares the same DB, so it composes with breadstuffs' `pg-dregg` (dregg-in-
//! Postgres): a real dregg `Payable` settlement reads the `dreggnet_meter` outbox
//! ([`read_meter_outbox`]) to settle the lease against the charges this layer recorded.
//!
//! ## Map to the dregg lease
//!
//! A funded dregg `execution-lease` authorizes a durable workflow. [`WorkflowInput`]
//! carries the lease `budget_units`; the orchestration gates each step's charge against it
//! **before** scheduling the `MeterTick` — a step whose charge would exceed the budget
//! fails the workflow *before any charge commits* (the lease has lapsed → the workload is
//! reaped, never run-and-not-paid, and no partial charge lands). Because the ticks are
//! durable, crash-recovery resumes within the same budget — re-running never double-charges.
//!
//! ## Durability boundary (honest)
//!
//! Durability is exactly the durability of the `Provider` store. The store wired by the
//! default is the bundled SQLite provider on an on-disk DB: single-host, WAL-durable — it
//! survives process crash and restart on the **same host**, not host loss. Multi-region /
//! replicated durability is a property of a different store (the `duroxide-pg` Postgres
//! provider, or `pg_durable` running inside a replicated Postgres). Swapping the store does
//! not change a line of the workflow.

use anyhow::Result;
use serde::{Deserialize, Serialize};

/// The conserving-move primitive the settlement rail upholds — the kernel
/// `Effect::Transfer` paired-delta law, pointed (in the off-by-default
/// `dregg-conserve` lane) at the substrate's *proven* `dregg_cell::CellState`
/// signed-balance discipline (`recTransfer_balanceSum_conserve`) instead of the
/// hand-rolled `i64` twin the census (#1) named. See [`conserve`] for the design.
pub mod conserve;
pub mod settle;
pub use conserve::{ConservedMove, apply_conserving_transfer};
pub use settle::{ConservingLedger, LeaseCharge, SettleError, SettleReceipt, Settlement};

/// The **pg-dregg-backed verified conserving store** — the durable, verifiable replacement
/// for the in-process [`ConservingLedger`] twin, built on breadstuffs' real `pg-dregg`
/// verified store (the anti-substitution chain tooth `dregg.commit_log` runs). Gated behind
/// the off-by-default `pg-dregg` feature (the AGPL verified-store lane, like
/// `dreggnet-bridge`'s `dregg-verify`). The conserving + exactly-once + crash-resume
/// *semantics* are un-gated here; the real Poseidon2 `ledger_root` + the proof-attested
/// on-chain `Payable` are the S3-gated half (see [`verified::S3_GATED_SEAM`]).
#[cfg(feature = "pg-dregg")]
pub mod verified;
#[cfg(feature = "pg-dregg")]
pub use verified::{
    GENESIS_ROOT, S3_GATED_SEAM, SettledTurn, VerifiedChain, VerifiedConservingStore,
};

/// The orchestration name the durable runtime registers the built-in demo
/// (`add → double`) DreggNet workload under.
pub const ORCHESTRATION_NAME: &str = "DreggNetDurableWorkload";

/// The orchestration name for the **general** workload runner — an arbitrary list of
/// [`WorkloadSpec`] steps ([`WorkloadRun`]) run as durable, exactly-once-metered steps.
pub const ORCHESTRATION_WORKLOAD_RUN: &str = "DreggNetWorkloadRun";

/// The activity that runs one polyana workload step (via [`dreggnet_exec::run_workload`]).
pub const ACTIVITY_RUN_WORKLOAD: &str = "RunWorkload";

/// The activity that ticks the lease meter for one step (the transactional twin of work).
pub const ACTIVITY_METER_TICK: &str = "MeterTick";

/// The Postgres outbox table the `pg`-backed [`MeterTick`](ACTIVITY_METER_TICK) writes
/// each charge into. A dregg `Payable` settlement reads this table (see
/// [`read_meter_outbox`]).
pub const METER_TABLE: &str = "dreggnet_meter";

/// One lease meter charge — the input to the [`MeterTick`](ACTIVITY_METER_TICK) activity.
///
/// `period` is the step ordinal within the lease (1-based); `amount` is the units to debit
/// for this step. The `(lease_id, period)` pair — where `lease_id` is the workflow instance
/// id — is the idempotency key of the outbox row, so a re-run after a crash never charges
/// the same period twice.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct MeterCharge {
    pub period: i64,
    pub amount: i64,
}

/// One polyana workload step: a program to run through `dreggnet-exec`.
///
/// `label` identifies the step in the durable history + meter ledger (e.g. `"step1"`).
/// `lang`/`source` are the polyana provider family + program (WAT text for `wasm`/`wat`).
/// `cap_tier` is the sandbox grade the dregg lease authorizes (`"sandboxed"`/`"caged"`/`"microvm"`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkloadSpec {
    pub label: String,
    pub lang: String,
    pub source: String,
    pub cap_tier: String,
}

impl WorkloadSpec {
    fn tier(&self) -> Result<dreggnet_exec::CapTier, String> {
        Ok(match self.cap_tier.as_str() {
            "sandboxed" => dreggnet_exec::CapTier::Sandboxed,
            "jit" | "jit-sandboxed" | "jitsandboxed" => dreggnet_exec::CapTier::JitSandboxed,
            "caged" => dreggnet_exec::CapTier::Caged,
            "microvm" => dreggnet_exec::CapTier::MicroVm,
            other => return Err(format!("unknown cap_tier `{other}`")),
        })
    }
}

/// The lease-scoped input to the built-in demo durable workflow (the fixed
/// `add → double` chain, [`ORCHESTRATION_NAME`]). The general, arbitrary-workload
/// path uses [`WorkloadRun`] instead.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowInput {
    /// The execution-lease budget, in meter units. Each step ticks `cost_per_step`
    /// against it; a tick that would exceed `budget_units` fails the workflow (lapse → reap).
    pub budget_units: i64,
    /// Meter cost charged per step.
    pub cost_per_step: i64,
    /// If set, the orchestration parks on this external event *after step 1 is durably
    /// checkpointed and metered, but before step 2 runs*. This is the deterministic
    /// crash/pause point the recovery test drives; production runs leave it `None`.
    pub pause_event: Option<String>,
}

impl Default for WorkflowInput {
    fn default() -> Self {
        Self {
            budget_units: 1_000,
            cost_per_step: 1,
            pause_event: None,
        }
    }
}

/// The input to the **general** durable workflow ([`ORCHESTRATION_WORKLOAD_RUN`]): an
/// arbitrary, ordered list of polyana [`WorkloadSpec`] steps, each run as its own durable,
/// checkpointed, exactly-once-metered step.
///
/// This is the parameterized counterpart to the fixed-demo [`WorkflowInput`]. Any polyana
/// workload runs through it — an agent-served web request runs as a one-step `WorkloadRun`,
/// a batch job as an N-step one. Each step charges `cost_per_step` against `budget_units`;
/// a step whose charge would exceed the budget fails the workflow (lease lapse → reap)
/// before that step runs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkloadRun {
    /// The execution-lease budget, in meter units.
    pub budget_units: i64,
    /// Meter cost charged per step.
    pub cost_per_step: i64,
    /// The workload steps to run durably, in order.
    pub steps: Vec<WorkloadSpec>,
    /// Park on `pause_event` after this step ordinal (1-based) is durably checkpointed +
    /// metered, before the next step runs — the deterministic crash/pause point the
    /// recovery proof drives. `None` runs straight through.
    #[serde(default)]
    pub pause_after_step: Option<usize>,
    /// The external event the orchestration parks on at the pause point. Production runs
    /// leave it `None`.
    #[serde(default)]
    pub pause_event: Option<String>,
}

impl WorkloadRun {
    /// A straight run-to-completion of `steps`, charged `cost_per_step` against
    /// `budget_units`. No pause point.
    pub fn new(budget_units: i64, cost_per_step: i64, steps: Vec<WorkloadSpec>) -> Self {
        Self {
            budget_units,
            cost_per_step,
            steps,
            pause_after_step: None,
            pause_event: None,
        }
    }
}

/// The terminal result of a durable workflow.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WorkflowOutput {
    /// The first step's polyana value. The demo path's `add(40, 2)` lands here; the general
    /// path mirrors `outputs[0]` here for back-compat readers.
    #[serde(default)]
    pub step1: String,
    /// The second step's polyana value. The demo path's `step1 * 2` lands here; the general
    /// path mirrors `outputs[1]` here for back-compat readers.
    #[serde(default)]
    pub step2: String,
    /// Each durable step's first output value, in order — the general path's full result.
    #[serde(default)]
    pub outputs: Vec<String>,
    /// Total meter units charged against the lease across the workflow.
    pub meter_units: i64,
}

// ---------------------------------------------------------------------------
// Instrumentation ledger.
//
// Per-(instance, key) counters so callers/tests can observe exactly-once and the meter
// total without re-reading the duroxide store, and so concurrent workflows (and parallel
// tests) never alias. The meter tick lands here today; the dregg `Payable` charge is the
// bridge-rung replacement at this same seam.
// ---------------------------------------------------------------------------

/// Observable counters for the durable layer (per workflow instance).
pub mod metrics {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    fn ledger() -> &'static Mutex<HashMap<(String, String), i64>> {
        static LEDGER: OnceLock<Mutex<HashMap<(String, String), i64>>> = OnceLock::new();
        LEDGER.get_or_init(|| Mutex::new(HashMap::new()))
    }

    pub(crate) fn add(instance: &str, key: &str, delta: i64) -> i64 {
        let mut g = ledger().lock().expect("ledger poisoned");
        let e = g
            .entry((instance.to_string(), key.to_string()))
            .or_insert(0);
        *e += delta;
        *e
    }

    /// Read a counter for a workflow instance (`0` if never touched).
    pub fn get(instance: &str, key: &str) -> i64 {
        let g = ledger().lock().expect("ledger poisoned");
        *g.get(&(instance.to_string(), key.to_string()))
            .unwrap_or(&0)
    }

    /// How many times the `RunWorkload` activity actually executed for a given step label
    /// on this instance. Exactly-once means this stays `1` across a crash + resume.
    pub fn run_calls(instance: &str, label: &str) -> i64 {
        get(instance, &format!("run:{label}"))
    }

    /// The meter units charged against the lease for this instance.
    pub fn meter_units(instance: &str) -> i64 {
        get(instance, "meter_units")
    }
}

// ---------------------------------------------------------------------------
// Meter backend: where a `MeterTick` charge lands.
// ---------------------------------------------------------------------------

/// The meter backend a built workflow charges into.
///
/// Selected once when the registries are built ([`build_registries`] →
/// [`MeterBackend::InProcess`]; [`build_registries_with_pg_meter`] →
/// [`MeterBackend::Postgres`]). The workflow code is identical across backends — only the
/// charge sink changes.
#[derive(Clone)]
enum MeterBackend {
    /// Process-local [`metrics`] ledger. The always-green offline path.
    InProcess,
    /// The Postgres transactional outbox on the shared `duroxide-pg` pool.
    #[cfg(feature = "pg")]
    Postgres(std::sync::Arc<sqlx::PgPool>),
}

impl MeterBackend {
    /// Charge `amount` units for `period` against `lease_id`, returning the running total
    /// after this charge. Idempotent on `(lease_id, period)`: charging the same period
    /// twice (e.g. a crash re-running the activity) returns the already-recorded total
    /// without writing a second charge. `Err` leaves no charge committed.
    async fn charge(&self, lease_id: &str, charge: MeterCharge) -> Result<i64, String> {
        match self {
            MeterBackend::InProcess => {
                // duroxide runs an activity at most once per logical step and replays a
                // checkpointed result without re-running, so no in-process idempotency
                // guard is needed: each period's charge lands exactly once.
                Ok(metrics::add(lease_id, "meter_units", charge.amount))
            }
            #[cfg(feature = "pg")]
            MeterBackend::Postgres(pool) => {
                let total = pg::charge_outbox(pool, lease_id, charge).await?;
                Ok(total)
            }
        }
    }
}

/// The Postgres transactional-outbox meter sink.
#[cfg(feature = "pg")]
pub mod pg {
    use super::{METER_TABLE, MeterCharge};
    use anyhow::Result;
    use serde::{Deserialize, Serialize};
    use sqlx::{PgPool, Row};

    /// One recorded charge row in the [`dreggnet_meter`](METER_TABLE) outbox.
    #[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
    pub struct MeterRow {
        pub lease_id: String,
        pub period: i64,
        pub amount: i64,
        pub running_total: i64,
    }

    /// Create the `dreggnet_meter` outbox table if it does not exist. `duroxide-pg`
    /// migrates its own checkpoint schema on startup; this adds the meter outbox alongside
    /// it in the same database. Idempotent — safe to call on every startup.
    pub async fn ensure_meter_schema(pool: &PgPool) -> Result<()> {
        // `CREATE TABLE IF NOT EXISTS` is not concurrency-safe against the system catalogs:
        // two connections can both pass the existence check and then collide inserting the
        // table's implicit row type into `pg_type`. Serialize creators with a
        // transaction-scoped advisory lock so concurrent callers (e.g. parallel tests) are
        // safe. The lock key is an arbitrary fixed constant for this table.
        let mut tx = pool.begin().await?;
        sqlx::query("SELECT pg_advisory_xact_lock($1)")
            .bind(0x6452_6547_4d54_5230_i64) // "dRegMTR0" — a stable per-table lock key
            .execute(&mut *tx)
            .await?;
        sqlx::query(&format!(
            "CREATE TABLE IF NOT EXISTS {METER_TABLE} (
                 lease_id      TEXT        NOT NULL,
                 period        BIGINT      NOT NULL,
                 amount        BIGINT      NOT NULL,
                 running_total BIGINT      NOT NULL,
                 charged_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
                 PRIMARY KEY (lease_id, period)
             )"
        ))
        .execute(&mut *tx)
        .await?;
        tx.commit().await?;
        Ok(())
    }

    /// Charge one period for a lease into the outbox, in **one Postgres transaction**, and
    /// return the running total after this charge.
    ///
    /// The transaction reads the prior running total, computes the new one, and inserts the
    /// row `ON CONFLICT (lease_id, period) DO NOTHING` — so a re-run of an already-charged
    /// period commits nothing new and returns the recorded total. The budget gate lives in
    /// the orchestration *before* this is scheduled, so an over-budget step never reaches
    /// here and no partial charge can land.
    pub async fn charge_outbox(
        pool: &PgPool,
        lease_id: &str,
        charge: MeterCharge,
    ) -> Result<i64, String> {
        let mut tx = pool
            .begin()
            .await
            .map_err(|e| format!("MeterTick: begin: {e}"))?;

        // Idempotency: if this period is already charged, return its recorded total.
        let existing: Option<i64> = sqlx::query_scalar(&format!(
            "SELECT running_total FROM {METER_TABLE} WHERE lease_id = $1 AND period = $2"
        ))
        .bind(lease_id)
        .bind(charge.period)
        .fetch_optional(&mut *tx)
        .await
        .map_err(|e| format!("MeterTick: select existing: {e}"))?;
        if let Some(total) = existing {
            tx.rollback().await.ok();
            return Ok(total);
        }

        // running_total is monotonic per period, so MAX is the latest total for the lease.
        let prior: i64 = sqlx::query_scalar(&format!(
            "SELECT COALESCE(MAX(running_total), 0) FROM {METER_TABLE} WHERE lease_id = $1"
        ))
        .bind(lease_id)
        .fetch_one(&mut *tx)
        .await
        .map_err(|e| format!("MeterTick: select prior: {e}"))?;
        let running_total = prior + charge.amount;

        sqlx::query(&format!(
            "INSERT INTO {METER_TABLE} (lease_id, period, amount, running_total)
                 VALUES ($1, $2, $3, $4)
             ON CONFLICT (lease_id, period) DO NOTHING"
        ))
        .bind(lease_id)
        .bind(charge.period)
        .bind(charge.amount)
        .bind(running_total)
        .execute(&mut *tx)
        .await
        .map_err(|e| format!("MeterTick: insert charge: {e}"))?;

        tx.commit()
            .await
            .map_err(|e| format!("MeterTick: commit: {e}"))?;

        // Mirror into the in-process observability ledger only on a genuine new charge, so
        // a replayed/idempotent re-run never inflates the observable counter.
        super::metrics::add(lease_id, "meter_units", charge.amount);
        Ok(running_total)
    }

    /// Read the recorded charges for a lease from the outbox, in period order.
    ///
    /// This is the **settlement wire**: a real dregg `Payable` settlement (breadstuffs'
    /// `pg-dregg`, in the same database) reads these rows to settle the lease against the
    /// charges this durable layer committed.
    pub async fn read_meter_outbox(pool: &PgPool, lease_id: &str) -> Result<Vec<MeterRow>> {
        let rows = sqlx::query(&format!(
            "SELECT lease_id, period, amount, running_total
                 FROM {METER_TABLE} WHERE lease_id = $1 ORDER BY period"
        ))
        .bind(lease_id)
        .fetch_all(pool)
        .await?;
        Ok(rows
            .into_iter()
            .map(|r| MeterRow {
                lease_id: r.get("lease_id"),
                period: r.get("period"),
                amount: r.get("amount"),
                running_total: r.get("running_total"),
            })
            .collect())
    }
}

#[cfg(feature = "pg")]
pub use pg::{MeterRow, ensure_meter_schema, read_meter_outbox};

/// The synchronous core of a workload step: run it through polyana, return its first
/// output value. Shared by the activity and available for direct (non-durable) callers.
pub fn run_workload_step(spec: &WorkloadSpec) -> Result<String> {
    let tier = spec.tier().map_err(|e| anyhow::anyhow!(e))?;
    let out = dreggnet_exec::run_workload(&spec.lang, &spec.source, tier)?;
    out.values
        .into_iter()
        .next()
        .ok_or_else(|| anyhow::anyhow!("workload step `{}` returned no values", spec.label))
}

/// Build a WAT module that computes `add(40, 2)` and exports it as `run` — workflow step 1.
pub fn step1_add_spec() -> WorkloadSpec {
    WorkloadSpec {
        label: "step1".to_string(),
        lang: "wat".to_string(),
        source: r#"
            (module
              (func $add (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add)
              (func (export "run") (result i32)
                (call $add (i32.const 40) (i32.const 2))))
        "#
        .to_string(),
        cap_tier: "sandboxed".to_string(),
    }
}

/// Build a WAT module that USES step 1's result `v` (doubles it) — workflow step 2.
///
/// The constant is `v`, embedded from the durably-recorded step-1 result, so step 2 is
/// genuinely a function of step 1's output (the workflow is a real dependency chain).
pub fn step2_double_spec(v: i32) -> WorkloadSpec {
    WorkloadSpec {
        label: "step2".to_string(),
        lang: "wat".to_string(),
        source: format!(
            r#"
            (module
              (func (export "run") (result i32)
                (i32.mul (i32.const {v}) (i32.const 2))))
        "#
        ),
        cap_tier: "sandboxed".to_string(),
    }
}

/// Build the duroxide registries (activities + orchestration) for the DreggNet durable
/// workload, charging the meter into the **in-process** ledger ([`MeterBackend::InProcess`]).
/// This is the always-green offline path. Register these with a `duroxide` runtime over any
/// `Provider` store.
pub fn build_registries() -> (
    duroxide::runtime::registry::ActivityRegistry,
    duroxide::OrchestrationRegistry,
) {
    build_with_backend(MeterBackend::InProcess)
}

/// Build the registries with the **Postgres transactional outbox** as the meter backend:
/// each `MeterTick` charge is written to the [`dreggnet_meter`](METER_TABLE) table on the
/// same `PgPool` the `duroxide-pg` `PostgresProvider` checkpoints into. Call
/// [`ensure_meter_schema`] once on the pool before starting the runtime.
///
/// ```no_run
/// # async fn ex(store: std::sync::Arc<duroxide_pg::PostgresProvider>) -> anyhow::Result<()> {
/// use std::sync::Arc;
/// dreggnet_durable::ensure_meter_schema(store.pool()).await?;
/// let pool = Arc::new(store.pool().clone());
/// let (activities, orchestrations) = dreggnet_durable::build_registries_with_pg_meter(pool);
/// # let _ = (activities, orchestrations); Ok(())
/// # }
/// ```
#[cfg(feature = "pg")]
pub fn build_registries_with_pg_meter(
    pool: std::sync::Arc<sqlx::PgPool>,
) -> (
    duroxide::runtime::registry::ActivityRegistry,
    duroxide::OrchestrationRegistry,
) {
    build_with_backend(MeterBackend::Postgres(pool))
}

fn build_with_backend(
    backend: MeterBackend,
) -> (
    duroxide::runtime::registry::ActivityRegistry,
    duroxide::OrchestrationRegistry,
) {
    use duroxide::runtime::registry::ActivityRegistry;
    use duroxide::{OrchestrationContext, OrchestrationRegistry};

    let activities = ActivityRegistry::builder()
        // RunWorkload: decode a WorkloadSpec, run it on polyana, return the first value.
        // `run_workload` drives its own current-thread runtime, so we offload it to a
        // blocking thread (we are already inside duroxide's tokio runtime here).
        .register(
            ACTIVITY_RUN_WORKLOAD,
            |ctx: duroxide::ActivityContext, input: String| async move {
                let instance = ctx.instance_id().to_string();
                let spec: WorkloadSpec = serde_json::from_str(&input)
                    .map_err(|e| format!("RunWorkload: bad spec: {e}"))?;
                let label = spec.label.clone();
                let value = tokio::task::spawn_blocking(move || run_workload_step(&spec))
                    .await
                    .map_err(|e| format!("RunWorkload: join error: {e}"))?
                    .map_err(|e| format!("RunWorkload: {e}"))?;
                // Count the REAL execution (not the replayed return) so exactly-once is observable.
                metrics::add(&instance, &format!("run:{label}"), 1);
                Ok(value)
            },
        )
        // MeterTick: charge `amount` units for `period` against this lease (= the workflow
        // instance), returning the running total. The single seam where the charge lands —
        // either the in-process ledger or the Postgres outbox (the dregg `Payable` charge).
        .register(
            ACTIVITY_METER_TICK,
            move |ctx: duroxide::ActivityContext, input: String| {
                let backend = backend.clone();
                async move {
                    let lease_id = ctx.instance_id().to_string();
                    let charge: MeterCharge = serde_json::from_str(&input)
                        .map_err(|e| format!("MeterTick: bad charge: {e}"))?;
                    let total = backend.charge(&lease_id, charge).await?;
                    Ok(total.to_string())
                }
            },
        )
        .build();

    let orchestrations = OrchestrationRegistry::builder()
        // The general workload runner: an ARBITRARY list of WorkloadSpec steps run
        // durably. Each step gates its charge BEFORE running (an exhausted lease reaps the
        // step rather than running-and-not-paying), runs on polyana, then meters — so every
        // step is its own checkpointed, exactly-once, metered durable unit. This is the path
        // an agent-served web request runs through.
        .register(ORCHESTRATION_WORKLOAD_RUN, |ctx: OrchestrationContext, input: String| async move {
            let cfg: WorkloadRun =
                serde_json::from_str(&input).map_err(|e| format!("bad WorkloadRun: {e}"))?;

            let mut total: i64 = 0;
            let mut outputs: Vec<String> = Vec::with_capacity(cfg.steps.len());
            for (i, spec) in cfg.steps.iter().enumerate() {
                let period = (i as i64) + 1;
                // The lease-budget ceiling decision is the shared replenishing-budget
                // core (`lease_budget_admits`) — the same one the control-plane uptime
                // meter uses, instead of a hand-rolled `projected > budget`. Pure /
                // deterministic, so it is replay-safe inside the orchestration.
                if !dreggnet_exec::budget::lease_budget_admits(
                    cfg.budget_units,
                    cfg.cost_per_step,
                    period,
                ) {
                    let projected = total + cfg.cost_per_step;
                    return Err(format!(
                        "execution-lease exhausted: step {period} charge would reach \
                         {projected} > budget {}",
                        cfg.budget_units
                    ));
                }
                let spec_json = serde_json::to_string(spec).map_err(|e| e.to_string())?;
                let value = ctx.schedule_activity(ACTIVITY_RUN_WORKLOAD, spec_json).await?;

                let charge = serde_json::to_string(&MeterCharge { period, amount: cfg.cost_per_step })
                    .map_err(|e| e.to_string())?;
                total = ctx
                    .schedule_activity(ACTIVITY_METER_TICK, charge)
                    .await?
                    .parse()
                    .map_err(|e| format!("meter total: {e}"))?;
                outputs.push(value);

                // Deterministic crash/pause point (recovery proof only): park after this
                // step is durably checkpointed + metered, before the next step runs.
                if cfg.pause_after_step == Some(period as usize) {
                    if let Some(ev) = cfg.pause_event.as_ref() {
                        let _ = ctx.schedule_wait(ev).await;
                    }
                }
            }
            let out = WorkflowOutput {
                step1: outputs.first().cloned().unwrap_or_default(),
                step2: outputs.get(1).cloned().unwrap_or_default(),
                outputs,
                meter_units: total,
            };
            serde_json::to_string(&out).map_err(|e| e.to_string())
        })
        .register(ORCHESTRATION_NAME, |ctx: OrchestrationContext, input: String| async move {
            let cfg: WorkflowInput =
                serde_json::from_str(&input).map_err(|e| format!("bad WorkflowInput: {e}"))?;

            // --- Built-in demo path: the fixed add → double chain. ---
            // --- Step 1: run add(40,2) on polyana, then meter it. ---
            // Gate the charge BEFORE it commits: the lease scope starts at 0 (lease_id =
            // this instance), so step1's projected total is exactly `cost_per_step`.
            let step1_spec = serde_json::to_string(&step1_add_spec()).map_err(|e| e.to_string())?;
            let step1 = ctx.schedule_activity(ACTIVITY_RUN_WORKLOAD, step1_spec).await?;

            if cfg.cost_per_step > cfg.budget_units {
                return Err(format!(
                    "execution-lease exhausted: step1 charge {} > budget {}",
                    cfg.cost_per_step, cfg.budget_units
                ));
            }
            let charge1 = serde_json::to_string(&MeterCharge { period: 1, amount: cfg.cost_per_step })
                .map_err(|e| e.to_string())?;
            let total1: i64 = ctx
                .schedule_activity(ACTIVITY_METER_TICK, charge1)
                .await?
                .parse()
                .map_err(|e| format!("meter total: {e}"))?;

            // --- Crash/pause point: park until the external event (recovery test only). ---
            if let Some(ev) = cfg.pause_event.as_ref() {
                let _ = ctx.schedule_wait(ev).await;
            }

            // --- Step 2: gate its charge BEFORE running the work or charging, so an
            // exhausted lease reaps the step rather than running-and-not-paying. ---
            let projected2 = total1 + cfg.cost_per_step;
            if projected2 > cfg.budget_units {
                return Err(format!(
                    "execution-lease exhausted: step2 charge would reach {projected2} > budget {}",
                    cfg.budget_units
                ));
            }
            let v: i32 = step1.trim().parse().map_err(|e| format!("step1 not an i32: {e}"))?;
            let step2_spec = serde_json::to_string(&step2_double_spec(v)).map_err(|e| e.to_string())?;
            let step2 = ctx.schedule_activity(ACTIVITY_RUN_WORKLOAD, step2_spec).await?;

            let charge2 = serde_json::to_string(&MeterCharge { period: 2, amount: cfg.cost_per_step })
                .map_err(|e| e.to_string())?;
            let total2: i64 = ctx
                .schedule_activity(ACTIVITY_METER_TICK, charge2)
                .await?
                .parse()
                .map_err(|e| format!("meter total: {e}"))?;

            let out = WorkflowOutput {
                outputs: vec![step1.clone(), step2.clone()],
                step1,
                step2,
                meter_units: total2,
            };
            serde_json::to_string(&out).map_err(|e| e.to_string())
        })
        .build();

    (activities, orchestrations)
}

// ---------------------------------------------------------------------------
// One-shot durable runners.
//
// Spin up a duroxide runtime over a store, run one workflow instance to completion, and
// return its [`WorkflowOutput`]. This is the seam an upstream data plane drives to run a
// single request as a durable, exactly-once-metered workflow without itself depending on
// duroxide. Two stores: the in-memory variant (a throwaway proof of the weld) and the
// on-disk variant ([`run_workflow_on_disk_blocking`], below) the `dreggnet-webapp`
// `LeasedRouter` uses per request — persistent, so an in-flight request survives a crash.
// ---------------------------------------------------------------------------

/// Run a [`WorkloadRun`] to completion over an **in-memory** SQLite durable store, blocking
/// the caller until it finishes, and return its [`WorkflowOutput`].
///
/// This drives its own current-thread tokio runtime, so a synchronous, tokio-free caller can
/// run a request as a real durable workflow: the steps run on polyana, each is checkpointed,
/// and the `MeterTick` charges exactly-once. An over-budget step fails the workflow (the lease
/// lapse → reap), surfaced here as `Err`.
///
/// The store is process-local and in-memory — it proves the request→durable→metered weld end
/// to end but does NOT survive the process. For the persistent serving path (and the
/// crash-resume-across-a-real-restart guarantee) use [`run_workflow_on_disk_blocking`].
///
/// Must NOT be called from inside an existing tokio runtime (it builds its own).
#[cfg(feature = "sqlite")]
pub fn run_workflow_in_memory_blocking(
    input: &WorkloadRun,
    instance: &str,
) -> Result<WorkflowOutput, String> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("durable: tokio runtime build failed: {e}"))?;
    rt.block_on(run_workflow_in_memory(input, instance))
}

/// The async core of [`run_workflow_in_memory_blocking`]: open a fresh in-memory SQLite
/// store, run `input` as instance `instance` to completion, and return its output.
#[cfg(feature = "sqlite")]
pub async fn run_workflow_in_memory(
    input: &WorkloadRun,
    instance: &str,
) -> Result<WorkflowOutput, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};
    use std::sync::Arc;
    use std::time::Duration;

    let store = Arc::new(
        SqliteProvider::new_in_memory()
            .await
            .map_err(|e| format!("durable: open in-memory store: {e}"))?,
    );
    let input_json = serde_json::to_string(input).map_err(|e| e.to_string())?;
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let result = async {
        client
            .start_orchestration(instance, ORCHESTRATION_WORKLOAD_RUN, input_json)
            .await
            .map_err(|e| format!("durable: start orchestration: {e}"))?;
        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(30))
            .await
            .map_err(|e| format!("durable: await orchestration: {e}"))?;
        match status {
            OrchestrationStatus::Completed { output, .. } => {
                serde_json::from_str(&output).map_err(|e| format!("durable: decode output: {e}"))
            }
            OrchestrationStatus::Failed { details, .. } => Err(details.display_message()),
            other => Err(format!("durable: unexpected status: {other:?}")),
        }
    }
    .await;

    rt.shutdown(None).await;
    result
}

/// Run a [`WorkloadRun`] to completion over an **on-disk** SQLite durable store at
/// `db_path`, blocking the caller until it finishes, and return its [`WorkflowOutput`].
///
/// This is the persistent twin of [`run_workflow_in_memory_blocking`]: the workflow's
/// checkpoints (and, with the in-process meter, the recorded charges) are written to
/// `db_path` rather than to a process-local in-memory store. The consequence is the
/// stronger guarantee — if the **process** crashes mid-workflow, the instance survives on
/// disk and a fresh process can resume it from the last checkpoint, exactly-once: a
/// completed step's recorded result is replayed (never re-executed) and the meter is never
/// double-charged. (The in-memory store is lost on a process exit; this one is not.)
///
/// `db_path`'s parent directory is created if needed. The store is single-host, WAL-durable
/// SQLite — it survives process crash + restart on the **same host**, not host loss (that is
/// the Postgres store's boundary; see the crate-level docs). Multiple distinct instances may
/// share one `db_path`; the recovery path on a fresh process is to attach a runtime to the
/// same `db_path` (the runtime auto-resumes any incomplete instance) and await it — this
/// function does exactly that when called with an `instance` already present in the store.
///
/// Must NOT be called from inside an existing tokio runtime (it builds its own).
#[cfg(feature = "sqlite")]
pub fn run_workflow_on_disk_blocking(
    input: &WorkloadRun,
    instance: &str,
    db_path: &std::path::Path,
) -> Result<WorkflowOutput, String> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("durable: tokio runtime build failed: {e}"))?;
    rt.block_on(run_workflow_on_disk(input, instance, db_path))
}

/// The async core of [`run_workflow_on_disk_blocking`]: open (or create) the on-disk SQLite
/// store at `db_path`, run `input` as instance `instance` to completion, and return its
/// output.
///
/// If `instance` is **not yet** in the store this starts it; if it **is** present (a crashed
/// request being recovered on a fresh process), it does not re-start — the runtime attached
/// here auto-resumes the in-flight instance and this call simply awaits its completion. That
/// makes the function safe to call as both the first run *and* the post-crash recovery of the
/// same request.
#[cfg(feature = "sqlite")]
pub async fn run_workflow_on_disk(
    input: &WorkloadRun,
    instance: &str,
    db_path: &std::path::Path,
) -> Result<WorkflowOutput, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};
    use std::sync::Arc;
    use std::time::Duration;

    if let Some(parent) = db_path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .map_err(|e| format!("durable: create store dir {}: {e}", parent.display()))?;
        }
    }
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());
    let store = Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .map_err(|e| format!("durable: open on-disk store {}: {e}", db_path.display()))?,
    );
    let input_json = serde_json::to_string(input).map_err(|e| e.to_string())?;
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let result = async {
        // Start only if this instance is not already on disk. A present instance is a
        // request that crashed mid-flight; the runtime started above auto-resumes it, so we
        // must NOT re-start (that would reject) — just await its completion.
        let present = matches!(
            client.get_orchestration_status(instance).await,
            Ok(s) if !matches!(s, OrchestrationStatus::NotFound)
        );
        if !present {
            client
                .start_orchestration(instance, ORCHESTRATION_WORKLOAD_RUN, input_json)
                .await
                .map_err(|e| format!("durable: start orchestration: {e}"))?;
        }
        // On-disk SQLite serializes writers; under concurrent load duroxide backs off and
        // retries locked writes (its own `busy_timeout` is 60s). Wait that long to match, so
        // a contended-but-progressing workflow is not declared failed prematurely.
        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(60))
            .await
            .map_err(|e| format!("durable: await orchestration: {e}"))?;
        match status {
            OrchestrationStatus::Completed { output, .. } => {
                serde_json::from_str(&output).map_err(|e| format!("durable: decode output: {e}"))
            }
            OrchestrationStatus::Failed { details, .. } => Err(details.display_message()),
            other => Err(format!("durable: unexpected status: {other:?}")),
        }
    }
    .await;

    rt.shutdown(None).await;
    result
}
