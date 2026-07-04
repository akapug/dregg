//! `dreggnet-bridge` — the keystone where a funded dregg execution-lease drives a
//! durable metered workflow.
//!
//! ```text
//!   dregg execution-lease  (the AUTHORIZATION — who, what cap-grade, what budget)
//!     └─ dreggnet-bridge    (THIS crate — map the lease → a tier, fulfill it)
//!        └─ dreggnet-durable (the durable, exactly-once, crash-resumable workflow)
//!           └─ dreggnet-exec (run_workload → the owned wasmi sandbox, at the mapped cap-tier)
//! ```
//!
//! ## What the bridge does (the 5-step lease⟷workload weld)
//!
//! 1. Take a funded dregg [`Lease`] (its lessee, authorized [`CapGrade`], asset,
//!    and `budget_units`).
//! 2. Map the lease's cap-grade → a [`CapTier`] + provider/lang
//!    ([`map_cap_grade`]). The lease's authorized grade picks the sandbox tier; a
//!    workload that demands a stronger floor than the lease authorizes is refused.
//! 3. [`fulfill`] launches the durable [`dreggnet_durable`] workflow over the
//!    mapped tier — each step runs on the owned wasmi sandbox via `dreggnet-exec`, and the
//!    `MeterTick` activity charges `per_period_units` against the lease budget.
//! 4. An over-budget tick **fails the workflow** (lapse → reap): no work runs
//!    beyond what the lease's budget proves was paid for.
//! 5. Because the meter ticks are durable history, crash-recovery **resumes
//!    within the same budget** — the durable layer proves exactly-once metering,
//!    so a crash never double-charges and an exhausted lease stays failed.
//!
//! The honest invariant (ARCHITECTURE.md "The bridge"): **the bridge never lets a
//! workload run beyond what the lease authorizes, and never claims more than the
//! lease budget proves was paid for.**
//!
//! ## Real vs mock (read this)
//!
//! - **Real:** the durable workflow, exactly-once metering, crash-resume, the
//!   owned wasmi execution (the `add(40,2)` / `*2` steps genuinely run in the owned wasmi
//!   sandbox), and the budget gate (an over-budget tick fails the workflow).
//! - **Mock by default:** the [`Lease`] struct mirrors breadstuffs' `LeaseTerms`
//!   (`starbridge-apps/execution-lease` + `sdk/src/service_economy.rs`). On the
//!   default build it is constructed in-process ([`Lease::funded`]). Behind the
//!   `dregg-verify` feature it is **read from a dregg node** — [`watch::DreggNodeFeed`]
//!   attests a node's receipt log and decodes each funded execution-lease grant
//!   (lessee / cap-grade / budget) into a [`Lease`] via [`dregg_verify::read_funded_leases`].
//!   The remaining step is the live light-client RPC that fetches the log records.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use dreggnet_durable::{
    ORCHESTRATION_NAME, ORCHESTRATION_WORKLOAD_RUN, WorkflowInput, WorkflowOutput, WorkloadRun,
    WorkloadSpec, build_registries,
};
use dreggnet_exec::CapTier;
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

// Re-export the durable surface a caller (or the crash-resume proof) needs to
// drive the runtime around a bridge-derived [`WorkflowInput`].
pub use dreggnet_durable::{WorkflowOutput as DurableOutput, metrics};

pub mod dregg_verify;
pub mod watch;

// The lease-watcher surface: the watch→fulfill→reap loop and its feeds.
pub use watch::{
    DreggNodeFeed, FeedItem, Fulfilled, LeaseFeed, LeaseWatcher, MockFeed, MockFeedSender,
    ReapReason, Reaped, WatchReport,
};

/// The cap-grade a dregg execution-lease authorizes — the isolation tier the
/// lessee is allowed to run at. Ordered weakest → strongest isolation, so
/// `grade >= floor` means "this lease may run a workload that demands `floor`".
///
/// This is the lease-side authorization that [`map_cap_grade`] turns into a
/// concrete [`CapTier`] + provider/language chain. It mirrors the
/// grade a real dregg lease cell would carry in its committed state (the
/// breadstuffs `execution-lease` factory's `allowed_cap_templates`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CapGrade {
    /// In-process language sandbox (wasmi / wasmtime / v8 / graal).
    Sandboxed,
    /// Native process under seccomp + landlock.
    Caged,
    /// Hardware-isolated microVM (firecracker).
    MicroVm,
}

impl std::fmt::Display for CapGrade {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CapGrade::Sandboxed => "sandboxed",
            CapGrade::Caged => "caged",
            CapGrade::MicroVm => "microvm",
        };
        f.write_str(s)
    }
}

/// The engine provider + language chain a [`CapGrade`] resolves to: the sandbox
/// tier ([`CapTier`]) the workload runs at, the provider family that enforces it,
/// and the workload language that family accepts at this rung.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TierBinding {
    /// The sandbox tier the workload instantiates at.
    pub tier: CapTier,
    /// The engine provider family that enforces `tier`.
    pub provider: &'static str,
    /// The workload language this provider family accepts at `tier` (the `lang`
    /// `dreggnet_exec::run_workload` routes at that tier: `wat` for wasmi/Sandboxed,
    /// `native` for the OS-sandboxed Caged tier, the guest entrypoint for MicroVm).
    pub lang: &'static str,
}

/// Map a lease's authorized [`CapGrade`] → the [`CapTier`] + provider/lang chain
/// it picks.
///
/// Each grade resolves to the provider family `dreggnet-exec` serves at that
/// tier, and the `lang` is the language that family accepts there (matching
/// `dreggnet-exec`'s own `run_workload` routing — see its module docs):
///   - `Sandboxed` → the OWNED wasmi interpreter, `wat` (the genuinely-executed tier);
///   - `Caged` → the OS-sandboxed native tier, `native` (an honest fail-closed seam
///     in `dreggnet-exec` today — no owned native engine linked);
///   - `MicroVm` → the hardware-isolated microVM tier, lang-agnostic at the boundary
///     (an honest fail-closed seam in `dreggnet-exec` today).
///
/// This binding is what the control plane schedules against (the `tier` picks the
/// [`MachineSpec`] backend) and the floor check below ranks the grade by. The
/// in-process durable workflow the bridge drives today runs every grade at the
/// [`CapTier::Sandboxed`] owned-wasmi floor — a stronger grade satisfies a weaker
/// floor, so a `Caged`/`MicroVm` lease may run the sandboxed durable workload — so
/// this binding's `lang` is NOT itself the dispatch lang for that in-process step
/// (that is hardcoded `wat`@`sandboxed`).
pub fn map_cap_grade(grade: CapGrade) -> TierBinding {
    match grade {
        CapGrade::Sandboxed => TierBinding {
            tier: CapTier::Sandboxed,
            provider: "dreggnet-wasmi",
            lang: "wat",
        },
        CapGrade::Caged => TierBinding {
            tier: CapTier::Caged,
            // The OS-sandboxed native tier (seccomp-bpf + Landlock) — an honest
            // fail-closed seam in dreggnet-exec today. Serves `native`/`bin`, not `wat`.
            provider: "dreggnet-native (seam)",
            lang: "native",
        },
        CapGrade::MicroVm => TierBinding {
            tier: CapTier::MicroVm,
            // The hardware-isolated microVM tier — an honest fail-closed seam in
            // dreggnet-exec today. Lang-agnostic; `lang` names the guest entrypoint.
            provider: "dreggnet-microvm (seam)",
            lang: "wat",
        },
    }
}

/// A dregg execution-lease — the authorization a workload runs under.
///
/// **MOCK** at this rung: a plain struct mirroring breadstuffs' `LeaseTerms`
/// (`starbridge-apps/execution-lease/src/lib.rs` — `provider`/`lease`/`asset`/
/// `rent_per_period`; and `sdk/src/service_economy.rs` — `max_steps`/budget). The
/// real funded lease is a cap-bounded dregg cell whose committed heap holds the
/// budget, the meter ([`StandingObligation`]), and the cap-grade; reading it from
/// a dregg node / light client is the named next sub-step (see [`dregg_verify`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lease {
    /// The lessee — the agent renting durable execution. (Mock: a tag; real: the
    /// dregg lease cell's holder / `CellId`.)
    pub lessee: String,
    /// The isolation tier this lease authorizes.
    pub cap_grade: CapGrade,
    /// The asset the lease budget is denominated in. (Mock: a tag; real: the
    /// dregg lease cell's `token_id`.)
    pub asset: String,
    /// The total metered budget the lease was funded with, in meter units. Each
    /// durable step charges `per_period_units`; a charge that would exceed this
    /// fails the workflow (lapse → reap).
    pub budget_units: i64,
    /// The meter cost charged per durable step (one period). Mirrors breadstuffs'
    /// `rent_per_period`. Must be `> 0`.
    pub per_period_units: i64,
    /// Whether the lease is funded + active. An unfunded lease authorizes NO work
    /// (the bridge refuses to start the workflow at all — truly no unpaid work).
    pub funded: bool,
}

impl Lease {
    /// A funded, active lease for `lessee` at `grade`, funded with `budget_units`
    /// of `asset`, charged `per_period_units` per durable step.
    pub fn funded(
        lessee: impl Into<String>,
        grade: CapGrade,
        asset: impl Into<String>,
        budget_units: i64,
        per_period_units: i64,
    ) -> Lease {
        Lease {
            lessee: lessee.into(),
            cap_grade: grade,
            asset: asset.into(),
            budget_units,
            per_period_units,
            funded: true,
        }
    }

    /// Whether the lease may authorize work right now: funded, with a positive
    /// per-period cost and a non-negative budget.
    pub fn is_active(&self) -> bool {
        self.funded && self.per_period_units > 0 && self.budget_units >= 0
    }

    /// The tier binding this lease's cap-grade resolves to.
    pub fn tier_binding(&self) -> TierBinding {
        map_cap_grade(self.cap_grade)
    }
}

/// Why a fulfillment was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BridgeError {
    /// The lease is not funded/active: it authorizes no work, so the bridge never
    /// starts the workflow (no unpaid work, ever).
    Unfunded { lessee: String },
    /// The lease terms are ill-formed (non-positive per-period cost, negative
    /// budget).
    IllFormed(String),
    /// The lease's authorized cap-grade is below the floor the workload demands:
    /// the bridge refuses rather than silently downgrade isolation.
    GradeBelowFloor { grade: CapGrade, floor: CapTier },
    /// The durable workflow failed — most importantly, an over-budget meter tick
    /// (the lease lapsed → the workload is reaped). The message carries the
    /// duroxide failure detail (e.g. `"execution-lease exhausted after step2"`).
    WorkflowFailed(String),
    /// The durable runtime / store surfaced an error.
    Durable(String),
}

impl std::fmt::Display for BridgeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BridgeError::Unfunded { lessee } => {
                write!(f, "lease for `{lessee}` is not funded: no work authorized")
            }
            BridgeError::IllFormed(why) => write!(f, "ill-formed lease: {why}"),
            BridgeError::GradeBelowFloor { grade, floor } => write!(
                f,
                "lease cap-grade {grade} is below the workload floor {floor:?}"
            ),
            BridgeError::WorkflowFailed(msg) => write!(f, "durable workflow failed: {msg}"),
            BridgeError::Durable(msg) => write!(f, "durable runtime error: {msg}"),
        }
    }
}

impl std::error::Error for BridgeError {}

/// Validate a lease and derive the [`WorkflowInput`] that drives the durable
/// workflow against its budget.
///
/// This is the single gate every fulfillment path runs through (both [`fulfill`]
/// and the crash-resume proof), so the lease check sits on the same path as the
/// durable run:
/// - an unfunded lease is refused ([`BridgeError::Unfunded`]) — no workflow starts;
/// - ill-formed terms are refused;
/// - the lease's cap-grade must meet the floor the workload demands (the durable
///   workload runs at [`CapTier::Sandboxed`]); a lease below that floor is refused;
/// - the lease's `budget_units` + `per_period_units` become the durable workflow's
///   budget + per-step cost, so the `MeterTick` charges against the real lease.
///
/// `pause_event` (when set) is the deterministic park point the crash-resume proof
/// drives — `None` for a straight run-to-completion.
pub fn workflow_input_for_lease(
    lease: &Lease,
    pause_event: Option<String>,
) -> Result<WorkflowInput, BridgeError> {
    if !lease.funded {
        return Err(BridgeError::Unfunded {
            lessee: lease.lessee.clone(),
        });
    }
    if lease.per_period_units <= 0 {
        return Err(BridgeError::IllFormed(format!(
            "per_period_units must be > 0, got {}",
            lease.per_period_units
        )));
    }
    if lease.budget_units < 0 {
        return Err(BridgeError::IllFormed(format!(
            "budget_units must be >= 0, got {}",
            lease.budget_units
        )));
    }

    // The durable workload runs at the Sandboxed floor (wasmi). A lease must
    // authorize at least that grade; a stronger grade satisfies it.
    let floor = CapTier::Sandboxed;
    if lease.tier_binding().tier < floor {
        return Err(BridgeError::GradeBelowFloor {
            grade: lease.cap_grade,
            floor,
        });
    }

    Ok(WorkflowInput {
        budget_units: lease.budget_units,
        cost_per_step: lease.per_period_units,
        pause_event,
    })
}

/// **Fulfill a lease** — launch the durable metered workflow over the lease's
/// mapped tier, metered against the lease budget, and run it to completion.
///
/// Each durable step runs on the owned wasmi sandbox via `dreggnet-exec`; the `MeterTick` charges
/// `per_period_units` against the lease budget. If a tick would exceed
/// `budget_units` the workflow fails ([`BridgeError::WorkflowFailed`] carrying the
/// lapse detail) — no work runs beyond what the lease authorizes. An unfunded
/// lease never starts a workflow ([`BridgeError::Unfunded`]).
///
/// Durability here is in-memory (a fresh, **per-call isolated** duroxide SQLite
/// store) — enough to prove the lease⟷workflow⟷meter weld end to end. The
/// crash-resume guarantee (resume within the same budget) is proved over an on-disk
/// store in the crate's integration test, driving the same [`workflow_input_for_lease`]
/// gate.
///
/// ## Why an on-disk WAL store (the snoopy power-event deadlock)
///
/// duroxide's `SqliteProvider::new_in_memory()` opens `sqlite::memory:?cache=shared`.
/// A **shared-cache in-memory** SQLite database uses **table-level** locking, and
/// duroxide's runtime drives each store with a *pool of connections* (an orchestrator
/// dispatcher and a worker dispatcher, concurrently). Two connections that each hold a
/// read lock and try to upgrade to a write lock **deadlock** — SQLite returns
/// `SQLITE_LOCKED` (code 6, *"database is deadlocked"*), which `PRAGMA busy_timeout`
/// does **not** cover (busy_timeout only retries `SQLITE_BUSY`). duroxide flags it
/// retryable and backs off, so under a burst of concurrent `/fulfill` — exactly what a
/// post-power-event restart produces, with the edge re-dispatching + health checks +
/// retries piling up — the agent drowns in a "database is deadlocked, backing off"
/// retry storm that pegs the runtime and starves its accept loop: it serves nothing
/// despite the bind (the snoopy symptom David reported).
///
/// The fix is to back the store with an **on-disk** SQLite database instead. A file
/// store uses **WAL** journaling (duroxide sets `journal_mode = WAL` for file DBs),
/// where readers never block the writer and writer contention is resolved by
/// `busy_timeout` as `SQLITE_BUSY` (retried-and-*progresses*) rather than a hard
/// `SQLITE_LOCKED` deadlock. Each `fulfill` gets its **own** temp database (a
/// process-unique path), torn down when the call returns (success or error, via the
/// [`StoreDir`] drop guard), so concurrent fulfillments are fully isolated and the
/// durable workflow runs to completion without the deadlock storm.
pub async fn fulfill(lease: &Lease, instance: &str) -> Result<WorkflowOutput, BridgeError> {
    let input = workflow_input_for_lease(lease, None)?;
    let input_json =
        serde_json::to_string(&input).map_err(|e| BridgeError::Durable(e.to_string()))?;
    run_orchestration(ORCHESTRATION_NAME, &input_json, instance).await
}

/// A caller-declared workload to run under a lease — the language + program source
/// the `dreggnet run --source` verb threads through. The program runs as a single
/// durable, exactly-once-metered step on the owned sandbox at the lease's sandbox floor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkloadSource {
    /// The owned-sandbox workload language (`wat`/`wasm` at this rung).
    pub lang: String,
    /// The program source (WAT text for `wat`/`wasm`).
    pub source: String,
}

/// **Fulfill a lease running a CALLER-DECLARED workload** — the `run --source` path.
///
/// Unlike [`fulfill`] (the fixed `add → double` demo), this runs the program the
/// caller actually wrote: it is launched as a single-step durable [`WorkloadRun`]
/// over the same lease gate ([`workflow_input_for_lease`]) and the same per-call
/// on-disk WAL store, charged exactly-once against the lease budget. The step runs
/// at the sandboxed floor (wasmi) — the grade every lease authorizes — so any
/// authorized lease can run a WAT program; an over-budget step lapses the workflow.
pub async fn fulfill_workload(
    lease: &Lease,
    instance: &str,
    workload: &WorkloadSource,
) -> Result<WorkflowOutput, BridgeError> {
    // Validate the lease on the same gate the demo path uses (unfunded / ill-formed /
    // grade-below-floor are refused before any work runs) and derive the budget.
    let input = workflow_input_for_lease(lease, None)?;
    let spec = WorkloadSpec {
        label: "run".to_string(),
        lang: workload.lang.clone(),
        source: workload.source.clone(),
        // The sandboxed floor (wasmi) — the floor every cap-grade satisfies and the
        // only tier `wat` is wired at, mirroring the demo step specs.
        cap_tier: "sandboxed".to_string(),
    };
    let run = WorkloadRun::new(input.budget_units, input.cost_per_step, vec![spec]);
    let run_json = serde_json::to_string(&run).map_err(|e| BridgeError::Durable(e.to_string()))?;
    run_orchestration(ORCHESTRATION_WORKLOAD_RUN, &run_json, instance).await
}

/// Drive one durable orchestration to completion over a per-call on-disk WAL store
/// (the process-unique, drop-cleaned store), returning its [`WorkflowOutput`]. The
/// shared core of [`fulfill`] (the fixed demo) and [`fulfill_workload`] (a
/// caller-declared program) — see the [`fulfill`] doc-comment for *why* the store is
/// on-disk and not the in-memory shared-cache store (the snoopy power-event deadlock).
async fn run_orchestration(
    orchestration: &str,
    input_json: &str,
    instance: &str,
) -> Result<WorkflowOutput, BridgeError> {
    // Per-call on-disk WAL store in a process-unique temp dir. The `StoreDir` guard
    // removes the dir (db + `-wal`/`-shm`) on drop, on every exit path including `?`.
    static STORE_SEQ: AtomicU64 = AtomicU64::new(0);
    let seq = STORE_SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("dn-fulfill-{}-{seq}", std::process::id()));
    std::fs::create_dir_all(&dir)
        .map_err(|e| BridgeError::Durable(format!("create durable store dir: {e}")))?;
    let _store_dir = StoreDir(dir.clone());
    let db_path = dir.join("durable.db");
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());

    let store = Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .map_err(|e| BridgeError::Durable(format!("open durable store: {e}")))?,
    );
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    client
        .start_orchestration(instance, orchestration, input_json.to_string())
        .await
        .map_err(|e| BridgeError::Durable(format!("start orchestration: {e}")))?;

    let status = client
        .wait_for_orchestration(instance, Duration::from_secs(30))
        .await
        .map_err(|e| BridgeError::Durable(format!("await orchestration: {e}")))?;

    let result = match status {
        OrchestrationStatus::Completed { output, .. } => serde_json::from_str(&output)
            .map_err(|e| BridgeError::Durable(format!("decode output: {e}"))),
        OrchestrationStatus::Failed { details, .. } => {
            Err(BridgeError::WorkflowFailed(details.display_message()))
        }
        other => Err(BridgeError::WorkflowFailed(format!("{other:?}"))),
    };

    rt.shutdown(None).await;
    result
}

/// RAII guard: removes a per-`fulfill` temp store directory (the SQLite db plus its
/// `-wal`/`-shm` sidecars) when the fulfillment returns, on every path.
struct StoreDir(std::path::PathBuf);

impl Drop for StoreDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_grade_maps_to_tier_and_provider() {
        let s = map_cap_grade(CapGrade::Sandboxed);
        assert_eq!(s.tier, CapTier::Sandboxed);
        assert_eq!(s.provider, "dreggnet-wasmi");
        assert_eq!(s.lang, "wat");

        assert_eq!(map_cap_grade(CapGrade::Caged).tier, CapTier::Caged);
        assert_eq!(map_cap_grade(CapGrade::MicroVm).tier, CapTier::MicroVm);

        // A stronger grade out-ranks a weaker floor (provider must meet/exceed).
        assert!(CapGrade::MicroVm > CapGrade::Sandboxed);
    }

    #[test]
    fn unfunded_lease_authorizes_no_work() {
        let lease = Lease {
            lessee: "agent-x".into(),
            cap_grade: CapGrade::Sandboxed,
            asset: "USD-test".into(),
            budget_units: 100,
            per_period_units: 1,
            funded: false,
        };
        assert!(!lease.is_active());
        assert!(matches!(
            workflow_input_for_lease(&lease, None),
            Err(BridgeError::Unfunded { lessee }) if lessee == "agent-x"
        ));
    }

    #[test]
    fn ill_formed_per_period_is_refused() {
        let lease = Lease::funded("a", CapGrade::Sandboxed, "USD", 100, 0);
        assert!(matches!(
            workflow_input_for_lease(&lease, None),
            Err(BridgeError::IllFormed(_))
        ));
    }

    #[test]
    fn funded_lease_yields_a_budgeted_workflow_input() {
        let lease = Lease::funded("a", CapGrade::Caged, "USD", 100, 7);
        let input = workflow_input_for_lease(&lease, None).expect("active lease");
        assert_eq!(input.budget_units, 100);
        assert_eq!(input.cost_per_step, 7);
        assert!(input.pause_event.is_none());
    }
}
