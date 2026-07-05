//! # dreggnet-workload — the workload-simulation test harness
//!
//! A harness that drives the REAL DreggNet surfaces — the `Orchestrator` loop, the
//! `ConservingLedger` settlement rail, the durable layer, and `run_workload` —
//! under realistic multi-tenant, concurrent, fault-injected, sustained load, and
//! measures what happens (throughput, latency, finality, economy conservation,
//! resource use).
//!
//! Plan + scope: `docs/WORKLOAD-TEST-PLAN.md`. The six scenario classes live as
//! `#[ignore]`d skeletons under `tests/` — an overnight run fills the bodies in and
//! runs them (`make test-workload`). This crate is a workspace member (so
//! `cargo build`/`cargo check` keep it green) but is NOT in the `make test`
//! service-crate set, so the gauntlet never runs it.
//!
//! ## Shape
//!
//! ```ignore
//! let profile = LoadProfile::default().with_env_overrides();
//! let sim = Simulator::new(profile).await;
//! let report = sim.run("scale_load").await;
//! report.print_table();
//! assert!(!report.has_failure());          // the §3 invariants held
//! ```
//!
//! A scenario implements [`Scenario`]: it declares the [`LoadProfile`] it drives
//! and (optionally) a [`FaultPlan`], runs the simulator, and `check`s the SLO +
//! invariant table.

pub mod backends;
pub mod faults;
pub mod metrics;
pub mod profile;
pub mod report;
pub mod simulator;
pub mod tenant;

pub use faults::{Fault, FaultPlan};
pub use metrics::{LeaseEvent, MetricSnapshot, Metrics, ResourceSample};
pub use profile::{Arrival, BudgetModel, LoadProfile, RunBound, TierMix};
pub use report::{RunReport, SloResult};
pub use simulator::Simulator;
pub use tenant::{Tenant, TenantLease};

/// The contract each of the six scenario classes implements (the plan §2). A
/// scenario is fill-in-the-blank: `profile`/`faults` declare the load, `run` drives
/// the simulator, and `check` returns the scenario-specific SLO + invariant table.
///
/// Native `async fn` in traits (Rust ≥ 1.94) — scenarios are concrete types used
/// directly in the `#[tokio::test]` bodies, so no `dyn`/boxing is needed.
pub trait Scenario {
    /// The scenario's stable name (used for the `.prom` output + the SLO table).
    fn name(&self) -> &str;

    /// The load this scenario drives.
    fn profile(&self) -> LoadProfile;

    /// The fault schedule (default: the happy path).
    fn faults(&self) -> FaultPlan {
        FaultPlan::none()
    }

    /// Build + drive the simulator, returning the measured report. The default
    /// is the common case (build from `profile`/`faults`, run once).
    fn run(&self) -> impl std::future::Future<Output = RunReport> + Send
    where
        Self: Sync,
    {
        async move {
            let sim = Simulator::new(self.profile())
                .await
                .with_faults(self.faults());
            sim.run(self.name()).await
        }
    }

    /// The scenario-specific SLO + invariant checks over the report. The scaffold
    /// ships `SloResult::todo(..)` placeholders the overnight run calibrates.
    fn check(&self, report: &RunReport) -> Vec<SloResult>;
}
