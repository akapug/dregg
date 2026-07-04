//! [`Scheduler`] — places a funded lease on a provider's machine and tracks the
//! resulting workload's lifecycle.
//!
//! The flow ([`Scheduler::place`]):
//! 1. **Refuse unpaid work first.** An inactive lease (unfunded / ill-formed) is
//!    rejected *before any machine is provisioned* — no box is rented for a lease
//!    whose budget isn't proven. (The bridge re-checks this too; the scheduler does
//!    it up front so it never spends to discover it.)
//! 2. **Provision** a machine matching the lease's cap-grade (→ cap-tier) via the
//!    [`VmProvider`].
//! 3. **Fulfill** the lease on that machine (`run_lease` → the bridge's durable
//!    workflow). Success → [`WorkloadState::Completed`]; an over-budget lapse
//!    ([`ProviderError::WorkloadLapsed`]) → [`WorkloadState::Lapsed`].
//! 4. **Reap on lapse.** A lapsed workload's machine is terminated immediately (no
//!    machine left running for an unpayable lease); the workload moves to
//!    [`WorkloadState::Reaped`]. A completed workload's machine can be reaped
//!    explicitly via [`Scheduler::reap`].

use std::collections::HashMap;
use std::sync::Mutex;

use dreggnet_bridge::{DurableOutput, Lease, WorkloadSource};

use crate::provider::{MachineSize, MachineSpec, ProviderError, VmProvider};

/// The id of a scheduled workload (distinct from the machine it runs on).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WorkloadId(pub String);

impl WorkloadId {
    pub fn new() -> WorkloadId {
        WorkloadId(uuid::Uuid::new_v4().to_string())
    }
}

impl Default for WorkloadId {
    fn default() -> Self {
        WorkloadId::new()
    }
}

impl std::fmt::Display for WorkloadId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Where a scheduled workload is in its lifecycle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkloadState {
    /// Placed on a machine; the durable workflow is in flight.
    Running,
    /// The durable workflow finished successfully.
    Completed,
    /// The lease lapsed (an over-budget meter tick failed the workflow). Pending reap.
    Lapsed(String),
    /// The workload's machine has been released back to the provider.
    Reaped,
}

/// A workload the scheduler is tracking: its lease, the machine it was placed on,
/// its lifecycle state, and (on success) the durable workflow output.
#[derive(Debug, Clone)]
pub struct ScheduledWorkload {
    pub id: WorkloadId,
    pub lease: Lease,
    pub machine: crate::provider::Machine,
    pub state: WorkloadState,
    pub output: Option<DurableOutput>,
    /// The reason the workload lapsed, if it did — PRESERVED across the eager reap
    /// that follows a lapse (which transitions `state` to [`WorkloadState::Reaped`]
    /// and would otherwise discard the [`WorkloadState::Lapsed`] payload). This is
    /// the REAL failure cause (e.g. `wasmi-provider: export 'run' not found`), so a
    /// caller can diagnose a reaped workload accurately instead of blaming the
    /// budget. `None` for a workload that completed or was never lapsed.
    pub lapse_reason: Option<String>,
}

/// Why a placement was refused before any machine was provisioned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlacementError {
    /// The lease is not active (unfunded / non-positive per-period / negative budget):
    /// no machine is rented for it.
    LeaseInactive { lessee: String },
    /// A provider operation failed while provisioning (infrastructure error).
    Provider(ProviderError),
}

impl std::fmt::Display for PlacementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlacementError::LeaseInactive { lessee } => {
                write!(
                    f,
                    "lease for `{lessee}` is inactive: no machine provisioned"
                )
            }
            PlacementError::Provider(e) => write!(f, "provider error during placement: {e}"),
        }
    }
}

impl std::error::Error for PlacementError {}

/// The control-plane scheduler over a single [`VmProvider`].
pub struct Scheduler<P: VmProvider> {
    provider: P,
    /// The compute size every placement requests (a single knob at this rung; a real
    /// scheduler would size from the lease's resource grant).
    size: MachineSize,
    /// The region every placement requests.
    region: String,
    workloads: Mutex<HashMap<WorkloadId, ScheduledWorkload>>,
}

impl<P: VmProvider> Scheduler<P> {
    /// A scheduler that places workloads on `provider`, renting `size` machines in
    /// `region`.
    pub fn new(provider: P, size: MachineSize, region: impl Into<String>) -> Scheduler<P> {
        Scheduler {
            provider,
            size,
            region: region.into(),
            workloads: Mutex::new(HashMap::new()),
        }
    }

    /// The underlying provider (e.g. to `list()` its machines).
    pub fn provider(&self) -> &P {
        &self.provider
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<WorkloadId, ScheduledWorkload>> {
        self.workloads.lock().expect("scheduler registry poisoned")
    }

    /// A snapshot of a tracked workload.
    pub fn workload(&self, id: &WorkloadId) -> Option<ScheduledWorkload> {
        self.lock().get(id).cloned()
    }

    /// All tracked workloads.
    pub fn workloads(&self) -> Vec<ScheduledWorkload> {
        self.lock().values().cloned().collect()
    }

    /// Place a funded lease: provision a machine for its cap-grade, fulfill it via the
    /// bridge (the built-in demo workflow), and record the resulting workload. A lapsed
    /// lease is reaped immediately.
    ///
    /// Returns the [`WorkloadId`]; query its outcome with [`Scheduler::workload`].
    pub async fn place(&self, lease: Lease) -> Result<WorkloadId, PlacementError> {
        self.place_workload(lease, None).await
    }

    /// Place a funded lease running a CALLER-DECLARED workload (the `run --source`
    /// path): provision a machine for its cap-grade, fulfill it with `workload` (the
    /// program the caller wrote; `None` runs the built-in demo), and record the
    /// resulting workload. A lapsed lease is reaped immediately.
    pub async fn place_workload(
        &self,
        lease: Lease,
        workload: Option<WorkloadSource>,
    ) -> Result<WorkloadId, PlacementError> {
        // 1. No machine for unpaid work.
        if !lease.is_active() {
            return Err(PlacementError::LeaseInactive {
                lessee: lease.lessee.clone(),
            });
        }

        // 2. Provision a machine at the lease's cap-tier.
        let spec = MachineSpec::new(lease.tier_binding().tier, self.size, self.region.clone());
        let machine = self
            .provider
            .provision(spec)
            .await
            .map_err(PlacementError::Provider)?;

        // Record it as Running before we drive the (awaited) fulfillment, so the
        // workload is observable for its whole life.
        let id = WorkloadId::new();
        let instance = id.0.clone();
        self.lock().insert(
            id.clone(),
            ScheduledWorkload {
                id: id.clone(),
                lease: lease.clone(),
                machine: machine.clone(),
                state: WorkloadState::Running,
                output: None,
                lapse_reason: None,
            },
        );

        // 3. Fulfill on the machine (the bridge's durable workflow — the declared
        //    program if one was supplied, else the built-in demo).
        match self
            .provider
            .run_lease_workload(&machine, &lease, &instance, workload.as_ref())
            .await
        {
            Ok(out) => {
                if let Some(w) = self.lock().get_mut(&id) {
                    w.state = WorkloadState::Completed;
                    w.output = Some(out);
                }
            }
            Err(ProviderError::WorkloadLapsed(why)) => {
                if let Some(w) = self.lock().get_mut(&id) {
                    // Record the real cause where the eager reap below cannot lose
                    // it (reap transitions `state` → Reaped). A caller reads
                    // `lapse_reason` to diagnose the workload accurately.
                    w.lapse_reason = Some(why.clone());
                    w.state = WorkloadState::Lapsed(why);
                }
                // 4. Reap the lapsed workload's machine immediately.
                self.reap(&id).await.map_err(PlacementError::Provider)?;
            }
            Err(e) => {
                // An infrastructure error: reap the machine we provisioned, then
                // surface the error (we don't leave a rented box dangling).
                let _ = self.provider.terminate(&machine.id).await;
                self.lock().remove(&id);
                return Err(PlacementError::Provider(e));
            }
        }

        Ok(id)
    }

    /// Reap a workload: terminate its machine and mark it [`WorkloadState::Reaped`].
    /// Idempotent — reaping an already-reaped workload is a no-op.
    pub async fn reap(&self, id: &WorkloadId) -> Result<(), ProviderError> {
        let machine_id = {
            let g = self.lock();
            match g.get(id) {
                Some(w) if w.state == WorkloadState::Reaped => return Ok(()),
                Some(w) => w.machine.id.clone(),
                None => return Ok(()),
            }
        };
        self.provider.terminate(&machine_id).await?;
        if let Some(w) = self.lock().get_mut(id) {
            w.state = WorkloadState::Reaped;
        }
        Ok(())
    }

    /// Sweep: reap every workload currently in [`WorkloadState::Lapsed`]. Returns the
    /// ids reaped. (A real control loop calls this on a timer alongside a lease-lapse
    /// watch; `place` already reaps eagerly, so this catches anything observed lapsed
    /// out of band.)
    pub async fn reap_lapsed(&self) -> Result<Vec<WorkloadId>, ProviderError> {
        let lapsed: Vec<WorkloadId> = self
            .lock()
            .iter()
            .filter(|(_, w)| matches!(w.state, WorkloadState::Lapsed(_)))
            .map(|(id, _)| id.clone())
            .collect();
        for id in &lapsed {
            self.reap(id).await?;
        }
        Ok(lapsed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::local::LocalProvider;
    use crate::provider::{MachineStatus, VmProvider};
    use dreggnet_bridge::CapGrade;

    fn sched() -> Scheduler<LocalProvider> {
        Scheduler::new(LocalProvider::new(), MachineSize::Small, "local")
    }

    /// The end-to-end happy path: a funded lease is scheduled → fulfilled via the
    /// bridge (the real wasmi `add(40,2)` then `*2` steps) → reaped.
    #[tokio::test]
    async fn place_fulfills_via_bridge_then_reaps() {
        let s = sched();
        let lease = Lease::funded("agent-1", CapGrade::Sandboxed, "USD", 100, 1);

        let id = s.place(lease).await.expect("placed");
        let w = s.workload(&id).expect("tracked");
        assert_eq!(w.state, WorkloadState::Completed);

        // The durable workflow really ran on the owned sandbox: step1 = add(40,2) = 42, step2 = 84.
        let out = w.output.expect("output");
        assert_eq!(out.step1, "42");
        assert_eq!(out.step2, "84");
        // Two metered steps at cost 1 each.
        assert_eq!(out.meter_units, 2);

        // A machine was provisioned and is still Running until reaped.
        assert_eq!(
            s.provider().status(&w.machine.id).await.unwrap(),
            MachineStatus::Running
        );

        // Reap → the machine is terminated, the workload is Reaped.
        s.reap(&id).await.expect("reaped");
        assert_eq!(s.workload(&id).unwrap().state, WorkloadState::Reaped);
        assert_eq!(
            s.provider().status(&w.machine.id).await.unwrap(),
            MachineStatus::Terminated
        );
    }

    /// An over-budget lease lapses during fulfillment and is reaped automatically; no
    /// machine is left running.
    #[tokio::test]
    async fn over_budget_lease_lapses_and_is_auto_reaped() {
        let s = sched();
        // budget 1, cost 2: the first meter tick already exceeds the budget → lapse.
        let lease = Lease::funded("agent-2", CapGrade::Sandboxed, "USD", 1, 2);

        let id = s.place(lease).await.expect("placed (then lapsed+reaped)");
        let w = s.workload(&id).expect("tracked");
        // place() reaps a lapse eagerly, so the terminal state is Reaped.
        assert_eq!(w.state, WorkloadState::Reaped);
        assert!(w.output.is_none());

        // The provisioned machine was terminated by the reap (no dangling box).
        assert_eq!(
            s.provider().status(&w.machine.id).await.unwrap(),
            MachineStatus::Terminated
        );
    }

    /// An unfunded lease never provisions a machine.
    #[tokio::test]
    async fn unfunded_lease_provisions_nothing() {
        let s = sched();
        let lease = Lease {
            lessee: "agent-3".into(),
            cap_grade: CapGrade::Sandboxed,
            asset: "USD".into(),
            budget_units: 100,
            per_period_units: 1,
            funded: false,
        };
        assert!(matches!(
            s.place(lease).await,
            Err(PlacementError::LeaseInactive { lessee }) if lessee == "agent-3"
        ));
        // Nothing rented.
        assert!(s.provider().list().await.unwrap().is_empty());
        assert!(s.workloads().is_empty());
    }

    /// `reap_lapsed` is a no-op when nothing has lapsed (place already reaps eagerly).
    #[tokio::test]
    async fn reap_lapsed_sweep_is_clean_after_eager_reap() {
        let s = sched();
        let lease = Lease::funded("agent-4", CapGrade::Sandboxed, "USD", 1, 2);
        s.place(lease).await.unwrap();
        // Already reaped eagerly → the sweep finds nothing still Lapsed.
        assert!(s.reap_lapsed().await.unwrap().is_empty());
    }
}
