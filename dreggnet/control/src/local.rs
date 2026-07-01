//! [`LocalProvider`] — the dev provider that runs a workload **in-process via the
//! bridge**. Provisioning a machine is a bookkeeping entry in an in-memory registry;
//! [`VmProvider::run_lease`] fulfills the lease right here on this host through
//! [`dreggnet_bridge::fulfill`]. This is the path the end-to-end place→fulfill→reap
//! test exercises.

use std::collections::HashMap;
use std::sync::Mutex;

use async_trait::async_trait;
use dreggnet_bridge::{BridgeError, DurableOutput, Lease, WorkloadSource};

use crate::provider::{Machine, MachineId, MachineSpec, MachineStatus, ProviderError, VmProvider};

/// A provider that rents "machines" that are really this process. Machines live in
/// an in-memory registry; a workload runs in-process via the bridge.
#[derive(Default)]
pub struct LocalProvider {
    machines: Mutex<HashMap<MachineId, Machine>>,
}

impl LocalProvider {
    pub fn new() -> LocalProvider {
        LocalProvider {
            machines: Mutex::new(HashMap::new()),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<MachineId, Machine>> {
        self.machines
            .lock()
            .expect("local provider registry poisoned")
    }
}

#[async_trait]
impl VmProvider for LocalProvider {
    fn name(&self) -> &'static str {
        "local"
    }

    async fn provision(&self, spec: MachineSpec) -> Result<Machine, ProviderError> {
        let machine = Machine {
            id: MachineId::new(),
            spec,
            // A local machine is this already-running process: ready immediately.
            status: MachineStatus::Running,
            provider: "local",
        };
        self.lock().insert(machine.id.clone(), machine.clone());
        Ok(machine)
    }

    async fn terminate(&self, id: &MachineId) -> Result<(), ProviderError> {
        let mut g = self.lock();
        match g.get_mut(id) {
            Some(m) => {
                m.status = MachineStatus::Terminated;
                Ok(())
            }
            None => Err(ProviderError::NotFound(id.clone())),
        }
    }

    async fn list(&self) -> Result<Vec<Machine>, ProviderError> {
        Ok(self.lock().values().cloned().collect())
    }

    async fn status(&self, id: &MachineId) -> Result<MachineStatus, ProviderError> {
        self.lock()
            .get(id)
            .map(|m| m.status)
            .ok_or_else(|| ProviderError::NotFound(id.clone()))
    }

    async fn run_lease(
        &self,
        machine: &Machine,
        lease: &Lease,
        instance: &str,
    ) -> Result<DurableOutput, ProviderError> {
        // The demo workflow is the no-declared-workload case of run_lease_workload.
        self.run_lease_workload(machine, lease, instance, None)
            .await
    }

    async fn run_lease_workload(
        &self,
        machine: &Machine,
        lease: &Lease,
        instance: &str,
        workload: Option<&WorkloadSource>,
    ) -> Result<DurableOutput, ProviderError> {
        // The machine must actually be runnable; a terminated machine accepts no work.
        let status = self
            .lock()
            .get(&machine.id)
            .map(|m| m.status)
            .ok_or_else(|| ProviderError::NotFound(machine.id.clone()))?;
        if status != MachineStatus::Running {
            return Err(ProviderError::NotRunnable {
                id: machine.id.clone(),
                status,
            });
        }

        // Run the durable workload right here on this host, via the bridge. With a
        // caller-declared `workload` the program the caller wrote runs; otherwise the
        // built-in demo runs. An over-budget lease fails the workflow → we surface it
        // as a lapse so the scheduler reaps the machine; any other bridge error is
        // infrastructure.
        let result = match workload {
            Some(w) => dreggnet_bridge::fulfill_workload(lease, instance, w).await,
            None => dreggnet_bridge::fulfill(lease, instance).await,
        };
        match result {
            Ok(out) => Ok(out),
            Err(BridgeError::WorkflowFailed(msg)) => Err(ProviderError::WorkloadLapsed(msg)),
            Err(other) => Err(ProviderError::Bridge(other.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::provider::{MachineSize, MachineSpec};
    use dreggnet_exec::CapTier;

    fn spec() -> MachineSpec {
        MachineSpec::new(CapTier::Sandboxed, MachineSize::Small, "local")
    }

    #[tokio::test]
    async fn provision_then_list_then_terminate() {
        let p = LocalProvider::new();
        let m = p.provision(spec()).await.unwrap();
        assert_eq!(m.provider, "local");
        assert_eq!(m.status, MachineStatus::Running);

        let listed = p.list().await.unwrap();
        assert_eq!(listed.len(), 1);
        assert_eq!(p.status(&m.id).await.unwrap(), MachineStatus::Running);

        p.terminate(&m.id).await.unwrap();
        assert_eq!(p.status(&m.id).await.unwrap(), MachineStatus::Terminated);

        // Unknown id is a NotFound, not a panic.
        assert!(matches!(
            p.status(&MachineId::new()).await,
            Err(ProviderError::NotFound(_))
        ));
    }

    #[tokio::test]
    async fn run_lease_refuses_a_terminated_machine() {
        let p = LocalProvider::new();
        let m = p.provision(spec()).await.unwrap();
        p.terminate(&m.id).await.unwrap();
        let lease = Lease::funded("a", dreggnet_bridge::CapGrade::Sandboxed, "USD", 100, 1);
        assert!(matches!(
            p.run_lease(&m, &lease, "i-term").await,
            Err(ProviderError::NotRunnable { .. })
        ));
    }
}
