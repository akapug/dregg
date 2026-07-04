//! The rentable-machine abstraction.
//!
//! A [`VmProvider`] rents machines: it can [`provision`](VmProvider::provision) one
//! to a [`MachineSpec`] (cap-tier / size / region), [`terminate`](VmProvider::terminate)
//! it, [`list`](VmProvider::list) what it holds, query a machine's
//! [`status`](VmProvider::status), and [`run_lease`](VmProvider::run_lease) — dispatch
//! a funded durable workload onto a provisioned machine. Concrete impls:
//! [`crate::LocalProvider`] (in-process, via the bridge) and [`crate::Ec2Provider`]
//! (AWS EC2, argv real / API stubbed).

use async_trait::async_trait;
use dreggnet_bridge::{DurableOutput, Lease, WorkloadSource};
use dreggnet_exec::CapTier;
use serde::{Deserialize, Serialize};

/// The opaque handle a provider assigns a machine it rents. For the local
/// provider this is a generated UUID; for EC2 it would carry the `i-…` instance id.
/// `Serialize`/`Deserialize` so a [`MeshNode`](crate::mesh::MeshNode) keyed by it
/// persists in the durable mesh registry (the data-plane durability blocker).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MachineId(pub String);

impl MachineId {
    /// A fresh, unique machine id.
    pub fn new() -> MachineId {
        MachineId(uuid::Uuid::new_v4().to_string())
    }
}

impl Default for MachineId {
    fn default() -> Self {
        MachineId::new()
    }
}

impl std::fmt::Display for MachineId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// How much machine to rent — the compute size axis, orthogonal to the cap-tier
/// (which sets the *isolation*). Mapped to a concrete instance type by each provider
/// (e.g. EC2 `t3.small`/`t3.medium`/`t3.large`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MachineSize {
    Small,
    Medium,
    Large,
}

impl MachineSize {
    /// The EC2 instance type this size maps to.
    pub fn ec2_instance_type(self) -> &'static str {
        match self {
            MachineSize::Small => "t3.small",
            MachineSize::Medium => "t3.medium",
            MachineSize::Large => "t3.large",
        }
    }

    /// The size an EC2 instance type maps back to (the inverse of
    /// [`ec2_instance_type`](MachineSize::ec2_instance_type)), used when
    /// reconstructing a [`MachineSpec`] from a `describe-instances` response.
    pub fn from_ec2_instance_type(instance_type: &str) -> Option<MachineSize> {
        match instance_type {
            "t3.small" => Some(MachineSize::Small),
            "t3.medium" => Some(MachineSize::Medium),
            "t3.large" => Some(MachineSize::Large),
            _ => None,
        }
    }
}

/// What machine to provision: the isolation tier (from the lease cap-grade), the
/// compute size, and the region to rent it in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachineSpec {
    /// The isolation tier the workload runs at (derived from the lease's cap-grade).
    pub cap_tier: CapTier,
    /// The compute size to rent.
    pub size: MachineSize,
    /// The region to rent the machine in (e.g. `"us-east-1"`, or `"local"`).
    pub region: String,
}

impl MachineSpec {
    /// A spec at `cap_tier`/`size` in `region`.
    pub fn new(cap_tier: CapTier, size: MachineSize, region: impl Into<String>) -> MachineSpec {
        MachineSpec {
            cap_tier,
            size,
            region: region.into(),
        }
    }
}

/// The lifecycle state of a rented machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MachineStatus {
    /// Requested; not yet ready to accept a workload.
    Provisioning,
    /// Ready / running a workload.
    Running,
    /// Released back to the provider; no longer billable.
    Terminated,
}

/// A machine a provider rented to a [`MachineSpec`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Machine {
    pub id: MachineId,
    pub spec: MachineSpec,
    pub status: MachineStatus,
    /// The provider family that rents this machine (e.g. `"local"`, `"aws-ec2"`).
    pub provider: &'static str,
}

/// Why a provider operation failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProviderError {
    /// No machine with this id is held by the provider.
    NotFound(MachineId),
    /// The machine is not in a state that can accept a workload.
    NotRunnable {
        id: MachineId,
        status: MachineStatus,
    },
    /// The durable workload running on the machine failed — most importantly an
    /// over-budget meter tick (the lease lapsed). The scheduler reads this as a
    /// lapse and reaps the machine.
    WorkloadLapsed(String),
    /// The bridge / durable runtime surfaced an infrastructure error (not a lapse).
    Bridge(String),
    /// An AWS operation failed: the `aws` CLI could not be spawned, exited non-zero
    /// (the message carries its stderr), or its JSON output could not be parsed. This
    /// is how [`crate::Ec2Provider`] surfaces a real wire failure.
    Aws(String),
    /// The provider cannot yet perform this operation for real; the message carries
    /// the exact command it *would* run (e.g. the `aws ec2 …` argv). This is how the
    /// [`crate::Ec2Provider`] sketch reports its stubbed API surface.
    Unimplemented {
        provider: &'static str,
        would_run: String,
    },
}

impl std::fmt::Display for ProviderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProviderError::NotFound(id) => write!(f, "no such machine: {id}"),
            ProviderError::NotRunnable { id, status } => {
                write!(f, "machine {id} not runnable (status {status:?})")
            }
            ProviderError::WorkloadLapsed(msg) => write!(f, "workload lapsed: {msg}"),
            ProviderError::Bridge(msg) => write!(f, "bridge error: {msg}"),
            ProviderError::Aws(msg) => write!(f, "aws error: {msg}"),
            ProviderError::Unimplemented {
                provider,
                would_run,
            } => {
                write!(f, "{provider} not wired; would run: {would_run}")
            }
        }
    }
}

impl std::error::Error for ProviderError {}

/// The rentable-machine abstraction. Implementors rent machines and dispatch durable
/// workloads onto them. See [`crate::LocalProvider`] (real, in-process) and
/// [`crate::Ec2Provider`] (AWS EC2, stubbed API).
#[async_trait]
pub trait VmProvider: Send + Sync {
    /// The provider family name (e.g. `"local"`, `"aws-ec2"`).
    fn name(&self) -> &'static str;

    /// Rent a machine matching `spec`.
    async fn provision(&self, spec: MachineSpec) -> Result<Machine, ProviderError>;

    /// Release a machine back to the provider (stop billing for it).
    async fn terminate(&self, id: &MachineId) -> Result<(), ProviderError>;

    /// All machines this provider currently holds.
    async fn list(&self) -> Result<Vec<Machine>, ProviderError>;

    /// The current status of one machine.
    async fn status(&self, id: &MachineId) -> Result<MachineStatus, ProviderError>;

    /// Dispatch a funded durable workload (a lease) onto a provisioned machine and
    /// run it to completion. `instance` is the durable-workflow instance id (the
    /// idempotency / replay key). Returns the workflow output on success; an
    /// over-budget lease surfaces as [`ProviderError::WorkloadLapsed`].
    ///
    /// This runs the built-in demo workflow; to run a caller-declared program use
    /// [`run_lease_workload`](VmProvider::run_lease_workload).
    async fn run_lease(
        &self,
        machine: &Machine,
        lease: &Lease,
        instance: &str,
    ) -> Result<DurableOutput, ProviderError>;

    /// Dispatch a funded lease running a CALLER-DECLARED workload (the `run --source`
    /// path) onto a provisioned machine. `workload` is the program the caller wrote;
    /// `None` runs the built-in demo (equivalent to [`run_lease`](VmProvider::run_lease)).
    ///
    /// The default implementation ignores `workload` and runs the demo, so a provider
    /// that has not wired arbitrary-program dispatch keeps working; [`crate::LocalProvider`]
    /// overrides it to genuinely run the declared program through the bridge.
    async fn run_lease_workload(
        &self,
        machine: &Machine,
        lease: &Lease,
        instance: &str,
        workload: Option<&WorkloadSource>,
    ) -> Result<DurableOutput, ProviderError> {
        let _ = workload;
        self.run_lease(machine, lease, instance).await
    }
}
