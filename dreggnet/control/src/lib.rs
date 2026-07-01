//! `dreggnet-control` — the DreggNet control plane (ARCHITECTURE.md ladder rung 4):
//! **scheduling + workload lifecycle + a rentable-machine provider abstraction**.
//!
//! ```text
//!   dregg execution-lease  (the AUTHORIZATION — who, what cap-grade, what budget)
//!     └─ dreggnet-control   (THIS crate — decides WHICH machine, places + reaps)
//!        └─ dreggnet-bridge  (fulfills the lease as a durable polyana workflow)
//!           └─ dreggnet-durable / dreggnet-exec / polyana
//! ```
//!
//! The bridge ([`dreggnet_bridge::fulfill`]) runs a durable workflow on the *local*
//! machine; the control plane decides *which* machine the workload runs on, places
//! it there, tracks its lifecycle, and reaps it when its lease lapses.
//!
//! ## The two pieces
//!
//! - **[`VmProvider`]** — the rentable-machine abstraction: `provision(spec) ->
//!   Machine`, `terminate(id)`, `list()`, `status(id)`, plus `run_lease(...)` to
//!   dispatch a durable workload onto a provisioned machine. A `spec` is a
//!   ([`provider::MachineSpec`]) cap-tier / size / region triple.
//!   - [`LocalProvider`] — runs the workload **in-process via the bridge**. Real,
//!     end-to-end: a lease is fulfilled by [`dreggnet_bridge::fulfill`] on this host.
//!   - [`Ec2Provider`] — the AWS EC2 scale-out. Real: the `aws ec2 …` argv it
//!     issues (RunInstances/TerminateInstances/DescribeInstances), the response
//!     parsing, and the whole provision→running→list/status→terminate lifecycle —
//!     issued over the [`ec2::AwsCli`] seam (the `aws` CLI in production, a mock in
//!     tests, so the lifecycle is provable with no AWS account). A real fleet
//!     ([`Ec2Provider::for_fleet`]) is wired to the real overlay mesh
//!     ([`TailscaleMesh`]). The live `run-instances` (real money) is gated on
//!     `DREGGNET_EC2_LIVE=1`. There is deliberately **no Hetzner provider**.
//!
//! - **[`Scheduler`]** — places a funded lease on a provider's machine and tracks
//!   the resulting workload's lifecycle ([`scheduler::WorkloadState`]:
//!   `Running`/`Completed`/`Lapsed`/`Reaped`). It refuses an unfunded lease
//!   *before* provisioning any machine (no box rented for unpaid work); on a lease
//!   lapse (an over-budget durable workflow → [`dreggnet_bridge::BridgeError::WorkflowFailed`])
//!   it reaps the machine.
//!
//! ## Real vs stubbed (honest)
//!
//! - **Real:** the [`VmProvider`] trait; the [`LocalProvider`] machine registry +
//!   the in-process bridge fulfillment; the [`Scheduler`] place→fulfill→reap
//!   lifecycle (proven end-to-end against the bridge in the crate tests); the
//!   [`Ec2Provider`] argv construction, response parsing, and full lifecycle (proven
//!   against a mock [`ec2::AwsCli`]); the secure mesh dispatch ([`mesh`]) over the
//!   real overlay ([`TailscaleMesh`]).
//! - **Reviewed-go (real cloud / money):** the live `aws ec2 run-instances` against
//!   a real account ([`ec2::SystemAwsCli`]) — gated on `DREGGNET_EC2_LIVE=1` — and
//!   bringing a real fleet up on the live overlay.

pub mod compute_cell;
pub mod config;
pub mod ec2;
pub mod fleet;
pub mod hosting_meter;
pub mod local;
pub mod mesh;
pub mod node_api;
pub mod orchestrator;
pub mod provider;
pub mod scheduler;
pub mod server;
pub mod settle_ledger;
pub mod wg;

pub use config::{BackendConfig, CellSource, ConfigError, ProviderConfig};
pub use ec2::{AwsCli, Ec2Provider, SystemAwsCli};
pub use fleet::{Backend, BackendRegistry, BackendStatus, FleetError, Health, Placement};
// The unified metered-`$DREGG` hosting billing rail (§3.5): publish/bandwidth/
// uptime/cert/build → settled exactly-once Σδ=0 through the conserving ledger, with
// the bandwidth byte-counter roll-up and the over-budget lapse (stops serving).
pub use hosting_meter::{
    BandwidthOutcome, HostingError, HostingMeter, HostingPricing, HostingReceipt, HostingResource,
};
pub use local::LocalProvider;
pub use mesh::{
    Mesh, MeshConfig, MeshError, MeshKeypair, MeshLink, MeshNode, MeshNodeRegistry, StubMesh,
    TailscaleMesh, default_mesh, dispatch_lease_over_mesh,
};
pub use orchestrator::{
    ChannelLeaseSource, LeaseSender, LeaseSource, OrchestratedLease, OrchestratedWorkload,
    Orchestrator, TickReport,
};
// The GO-REAL wire: read funded leases + settle metered work over a live dregg
// node's HTTP API (a plain network client — no kernel link).
pub use node_api::{
    CellDetail, CellListEntry, CheckpointAnchor, CheckpointInfo, NodeApiClient, NodeApiError,
    NodeApiLeaseSource, NodeApiSettlement, TrustedRoot,
};
// The light-client VERIFIED on-chain lease read (links the dregg verified core).
#[cfg(feature = "dregg-verify")]
pub use node_api::VerifiedNodeLeaseSource;
pub use provider::{
    Machine, MachineId, MachineSize, MachineSpec, MachineStatus, ProviderError, VmProvider,
};
pub use scheduler::{PlacementError, ScheduledWorkload, Scheduler, WorkloadId, WorkloadState};
// Persistent servers: long-running, durable, per-period-uptime-metered server
// instances (the fly.io-machines model — `docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.3).
pub use server::{
    MeterOutcome, ServerError, ServerFleet, ServerRecord, ServerState, ServerStore, UptimeReport,
};
// The DURABLE settlement dedup: a restart-surviving `(lease, period)` ledger so the
// real settlement rail is exactly-once across a restart (LEASE-3), not in-memory.
pub use settle_ledger::{DurableSettleLedger, Reserved, SettleRecord};

// Re-export the lease + bridge vocabulary a caller drives the control plane with,
// so a downstream crate need only depend on `dreggnet-control`.
pub use dreggnet_bridge::{BridgeError, CapGrade, DurableOutput, Lease, WorkloadSource};
pub use dreggnet_exec::CapTier;
// The settlement (Payable) rail the orchestrator pays metered work through.
pub use dreggnet_durable::{ConservingLedger, LeaseCharge, SettleError, SettleReceipt, Settlement};
// The static-hosting serving-path byte-counter the hosting meter rolls up + lapses.
pub use dreggnet_webapp::BandwidthMeter;
