//! fly.io-machines-compatible wire types.
//!
//! These mirror the shape of the [Fly Machines API](https://fly.io/docs/machines/api/)
//! so an existing fly client (or `flyctl`'s machines calls) can speak to a
//! DreggNet gateway. They are the public request/response bodies; the gateway
//! maps a [`CreateMachineRequest`] onto a dregg execution-lease (see
//! [`crate::lease`]).
//!
//! Divergences from fly are called out inline (`DIVERGENCE:`); the broad shape
//! is faithful, the dregg-specific fields (cap-grade ⟷ guest class) are the
//! honest extensions.

use serde::{Deserialize, Serialize};

/// The lifecycle state of a machine, fly-compatible (lowercase wire form).
///
/// DIVERGENCE: fly also has `replacing` / `destroying` / `suspended`; we model
/// the subset the lease⟷workload weld produces. A machine that the lease
/// refuses (over-budget / unfunded) lands in [`MachineState::Failed`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MachineState {
    /// Record created, lease validated, not yet launched.
    Created,
    /// The durable workload is being launched on the fleet.
    Starting,
    /// The workload is running.
    Started,
    /// A stop was requested; the workload is being reaped.
    Stopping,
    /// The workload is reaped; the record persists.
    Stopped,
    /// Being deleted.
    Destroying,
    /// Deleted.
    Destroyed,
    /// The lease refused the work (unfunded / ill-formed / over-budget) or the
    /// durable workflow failed.
    Failed,
}

impl MachineState {
    /// The lowercase wire name.
    pub const fn as_str(self) -> &'static str {
        match self {
            MachineState::Created => "created",
            MachineState::Starting => "starting",
            MachineState::Started => "started",
            MachineState::Stopping => "stopping",
            MachineState::Stopped => "stopped",
            MachineState::Destroying => "destroying",
            MachineState::Destroyed => "destroyed",
            MachineState::Failed => "failed",
        }
    }
}

/// The guest sizing of a machine (fly's `config.guest`).
///
/// `cpu_kind` selects the isolation/perf class; [`crate::lease`] maps it onto a
/// dregg [`CapGrade`](dreggnet_bridge::CapGrade).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuestConfig {
    /// `shared` or `performance` (fly). Drives the dregg cap-grade mapping.
    #[serde(default = "GuestConfig::default_cpu_kind")]
    pub cpu_kind: String,
    /// Number of vCPUs.
    #[serde(default = "GuestConfig::default_cpus")]
    pub cpus: u32,
    /// Memory in MiB.
    #[serde(default = "GuestConfig::default_memory_mb")]
    pub memory_mb: u32,
}

impl GuestConfig {
    fn default_cpu_kind() -> String {
        "shared".to_string()
    }
    const fn default_cpus() -> u32 {
        1
    }
    const fn default_memory_mb() -> u32 {
        256
    }
}

impl Default for GuestConfig {
    fn default() -> Self {
        GuestConfig {
            cpu_kind: GuestConfig::default_cpu_kind(),
            cpus: GuestConfig::default_cpus(),
            memory_mb: GuestConfig::default_memory_mb(),
        }
    }
}

/// The machine config (fly's `config`).
///
/// Kept to the load-bearing subset: `image`, `guest`, and `env`. fly carries
/// `services`, `mounts`, `checks`, `restart`, etc.; those are recorded here as
/// a passthrough `extra` map so a fly client's full config round-trips without
/// the gateway having to model every key yet (`DIVERGENCE:` not enforced).
// Note: no `Eq` — `extra` holds `serde_json::Value`, which is `PartialEq` only.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct MachineConfig {
    /// The workload image / artifact reference. (DIVERGENCE: fly pulls an OCI
    /// image; DreggNet's bridge runs a polyana workload — the image string is
    /// the workload reference the bridge resolves to a polyana component.)
    #[serde(default)]
    pub image: String,
    /// Guest sizing.
    #[serde(default)]
    pub guest: GuestConfig,
    /// Environment variables.
    #[serde(default)]
    pub env: std::collections::BTreeMap<String, String>,
    /// Unmodeled fly config keys, preserved verbatim so a fly client's request
    /// round-trips. Not enforced by the bridge at this rung.
    #[serde(flatten)]
    pub extra: std::collections::BTreeMap<String, serde_json::Value>,
}

/// The body of `POST /v1/apps/{app}/machines` (fly create).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct CreateMachineRequest {
    /// Optional machine name (fly auto-generates one when omitted).
    #[serde(default)]
    pub name: Option<String>,
    /// Optional region (fly placement hint). DreggNet maps this onto fleet
    /// placement at the control plane (rung 4); recorded here for compat.
    #[serde(default)]
    pub region: Option<String>,
    /// The machine config.
    #[serde(default)]
    pub config: MachineConfig,
}

/// A machine record, fly-compatible.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Machine {
    /// The machine id (fly: a 14-hex-char id).
    pub id: String,
    /// The machine name.
    pub name: String,
    /// The lifecycle state.
    pub state: MachineState,
    /// The region the machine is placed in.
    pub region: String,
    /// The instance id (fly: the running-instance handle; here, the durable
    /// orchestration instance the bridge drives).
    pub instance_id: String,
    /// The private (mesh) IP. Empty until the control plane assigns one.
    pub private_ip: String,
    /// The machine config.
    pub config: MachineConfig,
    /// Creation timestamp (RFC3339).
    pub created_at: String,
    /// Last-update timestamp (RFC3339).
    pub updated_at: String,
    /// DreggNet extension: the result of dispatching this machine's workload to a
    /// compute node (the real durable metered outcome, or the lapse/failure reason).
    /// `None` until the workload is dispatched (a freshly-`created` machine). A fly
    /// client ignores this extra field; a DreggNet client reads the real metering.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dregg: Option<DispatchReport>,
}

/// The outcome of dispatching a machine's workload onto a compute node — the
/// DreggNet-specific result attached to a [`Machine`] after it runs.
///
/// On success it carries the **real** durable metered result the node returned
/// (the polyana step outputs + the `meter_units` charged against the lease). On a
/// lapse (an over-budget / refused lease) or an infrastructure failure it carries
/// the reason, so the machine record reflects exactly what happened to the work.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DispatchReport {
    /// How the workload was dispatched: `"tailscale"` / `"wireguard"` (remote, over
    /// the overlay to a compute node) or `"local"` (in-process bridge on this host).
    pub backend: String,
    /// The compute node the workload ran on (e.g. `"100.64.0.2:8021"`), if remote.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub node: Option<String>,
    /// The total meter units charged against the lease, on success.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub meter_units: Option<i64>,
    /// The durable workflow's per-step outputs, on success.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub outputs: Vec<String>,
    /// The lapse / failure reason, when the workload did not complete (an
    /// over-budget lease lapsed, or the dispatch could not reach the node).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

/// A fly-style error body (`{ "error": "..." }`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiError {
    /// Human-readable error message.
    pub error: String,
}

impl ApiError {
    /// Build an error body.
    pub fn new(msg: impl Into<String>) -> Self {
        ApiError { error: msg.into() }
    }
}

/// The body returned by `stop` / `start` / `delete` actions (`{ "ok": true }`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OkBody {
    /// Whether the action was accepted.
    pub ok: bool,
}

impl OkBody {
    /// An accepted-action body.
    pub fn accepted() -> Self {
        OkBody { ok: true }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_request_defaults_are_sane() {
        // An empty body parses to a valid default request (fly allows a minimal
        // create; the guest defaults to a shared-1cpu-256mb sandbox).
        let req: CreateMachineRequest = serde_json::from_str("{}").unwrap();
        assert!(req.name.is_none());
        assert_eq!(req.config.guest.cpu_kind, "shared");
        assert_eq!(req.config.guest.cpus, 1);
        assert_eq!(req.config.guest.memory_mb, 256);
    }

    #[test]
    fn machine_state_round_trips_lowercase() {
        let j = serde_json::to_string(&MachineState::Started).unwrap();
        assert_eq!(j, "\"started\"");
        let s: MachineState = serde_json::from_str("\"failed\"").unwrap();
        assert_eq!(s, MachineState::Failed);
    }

    #[test]
    fn fly_style_create_body_parses() {
        let body = r#"{
            "name": "my-app-machine",
            "region": "ord",
            "config": {
                "image": "registry.fly.io/my-app:deployment-01",
                "guest": { "cpu_kind": "performance", "cpus": 2, "memory_mb": 1024 },
                "env": { "FOO": "bar" }
            }
        }"#;
        let req: CreateMachineRequest = serde_json::from_str(body).unwrap();
        assert_eq!(req.name.as_deref(), Some("my-app-machine"));
        assert_eq!(req.region.as_deref(), Some("ord"));
        assert_eq!(req.config.guest.cpu_kind, "performance");
        assert_eq!(req.config.guest.cpus, 2);
        assert_eq!(req.config.env.get("FOO").map(String::as_str), Some("bar"));
    }
}
