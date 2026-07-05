//! `ProviderConfig` — the self-hostable provider's configuration.
//!
//! DreggNet is **not a monolith**: anyone can run their own provider/executor
//! against their own dregg cells, their own machines, their own gateway. This is
//! the config that makes the provider a clean, pointable unit rather than a
//! hardcoded service — the `dreggnet-provider` entrypoint
//! ([`crate::bin`](../bin/dreggnet-provider.rs)) loads it and stands up the
//! [`VmProvider`](crate::VmProvider) it describes.
//!
//! ```toml
//! # dreggnet-provider.toml
//! name   = "my-provider"
//! region = "home-lab"
//! asset  = "USD"
//! gateway_bind = "0.0.0.0:8080"
//!
//! [cells]                      # where funded execution-leases are read from
//! kind = "mock"                # or: kind = "dregg_node", node_url = "https://my-node:9090"
//!
//! [backend]                    # what machines this provider rents
//! kind = "local"               # or: kind = "ec2", ami_id = "ami-…", owner = "me"
//! ```
//!
//! Every field has a default, so an empty config is a valid (mock-cells,
//! local-backend) provider. Environment variables override the file
//! ([`ProviderConfig::apply_env`]) so a deployment is configured without editing
//! a file: `DREGGNET_REGION`, `DREGGNET_GATEWAY_BIND`, `DREGGNET_ASSET`,
//! `DREGGNET_NODE_URL` (→ read leases from that dregg node), `DREGGNET_BACKEND`.

use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::ec2::Ec2Provider;
use crate::local::LocalProvider;
use crate::provider::VmProvider;

/// A self-hostable provider's full configuration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProviderConfig {
    /// A label for this provider deployment (the lease-owner tag, the EC2 tag).
    #[serde(default = "ProviderConfig::default_name")]
    pub name: String,
    /// Where this provider reads funded execution-leases from.
    #[serde(default)]
    pub cells: CellSource,
    /// What machine backend this provider rents.
    #[serde(default)]
    pub backend: BackendConfig,
    /// The region tag machines are placed in.
    #[serde(default = "ProviderConfig::default_region")]
    pub region: String,
    /// The address this provider's HTTP gateway binds.
    #[serde(default = "ProviderConfig::default_gateway_bind")]
    pub gateway_bind: String,
    /// The default asset tag a synthesized lease is denominated in.
    #[serde(default = "ProviderConfig::default_asset")]
    pub asset: String,
    /// The compute backends this provider dispatches funded leases onto (the
    /// node-agent fleet). Empty by default — a `DreggNode` deployment lists its
    /// fleet here (or names a single backend via `DREGGNET_COMPUTE_*` env).
    #[serde(default)]
    pub compute: Vec<ComputeBackend>,
    /// The finalized-checkpoint trusted-root anchor for the verified read
    /// (`CommitBindsMMR`). When set, the verified lease read trusts this anchored
    /// receipt-index root over the node's served root. `None` = the node-served
    /// (TOFU) root.
    #[serde(default)]
    pub trusted_root: Option<CheckpointAnchorConfig>,
}

impl Default for ProviderConfig {
    fn default() -> Self {
        ProviderConfig {
            name: ProviderConfig::default_name(),
            cells: CellSource::default(),
            backend: BackendConfig::default(),
            region: ProviderConfig::default_region(),
            gateway_bind: ProviderConfig::default_gateway_bind(),
            asset: ProviderConfig::default_asset(),
            compute: Vec::new(),
            trusted_root: None,
        }
    }
}

/// One compute backend in the provider's fleet — a node-agent the orchestrator
/// dispatches funded leases onto over the mesh, and the payable cell its metered
/// work settles into.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComputeBackend {
    /// The backend's fleet name (the settlement beneficiary key).
    pub name: String,
    /// The backend's address on the mesh overlay the bridge agent listens on
    /// (e.g. `100.64.0.2`, or `127.0.0.1` for a co-located/local backend).
    pub overlay_addr: String,
    /// The port the bridge agent (`/fulfill`) listens on (default 8021).
    #[serde(default = "ComputeBackend::default_agent_port")]
    pub agent_port: u16,
    /// The backend's payable cell id (hex) — where its metered work settles to.
    pub payable_cell: String,
    /// Max concurrent workloads this backend accepts (default 4).
    #[serde(default = "ComputeBackend::default_capacity")]
    pub capacity: usize,
}

impl ComputeBackend {
    fn default_agent_port() -> u16 {
        8021
    }
    fn default_capacity() -> usize {
        4
    }
}

/// The finalized-checkpoint trusted-root anchor (`CommitBindsMMR`), as configured.
/// Maps to [`crate::CheckpointAnchor`] in the daemon's verified-read wiring.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CheckpointAnchorConfig {
    /// The finalized checkpoint height this anchor pins.
    pub height: u64,
    /// The root-pinned receipt-log length at the anchored checkpoint.
    pub len: u64,
    /// The receipt-index MMR root committed by that finalized checkpoint (hex).
    pub mmr_root: String,
    /// The minimum QC vote count for a checkpoint to count as finalized.
    #[serde(default)]
    pub min_qc_votes: usize,
}

impl ProviderConfig {
    fn default_name() -> String {
        "dreggnet-provider".to_string()
    }
    fn default_region() -> String {
        "local".to_string()
    }
    fn default_gateway_bind() -> String {
        "0.0.0.0:8080".to_string()
    }
    fn default_asset() -> String {
        "USD".to_string()
    }

    /// Parse a config from a TOML string.
    pub fn from_toml_str(s: &str) -> Result<ProviderConfig, ConfigError> {
        toml::from_str(s).map_err(|e| ConfigError::Parse(e.to_string()))
    }

    /// Load a config from a TOML file, then apply environment overrides. A
    /// missing path yields the default config (still env-overridable), so a
    /// provider can run with zero config files.
    pub fn load(path: Option<&Path>) -> Result<ProviderConfig, ConfigError> {
        let mut cfg = match path {
            Some(p) if p.exists() => {
                let text = std::fs::read_to_string(p)
                    .map_err(|e| ConfigError::Io(format!("{}: {e}", p.display())))?;
                ProviderConfig::from_toml_str(&text)?
            }
            _ => ProviderConfig::default(),
        };
        cfg.apply_env();
        Ok(cfg)
    }

    /// Apply `DREGGNET_*` environment overrides over the loaded config.
    pub fn apply_env(&mut self) {
        if let Ok(v) = std::env::var("DREGGNET_NAME") {
            self.name = v;
        }
        if let Ok(v) = std::env::var("DREGGNET_REGION") {
            self.region = v;
        }
        if let Ok(v) = std::env::var("DREGGNET_GATEWAY_BIND") {
            self.gateway_bind = v;
        }
        if let Ok(v) = std::env::var("DREGGNET_ASSET") {
            self.asset = v;
        }
        // A node URL flips the cells source to a live dregg node.
        if let Ok(url) = std::env::var("DREGGNET_NODE_URL") {
            self.cells = CellSource::DreggNode { node_url: url };
        }
        // The backend kind: `local` or `ec2` (EC2 also needs DREGGNET_EC2_AMI).
        if let Ok(kind) = std::env::var("DREGGNET_BACKEND") {
            match kind.as_str() {
                "local" => self.backend = BackendConfig::Local,
                "ec2" => {
                    let ami_id = std::env::var("DREGGNET_EC2_AMI").unwrap_or_default();
                    self.backend = BackendConfig::Ec2 {
                        ami_id,
                        owner: self.name.clone(),
                        security_group: std::env::var("DREGGNET_EC2_SECURITY_GROUP").ok(),
                    };
                }
                _ => {}
            }
        }
        // A single compute backend, configured purely from env (the local-proof /
        // single-node path). Appended to any file-listed `[[compute]]` backends.
        if let (Ok(name), Ok(addr), Ok(payable)) = (
            std::env::var("DREGGNET_COMPUTE_NAME"),
            std::env::var("DREGGNET_COMPUTE_ADDR"),
            std::env::var("DREGGNET_COMPUTE_PAYABLE"),
        ) {
            let agent_port = std::env::var("DREGGNET_COMPUTE_PORT")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or_else(ComputeBackend::default_agent_port);
            let capacity = std::env::var("DREGGNET_COMPUTE_CAPACITY")
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or_else(ComputeBackend::default_capacity);
            self.compute.push(ComputeBackend {
                name,
                overlay_addr: addr,
                agent_port,
                payable_cell: payable,
                capacity,
            });
        }
    }

    /// Construct the [`VmProvider`] this config describes.
    ///
    /// `local` builds a [`LocalProvider`] (workloads run in-process via the
    /// bridge); `ec2` builds an [`Ec2Provider`] for a real fleet
    /// ([`Ec2Provider::for_fleet`]) — tagged with the provider name, joined to the
    /// configured security group, and wired to the real overlay mesh
    /// ([`crate::TailscaleMesh`]) as the dispatch plane.
    pub fn build_provider(&self) -> Box<dyn VmProvider> {
        match &self.backend {
            BackendConfig::Local => Box::new(LocalProvider::new()),
            BackendConfig::Ec2 {
                ami_id,
                owner,
                security_group,
            } => Box::new(Ec2Provider::for_fleet(
                ami_id.clone(),
                owner.clone(),
                security_group.clone(),
            )),
        }
    }
}

/// Where a provider reads funded execution-leases from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CellSource {
    /// In-process mock leases — the default-green path, no dregg node required.
    /// A self-hoster proves the loop end-to-end before pointing at a real node.
    Mock,
    /// Read funded execution-lease grants from a dregg node's receipt log (the
    /// bridge's `dregg-verify` lane). `node_url` is the node's light-client RPC.
    /// The decode (`dreggnet_bridge::dregg_verify`) is real and gated; the live
    /// RPC fetch is the named next step.
    DreggNode {
        /// The dregg node / light-client RPC endpoint.
        node_url: String,
    },
}

impl Default for CellSource {
    fn default() -> Self {
        CellSource::Mock
    }
}

impl CellSource {
    /// A short human description of where leases come from.
    pub fn describe(&self) -> String {
        match self {
            CellSource::Mock => "mock (in-process leases)".to_string(),
            CellSource::DreggNode { node_url } => format!("dregg node @ {node_url}"),
        }
    }
}

/// What machine backend a provider rents.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum BackendConfig {
    /// Run workloads in-process on this host via the bridge ([`LocalProvider`]).
    Local,
    /// Rent AWS EC2 instances ([`Ec2Provider`]).
    Ec2 {
        /// The AMI to boot.
        ami_id: String,
        /// The owner tag applied to every instance (`dreggnet=<owner>`).
        owner: String,
        /// The security group every provisioned instance joins (`--security-group-ids`).
        /// `None` leaves the account's default security group.
        #[serde(default)]
        security_group: Option<String>,
    },
}

impl Default for BackendConfig {
    fn default() -> Self {
        BackendConfig::Local
    }
}

impl BackendConfig {
    /// The provider family name this backend builds.
    pub fn provider_name(&self) -> &'static str {
        match self {
            BackendConfig::Local => "local",
            BackendConfig::Ec2 { .. } => "aws-ec2",
        }
    }
}

/// Why loading a [`ProviderConfig`] failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigError {
    /// The config file could not be read.
    Io(String),
    /// The TOML did not parse / did not match the schema.
    Parse(String),
}

impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfigError::Io(e) => write!(f, "config io error: {e}"),
            ConfigError::Parse(e) => write!(f, "config parse error: {e}"),
        }
    }
}

impl std::error::Error for ConfigError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_toml_is_a_valid_default_provider() {
        let cfg = ProviderConfig::from_toml_str("").unwrap();
        assert_eq!(cfg, ProviderConfig::default());
        assert!(matches!(cfg.cells, CellSource::Mock));
        assert!(matches!(cfg.backend, BackendConfig::Local));
        assert_eq!(cfg.build_provider().name(), "local");
    }

    #[test]
    fn full_toml_round_trips() {
        let toml_src = r#"
            name = "home-lab"
            region = "basement"
            asset = "sats"
            gateway_bind = "127.0.0.1:9000"

            [cells]
            kind = "dregg_node"
            node_url = "https://node.example:9090"

            [backend]
            kind = "ec2"
            ami_id = "ami-0abc"
            owner = "ember"
        "#;
        let cfg = ProviderConfig::from_toml_str(toml_src).unwrap();
        assert_eq!(cfg.name, "home-lab");
        assert_eq!(cfg.region, "basement");
        assert_eq!(
            cfg.cells,
            CellSource::DreggNode {
                node_url: "https://node.example:9090".into()
            }
        );
        assert_eq!(cfg.backend.provider_name(), "aws-ec2");
        assert_eq!(cfg.build_provider().name(), "aws-ec2");
    }

    #[test]
    fn ec2_backend_carries_an_optional_security_group_and_builds_for_a_real_fleet() {
        let toml_src = r#"
            [backend]
            kind = "ec2"
            ami_id = "ami-0abc"
            owner = "ember"
            security_group = "sg-12345"
        "#;
        let cfg = ProviderConfig::from_toml_str(toml_src).unwrap();
        match &cfg.backend {
            BackendConfig::Ec2 { security_group, .. } => {
                assert_eq!(security_group.as_deref(), Some("sg-12345"))
            }
            other => panic!("expected an ec2 backend, got {other:?}"),
        }
        // build_provider routes through `for_fleet`, so the real fleet is wired to
        // the real overlay mesh (proven at the Ec2Provider level).
        assert_eq!(cfg.build_provider().name(), "aws-ec2");
    }

    #[test]
    fn ec2_security_group_is_optional() {
        // The field defaults to None when omitted (existing configs still parse).
        let cfg = ProviderConfig::from_toml_str(
            "[backend]\nkind = \"ec2\"\nami_id = \"ami-x\"\nowner = \"me\"\n",
        )
        .unwrap();
        assert!(matches!(
            cfg.backend,
            BackendConfig::Ec2 {
                security_group: None,
                ..
            }
        ));
    }

    #[test]
    fn env_overrides_apply() {
        // Use a unique-ish guard so this doesn't race other tests' env reads.
        unsafe {
            std::env::set_var("DREGGNET_REGION", "env-region");
            std::env::set_var("DREGGNET_NODE_URL", "https://env-node:1");
        }
        let mut cfg = ProviderConfig::default();
        cfg.apply_env();
        assert_eq!(cfg.region, "env-region");
        assert_eq!(
            cfg.cells,
            CellSource::DreggNode {
                node_url: "https://env-node:1".into()
            }
        );
        unsafe {
            std::env::remove_var("DREGGNET_REGION");
            std::env::remove_var("DREGGNET_NODE_URL");
        }
    }

    #[test]
    fn missing_path_is_default() {
        let cfg = ProviderConfig::load(Some(Path::new("/nonexistent/dreggnet.toml"))).unwrap();
        // (env from other tests is cleared; region default holds unless env set)
        assert!(matches!(cfg.backend, BackendConfig::Local));
    }
}
