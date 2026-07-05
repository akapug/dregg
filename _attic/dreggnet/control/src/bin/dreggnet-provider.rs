//! `dreggnet-provider` — the self-hostable provider entrypoint.
//!
//! Point it at your config (your cells, your machines, your gateway) and it
//! stands up the [`VmProvider`](dreggnet_control::VmProvider) you described. This
//! is what makes DreggNet federated rather than a monolith: anyone runs their own
//! provider against their own dregg cells. The moat is the network, not the code.
//!
//! ```sh
//! dreggnet-provider                         # default: mock cells, local backend (offline demo)
//! dreggnet-provider --config provider.toml  # your config
//! DREGGNET_NODE_URL=https://my-node:9090 \
//!   DREGGNET_REGION=home-lab dreggnet-provider   # env overrides
//! ```
//!
//! What it does:
//! 1. Loads + resolves the [`ProviderConfig`] (file + `DREGGNET_*` env overrides)
//!    and prints the resolved plan.
//! 2. **With a `dregg_node` cells source** (`DREGGNET_NODE_URL` / `[cells] kind =
//!    "dregg_node"`): runs the REAL autonomous loop — funded execution-leases are
//!    READ from the live node (light-client-VERIFIED when built `--features
//!    dregg-verify`), dispatched onto the configured compute backends, metered, and
//!    each metered period SETTLED as a real conserving `Transfer` turn submitted
//!    back to the node. This is [`Orchestrator::run_until_shutdown`] over the real
//!    seams ([`VerifiedNodeLeaseSource`] + [`NodeApiSettlement`]) — the daemon, not
//!    a demo. It runs until `ctrl-c`.
//! 3. **With `mock` cells + a `local` backend**: runs an offline demo lease
//!    end-to-end through the provider to prove the wiring on this host.
//!
//! See `docs/SELF-HOST.md` and `docs/GO-REAL.md` for the full guides.

use std::path::PathBuf;
use std::sync::Arc;

use dreggnet_control::config::{BackendConfig, CellSource, ComputeBackend, ProviderConfig};
use dreggnet_control::{CapGrade, Lease};

#[tokio::main]
async fn main() {
    init_tracing();

    let args: Vec<String> = std::env::args().collect();
    let config_path = parse_config_path(&args);

    let cfg = match ProviderConfig::load(config_path.as_deref()) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("dreggnet-provider: {e}");
            std::process::exit(1);
        }
    };

    print_plan(&cfg, config_path.as_deref());

    // A live dregg-node cells source runs the REAL autonomous loop.
    if let CellSource::DreggNode { node_url } = cfg.cells.clone() {
        if let Err(e) = run_real_loop(&cfg, &node_url).await {
            eprintln!("dreggnet-provider: real loop failed: {e}");
            std::process::exit(1);
        }
        return;
    }

    let provider = cfg.build_provider();
    eprintln!("dreggnet-provider: built `{}` provider", provider.name());

    // Mock cells + a local backend: the offline demo that proves the wiring here.
    let demoable =
        matches!(cfg.backend, BackendConfig::Local) && matches!(cfg.cells, CellSource::Mock);
    if !demoable {
        eprintln!(
            "dreggnet-provider: provider is configured; the run loop against {} \
             with the {} backend is the deployment step (see docs/SELF-HOST.md).",
            cfg.cells.describe(),
            cfg.backend.provider_name(),
        );
        return;
    }

    eprintln!("dreggnet-provider: running an offline demo lease through the provider…");
    if let Err(e) = run_demo_lease(&cfg, provider.as_ref()).await {
        eprintln!("dreggnet-provider: demo failed: {e}");
        std::process::exit(1);
    }
}

/// Install the structured-logging subscriber so the control-plane spans
/// (`tick`/`process_lease`/`meter_period`/`tick_bandwidth` with `lessee`/`server_id`/
/// `period`/`units` fields) are emitted. Verbosity is `RUST_LOG`-controlled, defaulting
/// to `info` for this crate; format follows `DREGGNET_LOG_FORMAT=json` for a JSON sink.
fn init_tracing() {
    use tracing_subscriber::{EnvFilter, fmt, prelude::*};
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info,dreggnet_control=info"));
    let registry = tracing_subscriber::registry().with(filter);
    if std::env::var("DREGGNET_LOG_FORMAT").as_deref() == Ok("json") {
        registry.with(fmt::layer().json()).init();
    } else {
        registry.with(fmt::layer()).init();
    }
}

/// Run the REAL autonomous orchestration loop against a live dregg node: read
/// funded leases (verified), dispatch onto the compute fleet, meter, settle each
/// period as a real `Transfer`, reap. Runs until `ctrl-c`.
async fn run_real_loop(
    cfg: &ProviderConfig,
    node_url: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    use dreggnet_control::fleet::Backend;
    use dreggnet_control::mesh::{MeshKeypair, MeshNode, TailscaleMesh};
    use dreggnet_control::provider::MachineId;
    use dreggnet_control::{BackendRegistry, NodeApiSettlement, Orchestrator};

    if cfg.compute.is_empty() {
        return Err(
            "no compute backends configured: add `[[compute]]` to the config \
                    (name/overlay_addr/payable_cell) or set DREGGNET_COMPUTE_NAME / \
                    _ADDR / _PAYABLE. The loop has nothing to dispatch onto."
                .into(),
        );
    }

    // The operator bearer for the node's protected submit endpoint (settlement).
    let bearer = std::env::var("DREGGNET_NODE_BEARER").unwrap_or_default();
    if bearer.is_empty() {
        eprintln!(
            "dreggnet-provider: WARNING — DREGGNET_NODE_BEARER is unset; settlement \
             Transfer turns will be rejected by the node's protected submit endpoint. \
             Unlock the node and export its bearer token to settle."
        );
    }

    // The real settlement rail: one conserving Transfer per metered period, mapped
    // backend name → payable cell id.
    let mut settlement = NodeApiSettlement::new(node_url, bearer);
    for b in &cfg.compute {
        settlement = settlement.map_backend(&b.name, &b.payable_cell);
    }
    // DURABLE settlement dedup (LEASE-3): persist each settled (lease, period) to
    // disk so a restart of this daemon cannot re-submit — and so double-charge — an
    // already-settled period. Path from DREGGNET_SETTLE_LEDGER (default
    // ./dreggnet-settle.jsonl). The dedup is enforced BEFORE every Transfer submit.
    let ledger_path = std::env::var("DREGGNET_SETTLE_LEDGER")
        .unwrap_or_else(|_| "dreggnet-settle.jsonl".to_string());
    let settlement = settlement
        .with_ledger_path(&ledger_path)
        .map_err(|e| format!("open durable settlement ledger `{ledger_path}`: {e}"))?;
    eprintln!("  settle ledger: durable at {ledger_path} (exactly-once across restart)");
    let settlement = Arc::new(settlement);

    // The compute fleet the loop dispatches onto.
    let registry = Arc::new(BackendRegistry::new());
    for b in &cfg.compute {
        let overlay: std::net::Ipv4Addr = b.overlay_addr.parse().map_err(|e| {
            format!(
                "backend `{}` overlay_addr `{}`: {e}",
                b.name, b.overlay_addr
            )
        })?;
        // A co-located/already-meshed backend: the dispatch reaches it at
        // overlay_addr:agent_port over the up mesh link (the endpoint/key are the
        // handshake material, placeholders for an already-up overlay).
        let mut node = MeshNode::new(
            MachineId(b.name.clone()),
            MeshKeypair::generate().public_base64(),
            "0.0.0.0:51820",
            overlay,
        );
        node.agent_port = b.agent_port;
        registry.register(Backend::new(&b.name, node, b.capacity));
        registry.mark_healthy(&b.name);
        eprintln!(
            "  backend {} @ {}:{} (cap {}) → pays {}",
            b.name, b.overlay_addr, b.agent_port, b.capacity, b.payable_cell
        );
    }

    let mesh = Arc::new(TailscaleMesh::new());
    let orch = Orchestrator::new(registry, mesh, settlement);

    let source = build_lease_source(cfg, node_url);
    describe_source(cfg);

    eprintln!(
        "dreggnet-provider: real loop running against {} — reading funded leases, \
         dispatching, metering, settling. ctrl-c to stop.",
        cfg.cells.describe()
    );

    let shutdown = async {
        let _ = tokio::signal::ctrl_c().await;
        eprintln!("dreggnet-provider: shutdown signal — draining…");
    };
    orch.run_until_shutdown(source, shutdown).await;
    eprintln!("dreggnet-provider: stopped.");
    Ok(())
}

/// Build the lease source for the real loop. Feature-on (`dregg-verify`): the
/// light-client-VERIFIED on-chain read, optionally pinned to a finalized-checkpoint
/// trusted root (`CommitBindsMMR`). Feature-off: the node-API read (cell-API
/// trusted) — still real, just not light-client-verified.
#[cfg(feature = "dregg-verify")]
fn build_lease_source(
    cfg: &ProviderConfig,
    node_url: &str,
) -> dreggnet_control::VerifiedNodeLeaseSource {
    use dreggnet_control::{CheckpointAnchor, VerifiedNodeLeaseSource};
    let mut source = VerifiedNodeLeaseSource::new(node_url);
    if let Some(a) = &cfg.trusted_root {
        source = source.with_checkpoint_anchor(CheckpointAnchor {
            height: a.height,
            len: a.len,
            mmr_root: a.mmr_root.clone(),
            min_qc_votes: a.min_qc_votes,
        });
    }
    source
}

#[cfg(not(feature = "dregg-verify"))]
fn build_lease_source(
    _cfg: &ProviderConfig,
    node_url: &str,
) -> dreggnet_control::NodeApiLeaseSource {
    dreggnet_control::NodeApiLeaseSource::new(node_url)
}

/// Print which lease-read path is active (verified vs cell-API trusted).
fn describe_source(cfg: &ProviderConfig) {
    #[cfg(feature = "dregg-verify")]
    {
        match &cfg.trusted_root {
            Some(a) => eprintln!(
                "  lease read   : LIGHT-CLIENT VERIFIED, trusted root pinned to finalized \
                 checkpoint height {} (len {})",
                a.height, a.len
            ),
            None => eprintln!(
                "  lease read   : LIGHT-CLIENT VERIFIED (node-served root, TOFU — pin a \
                 [trusted_root] checkpoint anchor to harden)"
            ),
        }
    }
    #[cfg(not(feature = "dregg-verify"))]
    {
        let _ = cfg;
        eprintln!(
            "  lease read   : node cell-API (trusted; build --features dregg-verify for the \
             light-client-VERIFIED read)"
        );
    }
}

/// Provision a machine, run a funded demo lease on it via the bridge, then reap.
async fn run_demo_lease(
    cfg: &ProviderConfig,
    provider: &dyn dreggnet_control::VmProvider,
) -> Result<(), Box<dyn std::error::Error>> {
    use dreggnet_control::{MachineSize, MachineSpec};

    // A funded lease that authorizes a small sandboxed workload (mock cells).
    let lease = Lease::funded(&cfg.name, CapGrade::Sandboxed, &cfg.asset, 1_000, 1);
    let spec = MachineSpec::new(lease.tier_binding().tier, MachineSize::Small, &cfg.region);

    let machine = provider.provision(spec).await?;
    eprintln!(
        "  provisioned machine {} ({})",
        machine.id, machine.provider
    );

    let instance = format!("{}-demo-{}", cfg.name, machine.id);
    match provider.run_lease(&machine, &lease, &instance).await {
        Ok(out) => {
            eprintln!(
                "  workload completed on the owned sandbox: step1={} step2={} meter_units={}",
                out.step1, out.step2, out.meter_units
            );
        }
        Err(e) => {
            eprintln!("  workload did not complete: {e}");
            provider.terminate(&machine.id).await.ok();
            return Err(Box::new(e));
        }
    }

    provider.terminate(&machine.id).await?;
    eprintln!("  reaped machine {}", machine.id);
    eprintln!(
        "dreggnet-provider: demo OK — the configured provider ran a metered, sandboxed workload."
    );
    Ok(())
}

/// Print the resolved configuration plan.
fn print_plan(cfg: &ProviderConfig, path: Option<&std::path::Path>) {
    eprintln!("dreggnet-provider: resolved plan");
    match path {
        Some(p) if p.exists() => eprintln!("  config       : {}", p.display()),
        _ => eprintln!("  config       : (defaults + env)"),
    }
    eprintln!("  name         : {}", cfg.name);
    eprintln!("  region       : {}", cfg.region);
    eprintln!("  asset        : {}", cfg.asset);
    eprintln!("  cells        : {}", cfg.cells.describe());
    eprintln!("  backend      : {}", cfg.backend.provider_name());
    eprintln!("  gateway bind : {}", cfg.gateway_bind);
    if !cfg.compute.is_empty() {
        eprintln!("  compute      : {}", describe_compute(&cfg.compute));
    }
}

/// A one-line summary of the configured compute fleet.
fn describe_compute(compute: &[ComputeBackend]) -> String {
    compute
        .iter()
        .map(|b| format!("{}@{}:{}", b.name, b.overlay_addr, b.agent_port))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Parse `--config <path>` / `-c <path>`; default to `./dreggnet-provider.toml`
/// when it exists, else `None` (defaults + env).
fn parse_config_path(args: &[String]) -> Option<PathBuf> {
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--config" | "-c" => {
                return args.get(i + 1).map(PathBuf::from);
            }
            _ => i += 1,
        }
    }
    let default = PathBuf::from("dreggnet-provider.toml");
    if default.exists() {
        Some(default)
    } else {
        None
    }
}
