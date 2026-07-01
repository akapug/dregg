//! `dreggnet-gateway` — the runnable fly-compatible machines API server.
//!
//! This is the serving binary for the gateway library: it binds a TCP listener
//! and serves the [`MachinesHandler`](dreggnet_gateway::MachinesHandler) route
//! table over a small HTTP/1.1 connection loop. Each accepted connection's
//! request line + headers + body are read off the socket, dispatched through
//! the **real** route table + lease gate
//! ([`MachinesHandler::dispatch`](dreggnet_gateway::MachinesHandler::dispatch)),
//! and the fly-shaped JSON response written back.
//!
//! ```sh
//! dreggnet-gateway --port 8080
//!
//! curl -s -X POST localhost:8080/v1/apps/demo/machines \
//!   -H 'content-type: application/json' \
//!   -d '{"name":"w1","config":{"guest":{"cpus":1,"memory_mb":256}}}'
//! curl -s localhost:8080/v1/apps/demo/machines
//! ```
//!
//! ## What this binary serves
//!
//! - **The friendly root:** `GET /` is a status landing page (HTML); `GET /status`
//!   and `GET /healthz` are its JSON forms — name, machine count, where workloads
//!   run, federation health, the portal pointer. Not a fly-shaped 404.
//! - **The machines API:** list, status, stop, start, delete, and create. Create
//!   decodes the request body (the server reads it off the socket), runs it through
//!   the bridge's real lease-gate ([`dreggnet_bridge::workflow_input_for_lease`]),
//!   and records the machine. A lease the bridge refuses yields a 4xx and **no**
//!   machine record.
//! - **The static minisites:** a published `<name>.example.com` host serves the
//!   site cell's assets, of any size, byte-for-byte (large assets stream complete).
//! - **`GET /metrics`:** a Prometheus exposition of per-request counters.
//!
//! ## Hardening (the public-internet surface)
//!
//! The hand-rolled loop bounds the abuse vectors a public surface attracts, even
//! behind Caddy: per-socket read/write timeouts plus an overall request deadline
//! (slow-loris), a request body-size cap returning `413` (untrusted
//! `Content-Length`), a connection-concurrency cap (thread-per-connection DoS),
//! and explicit `Transfer-Encoding: chunked` request decoding. A response larger
//! than the working buffer grows the buffer to fit rather than silently
//! truncating the body under a full `Content-Length`. Every served request is
//! recorded into [`Metrics`]. These limits reject only abusive/malformed traffic;
//! a well-behaved client sees the same bytes as before.
//!
//! Built on the gateway's own clean-room HTTP value types ([`dreggnet_http`]) —
//! pure-`std`, no third-party HTTP engine, so it builds natively on macOS and
//! Linux. For a Linux deploy artifact from macOS:
//! `cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-gateway`.

use std::io::{Read, Write};
use std::net::{Ipv4Addr, TcpListener, TcpStream};
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use dreggnet_gateway::{
    ApiHandler, ComputeBackend, FundingSource, GatewayInfo, MachineGateway, MachinesHandler,
    Metrics, NodeFunding, SiteHostHandler, SitePublishHandler, StorageHandler, Surface,
};
use dreggnet_guard::Guard;
use dreggnet_http::handler::HandlerResult;
use dreggnet_http::response::{StatusCode, content_type};
use dreggnet_http::{Method, ResponseWriter};
use dreggnet_storage::BucketRegistry;
use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry, is_valid_name};
use dreggnet_webauth::cred::PublicKey;
use tokio::runtime::Runtime;
use tokio::sync::Semaphore;

/// Default cap on the request header block; a larger header block is rejected
/// with 431. Override with `DREGGNET_MAX_HEADER_BYTES`.
const MAX_HEADER_BYTES: usize = 64 * 1024;
/// Initial response buffer size (status line + headers + body). The buffer grows
/// to fit a larger response rather than truncating it.
const RESPONSE_BUF_BYTES: usize = 256 * 1024;
/// Default per-socket read timeout (idle-stall guard).
const DEFAULT_READ_TIMEOUT_MS: u64 = 30_000;
/// Default per-socket write timeout.
const DEFAULT_WRITE_TIMEOUT_MS: u64 = 30_000;
/// Default total wall-clock budget to read one request (slow-trickle guard).
const DEFAULT_REQUEST_DEADLINE_MS: u64 = 60_000;
/// Default request body-size cap (declared or actual); over this is a 413.
const DEFAULT_MAX_BODY_BYTES: usize = 4 * 1024 * 1024;
/// Default cap on simultaneously-served connections (thread-per-connection DoS
/// guard); excess connections wait for a slot.
const DEFAULT_MAX_CONNECTIONS: usize = 1024;

/// Robustness limits for the connection loop, configurable via `DREGGNET_*` env.
#[derive(Debug, Clone)]
struct Limits {
    read_timeout: Duration,
    write_timeout: Duration,
    request_deadline: Duration,
    max_header_bytes: usize,
    max_body_bytes: usize,
    max_connections: usize,
}

impl Limits {
    fn from_env() -> Limits {
        Limits {
            read_timeout: env_ms("DREGGNET_READ_TIMEOUT_MS", DEFAULT_READ_TIMEOUT_MS),
            write_timeout: env_ms("DREGGNET_WRITE_TIMEOUT_MS", DEFAULT_WRITE_TIMEOUT_MS),
            request_deadline: env_ms("DREGGNET_REQUEST_DEADLINE_MS", DEFAULT_REQUEST_DEADLINE_MS),
            max_header_bytes: env_usize("DREGGNET_MAX_HEADER_BYTES", MAX_HEADER_BYTES),
            max_body_bytes: env_usize("DREGGNET_MAX_BODY_BYTES", DEFAULT_MAX_BODY_BYTES),
            max_connections: env_usize("DREGGNET_MAX_CONNECTIONS", DEFAULT_MAX_CONNECTIONS).max(1),
        }
    }
}

/// The shared serving context: the handlers, the blocking runtime, the metrics,
/// and the robustness limits — cloned (by `Arc`) into each connection thread.
struct Ctx {
    handler: Arc<MachinesHandler>,
    site_handler: Arc<SiteHostHandler>,
    storage_handler: Arc<StorageHandler>,
    publish_handler: Arc<SitePublishHandler>,
    api_handler: Arc<ApiHandler>,
    runtime: Arc<Runtime>,
    metrics: Arc<Metrics>,
    limits: Limits,
}

fn main() -> std::io::Result<()> {
    init_tracing();
    let args: Vec<String> = std::env::args().collect();
    let bind = parse_bind(&args);

    // The gateway: dispatch a created machine's workload to a real compute node over
    // the overlay (the live edge→node-a path) when configured, else fulfill it
    // in-process (the dev / single-box default). See `env_gateway`.
    let (gateway, dispatch_desc) = env_gateway();
    let info = env_info();
    let handler = Arc::new(MachinesHandler::with_info(Arc::new(gateway), info));

    // The static web-hosting data plane: published minisite cells served by `Host`
    // (`<name>.example.com`). The registry is loaded once at boot from the sites
    // directory (`DREGGNET_SITES_DIR`, default `/srv/sites`) — each subdirectory
    // `<name>/…` is published as the site cell `<name>` through the cap-gated,
    // receipted publish turn, the same `SiteRegistry::publish` the CLI drives.
    // The bandwidth byte-counter rides the serving path: every delivered body byte
    // is accrued per site (the genuinely-new hosting meter, §3.5). Counting is
    // always live (a harmless in-memory accumulator); the per-period roll-up that
    // settles it as real `$DREGG` is the separate control-plane meter
    // (`dreggnet_control::HostingMeter`) — flipping real billing on is reviewed-go.
    // SIGNED so each publish seals a re-witnessable receipt (the `dregg-cloud
    // verify` path), AND metered so the serving path counts bandwidth. The signing
    // secret rides `DREGGNET_SITE_SEED` (32-byte hex), defaulting to a fixed dev seed.
    let registry = Arc::new(
        SiteRegistry::signed(env_site_seed())
            .with_bandwidth_meter(Arc::new(dreggnet_webapp::BandwidthMeter::new())),
    );
    let sites_dir =
        std::env::var("DREGGNET_SITES_DIR").unwrap_or_else(|_| "/srv/sites".to_string());
    let site_owner =
        std::env::var("DREGGNET_SITE_OWNER").unwrap_or_else(|_| "agent:dreggnet".to_string());
    let published = load_sites(&registry, Path::new(&sites_dir), &site_owner);
    // The custom-domain control plane: verified BYO domains (`blog.example.com`)
    // routed to their bound site cells beside the `<name>.example.com` wildcard.
    // Empty at boot — bindings arrive via the control surface (`dregg domains add`);
    // only a *verified* binding routes or earns a cert (the on-demand-TLS `ask`).
    let domains = Arc::new(dregg_domains::DomainRegistry::new());
    // The on-demand-TLS `ask` re-confirms a custom domain's control against LIVE
    // DNS before a cert is minted (never a client-asserted flag). Build the live
    // resolver once; if it cannot start, fall back to proven-bindings-only (an
    // unverified custom domain then simply earns no cert).
    let site_handler = Arc::new(match dregg_domains::LiveDns::from_system() {
        Ok(resolver) => SiteHostHandler::with_domains_and_resolver(
            Arc::clone(&registry),
            Arc::clone(&domains),
            Arc::new(resolver),
        ),
        Err(e) => {
            tracing::warn!(error = %e, "live DNS resolver unavailable; custom-domain cert asks read only already-proven bindings");
            SiteHostHandler::with_domains(Arc::clone(&registry), Arc::clone(&domains))
        }
    });

    // The durable object-store data plane: the cap-gated, metered, receipted
    // `BucketRegistry` served over `PUT/GET/DELETE /storage/<bucket>/<key>`. The
    // registry is a SIGNED receipt stream (so each put/delete is re-witnessable);
    // the signing secret rides `DREGGNET_STORAGE_SEED` (32-byte hex), defaulting to
    // a fixed dev seed. Writes are gated on a `dga1_` `storage-bucket/<name>`
    // credential verified under the same root authority the webauth edge uses
    // (`DREGGNET_WEBAUTH_ROOT_PUBKEY`); unset → writes fail closed (401), reads
    // (public, re-witnessable) still serve.
    let storage_registry = Arc::new(BucketRegistry::signed(env_storage_seed()));
    let storage_root = env_storage_root();
    if storage_root.is_none() {
        tracing::warn!(
            "no storage cap-authority configured (set DREGGNET_WEBAUTH_ROOT_PUBKEY); storage writes will be refused (401), public reads still serve"
        );
    }
    let storage_handler = Arc::new(StorageHandler::with_budget(
        storage_registry,
        storage_root,
        dreggnet_gateway::storage::DEFAULT_BUDGET_UNITS,
    ));

    // The site-publish CONTROL plane: `POST /v1/sites/<name>/publish` accepts a built
    // static bundle and publishes it into the SAME signed `SiteRegistry` the static
    // data plane serves from — so `dregg-cloud deploy --endpoint <gateway>` pushes a
    // real site to the live cloud, served + `dregg-cloud verify`-able. Cap-gated to
    // the publishing `dga1_` subject (the owner) under the same root authority the
    // storage write-gate uses, and FUNDED through the same node funding source the
    // machines API reads (LEASE-1a) — no funding source ⇒ publishes fail closed.
    let publish_funding = env_funding();
    let publish_handler = Arc::new(SitePublishHandler::new(
        Arc::clone(&registry),
        env_storage_root(),
        publish_funding,
    ));

    // The customer-console READ plane: cap-scoped `GET /api/{sites,servers,domains,
    // buckets,billing/{spend,balances}}` — each returns only the records owned by
    // the verified `X-Dregg-Subject`. The gateway holds the site / domain / bucket
    // registries live; the server fleet + $DREGG ledger are pluggable sources, empty
    // until the control plane exposes them (the honesty law the console shares).
    let api_handler = Arc::new(ApiHandler::new(
        Arc::clone(&registry),
        Arc::clone(&domains),
        Arc::clone(storage_handler.registry()),
    ));

    // The dispatch + node-health probe are async / blocking-IO; the connection loop
    // is a synchronous thread-per-connection model, so each connection blocks on the
    // shared runtime to drive the (async) create→dispatch path.
    let runtime = Arc::new(
        tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?,
    );

    let limits = Limits::from_env();
    let metrics = Arc::new(Metrics::new());
    let ctx = Arc::new(Ctx {
        handler,
        site_handler,
        storage_handler,
        publish_handler,
        api_handler,
        runtime,
        metrics,
        limits: limits.clone(),
    });

    let listener = TcpListener::bind(&bind)?;
    eprintln!("dreggnet-gateway: serving the fly-compatible machines API on http://{bind}");
    eprintln!("  compute: {dispatch_desc}");
    eprintln!("  hosting: {} site(s) from {sites_dir}", published.len());
    for name in &published {
        eprintln!("    https://{name}.example.com/");
    }
    eprintln!(
        "  limits: read {}ms, write {}ms, deadline {}ms, body {} B, conns {}",
        limits.read_timeout.as_millis(),
        limits.write_timeout.as_millis(),
        limits.request_deadline.as_millis(),
        limits.max_body_bytes,
        limits.max_connections,
    );
    eprintln!("  try: curl -s http://{bind}/            # the friendly root");
    eprintln!("  try: curl -s http://{bind}/metrics     # Prometheus metrics");
    tracing::info!(%bind, conns = limits.max_connections, "gateway listening");

    run_server(listener, ctx);
    Ok(())
}

/// Install a `tracing` subscriber so per-request events + connection errors are
/// emitted structured (replacing the old `eprintln!` error path). Honors
/// `RUST_LOG`; defaults to `info`. `try_init` so test re-entry is harmless.
fn init_tracing() {
    use tracing_subscriber::EnvFilter;
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    let _ = tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(false)
        .try_init();
}

/// The accept loop: bound in-flight connections with a semaphore (excess accepts
/// wait for a slot), then serve each on its own thread holding a permit.
fn run_server(listener: TcpListener, ctx: Arc<Ctx>) {
    let sem = Arc::new(Semaphore::new(ctx.limits.max_connections));
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                // Backpressure: don't accept unbounded work — wait for a free
                // connection slot before spawning. A held permit bounds the
                // number of live connection threads.
                let permit = match ctx.runtime.block_on(sem.clone().acquire_owned()) {
                    Ok(p) => p,
                    Err(_) => break, // the semaphore was closed → shutting down
                };
                let ctx = Arc::clone(&ctx);
                std::thread::spawn(move || {
                    let _permit = permit; // released when the connection finishes
                    if let Err(e) = serve_connection(stream, &ctx) {
                        ctx.metrics.record_connection_error();
                        tracing::warn!(error = %e, "connection error");
                    }
                });
            }
            Err(e) => tracing::warn!(error = %e, "accept error"),
        }
    }
}

/// Build the gateway from `DREGGNET_*` env, returning it plus a human description of
/// where workloads run, how creates are funded, and whether the abuse guard is on.
///
/// **Compute (where a created machine runs):**
/// - `DREGGNET_DISPATCH=tailscale` → dispatch over the host's tailnet/headscale
///   overlay to the compute node at `DREGGNET_NODE_A_OVERLAY` (default
///   `100.64.0.2`) `:DREGGNET_NODE_A_PORT` (default `8021`) — the live edge path.
/// - anything else (the default) → fulfill leases in-process on this host.
///
/// **Funding (W1 — LEASE-1a, live in the binary):** the create path admits work
/// only against a lease the chain attests as funded. `DREGGNET_NODE_URL` (e.g.
/// `http://dregg-node:8420`) attaches a [`NodeFunding`] source that reads funded
/// leases live from that node on every create — node-trusted over the cell API by
/// default, **light-client-VERIFIED** when built `--features dregg-verify`. With
/// `DREGGNET_NODE_URL` UNSET the gateway has no way to confirm real on-chain
/// funding, so it fails **closed**: every `POST .../machines` is refused. (The
/// staging compose sets `DREGGNET_NODE_URL` so the default path admits funded work.)
///
/// **Guard (W4 — abuse prevention, live in the binary):** `DREGGNET_GUARD=on`
/// attaches the per-account [`Guard`] with conservative default quotas + deploy/
/// request rate limits, so an over-quota / rate-limited / suspended create is
/// refused in-band (402/429/403) — not just exercised in the library tests. The
/// governance-log signing seed is `DREGGNET_GUARD_SEED` (64-hex), else a fixed seed.
fn env_gateway() -> (MachineGateway, String) {
    let dispatch = std::env::var("DREGGNET_DISPATCH").unwrap_or_default();
    let (mut gateway, compute_desc) = if dispatch.eq_ignore_ascii_case("tailscale") {
        let overlay = std::env::var("DREGGNET_NODE_A_OVERLAY")
            .ok()
            .and_then(|s| s.parse::<Ipv4Addr>().ok())
            .unwrap_or(Ipv4Addr::new(100, 64, 0, 2));
        let port = std::env::var("DREGGNET_NODE_A_PORT")
            .ok()
            .and_then(|s| s.parse::<u16>().ok())
            .unwrap_or(8021);
        let backend = ComputeBackend::node_a(overlay, port);
        let desc = format!(
            "dispatch over the {} overlay to {} (a created machine RUNS a real metered workload there)",
            backend.backend(),
            backend.target(),
        );
        (MachineGateway::with_compute(backend), desc)
    } else {
        (
            MachineGateway::new(),
            "in-process bridge (single-box / dev; set DREGGNET_DISPATCH=tailscale to dispatch to a compute node)".to_string(),
        )
    };

    // W1 — the LEASE-1a funding gate, LIVE in the serving binary: read funded
    // leases from the dregg node (never synthesize them from the request).
    let funding_desc = match std::env::var("DREGGNET_NODE_URL")
        .ok()
        .filter(|s| !s.is_empty())
    {
        Some(node_url) => {
            gateway = gateway.funded_by(Arc::new(NodeFunding::new(&node_url)));
            #[cfg(feature = "dregg-verify")]
            let how = "light-client-VERIFIED on-chain read";
            #[cfg(not(feature = "dregg-verify"))]
            let how =
                "node-trusted cell-API read (build --features dregg-verify for the verified read)";
            format!("funded leases from the dregg node at {node_url} ({how})")
        }
        None => {
            tracing::warn!(
                "no funding source: DREGGNET_NODE_URL is unset, so the gateway fails CLOSED — \
                 EVERY POST /machines will be refused (Unfunded). Set \
                 DREGGNET_NODE_URL=http://dregg-node:8420 to admit funded work (LEASE-1a)."
            );
            "NONE — fail-closed, all creates refused (set DREGGNET_NODE_URL)".to_string()
        }
    };

    // W4 — the per-account abuse guard, LIVE in the serving binary.
    let guard_desc = if env_flag("DREGGNET_GUARD") {
        gateway = gateway.guarded_by(Arc::new(Guard::new(env_guard_seed())));
        "ON (conservative default quotas + deploy/request rate limits)".to_string()
    } else {
        "off (set DREGGNET_GUARD=on to enable per-account abuse prevention)".to_string()
    };

    let desc = format!("{compute_desc}\n  funding: {funding_desc}\n  guard:   {guard_desc}");
    (gateway, desc)
}

/// Whether a `DREGGNET_*` env flag is set to an affirmative value
/// (`1`/`on`/`true`/`yes`, case-insensitive).
fn env_flag(key: &str) -> bool {
    std::env::var(key)
        .map(|v| {
            let v = v.trim();
            v.eq_ignore_ascii_case("1")
                || v.eq_ignore_ascii_case("on")
                || v.eq_ignore_ascii_case("true")
                || v.eq_ignore_ascii_case("yes")
        })
        .unwrap_or(false)
}

/// The abuse guard's governance-log signing seed, from `DREGGNET_GUARD_SEED`
/// (64-hex), else a fixed dev seed. A real host sets a persistent secret so the
/// moderation history's signing key is stable across restarts.
fn env_guard_seed() -> [u8; 32] {
    std::env::var("DREGGNET_GUARD_SEED")
        .ok()
        .and_then(|s| hex32(&s))
        .unwrap_or([0x6du8; 32])
}

/// Build the friendly-landing info from `DREGGNET_*` env.
///
/// - `DREGGNET_GATEWAY_NAME` (default `"DreggNet gateway"`),
/// - `DREGGNET_PORTAL_URL` (default `https://portal.example.com`),
/// - `DREGGNET_NODE_HEALTH_URL` (e.g. `http://dregg-node:8420/health`) — probed for
///   federation health; unset → health `"unknown"`.
fn env_info() -> GatewayInfo {
    let mut info = GatewayInfo::default();
    if let Ok(name) = std::env::var("DREGGNET_GATEWAY_NAME") {
        if !name.is_empty() {
            info.name = name;
        }
    }
    if let Ok(portal) = std::env::var("DREGGNET_PORTAL_URL") {
        if !portal.is_empty() {
            info.portal_url = portal;
        }
    }
    if let Ok(url) = std::env::var("DREGGNET_NODE_HEALTH_URL") {
        if !url.is_empty() {
            info.node_health_url = Some(url);
        }
    }
    info.health_timeout = Duration::from_millis(800);
    info
}

/// Read a `Duration` from a milliseconds env var, falling back to `default_ms`.
fn env_ms(key: &str, default_ms: u64) -> Duration {
    let ms = std::env::var(key)
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(default_ms);
    Duration::from_millis(ms)
}

/// Read a `usize` from an env var, falling back to `default`.
fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(default)
}

/// The 32-byte secret seed the storage receipt chain signs under, from
/// `DREGGNET_STORAGE_SEED` (64-hex), else a fixed dev seed. A real host sets a
/// persistent secret so the receipt stream is stable across restarts.
fn env_storage_seed() -> [u8; 32] {
    std::env::var("DREGGNET_STORAGE_SEED")
        .ok()
        .and_then(|s| hex32(&s))
        .unwrap_or([0x5au8; 32])
}

/// The 32-byte secret seed the SITE publish receipt chain signs under, from
/// `DREGGNET_SITE_SEED` (64-hex), else a fixed dev seed. Signing the registry makes
/// every publish receipt re-witnessable (the `dregg-cloud verify` path); a real
/// host sets a persistent secret so the receipt stream is stable across restarts.
fn env_site_seed() -> [u8; 32] {
    std::env::var("DREGGNET_SITE_SEED")
        .ok()
        .and_then(|s| hex32(&s))
        .unwrap_or([0x51u8; 32])
}

/// The funding source the site-publish gate admits a publish against (LEASE-1a):
/// `NodeFunding` reading funded leases from the dregg node at `DREGGNET_NODE_URL`
/// (the same source the machines API uses), or `None` (unset) so publishes fail
/// **closed** — the gateway never publishes work it cannot confirm is funded.
fn env_funding() -> Option<Arc<dyn FundingSource>> {
    std::env::var("DREGGNET_NODE_URL")
        .ok()
        .filter(|s| !s.is_empty())
        .map(|node_url| Arc::new(NodeFunding::new(&node_url)) as Arc<dyn FundingSource>)
}

/// The storage cap-authority root public key, from `DREGGNET_WEBAUTH_ROOT_PUBKEY`
/// (the same root the webauth edge trusts). `None` (unset/invalid) → writes fail
/// closed.
fn env_storage_root() -> Option<PublicKey> {
    std::env::var("DREGGNET_WEBAUTH_ROOT_PUBKEY")
        .ok()
        .filter(|s| !s.is_empty())
        .and_then(|s| PublicKey::from_hex(&s).ok())
}

/// Decode a 64-char hex string into a 32-byte array; `None` if malformed.
fn hex32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

/// Parse `--port`/`-p` (default 8080) and `--bind`/`-b` host (default
/// `0.0.0.0`) into a `host:port` bind string.
fn parse_bind(args: &[String]) -> String {
    let mut port: u16 = 8080;
    let mut host = String::from("0.0.0.0");
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--port" | "-p" => {
                if let Some(v) = args.get(i + 1).and_then(|s| s.parse().ok()) {
                    port = v;
                }
                i += 2;
            }
            "--bind" | "-b" => {
                if let Some(v) = args.get(i + 1) {
                    host = v.clone();
                }
                i += 2;
            }
            _ => i += 1,
        }
    }
    format!("{host}:{port}")
}

/// Publish every immediate subdirectory of `sites_dir` as a site cell.
///
/// `sites_dir/<name>/…` → the site `<name>` (served at `<name>.example.com`),
/// published through the cap-gated, receipted [`SiteRegistry::publish`] with a
/// `site-host/<name>` cap held by `owner`. A missing directory is not an error
/// (hosting is simply off); a subdir whose name is not a valid DNS label, or which
/// has no files, is skipped with a warning. Returns the names actually published.
fn load_sites(registry: &SiteRegistry, sites_dir: &Path, owner: &str) -> Vec<String> {
    let mut published = Vec::new();
    let entries = match std::fs::read_dir(sites_dir) {
        Ok(e) => e,
        Err(_) => return published, // no sites dir → hosting is off, not a failure
    };
    let mut dirs: Vec<std::path::PathBuf> = entries
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    for dir in dirs {
        let name = match dir.file_name().and_then(|n| n.to_str()) {
            Some(n) if is_valid_name(n) => n.to_string(),
            Some(n) => {
                tracing::warn!(name = n, "skipping site — not a valid site name");
                continue;
            }
            None => continue,
        };
        let content = match load_dir(&dir) {
            Ok(c) if !c.is_empty() => c,
            Ok(_) => {
                tracing::warn!(%name, "skipping site — no files to publish");
                continue;
            }
            Err(e) => {
                tracing::warn!(%name, error = %e, "skipping site — read error");
                continue;
            }
        };
        let cap = PublishCap::for_site(owner, &name);
        match registry.publish(&cap, &name, content) {
            Ok(r) => {
                eprintln!(
                    "dreggnet-gateway: published `{}` ({} assets, root {}) by {}",
                    r.name, r.asset_count, r.content_root, r.owner
                );
                published.push(name);
            }
            Err(e) => tracing::warn!(%name, error = %e, "publish refused"),
        }
    }
    published
}

/// Recursively read `dir` into [`SiteContent`], keyed by path relative to `dir`
/// (`dir/index.html` → `/index.html`, `dir/img/logo.png` → `/img/logo.png`),
/// content-type inferred from each file's extension.
fn load_dir(dir: &Path) -> std::io::Result<SiteContent> {
    let mut content = SiteContent::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in std::fs::read_dir(&d)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.is_file() {
                let rel = path.strip_prefix(dir).unwrap_or(&path);
                let key = format!("/{}", rel.to_string_lossy().replace('\\', "/"));
                let bytes = std::fs::read(&path)?;
                content = content.with(key, bytes);
            }
        }
    }
    Ok(content)
}

/// The parsed request head: the request line + the few headers the loop acts on,
/// extracted in a single pass over the header block.
struct RequestHead {
    method: Method,
    path: String,
    /// `Content-Length`, if a valid one was declared.
    content_length: Option<usize>,
    /// Whether `Transfer-Encoding: chunked` was declared.
    chunked: bool,
    /// The `Host` header value (empty if absent).
    host: String,
    /// The presented dregg credential (`dga1_…`): `Authorization: Bearer <tok>`
    /// or `X-Dregg-Credential: <tok>`. The storage + site-publish write-gates verify it.
    credential: Option<String>,
    /// The verified cap-holder subject the webauth forward-auth (Caddy) echoes as
    /// `X-Dregg-Subject` — the authenticated owner the console read surfaces scope to.
    subject: Option<String>,
}

/// Parse the request line + `Content-Length` / `Transfer-Encoding` / `Host` in a
/// single pass over the header block. `None` if there is no request line.
fn parse_head(header_block: &[u8]) -> Option<RequestHead> {
    let text = String::from_utf8_lossy(header_block);
    let mut lines = text.split("\r\n");

    let request_line = lines.next()?;
    let mut parts = request_line.split_whitespace();
    let method = Method::from_bytes(parts.next().unwrap_or("").as_bytes());
    let path = parts.next().unwrap_or("/").to_string();

    let mut content_length = None;
    let mut chunked = false;
    let mut host = String::new();
    let mut authorization: Option<String> = None;
    let mut x_credential: Option<String> = None;
    let mut subject: Option<String> = None;
    for line in lines {
        if line.is_empty() {
            continue;
        }
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        let name = name.trim();
        let value = value.trim();
        if name.eq_ignore_ascii_case("content-length") {
            content_length = value.parse::<usize>().ok();
        } else if name.eq_ignore_ascii_case("transfer-encoding") {
            if value
                .split(',')
                .any(|t| t.trim().eq_ignore_ascii_case("chunked"))
            {
                chunked = true;
            }
        } else if name.eq_ignore_ascii_case("host") {
            host = value.to_string();
        } else if name.eq_ignore_ascii_case("authorization") {
            authorization = Some(value.to_string());
        } else if name.eq_ignore_ascii_case("x-dregg-credential") {
            x_credential = Some(value.to_string());
        } else if name.eq_ignore_ascii_case("x-dregg-subject") {
            subject = Some(value.to_string()).filter(|s| !s.is_empty());
        }
    }

    // Prefer `Authorization: Bearer <tok>`, else `X-Dregg-Credential: <tok>`.
    let credential = authorization
        .as_deref()
        .and_then(|a| {
            a.strip_prefix("Bearer ")
                .or_else(|| a.strip_prefix("bearer "))
                .map(|t| t.trim().to_string())
        })
        .or(x_credential)
        .filter(|c| !c.is_empty());

    Some(RequestHead {
        method,
        path,
        content_length,
        chunked,
        host,
        credential,
        subject,
    })
}

/// The outcome of reading a request body.
enum BodyOutcome {
    /// The full body was read.
    Body(Vec<u8>),
    /// The declared/actual size exceeds the cap → 413.
    TooLarge,
    /// A read timed out or the request deadline passed → 408.
    Timeout,
    /// The chunked framing was malformed → 400.
    Malformed,
}

/// Read an identity (Content-Length) body, capping at `max` and bounding total
/// time by `deadline`. `leftover` is whatever already followed the header block.
fn read_sized_body<R: Read>(
    stream: &mut R,
    leftover: &[u8],
    len: usize,
    max: usize,
    deadline: Instant,
) -> std::io::Result<BodyOutcome> {
    if len > max {
        return Ok(BodyOutcome::TooLarge);
    }
    let mut body = leftover.to_vec();
    let mut tmp = [0u8; 8192];
    while body.len() < len {
        if Instant::now() >= deadline {
            return Ok(BodyOutcome::Timeout);
        }
        match stream.read(&mut tmp) {
            Ok(0) => break, // peer closed early — serve what arrived, truncated below
            Ok(n) => body.extend_from_slice(&tmp[..n]),
            Err(e) if is_timeout(&e) => return Ok(BodyOutcome::Timeout),
            Err(e) => return Err(e),
        }
    }
    body.truncate(len);
    Ok(BodyOutcome::Body(body))
}

/// Decode a `Transfer-Encoding: chunked` request body, capping the decoded size
/// at `max` and bounding total time by `deadline`. `leftover` is whatever already
/// followed the header block.
fn read_chunked_body<R: Read>(
    stream: &mut R,
    leftover: &[u8],
    max: usize,
    deadline: Instant,
) -> std::io::Result<BodyOutcome> {
    let mut raw = leftover.to_vec();
    let mut decoded: Vec<u8> = Vec::new();
    let mut cursor = 0usize;
    let mut tmp = [0u8; 8192];

    loop {
        match find_subslice(&raw[cursor..], b"\r\n") {
            Some(rel) => {
                let line_end = cursor + rel;
                let size_line = &raw[cursor..line_end];
                // chunk-size [ ";" chunk-ext ]
                let size = match std::str::from_utf8(size_line)
                    .ok()
                    .map(|s| s.split(';').next().unwrap_or("").trim())
                    .and_then(|s| usize::from_str_radix(s, 16).ok())
                {
                    Some(v) => v,
                    None => return Ok(BodyOutcome::Malformed),
                };
                let data_start = line_end + 2;
                if size == 0 {
                    // The last chunk; the body is complete (trailers, if any, are
                    // not part of the entity and are ignored).
                    return Ok(BodyOutcome::Body(decoded));
                }
                if decoded.len() + size > max {
                    return Ok(BodyOutcome::TooLarge);
                }
                let need = data_start + size + 2; // data + trailing CRLF
                if raw.len() < need {
                    match fill(stream, &mut raw, &mut tmp, max, deadline)? {
                        Some(outcome) => return Ok(outcome),
                        None => continue,
                    }
                }
                decoded.extend_from_slice(&raw[data_start..data_start + size]);
                cursor = data_start + size + 2; // skip data + CRLF
            }
            None => match fill(stream, &mut raw, &mut tmp, max, deadline)? {
                Some(outcome) => return Ok(outcome),
                None => {}
            },
        }
    }
}

/// Read one more block into `raw` for the chunked decoder. Returns
/// `Some(outcome)` on a terminal condition (timeout / EOF / over-cap), `None` if
/// more bytes were appended and decoding should continue.
fn fill<R: Read>(
    stream: &mut R,
    raw: &mut Vec<u8>,
    tmp: &mut [u8],
    max: usize,
    deadline: Instant,
) -> std::io::Result<Option<BodyOutcome>> {
    if Instant::now() >= deadline {
        return Ok(Some(BodyOutcome::Timeout));
    }
    match stream.read(tmp) {
        Ok(0) => Ok(Some(BodyOutcome::Malformed)), // EOF mid-body
        Ok(n) => {
            raw.extend_from_slice(&tmp[..n]);
            // Bound the raw buffer too (framing overhead beyond the decoded cap).
            if raw.len() > max.saturating_add(64 * 1024) {
                return Ok(Some(BodyOutcome::TooLarge));
            }
            Ok(None)
        }
        Err(e) if is_timeout(&e) => Ok(Some(BodyOutcome::Timeout)),
        Err(e) => Err(e),
    }
}

/// Whether an IO error is a socket read/write timeout (a stalled peer).
fn is_timeout(e: &std::io::Error) -> bool {
    matches!(
        e.kind(),
        std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
    )
}

/// Serve a single request on one connection: read the request (with timeouts,
/// caps, and chunked decoding), route it by `Host`, write the response (growing
/// the buffer to fit so a large asset is never truncated), record metrics, then
/// close.
fn serve_connection(mut stream: TcpStream, ctx: &Ctx) -> std::io::Result<()> {
    let start = Instant::now();
    stream.set_read_timeout(Some(ctx.limits.read_timeout))?;
    stream.set_write_timeout(Some(ctx.limits.write_timeout))?;
    let deadline = start + ctx.limits.request_deadline;

    // 1. Read until the header block terminator (CRLFCRLF) is in the buffer,
    //    bounded by the header-size cap and the request deadline.
    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 8192];
    let header_end = loop {
        if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
            break pos + 4;
        }
        if Instant::now() >= deadline {
            return reject(&mut stream, ctx, start, 408, "408 Request Timeout");
        }
        match stream.read(&mut tmp) {
            Ok(0) => return Ok(()), // closed before a complete request — nothing to serve
            Ok(n) => {
                buf.extend_from_slice(&tmp[..n]);
                if buf.len() > ctx.limits.max_header_bytes {
                    return reject(
                        &mut stream,
                        ctx,
                        start,
                        431,
                        "431 Request Header Fields Too Large",
                    );
                }
            }
            Err(e) if is_timeout(&e) => {
                return reject(&mut stream, ctx, start, 408, "408 Request Timeout");
            }
            Err(e) => return Err(e),
        }
    };

    // 2. Parse the request line + the headers the loop acts on, in one pass.
    let Some(head) = parse_head(&buf[..header_end]) else {
        return reject(&mut stream, ctx, start, 400, "400 Bad Request");
    };

    // 3. Read the body: explicit chunked decode, or an identity Content-Length
    //    body, both capped at `max_body_bytes` and bounded by the deadline.
    let leftover = &buf[header_end..];
    let body = if head.chunked {
        match read_chunked_body(&mut stream, leftover, ctx.limits.max_body_bytes, deadline)? {
            BodyOutcome::Body(b) => b,
            BodyOutcome::TooLarge => {
                return reject(&mut stream, ctx, start, 413, "413 Payload Too Large");
            }
            BodyOutcome::Timeout => {
                return reject(&mut stream, ctx, start, 408, "408 Request Timeout");
            }
            BodyOutcome::Malformed => {
                return reject(&mut stream, ctx, start, 400, "400 Bad Request");
            }
        }
    } else {
        let len = head.content_length.unwrap_or(0);
        if len > ctx.limits.max_body_bytes {
            return reject(&mut stream, ctx, start, 413, "413 Payload Too Large");
        }
        match read_sized_body(
            &mut stream,
            leftover,
            len,
            ctx.limits.max_body_bytes,
            deadline,
        )? {
            BodyOutcome::Body(b) => b,
            BodyOutcome::TooLarge => {
                return reject(&mut stream, ctx, start, 413, "413 Payload Too Large");
            }
            BodyOutcome::Timeout => {
                return reject(&mut stream, ctx, start, 408, "408 Request Timeout");
            }
            BodyOutcome::Malformed => {
                return reject(&mut stream, ctx, start, 400, "400 Bad Request");
            }
        }
    };

    // 4. Route by `Host` / path, render the response into a right-sized buffer,
    //    write it, and record the sample.
    //
    //    - A published-minisite host (`<name>.example.com`) → the static
    //      `SiteHostHandler` (a pure read → grow-and-retry sizes the buffer to the
    //      asset, so a >256 KiB asset serves complete, never truncated).
    //    - The Caddy on-demand-TLS `ask` probe (`/internal/site-exists?domain=…`,
    //      an INTERNAL call — Caddy-only; bind/firewall to the internal interface)
    //      → 200 iff that host resolves to a published site, else 404.
    //    - `GET /metrics` → the Prometheus exposition.
    //    - Everything else → the fly-machines route table (`dispatch_async`), which
    //      is side-effecting (create/start), so it is rendered exactly once.
    let (surface, out) = if ctx.site_handler.serves_host(&head.host) {
        let out = render_pure(RESPONSE_BUF_BYTES, |w| {
            ctx.site_handler
                .dispatch(head.method, &head.host, &head.path, &body, w)
        });
        (Surface::Hosting, out)
    } else if path_is(&head.path, "/internal/site-exists") {
        let out = render_pure(4096, |w| site_exists_ask(&ctx.site_handler, &head.path, w));
        (Surface::Ask, out)
    } else if head.method == Method::Get && path_is(&head.path, "/metrics") {
        (
            Surface::Other,
            prometheus_response(&ctx.metrics.render_prometheus()),
        )
    } else if StorageHandler::serves_path(&head.path) {
        // The object-store data plane (`PUT/GET/DELETE /storage/<bucket>/<key>`).
        // A read is pure (the public, re-witnessable GET charges nothing), so it
        // grow-and-retries to serve a large object whole; a write/list/create is
        // side-effecting (metering + the receipt seal), rendered exactly once (the
        // JSON receipt is small, well under the buffer).
        let now = now_unix();
        let cred = head.credential.as_deref();
        let out = if head.method == Method::Get {
            render_pure(RESPONSE_BUF_BYTES, |w| {
                ctx.storage_handler
                    .dispatch(head.method, &head.path, cred, &body, now, w)
            })
        } else {
            render_once(RESPONSE_BUF_BYTES, |w| {
                ctx.storage_handler
                    .dispatch(head.method, &head.path, cred, &body, now, w)
            })
            .unwrap_or_else(response_too_large)
        };
        (Surface::Other, out)
    } else if SitePublishHandler::serves_path(&head.path) {
        // The site-publish control plane (`POST /v1/sites/<name>/publish`). Pushes a
        // built bundle into the live SiteRegistry — cap-gated + funded + receipted, a
        // side-effecting turn rendered exactly once (the JSON receipt is small).
        let now = now_unix();
        let cred = head.credential.as_deref();
        let out = render_once(RESPONSE_BUF_BYTES, |w| {
            ctx.publish_handler
                .dispatch(head.method, &head.path, cred, &body, now, w)
        })
        .unwrap_or_else(response_too_large);
        (Surface::Other, out)
    } else if ApiHandler::serves_path(&head.path) {
        // The customer-console read plane (cap-scoped `GET /api/...`). Pure reads
        // scoped to the verified `X-Dregg-Subject`; grow-and-retry sizes the buffer.
        let subject = head.subject.as_deref();
        let out = render_pure(RESPONSE_BUF_BYTES, |w| {
            ctx.api_handler
                .dispatch(head.method, &head.path, subject, w)
        });
        (Surface::Other, out)
    } else {
        // Side-effecting: render once. If the response would exceed the buffer we
        // must not ship a truncated body under a full Content-Length — send a
        // clean 500 instead (machines/JSON responses never approach this).
        let out = render_once(RESPONSE_BUF_BYTES, |w| {
            ctx.runtime.block_on(
                ctx.handler
                    .dispatch_async(head.method, &head.path, &body, w),
            )
        })
        .unwrap_or_else(response_too_large);
        (Surface::Machines, out)
    };

    stream.write_all(&out)?;
    stream.flush()?;
    record(ctx, surface, status_of(&out), out.len(), start);
    Ok(())
}

/// Whether `path` (query stripped) equals `want`.
fn path_is(path: &str, want: &str) -> bool {
    path.split('?').next() == Some(want)
}

/// Wall-clock unix seconds — the verifier clock for storage credential expiry.
fn now_unix() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// The Caddy on-demand-TLS `ask` endpoint: `GET /internal/site-exists?domain=<host>`.
/// A `200` iff `<host>` is a published `<name>.example.com` site cell **or a
/// verified custom domain**, else `404` — so Caddy mints a Let's Encrypt cert only
/// for a host a tenant actually controls (an unverified / squatted custom domain
/// earns no cert).
///
/// INTERNAL ONLY: this carries no authentication and is meant to be reachable
/// solely from Caddy. Bind/firewall the gateway's `:8080` to the internal
/// interface so the public internet cannot probe site existence.
fn site_exists_ask(
    site_handler: &SiteHostHandler,
    path: &str,
    response: &mut ResponseWriter,
) -> HandlerResult {
    let domain = path
        .split_once('?')
        .and_then(|(_, q)| q.split('&').find_map(|kv| kv.strip_prefix("domain=")))
        .unwrap_or("");
    let status = if site_handler.cert_ok(domain) {
        StatusCode::Ok
    } else {
        StatusCode::NotFound
    };
    response.status(status).content_length(0).body(&[]);
    HandlerResult::Written(response.position())
}

/// Render a **pure** response via `f` into a right-sized owned buffer, growing
/// the buffer until the slice-backed writer no longer truncates. `f` must be free
/// of observable side effects because it may be invoked more than once.
///
/// This is the truncation fix: the slice writer silently caps at the buffer
/// length, so a too-small buffer would emit a short body under a full
/// `Content-Length`. Growing until the written length is strictly inside the
/// buffer guarantees the whole response was captured.
fn render_pure(mut cap: usize, f: impl Fn(&mut ResponseWriter) -> HandlerResult) -> Vec<u8> {
    loop {
        let mut out = vec![0u8; cap];
        let mut writer = ResponseWriter::new(&mut out);
        let n = f(&mut writer).bytes_written();
        if n < cap {
            out.truncate(n);
            return out;
        }
        // The writer filled the buffer exactly — it may have truncated. Grow and
        // re-render to be certain we captured the whole response.
        cap = cap.saturating_mul(2);
    }
}

/// Render a side-effecting response via `f` exactly once into a `cap`-byte
/// buffer. Returns `None` if the response filled the buffer (a possible
/// truncation) so the caller can substitute a clean error rather than ship a
/// corrupt short body.
fn render_once(
    cap: usize,
    f: impl FnOnce(&mut ResponseWriter) -> HandlerResult,
) -> Option<Vec<u8>> {
    let mut out = vec![0u8; cap];
    let mut writer = ResponseWriter::new(&mut out);
    let n = f(&mut writer).bytes_written();
    if n < cap {
        out.truncate(n);
        Some(out)
    } else {
        None
    }
}

/// A `500` for a response that overflowed the working buffer (so it is never
/// shipped truncated under a full Content-Length).
fn response_too_large() -> Vec<u8> {
    render_pure(1024, |w| {
        let body = br#"{"error":"response too large"}"#;
        w.status(StatusCode::InternalServerError)
            .header_line(content_type::APPLICATION_JSON)
            .content_length(body.len())
            .body(body);
        HandlerResult::Written(w.position())
    })
}

/// Render the Prometheus metrics exposition as an HTTP response.
fn prometheus_response(body: &str) -> Vec<u8> {
    render_pure(body.len() + 256, |w| {
        w.status(StatusCode::Ok)
            .header(b"Content-Type", b"text/plain; version=0.0.4; charset=utf-8")
            .content_length(body.len())
            .body(body.as_bytes());
        HandlerResult::Written(w.position())
    })
}

/// The numeric status code of a rendered HTTP/1.1 response (`HTTP/1.1 NNN …`).
fn status_of(resp: &[u8]) -> u16 {
    resp.get(9..12)
        .and_then(|b| std::str::from_utf8(b).ok())
        .and_then(|s| s.trim().parse::<u16>().ok())
        .unwrap_or(0)
}

/// Write a bare status line + empty body and close (the early-reject paths),
/// recording the sample under the `other` surface. A write failure on a
/// misbehaving peer is swallowed (the connection is being dropped anyway).
fn reject(
    stream: &mut TcpStream,
    ctx: &Ctx,
    start: Instant,
    code: u16,
    status_line: &str,
) -> std::io::Result<()> {
    let msg = format!("HTTP/1.1 {status_line}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n");
    let n = match stream
        .write_all(msg.as_bytes())
        .and_then(|_| stream.flush())
    {
        Ok(()) => msg.len(),
        Err(_) => 0,
    };
    record(ctx, Surface::Other, code, n, start);
    Ok(())
}

/// Record one served request into the metrics + emit a structured trace event.
fn record(ctx: &Ctx, surface: Surface, status: u16, bytes: usize, start: Instant) {
    let micros = start.elapsed().as_micros() as u64;
    ctx.metrics.record(surface, status, bytes, micros);
    tracing::info!(
        surface = surface.label(),
        status,
        bytes,
        latency_us = micros,
        "served"
    );
}

/// First index of `needle` in `haystack`, if present.
fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::SocketAddr;

    #[test]
    fn parse_bind_defaults_and_overrides() {
        assert_eq!(parse_bind(&["dreggnet-gateway".into()]), "0.0.0.0:8080");
        assert_eq!(
            parse_bind(&["x".into(), "--port".into(), "9090".into()]),
            "0.0.0.0:9090"
        );
        assert_eq!(
            parse_bind(&[
                "x".into(),
                "--bind".into(),
                "127.0.0.1".into(),
                "-p".into(),
                "3000".into(),
            ]),
            "127.0.0.1:3000"
        );
    }

    #[test]
    fn parse_head_single_pass() {
        let block = b"POST /x?a=1 HTTP/1.1\r\nHost: blog.example.com\r\nContent-Length: 42\r\n\r\n";
        let head = parse_head(block).expect("head");
        assert_eq!(head.method, Method::Post);
        assert_eq!(head.path, "/x?a=1");
        assert_eq!(head.content_length, Some(42));
        assert!(!head.chunked);
        assert_eq!(head.host, "blog.example.com");

        // Case-insensitive header names; chunked detection.
        let block = b"GET / HTTP/1.1\r\ncontent-length:  7 \r\nTRANSFER-ENCODING: chunked\r\n\r\n";
        let head = parse_head(block).expect("head");
        assert_eq!(head.content_length, Some(7));
        assert!(head.chunked);

        // No body headers.
        let head = parse_head(b"GET /y HTTP/1.1\r\nHost: h\r\n\r\n").expect("head");
        assert_eq!(head.content_length, None);
        assert_eq!(head.path, "/y");
        assert_eq!(head.host, "h");
    }

    #[test]
    fn find_subslice_finds_header_terminator() {
        let b = b"GET / HTTP/1.1\r\nHost: h\r\n\r\nbody";
        let pos = find_subslice(b, b"\r\n\r\n").unwrap();
        assert_eq!(&b[pos + 4..], b"body");
    }

    #[test]
    fn site_hosts_route_to_the_site_handler() {
        // `serves_host` is the routing decision: a `<name>.example.com` host (or a
        // verified custom domain) goes to the static data plane; the machines API,
        // operator domains, raw-IP, and `localhost` fall through.
        let handler = SiteHostHandler::new(Arc::new(SiteRegistry::new()));
        assert!(handler.serves_host("blog.example.com"));
        assert!(handler.serves_host("hello.example.com:443"));
        assert!(!handler.serves_host("example.com"));
        assert!(!handler.serves_host("www.example.com"));
        assert!(!handler.serves_host("dreggnet.example.com"));
        assert!(!handler.serves_host("<EDGE_HOST>"));
        assert!(!handler.serves_host("localhost"));
        assert!(!handler.serves_host("localhost:8080"));
        assert!(!handler.serves_host(""));
    }

    #[test]
    fn site_exists_ask_gates_cert_issuance() {
        use dregg_domains::{ChallengeMethod, DOMAINS_CAP, DomainCap, DomainRegistry, MockDns};
        use dreggnet_webauth::cred::RootKey;
        use dreggnet_webauth::grant::mint_caps;

        let registry = Arc::new(SiteRegistry::new());
        registry
            .publish(
                &PublishCap::for_site("agent:dreggnet", "hello"),
                "hello",
                SiteContent::new().with("/index.html", "<h1>hi</h1>"),
            )
            .expect("publish");
        // A custom domain bound + verified; another bound but still Pending. Binds
        // are gated by a real root-minted credential (the cap chain), not a token.
        let root = RootKey::from_seed([9u8; 32]);
        let domains = Arc::new(DomainRegistry::with_authority(root.public()));
        let cred = || mint_caps(&root, [DOMAINS_CAP], None).encode();
        let r = domains
            .bind(
                &DomainCap::new(cred(), "blog.example.com"),
                "blog.example.com",
                "hello",
                ChallengeMethod::Txt,
            )
            .expect("bind");
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        domains.verify("blog.example.com", &dns).expect("verify");
        domains
            .bind(
                &DomainCap::new(cred(), "pending.example.com"),
                "pending.example.com",
                "hello",
                ChallengeMethod::Txt,
            )
            .expect("bind");
        let handler = SiteHostHandler::with_domains(registry, domains);

        let ask = |q: &str| -> String {
            let mut buf = vec![0u8; 1024];
            let mut w = ResponseWriter::new(&mut buf);
            let res = site_exists_ask(&handler, q, &mut w);
            String::from_utf8_lossy(&buf[..res.bytes_written()]).to_string()
        };
        // Published wildcard site → 200.
        assert!(ask("/internal/site-exists?domain=hello.example.com").contains("200"));
        assert!(ask("/internal/site-exists?domain=nope.example.com").contains("404"));
        assert!(ask("/internal/site-exists?domain=example.com").contains("404"));
        // Verified custom domain → 200 (cert minted); unverified/squatted → 404.
        assert!(ask("/internal/site-exists?domain=blog.example.com").contains("200"));
        assert!(ask("/internal/site-exists?domain=pending.example.com").contains("404"));
        assert!(ask("/internal/site-exists?domain=squat.attacker.com").contains("404"));
    }

    // -- A1: the truncation fix (the renderers) -----------------------------

    #[test]
    fn render_pure_grows_to_fit_a_large_body() {
        // A response far larger than the initial buffer must be captured whole,
        // with a Content-Length matching the bytes actually written.
        let body = vec![0x5Au8; 700 * 1024];
        let out = render_pure(64 * 1024, |w| {
            w.status(StatusCode::Ok)
                .header_line(content_type::APPLICATION_OCTET_STREAM)
                .content_length(body.len())
                .body(&body);
            HandlerResult::Written(w.position())
        });
        let text = String::from_utf8_lossy(&out);
        let sep = find_subslice(&out, b"\r\n\r\n").unwrap();
        let served_body = &out[sep + 4..];
        assert!(text.contains(&format!("Content-Length: {}", body.len())));
        assert_eq!(
            served_body,
            &body[..],
            "body must be byte-identical, not truncated"
        );
    }

    #[test]
    fn render_once_reports_overflow_instead_of_truncating() {
        let body = vec![0u8; 4096];
        // Buffer too small for the body → None (caller substitutes a 500).
        let res = render_once(512, |w| {
            w.status(StatusCode::Ok)
                .content_length(body.len())
                .body(&body);
            HandlerResult::Written(w.position())
        });
        assert!(res.is_none());
        // The 500 fallback is itself well-formed.
        let five = response_too_large();
        assert_eq!(status_of(&five), 500);
    }

    // -- A5: chunked request decoding ---------------------------------------

    #[test]
    fn chunked_decode_from_leftover() {
        let mut empty: &[u8] = &[];
        let raw = b"4\r\nWiki\r\n5\r\npedia\r\n0\r\n\r\n";
        let out = read_chunked_body(&mut empty, raw, 1 << 20, far_deadline()).unwrap();
        match out {
            BodyOutcome::Body(b) => assert_eq!(b, b"Wikipedia"),
            _ => panic!("expected a decoded body"),
        }
    }

    #[test]
    fn chunked_decode_streamed_across_reads() {
        // The framing arrives from the stream (not pre-buffered).
        let raw = b"3\r\nabc\r\n3\r\ndef\r\n0\r\n\r\n".to_vec();
        let mut cursor = std::io::Cursor::new(raw);
        let empty: &[u8] = &[];
        let out = read_chunked_body(&mut cursor, empty, 1 << 20, far_deadline()).unwrap();
        match out {
            BodyOutcome::Body(b) => assert_eq!(b, b"abcdef"),
            _ => panic!("expected a decoded body"),
        }
    }

    #[test]
    fn chunked_over_cap_is_too_large() {
        let mut empty: &[u8] = &[];
        let raw = b"a\r\n0123456789\r\n0\r\n\r\n"; // 10 bytes, cap 4
        let out = read_chunked_body(&mut empty, raw, 4, far_deadline()).unwrap();
        assert!(matches!(out, BodyOutcome::TooLarge));
    }

    #[test]
    fn sized_body_over_cap_is_too_large() {
        let mut empty: &[u8] = &[];
        let out = read_sized_body(&mut empty, &[], 1000, 100, far_deadline()).unwrap();
        assert!(matches!(out, BodyOutcome::TooLarge));
    }

    fn far_deadline() -> Instant {
        Instant::now() + Duration::from_secs(30)
    }

    // -- A1..A6: end-to-end over a real socket ------------------------------

    /// A small, fast-limit context with `big.example.com` serving a >256 KiB
    /// asset. Returns the bound address; the server thread runs for the test's
    /// lifetime.
    fn spawn_server(
        big_asset: Vec<u8>,
        max_body: usize,
        max_conns: usize,
    ) -> (SocketAddr, Vec<u8>) {
        let registry = Arc::new(SiteRegistry::new());
        registry
            .publish(
                &PublishCap::for_site("agent:test", "big"),
                "big",
                SiteContent::new().with("/big.bin", big_asset.clone()),
            )
            .expect("publish");
        let site_handler = Arc::new(SiteHostHandler::new(Arc::clone(&registry)));
        let storage_handler = Arc::new(StorageHandler::with_budget(
            Arc::new(BucketRegistry::signed([1u8; 32])),
            None,
            dreggnet_gateway::storage::DEFAULT_BUDGET_UNITS,
        ));
        // Not exercised by the connection-loop tests, but the Ctx needs them: a
        // publish handler (no funding ⇒ would fail closed) and an empty api handler.
        let publish_handler = Arc::new(SitePublishHandler::new(Arc::clone(&registry), None, None));
        let api_handler = Arc::new(ApiHandler::new(
            Arc::clone(&registry),
            Arc::new(dregg_domains::DomainRegistry::new()),
            Arc::clone(storage_handler.registry()),
        ));
        let handler = Arc::new(MachinesHandler::fresh());
        let runtime = Arc::new(
            tokio::runtime::Builder::new_multi_thread()
                .worker_threads(2)
                .enable_all()
                .build()
                .unwrap(),
        );
        let limits = Limits {
            read_timeout: Duration::from_millis(200),
            write_timeout: Duration::from_millis(500),
            request_deadline: Duration::from_millis(400),
            max_header_bytes: 64 * 1024,
            max_body_bytes: max_body,
            max_connections: max_conns,
        };
        let ctx = Arc::new(Ctx {
            handler,
            site_handler,
            storage_handler,
            publish_handler,
            api_handler,
            runtime,
            metrics: Arc::new(Metrics::new()),
            limits,
        });
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        std::thread::spawn(move || run_server(listener, ctx));
        (addr, big_asset)
    }

    /// Send `request` bytes, read the full response (server closes after one
    /// request), return the raw response.
    fn round_trip(addr: SocketAddr, request: &[u8]) -> Vec<u8> {
        let mut conn = TcpStream::connect(addr).unwrap();
        conn.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        conn.write_all(request).unwrap();
        let mut resp = Vec::new();
        conn.read_to_end(&mut resp).unwrap();
        resp
    }

    fn split_body(resp: &[u8]) -> (&[u8], &[u8]) {
        let sep = find_subslice(resp, b"\r\n\r\n").expect("header terminator");
        (&resp[..sep], &resp[sep + 4..])
    }

    #[test]
    fn a1_large_asset_serves_complete() {
        // 300 KiB > the 256 KiB working buffer — would be truncated by the old
        // slice writer. It must arrive byte-for-byte with a matching length.
        let asset: Vec<u8> = (0..300 * 1024).map(|i| (i % 251) as u8).collect();
        let (addr, asset) = spawn_server(asset, 4 * 1024 * 1024, 64);
        let resp = round_trip(
            addr,
            b"GET /big.bin HTTP/1.1\r\nHost: big.example.com\r\nConnection: close\r\n\r\n",
        );
        let (headers, body) = split_body(&resp);
        let headers = String::from_utf8_lossy(headers);
        assert!(headers.contains("200 OK"), "headers: {headers}");
        assert!(
            headers.contains(&format!("Content-Length: {}", asset.len())),
            "headers: {headers}"
        );
        assert_eq!(body.len(), asset.len(), "short read — body was truncated");
        assert_eq!(body, &asset[..], "body not byte-identical");
    }

    #[test]
    fn a2_slow_loris_is_dropped_with_408() {
        let (addr, _) = spawn_server(vec![1, 2, 3], 4096, 64);
        let mut conn = TcpStream::connect(addr).unwrap();
        conn.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        // A partial header that never terminates: the server hits its read
        // timeout / deadline and responds 408, then closes.
        conn.write_all(b"GET / HTTP/1.1\r\nHost: localhost\r\n")
            .unwrap();
        let mut resp = Vec::new();
        conn.read_to_end(&mut resp).unwrap();
        let text = String::from_utf8_lossy(&resp);
        assert!(text.contains("408"), "expected 408, got: {text}");
    }

    #[test]
    fn a3_oversized_body_is_413() {
        let (addr, _) = spawn_server(vec![1], 1024, 64); // body cap = 1 KiB
        // Declare a body far over the cap; the server rejects before reading it.
        let resp = round_trip(
            addr,
            b"POST /v1/apps/x/machines HTTP/1.1\r\nHost: localhost\r\nContent-Length: 5000000\r\n\r\n",
        );
        let text = String::from_utf8_lossy(&resp);
        assert!(text.contains("413"), "expected 413, got: {text}");
    }

    #[test]
    fn a5_chunked_request_is_handled_end_to_end() {
        let (addr, _) = spawn_server(vec![1], 4 * 1024 * 1024, 64);
        // A chunked-encoded create body — the server decodes it and returns a
        // complete, well-formed response (not a hang / short read).
        let resp = round_trip(
            addr,
            b"POST /v1/apps/demo/machines HTTP/1.1\r\nHost: localhost\r\n\
              Transfer-Encoding: chunked\r\n\r\n2\r\n{}\r\n0\r\n\r\n",
        );
        let text = String::from_utf8_lossy(&resp);
        assert!(text.starts_with("HTTP/1.1 "), "no HTTP response: {text}");
    }

    #[test]
    fn a6_metrics_endpoint_serves_prometheus() {
        let (addr, _) = spawn_server(vec![1], 4 * 1024 * 1024, 64);
        // Serve a request first so a counter is non-zero.
        let _ = round_trip(
            addr,
            b"GET /not-a-route HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n",
        );
        let resp = round_trip(
            addr,
            b"GET /metrics HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n",
        );
        let (headers, body) = split_body(&resp);
        let headers = String::from_utf8_lossy(headers);
        let body = String::from_utf8_lossy(body);
        assert!(headers.contains("200 OK"), "headers: {headers}");
        assert!(
            body.contains("# TYPE gateway_requests_total counter"),
            "body: {body}"
        );
        assert!(
            body.contains("gateway_request_duration_seconds_count"),
            "body: {body}"
        );
    }
}
