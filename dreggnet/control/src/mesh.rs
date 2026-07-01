//! `mesh` — the secure control-plane↔fleet plane (ARCHITECTURE.md: "wireguard /
//! tailscale mesh between control plane and the Hetzner fleet").
//!
//! The control plane provisions a machine ([`crate::VmProvider`]); to actually
//! *reach* it — dispatch a workload onto it, health-check it, serve a workload's
//! ingress through it — it needs a secure link to that machine that does not
//! depend on the machine having a public, internet-exposed bridge port. That link
//! is a WireGuard overlay: every fleet node and the control plane share one
//! encrypted private network (the `100.64.0.0/10` carrier-grade-NAT overlay, the
//! same range Tailscale uses), and the control plane addresses a node by its
//! *overlay* address rather than its public IP.
//!
//! ## What this module is
//!
//! - [`MeshKeypair`] / [`MeshConfig`] — the control plane's own WireGuard identity
//!   (an x25519 keypair) and overlay parameters (its overlay address, listen port,
//!   the overlay CIDR it routes to the fleet). Cross-platform, real.
//! - [`MeshNode`] — a fleet node to reach: its WireGuard public key, its public
//!   UDP endpoint, and its overlay address. A worker registers this with the
//!   control plane on boot.
//! - [`MeshConfig::wireguard_ini`] — renders the standard WireGuard `[Interface]`
//!   + `[Peer]` config that brings up the link to one node. This is exactly the
//!   INI DreggNet's own [`crate::wg::WireGuardConfig::from_ini`] parses, so the
//!   config round-trips into a real userspace engine (boringtun-backed).
//! - [`Mesh`] / [`MeshLink`] — the link abstraction: `connect(node) -> MeshLink`,
//!   then `health_check()` / `dispatch_target(port)` over the established link.
//! - [`TailscaleMesh`] — the **live** backend the edge↔node-a deploy uses: it
//!   rides the host's existing tailnet/headscale overlay (no per-process tunnel),
//!   addresses each node by its tailnet IP, and is cross-platform.
//! - [`StubMesh`] — a cross-platform backend for the macOS dev host and unit tests;
//!   [`StubMesh::dispatching_to`] points its links at a local fulfill stub so the
//!   real POST code path is exercised offline.
//! - [`WireguardMesh`] — the self-managed-tunnel alternative: backs `connect` with
//!   a real [`crate::wg::WireGuardEngine`] (boringtun-backed) built from the config.
//!
//! ## The dispatch path (real)
//!
//! [`dispatch_lease_over_mesh`] (wired into [`crate::Ec2Provider::run_lease`])
//! establishes the link, health-checks the node over it, then issues the real
//! `POST <overlay-addr>:8021/fulfill` carrying the lease and decodes the durable
//! metered [`DurableOutput`] the remote bridge agent (the node-agent) returns.
//! All three legs are real over a live link; a 4xx refusal maps to a lapse. A plain
//! [`StubMesh`] link (no live tunnel, no override) has no dispatch carrier, so a
//! dispatch over it surfaces as the named live-overlay step (the honest macOS-dev
//! / no-tailnet default). Proven live edge→node-a through the control plane (see
//! `deploy/COMPUTE-BACKEND.md`); the unit tests drive the POST against a local
//! fulfill stub.

use std::collections::HashMap;
use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Mutex;

use async_trait::async_trait;
use base64::Engine as _;
use base64::engine::general_purpose::STANDARD as BASE64;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroizing;

use crate::provider::{MachineId, ProviderError};
use dreggnet_bridge::{DurableOutput, Lease};

/// The overlay CIDR the fleet lives in — the carrier-grade-NAT range Tailscale /
/// WireGuard meshes conventionally use. The control plane routes this whole range
/// across the mesh; each node owns one `/32` host route inside it.
pub const OVERLAY_CIDR: &str = "100.64.0.0/10";

/// The default WireGuard UDP listen port (the canonical WireGuard port).
pub const DEFAULT_LISTEN_PORT: u16 = 51820;

/// The default port the fleet worker's bridge agent listens on, on the overlay.
/// This is where the control plane dispatches a workload / health-checks a node.
pub const DEFAULT_AGENT_PORT: u16 = 8021;

/// Why a mesh operation failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MeshError {
    /// The rendered config / keypair was malformed (bad key, bad address).
    Setup(String),
    /// The link was established but the node could not be reached over it (no
    /// live tunnel yet — the live two-node handshake is the deploy step).
    Unreachable(String),
    /// The underlying WireGuard engine failed to come up.
    Backend(String),
}

impl std::fmt::Display for MeshError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MeshError::Setup(m) => write!(f, "mesh setup error: {m}"),
            MeshError::Unreachable(m) => write!(f, "mesh node unreachable: {m}"),
            MeshError::Backend(m) => write!(f, "mesh backend error: {m}"),
        }
    }
}

impl std::error::Error for MeshError {}

/// An x25519 keypair — a WireGuard identity. The public key is what a peer needs
/// to authenticate this end; the private key never leaves this process (it is
/// held in [`Zeroizing`] so it is wiped on drop).
pub struct MeshKeypair {
    secret: StaticSecret,
    public: PublicKey,
}

impl MeshKeypair {
    /// Generate a fresh WireGuard keypair.
    pub fn generate() -> MeshKeypair {
        let secret = StaticSecret::random_from_rng(crypto_rng());
        let public = PublicKey::from(&secret);
        MeshKeypair { secret, public }
    }

    /// Reconstruct a keypair from a base64-encoded 32-byte private key (the
    /// standard WireGuard `PrivateKey` encoding).
    pub fn from_private_base64(b64: &str) -> Result<MeshKeypair, MeshError> {
        let bytes = decode_key_bytes(b64)?;
        let secret = StaticSecret::from(bytes);
        let public = PublicKey::from(&secret);
        Ok(MeshKeypair { secret, public })
    }

    /// The base64 public key — what a peer registers to authenticate this end.
    pub fn public_base64(&self) -> String {
        BASE64.encode(self.public.as_bytes())
    }

    /// The base64 private key (held in [`Zeroizing`] so the rendered string is
    /// wiped on drop). Used to render the `[Interface] PrivateKey` of the config.
    pub fn private_base64(&self) -> Zeroizing<String> {
        Zeroizing::new(BASE64.encode(self.secret.to_bytes()))
    }
}

impl std::fmt::Debug for MeshKeypair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Never render the private half.
        f.debug_struct("MeshKeypair")
            .field("public", &self.public_base64())
            .finish_non_exhaustive()
    }
}

/// A fleet node the control plane wants to reach over the mesh.
///
/// `Serialize`/`Deserialize` + [`Record`] so a registered node persists in the
/// durable [`MeshNodeRegistry`], surviving a control-plane restart (the data-plane
/// durability blocker — otherwise a worker's mesh identity is lost on reboot and the
/// control plane can no longer reach a node it provisioned).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MeshNode {
    /// The provisioned machine this node is.
    pub machine: MachineId,
    /// The node's WireGuard public key (base64), as it registered on boot.
    pub public_key: String,
    /// The node's public UDP endpoint (`ip:port`) the handshake dials.
    pub endpoint: String,
    /// The node's address on the overlay (e.g. `100.64.0.2`).
    pub overlay_addr: Ipv4Addr,
    /// The port the node's bridge agent listens on, on the overlay.
    pub agent_port: u16,
}

impl MeshNode {
    /// A node reachable at `endpoint` (public UDP) and `overlay_addr` (its mesh
    /// address), authenticated by `public_key`, with the agent on the default port.
    pub fn new(
        machine: MachineId,
        public_key: impl Into<String>,
        endpoint: impl Into<String>,
        overlay_addr: Ipv4Addr,
    ) -> MeshNode {
        MeshNode {
            machine,
            public_key: public_key.into(),
            endpoint: endpoint.into(),
            overlay_addr,
            agent_port: DEFAULT_AGENT_PORT,
        }
    }
}

/// The control plane's own mesh identity + overlay parameters.
#[derive(Debug)]
pub struct MeshConfig {
    /// The control plane's WireGuard identity.
    pub keypair: MeshKeypair,
    /// The control plane's address on the overlay (e.g. `100.64.0.1`).
    pub overlay_addr: Ipv4Addr,
    /// The UDP port this end listens on.
    pub listen_port: u16,
    /// PersistentKeepalive (seconds) to hold the tunnel open through NAT.
    pub keepalive_secs: u16,
}

impl MeshConfig {
    /// A control-plane mesh config with a freshly-generated identity, bound to
    /// `overlay_addr` on the overlay (conventionally `100.64.0.1`).
    pub fn generate(overlay_addr: Ipv4Addr) -> MeshConfig {
        MeshConfig {
            keypair: MeshKeypair::generate(),
            overlay_addr,
            listen_port: DEFAULT_LISTEN_PORT,
            keepalive_secs: 25,
        }
    }

    /// The control plane's base64 public key — what a fleet node registers as its
    /// peer to authenticate the control plane.
    pub fn public_key_base64(&self) -> String {
        self.keypair.public_base64()
    }

    /// Render the standard WireGuard INI that brings up the link to `node`. This
    /// is exactly the format [`crate::wg::WireGuardConfig::from_ini`] parses, so it
    /// round-trips into a real userspace engine on any host; it is also the
    /// inspectable, deployable artifact.
    ///
    /// The peer's `AllowedIPs` is the node's `/32` host route, so traffic to that
    /// one overlay address is routed through this peer's tunnel.
    pub fn wireguard_ini(&self, node: &MeshNode) -> Zeroizing<String> {
        Zeroizing::new(format!(
            "[Interface]\n\
             PrivateKey = {priv}\n\
             ListenPort = {port}\n\
             Address = {addr}/32\n\
             \n\
             [Peer]\n\
             PublicKey = {peer_pub}\n\
             Endpoint = {endpoint}\n\
             AllowedIPs = {node_addr}/32\n\
             PersistentKeepalive = {keepalive}\n",
            priv = self.keypair.private_base64().as_str(),
            port = self.listen_port,
            addr = self.overlay_addr,
            peer_pub = node.public_key,
            endpoint = node.endpoint,
            node_addr = node.overlay_addr,
            keepalive = self.keepalive_secs,
        ))
    }
}

/// The secure-plane abstraction: establish a link to a fleet node.
#[async_trait]
pub trait Mesh: Send + Sync {
    /// The backend name (e.g. `"wireguard"`, `"stub"`).
    fn backend(&self) -> &'static str;

    /// Establish a link to `node` over the mesh. On Linux this builds a real
    /// WireGuard engine from the rendered config; the live handshake against the
    /// node completes once both ends are up (the deploy step).
    async fn connect(&self, node: &MeshNode) -> Result<MeshLink, MeshError>;
}

/// How a [`MeshLink`] is backed.
#[derive(Debug)]
enum LinkState {
    /// No live tunnel (macOS dev host / tests). `reachable` simulates whether the
    /// node would answer the health-check, so the control-uses-mesh path can be
    /// exercised offline. `dispatch_to`, when set, is a concrete TCP address the
    /// dispatch POST is actually sent to (a *local* fulfill stub) — this is how a
    /// unit test drives the real POST code path without a live overlay.
    Stub {
        reachable: bool,
        dispatch_to: Option<SocketAddr>,
    },
    /// The host is already on the tailnet/headscale overlay (e.g. `tailscale0` is
    /// up and routes the overlay CIDR). The link addresses the node by its tailnet
    /// IP and lets the host carry the bytes — no per-process tunnel, so this is
    /// cross-platform and is what the live edge↔node-a deploy uses. `health_check`
    /// and the dispatch POST are real TCP over the host overlay.
    Tailscale,
    /// A real WireGuard engine is up for this link. `peer_count` is the number of
    /// peers the engine was built with (1 for a single-node link).
    Wireguard { peer_count: usize },
}

/// An established link to one fleet node. Address the node at its overlay address
/// via [`target`](MeshLink::target); check it is answering via
/// [`health_check`](MeshLink::health_check).
#[derive(Debug)]
pub struct MeshLink {
    node: MeshNode,
    backend: &'static str,
    state: LinkState,
}

impl MeshLink {
    /// The node this link reaches.
    pub fn node(&self) -> &MeshNode {
        &self.node
    }

    /// The backend that established this link.
    pub fn backend(&self) -> &'static str {
        self.backend
    }

    /// The overlay socket address to reach a service on the node at `port`.
    pub fn target(&self, port: u16) -> SocketAddr {
        SocketAddr::new(self.node.overlay_addr.into(), port)
    }

    /// The concrete TCP address the dispatch POST is sent to, or `None` if this
    /// link cannot actually carry the workload (a plain stub with no live tunnel
    /// and no local override — the macOS dev host / honest default).
    ///
    /// - A live WireGuard link routes to the node's overlay address ([`target`]).
    /// - A stub link routes to its `dispatch_to` override when one is set (a local
    ///   fulfill stub a test stands up), and is non-dispatchable otherwise.
    pub fn dispatch_target(&self, port: u16) -> Option<SocketAddr> {
        match self.state {
            LinkState::Stub { dispatch_to, .. } => dispatch_to,
            LinkState::Tailscale => Some(self.target(port)),
            LinkState::Wireguard { .. } => Some(self.target(port)),
        }
    }

    /// The number of WireGuard peers backing this link (the single node for a
    /// per-node link). `0` for a [`StubMesh`] link (no live engine).
    pub fn peer_count(&self) -> usize {
        match self.state {
            LinkState::Stub { .. } => 0,
            // The host overlay carries a tailscale link — no per-process peers.
            LinkState::Tailscale => 0,
            LinkState::Wireguard { peer_count } => peer_count,
        }
    }

    /// Whether a live tunnel is up (always `false` for a [`StubMesh`] link). A
    /// [`TailscaleMesh`] link is live: the host overlay carries it.
    pub fn is_live(&self) -> bool {
        match self.state {
            LinkState::Stub { .. } => false,
            LinkState::Tailscale => true,
            LinkState::Wireguard { .. } => true,
        }
    }

    /// Check the node is answering on its bridge-agent port over the link. On a
    /// live link (a [`TailscaleMesh`] over the host overlay, or a Linux WireGuard
    /// tunnel) this is a real TCP probe to the node's overlay address; on a stub
    /// link it reports the simulated reachability (no live tunnel exists).
    pub async fn health_check(&self) -> Result<(), MeshError> {
        match &self.state {
            LinkState::Stub { reachable, .. } => {
                if *reachable {
                    Ok(())
                } else {
                    Err(MeshError::Unreachable(format!(
                        "no live tunnel to {} (stub link; the live two-node handshake is the deploy step)",
                        self.target(self.node.agent_port)
                    )))
                }
            }
            LinkState::Tailscale => self.tcp_probe().await,
            LinkState::Wireguard { .. } => self.tcp_probe().await,
        }
    }

    /// A real TCP probe to the node's bridge-agent port over the overlay — the
    /// liveness check a live link uses.
    async fn tcp_probe(&self) -> Result<(), MeshError> {
        let target = self.target(self.node.agent_port);
        let probe = tokio::time::timeout(
            std::time::Duration::from_secs(5),
            tokio::net::TcpStream::connect(target),
        )
        .await;
        match probe {
            Ok(Ok(_stream)) => Ok(()),
            Ok(Err(e)) => Err(MeshError::Unreachable(format!("{target}: {e}"))),
            Err(_) => Err(MeshError::Unreachable(format!("{target}: timed out"))),
        }
    }
}

/// A cross-platform mesh with no live tunnel — the macOS dev host / unit-test
/// backend (the net/ crates are Linux-only). `connect` records the link; whether
/// `health_check` succeeds is governed by the simulated reachability.
#[derive(Debug, Default)]
pub struct StubMesh {
    reachable: bool,
    dispatch_to: Option<SocketAddr>,
}

impl StubMesh {
    /// A stub whose links report the node as unreachable (the honest default: no
    /// live tunnel exists off the fleet).
    pub fn new() -> StubMesh {
        StubMesh {
            reachable: false,
            dispatch_to: None,
        }
    }

    /// A stub whose links report the node as reachable — for exercising the
    /// control-uses-mesh health-check path offline. Its links carry no dispatch
    /// target, so a dispatch over such a link is the honest "no live tunnel" case.
    pub fn reachable() -> StubMesh {
        StubMesh {
            reachable: true,
            dispatch_to: None,
        }
    }

    /// A stub whose links are reachable *and* send the dispatch POST to `addr` — a
    /// concrete local fulfill stub. This is how a unit test drives the real POST
    /// code path (`POST /fulfill`) against a loopback server that speaks the same
    /// `:8021/fulfill` contract the node-agent does, with no live overlay.
    pub fn dispatching_to(addr: SocketAddr) -> StubMesh {
        StubMesh {
            reachable: true,
            dispatch_to: Some(addr),
        }
    }
}

#[async_trait]
impl Mesh for StubMesh {
    fn backend(&self) -> &'static str {
        "stub"
    }

    async fn connect(&self, node: &MeshNode) -> Result<MeshLink, MeshError> {
        Ok(MeshLink {
            node: node.clone(),
            backend: "stub",
            state: LinkState::Stub {
                reachable: self.reachable,
                dispatch_to: self.dispatch_to,
            },
        })
    }
}

/// The mesh that rides the host's existing tailnet/headscale overlay — the backend
/// the **live** edge↔node-a deploy uses. It does not stand up its own tunnel: it
/// assumes the host is already on the overlay (`tailscale0` is up and routes the
/// overlay CIDR, as on the DreggNet edge `100.64.0.1` reaching node-a
/// `100.64.0.2`), addresses each node by its tailnet IP, and lets the host carry the
/// bytes. So it is cross-platform (no Linux-only WireGuard engine) and its links are
/// live: `health_check` is a real TCP probe and the dispatch POST is real HTTP over
/// the overlay.
///
/// This is the deploy-time complement to [`WireguardMesh`] (which manages its own
/// per-process WireGuard tunnel from a [`MeshConfig`]): on a host already joined to
/// a tailnet, the overlay is the host's, and `TailscaleMesh` simply uses it.
#[derive(Debug, Default)]
pub struct TailscaleMesh;

impl TailscaleMesh {
    /// A tailscale-overlay mesh. The host must already be on the tailnet (the join
    /// is the operator step, e.g. `tailscale up` / `headscale` enrollment).
    pub fn new() -> TailscaleMesh {
        TailscaleMesh
    }
}

#[async_trait]
impl Mesh for TailscaleMesh {
    fn backend(&self) -> &'static str {
        "tailscale"
    }

    async fn connect(&self, node: &MeshNode) -> Result<MeshLink, MeshError> {
        Ok(MeshLink {
            node: node.clone(),
            backend: "tailscale",
            state: LinkState::Tailscale,
        })
    }
}

/// The self-managed-tunnel mesh, backed by a real userspace WireGuard engine.
/// `connect` renders the config and builds a real [`crate::wg::WireGuardEngine`]
/// (DreggNet's own boringtun-backed wrapper). Cross-platform: boringtun is
/// userspace, so unlike the old Elide net/ stack this builds on every host.
pub struct WireguardMesh {
    config: MeshConfig,
}

impl WireguardMesh {
    /// A WireGuard mesh that brings links up under `config` (the control plane's
    /// identity + overlay parameters).
    pub fn new(config: MeshConfig) -> WireguardMesh {
        WireguardMesh { config }
    }
}

#[async_trait]
impl Mesh for WireguardMesh {
    fn backend(&self) -> &'static str {
        "wireguard"
    }

    async fn connect(&self, node: &MeshNode) -> Result<MeshLink, MeshError> {
        // Render the config and parse it back through our own `wg` module, then
        // build the real userspace engine. Bringing the TUN device up and
        // completing the Noise handshake against the live node is the deploy step.
        let ini = self.config.wireguard_ini(node);
        let wg_config = crate::wg::WireGuardConfig::from_ini(ini.as_str())
            .map_err(|e| MeshError::Setup(e.to_string()))?;
        let engine = crate::wg::WireGuardEngine::new(wg_config)
            .map_err(|e| MeshError::Backend(e.to_string()))?;
        Ok(MeshLink {
            node: node.clone(),
            backend: "wireguard",
            state: LinkState::Wireguard {
                peer_count: engine.peer_count(),
            },
        })
    }
}

/// Build the default mesh for this platform under `config`: a real
/// [`WireguardMesh`] on Linux (the deploy target), a [`StubMesh`] elsewhere (the
/// macOS dev host). This is the constructor the control plane uses so the same
/// call site compiles on both.
#[cfg(target_os = "linux")]
pub fn default_mesh(config: MeshConfig) -> std::sync::Arc<dyn Mesh> {
    std::sync::Arc::new(WireguardMesh::new(config))
}

/// Build the default mesh for this platform (non-Linux: a [`StubMesh`]).
#[cfg(not(target_os = "linux"))]
pub fn default_mesh(_config: MeshConfig) -> std::sync::Arc<dyn Mesh> {
    std::sync::Arc::new(StubMesh::new())
}

/// Reach a provisioned `node` over the `mesh` and dispatch `lease`'s durable
/// workload to its bridge agent. This is the control-plane-uses-the-mesh path:
/// it establishes the link, health-checks the node over it, and then issues the
/// real `POST <overlay-addr>:8021/fulfill` carrying the lease, returning the
/// durable metered result the remote bridge agent (the node-agent) produces.
///
/// All three legs are real:
/// - **connect** — on Linux this builds a real WireGuard engine from the rendered
///   config; on a stub link it records the link.
/// - **health-check** — the node must answer over the link before it is handed work.
/// - **dispatch** — a real HTTP `POST /fulfill` to the link's dispatch target (the
///   node's overlay address for a live WireGuard link; a local fulfill stub for a
///   [`StubMesh::dispatching_to`] link in a unit test). The node-agent runs the
///   lease as a durable polyana workflow and returns the metered [`DurableOutput`].
///
/// A plain stub link (the macOS dev host / honest default — no live tunnel, no
/// override) has no dispatch carrier, so dispatch over it surfaces as the named
/// live-overlay step ([`ProviderError::Unimplemented`] carrying the exact POST it
/// would issue over a live link). The in-process path is
/// [`crate::LocalProvider::run_lease`].
pub async fn dispatch_lease_over_mesh(
    mesh: &dyn Mesh,
    node: &MeshNode,
    lease: &Lease,
    instance: &str,
) -> Result<DurableOutput, ProviderError> {
    let link = mesh
        .connect(node)
        .await
        .map_err(|e| ProviderError::Bridge(format!("mesh connect to {}: {e}", node.endpoint)))?;

    // The node must answer over the link before we hand it work.
    link.health_check()
        .await
        .map_err(|e| ProviderError::Bridge(format!("mesh health-check: {e}")))?;

    // Where the dispatch POST actually goes. A live link carries it to the node's
    // overlay address; a stub-with-override carries it to a local fulfill stub. A
    // plain stub cannot carry the workload — that is the live-overlay deploy step.
    let target = match link.dispatch_target(node.agent_port) {
        Some(target) => target,
        None => {
            return Err(ProviderError::Unimplemented {
                provider: "mesh",
                would_run: format!(
                    "POST http://{}/fulfill (lessee={}, instance={instance}) over the {} mesh link \
                     — the link has no live tunnel (bring up the two-node WireGuard handshake)",
                    link.target(node.agent_port),
                    lease.lessee,
                    link.backend(),
                ),
            });
        }
    };

    post_fulfill(target, lease, instance, link.backend()).await
}

/// Issue the real `POST <target>/fulfill` carrying `lease`, and decode the durable
/// metered [`DurableOutput`] the bridge agent returns. This speaks exactly the
/// `:8021/fulfill` contract the node-agent serves (`deploy/node-agent`):
/// the request body is the JSON lease descriptor, the response body is the metered
/// `{ step1, step2, outputs, meter_units, … }`.
///
/// A raw HTTP/1.1 client (no extra dependency) over a `tokio` TCP stream — the same
/// minimal wire the agent itself speaks. A `4xx` refusal (an unfunded / over-budget
/// lease) maps to [`ProviderError::WorkloadLapsed`] so the scheduler reaps it; any
/// other non-`200` or transport fault maps to [`ProviderError::Bridge`].
async fn post_fulfill(
    target: SocketAddr,
    lease: &Lease,
    instance: &str,
    backend: &str,
) -> Result<DurableOutput, ProviderError> {
    let body = serde_json::json!({
        "lessee": lease.lessee,
        "cap_grade": lease.cap_grade.to_string(),
        "asset": lease.asset,
        "budget_units": lease.budget_units,
        "per_period_units": lease.per_period_units,
        "instance": instance,
    })
    .to_string();

    let request = format!(
        "POST /fulfill HTTP/1.1\r\n\
         Host: {target}\r\n\
         Content-Type: application/json\r\n\
         Content-Length: {}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        body.len(),
    );

    let connect = tokio::time::timeout(
        std::time::Duration::from_secs(10),
        tokio::net::TcpStream::connect(target),
    )
    .await
    .map_err(|_| ProviderError::Bridge(format!("dispatch POST to {target}: connect timed out")))?
    .map_err(|e| ProviderError::Bridge(format!("dispatch POST to {target}: connect: {e}")))?;
    let mut stream = connect;

    stream
        .write_all(request.as_bytes())
        .await
        .map_err(|e| ProviderError::Bridge(format!("dispatch POST to {target}: write: {e}")))?;
    stream
        .flush()
        .await
        .map_err(|e| ProviderError::Bridge(format!("dispatch POST to {target}: flush: {e}")))?;

    // The agent answers with `Connection: close`, so read to EOF.
    let mut raw = Vec::with_capacity(8 * 1024);
    tokio::time::timeout(
        std::time::Duration::from_secs(60),
        stream.read_to_end(&mut raw),
    )
    .await
    .map_err(|_| ProviderError::Bridge(format!("dispatch POST to {target}: read timed out")))?
    .map_err(|e| ProviderError::Bridge(format!("dispatch POST to {target}: read: {e}")))?;

    let (status, response_body) = split_http_response(&raw).ok_or_else(|| {
        ProviderError::Bridge(format!(
            "dispatch POST to {target}: malformed HTTP response"
        ))
    })?;

    if status == 200 {
        let out: DurableOutput = serde_json::from_slice(response_body).map_err(|e| {
            ProviderError::Bridge(format!(
                "dispatch POST to {target} over the {backend} link: decode result: {e}"
            ))
        })?;
        Ok(out)
    } else {
        // The agent's error envelope is `{ "ok": false, "error": "..." }`.
        let detail = serde_json::from_slice::<serde_json::Value>(response_body)
            .ok()
            .and_then(|v| {
                v.get("error")
                    .and_then(|e| e.as_str())
                    .map(|s| s.to_string())
            })
            .unwrap_or_else(|| String::from_utf8_lossy(response_body).trim().to_string());
        // A 4xx is the bridge refusing the lease (unfunded / over-budget lapse):
        // the scheduler reads this as a lapse and reaps. A 5xx is infrastructure.
        if (400..500).contains(&status) {
            Err(ProviderError::WorkloadLapsed(format!(
                "lease for `{}` refused by the bridge agent (HTTP {status}): {detail}",
                lease.lessee
            )))
        } else {
            Err(ProviderError::Bridge(format!(
                "dispatch POST to {target} returned HTTP {status}: {detail}"
            )))
        }
    }
}

/// Split a raw HTTP/1.1 response into `(status_code, body_bytes)`. Returns `None` if
/// the status line or the header/body separator is missing.
fn split_http_response(raw: &[u8]) -> Option<(u16, &[u8])> {
    let sep = raw.windows(4).position(|w| w == b"\r\n\r\n")?;
    let head = &raw[..sep];
    let body = &raw[sep + 4..];
    // Status line: `HTTP/1.1 200 OK`.
    let line_end = head
        .windows(2)
        .position(|w| w == b"\r\n")
        .unwrap_or(head.len());
    let status_line = std::str::from_utf8(&head[..line_end]).ok()?;
    let code = status_line.split_whitespace().nth(1)?.parse::<u16>().ok()?;
    Some((code, body))
}

/// A [`MeshNode`] is a durable record keyed by its machine id — the unit the
/// [`MeshNodeRegistry`]'s durable umem cell lays into its heap, so a control-plane
/// restart reconstructs the mesh identities workers registered (and can still reach
/// those nodes) FROM the committed heap rather than losing them with the process.
impl dreggnet_umem::Record for MeshNode {
    fn store_key(&self) -> String {
        self.machine.0.clone()
    }
}

/// A registry mapping a provisioned machine to the mesh identity its worker
/// registered on boot. A provider consults this to find how to reach a machine
/// over the mesh.
///
/// With a durable backend attached ([`with_durable_store`](MeshNodeRegistry::with_durable_store)),
/// the registry IS a **umem cell**: every [`register`](MeshNodeRegistry::register) is
/// laid into the cell's `(collection,key) -> value` heap and committed to the real
/// sorted-Poseidon2 boundary root, so a control-plane restart RECONSTRUCTS the
/// registered nodes FROM the committed heap — the mesh half of the durable data plane
/// (servers are durable the same way via [`crate::server::ServerStore`]). This replaces
/// the from-scratch JSON-lines log with the real substrate (the #2 re-dregg move,
/// `docs/REGISTRIES-AS-UMEM.md`), unlocking fork / time-travel / merge-readiness.
#[derive(Default)]
pub struct MeshNodeRegistry {
    nodes: Mutex<HashMap<MachineId, MeshNode>>,
    store: Option<dreggnet_umem::UmemRegistry<MeshNode>>,
}

impl MeshNodeRegistry {
    pub fn new() -> MeshNodeRegistry {
        MeshNodeRegistry {
            nodes: Mutex::new(HashMap::new()),
            store: None,
        }
    }

    /// Attach a **durable umem backend** at `path` and **reconstruct** the registered
    /// nodes: open the [`UmemRegistry`](dreggnet_umem::UmemRegistry) (the registry AS a
    /// umem cell), restore every persisted [`MeshNode`] FROM the committed heap back
    /// into the live map, and commit every future
    /// [`register`](MeshNodeRegistry::register) to the heap — so a control-plane restart
    /// can still reach the nodes a prior process learned (the data-plane durability
    /// blocker). The restore **fails closed** if the committed heap does not bind its
    /// sealed boundary root (the `root_binds_get` discipline).
    pub fn with_durable_store(
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<MeshNodeRegistry> {
        let store = dreggnet_umem::UmemRegistry::<MeshNode>::open(path).map_err(|e| e.into_io())?;
        let mut nodes = HashMap::new();
        for node in store.all() {
            nodes.insert(node.machine.clone(), node);
        }
        Ok(MeshNodeRegistry {
            nodes: Mutex::new(nodes),
            store: Some(store),
        })
    }

    /// Record (or replace) the mesh identity a worker registered for its machine,
    /// committing it to the umem heap first (when a durable backend is attached) so the
    /// node is reachable again after a control-plane restart. A store fault surfaces as
    /// the returned [`io::Error`](std::io::Error) (the register is refused rather
    /// than reported durable when it is not); the in-memory-only default is infallible.
    pub fn register(&self, node: MeshNode) -> std::io::Result<()> {
        if let Some(store) = &self.store {
            store.append(&node).map_err(|e| e.into_io())?;
        }
        self.nodes
            .lock()
            .expect("mesh node registry poisoned")
            .insert(node.machine.clone(), node);
        Ok(())
    }

    /// The mesh identity registered for `machine`, if any.
    pub fn get(&self, machine: &MachineId) -> Option<MeshNode> {
        self.nodes
            .lock()
            .expect("mesh node registry poisoned")
            .get(machine)
            .cloned()
    }

    /// The durable backend path, if this registry persists its nodes.
    pub fn durable_path(&self) -> Option<&std::path::Path> {
        self.store.as_ref().map(|s| s.path())
    }

    /// The registry's **committed umem boundary root** (hex), if durably backed: the
    /// real sorted-Poseidon2 `compute_heap_root` over the mesh-registry cell's heap.
    /// `None` when in-memory-only.
    pub fn umem_root(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.boundary_root())
    }

    /// **Fork the whole mesh registry** (a umem superpower a `Mutex<HashMap>` can never
    /// give): copy the committed cell at `new_path`, returning a divergent
    /// `MeshNodeRegistry` that starts byte-identical and diverges as either side
    /// registers. `None` when in-memory-only (nothing committed to fork).
    pub fn fork_registry(
        &self,
        new_path: impl AsRef<std::path::Path>,
    ) -> Option<std::io::Result<MeshNodeRegistry>> {
        let store = self.store.as_ref()?;
        Some(match store.fork(new_path) {
            Ok(forked) => {
                let mut nodes = HashMap::new();
                for node in forked.all() {
                    nodes.insert(node.machine.clone(), node);
                }
                Ok(MeshNodeRegistry {
                    nodes: Mutex::new(nodes),
                    store: Some(forked),
                })
            }
            Err(e) => Err(e.into_io()),
        })
    }

    /// **Time-travel — checkpoint** the current registry: the committed boundary root,
    /// retained so [`restore_registry`](Self::restore_registry) can return to it.
    /// `None` when in-memory-only.
    pub fn checkpoint_registry(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.checkpoint())
    }

    /// **Time-travel — restore** the registry to an earlier committed `root`: the
    /// registered nodes revert to that committed state, durably (the rollback survives a
    /// restart), and the in-memory map is reloaded from the restored heap. A no-op
    /// `Ok(())` when in-memory-only.
    pub fn restore_registry(&self, root: &str) -> std::io::Result<()> {
        if let Some(store) = &self.store {
            store.restore(root).map_err(|e| e.into_io())?;
            let mut nodes = self.nodes.lock().expect("mesh node registry poisoned");
            nodes.clear();
            for node in store.all() {
                nodes.insert(node.machine.clone(), node);
            }
        }
        Ok(())
    }
}

/// The RNG used to generate keypairs — the OS CSPRNG.
fn crypto_rng() -> impl rand_core::RngCore + rand_core::CryptoRng {
    // x25519-dalek 2 re-exports the rand_core it expects; OsRng satisfies it.
    rand_core::OsRng
}

/// Decode a base64 32-byte key, the standard WireGuard key encoding.
fn decode_key_bytes(b64: &str) -> Result<[u8; 32], MeshError> {
    let decoded = BASE64
        .decode(b64.trim())
        .map_err(|e| MeshError::Setup(format!("base64 decode: {e}")))?;
    if decoded.len() != 32 {
        return Err(MeshError::Setup(format!(
            "expected 32 key bytes, got {}",
            decoded.len()
        )));
    }
    let mut key = [0u8; 32];
    key.copy_from_slice(&decoded);
    Ok(key)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_bridge::CapGrade;

    fn node() -> MeshNode {
        MeshNode::new(
            MachineId("i-0fleet".into()),
            // A valid base64 32-byte key (a generated peer public key).
            MeshKeypair::generate().public_base64(),
            "203.0.113.7:51820",
            Ipv4Addr::new(100, 64, 0, 2),
        )
    }

    #[test]
    fn keypair_roundtrips_through_base64() {
        let kp = MeshKeypair::generate();
        let restored = MeshKeypair::from_private_base64(kp.private_base64().as_str()).unwrap();
        // Same private key → same public key.
        assert_eq!(kp.public_base64(), restored.public_base64());
    }

    #[test]
    fn bad_key_is_a_setup_error_not_a_panic() {
        assert!(matches!(
            MeshKeypair::from_private_base64("not-base64!!"),
            Err(MeshError::Setup(_))
        ));
        assert!(matches!(
            MeshKeypair::from_private_base64(&BASE64.encode([0u8; 16])),
            Err(MeshError::Setup(_))
        ));
    }

    #[test]
    fn rendered_ini_has_the_wireguard_shape() {
        let cfg = MeshConfig::generate(Ipv4Addr::new(100, 64, 0, 1));
        let n = node();
        let ini = cfg.wireguard_ini(&n);
        let ini = ini.as_str();
        assert!(ini.contains("[Interface]"));
        assert!(ini.contains("ListenPort = 51820"));
        assert!(ini.contains("Address = 100.64.0.1/32"));
        assert!(ini.contains("[Peer]"));
        assert!(ini.contains(&format!("PublicKey = {}", n.public_key)));
        assert!(ini.contains("Endpoint = 203.0.113.7:51820"));
        assert!(ini.contains("AllowedIPs = 100.64.0.2/32"));
        assert!(ini.contains("PersistentKeepalive = 25"));
    }

    #[tokio::test]
    async fn stub_connect_then_health_check_reachable() {
        let mesh = StubMesh::reachable();
        let n = node();
        let link = mesh.connect(&n).await.unwrap();
        assert_eq!(link.backend(), "stub");
        assert!(!link.is_live()); // no real tunnel off the fleet
        assert_eq!(
            link.target(n.agent_port),
            "100.64.0.2:8021".parse().unwrap()
        );
        link.health_check().await.expect("simulated reachable");
    }

    #[tokio::test]
    async fn stub_unreachable_is_an_error() {
        let mesh = StubMesh::new();
        let link = mesh.connect(&node()).await.unwrap();
        assert!(matches!(
            link.health_check().await,
            Err(MeshError::Unreachable(_))
        ));
    }

    #[tokio::test]
    async fn dispatch_over_a_plain_stub_is_the_named_live_overlay_step() {
        // A plain reachable stub has no dispatch carrier (no live tunnel, no local
        // override): connect + health-check succeed, but the dispatch is reported
        // as the live-overlay deploy step, carrying the exact POST it would issue.
        let mesh = StubMesh::reachable();
        let n = node();
        let lease = Lease::funded("agent-mesh", CapGrade::Sandboxed, "USD", 100, 1);
        let res = dispatch_lease_over_mesh(&mesh, &n, &lease, "wl-1").await;
        match res {
            Err(ProviderError::Unimplemented {
                provider,
                would_run,
            }) => {
                assert_eq!(provider, "mesh");
                assert!(would_run.contains("100.64.0.2:8021"));
                assert!(would_run.contains("agent-mesh"));
                assert!(would_run.contains("stub mesh link"));
            }
            other => panic!("expected the named live-overlay step, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn dispatch_issues_a_real_post_and_decodes_the_metered_result() {
        // The dispatch code path for real: stand up a local fulfill stub speaking
        // the same `:8021/fulfill` contract the node-agent does, point a stub
        // mesh link at it, and dispatch a funded lease. The control plane must
        // issue a real `POST /fulfill` carrying the lease and decode the durable
        // metered result back — the gateway→(bridge agent) path with the overlay
        // hop swapped for loopback.
        let captured = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let addr = spawn_fulfill_stub(captured.clone(), 200, None).await;

        let mesh = StubMesh::dispatching_to(addr);
        let mut n = node();
        n.overlay_addr = Ipv4Addr::new(100, 64, 0, 2); // dispatch_to overrides the wire target
        let lease = Lease::funded("agent-mesh", CapGrade::Sandboxed, "USD-mesh", 100, 1);

        let out = dispatch_lease_over_mesh(&mesh, &n, &lease, "wl-real")
            .await
            .expect("a real POST should return the metered durable result");

        // The metered result the agent returned was decoded into a DurableOutput.
        assert_eq!(out.meter_units, 2);
        assert_eq!(out.outputs, vec!["42".to_string(), "84".to_string()]);

        // The POST genuinely carried the lease descriptor the agent expects.
        let req = captured.lock().unwrap().clone();
        assert!(req.contains("POST /fulfill"));
        assert!(req.contains("\"lessee\":\"agent-mesh\""));
        assert!(req.contains("\"instance\":\"wl-real\""));
        assert!(req.contains("\"cap_grade\":\"sandboxed\""));
        assert!(req.contains("\"budget_units\":100"));
    }

    #[tokio::test]
    async fn tailscale_mesh_dispatches_over_a_live_link() {
        // The live backend the edge↔node-a deploy uses: a TailscaleMesh link is
        // live (a real TCP probe + a real POST to the node's tailnet IP), riding
        // the host overlay. Pointing the node's overlay address at a loopback
        // fulfill stub exercises the genuine backend path with no live overlay.
        let captured = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let addr = spawn_fulfill_stub(captured, 200, None).await;

        let mesh = TailscaleMesh::new();
        let mut n = node();
        // Address the node at the loopback stub (the stand-in for its tailnet IP).
        let ip = match addr.ip() {
            std::net::IpAddr::V4(v4) => v4,
            _ => unreachable!("loopback is v4"),
        };
        n.overlay_addr = ip;
        n.agent_port = addr.port();

        let link = mesh.connect(&n).await.unwrap();
        assert_eq!(link.backend(), "tailscale");
        assert!(link.is_live());
        assert_eq!(link.dispatch_target(n.agent_port), Some(addr));
        link.health_check()
            .await
            .expect("the stub is answering over the link");

        let lease = Lease::funded("agent-tail", CapGrade::Sandboxed, "USD-mesh", 100, 1);
        let out = dispatch_lease_over_mesh(&mesh, &n, &lease, "wl-tail")
            .await
            .expect("a real POST over the tailscale link returns the metered result");
        assert_eq!(out.meter_units, 2);
    }

    #[tokio::test]
    async fn dispatch_maps_a_refused_lease_to_a_lapse() {
        // A 4xx from the bridge agent (an unfunded / over-budget lease the agent
        // refuses) surfaces as a WorkloadLapsed the scheduler reaps — no result is
        // fabricated for work the lease did not authorize.
        let captured = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
        let addr = spawn_fulfill_stub(
            captured,
            402,
            Some(r#"{"ok":false,"error":"execution-lease exhausted after step2"}"#.into()),
        )
        .await;

        let mesh = StubMesh::dispatching_to(addr);
        let n = node();
        let lease = Lease::funded("agent-broke", CapGrade::Sandboxed, "USD-mesh", 1, 1);
        match dispatch_lease_over_mesh(&mesh, &n, &lease, "wl-lapse").await {
            Err(ProviderError::WorkloadLapsed(msg)) => {
                assert!(msg.contains("agent-broke"));
                assert!(msg.contains("exhausted"));
            }
            other => panic!("expected a lapse, got {other:?}"),
        }
    }

    /// Stand up a local server speaking the `:8021/fulfill` contract: for every
    /// `POST /fulfill` it captures the raw request into `captured`, then replies
    /// `status`. With `body = None` it returns a canned metered success envelope
    /// (the shape the node-agent produces for the `add(40,2)→×2` dogfood lease);
    /// with a body it returns that verbatim. Bare connect-then-close probes (the
    /// health-check leg) are ignored, so the live-link path (probe + POST) is served.
    /// Loops for the test's lifetime. Returns the loopback address to dispatch at.
    async fn spawn_fulfill_stub(
        captured: std::sync::Arc<std::sync::Mutex<String>>,
        status: u16,
        body: Option<String>,
    ) -> SocketAddr {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move {
            loop {
                let (mut stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => return,
                };
                let captured = captured.clone();
                let body = body.clone();
                tokio::spawn(async move {
                    // Read the request headers, then the Content-Length-bounded body.
                    let mut buf = Vec::new();
                    let mut tmp = [0u8; 4096];
                    let header_end = loop {
                        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
                            break pos;
                        }
                        let n = stream.read(&mut tmp).await.unwrap_or(0);
                        if n == 0 {
                            return; // a bare probe (health-check) — nothing to serve
                        }
                        buf.extend_from_slice(&tmp[..n]);
                    };
                    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
                    let content_len = head
                        .split("\r\n")
                        .find_map(|l| {
                            let (k, v) = l.split_once(':')?;
                            if k.trim().eq_ignore_ascii_case("content-length") {
                                v.trim().parse::<usize>().ok()
                            } else {
                                None
                            }
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
                    *captured.lock().unwrap() = String::from_utf8_lossy(&buf).to_string();

                    let payload = body.unwrap_or_else(|| {
                        serde_json::json!({
                            "ok": true,
                            "lessee": "agent-mesh",
                            "instance": "wl-real",
                            "step1": "42",
                            "step2": "84",
                            "outputs": ["42", "84"],
                            "meter_units": 2,
                        })
                        .to_string()
                    });
                    let resp = format!(
                        "HTTP/1.1 {status} X\r\nContent-Type: application/json\r\n\
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

    #[tokio::test]
    async fn dispatch_refuses_an_unreachable_node() {
        // If the node does not answer over the link, no work is handed to it.
        let mesh = StubMesh::new();
        let n = node();
        let lease = Lease::funded("agent-mesh", CapGrade::Sandboxed, "USD", 100, 1);
        assert!(matches!(
            dispatch_lease_over_mesh(&mesh, &n, &lease, "wl-2").await,
            Err(ProviderError::Bridge(_))
        ));
    }

    #[test]
    fn registry_records_and_resolves_a_node() {
        let reg = MeshNodeRegistry::new();
        let n = node();
        assert!(reg.get(&n.machine).is_none());
        reg.register(n.clone()).unwrap();
        assert_eq!(reg.get(&n.machine).unwrap().overlay_addr, n.overlay_addr);
    }

    /// The mesh registry is durable: a registered node survives a control-plane
    /// "restart" (drop the registry, reopen from the store) — reconstructed,
    /// reachable, exactly-once (no duplicate on reload).
    #[test]
    fn durable_mesh_registry_reconstructs_a_node_across_a_restart() {
        let mut path = std::env::temp_dir();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        path.push(format!("dreggnet-mesh-registry-{nanos}.log"));

        let n = node();
        {
            let reg = MeshNodeRegistry::with_durable_store(&path).unwrap();
            reg.register(n.clone()).unwrap();
            // A re-register of the same machine does not duplicate on reload.
            reg.register(n.clone()).unwrap();
        }
        // "Restart": a fresh registry over the same path reconstructs the node.
        let reopened = MeshNodeRegistry::with_durable_store(&path).unwrap();
        let got = reopened
            .get(&n.machine)
            .expect("node reconstructed after restart");
        assert_eq!(got.overlay_addr, n.overlay_addr);
        assert_eq!(got.public_key, n.public_key);
        std::fs::remove_file(&path).ok();
    }
}
