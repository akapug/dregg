//! The one seam between the status-page core and the live cloud.
//!
//! A [`StatusSource`] yields a source-agnostic [`RawHealth`] bundle — the raw
//! reachability + readings of each surface. [`crate::aggregate::build`] turns
//! that into the public [`StatusPage`](crate::model::StatusPage). This split is
//! what makes the page testable and honest at once:
//!
//! - [`FixtureSource`] returns deterministic [`RawHealth`] (healthy or degraded
//!   variants) so the page renders + tests green standalone — the shipped path.
//! - [`LiveSource`] reads the real health surfaces over plain HTTP (the node
//!   `/status` + `/api/federations` + `/metrics`, the gateway `/status`, the
//!   control orchestrator, the bridge relayer) and fills what it can reach —
//!   leaving an unreachable surface as [`Probe::Unreachable`] → Unknown, never
//!   falsely green. Wiring it behind the production edge is the reviewed-go
//!   deploy step; the aggregation + render here are source-agnostic and complete.

use crate::model::Incident;

/// The outcome of probing one surface.
#[derive(Debug, Clone)]
pub enum Probe<T> {
    /// Reached the surface and read `T`.
    Reached(T),
    /// Could not reach it — carries a human error. Renders as Unknown (honest).
    Unreachable(String),
    /// Not deployed/configured here — excluded from the rollup.
    NotConfigured,
}

impl<T> Probe<T> {
    /// The reading, if reached.
    pub fn reached(&self) -> Option<&T> {
        match self {
            Probe::Reached(t) => Some(t),
            _ => None,
        }
    }
}

/// The dregg node's public health reading (from `/status`).
#[derive(Debug, Clone)]
pub struct NodeHealth {
    /// The node's own readiness verdict (store ok + consensus live + ≥1 block).
    pub finalizing: bool,
    /// Whether a consensus handle is attached + producing.
    pub consensus_live: bool,
    /// The blocklace DAG tip height (advances on every block).
    pub dag_height: u64,
    /// The attested-root / turn height (advances on turn-bearing finality).
    pub latest_height: u64,
    /// Connected peers.
    pub peer_count: u64,
    /// The committed-state producer ("lean" verified / "rust" legacy).
    pub state_producer: String,
}

/// The gateway / hosting front-door reading (from `/status`). Reached ⇒ up.
#[derive(Debug, Clone, Default)]
pub struct GatewayHealth {
    /// Machines listed, when reported.
    pub machines: Option<u64>,
}

/// The control / orchestrator reading. Reached ⇒ up.
#[derive(Debug, Clone, Default)]
pub struct ControlHealth {
    /// Servers/fleet under management, when reported.
    pub servers: Option<u64>,
}

/// The bridge observability reading (Solana/Stripe conservation).
#[derive(Debug, Clone, Default)]
pub struct BridgeHealth {
    /// Solana cluster reachability (`None` = not probed/observed).
    pub solana_reachable: Option<bool>,
    /// Stripe receiver reachability (`None` = not probed/observed).
    pub stripe_reachable: Option<bool>,
    /// Whether the conservation invariant was actually OBSERVED (a relayer ledger
    /// was parsed). When false, conservation is un-observed — never a false
    /// all-clear.
    pub conservation_observed: bool,
    /// Whether every observed mirror conserves (`live ≤ locked`).
    pub conservation_ok: bool,
    /// Whether a SUCCESSFUL double-mint / conservation breach was detected.
    pub breach: bool,
}

/// The economy conservation reading (the global ledger Σδ=0 invariant).
#[derive(Debug, Clone, Default)]
pub struct EconomyHealth {
    /// Whether conservation was actually observed (a balance was summed). When
    /// false, conservation is un-observed — Unknown, never a false all-clear.
    pub observed: bool,
    /// The signed sum of all balance deltas Σδ. Conserved iff `== 0`.
    pub delta_sum: i128,
}

impl EconomyHealth {
    /// Whether the conservation invariant holds (Σδ = 0).
    pub fn conserved(&self) -> bool {
        self.observed && self.delta_sum == 0
    }
}

/// One federation node's probe (the n=5 panel).
#[derive(Debug, Clone)]
pub struct FedNodeProbe {
    /// A human name / host label.
    pub name: String,
    /// Whether the node is up — `None` if unreachable (→ Unknown).
    pub up: Option<bool>,
    /// Its height, when known.
    pub height: Option<u64>,
    /// Seconds since its last finalized root, when known.
    pub finality_age_secs: Option<u64>,
}

/// The federation-wide probe.
#[derive(Debug, Clone)]
pub struct FederationProbe {
    /// The expected committee size (n).
    pub expected: usize,
    /// Per-node probes.
    pub nodes: Vec<FedNodeProbe>,
    /// The latest finalized height across the federation, when known.
    pub last_finalized_height: Option<u64>,
    /// Age of that last finalized root in seconds, when known.
    pub last_finalized_age_secs: Option<u64>,
    /// `dregg_consensus_differential_divergence_total` — the rust↔lean
    /// finalized-order disagreement counter. `None` = metrics unreachable.
    pub divergence: Option<u64>,
    /// Cumulative inbound gossip streams rejected for hitting the per-connection
    /// limit (the `net::gossip` rejected-stream counter) — storm-backpressure
    /// visibility. `None` = the node does not export the metric / `/metrics`
    /// unreachable → Unknown, never a false "no storm".
    pub gossip_rejected: Option<u64>,
}

impl Default for FederationProbe {
    fn default() -> Self {
        FederationProbe {
            expected: 5,
            nodes: Vec::new(),
            last_finalized_height: None,
            last_finalized_age_secs: None,
            divergence: None,
            gossip_rejected: None,
        }
    }
}

/// The raw, source-agnostic health bundle one [`StatusSource`] yields.
#[derive(Debug, Clone)]
pub struct RawHealth {
    pub node: Probe<NodeHealth>,
    pub gateway: Probe<GatewayHealth>,
    pub control: Probe<ControlHealth>,
    pub bridges: Probe<BridgeHealth>,
    pub economy: Probe<EconomyHealth>,
    pub federation: FederationProbe,
    /// The incident log (operator-posted and/or auto-detected from transitions).
    pub incidents: Vec<Incident>,
}

/// A source of the raw health bundle.
pub trait StatusSource: Send + Sync {
    /// Read the current raw health.
    fn health(&self) -> RawHealth;
    /// The uptime windows to compute, as `(label, seconds)`.
    fn uptime_windows(&self) -> Vec<(String, u64)> {
        vec![
            ("24h".to_string(), 24 * 3600),
            ("7d".to_string(), 7 * 24 * 3600),
            ("30d".to_string(), 30 * 24 * 3600),
        ]
    }
}

/// The deterministic demo source — the shipped, green-standalone path.
pub struct FixtureSource {
    raw: RawHealth,
}

impl FixtureSource {
    /// A fully-healthy fixture (all green, n=5 finalizing, conservation OK).
    pub fn healthy() -> Self {
        FixtureSource {
            raw: crate::fixtures::healthy(),
        }
    }

    /// A degraded fixture (a non-core service down + a stale federation node).
    pub fn degraded() -> Self {
        FixtureSource {
            raw: crate::fixtures::degraded(),
        }
    }

    /// A major-outage fixture (the node + economy conservation breached).
    pub fn outage() -> Self {
        FixtureSource {
            raw: crate::fixtures::outage(),
        }
    }

    /// Build from an explicit raw bundle.
    pub fn from_raw(raw: RawHealth) -> Self {
        FixtureSource { raw }
    }
}

impl StatusSource for FixtureSource {
    fn health(&self) -> RawHealth {
        self.raw.clone()
    }
}
