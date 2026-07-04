//! The public status-page data model — the at-a-glance verdict anyone can read.
//!
//! This is the PUBLIC subset of the operator [`dreggnet-ops`](../../ops) view:
//! ops shows the operator everything (logs, meters, per-machine detail); the
//! status page shows the public a crisp "is the cloud up?" — one overall banner,
//! a per-service row each, the n=5 federation panel, recent incidents, and an
//! uptime number. The whole assembled view is a [`StatusPage`], which serializes
//! verbatim as `/status.json`.
//!
//! ## The honesty law
//! A surface the page cannot reach renders [`ServiceState::Unknown`] — never a
//! false [`ServiceState::Operational`]. "We don't know" and "it's down" are
//! distinct, and neither is green. A configured-but-absent dependency is
//! [`ServiceState::NotConfigured`] and is excluded from the rollup.

use serde::Serialize;

/// The state of one service, worst-to-best meaningful for rollup ordering.
///
/// The ordering matters: [`worst_of`](ServiceState::worst_of) takes the more
/// severe of two states, and the overall banner is (essentially) the worst of
/// the core services. `NotConfigured` is outside the severity order — it is
/// excluded from the rollup, never dragging or lifting the verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ServiceState {
    /// Reached and healthy.
    Operational,
    /// Reached, but impaired (reduced capacity / quorum-but-not-full / stale).
    Degraded,
    /// Reached and reporting itself broken, or a critical invariant breached.
    Down,
    /// The page could NOT reach the surface — we genuinely don't know. NOT green.
    Unknown,
    /// The surface is not deployed/configured here — excluded from the rollup.
    NotConfigured,
}

impl ServiceState {
    /// A human label for the row.
    pub fn label(self) -> &'static str {
        match self {
            ServiceState::Operational => "Operational",
            ServiceState::Degraded => "Degraded",
            ServiceState::Down => "Down",
            ServiceState::Unknown => "Unknown",
            ServiceState::NotConfigured => "Not deployed",
        }
    }

    /// The stable string used in `/status.json` + CSS classes.
    pub fn slug(self) -> &'static str {
        match self {
            ServiceState::Operational => "operational",
            ServiceState::Degraded => "degraded",
            ServiceState::Down => "down",
            ServiceState::Unknown => "unknown",
            ServiceState::NotConfigured => "not_configured",
        }
    }

    /// Whether this state counts toward the health rollup (everything but
    /// `NotConfigured`).
    pub fn counts(self) -> bool {
        self != ServiceState::NotConfigured
    }
}

/// Which tier a service sits in — a core service down is a major outage; an
/// optional service down is a partial degradation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Tier {
    /// The cloud is not usable without it (node, federation, gateway, economy).
    Core,
    /// A secondary surface (orchestrator, bridges) — its loss degrades, not downs.
    Optional,
}

/// One service's public health row.
#[derive(Debug, Clone, Serialize)]
pub struct ServiceRow {
    /// A stable id ("node", "federation", "gateway", "control", "bridges", "economy").
    pub id: String,
    /// A human name shown in the table.
    pub name: String,
    /// Core vs optional (drives the overall-banner severity).
    pub tier: Tier,
    /// The rolled-up state.
    pub state: ServiceState,
    /// A short human detail line ("4/4 nodes finalizing", "conservation breach").
    pub detail: String,
}

/// The overall public verdict — the banner at the top of the page.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum OverallStatus {
    /// All systems operational.
    Operational,
    /// Some services degraded / a non-core service down (partial degradation).
    Degraded,
    /// A core service is down (major outage).
    Down,
    /// The page cannot reach anything — status is genuinely unknown.
    Unknown,
}

impl OverallStatus {
    /// The big banner headline.
    pub fn headline(self) -> &'static str {
        match self {
            OverallStatus::Operational => "All Systems Operational",
            OverallStatus::Degraded => "Partial Service Degradation",
            OverallStatus::Down => "Major Service Outage",
            OverallStatus::Unknown => "Status Unknown",
        }
    }

    /// The stable string used in `/status.json` + CSS class.
    pub fn slug(self) -> &'static str {
        match self {
            OverallStatus::Operational => "operational",
            OverallStatus::Degraded => "degraded",
            OverallStatus::Down => "down",
            OverallStatus::Unknown => "unknown",
        }
    }
}

/// The rust↔lean finality differential state (the verified-execution cross-check
/// the light client relies on). Surfaced distinctly on the federation panel.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Differential {
    /// The Rust and Lean producers agree on finalized order (the healthy state).
    Agreeing,
    /// They DISAGREED — `dregg_consensus_differential_divergence_total` > 0. A
    /// consensus-implementation bug; the verified Lean order is authoritative for
    /// the poll, but the disagreement must be investigated. Carries the count.
    Diverged { count: u64 },
    /// The differential counter could not be read (metrics unreachable).
    Unknown,
}

impl Differential {
    /// A short human label for the panel.
    pub fn label(&self) -> String {
        match self {
            Differential::Agreeing => "rust↔lean: agreeing".to_string(),
            Differential::Diverged { count } => {
                format!("rust↔lean: DIVERGED ({count})")
            }
            Differential::Unknown => "rust↔lean: unknown".to_string(),
        }
    }
}

/// One federation node's public status (the n=5 panel rows).
#[derive(Debug, Clone, Serialize)]
pub struct FederationNode {
    /// A human name ("dregg-1" … or a host label).
    pub name: String,
    /// Whether the node is up — `Unknown` if the page couldn't reach it.
    pub state: ServiceState,
    /// Its DAG/chain height, when known.
    pub height: Option<u64>,
    /// Seconds since its last finalized root, when known (finality latency).
    pub finality_age_secs: Option<u64>,
}

/// The federation panel — the n-node view: who's up, finality, the differential,
/// and the gossip storm-backpressure visibility.
#[derive(Debug, Clone, Serialize)]
pub struct FederationPanel {
    /// The expected committee size (n, e.g. 5).
    pub expected: usize,
    /// How many nodes are observed up.
    pub up: usize,
    /// How many are observed finalizing (up + finality not stale).
    pub finalizing: usize,
    /// The BFT quorum needed to finalize (n − f, f = ⌊(n−1)/3⌋).
    pub quorum_needed: usize,
    /// The latest finalized height across the federation, when known.
    pub last_finalized_height: Option<u64>,
    /// Age of that last finalized root in seconds (the finality latency).
    pub last_finalized_age_secs: Option<u64>,
    /// The rust↔lean finality differential state.
    pub differential: Differential,
    /// Cumulative inbound gossip streams REJECTED for hitting the per-connection
    /// limit — the storm-backpressure visibility (the `net::gossip`
    /// rejected-stream counter). `None` = the metric is not exported by the node
    /// (or `/metrics` was unreachable) → shown Unknown, never a false "no storm".
    pub gossip_rejected: Option<u64>,
    /// Per-node rows.
    pub nodes: Vec<FederationNode>,
}

/// One incident in the public incident log.
#[derive(Debug, Clone, Serialize)]
pub struct Incident {
    /// A stable id (operator-assigned or auto-detected, e.g. "inc_20260630_node").
    pub id: String,
    /// A short title ("Node finality stalled").
    pub title: String,
    /// "down" (major) / "degraded" (partial) / "info" (maintenance/notice).
    pub severity: String,
    /// When it started (RFC3339).
    pub started_at: String,
    /// When it resolved (RFC3339), or `None` if ongoing.
    pub resolved_at: Option<String>,
    /// The services it affected (row ids).
    pub affected: Vec<String>,
    /// A human description / latest update.
    pub body: String,
}

impl Incident {
    /// Whether the incident is still open (unresolved).
    pub fn is_open(&self) -> bool {
        self.resolved_at.is_none()
    }
}

/// An uptime figure over one window (e.g. last 24h / 7d / 30d).
#[derive(Debug, Clone, Serialize)]
pub struct UptimeWindow {
    /// A human label for the window ("24h", "7d", "30d").
    pub label: String,
    /// The window length in seconds.
    pub window_secs: u64,
    /// Uptime as a percentage in `[0, 100]`.
    pub uptime_pct: f64,
    /// Total counted downtime within the window, in seconds.
    pub downtime_secs: u64,
}

/// The whole assembled public status page — the object `/status.json` serializes
/// and [`crate::render`] renders to HTML.
#[derive(Debug, Clone, Serialize)]
pub struct StatusPage {
    /// When this snapshot was generated (RFC3339).
    pub generated_at: String,
    /// The overall public verdict.
    pub overall: OverallStatus,
    /// A human one-liner under the banner.
    pub overall_detail: String,
    /// The per-service rows (core then optional).
    pub services: Vec<ServiceRow>,
    /// The n=5 federation panel.
    pub federation: FederationPanel,
    /// Recent incidents (newest first).
    pub incidents: Vec<Incident>,
    /// Uptime over each configured window.
    pub uptime: Vec<UptimeWindow>,
}

impl StatusPage {
    /// The service row by id, if present.
    pub fn service(&self, id: &str) -> Option<&ServiceRow> {
        self.services.iter().find(|s| s.id == id)
    }
}
