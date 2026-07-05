//! Roll the raw [`RawHealth`] probes up into the public [`StatusPage`].
//!
//! This is the honesty engine. Each surface's [`Probe`] becomes a [`ServiceRow`]:
//! `Reached(healthy)` → Operational, `Reached(impaired)` → Degraded/Down,
//! `Unreachable` → **Unknown** (never green), `NotConfigured` → excluded. The
//! overall banner is the worst of the core services, with one twist: a partial
//! visibility (some Unknown, some not) is Degraded, and total blindness (all
//! Unknown) is Unknown — we never paint a cloud we cannot see as either green or
//! a confirmed outage.

use crate::incidents;
use crate::model::*;
use crate::source::*;

/// Finality older than this (seconds) drags a node/federation to Degraded.
pub const STALE_FINALITY_SECS: u64 = 120;

/// Build the public status page from a raw health bundle.
///
/// `now_epoch` is the current Unix time (seconds), used for uptime windows.
/// `windows` is the `(label, seconds)` set to compute uptime over.
pub fn build(
    raw: &RawHealth,
    now_rfc3339: String,
    now_epoch: i64,
    windows: &[(String, u64)],
) -> StatusPage {
    let federation = build_federation(&raw.federation);

    let services = vec![
        node_row(&raw.node),
        federation_row(&federation),
        gateway_row(&raw.gateway),
        economy_row(&raw.economy),
        control_row(&raw.control),
        bridges_row(&raw.bridges),
    ];

    let (overall, overall_detail) = roll_up(&services);

    let mut incidents = raw.incidents.clone();
    // Newest first (by start time, lexicographic RFC3339 sorts chronologically).
    incidents.sort_by(|a, b| b.started_at.cmp(&a.started_at));

    let uptime = windows
        .iter()
        .map(|(label, secs)| incidents::uptime_window(label, *secs, &incidents, now_epoch))
        .collect();

    StatusPage {
        generated_at: now_rfc3339,
        overall,
        overall_detail,
        services,
        federation,
        incidents,
        uptime,
    }
}

/// The dregg node row.
fn node_row(probe: &Probe<NodeHealth>) -> ServiceRow {
    let (state, detail) = match probe {
        Probe::Reached(n) => {
            if n.finalizing && n.consensus_live {
                (
                    ServiceState::Operational,
                    format!(
                        "finalizing · height {} · {} peers · {} producer",
                        n.dag_height, n.peer_count, n.state_producer
                    ),
                )
            } else if n.consensus_live {
                (
                    ServiceState::Degraded,
                    "up but not finalizing (consensus live, no recent finality)".to_string(),
                )
            } else {
                (
                    ServiceState::Down,
                    "up but consensus is not live — the chain is not progressing".to_string(),
                )
            }
        }
        Probe::Unreachable(e) => (ServiceState::Unknown, format!("unreachable: {e}")),
        Probe::NotConfigured => (ServiceState::NotConfigured, "not deployed here".to_string()),
    };
    ServiceRow {
        id: "node".into(),
        name: "Node (consensus)".into(),
        tier: Tier::Core,
        state,
        detail,
    }
}

/// The gateway / hosting row.
fn gateway_row(probe: &Probe<GatewayHealth>) -> ServiceRow {
    let (state, detail) = match probe {
        Probe::Reached(g) => (
            ServiceState::Operational,
            match g.machines {
                Some(m) => format!("serving · {m} machines"),
                None => "serving".to_string(),
            },
        ),
        Probe::Unreachable(e) => (ServiceState::Unknown, format!("unreachable: {e}")),
        Probe::NotConfigured => (ServiceState::NotConfigured, "not deployed here".to_string()),
    };
    ServiceRow {
        id: "gateway".into(),
        name: "Gateway / Hosting".into(),
        tier: Tier::Core,
        state,
        detail,
    }
}

/// The control / orchestrator row (optional tier).
fn control_row(probe: &Probe<ControlHealth>) -> ServiceRow {
    let (state, detail) = match probe {
        Probe::Reached(c) => (
            ServiceState::Operational,
            match c.servers {
                Some(s) => format!("orchestrating · {s} servers"),
                None => "orchestrating".to_string(),
            },
        ),
        Probe::Unreachable(e) => (ServiceState::Unknown, format!("unreachable: {e}")),
        Probe::NotConfigured => (ServiceState::NotConfigured, "not deployed here".to_string()),
    };
    ServiceRow {
        id: "control".into(),
        name: "Control / Orchestrator".into(),
        tier: Tier::Optional,
        state,
        detail,
    }
}

/// The bridges row (Solana / Stripe conservation; optional tier).
fn bridges_row(probe: &Probe<BridgeHealth>) -> ServiceRow {
    let (state, detail) = match probe {
        Probe::Reached(b) => {
            if b.breach || (b.conservation_observed && !b.conservation_ok) {
                (
                    ServiceState::Down,
                    "CONSERVATION BREACH — more mirror asset circulates than is backed".to_string(),
                )
            } else {
                // Reachability of the rails, plus the honest conservation note.
                let rail = |r: Option<bool>| match r {
                    Some(true) => "up",
                    Some(false) => "down",
                    None => "n/a",
                };
                let any_down =
                    b.solana_reachable == Some(false) || b.stripe_reachable == Some(false);
                let cons = if b.conservation_observed {
                    "conservation OK"
                } else {
                    "conservation un-observed"
                };
                let detail = format!(
                    "solana {} · stripe {} · {}",
                    rail(b.solana_reachable),
                    rail(b.stripe_reachable),
                    cons
                );
                if any_down {
                    (ServiceState::Degraded, detail)
                } else if !b.conservation_observed {
                    // Reachable rails but conservation not observed: honest Unknown
                    // on the invariant — surface as Degraded, never green.
                    (ServiceState::Degraded, detail)
                } else {
                    (ServiceState::Operational, detail)
                }
            }
        }
        Probe::Unreachable(e) => (ServiceState::Unknown, format!("unreachable: {e}")),
        Probe::NotConfigured => (ServiceState::NotConfigured, "not deployed here".to_string()),
    };
    ServiceRow {
        id: "bridges".into(),
        name: "Bridges (Solana / Stripe)".into(),
        tier: Tier::Optional,
        state,
        detail,
    }
}

/// The economy conservation row (the global ledger Σδ=0 invariant; core tier).
fn economy_row(probe: &Probe<EconomyHealth>) -> ServiceRow {
    let (state, detail) = match probe {
        Probe::Reached(e) => {
            if !e.observed {
                (
                    ServiceState::Unknown,
                    "conservation un-observed (Σδ not summed) — not a clean bill".to_string(),
                )
            } else if e.delta_sum == 0 {
                (
                    ServiceState::Operational,
                    "conservation holds (Σδ = 0)".to_string(),
                )
            } else {
                (
                    ServiceState::Down,
                    format!(
                        "CONSERVATION BREACH: Σδ = {} ≠ 0 (asset created/destroyed)",
                        e.delta_sum
                    ),
                )
            }
        }
        Probe::Unreachable(e) => (ServiceState::Unknown, format!("unreachable: {e}")),
        Probe::NotConfigured => (ServiceState::NotConfigured, "not deployed here".to_string()),
    };
    ServiceRow {
        id: "economy".into(),
        name: "Economy (conservation)".into(),
        tier: Tier::Core,
        state,
        detail,
    }
}

/// The BFT quorum (n − f, f = ⌊(n−1)/3⌋) needed to finalize for committee size `n`.
pub fn quorum_needed(n: usize) -> usize {
    let f = n.saturating_sub(1) / 3;
    n.saturating_sub(f)
}

/// Assemble the federation panel from the probe.
fn build_federation(p: &FederationProbe) -> FederationPanel {
    let quorum = quorum_needed(p.expected);

    let stale = |age: Option<u64>| age.map(|a| a > STALE_FINALITY_SECS).unwrap_or(false);

    let nodes: Vec<FederationNode> = p
        .nodes
        .iter()
        .map(|n| {
            let state = match n.up {
                Some(true) if stale(n.finality_age_secs) => ServiceState::Degraded,
                Some(true) => ServiceState::Operational,
                Some(false) => ServiceState::Down,
                None => ServiceState::Unknown,
            };
            FederationNode {
                name: n.name.clone(),
                state,
                height: n.height,
                finality_age_secs: n.finality_age_secs,
            }
        })
        .collect();

    let up = p.nodes.iter().filter(|n| n.up == Some(true)).count();
    let finalizing = p
        .nodes
        .iter()
        .filter(|n| n.up == Some(true) && !stale(n.finality_age_secs))
        .count();

    let differential = match p.divergence {
        None => Differential::Unknown,
        Some(0) => Differential::Agreeing,
        Some(c) => Differential::Diverged { count: c },
    };

    FederationPanel {
        expected: p.expected,
        up,
        finalizing,
        quorum_needed: quorum,
        last_finalized_height: p.last_finalized_height,
        last_finalized_age_secs: p.last_finalized_age_secs,
        differential,
        gossip_rejected: p.gossip_rejected,
        nodes,
    }
}

/// The federation service row, derived from the assembled panel.
fn federation_row(f: &FederationPanel) -> ServiceRow {
    // A rust↔lean divergence is a consensus-correctness signal — Down regardless
    // of liveness (the two implementations disagree on finalized order).
    if let Differential::Diverged { count } = f.differential {
        return ServiceRow {
            id: "federation".into(),
            name: format!("Federation (n={})", f.expected),
            tier: Tier::Core,
            state: ServiceState::Down,
            detail: format!(
                "rust↔lean finality DIVERGED ({count}) — a consensus-implementation bug under investigation"
            ),
        };
    }

    let known = f
        .nodes
        .iter()
        .filter(|n| n.state != ServiceState::Unknown)
        .count();
    let (state, detail) = if known == 0 {
        (
            ServiceState::Unknown,
            "no federation node reachable — status unknown".to_string(),
        )
    } else if f.up == 0 {
        (
            ServiceState::Down,
            format!("0/{} nodes up — finality halted", f.expected),
        )
    } else if f.up < f.quorum_needed {
        (
            ServiceState::Down,
            format!(
                "{}/{} nodes up — below the {} quorum, finality halted",
                f.up, f.expected, f.quorum_needed
            ),
        )
    } else if f.finalizing < f.up || f.up < f.expected {
        (
            ServiceState::Degraded,
            format!(
                "{}/{} up · {} finalizing · quorum {} met (reduced redundancy)",
                f.up, f.expected, f.finalizing, f.quorum_needed
            ),
        )
    } else {
        (
            ServiceState::Operational,
            format!(
                "{}/{} nodes finalizing · height {} · {}",
                f.up,
                f.expected,
                f.last_finalized_height
                    .map(|h| h.to_string())
                    .unwrap_or_else(|| "—".into()),
                f.differential.label()
            ),
        )
    };

    ServiceRow {
        id: "federation".into(),
        name: format!("Federation (n={})", f.expected),
        tier: Tier::Core,
        state,
        detail,
    }
}

/// Roll the service rows up into the overall public verdict.
///
/// Worst-wins over the **counted** services (NotConfigured excluded):
/// - any core Down → Down (major outage)
/// - else any Down / Degraded (optional or core) → Degraded
/// - else if everything counted is Unknown → Unknown (total blindness)
/// - else if some Unknown but not all → Degraded (partial visibility)
/// - else → Operational
pub fn roll_up(services: &[ServiceRow]) -> (OverallStatus, String) {
    let counted: Vec<&ServiceRow> = services.iter().filter(|s| s.state.counts()).collect();

    if counted.is_empty() {
        return (OverallStatus::Unknown, "no services configured".to_string());
    }

    let core_down: Vec<&str> = counted
        .iter()
        .filter(|s| s.tier == Tier::Core && s.state == ServiceState::Down)
        .map(|s| s.name.as_str())
        .collect();
    if !core_down.is_empty() {
        return (
            OverallStatus::Down,
            format!("Major outage: {} down.", core_down.join(", ")),
        );
    }

    let any_down: Vec<&str> = counted
        .iter()
        .filter(|s| s.state == ServiceState::Down)
        .map(|s| s.name.as_str())
        .collect();
    let any_degraded: Vec<&str> = counted
        .iter()
        .filter(|s| s.state == ServiceState::Degraded)
        .map(|s| s.name.as_str())
        .collect();
    let unknown: Vec<&str> = counted
        .iter()
        .filter(|s| s.state == ServiceState::Unknown)
        .map(|s| s.name.as_str())
        .collect();

    if !any_down.is_empty() || !any_degraded.is_empty() {
        let mut affected = any_down.clone();
        affected.extend(any_degraded.iter().copied());
        return (
            OverallStatus::Degraded,
            format!("Degraded: {} impaired.", affected.join(", ")),
        );
    }

    if unknown.len() == counted.len() {
        return (
            OverallStatus::Unknown,
            "Cannot reach any service — status unknown.".to_string(),
        );
    }
    if !unknown.is_empty() {
        return (
            OverallStatus::Degraded,
            format!("Partial visibility: cannot reach {}.", unknown.join(", ")),
        );
    }

    (
        OverallStatus::Operational,
        "All systems operational.".to_string(),
    )
}
