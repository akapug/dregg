//! Deterministic fixtures — the green-standalone path the page runs + tests on.
//!
//! Three canonical bundles: [`healthy`] (all green), [`degraded`] (a non-core
//! service down + a stale federation node), and [`outage`] (the node + economy
//! conservation breached). They drive the demo deploy and the test gauntlet so
//! the page proves out without any live surface.

use crate::model::Incident;
use crate::source::*;

/// A fixed reference "now" so fixture-driven uptime/incident math is deterministic.
pub const FIXTURE_NOW_RFC3339: &str = "2026-06-30T12:00:00Z";

/// The fixed reference now as Unix epoch seconds (parsed from [`FIXTURE_NOW_RFC3339`]).
pub fn fixture_now_epoch() -> i64 {
    crate::incidents::parse_epoch(FIXTURE_NOW_RFC3339).expect("fixture now parses")
}

/// The five canonical federation nodes, all up and finalizing (the live n=5).
fn healthy_nodes() -> Vec<FedNodeProbe> {
    (1..=5)
        .map(|i| FedNodeProbe {
            name: format!("dregg-{i}"),
            up: Some(true),
            height: Some(10_840 + i as u64),
            finality_age_secs: Some(4),
        })
        .collect()
}

/// The recent incident log shown on every fixture (one resolved DOWN incident in
/// the last 24h → a visible, deterministic uptime dip).
fn fixture_incidents() -> Vec<Incident> {
    vec![
        Incident {
            id: "inc_20260630_finality".into(),
            title: "Node finality paused during committee rotation".into(),
            severity: "down".into(),
            started_at: "2026-06-30T09:00:00Z".into(),
            resolved_at: Some("2026-06-30T10:00:00Z".into()),
            affected: vec!["node".into(), "federation".into()],
            body: "A committee epoch rotation paused turn-bearing finality for ~1h. \
                   Heartbeat blocks continued; no turns were lost. Resolved after the \
                   new committee ratified."
                .into(),
        },
        Incident {
            id: "inc_20260628_bridge".into(),
            title: "Solana devnet RPC degraded".into(),
            severity: "degraded".into(),
            started_at: "2026-06-28T14:30:00Z".into(),
            resolved_at: Some("2026-06-28T15:10:00Z".into()),
            affected: vec!["bridges".into()],
            body: "The upstream Solana devnet RPC was intermittently unreachable; \
                   inbound lock observation was delayed. Conservation was never at risk."
                .into(),
        },
    ]
}

/// A fully-healthy bundle — all systems operational.
pub fn healthy() -> RawHealth {
    RawHealth {
        node: Probe::Reached(NodeHealth {
            finalizing: true,
            consensus_live: true,
            dag_height: 10_844,
            latest_height: 9_210,
            peer_count: 3,
            state_producer: "lean".into(),
        }),
        gateway: Probe::Reached(GatewayHealth { machines: Some(7) }),
        control: Probe::Reached(ControlHealth { servers: Some(2) }),
        bridges: Probe::Reached(BridgeHealth {
            solana_reachable: Some(true),
            stripe_reachable: Some(true),
            conservation_observed: true,
            conservation_ok: true,
            breach: false,
        }),
        economy: Probe::Reached(EconomyHealth {
            observed: true,
            delta_sum: 0,
        }),
        federation: FederationProbe {
            expected: 5,
            nodes: healthy_nodes(),
            last_finalized_height: Some(10_845),
            last_finalized_age_secs: Some(4),
            divergence: Some(0),
            gossip_rejected: Some(0),
        },
        incidents: fixture_incidents(),
    }
}

/// A degraded bundle — an optional service down + a stale federation node, but
/// the core (node/economy/quorum) still operational. Overall → Degraded, NOT green.
pub fn degraded() -> RawHealth {
    let mut nodes = healthy_nodes();
    // One node has gone stale (still up, but finality lagging) → reduced redundancy.
    nodes[4].finality_age_secs = Some(600);
    RawHealth {
        node: Probe::Reached(NodeHealth {
            finalizing: true,
            consensus_live: true,
            dag_height: 10_844,
            latest_height: 9_210,
            peer_count: 3,
            state_producer: "lean".into(),
        }),
        gateway: Probe::Reached(GatewayHealth { machines: Some(7) }),
        // The orchestrator is unreachable from the status page → Unknown.
        control: Probe::Unreachable("connect control:8086: connection refused".into()),
        // The bridge relayer is down → Solana/Stripe reachability unknown there,
        // and the rails report down.
        bridges: Probe::Reached(BridgeHealth {
            solana_reachable: Some(false),
            stripe_reachable: Some(true),
            conservation_observed: true,
            conservation_ok: true,
            breach: false,
        }),
        economy: Probe::Reached(EconomyHealth {
            observed: true,
            delta_sum: 0,
        }),
        federation: FederationProbe {
            expected: 5,
            nodes,
            last_finalized_height: Some(10_845),
            last_finalized_age_secs: Some(8),
            divergence: Some(0),
            // A burst of inbound gossip was rejected by the per-connection limit —
            // storm backpressure is visibly engaging (informational, not an alarm).
            gossip_rejected: Some(37),
        },
        incidents: fixture_incidents(),
    }
}

/// A major-outage bundle — the node is not finalizing AND the economy
/// conservation invariant is breached (Σδ ≠ 0). Overall → Down.
pub fn outage() -> RawHealth {
    let nodes = vec![
        FedNodeProbe {
            name: "dregg-1".into(),
            up: Some(true),
            height: Some(10_844),
            finality_age_secs: Some(900),
        },
        FedNodeProbe {
            name: "dregg-2".into(),
            up: Some(false),
            height: None,
            finality_age_secs: None,
        },
        FedNodeProbe {
            name: "dregg-3".into(),
            up: Some(false),
            height: None,
            finality_age_secs: None,
        },
        FedNodeProbe {
            name: "dregg-4".into(),
            up: Some(false),
            height: None,
            finality_age_secs: None,
        },
        FedNodeProbe {
            name: "dregg-5".into(),
            up: None,
            height: None,
            finality_age_secs: None,
        },
    ];
    RawHealth {
        node: Probe::Reached(NodeHealth {
            finalizing: false,
            consensus_live: false,
            dag_height: 10_844,
            latest_height: 9_210,
            peer_count: 0,
            state_producer: "lean".into(),
        }),
        gateway: Probe::Unreachable("connect gateway:8080: connection refused".into()),
        control: Probe::Unreachable("connect control:8086: connection refused".into()),
        bridges: Probe::Reached(BridgeHealth {
            solana_reachable: Some(false),
            stripe_reachable: Some(false),
            conservation_observed: true,
            conservation_ok: false,
            breach: true,
        }),
        economy: Probe::Reached(EconomyHealth {
            observed: true,
            delta_sum: 500, // a non-zero Σδ — asset apparently created
        }),
        federation: FederationProbe {
            expected: 5,
            nodes,
            last_finalized_height: Some(10_840),
            last_finalized_age_secs: Some(900),
            divergence: Some(0),
            gossip_rejected: None, // metrics unreachable in the outage → Unknown
        },
        incidents: {
            let mut inc = fixture_incidents();
            inc.insert(
                0,
                Incident {
                    id: "inc_20260630_outage".into(),
                    title: "Quorum lost — finality halted".into(),
                    severity: "down".into(),
                    started_at: "2026-06-30T11:45:00Z".into(),
                    resolved_at: None, // ongoing
                    affected: vec!["node".into(), "federation".into(), "economy".into()],
                    body: "Three federation nodes are down and one is unreachable; the BFT \
                           quorum is lost and finality is halted. Investigating."
                        .into(),
                },
            );
            inc
        },
    }
}
