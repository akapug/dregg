//! Proof gauntlet for the public status page.
//!
//! Renders the page against deterministic fixtures and proves: it is operational
//! when healthy, degraded when a service is down (NEVER falsely green), down on a
//! core breach, honest-Unknown on an unreachable surface, the per-service rows +
//! federation panel render, `/status.json` is valid, and the incident log +
//! uptime compute.

use dreggnet_status::aggregate::{self, build};
use dreggnet_status::fixtures::{self, FIXTURE_NOW_RFC3339, fixture_now_epoch};
use dreggnet_status::model::*;
use dreggnet_status::render;
use dreggnet_status::source::*;

/// Build a page from a raw bundle at the fixed fixture time (deterministic uptime).
fn page(raw: &RawHealth) -> StatusPage {
    let windows = vec![
        ("24h".to_string(), 24 * 3600u64),
        ("7d".to_string(), 7 * 24 * 3600),
    ];
    build(
        raw,
        FIXTURE_NOW_RFC3339.to_string(),
        fixture_now_epoch(),
        &windows,
    )
}

#[test]
fn healthy_is_operational_and_green_down_the_board() {
    let p = page(&fixtures::healthy());
    assert_eq!(p.overall, OverallStatus::Operational);
    // Every counted service is operational.
    for s in &p.services {
        if s.state.counts() {
            assert_eq!(
                s.state,
                ServiceState::Operational,
                "service {} should be operational, was {:?}: {}",
                s.id,
                s.state,
                s.detail
            );
        }
    }
    // The federation panel shows the n=5, all up + finalizing, agreeing.
    assert_eq!(p.federation.expected, 5);
    assert_eq!(p.federation.up, 5);
    assert_eq!(p.federation.finalizing, 5);
    assert_eq!(p.federation.differential, Differential::Agreeing);
    // The gossip storm-backpressure visibility is present (0 rejections, healthy).
    assert_eq!(p.federation.gossip_rejected, Some(0));
}

#[test]
fn a_down_service_shows_degraded_not_green() {
    // A single OPTIONAL service down must pull overall to Degraded — never green.
    let mut raw = fixtures::healthy();
    raw.bridges = Probe::Reached(BridgeHealth {
        solana_reachable: Some(false),
        stripe_reachable: Some(false),
        conservation_observed: true,
        conservation_ok: false,
        breach: true, // a conservation breach on the bridge
    });
    let p = page(&raw);
    // The bridge row itself is Down...
    assert_eq!(p.service("bridges").unwrap().state, ServiceState::Down);
    // ...and the overall is Degraded (a non-core service), NOT Operational.
    assert_ne!(p.overall, OverallStatus::Operational);
    assert_eq!(p.overall, OverallStatus::Degraded);
}

#[test]
fn the_degraded_fixture_is_degraded_not_green() {
    let p = page(&fixtures::degraded());
    assert_eq!(p.overall, OverallStatus::Degraded);
    assert_ne!(p.overall, OverallStatus::Operational);
    // The unreachable control surface is honestly Unknown, not green.
    assert_eq!(p.service("control").unwrap().state, ServiceState::Unknown);
    // A core service (node) is still fine, so this is partial degradation.
    assert_eq!(p.service("node").unwrap().state, ServiceState::Operational);
}

#[test]
fn a_core_breach_is_a_major_outage() {
    let p = page(&fixtures::outage());
    assert_eq!(p.overall, OverallStatus::Down);
    // The node is not finalizing → Down; the economy Σδ≠0 → Down.
    assert_eq!(p.service("node").unwrap().state, ServiceState::Down);
    assert_eq!(p.service("economy").unwrap().state, ServiceState::Down);
    // The federation lost quorum (only 1/5 observed up, quorum is 4).
    assert_eq!(p.service("federation").unwrap().state, ServiceState::Down);
    assert_eq!(p.federation.quorum_needed, 4);
}

#[test]
fn an_unreachable_surface_is_unknown_never_green() {
    let mut raw = fixtures::healthy();
    raw.node = Probe::Unreachable("connect dregg-node:8420: connection refused".into());
    let p = page(&raw);
    // The node we cannot reach is Unknown — not green, not falsely down.
    assert_eq!(p.service("node").unwrap().state, ServiceState::Unknown);
    // Overall is no longer Operational (partial visibility → Degraded).
    assert_ne!(p.overall, OverallStatus::Operational);
}

#[test]
fn total_blindness_is_unknown_not_a_confirmed_outage() {
    // Every surface unreachable + no federation node observable → overall Unknown.
    let raw = RawHealth {
        node: Probe::Unreachable("x".into()),
        gateway: Probe::Unreachable("x".into()),
        control: Probe::Unreachable("x".into()),
        bridges: Probe::Unreachable("x".into()),
        economy: Probe::Unreachable("x".into()),
        federation: FederationProbe {
            expected: 5,
            nodes: vec![FedNodeProbe {
                name: "dregg-1".into(),
                up: None,
                height: None,
                finality_age_secs: None,
            }],
            last_finalized_height: None,
            last_finalized_age_secs: None,
            divergence: None,
            gossip_rejected: None,
        },
        incidents: vec![],
    };
    let p = page(&raw);
    assert_eq!(p.overall, OverallStatus::Unknown);
}

#[test]
fn gossip_rejection_is_honest_unknown_when_unexported() {
    // The storm-visibility seam: when the node does not export the rejected-stream
    // metric, the panel says Unknown — never a false "no storm".
    let mut raw = fixtures::healthy();
    raw.federation.gossip_rejected = None;
    let p = page(&raw);
    assert_eq!(p.federation.gossip_rejected, None);
    let html = render::page_html(&p);
    assert!(html.contains("gossip backpressure"));
    assert!(html.contains("unknown"));
}

#[test]
fn gossip_storm_visibility_surfaces_the_rejection_count() {
    // A rejection count is surfaced (storm backpressure visible) without being
    // mislabelled as a hard outage (cumulative count ≠ active storm).
    let mut raw = fixtures::healthy();
    raw.federation.gossip_rejected = Some(42);
    let p = page(&raw);
    assert_eq!(p.federation.gossip_rejected, Some(42));
    // The federation stays Operational (visibility, not an alarm) — honest.
    assert_eq!(
        p.service("federation").unwrap().state,
        ServiceState::Operational
    );
    let html = render::page_html(&p);
    assert!(html.contains("42"));
    assert!(html.contains("streams rejected"));
}

#[test]
fn rust_lean_divergence_downs_the_federation() {
    let mut raw = fixtures::healthy();
    raw.federation.divergence = Some(2);
    let p = page(&raw);
    assert_eq!(p.service("federation").unwrap().state, ServiceState::Down);
    assert!(matches!(
        p.federation.differential,
        Differential::Diverged { count: 2 }
    ));
    // A core service down ⇒ major outage.
    assert_eq!(p.overall, OverallStatus::Down);
}

#[test]
fn quorum_arithmetic_is_bft() {
    // n=4 → f=1 → needs 3; n=7 → f=2 → needs 5; n=1 → needs 1.
    assert_eq!(aggregate::quorum_needed(4), 3);
    assert_eq!(aggregate::quorum_needed(7), 5);
    assert_eq!(aggregate::quorum_needed(1), 1);
}

#[test]
fn status_json_is_valid_and_round_trips() {
    let p = page(&fixtures::healthy());
    let json = serde_json::to_string(&p).expect("serialize");
    let v: serde_json::Value = serde_json::from_str(&json).expect("valid json");
    assert_eq!(v["overall"], "operational");
    assert!(v["services"].as_array().unwrap().len() >= 6);
    assert_eq!(v["federation"]["expected"], 5);
    assert!(v["uptime"].as_array().unwrap().len() >= 1);
    // The state slugs are the stable public vocabulary.
    let node = v["services"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["id"] == "node")
        .unwrap();
    assert_eq!(node["state"], "operational");
}

#[test]
fn uptime_reflects_the_down_incident_window() {
    // The healthy fixture carries one resolved 1h DOWN incident in the last 24h.
    let p = page(&fixtures::healthy());
    let h24 = p.uptime.iter().find(|u| u.label == "24h").unwrap();
    assert_eq!(h24.downtime_secs, 3600);
    // (86400 - 3600) / 86400 = 95.833%.
    assert!(
        (h24.uptime_pct - 95.833).abs() < 0.01,
        "got {}",
        h24.uptime_pct
    );
    // The degraded-severity incident does NOT subtract from uptime.
    let d7 = p.uptime.iter().find(|u| u.label == "7d").unwrap();
    assert_eq!(d7.downtime_secs, 3600);
}

#[test]
fn open_incident_runs_to_now_in_uptime() {
    let p = page(&fixtures::outage());
    // The outage fixture adds an ongoing DOWN incident started 15 min before now.
    let h24 = p.uptime.iter().find(|u| u.label == "24h").unwrap();
    // 15 min (open) + the earlier 1h resolved = 4500s downtime.
    assert_eq!(h24.downtime_secs, 900 + 3600);
    // The open incident is newest-first and unresolved.
    assert!(p.incidents.first().unwrap().is_open());
}

#[test]
fn html_renders_banner_services_and_federation() {
    let p = page(&fixtures::healthy());
    let html = render::page_html(&p);
    assert!(html.contains("All Systems Operational"));
    assert!(html.contains("DreggNet Status"));
    // Per-service rows.
    assert!(html.contains("Node (consensus)"));
    assert!(html.contains("Economy (conservation)"));
    // Federation panel.
    assert!(html.contains("Federation"));
    assert!(html.contains("dregg-1"));
    assert!(html.contains("rust↔lean: agreeing"));
    // Incident log + the /status.json link + the honesty note.
    assert!(html.contains("Recent incidents"));
    assert!(html.contains("/status.json"));
    assert!(html.contains("Unknown"));
}

#[test]
fn degraded_html_shows_unknown_pill_for_unreachable() {
    let p = page(&fixtures::degraded());
    let html = render::page_html(&p);
    assert!(html.contains("Partial Service Degradation"));
    // The unreachable control surface renders an Unknown pill, not Operational.
    assert!(html.contains("pill unknown"));
}

#[test]
fn html_escapes_incident_text() {
    let mut raw = fixtures::healthy();
    raw.incidents.insert(
        0,
        Incident {
            id: "inc_xss".into(),
            title: "<script>alert(1)</script>".into(),
            severity: "info".into(),
            started_at: "2026-06-30T11:00:00Z".into(),
            resolved_at: Some("2026-06-30T11:05:00Z".into()),
            affected: vec![],
            body: "a & b < c".into(),
        },
    );
    let html = render::page_html(&page(&raw));
    assert!(!html.contains("<script>alert(1)</script>"));
    assert!(html.contains("&lt;script&gt;"));
    assert!(html.contains("a &amp; b &lt; c"));
}

#[test]
fn fixture_source_drives_the_public_entry_point() {
    // The whole-page entry point works through the trait object (as the server uses it).
    let src = FixtureSource::healthy();
    let raw = src.health();
    let p = build(
        &raw,
        FIXTURE_NOW_RFC3339.to_string(),
        fixture_now_epoch(),
        &src.uptime_windows(),
    );
    assert_eq!(p.overall, OverallStatus::Operational);
    assert_eq!(p.uptime.len(), 3); // 24h / 7d / 30d default windows
}
