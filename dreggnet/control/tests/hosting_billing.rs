//! End-to-end proof of the metered-`$DREGG` hosting billing rail
//! (`docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.5), driven through the local / in-process
//! path: a real published site cell served over the real serving loop, its bandwidth
//! accrued by the byte-counter in the serving path, rolled up + settled through the
//! same conserving exactly-once ledger compute-leases use, and an over-budget site
//! lapsing (serving stops). Plus publish/cert/build/uptime each metering + settling.
//!
//! This is the safe-autonomous half: every charge settles through the in-process
//! [`ConservingLedger`]. Pointing the same meter at the real
//! `NodeApiSettlement` (real `$DREGG`, real on-chain `Transfer`) is the S3-gated flip
//! — the seam is identical, so what this proves carries over unchanged.

use std::sync::Arc;

use dreggnet_control::{
    BandwidthMeter, BandwidthOutcome, ConservingLedger, HostingMeter, HostingPricing,
};
use dreggnet_webapp::WebRequest;
use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};

const DREGG: &str = "DREGG";

fn blog_content() -> SiteContent {
    SiteContent::new()
        .with(
            "/index.html",
            "<h1>served on example.com</h1><p>a hosted dregg cell</p>",
        )
        .with("/style.css", "h1{color:teal}body{font-family:system-ui}")
}

/// Serve a site → bandwidth accrues in the serving path → metered + settled
/// (Σδ=0, exactly-once); a publish/cert/build/uptime each meter + settle.
#[test]
fn hosting_resources_meter_and_settle_through_the_conserving_ledger() {
    // The shared bandwidth byte-counter: the serving path records into it, the
    // control meter rolls it up.
    let bandwidth = Arc::new(BandwidthMeter::new());
    // The real static-hosting data plane, metered.
    let registry = SiteRegistry::with_bandwidth(Arc::clone(&bandwidth));

    // The conserving exactly-once ledger (the same rail compute-leases settle on).
    let ledger = Arc::new(ConservingLedger::new());
    ledger.fund(DREGG, "agent:ember", 10_000);
    let meter = HostingMeter::new(
        HostingPricing::default(),
        ledger.clone(),
        DREGG,
        "dreggnet-provider",
        Arc::clone(&bandwidth),
    );
    meter.register_site("blog", "agent:ember");

    // --- PUBLISH: a cap-gated publish turn, then meter the publish charge. ---
    let receipt = registry
        .publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            blog_content(),
        )
        .expect("publish");
    let stored: u64 = blog_content()
        .assets
        .values()
        .map(|a| a.body.len() as u64)
        .sum();
    let pub_charge = meter
        .meter_publish("blog", "agent:ember", stored, receipt.seq)
        .expect("meter publish");
    assert!(pub_charge.units > 0);
    assert!(!pub_charge.settle.replayed);

    // --- SERVE: every successful serve accrues its body bytes for the site. ---
    let mut served_bytes = 0u64;
    for _ in 0..1000 {
        let resp = registry.resolve("blog.example.com", &WebRequest::get("/"));
        assert_eq!(resp.status, 200);
        served_bytes += resp.body.len() as u64;
        let css = registry.resolve("blog.example.com", &WebRequest::get("/style.css"));
        assert_eq!(css.status, 200);
        served_bytes += css.body.len() as u64;
    }
    assert_eq!(
        bandwidth.served("blog"),
        served_bytes,
        "the serving path counted every byte"
    );
    assert_eq!(bandwidth.unbilled("blog"), served_bytes);

    // --- BANDWIDTH: roll up the served bytes into one settled charge. ---
    let bw_units = match meter.tick_bandwidth("blog", "agent:ember").unwrap() {
        BandwidthOutcome::Charged {
            bytes,
            units,
            period,
        } => {
            assert_eq!(bytes, served_bytes);
            assert_eq!(period, 1);
            assert!(units > 0);
            units
        }
        other => panic!("expected a bandwidth charge, got {other:?}"),
    };
    // The cursor advanced — a second roll-up with no new traffic settles nothing.
    assert_eq!(bandwidth.unbilled("blog"), 0);
    assert_eq!(
        meter.tick_bandwidth("blog", "agent:ember").unwrap(),
        BandwidthOutcome::NoTraffic
    );

    // --- CERT / BUILD / UPTIME: each meters + settles. ---
    let cert = meter
        .meter_cert("blog.example.com", "agent:ember", 0)
        .unwrap();
    let build = meter.meter_build("deploy-1", "agent:ember", 4, 0).unwrap();
    let uptime = meter.meter_uptime("blog", "agent:ember", 1).unwrap();

    // The provider was credited exactly the sum of every charge; supply conserved.
    let total = pub_charge.units + bw_units + cert.units + build.units + uptime.units;
    assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), total);
    assert_eq!(ledger.balance(DREGG, "agent:ember"), 10_000 - total);
    assert_eq!(
        ledger.total_supply(DREGG),
        10_000,
        "Σδ = 0 across all hosting charges"
    );

    // --- EXACTLY-ONCE: re-metering any charge moves no value again. ---
    let replay = meter
        .meter_publish("blog", "agent:ember", stored, receipt.seq)
        .expect("replay");
    assert!(replay.settle.replayed);
    assert_eq!(
        ledger.balance(DREGG, "dreggnet-provider"),
        total,
        "a replayed charge settles nothing new"
    );
}

/// An over-budget site lapses (stops serving): once the owner's spend account can no
/// longer fund a bandwidth roll-up, the meter lapses the site and the serving path
/// refuses it with `402` — the hosting analog of a lapsed compute lease being reaped.
#[test]
fn an_over_budget_site_lapses_and_stops_serving() {
    let bandwidth = Arc::new(BandwidthMeter::new());
    let registry = SiteRegistry::with_bandwidth(Arc::clone(&bandwidth));

    let ledger = Arc::new(ConservingLedger::new());
    // A thin budget: enough for one bandwidth roll-up (5 units / MiB), not two.
    ledger.fund(DREGG, "agent:ember", 5);
    let meter = HostingMeter::new(
        HostingPricing::default(),
        ledger.clone(),
        DREGG,
        "dreggnet-provider",
        Arc::clone(&bandwidth),
    );
    meter.register_site("blog", "agent:ember");
    registry
        .publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            blog_content(),
        )
        .expect("publish");

    // Serve + accrue ~1 MiB, roll up → settles (affordable).
    bandwidth.record("blog", 1024 * 1024);
    assert!(matches!(
        meter.tick_bandwidth("blog", "agent:ember").unwrap(),
        BandwidthOutcome::Charged { .. }
    ));
    // The site still serves (live).
    assert_eq!(
        registry
            .resolve("blog.example.com", &WebRequest::get("/"))
            .status,
        200
    );

    // Accrue another MiB; the owner is now broke → the roll-up lapses the site.
    bandwidth.record("blog", 1024 * 1024);
    assert!(matches!(
        meter.tick_bandwidth("blog", "agent:ember").unwrap(),
        BandwidthOutcome::Lapsed { .. }
    ));
    assert!(bandwidth.is_lapsed("blog"));

    // Serving now stops: a lapsed site is refused with 402, and accrues no bandwidth.
    let before = bandwidth.served("blog");
    let resp = registry.resolve("blog.example.com", &WebRequest::get("/"));
    assert_eq!(resp.status, 402, "a lapsed site stops serving");
    assert_eq!(
        bandwidth.served("blog"),
        before,
        "a refused serve accrues nothing"
    );

    // Σδ = 0 held throughout (only one affordable roll-up settled).
    assert_eq!(ledger.total_supply(DREGG), 5);
    assert_eq!(ledger.balance(DREGG, "dreggnet-provider"), 5);
}
