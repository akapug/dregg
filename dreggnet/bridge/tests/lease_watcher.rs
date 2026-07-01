//! The watcher proof: DreggNet watches a feed of funded dregg execution-leases and
//! fulfills each — the WATCH→FULFILL→REAP loop, end to end, over a [`MockFeed`].
//!
//! Rung 3 (`fulfill`) welded a single lease to a durable polyana workflow. This
//! proves the loop around it:
//!
//!   1. A MockFeed yields TWO funded leases → the watcher fulfills BOTH (each runs
//!      its durable 2-step polyana workflow — `add(40,2)`→`*2` — metered against its
//!      own budget, with its own per-instance meter ledger).
//!   2. An OVER-BUDGET lease (budget 1, 1 unit/step) is REAPED: step1's tick fits,
//!      step2's lapses → the workflow fails → NO claimable result. No unpaid work is
//!      billed or delivered.
//!   3. An UNFUNDED lease is REAPED before any workflow starts (never authorized).
//!   4. All of the above arrive on the SAME feed and are fulfilled CONCURRENTLY
//!      (the watcher tracks the running set and reaps each as it settles).

use dreggnet_bridge::{CapGrade, FeedItem, Lease, LeaseWatcher, MockFeed, ReapReason, metrics};

/// The keystone: two funded leases are both fulfilled; an over-budget lease and an
/// unfunded lease are both reaped with no unpaid work — all off one concurrent feed.
#[tokio::test]
async fn watcher_fulfills_funded_leases_and_reaps_lapsed_ones() {
    // Two genuinely funded leases (budget covers both metered steps).
    let funded_a = Lease::funded("agent-a", CapGrade::Sandboxed, "USD-test", 100, 1);
    let funded_b = Lease::funded("agent-b", CapGrade::MicroVm, "USD-test", 50, 2);
    // An over-budget lease: budget 1, but the 2-step workflow needs 2 units → lapses.
    let over_budget = Lease::funded("agent-broke", CapGrade::Sandboxed, "USD-test", 1, 1);
    // An unfunded lease authorizes no work at all.
    let unfunded = Lease {
        lessee: "agent-deadbeat".into(),
        cap_grade: CapGrade::Sandboxed,
        asset: "USD-test".into(),
        budget_units: 100,
        per_period_units: 1,
        funded: false,
    };

    let feed = MockFeed::from_items([
        FeedItem::new("watch-funded-a", funded_a),
        FeedItem::new("watch-funded-b", funded_b),
        FeedItem::new("watch-over-budget", over_budget),
        FeedItem::new("watch-unfunded", unfunded),
    ]);

    let report = LeaseWatcher::watch(feed).await;

    // Every one of the four leases is accounted for: two fulfilled, two reaped.
    assert_eq!(
        report.total(),
        4,
        "every lease the feed yielded is accounted for"
    );
    assert_eq!(report.fulfilled.len(), 2, "both funded leases fulfilled");
    assert_eq!(
        report.reaped.len(),
        2,
        "the over-budget and unfunded leases reaped"
    );

    // --- The two funded leases were fulfilled, each metered against its own budget.
    let a = report
        .fulfilled
        .iter()
        .find(|f| f.instance == "watch-funded-a")
        .expect("funded-a fulfilled");
    assert_eq!(a.lessee, "agent-a");
    assert_eq!(a.output.step1, "42"); // polyana add(40, 2)
    assert_eq!(a.output.step2, "84"); // polyana 42 * 2
    assert_eq!(a.output.meter_units, 2); // two steps × 1 unit
    assert_eq!(metrics::meter_units("watch-funded-a"), 2);

    let b = report
        .fulfilled
        .iter()
        .find(|f| f.instance == "watch-funded-b")
        .expect("funded-b fulfilled");
    assert_eq!(b.lessee, "agent-b");
    assert_eq!(b.output.meter_units, 4); // two steps × 2 units

    // --- The over-budget lease was reaped (lapsed): no claimable output exists.
    let lapsed = report
        .reaped
        .iter()
        .find(|r| r.instance == "watch-over-budget")
        .expect("over-budget reaped");
    assert_eq!(lapsed.lessee, "agent-broke");
    assert!(
        matches!(&lapsed.reason, ReapReason::Lapsed(_)),
        "over-budget lease lapsed, got {:?}",
        lapsed.reason
    );
    // No unpaid work: the lapsed lease never appears among the fulfilled (billable) set.
    assert!(
        !report
            .fulfilled
            .iter()
            .any(|f| f.instance == "watch-over-budget"),
        "a lapsed lease is never billed/delivered"
    );

    // --- The unfunded lease was reaped without ever starting a workflow.
    let dead = report
        .reaped
        .iter()
        .find(|r| r.instance == "watch-unfunded")
        .expect("unfunded reaped");
    assert_eq!(dead.lessee, "agent-deadbeat");
    assert!(
        matches!(&dead.reason, ReapReason::NotAuthorized(_)),
        "unfunded lease never authorized, got {:?}",
        dead.reason
    );
    // Never authorized → never metered.
    assert_eq!(metrics::meter_units("watch-unfunded"), 0);
}

/// The feed can deliver leases over time (the channel source): the watcher keeps
/// running until the sender is dropped, fulfilling each lease as it arrives.
#[tokio::test]
async fn watcher_drains_a_live_channel_feed() {
    let (tx, feed) = MockFeed::channel();

    // Push leases, then drop the sender to close the feed.
    tx.send(
        "live-1",
        Lease::funded("agent-live-1", CapGrade::Sandboxed, "USD-test", 100, 1),
    )
    .expect("send 1");
    tx.send(
        "live-2",
        Lease::funded("agent-live-2", CapGrade::Caged, "USD-test", 100, 1),
    )
    .expect("send 2");
    drop(tx);

    let report = LeaseWatcher::watch(feed).await;

    assert_eq!(report.fulfilled.len(), 2);
    assert!(report.reaped.is_empty());
    assert_eq!(metrics::meter_units("live-1"), 2);
    assert_eq!(metrics::meter_units("live-2"), 2);
}
