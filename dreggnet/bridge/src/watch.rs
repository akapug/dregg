//! The lease **WATCHER** — the second half of the DreggNet bridge.
//!
//! Rung 3 ([`crate::fulfill`]) welded a *single* funded lease to a durable polyana
//! workflow. This module closes the loop: DreggNet **watches a feed of funded dregg
//! execution-leases and fulfills each as it arrives**.
//!
//! ```text
//!   LeaseFeed (funded leases arrive) ─┐
//!                                      ├─ LeaseWatcher::watch
//!     per lease: map cap_grade→tier ──┤     • spawn fulfill (concurrent)
//!                call fulfill ─────────┤     • track running workloads
//!                track / reap ─────────┘     • reap each on completion / lapse
//! ```
//!
//! ## What the watch loop does (per lease)
//!
//! 1. Pull the next funded [`crate::Lease`] off the [`LeaseFeed`].
//! 2. Its cap-grade already maps to a polyana tier via [`crate::map_cap_grade`];
//!    [`crate::fulfill`] runs that mapping + the budget gate on the same path, so the
//!    watcher just hands the lease to `fulfill`.
//! 3. Spawn the durable workflow as a tracked, **running** task (concurrent — the
//!    durable metrics ledger is keyed per instance, so concurrent leases never alias).
//! 4. **Reap** each lease as its task finishes:
//!    - a completed workflow → [`Fulfilled`] (its metered [`WorkflowOutput`]);
//!    - an over-budget tick / lapsed lease → [`Reaped`] with [`ReapReason::Lapsed`]
//!      — the workflow yielded NO claimable result, so **no unpaid work is billed**;
//!    - an unfunded / ill-formed / under-graded lease → [`Reaped`] with
//!      [`ReapReason::NotAuthorized`] — `fulfill` never started a workflow at all.
//!
//! ## Real vs mock (read this)
//!
//! - **Real:** the watch→fulfill→reap **loop** itself — it concurrently fulfills
//!   every lease a feed yields, tracks the running set, and reaps each on
//!   completion/lapse, with the same budget gate + durable metering `fulfill` proves.
//! - **Source of leases:** [`MockFeed`] is an in-memory channel of leases (the dev
//!   source the tests drive on the default Apache/offline build). The REAL feed —
//!   [`DreggNodeFeed`] — reads funded execution-leases from a dregg node's receipt
//!   log through the [`crate::dregg_verify`] seam (`query_shadow_attest_whole_log`,
//!   a verified whole-log attestation). It is **wired behind the `dregg-verify`
//!   feature** (off by default for AGPL isolation): feature-off it is structurally
//!   inert (yields nothing), feature-on `DreggNodeFeed::from_node_log` attests the
//!   log and decodes each funded lease grant into a [`crate::Lease`]. The remaining
//!   step is the live light-client RPC that fetches the records (see
//!   [`crate::dregg_verify`]).

use std::future::Future;

use tokio::sync::mpsc::{self, UnboundedReceiver, UnboundedSender};
use tokio::task::JoinSet;

use crate::{BridgeError, Lease, WorkflowOutput, fulfill};

/// One lease as it arrives off a [`LeaseFeed`], paired with the durable instance
/// key its workflow runs under.
///
/// The `instance` is the stable identity the watcher tracks the running workload by
/// (and the duroxide orchestration id). Real leases derive it from the lease cell's
/// `CellId`; the [`MockFeed`] lets the caller choose it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeedItem {
    /// The durable workflow instance id this lease is fulfilled under.
    pub instance: String,
    /// The funded lease authorizing the work.
    pub lease: Lease,
}

impl FeedItem {
    /// A feed item: fulfill `lease` under durable instance `instance`.
    pub fn new(instance: impl Into<String>, lease: Lease) -> FeedItem {
        FeedItem {
            instance: instance.into(),
            lease,
        }
    }
}

/// A source of funded dregg execution-leases. The watcher pulls one item at a time;
/// `None` means the feed is exhausted and the watch loop drains its running set and
/// returns.
///
/// This is the seam between "where leases come from" (mock channel today, a dregg
/// light-client read tomorrow — see [`DreggNodeFeed`]) and the watch→fulfill→reap
/// loop, which is real regardless of the source.
pub trait LeaseFeed {
    /// Yield the next funded lease, or `None` when the feed is exhausted.
    fn next_lease(&mut self) -> impl Future<Output = Option<FeedItem>> + Send;
}

/// A successfully fulfilled lease: its workflow completed within budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fulfilled {
    /// The durable instance the workflow ran under.
    pub instance: String,
    /// The lessee the lease authorized.
    pub lessee: String,
    /// The metered terminal result of the durable workflow.
    pub output: WorkflowOutput,
}

/// A reaped lease: it produced no claimable, billable work.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reaped {
    /// The durable instance the (refused or lapsed) workflow was keyed under.
    pub instance: String,
    /// The lessee the lease named.
    pub lessee: String,
    /// Why it was reaped.
    pub reason: ReapReason,
}

/// Why a lease was reaped rather than fulfilled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReapReason {
    /// The lease never authorized work: unfunded, ill-formed, or its cap-grade was
    /// below the workload floor. [`crate::fulfill`] refused before starting any
    /// workflow — truly no unpaid work.
    NotAuthorized(BridgeError),
    /// The lease lapsed mid-flight: an over-budget meter tick failed the workflow,
    /// so it yielded no claimable result. The string carries the durable lapse
    /// detail (e.g. the over-budget step that tripped it).
    Lapsed(String),
}

/// The terminal tally of a watch run: every lease the feed yielded, partitioned into
/// the ones fulfilled within budget and the ones reaped (refused or lapsed).
///
/// The invariant the watcher upholds: `fulfilled.len() + reaped.len()` equals the
/// number of leases the feed yielded, and **no reaped lease was billed** for work.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WatchReport {
    /// Leases whose durable workflow completed within budget.
    pub fulfilled: Vec<Fulfilled>,
    /// Leases that produced no billable work (refused or lapsed).
    pub reaped: Vec<Reaped>,
}

impl WatchReport {
    /// Total leases accounted for (fulfilled + reaped).
    pub fn total(&self) -> usize {
        self.fulfilled.len() + self.reaped.len()
    }

    fn record(&mut self, outcome: LeaseOutcome) {
        match outcome {
            LeaseOutcome::Fulfilled(f) => self.fulfilled.push(f),
            LeaseOutcome::Reaped(r) => self.reaped.push(r),
        }
    }
}

enum LeaseOutcome {
    Fulfilled(Fulfilled),
    Reaped(Reaped),
}

/// The watch→fulfill→reap loop.
///
/// [`watch`](LeaseWatcher::watch) drains a [`LeaseFeed`], fulfilling every funded
/// lease concurrently, tracking the running workloads, and reaping each as it
/// completes or lapses. It returns once the feed is exhausted and all running
/// workloads have settled.
pub struct LeaseWatcher;

impl LeaseWatcher {
    /// Watch `feed` to exhaustion, fulfilling and reaping every lease.
    ///
    /// Leases are fulfilled **concurrently**: each lease's durable workflow runs in
    /// its own task (its own in-memory duroxide store + per-instance metrics ledger,
    /// so there is no cross-lease aliasing). New leases are pulled while earlier ones
    /// are still running; each running workload is reaped into the [`WatchReport`] as
    /// it settles. When the feed yields `None`, the loop drains the remaining running
    /// set and returns the full tally.
    pub async fn watch<F: LeaseFeed>(mut feed: F) -> WatchReport {
        let mut running: JoinSet<LeaseOutcome> = JoinSet::new();
        let mut report = WatchReport::default();
        let mut feed_open = true;

        loop {
            tokio::select! {
                // Pull the next funded lease (only while the feed is still open).
                item = feed.next_lease(), if feed_open => match item {
                    Some(FeedItem { instance, lease }) => {
                        // Spawn the durable fulfillment as a tracked, running workload.
                        running.spawn(fulfill_one(instance, lease));
                    }
                    None => feed_open = false,
                },
                // Reap a running workload as it settles (disabled when none run, so
                // the loop doesn't busy-spin on `JoinSet`'s empty `None`).
                Some(joined) = running.join_next(), if !running.is_empty() => {
                    if let Ok(outcome) = joined {
                        report.record(outcome);
                    }
                    // A `JoinError` (task panic/abort) is dropped: `fulfill_one` is
                    // infallible by construction, so this is not expected to fire.
                }
            }

            // Feed exhausted and nothing left running → done.
            if !feed_open && running.is_empty() {
                break;
            }
        }

        report
    }
}

/// Fulfill one lease and classify the outcome. Infallible: every result (success,
/// lapse, or refusal) becomes a [`LeaseOutcome`] the watcher tracks.
async fn fulfill_one(instance: String, lease: Lease) -> LeaseOutcome {
    let lessee = lease.lessee.clone();
    match fulfill(&lease, &instance).await {
        Ok(output) => LeaseOutcome::Fulfilled(Fulfilled {
            instance,
            lessee,
            output,
        }),
        // An over-budget tick / lapsed lease: the workflow failed, no claimable work.
        Err(BridgeError::WorkflowFailed(detail)) => LeaseOutcome::Reaped(Reaped {
            instance,
            lessee,
            reason: ReapReason::Lapsed(detail),
        }),
        // Unfunded / ill-formed / under-graded: never authorized, never started.
        Err(other) => LeaseOutcome::Reaped(Reaped {
            instance,
            lessee,
            reason: ReapReason::NotAuthorized(other),
        }),
    }
}

// ---------------------------------------------------------------------------
// MockFeed — the dev source (in-memory channel of leases).
// ---------------------------------------------------------------------------

/// The sending half of a [`MockFeed`]: push funded leases at the watcher as they
/// "arrive". Drop it to close the feed (the watch loop then drains and returns).
#[derive(Debug, Clone)]
pub struct MockFeedSender {
    tx: UnboundedSender<FeedItem>,
}

impl MockFeedSender {
    /// Push a lease onto the feed under instance `instance`.
    pub fn send(&self, instance: impl Into<String>, lease: Lease) -> Result<(), Lease> {
        self.tx
            .send(FeedItem::new(instance, lease))
            .map_err(|e| e.0.lease)
    }
}

/// An **in-memory channel feed** of funded leases — the dev/test source.
///
/// Leases arrive over a channel, modelling a real feed without any dregg dependency
/// (so the watch→fulfill→reap loop is testable on the default Apache/offline build).
/// Use [`MockFeed::channel`] to push leases over time, or [`MockFeed::from_items`]
/// for a pre-loaded batch.
pub struct MockFeed {
    rx: UnboundedReceiver<FeedItem>,
}

impl MockFeed {
    /// A live feed plus its sender. Push leases via the [`MockFeedSender`]; the feed
    /// ends when every sender is dropped.
    pub fn channel() -> (MockFeedSender, MockFeed) {
        let (tx, rx) = mpsc::unbounded_channel();
        (MockFeedSender { tx }, MockFeed { rx })
    }

    /// A feed pre-loaded with `items`, which ends after the last is yielded.
    pub fn from_items(items: impl IntoIterator<Item = FeedItem>) -> MockFeed {
        let (tx, rx) = mpsc::unbounded_channel();
        for item in items {
            // The receiver is held in the returned `MockFeed`, so this cannot fail.
            let _ = tx.send(item);
        }
        // Dropping `tx` here closes the feed once the buffered items drain.
        MockFeed { rx }
    }
}

impl LeaseFeed for MockFeed {
    fn next_lease(&mut self) -> impl Future<Output = Option<FeedItem>> + Send {
        async move { self.rx.recv().await }
    }
}

// ---------------------------------------------------------------------------
// DreggNodeFeed — the named real feed (the wire to flip on later).
// ---------------------------------------------------------------------------

/// The **real** lease feed: funded execution-leases read from a dregg node's
/// receipt log via a verified whole-log attestation.
///
/// Behind the `dregg-verify` feature, [`from_node_log`](DreggNodeFeed::from_node_log)
/// runs [`crate::dregg_verify::read_funded_leases`]: it attests the node's receipt
/// log (`query_shadow_attest_whole_log` — fail-closed if the log does not verify
/// against its MMR root), decodes each attested funded execution-lease grant into a
/// [`crate::Lease`], and queues the result. [`next_lease`](LeaseFeed::next_lease)
/// then drains that queue to the watch→fulfill→reap loop, which is unchanged.
///
/// On the default Apache/offline build the dregg verified-core is NOT linked (AGPL
/// isolation — see [`crate::dregg_verify`]), so `from_node_log` does not exist and
/// the only constructor ([`new`](DreggNodeFeed::new)) leaves the queue empty: the
/// feed yields nothing and a watch run over it is a clean no-op.
///
/// **What is real vs pending a live node:** the verified read + funded-lease decode
/// are real (exercised feature-on in `dregg_verify`'s tests). The *transport* that
/// fetches the receipt-log records from a live dregg node / light client over
/// `node_endpoint` is the remaining step — today the records are handed to
/// `from_node_log`; the live light-client RPC that produces them is named, not yet
/// wired (see `crate::dregg_verify`).
pub struct DreggNodeFeed {
    /// The dregg node / light-client endpoint the real read polls. Recorded so the
    /// routing is explicit even on the default build.
    pub node_endpoint: String,
    /// Decoded funded leases awaiting delivery to the watcher, in receipt order.
    /// Empty on the default build (no constructor populates it without the
    /// verified-core link), which is what makes the feed structurally inert there.
    pending: std::collections::VecDeque<FeedItem>,
}

impl DreggNodeFeed {
    /// Name the real feed against a dregg node endpoint, with no leases queued.
    /// On the default build this is the only constructor, so the feed is inert
    /// (yields `None`). Feed it via [`from_node_log`](DreggNodeFeed::from_node_log)
    /// under `dregg-verify`.
    pub fn new(node_endpoint: impl Into<String>) -> DreggNodeFeed {
        DreggNodeFeed {
            node_endpoint: node_endpoint.into(),
            pending: std::collections::VecDeque::new(),
        }
    }

    /// Build the real feed from a dregg node's receipt-log records: attest the
    /// whole log and decode every funded execution-lease grant into a queued
    /// [`FeedItem`] (see [`crate::dregg_verify::read_funded_leases`]). Returns
    /// `Err` if the log is empty or does not verify against its root (fail-closed).
    ///
    /// `records` is the receipt log fetched from the node at `node_endpoint`; the
    /// live light-client RPC that produces it is the remaining transport step.
    #[cfg(feature = "dregg-verify")]
    pub fn from_node_log(
        node_endpoint: impl Into<String>,
        records: &[polyana_dregg_bridge::QueryShadowRecord],
    ) -> Result<DreggNodeFeed, polyana_dregg_bridge::QueryShadowError> {
        let pending = crate::dregg_verify::read_funded_leases(records)?.into();
        Ok(DreggNodeFeed {
            node_endpoint: node_endpoint.into(),
            pending,
        })
    }
}

impl LeaseFeed for DreggNodeFeed {
    fn next_lease(&mut self) -> impl Future<Output = Option<FeedItem>> + Send {
        // Drain the queue the verified read filled. On the default build the queue
        // is always empty (no `from_node_log`), so the feed is a clean no-op.
        async move { self.pending.pop_front() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CapGrade;

    /// The named real feed is inert on the default build: with the verified core
    /// NOT linked, `new` is the only constructor and it yields nothing, so a watch
    /// run over it is a clean no-op. (Feature-on, `from_node_log` populates it — see
    /// `crate::dregg_verify`'s tests — so this default-build assertion is gated off.)
    #[cfg(not(feature = "dregg-verify"))]
    #[tokio::test]
    async fn dregg_node_feed_is_inert_on_default_build() {
        assert!(!crate::dregg_verify::DREGG_VERIFY_ENABLED);
        let feed = DreggNodeFeed::new("dregg-node://localhost");
        let report = LeaseWatcher::watch(feed).await;
        assert_eq!(report.total(), 0);
    }

    /// Feature-on, an empty node feed (no records fed) still yields nothing — a
    /// watch over a not-yet-populated `DreggNodeFeed::new` is a clean no-op.
    #[cfg(feature = "dregg-verify")]
    #[tokio::test]
    async fn dregg_node_feed_new_is_empty_until_populated() {
        assert!(crate::dregg_verify::DREGG_VERIFY_ENABLED);
        let feed = DreggNodeFeed::new("dregg-node://localhost");
        let report = LeaseWatcher::watch(feed).await;
        assert_eq!(report.total(), 0);
    }

    /// `from_items` yields its leases in order, then ends.
    #[tokio::test]
    async fn mock_feed_from_items_drains_then_ends() {
        let lease = Lease::funded("a", CapGrade::Sandboxed, "USD", 100, 1);
        let mut feed = MockFeed::from_items([FeedItem::new("i-1", lease.clone())]);
        let first = feed.next_lease().await.expect("one item");
        assert_eq!(first.instance, "i-1");
        assert_eq!(first.lease, lease);
        assert!(feed.next_lease().await.is_none());
    }
}
