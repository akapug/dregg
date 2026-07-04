//! Regression: the node-agent must serve a BURST of concurrent `/fulfill`
//! requests without the duroxide store deadlocking — the "duroxide DB deadlock on
//! startup, never binds" finding from node-b's PSU power event (an operator's homelab,
//! recovery thread 2026-06-29).
//!
//! ## What actually wedged
//!
//! The node-agent (`deploy/node-agent`) spawns one tokio task per inbound
//! connection and each `/fulfill` calls [`dreggnet_bridge::fulfill`], which opens a
//! duroxide SQLite store for the durable workflow. The store was opened via
//! duroxide's `SqliteProvider::new_in_memory()` — `sqlite::memory:?cache=shared`. A
//! **shared-cache in-memory** SQLite database uses **table-level** locking, and
//! duroxide drives each store with a *pool of connections* (its orchestrator and
//! worker dispatchers, concurrently). Two connections that each hold a read lock and
//! try to upgrade to a write lock **deadlock** — SQLite returns `SQLITE_LOCKED`
//! (code 6, *"database is deadlocked"*), which `PRAGMA busy_timeout` does NOT cover
//! (it only retries `SQLITE_BUSY`). duroxide flags that retryable and backs off, so a
//! post-power-event burst of concurrent dispatch/health/retry traffic drowned the
//! agent in a "database is deadlocked, backing off" retry storm that pegged the
//! runtime and starved its accept loop — it served nothing despite the bind.
//!
//! The fix ([`dreggnet_bridge::fulfill`]) backs each call with its OWN on-disk
//! **WAL** database (a process-unique temp dir, torn down when the call returns). WAL
//! journaling lets readers run without blocking the writer and resolves writer
//! contention via `busy_timeout` (`SQLITE_BUSY`, retried-and-*progresses*) instead of
//! a hard `SQLITE_LOCKED` deadlock — so the burst runs to completion, deadlock-free.
//!
//! ## How this test pins it
//!
//! It runs a wide burst of `fulfill`s at once and asserts two things:
//!   1. every request completes with the correct metered result (functional);
//!   2. duroxide emits **zero** "deadlocked" WARN events across the burst — captured
//!      with a tracing layer, this is the exact symptom an operator observed, so the test
//!      fails on the old shared-store code and passes on the isolated-store fix.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use dreggnet_bridge::{CapGrade, Lease, fulfill};
use tracing::field::{Field, Visit};
use tracing::span;

/// A minimal `tracing::Subscriber` that counts events whose formatted message
/// mentions a deadlock — duroxide logs `... database is deadlocked ... backing off`
/// on shared-store contention, so this directly observes the node-b symptom. It
/// uses only the `tracing` crate (no tracing-subscriber), so it has no extra
/// dependency surface. Spans are no-ops; only `event` is meaningful here.
#[derive(Clone, Default)]
struct DeadlockCounter(Arc<AtomicUsize>);

struct MsgVisitor {
    hit: bool,
}
impl Visit for MsgVisitor {
    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        if field.name() == "message" && format!("{value:?}").contains("deadlock") {
            self.hit = true;
        }
    }
    fn record_str(&mut self, field: &Field, value: &str) {
        if field.name() == "message" && value.contains("deadlock") {
            self.hit = true;
        }
    }
}

impl tracing::Subscriber for DeadlockCounter {
    fn enabled(&self, _md: &tracing::Metadata<'_>) -> bool {
        true
    }
    fn new_span(&self, _attrs: &span::Attributes<'_>) -> span::Id {
        span::Id::from_u64(1)
    }
    fn record(&self, _span: &span::Id, _values: &span::Record<'_>) {}
    fn record_follows_from(&self, _span: &span::Id, _follows: &span::Id) {}
    fn event(&self, event: &tracing::Event<'_>) {
        let mut v = MsgVisitor { hit: false };
        event.record(&mut v);
        if v.hit {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }
    fn enter(&self, _span: &span::Id) {}
    fn exit(&self, _span: &span::Id) {}
}

/// A wide burst of concurrent fulfillments completes correctly with NO deadlock.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn concurrent_fulfill_burst_does_not_deadlock() {
    // Enough concurrency to force shared-cache table-lock contention if the stores
    // were shared. Each is the default add(40,2)→×2 dogfood lease.
    const N: usize = 64;

    // A process-GLOBAL subscriber: duroxide's worker/orchestration dispatchers run
    // on other tokio worker threads, so a thread-local `set_default` would miss
    // their "database is deadlocked" warnings. This test binary has a single test,
    // so claiming the global default is safe.
    let counter = DeadlockCounter::default();
    let deadlocks = counter.0.clone();
    tracing::subscriber::set_global_default(counter).expect("set global tracing subscriber");

    let mut handles = Vec::with_capacity(N);
    for i in 0..N {
        handles.push(tokio::spawn(async move {
            let lease = Lease::funded("agent-mesh", CapGrade::Sandboxed, "USD-mesh", 100, 1);
            let instance = format!("mesh-wl-{i}");
            fulfill(&lease, &instance).await
        }));
    }

    let mut ok = 0usize;
    for (i, h) in handles.into_iter().enumerate() {
        let out = h
            .await
            .expect("fulfill task panicked")
            .unwrap_or_else(|e| panic!("fulfill #{i} failed (deadlock/timeout?): {e}"));
        assert_eq!(out.step1.trim(), "42", "fulfill #{i} step1");
        assert_eq!(out.step2.trim(), "84", "fulfill #{i} step2");
        assert_eq!(out.meter_units, 2, "fulfill #{i} meter");
        ok += 1;
    }
    assert_eq!(ok, N, "every concurrent fulfill completed");

    let n_deadlocks = deadlocks.load(Ordering::Relaxed);
    assert_eq!(
        n_deadlocks, 0,
        "duroxide reported {n_deadlocks} `database is deadlocked` (SQLITE_LOCKED) \
         events across the burst — the in-memory shared-cache store is deadlocking \
         under concurrent load (the node-b power-event wedge). fulfill must back the \
         durable workflow with an on-disk WAL store."
    );
}
