//! Crash-recovery + transactional-outbox proof for the DreggNet durable layer over a
//! **real Postgres** store.
//!
//! This is the Postgres twin of `durable_resume.rs`. The workflow code is identical and
//! provider-agnostic — only the duroxide `Provider` changes (the SQLite provider becomes
//! the in-process `duroxide-pg` `PostgresProvider`), and the `MeterTick` charge lands in
//! the `dreggnet_meter` **transactional outbox** on that provider's pool instead of the
//! in-process ledger. The properties proven:
//!
//! - exactly-once / crash-resume: a step's recorded result is replayed across a runtime
//!   teardown, not re-executed, and the meter is never double-charged;
//! - the outbox is charged **exactly twice** (one row per period), atomic with the steps,
//!   and a crash mid-workflow → resume leaves exactly two rows (idempotent on
//!   `(lease_id, period)`);
//! - over-budget fails the workflow **before any charge commits** — no partial charge row;
//! - a direct double-charge of the same `(lease, period)` writes only one row (the outbox
//!   row is idempotent), which is the structural guarantee behind crash-safety.
//!
//! Honesty / gating: these tests are `#[ignore]` and only run when a live Postgres is
//! reachable via the `DATABASE_URL` env var. The SQLite resume test stays the always-green,
//! offline proof; these are opt-in:
//!
//! ```text
//!   DATABASE_URL=postgres://user:pass@localhost:5432/dreggnet \
//!     cargo test -p dreggnet-durable --features pg --test durable_resume_pg -- --ignored --nocapture
//! ```
//!
//! `duroxide-pg`'s `PostgresProvider::new` migrates the checkpoint schema on startup;
//! `ensure_meter_schema` adds the `dreggnet_meter` outbox table alongside it. The instance
//! id (= the lease id) is made unique per run so repeated runs against the same (persistent)
//! Postgres never collide on an already-completed instance / already-charged lease.
#![cfg(feature = "pg")]

use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use dreggnet_durable::{
    MeterCharge, ORCHESTRATION_NAME, WorkflowInput, WorkflowOutput, build_registries_with_pg_meter,
    ensure_meter_schema, metrics, read_meter_outbox,
};
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};
use duroxide_pg::PostgresProvider;

async fn open_store(database_url: &str) -> Arc<PostgresProvider> {
    let store = Arc::new(
        PostgresProvider::new(database_url)
            .await
            .expect("open postgres durable store (migrates checkpoint schema on startup)"),
    );
    ensure_meter_schema(store.pool())
        .await
        .expect("create the dreggnet_meter outbox table");
    store
}

fn database_url() -> Option<String> {
    match std::env::var("DATABASE_URL") {
        Ok(u) => Some(u),
        Err(_) => {
            eprintln!("DATABASE_URL unset; skipping the Postgres durable-meter test");
            None
        }
    }
}

fn unique_lease(tag: &str) -> String {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    format!("lease-{tag}-pg-{nonce}")
}

#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL; opt-in (the SQLite test is the offline proof)"]
async fn durable_workflow_charges_the_outbox_exactly_once_per_step_across_a_crash() {
    let Some(database_url) = database_url() else {
        return;
    };

    let instance = unique_lease("workflow");
    let instance = instance.as_str();

    let input = serde_json::to_string(&WorkflowInput {
        budget_units: 100,
        cost_per_step: 1,
        // Park after step1 so we can crash deterministically between the two steps.
        pause_event: Some("Resume".to_string()),
    })
    .unwrap();

    // ===== Runtime #1: run up to the checkpoint, then "crash". =====
    {
        let store = open_store(&database_url).await;
        let (activities, orchestrations) =
            build_registries_with_pg_meter(Arc::new(store.pool().clone()));
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());

        client
            .start_orchestration(instance, ORCHESTRATION_NAME, input.clone())
            .await
            .expect("start");

        // Wait until step1 has executed AND the orchestration has parked on the wait
        // (still Running) — i.e. step1 + its meter charge are durably checkpointed/committed.
        let mut parked = false;
        for _ in 0..400 {
            let ran_step1 = metrics::run_calls(instance, "step1") >= 1;
            let status = client.get_orchestration_status(instance).await.unwrap();
            if ran_step1 && matches!(status, OrchestrationStatus::Running { .. }) {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        assert!(parked, "workflow did not reach the post-step1 checkpoint");
        tokio::time::sleep(Duration::from_millis(300)).await;

        // Pre-crash: step1 ran once, step2 not yet, and EXACTLY ONE charge row in the outbox.
        assert_eq!(
            metrics::run_calls(instance, "step1"),
            1,
            "step1 ran once before crash"
        );
        assert_eq!(
            metrics::run_calls(instance, "step2"),
            0,
            "step2 must not have run yet"
        );
        let rows = read_meter_outbox(store.pool(), instance).await.unwrap();
        assert_eq!(rows.len(), 1, "exactly one charge committed so far");
        assert_eq!(rows[0].period, 1);
        assert_eq!(rows[0].running_total, 1);

        // 💥 CRASH: tear the whole runtime down. The Postgres store keeps the checkpoint.
        rt.shutdown(None).await;
    }

    // ===== Runtime #2: resume over the SAME Postgres store. =====
    {
        let store = open_store(&database_url).await;
        let (activities, orchestrations) =
            build_registries_with_pg_meter(Arc::new(store.pool().clone()));
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());

        client
            .raise_event(instance, "Resume", "")
            .await
            .expect("raise");

        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(60))
            .await
            .expect("wait");

        let output = match status {
            OrchestrationStatus::Completed { output, .. } => output,
            other => panic!("workflow did not complete: {other:?}"),
        };
        let out: WorkflowOutput = serde_json::from_str(&output).unwrap();
        assert_eq!(out.step1, "42", "step1 = add(40,2)");
        assert_eq!(out.step2, "84", "step2 = step1 * 2");
        assert_eq!(out.meter_units, 2, "two metered steps total");

        // EXACTLY-ONCE: step1 was NOT re-executed on resume (replayed from the checkpoint).
        assert_eq!(
            metrics::run_calls(instance, "step1"),
            1,
            "step1 replayed, never re-run"
        );
        assert_eq!(
            metrics::run_calls(instance, "step2"),
            1,
            "step2 ran once, post-resume"
        );

        // The OUTBOX holds EXACTLY TWO charge rows — one per period, never doubled by the
        // crash. This is the durable, settlement-readable record.
        let rows = read_meter_outbox(store.pool(), instance).await.unwrap();
        assert_eq!(
            rows.len(),
            2,
            "outbox charged exactly twice (one row per period)"
        );
        assert_eq!(rows[0].period, 1);
        assert_eq!(rows[0].amount, 1);
        assert_eq!(rows[0].running_total, 1);
        assert_eq!(rows[1].period, 2);
        assert_eq!(rows[1].amount, 1);
        assert_eq!(
            rows[1].running_total, 2,
            "running total accumulates across periods"
        );

        rt.shutdown(None).await;
    }
}

/// Over-budget fails the workflow BEFORE any charge for the offending step commits: the
/// outbox holds only the affordable step's charge — no partial charge.
#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn over_budget_fails_before_the_charge_commits() {
    let Some(database_url) = database_url() else {
        return;
    };

    let store = open_store(&database_url).await;
    let instance = unique_lease("too-small");
    let instance = instance.as_str();

    // Budget 1, cost 1/step: step1's charge (total 1) fits; step2's would reach 2 > 1 → lapse.
    let input = serde_json::to_string(&WorkflowInput {
        budget_units: 1,
        cost_per_step: 1,
        pause_event: None,
    })
    .unwrap();

    let (activities, orchestrations) =
        build_registries_with_pg_meter(Arc::new(store.pool().clone()));
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    client
        .start_orchestration(instance, ORCHESTRATION_NAME, input)
        .await
        .expect("start");

    let status = client
        .wait_for_orchestration(instance, Duration::from_secs(60))
        .await
        .expect("wait");

    match status {
        OrchestrationStatus::Failed { details, .. } => assert!(
            details
                .display_message()
                .contains("execution-lease exhausted"),
            "unexpected failure: {}",
            details.display_message()
        ),
        other => panic!("expected lease-exhaustion failure, got: {other:?}"),
    }

    // Only step1's charge committed — the over-budget step2 never wrote a row.
    let rows = read_meter_outbox(store.pool(), instance).await.unwrap();
    assert_eq!(
        rows.len(),
        1,
        "no partial charge: only the affordable step committed"
    );
    assert_eq!(rows[0].period, 1);
    assert_eq!(rows[0].running_total, 1);

    rt.shutdown(None).await;
}

/// The outbox row is idempotent on `(lease_id, period)`: charging the same period twice
/// (what a crash-and-re-run does before a checkpoint) writes one row and returns the same
/// running total — the structural guarantee behind exactly-once.
#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn outbox_charge_is_idempotent_on_lease_period() {
    let Some(database_url) = database_url() else {
        return;
    };

    let store = open_store(&database_url).await;
    let lease = unique_lease("idem");
    let lease = lease.as_str();
    let pool = store.pool();

    // Charge period 1 twice (the re-run a crash would cause) — second call is a no-op insert.
    let t1 = dreggnet_durable::pg::charge_outbox(
        pool,
        lease,
        MeterCharge {
            period: 1,
            amount: 5,
        },
    )
    .await
    .unwrap();
    let t1_again = dreggnet_durable::pg::charge_outbox(
        pool,
        lease,
        MeterCharge {
            period: 1,
            amount: 5,
        },
    )
    .await
    .unwrap();
    assert_eq!(t1, 5);
    assert_eq!(
        t1_again, 5,
        "re-charging the same period returns the recorded total, not a sum"
    );

    // A genuine new period accumulates.
    let t2 = dreggnet_durable::pg::charge_outbox(
        pool,
        lease,
        MeterCharge {
            period: 2,
            amount: 3,
        },
    )
    .await
    .unwrap();
    assert_eq!(t2, 8, "running total = 5 + 3");

    let rows = read_meter_outbox(pool, lease).await.unwrap();
    assert_eq!(
        rows.len(),
        2,
        "two rows total — period 1 was not double-written"
    );
    assert_eq!(rows[0].running_total, 5);
    assert_eq!(rows[1].running_total, 8);
}
