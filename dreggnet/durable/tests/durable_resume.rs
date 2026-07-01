//! Crash-recovery proof for the DreggNet durable layer.
//!
//! A 2-step durable workflow runs on polyana through `dreggnet-exec`:
//!   step1 = polyana `add(40, 2)`  →  "42"   (then metered)
//!   step2 = polyana `42 * 2`      →  "84"   (then metered)
//!
//! We checkpoint after step1 (the workflow parks on an external event), then SIMULATE A
//! CRASH by tearing down the entire duroxide runtime. A fresh runtime is then created
//! over the SAME on-disk store and the workflow is resumed. The proof:
//!   - step1 is NOT re-executed (its activity counter stays 1 across the crash) —
//!     exactly-once: the recorded result is replayed, not recomputed;
//!   - step2 runs once, in the second runtime, and consumes step1's recorded result;
//!   - the meter total is 2, charged once each, never doubled.

use std::sync::Arc;
use std::time::Duration;

use dreggnet_durable::{
    ORCHESTRATION_NAME, ORCHESTRATION_WORKLOAD_RUN, WorkflowInput, WorkflowOutput, WorkloadRun,
    WorkloadSpec, build_registries, metrics, run_workflow_in_memory,
};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

/// A sandboxed WAT step that computes a constant via `op` on two literals, e.g.
/// `wat_step("a", "i32.add", 40, 2)` → `add(40,2) = 42`.
fn wat_step(label: &str, op: &str, x: i32, y: i32) -> WorkloadSpec {
    WorkloadSpec {
        label: label.to_string(),
        lang: "wat".to_string(),
        source: format!(
            "(module (func (export \"run\") (result i32) ({op} (i32.const {x}) (i32.const {y}))))"
        ),
        cap_tier: "sandboxed".to_string(),
    }
}

async fn open_store(db_url: &str) -> Arc<SqliteProvider> {
    Arc::new(
        SqliteProvider::new(db_url, None)
            .await
            .expect("open sqlite durable store"),
    )
}

#[tokio::test]
async fn durable_workflow_resumes_exactly_once_across_a_simulated_crash() {
    // On-disk durable store: it must survive the runtime being dropped and re-created.
    let dir = tempfile::tempdir().expect("tempdir");
    let db_path = dir.path().join("dreggnet-durable.db");
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());

    let instance = "lease-workflow-1";
    let input = serde_json::to_string(&WorkflowInput {
        budget_units: 100,
        cost_per_step: 1,
        // Park after step1 so we can crash deterministically between the two steps.
        pause_event: Some("Resume".to_string()),
    })
    .unwrap();

    // ===== Runtime #1: run up to the checkpoint, then "crash". =====
    {
        let store = open_store(&db_url).await;
        let (activities, orchestrations) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());

        client
            .start_orchestration(instance, ORCHESTRATION_NAME, input.clone())
            .await
            .expect("start");

        // Wait until step1 has actually executed AND the orchestration has parked on the
        // wait (still Running) — i.e. step1 + its meter tick are durably checkpointed.
        let mut parked = false;
        for _ in 0..200 {
            let ran_step1 = metrics::run_calls(instance, "step1") >= 1;
            let status = client.get_orchestration_status(instance).await.unwrap();
            if ran_step1 && matches!(status, OrchestrationStatus::Running { .. }) {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        assert!(parked, "workflow did not reach the post-step1 checkpoint");
        // Let the parked state flush to disk.
        tokio::time::sleep(Duration::from_millis(200)).await;

        // Pre-crash facts: step1 ran exactly once; step2 has NOT run; one meter tick.
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
        assert_eq!(
            metrics::meter_units(instance),
            1,
            "exactly one meter tick so far"
        );

        // 💥 CRASH: tear the whole runtime down. The on-disk store keeps the checkpoint.
        rt.shutdown(None).await;
    }

    // ===== Runtime #2: resume over the SAME on-disk store. =====
    {
        let store = open_store(&db_url).await;
        let (activities, orchestrations) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());

        // Resume: deliver the event the workflow parked on.
        client
            .raise_event(instance, "Resume", "")
            .await
            .expect("raise");

        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(30))
            .await
            .expect("wait");

        let output = match status {
            OrchestrationStatus::Completed { output, .. } => output,
            other => panic!("workflow did not complete: {other:?}"),
        };
        let out: WorkflowOutput = serde_json::from_str(&output).unwrap();

        // The workflow computed the right values, on polyana, across the crash.
        assert_eq!(out.step1, "42", "step1 = add(40,2)");
        assert_eq!(out.step2, "84", "step2 = step1 * 2");
        assert_eq!(out.meter_units, 2, "two metered steps total");

        // EXACTLY-ONCE: step1 was NOT re-executed on resume (still 1, replayed from history).
        assert_eq!(
            metrics::run_calls(instance, "step1"),
            1,
            "step1 must be replayed from the checkpoint, never re-run"
        );
        // step2 ran exactly once, in this second runtime.
        assert_eq!(
            metrics::run_calls(instance, "step2"),
            1,
            "step2 ran once, post-resume"
        );
        // The meter was charged exactly twice — never double-charged by the crash.
        assert_eq!(
            metrics::meter_units(instance),
            2,
            "meter charged exactly twice"
        );

        rt.shutdown(None).await;
    }
}

/// The general path: an ARBITRARY list of `WorkloadSpec` steps runs as a durable workflow.
/// Each step runs on polyana, is checkpointed, and is metered exactly-once. This is the
/// shape an agent-served web request runs through (one handler = one step).
#[tokio::test]
async fn arbitrary_workloadspec_runs_durably_and_meters() {
    // Two unrelated polyana workloads (not the built-in add/double demo).
    let steps = vec![
        wat_step("alpha", "i32.mul", 21, 2), // 42
        wat_step("beta", "i32.add", 50, 50), // 100
    ];
    let input = WorkloadRun::new(/*budget*/ 10, /*cost_per_step*/ 3, steps);

    let out: WorkflowOutput = run_workflow_in_memory(&input, "arb-1")
        .await
        .expect("arbitrary durable workflow completes");

    // Both arbitrary workloads genuinely ran on polyana, in order.
    assert_eq!(out.outputs, vec!["42".to_string(), "100".to_string()]);
    // step1/step2 mirror the first two for back-compat readers.
    assert_eq!(out.step1, "42");
    assert_eq!(out.step2, "100");
    // Metered exactly-once per step: 2 steps × 3 units = 6.
    assert_eq!(out.meter_units, 6);
    assert_eq!(metrics::run_calls("arb-1", "alpha"), 1);
    assert_eq!(metrics::run_calls("arb-1", "beta"), 1);
}

/// The general path is crash-resumable exactly-once: an arbitrary 2-step `WorkloadSpec`
/// workflow checkpoints after step1, "crashes" (runtime torn down), and resumes over the
/// SAME on-disk store — step1 is replayed (never re-run), step2 runs once, no double-charge.
#[tokio::test]
async fn arbitrary_workloadspec_resumes_exactly_once_across_a_crash() {
    let dir = tempfile::tempdir().expect("tempdir");
    let db_path = dir.path().join("dreggnet-arb.db");
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());

    let instance = "arb-crash-1";
    let steps = vec![
        wat_step("alpha", "i32.mul", 21, 2), // 42
        wat_step("beta", "i32.add", 50, 50), // 100
    ];
    let input = serde_json::to_string(&WorkloadRun {
        budget_units: 100,
        cost_per_step: 1,
        steps,
        // Park after step1 so we can crash deterministically between the two steps.
        pause_after_step: Some(1),
        pause_event: Some("Resume".to_string()),
    })
    .unwrap();

    // ===== Runtime #1: run to the post-step1 checkpoint, then "crash". =====
    {
        let store = open_store(&db_url).await;
        let (activities, orchestrations) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());
        client
            .start_orchestration(instance, ORCHESTRATION_WORKLOAD_RUN, input.clone())
            .await
            .expect("start");

        let mut parked = false;
        for _ in 0..200 {
            let ran = metrics::run_calls(instance, "alpha") >= 1;
            let status = client.get_orchestration_status(instance).await.unwrap();
            if ran && matches!(status, OrchestrationStatus::Running { .. }) {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        assert!(parked, "workflow did not reach the post-step1 checkpoint");
        tokio::time::sleep(Duration::from_millis(200)).await;

        assert_eq!(
            metrics::run_calls(instance, "alpha"),
            1,
            "step1 ran once before crash"
        );
        assert_eq!(
            metrics::run_calls(instance, "beta"),
            0,
            "step2 must not have run yet"
        );
        assert_eq!(
            metrics::meter_units(instance),
            1,
            "exactly one meter tick so far"
        );

        rt.shutdown(None).await; // 💥 crash
    }

    // ===== Runtime #2: resume over the SAME on-disk store. =====
    {
        let store = open_store(&db_url).await;
        let (activities, orchestrations) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());
        client
            .raise_event(instance, "Resume", "")
            .await
            .expect("raise");

        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(30))
            .await
            .expect("wait");
        let output = match status {
            OrchestrationStatus::Completed { output, .. } => output,
            other => panic!("workflow did not complete: {other:?}"),
        };
        let out: WorkflowOutput = serde_json::from_str(&output).unwrap();

        assert_eq!(out.outputs, vec!["42".to_string(), "100".to_string()]);
        assert_eq!(out.meter_units, 2, "two metered steps total");
        // EXACTLY-ONCE: step1 replayed from the checkpoint, never re-run.
        assert_eq!(
            metrics::run_calls(instance, "alpha"),
            1,
            "step1 never re-run"
        );
        assert_eq!(
            metrics::run_calls(instance, "beta"),
            1,
            "step2 ran once, post-resume"
        );
        assert_eq!(
            metrics::meter_units(instance),
            2,
            "meter charged exactly twice"
        );

        rt.shutdown(None).await;
    }
}

/// A lease whose budget cannot cover both steps lapses: the workflow fails rather than
/// running (and paying for) work the lease never authorized.
#[tokio::test]
async fn lease_budget_exhaustion_fails_the_workflow() {
    let store = Arc::new(SqliteProvider::new_in_memory().await.expect("mem store"));
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let instance = "lease-too-small";
    // Budget 1, cost 1/step: step1's tick (total 1) is fine; step2's tick (total 2) lapses.
    let input = serde_json::to_string(&WorkflowInput {
        budget_units: 1,
        cost_per_step: 1,
        pause_event: None,
    })
    .unwrap();

    client
        .start_orchestration(instance, ORCHESTRATION_NAME, input)
        .await
        .expect("start");

    let status = client
        .wait_for_orchestration(instance, Duration::from_secs(30))
        .await
        .expect("wait");

    match status {
        OrchestrationStatus::Failed { details, .. } => {
            assert!(
                details
                    .display_message()
                    .contains("execution-lease exhausted"),
                "unexpected failure: {}",
                details.display_message()
            );
        }
        other => panic!("expected lease-exhaustion failure, got: {other:?}"),
    }

    rt.shutdown(None).await;
}
