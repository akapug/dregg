//! The keystone proof: a funded dregg execution-lease drives a durable metered
//! workflow end to end, metered against the lease budget, exactly-once across a
//! crash.
//!
//! This composes rung 2 (real owned-wasmi execution) + the durable layer (exactly-once
//! crash-resume) + the lease gate (this rung) into one weld:
//!
//!   1. A FUNDED lease (budget 100, 1 unit/step) drives a 2-step metered workflow:
//!        step1 = `add(40,2)` → "42"  (then metered: 1 unit)
//!        step2 = `42 * 2`    → "84"  (then metered: 2 units total)
//!      end to end, within budget.
//!   2. An OVER-BUDGET lease (budget 1, 1 unit/step) FAILS: step1's tick fits
//!      (total 1), step2's tick lapses (total 2 > 1) → the workflow fails and
//!      yields NO claimable result, so DreggNet never bills/delivers beyond what
//!      the lease budget proves was paid for. An UNFUNDED lease never starts at all.
//!   3. A funded lease whose workflow CRASHES mid-flight resumes exactly-once
//!      WITHIN the same budget: step1 is replayed (not re-run), step2 runs once,
//!      the meter is charged exactly twice — the crash never double-charges.

use std::sync::Arc;
use std::time::Duration;

use dreggnet_bridge::{
    BridgeError, CapGrade, Lease, WorkloadSource, fulfill, fulfill_workload,
    workflow_input_for_lease,
};
use dreggnet_durable::{ORCHESTRATION_NAME, WorkflowOutput, build_registries, metrics};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

/// 1. A funded lease drives the durable 2-step metered workflow end to end, the
///    meter ticks once per step, total within budget.
#[tokio::test]
async fn funded_lease_drives_durable_two_step_workflow_within_budget() {
    let lease = Lease::funded("agent-fulfill", CapGrade::Sandboxed, "USD-test", 100, 1);
    assert!(lease.is_active());

    // The lease's cap-grade picks the tier the workload runs at.
    let binding = lease.tier_binding();
    assert_eq!(binding.provider, "dreggnet-wasmi");

    let out: WorkflowOutput = fulfill(&lease, "bridge-e2e-1")
        .await
        .expect("funded lease should fulfill end to end");

    // The values were computed ON THE OWNED SANDBOX, across the durable workflow.
    assert_eq!(out.step1, "42", "step1 = add(40,2)");
    assert_eq!(out.step2, "84", "step2 = 42*2");
    // The meter charged exactly twice against the lease budget (1 unit/step).
    assert_eq!(out.meter_units, 2, "two metered steps, within budget 100");

    // Each step ran exactly once.
    assert_eq!(metrics::run_calls("bridge-e2e-1", "step1"), 1);
    assert_eq!(metrics::run_calls("bridge-e2e-1", "step2"), 1);
}

/// 1b. A funded lease runs a CALLER-DECLARED workload (the `run --source` path):
///     the program the caller actually wrote runs on the owned sandbox, not the fixed demo.
#[tokio::test]
async fn funded_lease_runs_a_caller_declared_workload() {
    let lease = Lease::funded("agent-source", CapGrade::Sandboxed, "USD-test", 100, 1);

    // A WAT program the caller wrote (NOT the add→double demo): return 7.
    let workload = WorkloadSource {
        lang: "wat".to_string(),
        source: "(module (func (export \"run\") (result i32) (i32.const 7)))".to_string(),
    };

    let out = fulfill_workload(&lease, "bridge-source-1", &workload)
        .await
        .expect("a funded lease should run the declared workload");

    // The result is the caller's program's output (7), run as one durable step,
    // metered exactly once — NOT the demo's 42/84.
    assert_eq!(
        out.outputs,
        vec!["7".to_string()],
        "the declared program ran"
    );
    assert_eq!(out.step1, "7");
    assert_eq!(out.meter_units, 1, "one metered step at cost 1");
}

/// 1c. An over-budget lease running a declared workload lapses before the step is
///     claimed (no work delivered beyond what the budget paid for).
#[tokio::test]
async fn over_budget_declared_workload_lapses() {
    // Budget 0, 1 unit/step: the first (only) step's charge would reach 1 > 0 → lapse.
    let lease = Lease::funded("agent-source-broke", CapGrade::Sandboxed, "USD-test", 0, 1);
    let workload = WorkloadSource {
        lang: "wat".to_string(),
        source: "(module (func (export \"run\") (result i32) (i32.const 9)))".to_string(),
    };
    let err = fulfill_workload(&lease, "bridge-source-broke-1", &workload)
        .await
        .expect_err("an over-budget declared workload must lapse");
    assert!(matches!(err, BridgeError::WorkflowFailed(msg) if msg.contains("exhausted")));
}

/// 2a. An over-budget lease fails the workflow: it yields no claimable result, so
///     DreggNet never delivers/bills beyond what the lease budget proves was paid.
#[tokio::test]
async fn over_budget_lease_fails_with_no_claimable_result() {
    // Budget 1, 1 unit/step: step1's tick (total 1) fits; the step that would push
    // the meter to total 2 lapses the lease (2 > 1) → the workflow FAILS. The
    // durable orchestration meters-then-gates, so the failure surfaces as the
    // exhaustion error and NO WorkflowOutput is ever returned — nothing is claimed.
    let lease = Lease::funded("agent-broke", CapGrade::Sandboxed, "USD-test", 1, 1);

    let err = fulfill(&lease, "bridge-overbudget-1")
        .await
        .expect_err("an over-budget lease must fail the workflow");

    match err {
        BridgeError::WorkflowFailed(msg) => {
            assert!(
                msg.contains("execution-lease exhausted"),
                "unexpected failure: {msg}"
            );
        }
        other => panic!("expected WorkflowFailed, got {other:?}"),
    }

    // step1 ran and was metered within budget; the meter never settles below the
    // overspend into a delivered result — `fulfill` returned an error, not output.
    assert_eq!(metrics::run_calls("bridge-overbudget-1", "step1"), 1);
}

/// 2b. An unfunded lease never starts a workflow at all (truly no unpaid work).
#[tokio::test]
async fn unfunded_lease_never_starts_the_workflow() {
    let lease = Lease {
        lessee: "agent-unfunded".into(),
        cap_grade: CapGrade::Sandboxed,
        asset: "USD-test".into(),
        budget_units: 100,
        per_period_units: 1,
        funded: false,
    };

    let err = fulfill(&lease, "bridge-unfunded-1")
        .await
        .expect_err("an unfunded lease authorizes no work");
    assert!(matches!(err, BridgeError::Unfunded { .. }));

    // Nothing ran.
    assert_eq!(metrics::run_calls("bridge-unfunded-1", "step1"), 0);
    assert_eq!(metrics::meter_units("bridge-unfunded-1"), 0);
}

/// 3. A funded lease's workflow resumes exactly-once WITHIN the same budget across
///    a simulated crash — composing the durable-resume proof with the lease gate.
///
/// The [`WorkflowInput`] is derived from the lease via the SAME
/// [`workflow_input_for_lease`] gate `fulfill` uses, so the budget that bounds the
/// resume is the lease's budget, not a hand-rolled constant.
#[tokio::test]
async fn funded_lease_workflow_resumes_exactly_once_within_budget_across_a_crash() {
    let dir = tempfile::tempdir().expect("tempdir");
    let db_path = dir.path().join("bridge-durable.db");
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());

    let instance = "bridge-crash-1";
    let lease = Lease::funded("agent-durable", CapGrade::Caged, "USD-test", 100, 1);

    // The lease gate derives the budgeted workflow input; the crash park point is
    // the deterministic checkpoint between the two steps.
    let input = serde_json::to_string(
        &workflow_input_for_lease(&lease, Some("Resume".to_string())).expect("active lease"),
    )
    .unwrap();

    // ===== Runtime #1: run to the post-step1 checkpoint, then "crash". =====
    {
        let store = Arc::new(
            SqliteProvider::new(&db_url, None)
                .await
                .expect("open durable store"),
        );
        let (activities, orchestrations) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
        let client = Client::new(store.clone());

        client
            .start_orchestration(instance, ORCHESTRATION_NAME, input.clone())
            .await
            .expect("start");

        // Wait until step1 has run AND the workflow has parked (still Running) —
        // step1 + its meter tick are durably checkpointed.
        let mut parked = false;
        for _ in 0..200 {
            let ran = metrics::run_calls(instance, "step1") >= 1;
            let status = client.get_orchestration_status(instance).await.unwrap();
            if ran && matches!(status, OrchestrationStatus::Running { .. }) {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        assert!(parked, "workflow did not reach the post-step1 checkpoint");
        tokio::time::sleep(Duration::from_millis(200)).await;

        assert_eq!(metrics::run_calls(instance, "step1"), 1, "step1 ran once");
        assert_eq!(metrics::run_calls(instance, "step2"), 0, "step2 not yet");
        assert_eq!(metrics::meter_units(instance), 1, "one meter tick so far");

        // 💥 CRASH.
        rt.shutdown(None).await;
    }

    // ===== Runtime #2: resume over the SAME on-disk store. =====
    {
        let store = Arc::new(
            SqliteProvider::new(&db_url, None)
                .await
                .expect("reopen durable store"),
        );
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

        // Right values, on the owned sandbox, across the crash, within the lease budget.
        assert_eq!(out.step1, "42");
        assert_eq!(out.step2, "84");
        assert_eq!(out.meter_units, 2, "two metered steps, within budget 100");

        // EXACTLY-ONCE: step1 was replayed, never re-run; step2 ran once; the
        // meter was charged exactly twice — the crash never double-charged the lease.
        assert_eq!(
            metrics::run_calls(instance, "step1"),
            1,
            "step1 replayed from checkpoint, not re-run"
        );
        assert_eq!(
            metrics::run_calls(instance, "step2"),
            1,
            "step2 ran once post-resume"
        );
        assert_eq!(
            metrics::meter_units(instance),
            2,
            "meter charged exactly twice"
        );

        rt.shutdown(None).await;
    }
}
