//! The webapp data plane over the durability guarantee: a served web-app request
//! runs as a real durable, crash-resumable, exactly-once-metered `dreggnet_durable`
//! workflow.
//!
//! Two proofs:
//!   1. A request served through [`LeasedRouter`] runs THROUGH the durable layer:
//!      the handler executes on the owned sandbox, is metered, and the response is rendered
//!      from the durable workflow's output — and an over-budget request is refused.
//!   2. A request's durable workflow resumes EXACTLY-ONCE across a simulated crash:
//!      the handler step is checkpointed, the runtime is torn down, a fresh runtime
//!      resumes over the SAME on-disk store, and the handler is replayed (never
//!      re-run) with no double-charge.

use std::sync::Arc;
use std::time::Duration;

use dreggnet_bridge::{CapGrade, Lease};
use dreggnet_durable::{
    ORCHESTRATION_WORKLOAD_RUN, WorkflowOutput, WorkloadRun, build_registries, metrics,
};
use dreggnet_webapp::{LeasedRouter, WebRequest, assemble, handler_workload_spec};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

/// A served request runs as a durable workflow: the handler executes on the owned sandbox,
/// is metered against the lease, and the response is rendered from the workflow's
/// output. The budget gate still refuses an over-budget request.
#[test]
fn webapp_request_runs_as_a_durable_metered_workflow() {
    // Budget for exactly 2 requests at 1 unit each.
    let lease = Lease::funded("agent-x", CapGrade::Sandboxed, "USD", 2, 1);
    let router = LeasedRouter::new(assemble::demo_app("agent-x"), lease).unwrap();

    // GET /add?a=40&b=2 → the handler runs on the owned sandbox inside a durable workflow.
    let (r1, m1) = router.serve(&WebRequest::get("/add?a=40&b=2"));
    assert_eq!(r1.status, 200, "served durably: {}", r1.body_str());
    assert_eq!(
        r1.body_str(),
        "{\"result\":42}",
        "the owned sandbox computed the sum durably"
    );
    assert_eq!(m1.charged, 1, "the request was metered against the lease");

    let (r2, _m2) = router.serve(&WebRequest::get("/hello"));
    assert_eq!(r2.status, 200);
    assert!(
        r2.body_str().contains("computed 42"),
        "body: {}",
        r2.body_str()
    );

    // The third request would exceed the budget → 402, the handler never runs.
    let (r3, m3) = router.serve(&WebRequest::get("/add?a=1&b=1"));
    assert_eq!(r3.status, 402, "exhausted: {}", r3.body_str());
    assert_eq!(m3.charged, 2, "no charge on a refused request");
}

async fn open_store(db_url: &str) -> Arc<SqliteProvider> {
    Arc::new(
        SqliteProvider::new(db_url, None)
            .await
            .expect("open sqlite durable store"),
    )
}

/// A served request's durable workflow resumes exactly-once across a crash.
///
/// We drive the SAME one-step workflow `LeasedRouter` builds for a request (the
/// handler wrapped as a [`handler_workload_spec`]), but with a deterministic pause
/// point so we can crash AFTER the handler step is durably checkpointed + metered.
/// A fresh runtime resumes over the same on-disk store; the handler is replayed,
/// never re-run, and the meter is never double-charged.
#[tokio::test]
async fn webapp_request_resumes_exactly_once_across_a_crash() {
    let dir = tempfile::tempdir().expect("tempdir");
    let db_path = dir.path().join("dreggnet-webapp-req.db");
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());

    let instance = "webapp-req-crash-1";
    // The exact spec a request to `/hello` runs as one durable step.
    let req = WebRequest::get("/hello");
    let handler = assemble::hello_handler();
    let spec = handler_workload_spec(&handler, &req.query).expect("build handler spec");

    let input = serde_json::to_string(&WorkloadRun {
        budget_units: 5,
        cost_per_step: 1,
        steps: vec![spec],
        // Park after the handler step is checkpointed + metered, so we can crash there.
        pause_after_step: Some(1),
        pause_event: Some("Resume".to_string()),
    })
    .unwrap();

    // ===== Runtime #1: run the handler step to its checkpoint, then "crash". =====
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
            let ran = metrics::run_calls(instance, "handler") >= 1;
            let status = client.get_orchestration_status(instance).await.unwrap();
            if ran && matches!(status, OrchestrationStatus::Running { .. }) {
                parked = true;
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        assert!(
            parked,
            "request workflow did not reach the post-handler checkpoint"
        );
        tokio::time::sleep(Duration::from_millis(200)).await;

        assert_eq!(
            metrics::run_calls(instance, "handler"),
            1,
            "handler ran once before crash"
        );
        assert_eq!(
            metrics::meter_units(instance),
            1,
            "metered exactly once so far"
        );

        rt.shutdown(None).await; // 💥 crash mid-request
    }

    // ===== Runtime #2: resume the in-flight request over the SAME on-disk store. =====
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
            other => panic!("request workflow did not complete: {other:?}"),
        };
        let out: WorkflowOutput = serde_json::from_str(&output).unwrap();

        // The handler computed `21 * 2 = 42` on the owned sandbox, recovered across the crash.
        assert_eq!(out.outputs, vec!["42".to_string()]);
        // EXACTLY-ONCE: the handler was replayed from the checkpoint, never re-run,
        // and the meter was charged exactly once — the crash double-charged nothing.
        assert_eq!(
            metrics::run_calls(instance, "handler"),
            1,
            "handler never re-run on resume"
        );
        assert_eq!(out.meter_units, 1, "the request was metered exactly once");
        assert_eq!(
            metrics::meter_units(instance),
            1,
            "no double-charge across the crash"
        );

        rt.shutdown(None).await;
    }
}
