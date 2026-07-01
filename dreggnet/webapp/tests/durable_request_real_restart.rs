//! Crash-resume of a served web-app request across a **real process restart**.
//!
//! This is the stronger twin of `durable_request_resume.rs`. That test tears down the
//! duroxide *runtime* but stays inside one process, so the in-process observability ledger
//! survives the "crash". Here the crash is a genuine `SIGABRT` of a real child process: the
//! durable store must carry the whole guarantee on disk, because nothing in memory survives.
//!
//! The driver test forks the test binary twice (the libtest `--exact --ignored` re-invocation
//! trick), handing both children the same on-disk store path + instance id via env:
//!
//!   1. **Phase crash** — a child runs a request's durable workflow (the SAME
//!      `ORCHESTRATION_WORKLOAD_RUN` + [`handler_workload_spec`] the webapp serves) over an
//!      on-disk SQLite store until the handler step is durably checkpointed + metered and the
//!      workflow parks, then calls `std::process::abort()` — a hard, ungraceful kill (no
//!      destructors, no graceful shutdown).
//!   2. **Phase resume** — a *fresh* child process attaches a runtime to the SAME on-disk
//!      store, resumes the in-flight request, and runs it to completion.
//!
//! The proof, observed entirely in the fresh process (its in-process ledger starts empty):
//!   - the handler activity executes **zero** times on resume — the recorded result is
//!     replayed from the on-disk checkpoint, never re-run (exactly-once);
//!   - the meter activity executes **zero** times on resume, yet the completed workflow's
//!     `meter_units` is the correct `1` (reconstructed from the durable history) — the crash
//!     double-charged nothing;
//!   - the request completes with the right answer (`21 * 2 = 42`).

use std::sync::Arc;
use std::time::Duration;

use dreggnet_durable::{
    ORCHESTRATION_WORKLOAD_RUN, WorkflowOutput, WorkloadRun, build_registries, metrics,
};
use dreggnet_webapp::{WebRequest, assemble, handler_workload_spec};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

const ENV_DB: &str = "DREGGNET_TEST_DB";
const ENV_INSTANCE: &str = "DREGGNET_TEST_INSTANCE";
const RESUME_EVENT: &str = "Resume";

async fn open_store(db_path: &str) -> Arc<SqliteProvider> {
    let db_url = format!("sqlite:{db_path}?mode=rwc");
    Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .expect("open on-disk sqlite durable store"),
    )
}

/// The exact one-step workflow a `/hello` request runs through `LeasedRouter`, but with a
/// deterministic pause point so the child can crash AFTER the handler step is checkpointed.
fn request_workflow_json() -> (String, String) {
    let req = WebRequest::get("/hello");
    let handler = assemble::hello_handler();
    let spec = handler_workload_spec(&handler, &req.query).expect("build handler spec");
    let run = WorkloadRun {
        budget_units: 5,
        cost_per_step: 1,
        steps: vec![spec],
        // Park after the (only) handler step is durably checkpointed + metered.
        pause_after_step: Some(1),
        pause_event: Some(RESUME_EVENT.to_string()),
    };
    let label = run.steps[0].label.clone();
    (serde_json::to_string(&run).unwrap(), label)
}

// =========================================================================================
// The driver: fork the test binary into two real processes around a genuine crash.
// =========================================================================================

/// A served request's durable workflow survives a **real process restart** exactly-once.
#[test]
fn webapp_request_survives_a_real_process_restart() {
    let dir = tempfile::tempdir().expect("tempdir");
    // A persistent on-disk store path shared by both child processes (lives in the driver's
    // tempdir, which only this driver process owns + cleans up at the end).
    let db_path = dir.path().join("webapp-real-restart.db");
    let db = db_path.to_str().expect("utf-8 path").to_string();
    let instance = "webapp-real-restart-req-1";
    let exe = std::env::current_exe().expect("current test binary");

    // --- Phase 1: a child runs the request to its checkpoint, then ABORTS (real crash). ---
    let crash = std::process::Command::new(&exe)
        .args([
            "child_runs_request_to_checkpoint_then_aborts",
            "--exact",
            "--ignored",
            "--nocapture",
        ])
        .env(ENV_DB, &db)
        .env(ENV_INSTANCE, instance)
        .output()
        .expect("spawn the crash-phase child process");
    // A genuine ungraceful crash: the child did NOT exit cleanly.
    assert!(
        !crash.status.success(),
        "phase-1 child must crash (abort), not exit cleanly; status={:?}\nstdout:\n{}\nstderr:\n{}",
        crash.status,
        String::from_utf8_lossy(&crash.stdout),
        String::from_utf8_lossy(&crash.stderr),
    );
    assert!(
        String::from_utf8_lossy(&crash.stdout).contains("CHECKPOINTED_THEN_ABORTING"),
        "phase-1 child must reach the post-handler checkpoint before crashing;\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&crash.stdout),
        String::from_utf8_lossy(&crash.stderr),
    );

    // The on-disk store survived the crash: the in-flight instance is recoverable on disk.
    assert!(
        db_path.exists(),
        "the on-disk durable store must survive the crash"
    );

    // --- Phase 2: a FRESH process resumes from the on-disk store, exactly-once. ---
    let resume = std::process::Command::new(&exe)
        .args([
            "child_resumes_request_from_disk_exactly_once",
            "--exact",
            "--ignored",
            "--nocapture",
        ])
        .env(ENV_DB, &db)
        .env(ENV_INSTANCE, instance)
        .output()
        .expect("spawn the resume-phase child process");
    assert!(
        resume.status.success(),
        "phase-2 child must resume + complete exactly-once; status={:?}\nstdout:\n{}\nstderr:\n{}",
        resume.status,
        String::from_utf8_lossy(&resume.stdout),
        String::from_utf8_lossy(&resume.stderr),
    );
    assert!(
        String::from_utf8_lossy(&resume.stdout).contains("RESUME_OK exactly-once meter=1"),
        "phase-2 child must report exactly-once completion;\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&resume.stdout),
        String::from_utf8_lossy(&resume.stderr),
    );
}

// =========================================================================================
// The child phases. `#[ignore]`d so a normal `cargo test` skips them; the driver invokes each
// explicitly in its own process via `--exact --ignored`. When the env handshake is absent
// (a human running `cargo test -- --ignored`), they no-op so the suite stays green.
// =========================================================================================

/// Phase 1 (child process): run the request to its post-handler checkpoint, then hard-crash.
#[tokio::test]
#[ignore = "child process of webapp_request_survives_a_real_process_restart"]
async fn child_runs_request_to_checkpoint_then_aborts() {
    let (Ok(db), Ok(instance)) = (std::env::var(ENV_DB), std::env::var(ENV_INSTANCE)) else {
        return; // not invoked by the driver — no-op.
    };
    let (input, label) = request_workflow_json();

    let store = open_store(&db).await;
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());
    client
        .start_orchestration(&instance, ORCHESTRATION_WORKLOAD_RUN, input)
        .await
        .expect("start request workflow");

    // Wait until the handler step has executed AND the workflow has parked on the wait
    // (still Running) — i.e. the handler result + its meter charge are durably checkpointed.
    let mut parked = false;
    for _ in 0..400 {
        let ran = metrics::run_calls(&instance, &label) >= 1;
        let status = client.get_orchestration_status(&instance).await.unwrap();
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
    // Let the checkpoint flush to the on-disk WAL before the hard kill.
    tokio::time::sleep(Duration::from_millis(300)).await;
    assert_eq!(
        metrics::run_calls(&instance, &label),
        1,
        "handler ran once pre-crash"
    );
    assert_eq!(
        metrics::meter_units(&instance),
        1,
        "metered exactly once pre-crash"
    );

    // Marker for the driver, flushed to stdout, THEN the hard, ungraceful crash. No runtime
    // shutdown, no destructors — the on-disk store alone must carry the guarantee.
    println!("CHECKPOINTED_THEN_ABORTING");
    use std::io::Write;
    std::io::stdout().flush().ok();
    std::process::abort();
}

/// Phase 2 (fresh child process): resume the in-flight request from the on-disk store and
/// prove exactly-once — the handler is replayed (run 0 times here), the meter is not
/// double-charged, and the request completes correctly.
#[tokio::test]
#[ignore = "child process of webapp_request_survives_a_real_process_restart"]
async fn child_resumes_request_from_disk_exactly_once() {
    let (Ok(db), Ok(instance)) = (std::env::var(ENV_DB), std::env::var(ENV_INSTANCE)) else {
        return; // not invoked by the driver — no-op.
    };
    let (_, label) = request_workflow_json();

    let store = open_store(&db).await;
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    // Resume the request the crashed process left parked: deliver the event it waits on.
    client
        .raise_event(&instance, RESUME_EVENT, "")
        .await
        .expect("raise resume");

    let status = client
        .wait_for_orchestration(&instance, Duration::from_secs(30))
        .await
        .expect("await resumed request");
    let output = match status {
        OrchestrationStatus::Completed { output, .. } => output,
        other => panic!("resumed request did not complete: {other:?}"),
    };
    let out: WorkflowOutput = serde_json::from_str(&output).unwrap();

    // The request computed `21 * 2 = 42` on polyana, recovered across a real process restart.
    assert_eq!(
        out.outputs,
        vec!["42".to_string()],
        "request result recovered from disk"
    );
    // Meter not double-charged: the completed workflow's total is the correct 1, reconstructed
    // entirely from the on-disk durable history (this fresh process charged nothing itself).
    assert_eq!(
        out.meter_units, 1,
        "request metered exactly once across the restart"
    );

    // EXACTLY-ONCE, observed in THIS fresh process (its ledger started empty):
    //  - the handler activity ran 0 times here — its result was replayed from the checkpoint;
    //  - the meter activity charged 0 here — its charge was replayed, not re-applied.
    // A re-execution or a re-charge would be plainly visible as a non-zero count.
    assert_eq!(
        metrics::run_calls(&instance, &label),
        0,
        "handler must be REPLAYED from disk on resume, never re-executed in the fresh process"
    );
    assert_eq!(
        metrics::meter_units(&instance),
        0,
        "the meter charge must be REPLAYED, never re-applied in the fresh process"
    );

    rt.shutdown(None).await;
    println!("RESUME_OK exactly-once meter={}", out.meter_units);
}
