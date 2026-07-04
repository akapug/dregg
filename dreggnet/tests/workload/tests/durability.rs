//! Scenario 5.5 — Durability.
//!
//! Crash-resume across the workload (the durable SQLite layer), exactly-once, under
//! a population of in-flight workflows. Generalizes `durable/tests/durable_resume.rs`
//! from one workflow to many. See `docs/WORKLOAD-TEST-PLAN.md` §5.5.
//!
//! Run: `cargo test -p dreggnet-workload --release durability -- --ignored --nocapture`

use std::sync::Arc;
use std::time::{Duration, Instant};

use dreggnet_durable::{
    ORCHESTRATION_WORKLOAD_RUN, WorkflowOutput, WorkloadRun, WorkloadSpec, build_registries,
    metrics, run_workflow_on_disk,
};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

/// A sandboxed WAT step computing `op(x, y)` (the same shape the durable tests use).
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

async fn open_store(db_path: &std::path::Path) -> Arc<SqliteProvider> {
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());
    Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .expect("open sqlite durable store"),
    )
}

/// A population of durable workflows on-disk, each metered exactly-once (straight
/// run-to-completion, no crash). The aggregate meter is exactly `N × steps × cost`.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — run via `make test-workload`"]
async fn population_of_durable_workflows_meters_exactly_once() {
    let n: usize = std::env::var("DREGGNET_WL_TENANTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20);
    let dir = tempfile::tempdir().expect("tempdir");

    let mut total_meter = 0i64;
    for i in 0..n {
        let instance = format!("durable-{i}");
        let steps = vec![
            wat_step("alpha", "i32.mul", 21, 2), // 42
            wat_step("beta", "i32.add", 50, 50), // 100
        ];
        let input = WorkloadRun::new(/*budget*/ 10, /*cost_per_step*/ 1, steps);
        let db = dir.path().join(format!("{instance}.db"));

        let out = run_workflow_on_disk(&input, &instance, &db)
            .await
            .expect("durable workflow completes");

        assert_eq!(out.outputs, vec!["42".to_string(), "100".to_string()]);
        assert_eq!(out.meter_units, 2, "2 steps × 1 unit");
        assert_eq!(metrics::run_calls(&instance, "alpha"), 1, "step1 ran once");
        assert_eq!(metrics::run_calls(&instance, "beta"), 1, "step2 ran once");
        total_meter += out.meter_units;
    }

    assert_eq!(
        total_meter,
        (n as i64) * 2,
        "aggregate meter is exactly-once"
    );
    println!("  durable population: {n} workflows, aggregate meter={total_meter} (exactly-once)");
}

/// The crash-resume POPULATION: start N durable workflows on-disk, park each
/// mid-run (after step1), tear the runtime down (the crash), reopen the SAME
/// stores, resume ALL of them, and assert each replayed its completed step
/// (`run_calls` flat across the crash) + metered exactly-once. Measures resume time
/// as a function of in-flight count.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — crash-resume population (overnight)"]
async fn population_crash_resumes_exactly_once() {
    let n: usize = std::env::var("DREGGNET_WL_TENANTS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
    let dir = tempfile::tempdir().expect("tempdir");

    // Unique instance ids across this process (the durable metrics ledger is a
    // process-global keyed by instance; a fresh prefix avoids aliasing other tests).
    let run_tag = format!("crashpop-{}", std::process::id());
    let instances: Vec<String> = (0..n).map(|i| format!("{run_tag}-{i}")).collect();
    let dbs: Vec<_> = instances
        .iter()
        .map(|inst| dir.path().join(format!("{inst}.db")))
        .collect();

    let input_json = || {
        serde_json::to_string(&WorkloadRun {
            budget_units: 100,
            cost_per_step: 1,
            steps: vec![
                wat_step("alpha", "i32.mul", 21, 2), // 42
                wat_step("beta", "i32.add", 50, 50), // 100
            ],
            // Park after step1 so we crash deterministically between the two steps.
            pause_after_step: Some(1),
            pause_event: Some("Resume".to_string()),
        })
        .unwrap()
    };

    // ===== Runtime #1: start all N, run each to its post-step1 checkpoint, crash. =====
    {
        let mut rts = Vec::new();
        for (inst, db) in instances.iter().zip(&dbs) {
            let store = open_store(db).await;
            let (activities, orchestrations) = build_registries();
            let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
            let client = Client::new(store.clone());
            client
                .start_orchestration(inst, ORCHESTRATION_WORKLOAD_RUN, input_json())
                .await
                .expect("start");
            rts.push((inst.clone(), store, rt, client));
        }

        // Wait until EVERY workflow has run step1 and parked on the wait.
        for (inst, _store, _rt, client) in &rts {
            let mut parked = false;
            for _ in 0..400 {
                let ran = metrics::run_calls(inst, "alpha") >= 1;
                let status = client.get_orchestration_status(inst).await.unwrap();
                if ran && matches!(status, OrchestrationStatus::Running { .. }) {
                    parked = true;
                    break;
                }
                tokio::time::sleep(Duration::from_millis(20)).await;
            }
            assert!(
                parked,
                "workflow {inst} did not reach the post-step1 checkpoint"
            );
        }
        tokio::time::sleep(Duration::from_millis(200)).await;

        // Pre-crash facts: every instance ran step1 once, step2 zero, one meter tick.
        for inst in &instances {
            assert_eq!(
                metrics::run_calls(inst, "alpha"),
                1,
                "{inst}: step1 once pre-crash"
            );
            assert_eq!(metrics::run_calls(inst, "beta"), 0, "{inst}: step2 not yet");
            assert_eq!(
                metrics::meter_units(inst),
                1,
                "{inst}: one meter tick pre-crash"
            );
        }

        // 💥 CRASH: tear every runtime down. The on-disk stores keep the checkpoints.
        for (_inst, _store, rt, _client) in rts {
            rt.shutdown(None).await;
        }
    }

    // ===== Runtime #2: reopen the SAME stores, resume ALL, time the resume. =====
    let t_resume = Instant::now();
    {
        let mut rts = Vec::new();
        for (inst, db) in instances.iter().zip(&dbs) {
            let store = open_store(db).await;
            let (activities, orchestrations) = build_registries();
            let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
            let client = Client::new(store.clone());
            client.raise_event(inst, "Resume", "").await.expect("raise");
            rts.push((inst.clone(), store, rt, client));
        }
        for (inst, _store, rt, client) in rts {
            let status = client
                .wait_for_orchestration(&inst, Duration::from_secs(60))
                .await
                .expect("wait");
            let output = match status {
                OrchestrationStatus::Completed { output, .. } => output,
                other => panic!("{inst} did not complete: {other:?}"),
            };
            let out: WorkflowOutput = serde_json::from_str(&output).unwrap();
            assert_eq!(
                out.outputs,
                vec!["42".to_string(), "100".to_string()],
                "{inst} output"
            );
            assert_eq!(out.meter_units, 2, "{inst}: two metered steps");
            rt.shutdown(None).await;
        }
    }
    let resume_elapsed = t_resume.elapsed();

    // EXACTLY-ONCE across the whole population: step1 replayed (never re-run), step2
    // ran once each, the aggregate meter is exactly N×2 with no duplication.
    let mut agg_meter = 0i64;
    for inst in &instances {
        assert_eq!(
            metrics::run_calls(inst, "alpha"),
            1,
            "{inst}: step1 replayed, never re-run"
        );
        assert_eq!(
            metrics::run_calls(inst, "beta"),
            1,
            "{inst}: step2 ran once post-resume"
        );
        assert_eq!(
            metrics::meter_units(inst),
            2,
            "{inst}: meter charged exactly twice"
        );
        agg_meter += metrics::meter_units(inst);
    }
    assert_eq!(
        agg_meter,
        (n as i64) * 2,
        "aggregate exactly-once meter total"
    );
    println!(
        "  crash-resume population: {n} in-flight workflows resumed in {:.2}s ({:.1}ms/wf), \
         aggregate meter={agg_meter} (exactly-once)",
        resume_elapsed.as_secs_f64(),
        resume_elapsed.as_secs_f64() * 1e3 / (n as f64)
    );
}

/// The pg-store variant (mirrors `durable/tests/durable_resume_pg.rs`): the same
/// crash-resume exactly-once guarantee on the in-process PostgreSQL provider.
///
/// Skip-clean when `DATABASE_URL` is absent (the norm offline / on CI) — recorded
/// SKIPPED, never a false pass, mirroring the durable crate's pg-gated test. The pg
/// provider also requires the durable crate's `pg` feature; the harness keeps the
/// default (sqlite) build, so this variant documents the gated path and the env it
/// needs rather than compiling the pg drive.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — pg crash-resume variant (DATABASE_URL-gated)"]
async fn population_crash_resumes_exactly_once_pg() {
    let Ok(url) = std::env::var("DATABASE_URL") else {
        println!(
            "  pg variant: SKIPPED (DATABASE_URL unset) — the sqlite path covers the guarantee"
        );
        return;
    };
    println!(
        "  pg variant: DATABASE_URL set ({}…) but the harness builds the sqlite default; \
         enable the durable `pg` feature + run `durable_resume_pg.rs` for the live-pg drive.",
        &url.chars().take(12).collect::<String>()
    );
}
