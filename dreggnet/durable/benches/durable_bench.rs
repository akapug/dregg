//! Durable-layer characterization: the cost of running an owned-sandbox workload as a
//! crash-resumable `duroxide` workflow, the per-step overhead, and the on-disk
//! (SQLite) checkpoint + crash-resume cost.
//!
//! Hand-rolled `harness = false` bench (no criterion; offline). It reports:
//!   1. in-memory workflow latency at 1/2/4/8 steps — a linear fit separates the
//!      fixed per-workflow runtime cost from the marginal per-step (durable
//!      checkpoint + meter-tick + the owned sandbox run) cost;
//!   2. on-disk SQLite: a full run-to-completion (incl. WAL fsync) of a 2-step
//!      workflow — the durable-I/O tax over the in-memory path;
//!   3. checkpoint + crash-resume: run-to-park, tear the runtime down, reopen the
//!      on-disk store, resume to completion — the recovery cost.
//!
//! The Postgres path (`--features pg`) is the multi-host durability boundary; it
//! is `DATABASE_URL`-gated and NOT exercised here (noted in docs/PERF.md).
//!
//! Run:  `cargo bench -p dreggnet-durable --bench durable_bench`

use std::sync::Arc;
use std::time::{Duration, Instant};

use dreggnet_durable::{
    ORCHESTRATION_NAME, WorkflowInput, WorkflowOutput, WorkloadRun, WorkloadSpec, build_registries,
    metrics, run_workflow_in_memory_blocking,
};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

/// A trivial sandboxed WAT step (add of two literals) — keeps the *the owned sandbox* cost
/// minimal so the measured number is dominated by the durable machinery, not the
/// guest. (Workload-guest cost is characterized in the exec bench.)
fn wat_add_step(label: &str, x: i32, y: i32) -> WorkloadSpec {
    WorkloadSpec {
        label: label.to_string(),
        lang: "wat".to_string(),
        source: format!(
            "(module (func (export \"run\") (result i32) (i32.add (i32.const {x}) (i32.const {y}))))"
        ),
        cap_tier: "sandboxed".to_string(),
    }
}

fn fmt(d: Duration) -> String {
    let ms = d.as_secs_f64() * 1e3;
    if ms >= 1.0 {
        format!("{:.2}ms", ms)
    } else {
        format!("{:.1}us", ms * 1000.0)
    }
}

fn timed<F: FnMut()>(label: &str, iters: usize, warmup: usize, mut f: F) -> Duration {
    // iters == 0 is an explicit skip (used by the CI bench-smoke lane to drop the
    // slow on-disk duroxide path) — never run the body, never index empty samples.
    if iters == 0 {
        println!("  {label:<40} SKIPPED (0 iters)");
        return Duration::ZERO;
    }
    for _ in 0..warmup {
        f();
    }
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        f();
        samples.push(t.elapsed());
    }
    samples.sort();
    let n = samples.len().max(1);
    let mean: Duration = samples.iter().sum::<Duration>() / n as u32;
    let p50 = samples[n / 2];
    let p95 = samples[((n as f64) * 0.95) as usize % n];
    println!(
        "  {:<40} n={:<4} mean={:>9}  p50={:>9}  p95={:>9}  ~{:.0}/s",
        label,
        iters,
        fmt(mean),
        fmt(p50),
        fmt(p95),
        1.0 / mean.as_secs_f64()
    );
    mean
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn in_memory_run(steps: usize, counter: &mut u64) {
    let specs: Vec<WorkloadSpec> = (0..steps)
        .map(|i| wat_add_step(&format!("s{i}"), 40, 2))
        .collect();
    // Budget generous so no step lapses; cost 1/step.
    let run = WorkloadRun::new(steps as i64 * 4, 1, specs);
    *counter += 1;
    let inst = format!("bench-mem-{counter}");
    let out = run_workflow_in_memory_blocking(&run, &inst).expect("durable run");
    assert_eq!(out.outputs.len(), steps);
}

fn main() {
    println!("\n=== DreggNet durable-layer characterization ===");
    println!("    a owned-sandbox workload run as a crash-resumable duroxide workflow");
    println!("    (in-memory SQLite store; trivial WAT step so the number is the durable tax)\n");

    let iters = env_usize("BENCH_ITERS", 200);
    let mut ctr = 0u64;

    println!("  -- in-memory workflow latency by step count --");
    let m1 = timed("in-mem  1 step", iters, 10, || in_memory_run(1, &mut ctr));
    let m2 = timed("in-mem  2 steps", iters, 10, || in_memory_run(2, &mut ctr));
    let m4 = timed("in-mem  4 steps", iters / 2, 10, || {
        in_memory_run(4, &mut ctr)
    });
    let m8 = timed("in-mem  8 steps", iters / 4, 10, || {
        in_memory_run(8, &mut ctr)
    });

    // Linear fit over (1,2,4,8): marginal per-step from the 1->8 slope, fixed
    // per-workflow cost = m1 - per_step.
    let per_step = (m8.as_secs_f64() - m1.as_secs_f64()) / 7.0;
    let fixed = m1.as_secs_f64() - per_step;
    println!(
        "\n  derived:  fixed per-workflow ~{:.0}us   marginal per-step ~{:.0}us  (1->2->4->8 fit; m2={}, m4={})",
        fixed * 1e6,
        per_step * 1e6,
        fmt(m2),
        fmt(m4),
    );

    // ---- on-disk SQLite: full run-to-completion (incl. WAL fsync) ----
    println!("\n  -- on-disk SQLite store (durable I/O tax) --");
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("rt");
    let disk_iters = env_usize("BENCH_DISK_ITERS", 50);

    let mut disk_ctr = 0u64;
    timed("on-disk 2-step run-to-completion", disk_iters, 3, || {
        disk_ctr += 1;
        rt.block_on(on_disk_full_run(disk_ctr));
    });

    // ---- checkpoint + crash-resume cost ----
    println!("\n  -- checkpoint + crash-resume (run-to-park, teardown, reopen, resume) --");
    let mut res_ctr = 0u64;
    timed("on-disk checkpoint+resume cycle", disk_iters, 3, || {
        res_ctr += 1;
        rt.block_on(on_disk_resume_cycle(res_ctr));
    });

    println!();
}

/// Open a fresh on-disk SQLite store in a temp dir and run a 2-step workflow to
/// completion — the full durable-I/O path (WAL writes + fsync on each checkpoint).
async fn on_disk_full_run(n: u64) {
    let dir = tempfile::tempdir().expect("tempdir");
    let db = dir.path().join("d.db");
    let url = format!("sqlite:{}?mode=rwc", db.display());
    let store = Arc::new(SqliteProvider::new(&url, None).await.expect("open"));
    let (a, o) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), a, o).await;
    let client = Client::new(store.clone());
    let inst = format!("bench-disk-{n}");
    let input = serde_json::to_string(&WorkflowInput {
        budget_units: 100,
        cost_per_step: 1,
        pause_event: None,
    })
    .unwrap();
    client
        .start_orchestration(&inst, ORCHESTRATION_NAME, input)
        .await
        .expect("start");
    let status = client
        .wait_for_orchestration(&inst, Duration::from_secs(30))
        .await
        .expect("wait");
    match status {
        OrchestrationStatus::Completed { output, .. } => {
            let _out: WorkflowOutput = serde_json::from_str(&output).unwrap();
        }
        other => panic!("did not complete: {other:?}"),
    }
    rt.shutdown(None).await;
}

/// The crash-resume path: run up to the post-step1 park point, tear the runtime
/// down, reopen the SAME on-disk store, and resume to completion.
async fn on_disk_resume_cycle(n: u64) {
    let dir = tempfile::tempdir().expect("tempdir");
    let db = dir.path().join("d.db");
    let url = format!("sqlite:{}?mode=rwc", db.display());
    let inst = format!("bench-resume-{n}");
    let input = serde_json::to_string(&WorkflowInput {
        budget_units: 100,
        cost_per_step: 1,
        pause_event: Some("Resume".to_string()),
    })
    .unwrap();

    // Runtime #1: run to the post-step1 checkpoint, then "crash".
    {
        let store = Arc::new(SqliteProvider::new(&url, None).await.expect("open1"));
        let (a, o) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), a, o).await;
        let client = Client::new(store.clone());
        client
            .start_orchestration(&inst, ORCHESTRATION_NAME, input)
            .await
            .expect("start");
        // Wait until step1 has run and the workflow has parked.
        for _ in 0..400 {
            let ran = metrics::run_calls(&inst, "step1") >= 1;
            let st = client.get_orchestration_status(&inst).await.unwrap();
            if ran && matches!(st, OrchestrationStatus::Running { .. }) {
                break;
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
        rt.shutdown(None).await;
    }
    // Runtime #2: resume over the same store.
    {
        let store = Arc::new(SqliteProvider::new(&url, None).await.expect("open2"));
        let (a, o) = build_registries();
        let rt = Runtime::start_with_store(store.clone(), a, o).await;
        let client = Client::new(store.clone());
        client
            .raise_event(&inst, "Resume", "")
            .await
            .expect("raise");
        let status = client
            .wait_for_orchestration(&inst, Duration::from_secs(30))
            .await
            .expect("wait");
        match status {
            OrchestrationStatus::Completed { .. } => {}
            other => panic!("resume did not complete: {other:?}"),
        }
        rt.shutdown(None).await;
    }
}
