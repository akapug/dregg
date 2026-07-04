//! `dreggnet-crash-resume` — the on-camera, real-process crash-resume proof.
//!
//! This is the *visceral* twin of the in-process recovery test
//! (`durable/tests/durable_resume.rs`). That test simulates a crash by tearing the
//! duroxide runtime down inside ONE process. This binary instead runs the durable
//! workload across TWO genuinely separate OS processes with a real `SIGKILL`
//! between them, over an on-disk SQLite durable store:
//!
//! ```text
//!   phase 1 (process A):  run step1 (add(40,2)=42) → meter period 1 → checkpoint
//!                         ↓  the orchestration parks on an external event
//!                         ↓  process A is SIGKILL-ed by demo/crash-resume.sh
//!   phase 2 (process B):  fresh process, SAME on-disk store
//!                         ↓  resume → step1 is REPLAYED (never re-run), step2 runs
//!                         ↓  meter period 2 charged once → exactly-once
//! ```
//!
//! ## Why a real `SIGKILL` is a stronger proof
//!
//! The in-process `metrics` ledger is process-local: it is wiped by a real crash.
//! So in phase 2 (a brand-new process) the count of times step1's activity body
//! *actually executed* starts at zero — and STAYS zero, because the recorded
//! result is replayed from the SQLite history rather than recomputed. A non-zero
//! step1 execution count in phase 2 would mean the work was re-run; observing zero
//! is direct, unfakeable evidence of exactly-once across the crash.
//!
//! The cumulative truth (across both processes) is reconstructed from a small
//! `--snapshot` JSON that phase 1 writes and phase 2 reads: it records how many
//! times each activity body *really ran* in phase 1. Summed with phase 2's own
//! process-local counts, it yields:
//!   - step1 real executions across the crash = 1  (ran in A, replayed in B)
//!   - step2 real executions across the crash = 1  (ran only in B)
//!   - meter charges across the crash         = 2  (period 1 in A, period 2 in B)
//! i.e. exactly-once per step, never double-charged.

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use anyhow::{Context, Result, anyhow, bail};
use clap::{Parser, ValueEnum};
use serde::{Deserialize, Serialize};

use dreggnet_durable::{
    ORCHESTRATION_NAME, WorkflowInput, WorkflowOutput, build_registries, metrics,
};
use duroxide::providers::sqlite::SqliteProvider;
use duroxide::runtime::Runtime;
use duroxide::{Client, OrchestrationStatus};

/// The external event the orchestration parks on after step 1; phase 2 raises it to resume.
const RESUME_EVENT: &str = "Resume";

#[derive(Parser)]
#[command(
    name = "dreggnet-crash-resume",
    about = "Drive a durable workload across a real process crash and prove exactly-once resume."
)]
struct Cli {
    /// Which half of the crash to run. Phase 1 runs to the checkpoint and parks
    /// (to be SIGKILL-ed); phase 2 resumes over the same store and proves exactly-once.
    #[arg(long, value_enum)]
    phase: Phase,
    /// The on-disk SQLite durable store. MUST be a path that survives the crash
    /// (an on-disk file, not `:memory:`), shared by both phases.
    #[arg(long)]
    db: PathBuf,
    /// The workflow instance id (= the lease id). Both phases must agree.
    #[arg(long, default_value = "lease-workflow-demo")]
    instance: String,
    /// The JSON snapshot phase 1 writes (its pre-crash facts) and phase 2 reads to
    /// reconstruct the cumulative exactly-once tally across the two processes.
    #[arg(long)]
    snapshot: PathBuf,
    /// Phase 1 creates this file once the post-step1 checkpoint is durable, so the
    /// driving script knows exactly when it is safe to SIGKILL.
    #[arg(long)]
    ready: Option<PathBuf>,
    /// The execution-lease budget, in meter units.
    #[arg(long, default_value_t = 100)]
    budget: i64,
    /// Meter units charged per durable step.
    #[arg(long, default_value_t = 1)]
    cost_per_step: i64,
}

#[derive(Clone, Copy, ValueEnum)]
enum Phase {
    #[value(name = "1")]
    One,
    #[value(name = "2")]
    Two,
}

/// The pre-crash facts phase 1 records for phase 2 to reconstruct the cumulative tally.
#[derive(Serialize, Deserialize, Debug)]
struct Snapshot {
    /// Times step1's activity body really executed in phase 1 (expected 1).
    step1_runs: i64,
    /// Times step2's activity body really executed in phase 1 (expected 0 — it parks first).
    step2_runs: i64,
    /// Meter charges that really committed in phase 1 (expected 1 — period 1).
    meter_charges: i64,
}

async fn open_store(db: &PathBuf) -> Result<Arc<SqliteProvider>> {
    let url = format!("sqlite:{}?mode=rwc", db.display());
    Ok(Arc::new(
        SqliteProvider::new(&url, None)
            .await
            .with_context(|| format!("open sqlite durable store {}", db.display()))?,
    ))
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.phase {
        Phase::One => phase1(&cli).await,
        Phase::Two => phase2(&cli).await,
    }
}

/// Phase 1: run to the post-step1 checkpoint, record the pre-crash facts, signal
/// "ready to crash", then stay alive so the driving script can SIGKILL us mid-flight.
async fn phase1(cli: &Cli) -> Result<()> {
    let store = open_store(&cli.db).await?;
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let input = serde_json::to_string(&WorkflowInput {
        budget_units: cli.budget,
        cost_per_step: cli.cost_per_step,
        // Park after step1 so we crash deterministically between the two steps.
        pause_event: Some(RESUME_EVENT.to_string()),
    })?;

    client
        .start_orchestration(&cli.instance, ORCHESTRATION_NAME, input)
        .await
        .map_err(|e| anyhow!("start orchestration: {e}"))?;

    // Wait until step1 has actually executed AND the orchestration has parked on the
    // wait (still Running) — i.e. step1 + its meter tick are durably checkpointed.
    let mut parked = false;
    for _ in 0..400 {
        let ran_step1 = metrics::run_calls(&cli.instance, "step1") >= 1;
        let status = client
            .get_orchestration_status(&cli.instance)
            .await
            .map_err(|e| anyhow!("status: {e}"))?;
        if ran_step1 && matches!(status, OrchestrationStatus::Running { .. }) {
            parked = true;
            break;
        }
        tokio::time::sleep(Duration::from_millis(25)).await;
    }
    if !parked {
        bail!("workflow did not reach the post-step1 checkpoint");
    }
    // Let the parked state flush to the on-disk store so it survives SIGKILL.
    tokio::time::sleep(Duration::from_millis(400)).await;

    let step1_runs = metrics::run_calls(&cli.instance, "step1");
    let step2_runs = metrics::run_calls(&cli.instance, "step2");
    let meter = metrics::meter_units(&cli.instance);

    let snap = Snapshot {
        step1_runs,
        step2_runs,
        meter_charges: meter,
    };
    std::fs::write(&cli.snapshot, serde_json::to_string(&snap)?)
        .with_context(|| format!("write snapshot {}", cli.snapshot.display()))?;

    println!("── PHASE 1 ── run to checkpoint, then crash ───────────────────────");
    println!("  store          {}", cli.db.display());
    println!("  instance       {}", cli.instance);
    println!("  step1          add(40, 2) = 42   [executed: {step1_runs}]");
    println!(
        "  meter period 1 charged {} unit(s)   (budget {})",
        meter, cli.budget
    );
    println!("  step2          not run yet         [executed: {step2_runs}]");
    println!("  checkpoint     DURABLE on disk — step1 + its meter tick survive a crash");

    if let Some(ready) = &cli.ready {
        std::fs::write(ready, format!("{}", std::process::id()))
            .with_context(|| format!("write ready file {}", ready.display()))?;
    }
    println!(
        "  pid            {}  (awaiting SIGKILL — the checkpoint is safe)",
        std::process::id()
    );

    // Stay alive so the driver can deliver a genuine SIGKILL while we are mid-workflow.
    // We deliberately do NOT shut the runtime down: the crash must be abrupt.
    for _ in 0..2400 {
        tokio::time::sleep(Duration::from_millis(25)).await;
    }
    // If we were never killed, exit cleanly (the driver handles the kill).
    rt.shutdown(None).await;
    Ok(())
}

/// Phase 2: a fresh process resumes over the SAME on-disk store and proves exactly-once.
async fn phase2(cli: &Cli) -> Result<()> {
    let snap: Snapshot = {
        let raw = std::fs::read_to_string(&cli.snapshot)
            .with_context(|| format!("read snapshot {}", cli.snapshot.display()))?;
        serde_json::from_str(&raw).context("parse snapshot")?
    };

    let store = open_store(&cli.db).await?;
    let (activities, orchestrations) = build_registries();
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    // Resume: deliver the event the workflow parked on before the crash.
    client
        .raise_event(&cli.instance, RESUME_EVENT, "")
        .await
        .map_err(|e| anyhow!("raise resume event: {e}"))?;

    let status = client
        .wait_for_orchestration(&cli.instance, Duration::from_secs(60))
        .await
        .map_err(|e| anyhow!("wait for completion: {e}"))?;
    let output = match status {
        OrchestrationStatus::Completed { output, .. } => output,
        other => bail!("workflow did not complete after resume: {other:?}"),
    };
    let out: WorkflowOutput = serde_json::from_str(&output).context("parse workflow output")?;

    // This process's own (post-crash) execution counts. The in-memory ledger started
    // empty, so these count ONLY what ran in phase 2.
    let step1_here = metrics::run_calls(&cli.instance, "step1");
    let step2_here = metrics::run_calls(&cli.instance, "step2");
    let meter_here = metrics::meter_units(&cli.instance);

    // Cumulative across the crash = phase 1 (snapshot) + phase 2 (this process).
    let step1_total = snap.step1_runs + step1_here;
    let step2_total = snap.step2_runs + step2_here;
    let meter_total = snap.meter_charges + meter_here;

    println!("── PHASE 2 ── resume over the SAME store ──────────────────────────");
    println!("  store          {}", cli.db.display());
    println!(
        "  resumed        instance {} from the on-disk checkpoint",
        cli.instance
    );
    println!(
        "  step1          = {}   REPLAYED, not re-run  [this process executed it {step1_here} time(s)]",
        out.step1
    );
    println!(
        "  step2          = {}   ran once this process  [executed: {step2_here}]",
        out.step2
    );
    println!("  meter period 2 charged {meter_here} unit(s) this process");
    println!();
    println!("  ── exactly-once across the crash ──");
    println!(
        "  step1 real executions   {step1_total}  (phase1 {} + phase2 {step1_here})",
        snap.step1_runs
    );
    println!(
        "  step2 real executions   {step2_total}  (phase1 {} + phase2 {step2_here})",
        snap.step2_runs
    );
    println!(
        "  meter charged (total)   {meter_total}  (phase1 {} + phase2 {meter_here})",
        snap.meter_charges
    );

    // The proof, asserted. Any violation fails the binary (so the demo/CI catches a regression).
    let mut ok = true;
    let mut check = |name: &str, got: i64, want: i64| {
        if got != want {
            eprintln!("  ✗ FAIL {name}: got {got}, want {want}");
            ok = false;
        }
    };
    check(
        "step1 executed exactly once across the crash",
        step1_total,
        1,
    );
    check(
        "step1 was NOT re-executed in the resumed process",
        step1_here,
        0,
    );
    check("step2 executed exactly once", step2_total, 1);
    check(
        "meter charged exactly twice (one per period), never doubled",
        meter_total,
        2,
    );
    if out.step1 != "42" {
        eprintln!("  ✗ FAIL step1 value: got {}, want 42", out.step1);
        ok = false;
    }
    if out.step2 != "84" {
        eprintln!("  ✗ FAIL step2 value: got {}, want 84", out.step2);
        ok = false;
    }

    rt.shutdown(None).await;

    if ok {
        println!();
        println!("  ✓ exactly-once proven across a real SIGKILL: step1 replayed, step2 ran once,");
        println!("    the meter charged exactly twice — no compute or charge was duplicated.");
        Ok(())
    } else {
        bail!("crash-resume exactly-once proof FAILED");
    }
}
