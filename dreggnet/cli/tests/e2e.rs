//! Full-stack end-to-end test for DreggNet.
//!
//! Two complementary proofs that the whole stack composes:
//!
//! 1. [`full_stack_lease_to_reap`] drives the layers **directly in one process** —
//!    lease → `Scheduler::place` → `LocalProvider` provisions → the bridge fulfills →
//!    the durable metered workflow runs (`add(40,2)=42`, then `*2=84`) → the meter
//!    ticks (2 units) → the result is returned → the machine is reaped. This is the
//!    layers-compose proof: every rung (control → bridge → durable → exec → the owned sandbox)
//!    is exercised in a single test.
//!
//! 2. [`cli_lease_run_status_flow`] drives the **`dregg-cloud` binary itself** against a
//!    temp state dir: `lease open` → `run` → `status`, asserting the operator face
//!    produces the same end-to-end result over its persisted registry.

use std::process::Command;

use dreggnet_control::{
    CapGrade, Lease, LocalProvider, MachineSize, MachineStatus, Scheduler, VmProvider,
    WorkloadState,
};

/// The whole stack in one test: lease → schedule → provision → fulfill (durable the owned sandbox
/// workflow) → meter → result → reap.
#[tokio::test]
async fn full_stack_lease_to_reap() {
    // A funded execution-lease: sandboxed grade, budget 100, 1 unit/step.
    let lease = Lease::funded("e2e-agent", CapGrade::Sandboxed, "USD", 100, 1);
    assert!(lease.is_active());

    // The control plane over the in-process LocalProvider (the genuine run path).
    let scheduler = Scheduler::new(LocalProvider::new(), MachineSize::Small, "local");

    // Place: provision a machine → fulfill the lease as a durable metered workflow.
    let workload_id = scheduler.place(lease).await.expect("placed");
    let workload = scheduler.workload(&workload_id).expect("tracked");

    // The durable workflow really ran on the owned sandbox, metered against the budget.
    assert_eq!(workload.state, WorkloadState::Completed);
    let out = workload.output.clone().expect("workflow output");
    assert_eq!(out.step1, "42", "step1 = add(40,2) on the owned sandbox");
    assert_eq!(out.step2, "84", "step2 = step1 * 2 on the owned sandbox");
    assert_eq!(out.meter_units, 2, "two metered steps at cost 1 each");

    // A machine was provisioned and is Running until reaped.
    let machine_id = workload.machine.id.clone();
    assert_eq!(
        scheduler.provider().status(&machine_id).await.unwrap(),
        MachineStatus::Running
    );

    // Reap → the machine is terminated, the workload is Reaped (no dangling box).
    scheduler.reap(&workload_id).await.expect("reaped");
    assert_eq!(
        scheduler.workload(&workload_id).unwrap().state,
        WorkloadState::Reaped
    );
    assert_eq!(
        scheduler.provider().status(&machine_id).await.unwrap(),
        MachineStatus::Terminated
    );
}

/// An over-budget lease lapses during fulfillment and is auto-reaped through the full
/// stack — no machine is left running for unpayable work.
#[tokio::test]
async fn full_stack_over_budget_lapses_and_reaps() {
    // budget 1, cost 2: the first meter tick already exceeds the budget → lapse.
    let lease = Lease::funded("e2e-broke", CapGrade::Sandboxed, "USD", 1, 2);
    let scheduler = Scheduler::new(LocalProvider::new(), MachineSize::Small, "local");

    let workload_id = scheduler
        .place(lease)
        .await
        .expect("placed then lapsed+reaped");
    let workload = scheduler.workload(&workload_id).expect("tracked");

    assert_eq!(workload.state, WorkloadState::Reaped);
    assert!(workload.output.is_none());
    assert_eq!(
        scheduler
            .provider()
            .status(&workload.machine.id)
            .await
            .unwrap(),
        MachineStatus::Terminated
    );
}

/// The operator face: drive the `dregg-cloud` binary `lease open` → `run` → `status`
/// against a temp state dir, proving the subcommands share state + run the workload.
#[test]
fn cli_lease_run_status_flow() {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let dir = tempfile::tempdir().unwrap();
    let state_dir = dir.path();

    // A workload source file (declared program; WAT text).
    let source = state_dir.join("workload.wat");
    std::fs::write(
        &source,
        "(module (func (export \"run\") (result i32) (i32.const 42)))",
    )
    .unwrap();

    // --- lease open ---
    let open = Command::new(bin)
        .args(["--state-dir"])
        .arg(state_dir)
        .args([
            "lease",
            "open",
            "--cap-tier",
            "sandboxed",
            "--budget",
            "100",
        ])
        .output()
        .expect("run `lease open`");
    assert!(
        open.status.success(),
        "lease open failed: {}",
        String::from_utf8_lossy(&open.stderr)
    );
    let open_out = String::from_utf8(open.stdout).unwrap();
    let lease_id = open_out
        .lines()
        .find_map(|l| l.strip_prefix("lease opened: "))
        .expect("lease id in output")
        .trim()
        .to_string();
    assert!(!lease_id.is_empty());

    // --- run ---
    let run = Command::new(bin)
        .args(["--state-dir"])
        .arg(state_dir)
        .args(["run", "--lease", &lease_id, "--lang", "wat", "--source"])
        .arg(&source)
        .output()
        .expect("run `run`");
    assert!(
        run.status.success(),
        "run failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let run_out = String::from_utf8(run.stdout).unwrap();
    // `run --source` runs the DECLARED program (this WAT returns 42), not a fixed
    // demo: the single durable step's output is 42, metered once.
    assert!(
        run_out.contains("output[0]  42"),
        "missing declared-program output in:\n{run_out}"
    );
    assert!(
        !run_out.contains("add(40, 2)"),
        "must NOT run the fixed demo:\n{run_out}"
    );
    assert!(
        run_out.contains("1 units charged"),
        "missing meter in:\n{run_out}"
    );
    assert!(
        run_out.contains("completed"),
        "missing state in:\n{run_out}"
    );

    // --- status (all) ---
    let status = Command::new(bin)
        .args(["--state-dir"])
        .arg(state_dir)
        .args(["status"])
        .output()
        .expect("run `status`");
    assert!(status.status.success());
    let status_out = String::from_utf8(status.stdout).unwrap();
    assert!(
        status_out.contains("WORKLOAD"),
        "missing header in:\n{status_out}"
    );
    assert!(
        status_out.contains("completed"),
        "missing completed workload in:\n{status_out}"
    );

    // --- status --lease (filtered) ---
    let filtered = Command::new(bin)
        .args(["--state-dir"])
        .arg(state_dir)
        .args(["status", "--lease", &lease_id])
        .output()
        .expect("run `status --lease`");
    assert!(filtered.status.success());
    let filtered_out = String::from_utf8(filtered.stdout).unwrap();
    assert!(
        filtered_out.contains("completed"),
        "filtered status missing workload:\n{filtered_out}"
    );

    // An unknown lease filter lists nothing (no panic).
    let none = Command::new(bin)
        .args(["--state-dir"])
        .arg(state_dir)
        .args(["status", "--lease", "no-such-lease"])
        .output()
        .expect("run `status --lease no-such-lease`");
    assert!(none.status.success());
    assert!(
        String::from_utf8(none.stdout)
            .unwrap()
            .contains("no workloads for lease")
    );
}

/// `run` against an unknown lease id fails cleanly (no panic, nonzero exit).
#[test]
fn cli_run_unknown_lease_errors() {
    let bin = env!("CARGO_BIN_EXE_dregg-cloud");
    let dir = tempfile::tempdir().unwrap();
    let source = dir.path().join("w.wat");
    std::fs::write(&source, "(module)").unwrap();

    let run = Command::new(bin)
        .args(["--state-dir"])
        .arg(dir.path())
        .args(["run", "--lease", "ghost", "--lang", "wat", "--source"])
        .arg(&source)
        .output()
        .expect("run");
    assert!(!run.status.success(), "expected failure for unknown lease");
    assert!(
        String::from_utf8(run.stderr)
            .unwrap()
            .contains("no lease `ghost`")
    );
}
