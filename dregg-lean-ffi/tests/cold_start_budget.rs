//! #86 — the COMPLETE Lean initialization is a node-boot cost, and it is budgeted here.
//!
//! `dregg-node` runs `lean_init_once()` (every module the archive links, via
//! `dregg_ffi_init_modules`) before its first log line, and Lean computes every compiled
//! no-argument `def` when its module initializes. A fixture or a `check_*` statement left in a
//! module the archive links therefore runs on every boot: on 2026-10-01 three such definitions in
//! `CrewFieldMissionRuntime` (three full `judge` runs) were ~117 s of a ~158 s start on hbox, and
//! ~6.3 min on the deployed box. Nothing failed; the node was only late, so nothing caught it.
//!
//! This measures the init in a FRESH process (the parent re-executes this test binary, so it holds
//! under libtest and nextest alike) and refuses a CPU cost above `BUDGET_CPU_SECONDS`. CPU, not
//! wall time, so a loaded build box does not turn contention into a red. Self-skips without the
//! archive (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).
#![cfg(feature = "lean-lib")]

use std::process::Command;
use std::time::Instant;

const CHILD: &str = "DREGG_COLD_START_CHILD";

/// CPU seconds the complete Lean initialization may cost. Measured after the #86 fix on hbox
/// (`dregg-node status`, whole process, before the first log line): see
/// claudesplosion/fixes/node-init-86.md. The deployed box ran ~2.4x slower than hbox for the same
/// work, so the budget leaves room for a slower machine while sitting far below the regression it
/// exists to catch (~158 s on hbox).
const BUDGET_CPU_SECONDS: f64 = 30.0;

/// User+system CPU seconds of this process (Linux `/proc/self/stat`, clock ticks at the kernel's
/// fixed `USER_HZ` = 100). `None` elsewhere; the caller then measures wall time.
fn cpu_seconds() -> Option<f64> {
    let stat = std::fs::read_to_string("/proc/self/stat").ok()?;
    // Fields after the parenthesised comm, which may itself contain spaces.
    let rest = &stat[stat.rfind(')')? + 2..];
    let fields: Vec<&str> = rest.split_whitespace().collect();
    // `rest` starts at field 3 (state); utime and stime are fields 14 and 15.
    let utime: u64 = fields.get(11)?.parse().ok()?;
    let stime: u64 = fields.get(12)?.parse().ok()?;
    Some((utime + stime) as f64 / 100.0)
}

fn peak_rss_kb() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

#[test]
fn complete_lean_init_fits_the_cold_start_budget() {
    if std::env::var(CHILD).is_ok() {
        // The child: a fresh process in which nothing has initialized Lean yet.
        assert_eq!(
            dregg_lean_ffi::lean_initialization_status(),
            Default::default(),
            "the measuring process must start with Lean uninitialized"
        );
        let cpu0 = cpu_seconds();
        let wall0 = Instant::now();
        // `lean_available` IS the complete initialization (`lean_init_once`, every linked module).
        let available = dregg_lean_ffi::lean_available();
        let wall = wall0.elapsed().as_secs_f64();
        let cpu = cpu_seconds().zip(cpu0).map(|(b, a)| b - a);
        println!(
            "COLD_START available={available} cpu_s={} wall_s={wall:.2} peak_rss_kb={}",
            cpu.map_or("na".to_string(), |c| format!("{c:.2}")),
            peak_rss_kb().map_or("na".to_string(), |k| k.to_string())
        );
        return;
    }

    let out = Command::new(std::env::current_exe().expect("test binary path"))
        .args([
            "--exact",
            "complete_lean_init_fits_the_cold_start_budget",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD, "1")
        .output()
        .expect("start the measuring child");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "the measuring child failed: {}\n{stdout}\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    // libtest prints `test <name> ... ` before the body's output, so the record can start mid-line.
    let line = stdout
        .lines()
        .find_map(|l| l.find("COLD_START ").map(|at| &l[at..]))
        .unwrap_or_else(|| panic!("the child printed no measurement — nothing was measured:\n{stdout}"));
    eprintln!("{line}");
    // The parent never initializes Lean itself; the child's verdict decides the quiet path.
    if !dregg_lean_ffi::demand_lean(
        line.contains("available=true"),
        "the linked Lean archive (the cold-start budget measures its initialization)",
    ) {
        return;
    }
    let field = |key: &str| -> Option<f64> {
        line.split_whitespace()
            .find_map(|kv| kv.strip_prefix(key))
            .and_then(|v| v.parse().ok())
    };
    // CPU where the platform reports it; wall time otherwise (it can only over-count).
    let spent = field("cpu_s=")
        .or_else(|| field("wall_s="))
        .expect("a cpu_s or wall_s figure");
    // `DREGG_COLD_START_BUDGET_S` can only TIGHTEN the budget (it is how the gate is shown to go
    // red: set it below the measured cost); it can never raise it.
    let budget = std::env::var("DREGG_COLD_START_BUDGET_S")
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .map_or(BUDGET_CPU_SECONDS, |v| v.min(BUDGET_CPU_SECONDS));
    assert!(
        spent <= budget,
        "complete Lean initialization cost {spent:.1} s, over the {budget} s cold-start \
         budget (#86). Every compiled no-argument `def` in a module the archive links runs at boot: \
         find it by sampling `dregg-node status --port 1` under gdb (the `_init_lp_*` frames under \
         `initialize_*`) and move a fixture or `check_*` into the module's `*Fixtures.lean`."
    );
}
