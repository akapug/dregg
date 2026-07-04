//! Workload-execution characterization: latency + throughput of
//! [`dreggnet_exec::run_workload`] per cap-tier (wasmi `Sandboxed`, wasmtime
//! `JitSandboxed`, native CPython `Caged`), plus a horizontal (N-thread) scaling
//! sweep on the dominant in-process tier.
//!
//! Hand-rolled `harness = false` bench (no criterion dependency, fully offline):
//! it runs a warmup, times N iterations with `Instant`, and prints a latency
//! distribution + a derived single-thread throughput. The native-CPython tier
//! is skipped (printed as SKIPPED) when no `python3` is on PATH, exactly like the
//! crate's unit test.
//!
//! Run:  `cargo bench -p dreggnet-exec --bench workload_exec`
//! Knobs (env): `BENCH_ITERS` (default per-tier below), `BENCH_WIDE_N`
//! (comma-list of thread counts for the wide sweep), `BENCH_WIDE_ITERS`.

use dreggnet_exec::{CapTier, Input, run_workload, run_workload_with_input};
use std::time::{Duration, Instant};

// ---- canonical workloads (the same sources the unit tests exercise) ----

/// wasmi (Sandboxed): a core module computing add(40, 2) == 42.
const WASMI_ADD: &str = r#"
    (module
      (func $add (param $a i32) (param $b i32) (result i32)
        local.get $a local.get $b i32.add)
      (func (export "run") (result i32)
        (call $add (i32.const 40) (i32.const 2))))
"#;

/// wasmtime (JitSandboxed): a component lifting add(40, 2) == 42.
const WASMTIME_ADD: &str = r#"
    (component
      (core module $m
        (func $add (param $a i32) (param $b i32) (result i32)
          local.get $a local.get $b i32.add)
        (func (export "run") (result i32)
          (call $add (i32.const 40) (i32.const 2))))
      (core instance $i (instantiate $m))
      (func (export "run") (result s32)
        (canon lift (core func $i "run"))))
"#;

/// A heavier wasmi workload: sum 1..=N in a loop (busy in-sandbox compute), to
/// separate "instantiate + call overhead" from "actual guest work".
const WASMI_LOOP: &str = r#"
    (module
      (func (export "run") (result i32)
        (local $i i32) (local $acc i32)
        (local.set $i (i32.const 0))
        (local.set $acc (i32.const 0))
        (block $done
          (loop $l
            (br_if $done (i32.ge_s (local.get $i) (i32.const 1000000)))
            (local.set $acc (i32.add (local.get $acc) (local.get $i)))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $l)))
        (local.get $acc)))
"#;

/// CPython (Caged): a guest that speaks the owned sandbox's newline-JSON wire and sums args.
const PY_ADD: &str = r#"import sys, json
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    req = json.loads(line)
    a = req.get("args", [])
    print(json.dumps({"ok": [a[0] + a[1]]}), flush=True)
"#;

// ---- timing harness ----

struct Stats {
    label: String,
    n: usize,
    samples: Vec<Duration>,
}

impl Stats {
    fn report(mut self) {
        self.samples.sort();
        let n = self.samples.len().max(1);
        let total: Duration = self.samples.iter().sum();
        let mean = total / n as u32;
        let min = self.samples[0];
        let p = |q: f64| self.samples[((n as f64 * q) as usize).min(n - 1)];
        let per_sec = if mean.as_secs_f64() > 0.0 {
            1.0 / mean.as_secs_f64()
        } else {
            f64::INFINITY
        };
        println!(
            "  {:<34} n={:<5} min={:>10}  mean={:>10}  p50={:>10}  p95={:>10}  p99={:>10}  ~{:>9.1}/s (1 thread)",
            self.label,
            self.n,
            fmt(min),
            fmt(mean),
            fmt(p(0.50)),
            fmt(p(0.95)),
            fmt(p(0.99)),
            per_sec,
        );
    }
}

fn fmt(d: Duration) -> String {
    let us = d.as_secs_f64() * 1e6;
    if us >= 1000.0 {
        format!("{:.2}ms", us / 1000.0)
    } else {
        format!("{:.1}us", us)
    }
}

fn bench<F: FnMut()>(label: &str, iters: usize, warmup: usize, mut f: F) -> Stats {
    for _ in 0..warmup {
        f();
    }
    let mut samples = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        f();
        samples.push(t.elapsed());
    }
    Stats {
        label: label.to_string(),
        n: iters,
        samples,
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn python3_available() -> bool {
    let bin = std::env::var("DREGGNET_PYTHON_BIN").unwrap_or_else(|_| "python3".into());
    std::process::Command::new(&bin)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn main() {
    println!("\n=== DreggNet workload-exec characterization (VERTICAL, single thread) ===");
    println!("    one `run_workload` = construct provider + store + load + instantiate + call\n");

    let iters = env_usize("BENCH_ITERS", 0);

    // wasmi Sandboxed — the cheapest real sandbox (pure interpreter).
    bench(
        "wasmi  Sandboxed   add(40,2)",
        if iters > 0 { iters } else { 2000 },
        50,
        || {
            let out = run_workload("wat", WASMI_ADD, CapTier::Sandboxed).expect("wasmi add");
            assert_eq!(out.values, vec!["42".to_string()]);
        },
    )
    .report();

    // wasmi Sandboxed with a 1M-iteration in-guest loop — shows the guest-work
    // floor vs the trivial-add overhead.
    bench(
        "wasmi  Sandboxed   sum(1..1e6)",
        if iters > 0 { iters } else { 500 },
        20,
        || {
            let _ = run_workload("wat", WASMI_LOOP, CapTier::Sandboxed).expect("wasmi loop");
        },
    )
    .report();

    // wasmtime JitSandboxed — Cranelift JIT compile + fuel meter per call.
    bench(
        "wasmtime JitSandbox add(40,2)",
        if iters > 0 { iters } else { 500 },
        20,
        || {
            let out =
                run_workload("wat", WASMTIME_ADD, CapTier::JitSandboxed).expect("wasmtime add");
            assert_eq!(out.values, vec!["42".to_string()]);
        },
    )
    .report();

    // native CPython Caged — a real python3 subprocess per call (spawn + wire).
    if python3_available() {
        bench(
            "python Caged       add(40,2)",
            if iters > 0 { iters } else { 200 },
            10,
            || {
                let out = run_workload_with_input(
                    "python",
                    PY_ADD,
                    CapTier::Caged,
                    &[Input::I64(40), Input::I64(2)],
                )
                .expect("python add");
                assert_eq!(out.values, vec!["42".to_string()]);
            },
        )
        .report();
    } else {
        println!("  python Caged       add(40,2)        SKIPPED (no python3 on PATH)");
    }

    // ---- WIDE: horizontal scaling on the dominant in-process tier (wasmi) ----
    println!("\n=== WIDE scaling sweep (N concurrent threads, wasmi Sandboxed add) ===");
    println!("    aggregate throughput vs thread count — finds the per-node plateau\n");

    let wide_iters = env_usize("BENCH_WIDE_ITERS", 2000);
    let ns: Vec<usize> = std::env::var("BENCH_WIDE_N")
        .ok()
        .map(|s| s.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .unwrap_or_else(|| {
            let cores = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(8);
            vec![1, 2, 4, cores, cores * 2]
        });

    println!(
        "    detected parallelism: {}",
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(0)
    );
    let mut baseline = 0.0f64;
    for (idx, &n) in ns.iter().enumerate() {
        let t = Instant::now();
        let handles: Vec<_> = (0..n)
            .map(|_| {
                std::thread::spawn(move || {
                    for _ in 0..wide_iters {
                        let _ =
                            run_workload("wat", WASMI_ADD, CapTier::Sandboxed).expect("wasmi add");
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }
        let elapsed = t.elapsed();
        let total_ops = (n * wide_iters) as f64;
        let throughput = total_ops / elapsed.as_secs_f64();
        if idx == 0 {
            baseline = throughput;
        }
        let scaling = if baseline > 0.0 {
            throughput / baseline
        } else {
            0.0
        };
        println!(
            "    N={:<4} {:>8} ops in {:>8.3}s  =>  {:>10.0} ops/s   ({:.2}x vs N=1)",
            n,
            n * wide_iters,
            elapsed.as_secs_f64(),
            throughput,
            scaling,
        );
    }
    println!();
}
