//! Control-plane characterization: the full lease lifecycle through the
//! scheduler — `place` (provision a LocalProvider machine + fulfill the lease as
//! a durable, metered polyana workflow) and `reap` (terminate the machine) —
//! sequential latency and concurrent throughput (leases/sec vs N).
//!
//! The `LocalProvider` runs the workload in-process via the bridge (the proven
//! end-to-end path); provisioning is a HashMap insert, so this isolates the
//! control-plane bookkeeping + the bridge fulfillment from any cloud-API latency
//! (the EC2 provider's `aws` CLI shell-out is the real-cloud number, not
//! measured offline here).
//!
//! Run:  `cargo bench -p dreggnet-control --bench scheduler_bench`

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use dreggnet_control::provider::MachineSize;
use dreggnet_control::{CapGrade, Lease, LocalProvider, Scheduler};

fn fmt(d: Duration) -> String {
    let ms = d.as_secs_f64() * 1e3;
    if ms >= 1.0 {
        format!("{:.2}ms", ms)
    } else {
        format!("{:.1}us", ms * 1000.0)
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn lease() -> Lease {
    Lease::funded("agent-bench", CapGrade::Sandboxed, "USD-test", 1_000_000, 1)
}

fn main() {
    println!("\n=== DreggNet control-plane (scheduler) characterization ===");
    println!("    place = provision (LocalProvider) + fulfill (durable workflow) ; then reap\n");

    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("rt");

    // --- sequential place->reap latency ---
    let seq_iters = env_usize("BENCH_ITERS", 150);
    {
        let sched = Scheduler::new(LocalProvider::new(), MachineSize::Small, "local");
        for _ in 0..5 {
            let id = rt.block_on(sched.place(lease())).expect("place");
            rt.block_on(sched.reap(&id)).expect("reap");
        }
        let mut samples = Vec::with_capacity(seq_iters);
        for _ in 0..seq_iters {
            let t = Instant::now();
            let id = rt.block_on(sched.place(lease())).expect("place");
            rt.block_on(sched.reap(&id)).expect("reap");
            samples.push(t.elapsed());
        }
        samples.sort();
        let n = samples.len();
        let mean: Duration = samples.iter().sum::<Duration>() / n as u32;
        println!(
            "  place+reap sequential                   n={:<4} mean={:>9}  p50={:>9}  p95={:>9}  ~{:.0} leases/s",
            n,
            fmt(mean),
            fmt(samples[n / 2]),
            fmt(samples[(n as f64 * 0.95) as usize % n]),
            1.0 / mean.as_secs_f64(),
        );
    }

    // --- concurrent place->reap throughput (WIDE) ---
    println!("\n  -- WIDE: N concurrent place+reap (leases/sec vs concurrency) --");
    let per_task = env_usize("BENCH_WIDE_ITERS", 80);
    let ns: Vec<usize> = std::env::var("BENCH_WIDE_N")
        .ok()
        .map(|s| s.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![1, 2, 4, 8, 16]);
    let mut baseline = 0.0f64;
    for (i, &n) in ns.iter().enumerate() {
        // One shared scheduler (the contention point: its workloads Mutex + the
        // provider's machine map are shared across all concurrent placements).
        let sched = Arc::new(Scheduler::new(
            LocalProvider::new(),
            MachineSize::Small,
            "local",
        ));
        let ctr = Arc::new(AtomicU64::new(0));
        let t = Instant::now();
        rt.block_on(async {
            let mut handles = Vec::new();
            for _ in 0..n {
                let sched = sched.clone();
                let ctr = ctr.clone();
                handles.push(tokio::spawn(async move {
                    for _ in 0..per_task {
                        let _ = ctr.fetch_add(1, Ordering::Relaxed);
                        let id = sched.place(lease()).await.expect("place");
                        sched.reap(&id).await.expect("reap");
                    }
                }));
            }
            for h in handles {
                h.await.unwrap();
            }
        });
        let e = t.elapsed();
        let tput = (n * per_task) as f64 / e.as_secs_f64();
        if i == 0 {
            baseline = tput;
        }
        println!(
            "    N={:<3} {:>5} leases in {:>7.3}s  =>  {:>8.0} leases/s   ({:.2}x vs N=1)",
            n,
            n * per_task,
            e.as_secs_f64(),
            tput,
            if baseline > 0.0 { tput / baseline } else { 0.0 },
        );
    }
    println!();
}
