//! Bridge characterization: the lease gate (pure validation) and full lease
//! fulfillment (`fulfill` — a funded lease driven as a durable, metered
//! workflow over a fresh in-memory SQLite store), sequential and concurrent.
//!
//! Hand-rolled `harness = false` bench (no criterion; offline).
//!
//! Run:  `cargo bench -p dreggnet-bridge --bench lease_lifecycle`

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use dreggnet_bridge::{CapGrade, Lease, fulfill, workflow_input_for_lease};

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

fn main() {
    println!("\n=== DreggNet bridge / lease-fulfillment characterization ===");
    println!("    fulfill() = validate lease -> open in-mem durable store -> run the");
    println!("    fixed add->double workflow on the owned sandbox, metered against the budget\n");

    let lease = Lease::funded("agent-bench", CapGrade::Sandboxed, "USD-test", 1_000_000, 1);

    // --- the pure lease gate (no work runs) — the 402/admission fast path ---
    {
        let iters = 1_000_000usize;
        let t = Instant::now();
        for _ in 0..iters {
            let _ = workflow_input_for_lease(&lease, None).expect("gate");
        }
        let e = t.elapsed();
        println!(
            "  lease gate (workflow_input_for_lease)   {} gates in {:.3}s  =>  {:.0}/s ({} each)",
            iters,
            e.as_secs_f64(),
            iters as f64 / e.as_secs_f64(),
            fmt(e / iters as u32),
        );
    }

    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("rt");

    // --- sequential fulfillment latency ---
    let seq_iters = env_usize("BENCH_ITERS", 200);
    {
        let ctr = AtomicU64::new(0);
        // warmup
        for _ in 0..5 {
            let inst = format!("warm-{}", ctr.fetch_add(1, Ordering::Relaxed));
            rt.block_on(fulfill(&lease, &inst)).expect("fulfill");
        }
        let mut samples = Vec::with_capacity(seq_iters);
        for _ in 0..seq_iters {
            let inst = format!("seq-{}", ctr.fetch_add(1, Ordering::Relaxed));
            let t = Instant::now();
            rt.block_on(fulfill(&lease, &inst)).expect("fulfill");
            samples.push(t.elapsed());
        }
        samples.sort();
        let n = samples.len();
        let mean: Duration = samples.iter().sum::<Duration>() / n as u32;
        println!(
            "  fulfill() sequential                    n={:<4} mean={:>9}  p50={:>9}  p95={:>9}  ~{:.0} leases/s (1 at a time)",
            n,
            fmt(mean),
            fmt(samples[n / 2]),
            fmt(samples[(n as f64 * 0.95) as usize % n]),
            1.0 / mean.as_secs_f64(),
        );
    }

    // --- concurrent fulfillment throughput (WIDE) ---
    println!("\n  -- WIDE: N concurrent fulfill() (leases/sec vs concurrency) --");
    let per_task = env_usize("BENCH_WIDE_ITERS", 100);
    let ns: Vec<usize> = std::env::var("BENCH_WIDE_N")
        .ok()
        .map(|s| s.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![1, 2, 4, 8, 16]);
    let mut baseline = 0.0f64;
    let lease = Arc::new(lease);
    for (i, &n) in ns.iter().enumerate() {
        let ctr = Arc::new(AtomicU64::new(0));
        let t = Instant::now();
        rt.block_on(async {
            let mut handles = Vec::new();
            for _ in 0..n {
                let lease = lease.clone();
                let ctr = ctr.clone();
                handles.push(tokio::spawn(async move {
                    for _ in 0..per_task {
                        let id = ctr.fetch_add(1, Ordering::Relaxed);
                        let inst = format!("conc-{n}-{id}");
                        fulfill(&lease, &inst).await.expect("fulfill");
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
