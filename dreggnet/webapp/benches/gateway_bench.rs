//! Gateway / webapp characterization: requests/sec through the router. Three
//! paths:
//!   1. `Router::serve` — the non-durable data plane (match -> polyana handler ->
//!      render). The raw request-routing + handler-exec floor.
//!   2. `LeasedRouter::serve` — the metered durable data plane: gate the lease
//!      budget, then run the handler THROUGH a one-step durable workflow.
//!   3. the `402` over-budget fast path — a request refused before any handler
//!      runs (the admission-control cost).
//!
//! Plus a WIDE sweep: N concurrent threads serving the durable path against one
//! shared LeasedRouter (the shared meter mutex is the contention point).
//!
//! Hand-rolled `harness = false` bench (no criterion; offline).
//! Run:  `cargo bench -p dreggnet-webapp --bench gateway_bench`

use std::sync::Arc;
use std::time::{Duration, Instant};

use dreggnet_bridge::{CapGrade, Lease};
use dreggnet_webapp::assemble::demo_app;
use dreggnet_webapp::http::WebRequest;
use dreggnet_webapp::router::{LeasedRouter, Router};

fn fmt(d: Duration) -> String {
    let us = d.as_secs_f64() * 1e6;
    if us >= 1000.0 {
        format!("{:.2}ms", us / 1000.0)
    } else {
        format!("{:.1}us", us)
    }
}

fn env_usize(key: &str, default: usize) -> usize {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn bench<F: FnMut()>(label: &str, iters: usize, warmup: usize, mut f: F) {
    for _ in 0..warmup {
        f();
    }
    let mut s = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        f();
        s.push(t.elapsed());
    }
    s.sort();
    let n = s.len().max(1);
    let mean: Duration = s.iter().sum::<Duration>() / n as u32;
    println!(
        "  {:<42} n={:<5} mean={:>9}  p50={:>9}  p95={:>9}  ~{:.0} req/s (1 thread)",
        label,
        iters,
        fmt(mean),
        fmt(s[n / 2]),
        fmt(s[(n as f64 * 0.95) as usize % n]),
        1.0 / mean.as_secs_f64(),
    );
}

fn main() {
    println!("\n=== DreggNet gateway / webapp (router) characterization ===");
    println!("    a served GET /add?a=40&b=2 -> polyana wasm handler -> rendered response\n");

    let req = WebRequest::get("/add?a=40&b=2");

    // --- 1. plain Router (non-durable data plane) ---
    let router = Router::new(demo_app("bench"));
    bench(
        "Router::serve (non-durable)",
        env_usize("BENCH_ITERS", 2000),
        50,
        || {
            let r = router.serve(&req);
            assert_eq!(r.status, 200);
        },
    );

    // --- 2. LeasedRouter (durable, metered) ---
    // Big budget, cost 1/req, so the gate always passes.
    let lease = Lease::funded("bench", CapGrade::Sandboxed, "USD", 1_000_000_000, 1);
    let leased = LeasedRouter::new(demo_app("bench"), lease).expect("leased router");
    bench(
        "LeasedRouter::serve (durable+metered)",
        env_usize("BENCH_DURABLE_ITERS", 500),
        20,
        || {
            let (r, _m) = leased.serve(&req);
            assert_eq!(r.status, 200);
        },
    );

    // --- 3. the 402 over-budget fast path ---
    // budget 0, cost 1: the first request is refused before any handler runs.
    let broke = Lease::funded("bench", CapGrade::Sandboxed, "USD", 0, 1);
    let leased_broke = LeasedRouter::new(demo_app("bench"), broke).expect("router");
    bench(
        "LeasedRouter::serve 402 (over-budget)",
        200_000,
        100,
        || {
            let (r, _m) = leased_broke.serve(&req);
            assert_eq!(r.status, 402);
        },
    );

    // --- 4. a 404 (unmatched, not charged) ---
    let miss = WebRequest::get("/nope");
    bench("LeasedRouter::serve 404 (no route)", 200_000, 100, || {
        let (r, _m) = leased.serve(&miss);
        assert_eq!(r.status, 404);
    });

    // ---- WIDE: N threads against one shared LeasedRouter (durable path) ----
    println!("\n=== WIDE: N concurrent threads, shared LeasedRouter durable path ===");
    println!("    req/sec vs threads — the shared meter Mutex is the contention point\n");
    let per_thread = env_usize("BENCH_WIDE_ITERS", 300);
    let ns: Vec<usize> = std::env::var("BENCH_WIDE_N")
        .ok()
        .map(|s| s.split(',').filter_map(|x| x.trim().parse().ok()).collect())
        .unwrap_or_else(|| {
            let cores = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(8);
            vec![1, 2, 4, cores]
        });
    let mut baseline = 0.0f64;
    for (i, &n) in ns.iter().enumerate() {
        // A fresh huge-budget router per N so the meter never runs out across the run.
        let lease = Lease::funded("bench", CapGrade::Sandboxed, "USD", i64::MAX, 1);
        let leased = Arc::new(LeasedRouter::new(demo_app("bench"), lease).expect("router"));
        let t = Instant::now();
        let handles: Vec<_> = (0..n)
            .map(|_| {
                let leased = leased.clone();
                let req = req.clone();
                std::thread::spawn(move || {
                    for _ in 0..per_thread {
                        let (r, _m) = leased.serve(&req);
                        assert_eq!(r.status, 200);
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }
        let e = t.elapsed();
        let tput = (n * per_thread) as f64 / e.as_secs_f64();
        if i == 0 {
            baseline = tput;
        }
        println!(
            "    N={:<3} {:>6} req in {:>7.3}s  =>  {:>8.0} req/s   ({:.2}x vs N=1)",
            n,
            n * per_thread,
            e.as_secs_f64(),
            tput,
            if baseline > 0.0 { tput / baseline } else { 0.0 },
        );
    }
    println!();
}
