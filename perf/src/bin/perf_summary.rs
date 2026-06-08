//! Standalone turn-proof performance summary — prints a table of real
//! prove/verify wall-clock times for the production `prove_effect_vm_p3` path.
//!
//! Run: `cargo run --release -p dregg-perf --bin perf-summary`
//!
//! Unlike the criterion bench, this is a single-shot report meant to be pasted
//! into the product assessment. It warms once, then times a few iterations and
//! reports the mean, so the numbers are reproducible without the full criterion
//! harness.

use std::time::Instant;

use dregg_circuit::effect_vm_p3_full_air::{prove_effect_vm_p3, verify_effect_vm_p3};
use dregg_perf::{build_trace, workloads};

fn fmt(secs: f64) -> String {
    if secs < 1e-3 {
        format!("{:.1} us", secs * 1e6)
    } else if secs < 1.0 {
        format!("{:.1} ms", secs * 1e3)
    } else {
        format!("{:.3} s", secs)
    }
}

fn main() {
    println!(
        "{:<20} {:>6} {:>12} {:>12}",
        "workload", "effs", "prove (mean)", "verify (mean)"
    );
    println!("{}", "-".repeat(54));

    for w in workloads() {
        let (trace, pis) = build_trace(&w);

        // Warm + correctness gate.
        let proof = prove_effect_vm_p3(&trace, &pis).expect("honest turn must prove");
        verify_effect_vm_p3(&proof, &pis).expect("honest proof must verify");

        let prove_iters = 5u32;
        let t0 = Instant::now();
        for _ in 0..prove_iters {
            let p = prove_effect_vm_p3(&trace, &pis).expect("prove");
            std::hint::black_box(&p);
        }
        let prove_mean = t0.elapsed().as_secs_f64() / prove_iters as f64;

        let verify_iters = 50u32;
        let t1 = Instant::now();
        for _ in 0..verify_iters {
            verify_effect_vm_p3(&proof, &pis).expect("verify");
        }
        let verify_mean = t1.elapsed().as_secs_f64() / verify_iters as f64;

        println!(
            "{:<20} {:>6} {:>12} {:>12}",
            w.name,
            w.effects.len(),
            fmt(prove_mean),
            fmt(verify_mean)
        );
    }
}
