//! Standalone turn-proof performance summary — prints a table of real
//! prove/verify wall-clock times for the production self-sovereign turn path
//! (`prove_turn_self_sovereign` / `verify_full_turn`). Under the `recursion`
//! default the EffectVM leg proves through the rotated IR-v2 descriptor tower.
//!
//! Run: `cargo run --release -p dregg-perf --bin perf-summary`
//!
//! Unlike the criterion bench, this is a single-shot report meant to be pasted
//! into the product assessment. It warms once, then times a few iterations and
//! reports the mean, so the numbers are reproducible without the full criterion
//! harness.

use std::time::Instant;

use dregg_circuit::effect_vm::pi;
use dregg_perf::{build_trace, workloads};
use dregg_sdk::{prove_turn_self_sovereign, verify_full_turn};

const TURN_HASH: [u8; 32] = [7u8; 32];

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
        let (_trace, pis) = build_trace(&w);
        let old_commit = pis[pi::OLD_COMMIT];
        let new_commit = pis[pi::NEW_COMMIT];

        // Warm + correctness gate.
        let proof = prove_turn_self_sovereign(&w.initial, &w.effects, TURN_HASH)
            .expect("honest turn must prove");
        verify_full_turn(&proof, old_commit, new_commit).expect("honest proof must verify");

        let prove_iters = 5u32;
        let t0 = Instant::now();
        for _ in 0..prove_iters {
            let p = prove_turn_self_sovereign(&w.initial, &w.effects, TURN_HASH).expect("prove");
            std::hint::black_box(&p);
        }
        let prove_mean = t0.elapsed().as_secs_f64() / prove_iters as f64;

        let verify_iters = 50u32;
        let t1 = Instant::now();
        for _ in 0..verify_iters {
            verify_full_turn(&proof, old_commit, new_commit).expect("verify");
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
