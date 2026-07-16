//! Benchmark: the injection leg on the plonky3 IR-v2 descriptor prover (`prove_injection_leg`).
//!
//! Run: `cargo run -p dregg-zkoracle-prove --release --example bench_injection_leg`
//!
//! The 1KB field → 1024 trace rows; the 8KB field → 8192 rows.
//!
//! 2026-07-16: this was a BEFORE/AFTER bench — legacy hand-STARK (`dregg_circuit::stark` via
//! `dsl::dfa_routing::prove_dfa_routing`, O(n²)) vs the descriptor prover. The stark-kill
//! campaign DELETED that legacy engine, so there is no BEFORE left to time and the import no
//! longer resolves (it was the last `cargo check --all-targets` error in the workspace). The
//! migration this bench measured is done; what remains is the AFTER anchor.

use std::time::Instant;

use dregg_zkoracle_prove::zk_leg::{prove_injection_leg, verify_injection_leg};

/// A benign (injection-free) field of exactly `n` bytes: a repeated sentence, no `{{`.
fn benign_field(n: usize) -> Vec<u8> {
    let seed = b"The capital of France is Paris. ";
    let mut v = Vec::with_capacity(n);
    while v.len() < n {
        v.push(seed[v.len() % seed.len()]);
    }
    v.truncate(n);
    v
}

fn main() {
    println!("== injection-leg prover benchmark (plonky3 IR-v2 descriptor prover) ==\n");

    for &kb in &[1usize, 8usize] {
        let n = kb * 1024;
        let field = benign_field(n);
        let rows = n.next_power_of_two().max(2);
        println!("--- {kb}KB field ({n} bytes → {rows} trace rows) ---");

        let t = Instant::now();
        let leg = prove_injection_leg(&field).expect("prove (descriptor)");
        let elapsed = t.elapsed();
        verify_injection_leg(&field, &leg).expect("verify (descriptor)");
        let proof_kb = leg.proof_bytes.len() as f64 / 1024.0;
        println!("  descriptor prover: {elapsed:?}  [proof {proof_kb:.1} KiB, verified OK]");
        println!();
    }
}
