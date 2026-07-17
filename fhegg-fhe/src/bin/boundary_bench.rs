//! MASKED DECRYPT-TO-SHARES — the end-to-end Tier-0 pipeline bench (closes the
//! §8 "partial-decrypt-into-shares" frontier item of OUTPUT-BOUNDARY-MPC.md).
//!
//! Runs the FULL output-boundary pipeline with no un-modelled value-channel step:
//!
//!   BFV carry-free fold  →  homomorphic Z_t masking (each party adds Enc(r_i))
//!   →  decrypt ONLY the one-time-padded value  →  local mod-t shares
//!   →  a2b_mod_t bridge  →  the unchanged Beaver-triple crossing  →  (p*, V*)
//!
//! For every (N,K,n) it checks the result EXACTLY equals the plaintext
//! `reference_clear` — correctness preserved, no silent drift. The headline is
//! the "aggregate-ready → p*-ready" number (fold + mask + decrypt + a2b +
//! crossing), the metric FHEGG-CODEX-ROUND4.md §Q2 names as the decisive one.

use std::time::Instant;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::boundary::masked_boundary_clear;
use fhegg_fhe::{reference_clear, Order, Side};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// Same book generator as additive_bench, so numbers compose across envelopes.
fn gen_orders(n: usize, k: usize, rng: &mut StdRng) -> Vec<Order> {
    let qmax: u16 = if n >= 512 { 32 } else { 100 };
    (0..n)
        .map(|i| {
            let side = if i % 2 == 0 { Side::Bid } else { Side::Ask };
            Order {
                side,
                limit: rng.gen_range(0..k),
                qty: rng.gen_range(1..=qmax),
            }
        })
        .collect()
}

fn main() {
    println!("=== MASKED DECRYPT-TO-SHARES — the full output-boundary pipeline, measured ===\n");
    println!("BFV fold -> homomorphic Z_t masks -> decrypt ONLY the padded value -> mod-t shares");
    println!("-> a2b_mod_t -> unchanged Beaver crossing -> reveal ONLY (p*,V*).");
    println!("Every row checked EXACTLY equal to the plaintext reference. Real BFV (fhe.rs), real MPC.\n");

    let params = pick_params(20);
    println!(
        "BFV: degree {} plaintext_modulus t={} (128-bit)\n",
        params.degree(),
        params.plaintext()
    );

    let configs = [
        (32usize, 64usize, 3usize),
        (128, 64, 4),
        (512, 64, 3),
        (128, 256, 4),
    ];

    println!(
        "{:>4} {:>4} {:>2} | {:>8} {:>8} {:>8} {:>8} {:>9} {:>9} | {:>10} {:>7} | {}",
        "N",
        "K",
        "n",
        "fold",
        "mask",
        "decrypt",
        "a2b",
        "crossing",
        "AGG->p*",
        "triples",
        "rounds",
        "result"
    );

    let mut all_ok = true;
    for &(n_orders, k, n_parties) in &configs {
        let mut rng = StdRng::seed_from_u64(0xB0DA_2026 ^ ((n_orders as u64) << 24) ^ (k as u64));
        let book = gen_orders(n_orders, k, &mut rng);
        let reference = reference_clear(&book, k);

        let t0 = Instant::now();
        let run = masked_boundary_clear(&book, k, 16, n_parties, &params, &mut rng);
        let _total = t0.elapsed();

        // "aggregate ciphertext ready -> proof-bindable p* ready": everything
        // AFTER the fold's output exists (mask + decrypt + a2b + crossing).
        let agg_to_pstar = run.mask + run.decrypt + run.a2b + run.crossing;

        let ok =
            run.cross.p_star == reference.p_star && run.cross.v_star as u32 == reference.v_star;
        all_ok &= ok;

        println!(
            "{:>4} {:>4} {:>2} | {:>7.4}s {:>7.4}s {:>7.4}s {:>7.4}s {:>8.2}ms {:>8.4}s | {:>10} {:>7} | {} p*={:?} V*={}",
            n_orders,
            k,
            n_parties,
            run.fold.as_secs_f64(),
            run.mask.as_secs_f64(),
            run.decrypt.as_secs_f64(),
            run.a2b.as_secs_f64(),
            run.crossing.as_secs_f64() * 1e3,
            agg_to_pstar.as_secs_f64(),
            run.triples_used,
            run.transcript.rounds,
            if ok { "OK " } else { "MISMATCH!" },
            run.cross.p_star,
            run.cross.v_star,
        );
    }
    assert!(
        all_ok,
        "masked-boundary pipeline must equal the plaintext reference"
    );

    println!(
        "\nheadline: AGG->p* is the R4 decisive metric (aggregate-ready -> p*-ready). The value\n\
         channel now has NO modelled step: the only decryption in the pipeline opens a one-time-\n\
         padded value (exact pad, enumeration-proven in boundary::tests). Contrast: the pure-FHE\n\
         crossing this path replaces is ~12-17 s (TFHE, ADDITIVE-FOLD-ENVELOPE.md) plus an\n\
         un-built BFV->TFHE scheme-switch. Rounds = network round-trips in deployment;\n\
         a2b depth is K-independent (slots convert in parallel).\n"
    );
    println!("=== done ===");
}
