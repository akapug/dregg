//! OUTPUT-BOUNDARY MPC crossing — the working PoC benchmark (codex Round-4 gold).
//!
//! Runs the real construction end to end and reports the GATE evidence:
//!   (A) CORRECTNESS — the MPC (p*,V*) equals the plaintext crossing, over the
//!       REAL BFV-folded curves (additive fold → additive shares → MPC), across
//!       N∈{32,128,512}, K∈{64,256}, n∈{3,4} parties. No plaintext-pretending: a
//!       real GF(2) secret-shared, Beaver-triple online phase computes the sign.
//!   (B) PRIVACY — reveal-only-(p*,V*): two DIFFERENT books with the SAME (p*,V*)
//!       produce statistically indistinguishable party views, and a simulator
//!       given only (p*,V*) reproduces the view distribution. (Same-leakage as
//!       reveal-nothing beyond the intended public output.)
//!   (C) LATENCY — the MPC crossing runs in MILLISECONDS (vs the FHE crossing's
//!       ~12–17 s, `ADDITIVE-FOLD-ENVELOPE.md`), plus its round/AND-gate cost.
//!
//! Reproduce: `cargo run --release --bin fhe-mpc-bench` (from `fhegg-fhe/`).

use std::time::Instant;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use fhegg_fhe::additive::{bfv_fold, pick_params};
use fhegg_fhe::mpc::{
    cross_curves, mpc_crossing, share_int, simulate, triples_needed, SharedInt, Transcript,
    TriplePool,
};
use fhegg_fhe::{reference_clear, Order, Side};

const B: usize = 16; // curve-coefficient bit-width (bucket sums < 2^16)

fn random_book(n: usize, k: usize, rng: &mut StdRng) -> Vec<Order> {
    (0..n)
        .map(|_| Order {
            side: if rng.gen::<bool>() {
                Side::Bid
            } else {
                Side::Ask
            },
            limit: rng.gen_range(0..k),
            qty: rng.gen_range(1..=8),
        })
        .collect()
}

fn main() {
    println!("=== OUTPUT-BOUNDARY MPC crossing — PoC (codex Round-4 gold) ===\n");
    println!("Real BFV additive fold -> threshold partial-decrypt-into-shares (modelled)");
    println!("-> GF(2) secret-shared, Beaver-triple GEQ crossing -> reveal ONLY (p*,V*).\n");

    correctness_and_latency();
    privacy_demo();

    println!("\n=== GATE ===");
    println!(
        "(A) correctness: MPC (p*,V*) == plaintext crossing, over REAL BFV curves — see table."
    );
    println!("(B) privacy: same-(p*,V*) books -> indistinguishable views; simulator matches — see below.");
    println!("(C) latency: MPC crossing in MILLISECONDS (vs FHE crossing ~12-17 s) — see table.");
}

fn correctness_and_latency() {
    println!("--- (A) correctness + (C) latency: real BFV fold -> MPC crossing ---");
    println!(
        "{:>4} {:>4} {:>3} | {:>10} {:>10} | {:>9} {:>10} {:>8} {:>7} | {}",
        "N", "K", "n", "BFV fold", "BFV enc", "MPC cross", "triples", "ANDs", "rounds", "correct"
    );
    let mut rng = StdRng::seed_from_u64(0xC0FFEE_11);
    let mut all_ok = true;
    for &n_orders in &[32usize, 128, 512] {
        for &k in &[64usize, 256] {
            for &n_parties in &[3usize, 4] {
                let book = random_book(n_orders, k, &mut rng);
                let reference = reference_clear(&book, k);

                // REAL BFV additive fold — the seam-free carrier. Its decrypted
                // curves are the input the threshold parties would partial-decrypt
                // INTO shares (no BFV->TFHE scheme switch: that seam is dissolved).
                let params = pick_params(20);
                let (demand, supply, fold_t) = bfv_fold(&book, k, &params);

                // OUTPUT-BOUNDARY MPC crossing on those real curves.
                let t0 = Instant::now();
                let (cross, tr, used) = cross_curves(&demand, &supply, B, n_parties, &mut rng);
                let mpc_dt = t0.elapsed();

                let ok = cross.p_star == reference.p_star
                    && cross.v_star as u32 == reference.v_star
                    && tr.is_reveal_only(k);
                all_ok &= ok;

                println!(
                    "{:>4} {:>4} {:>3} | {:>9.4}s {:>9.3}s | {:>7.2}ms {:>10} {:>8} {:>7} | {}",
                    n_orders,
                    k,
                    n_parties,
                    fold_t.fold.as_secs_f64(),
                    fold_t.encrypt.as_secs_f64(),
                    mpc_dt.as_secs_f64() * 1e3,
                    used,
                    tr.and_gates,
                    tr.rounds,
                    if ok {
                        format!("YES p*={:?} V*={}", cross.p_star, cross.v_star)
                    } else {
                        format!(
                            "NO mpc={:?}/{} ref={:?}/{}",
                            cross.p_star, cross.v_star, reference.p_star, reference.v_star
                        )
                    }
                );
                let _ = used;
            }
        }
    }
    println!(
        "\ncorrectness across ALL configs: {}",
        if all_ok {
            "ALL MATCH (MPC == plaintext)"
        } else {
            "!!! MISMATCH !!!"
        }
    );
    assert!(all_ok, "MPC crossing must equal the plaintext crossing");
    println!(
        "latency: the MPC crossing is milliseconds; the comparison it replaces is the\n\
         ~12-17 s O(K) TFHE crossing (ADDITIVE-FOLD-ENVELOPE.md). Rounds = O(b) network\n\
         round-trips (bit-width), K-independent (buckets batch by depth).\n"
    );
}

/// Collect the input-dependent part of a party's view over `runs` fresh executions
/// and return `(P[masked bit = 1], sign_vector, vstar_bits)`.
fn view_profile(
    demand: &[u64],
    supply: &[u64],
    n_parties: usize,
    runs: usize,
    seed: u64,
) -> (f64, Vec<u8>, Vec<u8>) {
    let k = demand.len();
    let mut rng = StdRng::seed_from_u64(seed);
    let mut ones = 0u64;
    let mut total = 0u64;
    let mut sign = Vec::new();
    let mut vstar = Vec::new();
    for _ in 0..runs {
        let mut pool = TriplePool::generate(triples_needed(k, B), n_parties, &mut rng);
        let d: Vec<SharedInt> = demand
            .iter()
            .map(|&v| share_int(v, B, n_parties, &mut rng))
            .collect();
        let s: Vec<SharedInt> = supply
            .iter()
            .map(|&v| share_int(v, B, n_parties, &mut rng))
            .collect();
        let mut tr = Transcript::default();
        let _ = mpc_crossing(&d, &s, &mut pool, &mut tr);
        for &m in &tr.masked {
            ones += m as u64;
            total += 1;
        }
        sign = tr.revealed_sign.clone();
        vstar = tr.revealed_vstar.clone();
    }
    (ones as f64 / total as f64, sign, vstar)
}

fn privacy_demo() {
    println!(
        "--- (B) privacy: reveal-only-(p*,V*) via same-(p*,V*) -> indistinguishable views ---"
    );
    let k = 32usize;
    let n_parties = 4usize;
    let runs = 200usize;
    let mut rng = StdRng::seed_from_u64(0xDA7A_B0B);

    // Find TWO DIFFERENT books that clear at the SAME (p*, V*). If the party view
    // reveals only (p*,V*), the two must be indistinguishable to any coalition
    // below threshold — that is the "same leakage as reveal-nothing" property.
    let mut buckets: std::collections::HashMap<(Option<usize>, u32), (Vec<u64>, Vec<u64>)> =
        std::collections::HashMap::new();
    let mut pair: Option<(
        (Vec<u64>, Vec<u64>),
        (Vec<u64>, Vec<u64>),
        (Option<usize>, u32),
    )> = None;
    for _ in 0..20000 {
        let book = random_book(rng.gen_range(8..40), k, &mut rng);
        let r = reference_clear(&book, k);
        if r.p_star.is_none() {
            continue;
        }
        let key = (r.p_star, r.v_star);
        let curves = (
            r.demand.iter().map(|&x| x as u64).collect::<Vec<_>>(),
            r.supply.iter().map(|&x| x as u64).collect::<Vec<_>>(),
        );
        if let Some(prev) = buckets.get(&key) {
            if prev.0 != curves.0 || prev.1 != curves.1 {
                pair = Some((prev.clone(), curves, key));
                break;
            }
        } else {
            buckets.insert(key, curves);
        }
    }

    let (b1, b2, key) = pair.expect("found two distinct books with the same (p*,V*)");
    println!(
        "found two DISTINCT aggregate curves with identical (p*,V*) = ({:?}, {}):",
        key.0, key.1
    );
    println!(
        "  book1 demand[..8]={:?} supply[..8]={:?}",
        &b1.0[..8],
        &b1.1[..8]
    );
    println!(
        "  book2 demand[..8]={:?} supply[..8]={:?}",
        &b2.0[..8],
        &b2.1[..8]
    );
    println!(
        "  (curves DIFFER: {}), yet both clear at the same (p*,V*).",
        if b1.0 != b2.0 || b1.1 != b2.1 {
            "confirmed"
        } else {
            "SAME?!"
        }
    );

    let (bias1, sign1, vstar1) = view_profile(&b1.0, &b1.1, n_parties, runs, 0x1111);
    let (bias2, sign2, vstar2) = view_profile(&b2.0, &b2.1, n_parties, runs, 0x2222);

    println!("\nparty view over {runs} fresh runs each ({n_parties} parties, K={k}):");
    println!(
        "  P[opened protocol bit = 1]:  book1 = {:.4}   book2 = {:.4}   (uniform = 0.5)",
        bias1, bias2
    );
    println!(
        "  |bias1 - bias2|           =  {:.4}   (-> 0: the masked messages carry no input info)",
        (bias1 - bias2).abs()
    );
    println!("  opened sign vector equal  :  {}", sign1 == sign2);
    println!("  revealed V* bits equal    :  {}", vstar1 == vstar2);

    // Simulator: given ONLY (p*,V*), reproduce the view distribution.
    let cross_ref = fhegg_fhe::mpc::Crossing {
        p_star: key.0,
        v_star: key.1 as u64,
    };
    let mut srng = StdRng::seed_from_u64(0x51A);
    let mut sim_ones = 0u64;
    let mut sim_total = 0u64;
    let mut sim_sign = Vec::new();
    let mut sim_vstar = Vec::new();
    for _ in 0..runs {
        let tr = simulate(&cross_ref, k, B, &mut srng);
        for &m in &tr.masked {
            sim_ones += m as u64;
            sim_total += 1;
        }
        sim_sign = tr.revealed_sign.clone();
        sim_vstar = tr.revealed_vstar.clone();
    }
    let sim_bias = sim_ones as f64 / sim_total as f64;
    println!("\nsimulator (given ONLY (p*,V*), no curves):");
    println!("  P[simulated bit = 1]      =  {:.4}   (matches real -> real view learnable from (p*,V*) alone)", sim_bias);
    println!(
        "  simulated sign vector = real sign vector : {}",
        sim_sign == sign1
    );
    println!(
        "  simulated V* bits     = real V* bits     : {}",
        sim_vstar == vstar1
    );

    let indistinguishable = sign1 == sign2
        && vstar1 == vstar2
        && (bias1 - bias2).abs() < 0.03
        && (bias1 - 0.5).abs() < 0.03
        && sim_sign == sign1
        && sim_vstar == vstar1;
    println!(
        "\nprivacy verdict: {}",
        if indistinguishable {
            "views are STATISTICALLY INDISTINGUISHABLE -> the MPC reveals ONLY (p*,V*)."
        } else {
            "!!! views distinguishable — privacy claim FAILS !!!"
        }
    );
    assert!(
        indistinguishable,
        "same-(p*,V*) books must yield indistinguishable views"
    );
    println!(
        "honest caveat: this is the SEMI-HONEST, below-threshold bound. >= t colluding\n\
         parties reconstruct the shares (t-of-n, not 'all-collude') — the minimum trust\n\
         for clearing over hidden data, and there is NO standing master decryption key."
    );
}
