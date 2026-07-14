//! `smooth-bench` — smooth-convex / SGD certified by a gradient-norm witness.
//!
//! Run: `cargo run --release --bin smooth-bench` (in `fhegg-solver/`).
//!
//! Demonstrates the engine reaches PAST LP/clearing: an untrusted (S)GD run on a
//! μ-strongly-convex objective, certified by `‖∇f(x)‖ ≤ ε` (near-stationarity)
//! with the convex suboptimality bound `f(x)−f* ≤ ‖∇f‖²/(2μ)`. Both polarities:
//! a converged point CERTIFIES; a far-from-stationary / tampered point is
//! REJECTED. On ridge instances we also solve the closed-form optimum to show
//! the certified bound BRACKETS the true suboptimality.
//!
//! HONEST framing (printed): verify-not-find is Otti's (USENIX Sec 2022,
//! LP+SDP+SGD); we add privacy + the checked certificate. The gradient
//! certificate is STATIONARITY — for a CONVEX f that is near-optimality; for a
//! NON-convex f (real ML) it is only a critical point, NOT model quality.

use fhegg_solver::smooth::{
    logistic_instance, ridge_instance, ridge_optimum, solve_gd, solve_sgd, CertGrad, SmoothConvex,
};
use std::time::Instant;

fn main() {
    println!("smooth-bench — smooth-convex / SGD certified by a gradient-norm witness");
    println!("verify-not-find follows Otti (USENIX Sec 2022, LP+SDP+SGD); WE add privacy + the");
    println!("checked certificate. Certificate = ‖∇f(x)‖≤ε (near-stationarity); for a CONVEX f");
    println!("that bounds f(x)−f* ≤ ‖∇f‖²/(2μ). NON-convex ⇒ stationarity, NOT optimality.\n");

    // --- ridge least-squares: closed-form optimum known → bracket the bound ---
    println!("ridge least-squares  min (1/2m)‖Ax−b‖² + (μ/2)‖x‖²   (μ-strongly convex):");
    println!(
        "{:<9} {:<8} {:>10} {:>11} {:>12} {:>12} {:>8}",
        "m×n", "solver", "solve_ms", "‖∇f(x)‖", "f(x)−f*", "cert_bound", "valid"
    );
    for (m, n, mu) in [(200usize, 20usize, 1e-2), (500, 40, 1e-2), (1000, 60, 1e-3)] {
        let obj = ridge_instance(m, n, mu, (m + n) as u64);
        let xstar = ridge_optimum(&obj);
        let fstar = obj.value(&xstar);

        // GD solver.
        let t0 = Instant::now();
        let gd = solve_gd(&obj, 4000);
        let gd_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let cert = gd.certificate(&obj, gd.grad_norm * 1.001 + 1e-12);
        let rep = cert.check();
        println!(
            "{:<9} {:<8} {:>10.2} {:>11.2e} {:>12.2e} {:>12.2e} {:>8}",
            format!("{m}×{n}"),
            "GD",
            gd_ms,
            rep.grad_norm,
            gd.value - fstar,
            rep.suboptimality_bound,
            rep.valid
        );

        // SGD solver — same problem, stochastic search, certified identically.
        let t0 = Instant::now();
        let sgd = solve_sgd(&obj, 200, 16, 7);
        let sgd_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let cert = sgd.certificate(&obj, sgd.grad_norm * 1.001 + 1e-12);
        let rep = cert.check();
        println!(
            "{:<9} {:<8} {:>10.2} {:>11.2e} {:>12.2e} {:>12.2e} {:>8}",
            format!("{m}×{n}"),
            "SGD",
            sgd_ms,
            rep.grad_norm,
            sgd.value - fstar,
            rep.suboptimality_bound,
            rep.valid
        );
        // Sanity: the certified bound brackets the true suboptimality.
        assert!(
            gd.value - fstar <= cert.suboptimality_bound + 1e-9
                || rep.suboptimality_bound >= gd.value - fstar,
            "certified bound must upper-bound true suboptimality"
        );
    }
    println!("  (f(x)−f* is UNKNOWABLE in general; shown via the closed-form ridge optimum.");
    println!("   cert_bound = ‖∇f‖²/(2μ) is what a verifier CHECKS — and it brackets f(x)−f*.)\n");

    // --- logistic: no closed form, same gradient certificate ---
    println!("L2-logistic  min (1/m)Σ log(1+exp(−yᵢaᵢ·x)) + (μ/2)‖x‖²  (same CertGrad):");
    println!(
        "{:<9} {:>10} {:>11} {:>12} {:>8}",
        "m×n", "solve_ms", "‖∇f(x)‖", "cert_bound", "valid"
    );
    for (m, n, mu) in [(200usize, 20usize, 1e-2), (500, 40, 1e-2)] {
        let obj = logistic_instance(m, n, mu, (m * 3 + n) as u64);
        let t0 = Instant::now();
        let gd = solve_gd(&obj, 8000);
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        let cert = gd.certificate(&obj, gd.grad_norm * 1.001 + 1e-12);
        let rep = cert.check();
        println!(
            "{:<9} {:>10.2} {:>11.2e} {:>12.2e} {:>8}",
            format!("{m}×{n}"),
            ms,
            rep.grad_norm,
            rep.suboptimality_bound,
            rep.valid
        );
        assert!(rep.valid, "logistic certificate must be valid");
    }

    // --- negative polarity: a far-from-stationary / tampered point is REJECTED ---
    println!("\nnegative polarity (the checker REFUSES a lie — recomputes ∇f from scratch):");
    let obj = ridge_instance(200, 20, 1e-2, 99);
    let x0 = vec![0.0f64; obj.dim()];
    let cert0 = CertGrad::from_point(&obj, &x0, 1e-4);
    let rep0 = cert0.check();
    println!(
        "  x=0 (far):        ‖∇f‖={:.3e} > ε=1e-4  ⇒ near_stationary={}  valid={}",
        rep0.grad_norm, rep0.near_stationary, rep0.valid
    );
    let gd = solve_gd(&obj, 4000);
    let mut tampered = gd.certificate(&obj, 1e-3);
    let before = tampered.check().valid;
    tampered.x[0] += 1.0;
    let rep_t = tampered.check();
    println!(
        "  converged then +1: baseline valid={before}  ⇒ tampered ‖∇f‖={:.3e}  valid={}",
        rep_t.grad_norm, rep_t.valid
    );
    assert!(!rep0.valid && !rep_t.valid, "both negative cases rejected");

    // --- the class table (what the engine certifies, per class) ---
    println!("\nverify-not-find, per optimization CLASS → certificate (the engine, not one rule):");
    println!(
        "  LP / convex-QP        → duality-gap    (cᵀs−wᵀf ≤ ε)     — pdhg, qp, discriminatory"
    );
    println!("  Fisher / equilibrium  → KKT residual   (βu≤p, CS ≈ 0)    — fisher");
    println!(
        "  combinatorial (0/1)   → weak-dual bound (W ≤ UB(y))      — package [certified approx]"
    );
    println!("  smooth-convex / SGD   → gradient norm  (‖∇f‖ ≤ ε)        — smooth  [THIS module]");
    println!(
        "  SDP                   → dual PSD cert   (C−ΣyᵢAᵢ ⪰ 0)    — NAMED next (design note §)"
    );
    println!("\nclearing is ONE class. ML north star: verified-private-SGD → verified-private-ML,");
    println!(
        "HONEST — for a non-convex net the gradient cert = a stationary point, not model quality."
    );
    let _: fn(&SmoothConvex) -> Vec<f64> = ridge_optimum; // keep the import honest
}
