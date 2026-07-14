//! fhEgg Stage-1 END-TO-END demo — the fast-search → checked-certificate pipeline.
//!
//! The native-eval end-to-end milestone, run as one crisp pipeline with timing and
//! BOTH polarities:
//!
//!   1. solve a real batch (PDHG on a real trade-graph circulation LP, timed);
//!   2. restore exact feasibility (spanning-forest residual routing);
//!   3. emit the Cert-F primal-dual certificate `(f, π, s)` + public `(A, w, c)`;
//!   4. emit the Cert-F check as the AIR `ConstraintSystem` (`air.rs`) — the SAME
//!      `n + 4m + 1` linear rows the Lean-verified `Market/CertF.lean` proves sound;
//!   5. EVALUATE the emitted AIR against the certificate → ACCEPT (positive polarity);
//!   6. TAMPER the certificate three ways (break conservation, over-cap, inflate gap)
//!      → the emitted AIR REJECTS each (negative polarity — soundness in code).
//!
//! This is Stage-1 wired end-to-end at the native-eval level: the untrusted PDHG
//! search produces a certificate; the AIR the STARK ingests (and the Lean checker
//! proves sound) is what DECIDES accept/reject — never the T solver iterations.
//!
//! The REAL STARK (a dregg BabyBear+FRI proof over this same AIR, hiding `(f,π,s)`)
//! is `circuit-prove/src/cert_f_air.rs`'s `prove_cert_f`; run its tests for that.
//!
//! Usage: `cargo run --release --bin fhegg-e2e`

use fhegg_solver::air::ConstraintSystem;
use fhegg_solver::cert::CertF;
use fhegg_solver::clearing::{allocate, clear, Order, Side};
use fhegg_solver::pdhg::{restore_feasibility, solve_cpu, FlowLp};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::time::Instant;

/// A random connected directed trade graph with a nontrivial circulation:
/// a Hamiltonian cycle (guarantees a feasible circulation) plus random chords.
fn gen_graph(n_nodes: usize, extra_edges: usize, seed: u64) -> FlowLp {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut edges: Vec<(u32, u32)> = (0..n_nodes)
        .map(|i| (i as u32, ((i + 1) % n_nodes) as u32))
        .collect();
    for _ in 0..extra_edges {
        let a = rng.gen_range(0..n_nodes) as u32;
        let mut b = rng.gen_range(0..n_nodes) as u32;
        if a == b {
            b = (b + 1) % n_nodes as u32;
        }
        edges.push((a, b));
    }
    let m = edges.len();
    let w: Vec<f64> = (0..m).map(|_| rng.gen_range(0.5..2.0)).collect();
    let c: Vec<f64> = (0..m).map(|_| rng.gen_range(1.0..10.0)).collect();
    FlowLp {
        n_nodes: n_nodes,
        edges,
        w,
        c,
    }
}

fn report(label: &str, sys: &ConstraintSystem, cert: &CertF, tol: f64) -> bool {
    let air = sys.evaluate(cert, tol);
    let check = cert.check_strict();
    let ok = air.satisfied();
    println!(
        "    {label:<28} AIR accept={:<5} (checker.valid={:<5})  {}",
        ok,
        check.valid,
        if air.satisfied() {
            "— accepted".to_string()
        } else {
            format!(
                "— REJECTED by [{}]",
                air.violated
                    .iter()
                    .map(|(l, _)| *l)
                    .collect::<Vec<_>>()
                    .join(", ")
                    .chars()
                    .take(60)
                    .collect::<String>()
            )
        }
    );
    // AIR and the Rust checker must always agree.
    assert_eq!(
        ok, check.valid,
        "AIR emission and CertF::check must agree on {label}"
    );
    ok
}

fn main() {
    println!("fhEgg Stage-1 END-TO-END: fast search → checked certificate (native-eval)\n");

    // ---- A real batch: aggregation clearing (fhEgg T=1), shown as context. ----
    println!("=== [0] a real uniform-price batch clears (fhEgg T=1 aggregation) ===");
    let mut rng = StdRng::seed_from_u64(0xC0FFEE);
    let k = 256usize;
    let orders: Vec<Order> = (0..5000)
        .map(|_| {
            let side = if rng.gen_bool(0.5) {
                Side::Bid
            } else {
                Side::Ask
            };
            let qty = rng.gen_range(1..100u64);
            let limit = match side {
                Side::Bid => rng.gen_range(k / 3..k) as u32,
                Side::Ask => rng.gen_range(0..(2 * k) / 3) as u32,
            };
            Order { side, qty, limit }
        })
        .collect();
    let t0 = Instant::now();
    let cleared = clear(&orders, k);
    let alloc = allocate(&orders, &cleared);
    let clear_us = t0.elapsed().as_secs_f64() * 1e6;
    println!(
        "    N={} orders, K={k} levels: cleared V*={} at price index {}, conserves={} ({clear_us:.1} µs)\n",
        orders.len(),
        cleared.cleared_volume,
        cleared.clearing_price,
        alloc.conserves()
    );

    // ---- The convex core: PDHG solve → certificate → AIR check. ----
    println!("=== [1] fast UNTRUSTED search: PDHG on a real circulation LP ===");
    let n = 256usize;
    let m_target = 4096usize;
    let lp = gen_graph(n, m_target - n, 0xBEEF);
    let iters = 4000usize;

    let t0 = Instant::now();
    let approx = solve_cpu(&lp, iters);
    let solve_ms = t0.elapsed().as_secs_f64() * 1e3;

    let t0 = Instant::now();
    let (f_exact, box_viol) = restore_feasibility(&lp, approx.f.clone());
    let restore_us = t0.elapsed().as_secs_f64() * 1e6;

    println!(
        "    graph: {} nodes, {} edges, T={iters} iters",
        lp.n_nodes,
        lp.m()
    );
    println!(
        "    PDHG solve:            {solve_ms:>8.2} ms   (gap {:.2e}, ‖Af‖ before {:.2e})",
        approx.duality_gap, approx.feas_residual
    );
    println!("    feasibility restore:   {restore_us:>8.2} µs   (box violation {box_viol:.1e})\n");

    println!("=== [2] emit the Cert-F certificate (f, π, s) + public (A, w, c) ===");
    let t0 = Instant::now();
    let cert = CertF::from_solution(&lp, &f_exact, &approx.y, 0.5);
    let cert_us = t0.elapsed().as_secs_f64() * 1e6;
    println!(
        "    wᵀf (cleared volume) = {:.4},  cᵀs (dual) = {:.4},  gap = {:.3e}",
        cert.primal_obj, cert.dual_obj, cert.duality_gap
    );
    println!(
        "    ‖Af‖_∞ after restore = {:.3e}   (certificate built in {cert_us:.1} µs)\n",
        cert.feas_residual
    );

    println!("=== [3] emit the Cert-F AIR (the STARK/Lean bridge, air.rs) ===");
    let t0 = Instant::now();
    let sys = ConstraintSystem::emit(&cert);
    let emit_us = t0.elapsed().as_secs_f64() * 1e6;
    let n_terms: usize = sys.constraints.iter().map(|c| c.terms.len()).sum();
    println!(
        "    {} constraints, {n_terms} terms over {} witness cells  (n+4m+1 = {}; O(m+nnz A))",
        sys.constraints.len(),
        sys.n_vars,
        lp.n_nodes + 4 * lp.m() + 1
    );
    println!(
        "    rows: conservation(==0) · box_lower/upper(≥0) · slack_sign(≥0) · dual_feas(≥0) · duality_gap(≤ε)   ({emit_us:.1} µs)\n"
    );

    println!("=== [4] EVALUATE the AIR against the certificate (accept/reject) ===");
    let tol = 1e-7;

    // Positive polarity: the honest certificate is ACCEPTED.
    println!("  positive polarity (the honest solver output):");
    let t0 = Instant::now();
    let accepted = report("honest certificate", &sys, &cert, tol);
    let eval_us = t0.elapsed().as_secs_f64() * 1e6;
    assert!(accepted, "the honest certificate MUST be accepted");
    println!("    (AIR evaluation: {eval_us:.1} µs)\n");

    // Negative polarity: three independent tampers, each REJECTED.
    println!("  negative polarity (tampered / non-optimal / non-conserving — must REJECT):");

    // (a) break conservation: add flow to one edge with no return leg.
    let mut tam_cons = cert.clone();
    tam_cons.f[0] += 3.0;
    let r_a = report("break conservation (Af≠0)", &sys, &tam_cons, tol);

    // (b) over-capacity: push one edge above its cap (box violation).
    let mut tam_box = cert.clone();
    let e = (0..lp.m())
        .max_by(|&a, &b| cert.c[a].partial_cmp(&cert.c[b]).unwrap())
        .unwrap();
    tam_box.f[e] = cert.c[e] + 5.0;
    let r_b = report("over-capacity (f>c)", &sys, &tam_box, tol);

    // (c) inflate the primal objective without earning it: claim a larger wᵀf so the
    //     reported gap is negative (violates weak duality / the gap ≤ ε row upward is
    //     fine, but a fabricated better-than-dual flow breaks conservation+box). To hit
    //     the GAP row specifically, zero the flow (feasible, but far from optimal):
    let mut tam_gap = cert.clone();
    for fe in tam_gap.f.iter_mut() {
        *fe = 0.0;
    }
    // zero flow conserves + is boxed; its gap = cᵀs − 0 = cᵀs ≫ ε ⇒ the gap row bites.
    let recomputed = CertF::from_solution(&lp, &tam_gap.f, &tam_gap.pi, cert.epsilon);
    let r_c = report("sub-optimal (gap>ε)", &sys, &recomputed, tol);

    assert!(!r_a && !r_b && !r_c, "every tamper MUST be rejected");

    println!("\n=== VERDICT ===");
    println!("  native-eval end-to-end WIRED: PDHG search → Cert-F certificate → Cert-F AIR");
    println!(
        "  (the {}-row linear system Market/CertF.lean proves sound) → verify.",
        sys.constraints.len()
    );
    println!("  positive polarity ACCEPTED · all three negative polarities REJECTED.");
    println!("  the AIR decides on the CERTIFICATE, never the T={iters} search iterations.");
    println!("\n  Tier-1 posture: solver-sees-plaintext, PRIVATE-FROM-THE-WORLD, PQ.");
    println!("  the real STARK (BabyBear+FRI, hiding (f,π,s)) = circuit-prove/src/cert_f_air.rs.");
}
