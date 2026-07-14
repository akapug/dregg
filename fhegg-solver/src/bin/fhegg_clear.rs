//! # `fhegg_clear` — the fhEgg single-phase SHIELDED clearing as a thin JSON CLI (the web wire)
//!
//! ```text
//! echo '<orders-json>' | fhegg_clear
//! ```
//!
//! This is the fhEgg engine's **single-phase clearing** driven by the SAME revealed DrEX orders
//! `drex_clear` reads, but cleared through the CONVEX / CERTIFICATE route rather than the TTC ring
//! matcher:
//!
//!   1. map the batch to a trade-circulation LP: nodes = assets, one capacitated weighted edge per
//!      order `(offerAsset → wantAsset)`, `cap = offerAmount`, `weight = priority` — a member of the
//!      fhEgg convex-clearing family (`fhegg_solver::pdhg`, the volume-max circulation `max wᵀf s.t.
//!      Af=0, 0≤f≤c`);
//!   2. **fast UNTRUSTED search**: `solve_cpu` (PDHG) → `restore_feasibility` — the solver sees the
//!      plaintext batch and clears it MAXIMALLY FAST;
//!   3. emit the **Cert-F primal-dual certificate** `(f, π, s)` (`fhegg_solver::cert::CertF`) — the
//!      LINEAR witness that makes the untrusted solve trustworthy;
//!   4. emit + EVALUATE the Cert-F **AIR** (`fhegg_solver::air::ConstraintSystem` — the exact
//!      `n+4m+1` rows the Lean-verified `Market/CertF.lean` proves sound): the honest certificate is
//!      ACCEPTED; a tampered one (broken conservation) is REJECTED. This is the VERIFIED checker —
//!      the fair-batch gate, in code.
//!
//! Output (stdout): the cleared batch — per-order cleared flow read off the certified circulation,
//! the Cert-F report (cleared weighted volume `wᵀf`, dual `cᵀs`, duality gap, conservation residual,
//! every check), the AIR accept + the tamper reject, and the two clearing tiers (solver-sees vs
//! world-sees-only-the-proof).
//!
//! ## The single-phase SHIELDED boundary — what is REAL here and what is NAMED
//!
//! Everything above is REAL and runs in this binary: the fair-batch clearing, the Cert-F certificate,
//! and the verified AIR accept/reject (the fairness/soundness gate). What this binary does NOT run is
//! the STARK-ZK wrap that HIDES `(f, π, s)` so the world sees only the proof — that is
//! `circuit-prove/src/cert_f_air.rs::{from_solution_json, prove_cert_f, verify_cert_f}` (a dregg
//! BabyBear+FRI proof over this SAME AIR; the reveal-nothing floor rests on its zero-knowledge). This
//! CLI emits the exact `(f, π, s)` + public `(A, w, c)` that `from_solution_json` ingests, so the
//! wire to the real STARK is a call away — see `stark_stage` in the output. Shown honestly: in THIS
//! demo the certificate is in the clear; the shielded wrap is named, not run.

use std::collections::BTreeMap;
use std::io::Read;

use fhegg_solver::air::ConstraintSystem;
use fhegg_solver::cert::CertF;
use fhegg_solver::pdhg::{restore_feasibility, solve_cpu, FlowLp};

use serde::{Deserialize, Serialize};

/// One revealed order as posted by the web app (same shape as `drex_clear`).
#[derive(Deserialize)]
struct OrderIn {
    trader: String,
    #[serde(rename = "offerAsset")]
    offer_asset: String,
    #[serde(rename = "offerAmount")]
    offer_amount: u64,
    #[serde(rename = "wantAsset")]
    want_asset: String,
    #[serde(rename = "wantMin")]
    want_min: u64,
    #[serde(default)]
    priority: u64,
}

#[derive(Serialize)]
struct ClearedOrder {
    trader: String,
    #[serde(rename = "offerAsset")]
    offer_asset: String,
    #[serde(rename = "offerAmount")]
    offer_amount: u64,
    #[serde(rename = "wantAsset")]
    want_asset: String,
    #[serde(rename = "wantMin")]
    want_min: u64,
    priority: u64,
    /// The cleared quantity of this order read off the certified circulation `f`.
    #[serde(rename = "clearedFlow")]
    cleared_flow: f64,
    /// Cleared / rested (a rested order got ~0 flow — no ring closed through it).
    filled: bool,
}

#[derive(Serialize)]
struct CertReportOut {
    /// Cleared weighted volume `wᵀf` (the fair-batch objective).
    #[serde(rename = "clearedVolume")]
    cleared_volume: f64,
    /// Dual objective `cᵀs`.
    #[serde(rename = "dualObjective")]
    dual_objective: f64,
    /// Duality gap `cᵀs − wᵀf` (optimality slack).
    #[serde(rename = "dualityGap")]
    duality_gap: f64,
    /// Conservation residual `‖Af‖_∞` (per-asset supply preserved).
    #[serde(rename = "conservationResidual")]
    conservation_residual: f64,
    conserves: bool,
    #[serde(rename = "primalBoxed")]
    primal_boxed: bool,
    #[serde(rename = "sNonneg")]
    s_nonneg: bool,
    #[serde(rename = "dualFeasible")]
    dual_feasible: bool,
    #[serde(rename = "gapOk")]
    gap_ok: bool,
    valid: bool,
}

#[derive(Serialize)]
struct AirOut {
    constraints: usize,
    terms: usize,
    #[serde(rename = "witnessCells")]
    witness_cells: usize,
    accept: bool,
    violated: Vec<String>,
}

#[derive(Serialize)]
struct TamperOut {
    what: String,
    accept: bool,
    violated: Vec<String>,
}

#[derive(Serialize)]
struct StarkStage {
    status: String,
    #[serde(rename = "revealNothingFloor")]
    reveal_nothing_floor: String,
    #[serde(rename = "wireEntryPoint")]
    wire_entry_point: String,
    hides: Vec<String>,
}

#[derive(Serialize)]
struct Tier {
    tier: String,
    sees: String,
}

#[derive(Serialize)]
struct Cleared {
    engine: String,
    mechanism: String,
    assets: Vec<String>,
    nodes: usize,
    edges: usize,
    iters: usize,
    orders: Vec<ClearedOrder>,
    certificate: CertReportOut,
    air: AirOut,
    tamper: TamperOut,
    #[serde(rename = "starkStage")]
    stark_stage: StarkStage,
    tiers: Vec<Tier>,
    /// The RAW Cert-F certificate `(n_nodes, edges, w, c, f, π, s, ε)` — the exact f64 wire
    /// shape `circuit-prove/src/cert_f_air.rs::from_solution_json` ingests. This is the
    /// SOLVER's plaintext view; it carries the private witness `(f, π, s)`, so it is the
    /// bridge input to the reveal-nothing STARK (`cert_f_prove`) and must NOT be forwarded
    /// to the world — the STARK's public output replaces it. `serve.mjs` holds it server-side
    /// and pipes it to the prover; the world sees only the resulting proof + public inputs.
    #[serde(rename = "solverCert")]
    solver_cert: CertF,
}

fn main() {
    let mut buf = String::new();
    if std::io::stdin().read_to_string(&mut buf).is_err() {
        eprintln!("fhegg_clear: failed to read stdin");
        std::process::exit(2);
    }
    let orders: Vec<OrderIn> = match serde_json::from_str(&buf) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("fhegg_clear: bad orders JSON: {e}");
            std::process::exit(2);
        }
    };
    if orders.is_empty() {
        eprintln!("fhegg_clear: empty batch");
        std::process::exit(2);
    }

    // ---- [1] map the batch to the trade-circulation LP (assets = nodes, orders = edges). ----
    // Node index per asset symbol, assigned in first-seen order.
    let mut asset_idx: BTreeMap<String, u32> = BTreeMap::new();
    let mut assets: Vec<String> = Vec::new();
    let idx_of =
        |sym: &str, asset_idx: &mut BTreeMap<String, u32>, assets: &mut Vec<String>| -> u32 {
            if let Some(&i) = asset_idx.get(sym) {
                i
            } else {
                let i = assets.len() as u32;
                asset_idx.insert(sym.to_string(), i);
                assets.push(sym.to_string());
                i
            }
        };

    let mut edges: Vec<(u32, u32)> = Vec::with_capacity(orders.len());
    let mut w: Vec<f64> = Vec::with_capacity(orders.len());
    let mut c: Vec<f64> = Vec::with_capacity(orders.len());
    for o in &orders {
        // An order OFFERS `offerAsset` to OBTAIN `wantAsset`: value releases at the
        // want node and lands at the offer node as the ring circulates, so the edge runs
        // wantAsset → offerAsset. Conservation `Af=0` at each asset node is exactly DrEX
        // per-asset conservation (what flows out as offers equals what flows in as wants).
        let tail = idx_of(&o.want_asset, &mut asset_idx, &mut assets);
        let head = idx_of(&o.offer_asset, &mut asset_idx, &mut assets);
        edges.push((tail, head));
        c.push(o.offer_amount.max(1) as f64);
        // Weight = priority (gains-from-trade proxy); default 1.0 so every order can clear.
        w.push(if o.priority == 0 {
            1.0
        } else {
            o.priority as f64
        });
    }
    let lp = FlowLp {
        n_nodes: assets.len(),
        edges,
        w,
        c,
    };

    // ---- [2] fast UNTRUSTED search: PDHG → exact-feasibility restore. ----
    let iters = 4000usize;
    let approx = solve_cpu(&lp, iters);
    let (f_exact, _box_viol) = restore_feasibility(&lp, approx.f.clone());

    // ---- [3] the Cert-F primal-dual certificate (f, π, s) + public (A, w, c). ----
    // epsilon: the optimality tolerance the certificate is claimed against.
    let epsilon = 0.5f64;
    let cert = CertF::from_solution(&lp, &f_exact, &approx.y, epsilon);
    let report = cert.check_strict();

    // ---- [4] emit + evaluate the Cert-F AIR (the verified fair-batch gate). ----
    let tol = 1e-7;
    let sys = ConstraintSystem::emit(&cert);
    let air_report = sys.evaluate(&cert, tol);
    let n_terms: usize = sys.constraints.iter().map(|cx| cx.terms.len()).sum();

    // Negative polarity: break conservation on one edge — the AIR must REJECT.
    let mut tampered = cert.clone();
    if !tampered.f.is_empty() {
        tampered.f[0] += 3.0;
    }
    let tamper_report = sys.evaluate(&tampered, tol);

    // Per-order cleared flow (rested if ~0).
    let cleared_orders: Vec<ClearedOrder> = orders
        .iter()
        .enumerate()
        .map(|(e, o)| {
            let flow = *f_exact.get(e).unwrap_or(&0.0);
            ClearedOrder {
                trader: o.trader.clone(),
                offer_asset: o.offer_asset.clone(),
                offer_amount: o.offer_amount,
                want_asset: o.want_asset.clone(),
                want_min: o.want_min,
                priority: if o.priority == 0 { 1 } else { o.priority },
                cleared_flow: (flow * 1e6).round() / 1e6,
                filled: flow > 1e-6,
            }
        })
        .collect();

    let out = Cleared {
        engine: "fhEgg single-phase clearing (fhegg-solver: PDHG circulation + Cert-F)".to_string(),
        mechanism: "volume-max trade circulation  max wᵀf  s.t. Af=0, 0≤f≤c  (the convex clearing family; uniform-price is its linear-utility floor)".to_string(),
        assets: assets.clone(),
        nodes: lp.n_nodes,
        edges: lp.m(),
        iters,
        orders: cleared_orders,
        certificate: CertReportOut {
            cleared_volume: (cert.primal_obj * 1e6).round() / 1e6,
            dual_objective: (cert.dual_obj * 1e6).round() / 1e6,
            duality_gap: (cert.duality_gap * 1e6).round() / 1e6,
            conservation_residual: cert.feas_residual,
            conserves: report.conserves,
            primal_boxed: report.primal_boxed,
            s_nonneg: report.s_nonneg,
            dual_feasible: report.dual_feasible,
            gap_ok: report.gap_ok,
            valid: report.valid,
        },
        air: AirOut {
            constraints: sys.constraints.len(),
            terms: n_terms,
            witness_cells: sys.n_vars,
            accept: air_report.satisfied(),
            violated: air_report
                .violated
                .iter()
                .map(|(l, _)| l.to_string())
                .collect(),
        },
        tamper: TamperOut {
            what: "break conservation: add 3 units to edge 0 with no return leg (Af≠0)".to_string(),
            accept: tamper_report.satisfied(),
            violated: tamper_report
                .violated
                .iter()
                .map(|(l, _)| l.to_string())
                .collect(),
        },
        stark_stage: StarkStage {
            status: "NAMED, not run in this demo".to_string(),
            reveal_nothing_floor:
                "the world sees only a STARK over this SAME AIR; the reveal-nothing floor rests on its zero-knowledge"
                    .to_string(),
            wire_entry_point:
                "circuit-prove/src/cert_f_air.rs::{from_solution_json → prove_cert_f → verify_cert_f}"
                    .to_string(),
            hides: vec![
                "f (the primal flow — who cleared how much)".to_string(),
                "π (the node potentials / dual prices)".to_string(),
                "s (the dual slacks)".to_string(),
            ],
        },
        tiers: vec![
            Tier {
                tier: "solver-sees (Stage-1, untrusted)".to_string(),
                sees: "the plaintext batch — every order, to clear it maximally fast".to_string(),
            },
            Tier {
                tier: "world-sees (the shielded output)".to_string(),
                sees: "only the proof: a fair batch cleared, per-asset conservation held — never who traded what (once the STARK stage is wired)".to_string(),
            },
        ],
        solver_cert: cert,
    };

    match serde_json::to_string(&out) {
        Ok(s) => println!("{s}"),
        Err(e) => {
            eprintln!("fhegg_clear: serialize failed: {e}");
            std::process::exit(1);
        }
    }
}
