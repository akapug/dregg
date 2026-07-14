//! CFMM optimal routing — route one trade through parallel constant-function
//! market makers (`PRIVATE-CONVEX-ENGINE.md` §3, Angeris–Chitra convex-CFMM;
//! `FHEGG-PRODUCT-ORDER-FRONTIER.md` R2.3 "CFMM routing convex until fixed venue
//! costs"). Public pool curves, private trade amounts — a Tier-1 mechanism.
//!
//! ## The convex program
//!
//! Split a fixed input `Δ` of token X across `N` constant-product pools to
//! maximise the total output of token Y. Pool `i` has reserves `(Rᵢ, Qᵢ)` and fee
//! factor `γ ∈ (0,1]`; sending `δᵢ` of X returns
//!
//! ```text
//!   gᵢ(δᵢ) = Qᵢ·γδᵢ / (Rᵢ + γδᵢ)          (constant-product xy=k output, concave↑)
//! ```
//!
//! and the router solves the CONCAVE maximisation
//!
//! ```text
//!   maximize   Σᵢ gᵢ(δᵢ)      subject to   Σᵢ δᵢ ≤ Δ,   δᵢ ≥ 0.
//! ```
//!
//! Each `gᵢ` is increasing and concave, so this is a convex program over the box +
//! budget simplex — the "projection onto the public reachable set" the doc names.
//!
//! ## The solver — water-filling on the marginal price (fixed-`T`, oblivious)
//!
//! At the optimum every ACTIVE pool has the same marginal output
//! `gᵢ'(δᵢ) = λ` (the dual of the budget), and inactive pools have a lower
//! marginal at `δᵢ = 0`. `gᵢ'(δ) = QᵢγRᵢ/(Rᵢ+γδ)²` is strictly decreasing, so it
//! inverts in closed form: `δᵢ(λ) = max(0, (√(QᵢγRᵢ/λ) − Rᵢ)/γ)`. `Σᵢ δᵢ(λ)` is
//! decreasing in `λ`; a fixed number of bisection steps on `λ` drives the spend to
//! `Δ` — a data-independent iteration (oblivious). The pool curves `(Rᵢ,Qᵢ,γ)` are
//! PUBLIC; only `Δ` and the routing `δ` are private.
//!
//! ## The certificate (`CertRoute`) — the routing KKT witness
//!
//! A pair `(δ, λ)` is certified optimal by the KKT of the concave program:
//!
//! ```text
//!   δ ≥ 0,   Σᵢ δᵢ ≤ Δ,   λ ≥ 0                       (primal / dual feasibility)
//!   gᵢ'(δᵢ) ≤ λ                          ∀ i           (no pool beats the margin)
//!   Σᵢ δᵢ (λ − gᵢ'(δᵢ)) = 0                            (complementary slackness)
//!   λ (Δ − Σᵢ δᵢ) = 0                                  (budget slackness)
//! ```
//!
//! The check is `O(N)` but NONLINEAR in the witness (`gᵢ'` is rational in `δᵢ`) —
//! so it is a Tier-1 certificate, not the affine Cert-F AIR (the honest note: the
//! CFMM invariant is a nonlinear public curve). Verify-not-find holds: the KKT
//! residual decides, independent of the bisection that found `(δ, λ)`.

use serde::Serialize;

/// One constant-product pool `(reserve_in, reserve_out, fee)` — PUBLIC curve.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Pool {
    /// Reserve of the input token `Rᵢ`.
    pub reserve_in: f64,
    /// Reserve of the output token `Qᵢ`.
    pub reserve_out: f64,
    /// Fee factor `γ ∈ (0,1]` (e.g. 0.997 for a 30bps pool).
    pub fee: f64,
}

impl Pool {
    /// Output `gᵢ(δ) = Qγδ/(R+γδ)` for input `δ`.
    #[inline]
    pub fn output(&self, delta: f64) -> f64 {
        if delta <= 0.0 {
            return 0.0;
        }
        let gd = self.fee * delta;
        self.reserve_out * gd / (self.reserve_in + gd)
    }

    /// Marginal output `gᵢ'(δ) = QγR/(R+γδ)²` (decreasing in `δ`). At `δ=0` this
    /// is the spot marginal `Qγ/R`.
    #[inline]
    pub fn marginal(&self, delta: f64) -> f64 {
        let d = self.reserve_in + self.fee * delta;
        self.reserve_out * self.fee * self.reserve_in / (d * d)
    }

    /// The input that makes the marginal equal `λ`: `δ(λ)=(√(QγR/λ)−R)/γ`,
    /// clamped at 0 (a pool with spot marginal `< λ` gets nothing).
    #[inline]
    fn input_for_marginal(&self, lambda: f64) -> f64 {
        if lambda <= 0.0 {
            return f64::INFINITY;
        }
        let root = (self.reserve_out * self.fee * self.reserve_in / lambda).sqrt();
        ((root - self.reserve_in) / self.fee).max(0.0)
    }
}

/// A routing instance: the pools + the fixed input budget `Δ`.
#[derive(Clone, Debug)]
pub struct RoutingProblem {
    pub pools: Vec<Pool>,
    pub budget: f64,
}

/// The solver output: the routing `δ`, the marginal price `λ`, the total output.
#[derive(Clone, Debug)]
pub struct RoutingResult {
    pub delta: Vec<f64>,
    pub lambda: f64,
    pub total_output: f64,
    pub spent: f64,
    pub iters: usize,
}

impl RoutingResult {
    pub fn certificate(&self, prob: &RoutingProblem, epsilon: f64) -> CertRoute {
        CertRoute::from_solution(prob, &self.delta, self.lambda, epsilon)
    }
}

/// Solve the routing program by bisection on the marginal price `λ` (fixed `T`).
pub fn solve_waterfill(prob: &RoutingProblem, iters: usize) -> RoutingResult {
    // The highest spot marginal is the upper bound on λ (above it nothing routes);
    // λ = 0 lower bound (everything routes, oversatisfying the budget).
    let mut lo = 0.0f64;
    let mut hi = prob
        .pools
        .iter()
        .map(|p| p.marginal(0.0))
        .fold(0.0f64, f64::max)
        .max(1e-12);

    let spend_at = |lambda: f64| -> f64 {
        prob.pools
            .iter()
            .map(|p| p.input_for_marginal(lambda).min(prob.budget))
            .sum::<f64>()
    };

    // If routing everything still cannot spend Δ (degenerate), λ→0 and the budget
    // slackness holds with λ=0. Otherwise bisect to Σδ(λ)=Δ.
    for _ in 0..iters {
        let mid = 0.5 * (lo + hi);
        if spend_at(mid) > prob.budget {
            lo = mid; // too much spend → raise λ
        } else {
            hi = mid; // too little spend → lower λ
        }
    }
    let lambda = 0.5 * (lo + hi);

    let mut delta: Vec<f64> = prob
        .pools
        .iter()
        .map(|p| p.input_for_marginal(lambda))
        .collect();
    // Numerically clip the tiny bisection residual so the budget is respected
    // exactly (Σδ ≤ Δ); the excess is at most the bisection tolerance.
    let spent: f64 = delta.iter().sum();
    if spent > prob.budget && spent > 0.0 {
        let scale = prob.budget / spent;
        for d in &mut delta {
            *d *= scale;
        }
    }
    let spent: f64 = delta.iter().sum();
    let total_output: f64 = prob
        .pools
        .iter()
        .zip(&delta)
        .map(|(p, &d)| p.output(d))
        .sum();

    RoutingResult {
        delta,
        lambda,
        total_output,
        spent,
        iters,
    }
}

/// The CFMM routing certificate (public pools + `(δ, λ)` witness).
#[derive(Clone, Debug, Serialize)]
pub struct CertRoute {
    pub pools: Vec<Pool>,
    pub budget: f64,
    pub delta: Vec<f64>,
    pub lambda: f64,
    pub epsilon: f64,
    pub total_output: f64,
}

/// The routing KKT check report.
#[derive(Clone, Debug, Serialize)]
pub struct CertRouteReport {
    /// `δ ≥ 0`.
    pub delta_nonneg: bool,
    /// `Σδ ≤ Δ`.
    pub budget_feasible: bool,
    /// `λ ≥ 0`.
    pub lambda_nonneg: bool,
    /// `gᵢ'(δᵢ) ≤ λ` for every pool.
    pub marginals_bounded: bool,
    /// Routing complementary slackness `Σ δᵢ(λ − gᵢ'(δᵢ)) ≈ 0`.
    pub routing_cs: f64,
    /// Budget slackness `λ(Δ − Σδ) ≈ 0`.
    pub budget_cs: f64,
    pub tol: f64,
    pub valid: bool,
}

impl CertRoute {
    pub fn from_solution(prob: &RoutingProblem, delta: &[f64], lambda: f64, epsilon: f64) -> Self {
        let total_output: f64 = prob
            .pools
            .iter()
            .zip(delta)
            .map(|(p, &d)| p.output(d))
            .sum();
        CertRoute {
            pools: prob.pools.clone(),
            budget: prob.budget,
            delta: delta.to_vec(),
            lambda,
            epsilon,
            total_output,
        }
    }

    /// Validate the routing KKT at slack `tol` (recomputed from the public pools +
    /// `(δ, λ)` — the checker trusts nothing stored).
    pub fn check_with(&self, tol: f64) -> CertRouteReport {
        let delta_nonneg = self.delta.iter().all(|&d| d >= -tol);
        let spent: f64 = self.delta.iter().sum();
        let budget_feasible = spent <= self.budget + tol;
        let lambda_nonneg = self.lambda >= -tol;

        let mut marginals_bounded = true;
        let mut routing_cs = 0.0f64;
        for (p, &d) in self.pools.iter().zip(&self.delta) {
            let gp = p.marginal(d);
            if gp > self.lambda + tol {
                marginals_bounded = false;
            }
            routing_cs += d.max(0.0) * (self.lambda - gp).abs();
        }
        let budget_cs = (self.lambda * (self.budget - spent)).abs();

        let cs_ok = routing_cs <= tol && budget_cs <= tol;
        let valid = delta_nonneg && budget_feasible && lambda_nonneg && marginals_bounded && cs_ok;
        CertRouteReport {
            delta_nonneg,
            budget_feasible,
            lambda_nonneg,
            marginals_bounded,
            routing_cs,
            budget_cs,
            tol,
            valid,
        }
    }

    /// `check_with` at a tolerance scaled to the budget (the routing/CS residuals
    /// are in input-token units).
    pub fn check(&self) -> CertRouteReport {
        self.check_with(self.epsilon * self.budget.max(1.0))
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

/// A deterministic sample of `n` pools with varied depth/price and a 30bps fee.
pub fn sample_pools(n: usize) -> Vec<Pool> {
    (0..n)
        .map(|i| Pool {
            reserve_in: 1000.0 * (1.0 + i as f64 * 0.5),
            reserve_out: 1000.0 * (1.0 + ((i + 2) % 4) as f64 * 0.4),
            fee: 0.997,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn routing_certifies_and_spends_budget() {
        let prob = RoutingProblem {
            pools: sample_pools(4),
            budget: 500.0,
        };
        let res = solve_waterfill(&prob, 100);
        let cert = res.certificate(&prob, 1e-6);
        let rep = cert.check();
        assert!(rep.delta_nonneg, "δ ≥ 0");
        assert!(rep.budget_feasible, "Σδ ≤ Δ");
        assert!(rep.marginals_bounded, "g'ᵢ ≤ λ");
        assert!(rep.valid, "converged routing must certify: {rep:?}");
        assert!(
            (res.spent - prob.budget).abs() < 1e-3,
            "budget spent: {} of {}",
            res.spent,
            prob.budget
        );
    }

    #[test]
    fn routing_beats_any_single_pool() {
        // Splitting across pools must yield at least as much as dumping the whole
        // budget into the best single pool (concavity ⇒ diversification helps).
        let prob = RoutingProblem {
            pools: sample_pools(4),
            budget: 800.0,
        };
        let res = solve_waterfill(&prob, 100);
        let best_single = prob
            .pools
            .iter()
            .map(|p| p.output(prob.budget))
            .fold(0.0f64, f64::max);
        assert!(
            res.total_output >= best_single - 1e-6,
            "routed output {} must beat best single pool {}",
            res.total_output,
            best_single
        );
    }

    #[test]
    fn active_pools_share_the_marginal() {
        // Every pool that receives flow has marginal ≈ λ (water-filling KKT).
        let prob = RoutingProblem {
            pools: sample_pools(5),
            budget: 600.0,
        };
        let res = solve_waterfill(&prob, 120);
        for (p, &d) in prob.pools.iter().zip(&res.delta) {
            if d > 1e-3 {
                assert!(
                    (p.marginal(d) - res.lambda).abs() < 1e-3,
                    "active pool marginal {} vs λ {}",
                    p.marginal(d),
                    res.lambda
                );
            }
        }
    }

    #[test]
    fn tampered_routing_is_rejected() {
        // Move budget from a good pool into a worse one → KKT residual blows up.
        let prob = RoutingProblem {
            pools: sample_pools(4),
            budget: 500.0,
        };
        let res = solve_waterfill(&prob, 100);
        let mut cert = res.certificate(&prob, 1e-6);
        // Shift 100 units from pool with most flow to pool with least flow.
        let (imax, _) = cert
            .delta
            .iter()
            .enumerate()
            .fold(
                (0, f64::MIN),
                |(bi, bv), (i, &v)| {
                    if v > bv {
                        (i, v)
                    } else {
                        (bi, bv)
                    }
                },
            );
        let (imin, _) = cert
            .delta
            .iter()
            .enumerate()
            .fold(
                (0, f64::MAX),
                |(bi, bv), (i, &v)| {
                    if v < bv {
                        (i, v)
                    } else {
                        (bi, bv)
                    }
                },
            );
        let shift = 100.0f64.min(cert.delta[imax]);
        cert.delta[imax] -= shift;
        cert.delta[imin] += shift;
        assert!(
            !cert.check().valid,
            "suboptimal routing must be rejected: {:?}",
            cert.check()
        );
    }

    #[test]
    fn json_has_routing_shape() {
        let prob = RoutingProblem {
            pools: sample_pools(3),
            budget: 300.0,
        };
        let res = solve_waterfill(&prob, 80);
        let cert = res.certificate(&prob, 1e-6);
        let json = cert.to_json();
        assert!(json.contains("\"lambda\""));
        assert!(json.contains("\"total_output\""));
    }
}
