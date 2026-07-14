//! Eisenberg–Gale / Fisher-market welfare-max equilibrium — the GENERAL
//! competitive clearing (`PRIVATE-CONVEX-ENGINE.md` §3, "the *true generalization
//! of fhEgg*"). Uniform-price is the linear-utility, single-good special case;
//! this is the whole convex program.
//!
//! ## The convex program (Eisenberg–Gale, linear utilities)
//!
//! `n` buyers, each with budget `bᵢ`; `g` divisible goods, each with supply `sⱼ`;
//! buyer `i` values a unit of good `j` at `uᵢⱼ ≥ 0` (linear utility
//! `Uᵢ(xᵢ) = Σⱼ uᵢⱼ xᵢⱼ`). The Eisenberg–Gale program maximises the
//! **budget-weighted Nash welfare**:
//!
//! ```text
//!   maximize   Σᵢ bᵢ · log( Σⱼ uᵢⱼ xᵢⱼ )
//!   subject to Σᵢ xᵢⱼ ≤ sⱼ   (supply of each good)
//!              xᵢⱼ ≥ 0
//! ```
//!
//! Its optimum is a **competitive (Walrasian) equilibrium from the given budgets**:
//! there exist prices `pⱼ` (the DUALS of the supply constraints) under which every
//! buyer spends their whole budget on their best bang-per-buck goods and every
//! good with a positive price clears. This is the marquee mechanism — a `log`
//! (concave) objective, so it needs the entropic/mirror-descent prox, NOT the FHE
//! v0 affine aggregation core (hence Tier-1, not Tier-0).
//!
//! ## The solver — proportional response (an untrusted, oblivious first-order run)
//!
//! Proportional-response dynamics (Zhang 2011; Birnbaum–Devanur–Xiao): a buyer
//! splits their budget into bids `bᵢⱼ` across goods; prices are the total spend
//! `pⱼ = Σᵢ bᵢⱼ`; each buyer receives a share `xᵢⱼ = (bᵢⱼ/pⱼ)·sⱼ`; then re-bids in
//! proportion to the utility each good delivered, `bᵢⱼ ← bᵢ·(uᵢⱼ xᵢⱼ)/Uᵢ`. It is a
//! mirror-descent (entropic-prox) ascent on the EG objective and converges to the
//! equilibrium — a fixed-`T`, data-independent iteration (oblivious in the §0.1
//! sense). It is the UNTRUSTED search; the [`CertEq`] certificate is what decides.
//!
//! ## The certificate (`CertEq`) — the KKT / competitive-equilibrium witness
//!
//! A pair `(x, p)` is certified an equilibrium by the KKT conditions of EG. With
//! the derived per-buyer multiplier `βᵢ = bᵢ / Uᵢ` (inverse marginal utility of
//! money — the dual of buyer `i`'s budget), the checker validates:
//!
//! ```text
//!   x ≥ 0,   Σᵢ xᵢⱼ ≤ sⱼ,   p ≥ 0                     (primal / price feasibility)
//!   βᵢ uᵢⱼ ≤ pⱼ                            ∀ i,j        (stationarity: no good beats βᵢ)
//!   Σᵢⱼ xᵢⱼ (pⱼ − βᵢ uᵢⱼ) = 0                          (buyer complementary slackness)
//!   Σⱼ pⱼ (sⱼ − Σᵢ xᵢⱼ) = 0                            (market-clearing slackness)
//! ```
//!
//! Stationarity + buyer-CS give budget exhaustion `Σⱼ pⱼ xᵢⱼ = bᵢ` for free (so the
//! equilibrium is *from the given incomes*). The certificate is **bilinear** in the
//! witness (`βᵢ uᵢⱼ`, `xᵢⱼ pⱼ`), not linear like Cert-F — an `O(n·g)` check but not
//! the affine Cert-F AIR (the honest tier note: private/derived weights ⇒
//! bilinear-in-witness, still `O(n·g)` not `O(T·n·g)`, `FHEGG-PRODUCT-ORDER-FRONTIER`
//! precision-correction #2). Verify-not-find holds: how `(x,p)` were found is
//! irrelevant; the KKT residual decides.

use serde::Serialize;

/// A linear-utility Fisher market instance (the PUBLIC program form).
#[derive(Clone, Debug)]
pub struct FisherMarket {
    pub n_buyers: usize,
    pub n_goods: usize,
    /// Budget per buyer `bᵢ` (length `n_buyers`).
    pub budgets: Vec<f64>,
    /// Supply per good `sⱼ` (length `n_goods`).
    pub supplies: Vec<f64>,
    /// Utility coefficients `uᵢⱼ`, row-major `n_buyers × n_goods`.
    pub util: Vec<f64>,
}

impl FisherMarket {
    #[inline]
    pub fn u(&self, i: usize, j: usize) -> f64 {
        self.util[i * self.n_goods + j]
    }

    /// Buyer `i`'s realised utility `Uᵢ = Σⱼ uᵢⱼ xᵢⱼ` from allocation `x`.
    pub fn utility(&self, x: &[f64], i: usize) -> f64 {
        (0..self.n_goods)
            .map(|j| self.u(i, j) * x[i * self.n_goods + j])
            .sum()
    }
}

/// The solver output: the allocation `x`, equilibrium prices `p`, per-buyer
/// utilities, and the EG objective `Σ bᵢ log Uᵢ`.
#[derive(Clone, Debug)]
pub struct FisherResult {
    pub x: Vec<f64>,
    pub prices: Vec<f64>,
    pub utilities: Vec<f64>,
    pub eg_objective: f64,
    pub iters: usize,
}

impl FisherResult {
    pub fn certificate(&self, m: &FisherMarket, epsilon: f64) -> CertEq {
        CertEq::from_solution(m, &self.x, &self.prices, epsilon)
    }
}

/// Solve the EG program by proportional-response dynamics (fixed `T`, oblivious).
pub fn solve_proportional_response(m: &FisherMarket, iters: usize) -> FisherResult {
    let n = m.n_buyers;
    let g = m.n_goods;
    let eps = 1e-12;

    // Bids bᵢⱼ initialised to a uniform split of each budget over the goods the
    // buyer values (so no all-zero-utility good attracts spend it cannot use).
    let mut bid = vec![0.0f64; n * g];
    for i in 0..n {
        let valued: Vec<usize> = (0..g).filter(|&j| m.u(i, j) > 0.0).collect();
        let share = if valued.is_empty() {
            0.0
        } else {
            m.budgets[i] / valued.len() as f64
        };
        for &j in &valued {
            bid[i * g + j] = share;
        }
    }

    let mut prices = vec![0.0f64; g];
    let mut x = vec![0.0f64; n * g];

    for _ in 0..iters {
        // Prices = total spend per good.
        for j in 0..g {
            let mut acc = 0.0;
            for i in 0..n {
                acc += bid[i * g + j];
            }
            prices[j] = acc;
        }
        // Allocation xᵢⱼ = (bidᵢⱼ / pⱼ) · sⱼ.
        for j in 0..g {
            let pj = prices[j].max(eps);
            for i in 0..n {
                x[i * g + j] = bid[i * g + j] / pj * m.supplies[j];
            }
        }
        // Re-bid in proportion to delivered utility: bidᵢⱼ = bᵢ·(uᵢⱼ xᵢⱼ)/Uᵢ.
        for i in 0..n {
            let ui = m.utility(&x, i).max(eps);
            for j in 0..g {
                let contrib = m.u(i, j) * x[i * g + j];
                bid[i * g + j] = m.budgets[i] * contrib / ui;
            }
        }
    }

    // Final prices/allocation from the converged bids.
    for j in 0..g {
        let mut acc = 0.0;
        for i in 0..n {
            acc += bid[i * g + j];
        }
        prices[j] = acc;
    }
    for j in 0..g {
        let pj = prices[j].max(eps);
        for i in 0..n {
            x[i * g + j] = bid[i * g + j] / pj * m.supplies[j];
        }
    }
    let utilities: Vec<f64> = (0..n).map(|i| m.utility(&x, i)).collect();
    let eg_objective: f64 = (0..n)
        .map(|i| m.budgets[i] * utilities[i].max(eps).ln())
        .sum();

    FisherResult {
        x,
        prices,
        utilities,
        eg_objective,
        iters,
    }
}

/// The Fisher-market equilibrium certificate (public program + `(x, p)` witness).
/// The KKT / competitive-equilibrium analogue of [`crate::cert::CertF`].
#[derive(Clone, Debug, Serialize)]
pub struct CertEq {
    pub n_buyers: usize,
    pub n_goods: usize,
    pub budgets: Vec<f64>,
    pub supplies: Vec<f64>,
    pub util: Vec<f64>,
    pub x: Vec<f64>,
    pub prices: Vec<f64>,
    pub epsilon: f64,
    pub eg_objective: f64,
}

/// The report of the equilibrium KKT checks (mirrors what a Lean checker proves).
#[derive(Clone, Debug, Serialize)]
pub struct CertEqReport {
    /// `x ≥ 0`.
    pub alloc_nonneg: bool,
    /// `Σᵢ xᵢⱼ ≤ sⱼ` for every good.
    pub supply_feasible: bool,
    /// `p ≥ 0`.
    pub prices_nonneg: bool,
    /// `βᵢ uᵢⱼ ≤ pⱼ` for every buyer/good (no good beats the buyer's rate).
    pub stationary: bool,
    /// Buyer complementary slackness `Σ xᵢⱼ(pⱼ − βᵢuᵢⱼ) ≈ 0`.
    pub buyer_cs: f64,
    /// Market-clearing slackness `Σⱼ pⱼ(sⱼ − Σᵢ xᵢⱼ) ≈ 0`.
    pub clearing_cs: f64,
    /// Max budget-exhaustion residual `|Σⱼ pⱼ xᵢⱼ − bᵢ|` (derived, reported).
    pub budget_residual: f64,
    /// The tolerance used (scaled to the total budget).
    pub tol: f64,
    pub valid: bool,
}

impl CertEq {
    pub fn from_solution(m: &FisherMarket, x: &[f64], prices: &[f64], epsilon: f64) -> Self {
        let utilities: Vec<f64> = (0..m.n_buyers).map(|i| m.utility(x, i)).collect();
        let eg_objective: f64 = (0..m.n_buyers)
            .map(|i| m.budgets[i] * utilities[i].max(1e-12).ln())
            .sum();
        CertEq {
            n_buyers: m.n_buyers,
            n_goods: m.n_goods,
            budgets: m.budgets.clone(),
            supplies: m.supplies.clone(),
            util: m.util.clone(),
            x: x.to_vec(),
            prices: prices.to_vec(),
            epsilon,
            eg_objective,
        }
    }

    fn market(&self) -> FisherMarket {
        FisherMarket {
            n_buyers: self.n_buyers,
            n_goods: self.n_goods,
            budgets: self.budgets.clone(),
            supplies: self.supplies.clone(),
            util: self.util.clone(),
        }
    }

    /// Validate the equilibrium KKT conditions at slack `tol` (recomputed from the
    /// public program + `(x, p)` — the checker trusts nothing stored).
    pub fn check_with(&self, tol: f64) -> CertEqReport {
        let m = self.market();
        let n = self.n_buyers;
        let g = self.n_goods;
        let eps = 1e-12;

        let alloc_nonneg = self.x.iter().all(|&v| v >= -tol);
        let prices_nonneg = self.prices.iter().all(|&v| v >= -tol);

        // Supply feasibility per good.
        let mut supply_feasible = true;
        let mut demand = vec![0.0f64; g];
        for j in 0..g {
            let mut d = 0.0;
            for i in 0..n {
                d += self.x[i * g + j];
            }
            demand[j] = d;
            if d > self.supplies[j] + tol {
                supply_feasible = false;
            }
        }

        // Per-buyer multiplier βᵢ = bᵢ / Uᵢ (inverse marginal utility of money).
        let utilities: Vec<f64> = (0..n).map(|i| m.utility(&self.x, i)).collect();
        let beta: Vec<f64> = (0..n)
            .map(|i| self.budgets[i] / utilities[i].max(eps))
            .collect();

        // Stationarity βᵢ uᵢⱼ ≤ pⱼ, and buyer complementary slackness.
        let mut stationary = true;
        let mut buyer_cs = 0.0f64;
        for i in 0..n {
            for j in 0..g {
                let gap = self.prices[j] - beta[i] * m.u(i, j); // ≥ 0 at equilibrium
                if gap < -tol {
                    stationary = false;
                }
                buyer_cs += self.x[i * g + j] * gap.abs();
            }
        }

        // Market-clearing slackness Σⱼ pⱼ(sⱼ − demandⱼ).
        let clearing_cs: f64 = (0..g)
            .map(|j| (self.prices[j] * (self.supplies[j] - demand[j])).abs())
            .sum();

        // Budget-exhaustion residual (derived, reported).
        let mut budget_residual = 0.0f64;
        for i in 0..n {
            let spend: f64 = (0..g).map(|j| self.prices[j] * self.x[i * g + j]).sum();
            budget_residual = budget_residual.max((spend - self.budgets[i]).abs());
        }

        let cs_ok = buyer_cs <= tol && clearing_cs <= tol;
        let valid = alloc_nonneg && supply_feasible && prices_nonneg && stationary && cs_ok;

        CertEqReport {
            alloc_nonneg,
            supply_feasible,
            prices_nonneg,
            stationary,
            buyer_cs,
            clearing_cs,
            budget_residual,
            tol,
            valid,
        }
    }

    /// `check_with` at a tolerance scaled to the total budget (the natural scale of
    /// the CS residuals, which are in money units).
    pub fn check(&self) -> CertEqReport {
        let total_budget: f64 = self.budgets.iter().sum::<f64>().max(1.0);
        self.check_with(self.epsilon * total_budget)
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

// ============================================================================
// Test-instance builders.
// ============================================================================

/// A small deterministic Fisher market: `n` buyers, `g` goods, unit supplies,
/// equal budgets, and a structured utility matrix (buyer `i` favours good
/// `i mod g` but values all goods positively — a genuinely contested market).
pub fn sample_market(n: usize, g: usize) -> FisherMarket {
    let mut util = vec![0.0f64; n * g];
    for i in 0..n {
        for j in 0..g {
            let base = 1.0 + ((i + 2 * j) % 5) as f64 * 0.5;
            let favour = if j == i % g { 3.0 } else { 0.0 };
            util[i * g + j] = base + favour;
        }
    }
    FisherMarket {
        n_buyers: n,
        n_goods: g,
        budgets: (0..n).map(|i| 1.0 + (i % 3) as f64).collect(),
        supplies: vec![1.0; g],
        util,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proportional_response_reaches_equilibrium() {
        let m = sample_market(4, 3);
        let res = solve_proportional_response(&m, 20_000);
        let cert = res.certificate(&m, 1e-4);
        let rep = cert.check();
        assert!(rep.alloc_nonneg, "x ≥ 0");
        assert!(rep.supply_feasible, "Σx ≤ s");
        assert!(rep.prices_nonneg, "p ≥ 0");
        assert!(rep.stationary, "βu ≤ p (MBB)");
        assert!(rep.valid, "converged equilibrium must certify: {rep:?}");
    }

    #[test]
    fn prices_satisfy_walras_law() {
        // Σⱼ pⱼ = Σᵢ bᵢ (prices redistribute exactly the total budget).
        let m = sample_market(5, 4);
        let res = solve_proportional_response(&m, 10_000);
        let total_price: f64 = res.prices.iter().sum();
        let total_budget: f64 = m.budgets.iter().sum();
        assert!(
            (total_price - total_budget).abs() < 1e-6,
            "Walras: Σp={total_price} vs Σb={total_budget}"
        );
    }

    #[test]
    fn budget_is_exhausted_at_equilibrium() {
        // Stationarity + buyer-CS ⇒ each buyer spends their whole budget.
        let m = sample_market(4, 3);
        let res = solve_proportional_response(&m, 20_000);
        let cert = res.certificate(&m, 1e-4);
        let rep = cert.check();
        let scale: f64 = m.budgets.iter().sum::<f64>();
        assert!(
            rep.budget_residual < 1e-3 * scale,
            "budget exhaustion residual {} too large",
            rep.budget_residual
        );
    }

    #[test]
    fn tampered_equilibrium_is_rejected() {
        // Move allocation off the equilibrium: break market clearing / supply.
        let m = sample_market(4, 3);
        let res = solve_proportional_response(&m, 20_000);
        let mut cert = res.certificate(&m, 1e-4);
        // Give buyer 0 all of good 0 on top of what everyone else holds → the
        // demand for good 0 exceeds supply, and clearing-CS blows up.
        cert.x[0] += m.supplies[0];
        let rep = cert.check();
        assert!(
            !rep.valid,
            "over-allocated certificate must be rejected: {rep:?}"
        );
    }

    #[test]
    fn tampered_prices_break_stationarity() {
        // Zero one price while buyers still hold that good → βu ≤ p fails there.
        let m = sample_market(4, 3);
        let res = solve_proportional_response(&m, 20_000);
        let mut cert = res.certificate(&m, 1e-4);
        cert.prices[0] = 0.0;
        let rep = cert.check();
        assert!(
            !rep.stationary || !rep.valid,
            "zeroed price must violate stationarity/CS: {rep:?}"
        );
    }

    #[test]
    fn eg_objective_increases_over_iterations() {
        // Proportional response is an ascent on the EG objective.
        let m = sample_market(4, 3);
        let early = solve_proportional_response(&m, 50);
        let late = solve_proportional_response(&m, 20_000);
        assert!(
            late.eg_objective >= early.eg_objective - 1e-9,
            "EG objective must not decrease: early={} late={}",
            early.eg_objective,
            late.eg_objective
        );
    }

    #[test]
    fn json_has_equilibrium_shape() {
        let m = sample_market(3, 2);
        let res = solve_proportional_response(&m, 5000);
        let cert = res.certificate(&m, 1e-4);
        let json = cert.to_json();
        assert!(json.contains("\"prices\""));
        assert!(json.contains("\"eg_objective\""));
    }
}
