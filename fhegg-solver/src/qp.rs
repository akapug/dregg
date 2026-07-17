//! QP via ADMM/OSQP — the second convex product on the same engine.
//!
//! Proves the "factory" claim (PRIVATE-CONVEX-ENGINE §2.5, §3): the private
//! convex engine is not one flow-LP but a family — a product is *a convex program
//! + a prox + its duality certificate*. Here the program is a quadratic program
//!
//! ```text
//!   minimize   ½ xᵀP x + qᵀx
//!   subject to l ≤ A x ≤ u          (OSQP standard form; box on x = identity rows of A)
//! ```
//!
//! solved by ADMM in the OSQP shape (Stellato et al. 2020): the KKT matrix
//!
//! ```text
//!   K = [ P + σI    Aᵀ   ]
//!       [ A       −ρ⁻¹ I ]
//! ```
//!
//! is CONSTANT across iterations (P, A are public structure), so it is factored
//! ONCE (dense LU here) and every iteration is a DIVISION-FREE back-substitution
//! plus a box projection — exactly the FHE-friendly shape (§1.3: "factor once,
//! iterate division-free"). This is the ADMM entry in the §2.5 method table, the
//! QP sibling of the PDHG flow-LP.
//!
//! ## The product — private Markowitz / mean-variance portfolio
//!
//! `min ½xᵀΣx − λ·μᵀx s.t. 1ᵀx = 1, 0 ≤ x ≤ w_max` (PRIVATE-CONVEX-ENGINE §3,
//! "Portfolio / Markowitz"): the covariance `Σ` and expected returns `μ` are the
//! PRIVATE data; the budget/long-only/position-cap constraints are the public
//! program form. `λ` sweeps the risk/return frontier (both polarities: `λ=0` =
//! min-variance diversified; large `λ` = return-seeking, concentrated to the cap).
//!
//! ## The certificate (§2.3, the QP Fenchel-gap specialization)
//!
//! A convex-QP optimum is certified by a primal-dual pair `(x, y)` satisfying the
//! complete KKT system — the QP analogue of Cert-F, still linear/quadratic-then-linear:
//!
//! ```text
//!   primal:  (A x − u)₊ = 0  and  (l − A x)₊ = 0        (l ≤ A x ≤ u)
//!   dual:    P x + q + Aᵀy = 0                          (stationarity)
//!   normal:  y ∈ N_[l,u](Ax)                            (sign + complementarity)
//! ```
//!
//! For a symmetric PSD `P`, all three residuals → 0 certify optimality INDEPENDENT
//! of how `(x, y)` were found (untrusted search, checked certificate).
//! [`CertQp::check`] validates the residuals; the public-program layer must pin the
//! convexity/PSD fact.  The
//! normal-cone check is load-bearing: primal feasibility plus stationarity alone can
//! be forged at a suboptimal point by choosing a dual with the wrong bound sign.

use serde::Serialize;

/// A dense QP instance in OSQP form `min ½xᵀPx+qᵀx s.t. l ≤ Ax ≤ u`.
/// Dense is fine at the portfolio scale (`n ≈ 10²–10³`).
#[derive(Clone, Debug)]
pub struct QpProblem {
    pub n: usize,
    /// `P` (n×n, symmetric PSD), row-major.
    pub p: Vec<f64>,
    pub q: Vec<f64>,
    /// Constraint matrix `A` (mc×n), row-major.
    pub a: Vec<f64>,
    pub l: Vec<f64>,
    pub u: Vec<f64>,
    pub mc: usize,
}

impl QpProblem {
    /// `A x`.
    pub fn a_times(&self, x: &[f64]) -> Vec<f64> {
        let mut out = vec![0.0; self.mc];
        for i in 0..self.mc {
            let mut s = 0.0;
            for j in 0..self.n {
                s += self.a[i * self.n + j] * x[j];
            }
            out[i] = s;
        }
        out
    }
    /// `Aᵀ y`.
    pub fn at_times(&self, y: &[f64]) -> Vec<f64> {
        let mut out = vec![0.0; self.n];
        for i in 0..self.mc {
            let yi = y[i];
            if yi == 0.0 {
                continue;
            }
            for j in 0..self.n {
                out[j] += self.a[i * self.n + j] * yi;
            }
        }
        out
    }
    /// `P x`.
    pub fn p_times(&self, x: &[f64]) -> Vec<f64> {
        let mut out = vec![0.0; self.n];
        for i in 0..self.n {
            let mut s = 0.0;
            for j in 0..self.n {
                s += self.p[i * self.n + j] * x[j];
            }
            out[i] = s;
        }
        out
    }
    /// Objective `½ xᵀP x + qᵀx`.
    pub fn objective(&self, x: &[f64]) -> f64 {
        let px = self.p_times(x);
        let quad: f64 = 0.5 * x.iter().zip(&px).map(|(a, b)| a * b).sum::<f64>();
        let lin: f64 = self.q.iter().zip(x).map(|(a, b)| a * b).sum();
        quad + lin
    }
}

/// The QP solution + certificate residuals.
#[derive(Clone, Debug)]
pub struct QpResult {
    pub x: Vec<f64>,
    /// Dual `y` on the constraints `l ≤ Ax ≤ u`.
    pub y: Vec<f64>,
    pub objective: f64,
    /// `‖(Ax−u)₊ + (l−Ax)₊‖_∞` (primal infeasibility).
    pub prim_res: f64,
    /// `‖Px + q + Aᵀy‖_∞` (dual / stationarity residual).
    pub dual_res: f64,
    pub iters: usize,
}

// ---------------------------------------------------------------------------
// Dense LU (factor once, solve each iteration) — the "public one-time factor".
// ---------------------------------------------------------------------------

/// In-place LU with partial pivoting on an n×n row-major matrix. Returns the
/// row-permutation. The KKT matrix is quasidefinite; partial pivoting is stable.
fn lu_factor(a: &mut [f64], n: usize) -> Vec<usize> {
    let mut piv: Vec<usize> = (0..n).collect();
    for k in 0..n {
        let mut p = k;
        let mut mx = a[k * n + k].abs();
        for i in (k + 1)..n {
            let v = a[i * n + k].abs();
            if v > mx {
                mx = v;
                p = i;
            }
        }
        if p != k {
            for j in 0..n {
                a.swap(k * n + j, p * n + j);
            }
            piv.swap(k, p);
        }
        let akk = a[k * n + k];
        for i in (k + 1)..n {
            let f = a[i * n + k] / akk;
            a[i * n + k] = f;
            for j in (k + 1)..n {
                a[i * n + j] -= f * a[k * n + j];
            }
        }
    }
    piv
}

/// Solve `L U x = P b` given the factorization from [`lu_factor`].
fn lu_solve(a: &[f64], piv: &[usize], n: usize, b: &[f64]) -> Vec<f64> {
    let mut x: Vec<f64> = piv.iter().map(|&p| b[p]).collect();
    for i in 0..n {
        for j in 0..i {
            x[i] -= a[i * n + j] * x[j];
        }
    }
    for i in (0..n).rev() {
        for j in (i + 1)..n {
            x[i] -= a[i * n + j] * x[j];
        }
        x[i] /= a[i * n + i];
    }
    x
}

/// Solve the QP by OSQP-style ADMM. `rho`, `sigma`, `alpha` are the standard OSQP
/// parameters (rho penalty, sigma regularization, alpha over-relaxation).
pub fn solve_admm(prob: &QpProblem, iters: usize, rho: f64, sigma: f64, alpha: f64) -> QpResult {
    let n = prob.n;
    let mc = prob.mc;
    let dim = n + mc;

    // Assemble the CONSTANT KKT matrix K = [[P+σI, Aᵀ],[A, −ρ⁻¹ I]].
    let mut k = vec![0.0f64; dim * dim];
    for i in 0..n {
        for j in 0..n {
            k[i * dim + j] = prob.p[i * n + j];
        }
        k[i * dim + i] += sigma;
    }
    for r in 0..mc {
        for j in 0..n {
            let a_rj = prob.a[r * n + j];
            k[(n + r) * dim + j] = a_rj; // A block
            k[j * dim + (n + r)] = a_rj; // Aᵀ block
        }
        k[(n + r) * dim + (n + r)] = -1.0 / rho;
    }
    let piv = lu_factor(&mut k, dim);

    let mut x = vec![0.0f64; n];
    let mut z = vec![0.0f64; mc];
    let mut y = vec![0.0f64; mc];

    for _ in 0..iters {
        // rhs = [σx − q ; z − ρ⁻¹ y].
        let mut rhs = vec![0.0f64; dim];
        for j in 0..n {
            rhs[j] = sigma * x[j] - prob.q[j];
        }
        for r in 0..mc {
            rhs[n + r] = z[r] - y[r] / rho;
        }
        let sol = lu_solve(&k, &piv, dim, &rhs);
        let xt = &sol[..n];
        let nu = &sol[n..];

        // z̃ = z + ρ⁻¹(ν − y).
        let ztil: Vec<f64> = (0..mc).map(|r| z[r] + (nu[r] - y[r]) / rho).collect();

        // x = α x̃ + (1−α) x.
        for j in 0..n {
            x[j] = alpha * xt[j] + (1.0 - alpha) * x[j];
        }
        // z = Π_{[l,u]}( α z̃ + (1−α) z + ρ⁻¹ y ); y update.
        for r in 0..mc {
            let zr_relaxed = alpha * ztil[r] + (1.0 - alpha) * z[r];
            let znew = (zr_relaxed + y[r] / rho).clamp(prob.l[r], prob.u[r]);
            y[r] += rho * (zr_relaxed - znew);
            z[r] = znew;
        }
    }

    finalize_qp(prob, x, y, iters)
}

/// Assemble the result + certificate residuals from `(x, y)`.
pub fn finalize_qp(prob: &QpProblem, x: Vec<f64>, y: Vec<f64>, iters: usize) -> QpResult {
    let ax = prob.a_times(&x);
    let prim_res = (0..prob.mc).fold(0.0f64, |m, r| {
        let over = (ax[r] - prob.u[r]).max(0.0);
        let under = (prob.l[r] - ax[r]).max(0.0);
        m.max(over + under)
    });
    let px = prob.p_times(&x);
    let aty = prob.at_times(&y);
    let dual_res = (0..prob.n).fold(0.0f64, |m, j| m.max((px[j] + prob.q[j] + aty[j]).abs()));
    let objective = prob.objective(&x);
    QpResult {
        x,
        y,
        objective,
        prim_res,
        dual_res,
        iters,
    }
}

// ---------------------------------------------------------------------------
// Markowitz builder + certificate.
// ---------------------------------------------------------------------------

/// Build a private Markowitz QP: `min ½xᵀΣx − λμᵀx s.t. 1ᵀx=1, 0≤x≤w_max`.
/// `cov` is n×n row-major (PSD); `mu` the expected returns.
pub fn markowitz(cov: &[f64], mu: &[f64], lambda: f64, w_max: f64) -> QpProblem {
    let n = mu.len();
    assert_eq!(cov.len(), n * n);
    let p = cov.to_vec();
    let q: Vec<f64> = mu.iter().map(|m| -lambda * m).collect();
    // Constraints: row 0 = budget 1ᵀx = 1; rows 1..=n = box 0 ≤ x_j ≤ w_max.
    let mc = n + 1;
    let mut a = vec![0.0f64; mc * n];
    for j in 0..n {
        a[j] = 1.0; // budget row
    }
    for j in 0..n {
        a[(1 + j) * n + j] = 1.0; // identity rows
    }
    let mut l = vec![0.0f64; mc];
    let mut u = vec![0.0f64; mc];
    l[0] = 1.0;
    u[0] = 1.0; // budget equality
    for j in 0..n {
        l[1 + j] = 0.0;
        u[1 + j] = w_max;
    }
    QpProblem {
        n,
        p,
        q,
        a,
        l,
        u,
        mc,
    }
}

/// The QP certificate (public program + primal-dual witness). The QP analogue of
/// [`crate::cert::CertF`]; `check` validates the KKT residual (§2.3).
#[derive(Clone, Debug, Serialize)]
pub struct CertQp {
    pub n: usize,
    pub mc: usize,
    pub p: Vec<f64>,
    pub q: Vec<f64>,
    pub a: Vec<f64>,
    pub l: Vec<f64>,
    pub u: Vec<f64>,
    pub x: Vec<f64>,
    pub y: Vec<f64>,
    pub epsilon: f64,
    pub objective: f64,
    pub prim_res: f64,
    pub dual_res: f64,
}

/// The QP certificate check report.
#[derive(Clone, Debug, Serialize)]
pub struct CertQpReport {
    pub well_formed: bool,
    pub primal_feasible: bool,
    pub dual_feasible: bool,
    pub normal_cone: bool,
    pub prim_res: f64,
    pub dual_res: f64,
    pub normal_res: f64,
    pub tol: f64,
    pub valid: bool,
}

impl CertQp {
    pub fn from_solution(prob: &QpProblem, res: &QpResult, epsilon: f64) -> Self {
        CertQp {
            n: prob.n,
            mc: prob.mc,
            p: prob.p.clone(),
            q: prob.q.clone(),
            a: prob.a.clone(),
            l: prob.l.clone(),
            u: prob.u.clone(),
            x: res.x.clone(),
            y: res.y.clone(),
            epsilon,
            objective: res.objective,
            prim_res: res.prim_res,
            dual_res: res.dual_res,
        }
    }

    /// Validate the complete KKT residual against `epsilon` (recomputed from
    /// `(x,y)` — a checker does not trust the stored residuals).
    pub fn check(&self) -> CertQpReport {
        let p_len = self.n.checked_mul(self.n);
        let a_len = self.mc.checked_mul(self.n);
        let all_finite = self
            .p
            .iter()
            .chain(&self.q)
            .chain(&self.a)
            .chain(&self.l)
            .chain(&self.u)
            .chain(&self.x)
            .chain(&self.y)
            .all(|v| v.is_finite());
        let well_formed = p_len == Some(self.p.len())
            && self.q.len() == self.n
            && a_len == Some(self.a.len())
            && self.l.len() == self.mc
            && self.u.len() == self.mc
            && self.x.len() == self.n
            && self.y.len() == self.mc
            && self.epsilon.is_finite()
            && self.epsilon >= 0.0
            && all_finite
            && self.l.iter().zip(&self.u).all(|(l, u)| l <= u);
        if !well_formed {
            return CertQpReport {
                well_formed: false,
                primal_feasible: false,
                dual_feasible: false,
                normal_cone: false,
                prim_res: f64::INFINITY,
                dual_res: f64::INFINITY,
                normal_res: f64::INFINITY,
                tol: self.epsilon,
                valid: false,
            };
        }
        let prob = QpProblem {
            n: self.n,
            p: self.p.clone(),
            q: self.q.clone(),
            a: self.a.clone(),
            l: self.l.clone(),
            u: self.u.clone(),
            mc: self.mc,
        };
        let ax = prob.a_times(&self.x);
        let px = prob.p_times(&self.x);
        let aty = prob.at_times(&self.y);
        let arithmetic_finite = ax.iter().all(|v| v.is_finite())
            && px.iter().all(|v| v.is_finite())
            && aty.iter().all(|v| v.is_finite())
            && (0..self.n).all(|j| (px[j] + self.q[j] + aty[j]).is_finite())
            && (0..self.mc).all(|r| (ax[r] + self.y[r]).is_finite());
        if !arithmetic_finite {
            return CertQpReport {
                well_formed: false,
                primal_feasible: false,
                dual_feasible: false,
                normal_cone: false,
                prim_res: f64::INFINITY,
                dual_res: f64::INFINITY,
                normal_res: f64::INFINITY,
                tol: self.epsilon,
                valid: false,
            };
        }
        let recomputed = finalize_qp(&prob, self.x.clone(), self.y.clone(), 0);
        // y ∈ N_[l,u](z) iff z = projection_[l,u](z + y).  This single
        // projection residual enforces lower-bound y≤0, upper-bound y≥0,
        // interior y=0, and leaves equality-row duals free.
        let normal_res = (0..self.mc).fold(0.0f64, |m, r| {
            let projected = (ax[r] + self.y[r]).clamp(self.l[r], self.u[r]);
            m.max((ax[r] - projected).abs())
        });
        let primal_feasible = recomputed.prim_res <= self.epsilon;
        let dual_feasible = recomputed.dual_res <= self.epsilon;
        let normal_cone = normal_res <= self.epsilon;
        CertQpReport {
            well_formed,
            primal_feasible,
            dual_feasible,
            normal_cone,
            prim_res: recomputed.prim_res,
            dual_res: recomputed.dual_res,
            normal_res,
            tol: self.epsilon,
            valid: primal_feasible && dual_feasible && normal_cone,
        }
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small deterministic covariance (diagonal-dominant PSD) + returns.
    fn instance(n: usize) -> (Vec<f64>, Vec<f64>) {
        let mut cov = vec![0.0f64; n * n];
        for i in 0..n {
            for j in 0..n {
                cov[i * n + j] = if i == j {
                    1.0 + i as f64 * 0.1
                } else {
                    0.2 / (1.0 + (i as f64 - j as f64).abs())
                };
            }
        }
        // Expected returns increasing with index.
        let mu: Vec<f64> = (0..n).map(|i| 0.05 + 0.02 * i as f64).collect();
        (cov, mu)
    }

    #[test]
    fn min_variance_polarity_diversifies() {
        // λ = 0: pure min-variance. Budget met, box respected, certificate valid.
        let (cov, mu) = instance(6);
        let prob = markowitz(&cov, &mu, 0.0, 1.0);
        let res = solve_admm(&prob, 4000, 1.0, 1e-6, 1.6);
        let sum: f64 = res.x.iter().sum();
        assert!((sum - 1.0).abs() < 1e-3, "budget 1ᵀx=1: sum={sum}");
        assert!(
            res.x.iter().all(|&v| v > -1e-4 && v < 1.0 + 1e-4),
            "box respected"
        );
        let cert = CertQp::from_solution(&prob, &res, 1e-3);
        assert!(
            cert.check().valid,
            "min-variance certificate valid: {:?}",
            cert.check()
        );
    }

    #[test]
    fn return_seeking_polarity_concentrates() {
        // Large λ with a position cap: weight piles onto the high-return assets up
        // to w_max. Opposite polarity from min-variance.
        let (cov, mu) = instance(6);
        let w_max = 0.4;
        let prob = markowitz(&cov, &mu, 20.0, w_max);
        let res = solve_admm(&prob, 6000, 1.0, 1e-6, 1.6);
        let sum: f64 = res.x.iter().sum();
        assert!((sum - 1.0).abs() < 1e-3, "budget met: sum={sum}");
        // Every position respects the cap.
        assert!(
            res.x.iter().all(|&v| v <= w_max + 1e-3),
            "position cap respected"
        );
        // The highest-return asset (last) is at/near its cap.
        assert!(
            res.x[5] > w_max - 0.05,
            "return-seeking concentrates: x5={}",
            res.x[5]
        );
        let cert = CertQp::from_solution(&prob, &res, 1e-3);
        assert!(
            cert.check().valid,
            "return-seeking certificate valid: {:?}",
            cert.check()
        );
    }

    #[test]
    fn tampered_qp_certificate_rejected() {
        let (cov, mu) = instance(5);
        let prob = markowitz(&cov, &mu, 1.0, 1.0);
        let res = solve_admm(&prob, 4000, 1.0, 1e-6, 1.6);
        let mut cert = CertQp::from_solution(&prob, &res, 1e-3);
        cert.x[0] += 0.5; // break budget + stationarity
        assert!(!cert.check().valid, "tampered QP solution must be rejected");
    }

    #[test]
    fn forged_wrong_sign_dual_is_rejected() {
        // min 1/2 x² - x on [0,2] has optimum x=1.  At the suboptimal lower
        // bound x=0, forged y=+1 cancels the gradient, so the OLD checker saw
        // prim_res=dual_res=0 and accepted at epsilon=0.  Lower-bound KKT duals
        // must be non-positive: the normal-cone residual catches the forgery.
        let prob = QpProblem {
            n: 1,
            p: vec![1.0],
            q: vec![-1.0],
            a: vec![1.0],
            l: vec![0.0],
            u: vec![2.0],
            mc: 1,
        };
        let forged = finalize_qp(&prob, vec![0.0], vec![1.0], 0);
        assert_eq!(forged.prim_res, 0.0);
        assert_eq!(forged.dual_res, 0.0);
        let cert = CertQp::from_solution(&prob, &forged, 0.0);
        let report = cert.check();
        assert_eq!(report.normal_res, 1.0);
        assert!(!report.normal_cone);
        assert!(
            !report.valid,
            "wrong-sign dual must not certify a suboptimal point"
        );
    }

    #[test]
    fn nonfinite_certificate_fails_closed() {
        let (cov, mu) = instance(3);
        let prob = markowitz(&cov, &mu, 1.0, 1.0);
        let res = solve_admm(&prob, 2000, 1.0, 1e-6, 1.6);
        let mut cert = CertQp::from_solution(&prob, &res, 1e-3);
        cert.x[0] = f64::NAN;
        let report = cert.check();
        assert!(!report.well_formed);
        assert!(!report.valid);
    }

    #[test]
    fn overflowing_certificate_fails_closed() {
        let prob = QpProblem {
            n: 1,
            p: vec![f64::MAX],
            q: vec![0.0],
            a: vec![1.0],
            l: vec![0.0],
            u: vec![f64::MAX],
            mc: 1,
        };
        let res = QpResult {
            x: vec![f64::MAX],
            y: vec![0.0],
            objective: 0.0,
            prim_res: 0.0,
            dual_res: 0.0,
            iters: 0,
        };
        let cert = CertQp::from_solution(&prob, &res, 0.0);
        let report = cert.check();
        assert!(!report.well_formed);
        assert!(!report.valid);
    }

    #[test]
    fn qp_json_has_shape() {
        let (cov, mu) = instance(3);
        let prob = markowitz(&cov, &mu, 1.0, 1.0);
        let res = solve_admm(&prob, 2000, 1.0, 1e-6, 1.6);
        let cert = CertQp::from_solution(&prob, &res, 1e-3);
        let json = cert.to_json();
        assert!(json.contains("\"prim_res\""));
        assert!(json.contains("\"dual_res\""));
    }
}
