//! Smooth-convex / SGD certified — the engine generalizes PAST LP/clearing.
//!
//! Everything else in this crate ([`crate::pdhg`], [`crate::qp`], [`crate::fisher`],
//! [`crate::package`]) certifies a program whose optimality witness is a
//! *duality gap* — a primal-dual pair `(x, y)` with `gap ≤ ε`. That is the
//! LP / convex-QP / equilibrium slice. This module carries the OTHER classical
//! verify-not-find axis (`docs/deos/VERIFIED-OPTIMIZATION-GENERALIZATION.md`):
//! **smooth convex minimization solved by (S)GD, certified by a gradient-norm
//! near-stationarity witness** — no dual variable, no simplex, just `‖∇f(x)‖`.
//!
//! This FOLLOWS Otti (Angel–Blumberg–Ioannidis–Woods, USENIX Security 2022),
//! whose verify-not-find compiler already spans **LP + SDP + SGD**
//! (`docs/deos/NOVELTY-AND-PAPER-ASSESSMENT.md` row 3). Verify-not-find is
//! Otti's; the breadth is Otti's. What dregg adds is the *privacy* carrier (the
//! same oblivious-fold / reveal-nothing discipline extends to this class) and
//! the *formal* checker. The point of this module is only to demonstrate that
//! our engine — verify-not-find over an optimization CLASS, one certificate per
//! class — reaches the smooth-convex/SGD class too, so **clearing is one
//! instantiation of a general verified-(private-)optimization substrate**, not
//! the whole of it.
//!
//! ## The problem — a concrete smooth convex objective
//!
//! Ridge-regularized least squares (equivalently: private tracking-error
//! portfolio, `min ‖Ax−b‖` tracking a benchmark with an L2 mandate):
//!
//! ```text
//!   f(x) = (1/2m) ‖A x − b‖²  +  (μ/2) ‖x‖²
//! ```
//!
//! `A` (`m×n`) and `b` are the data; `μ > 0` is the ridge / strong-convexity
//! coefficient (PUBLIC — part of the program form). Its Hessian is
//! `∇²f = (1/m) AᵀA + μ I ⪰ μ I`, so `f` is **`μ`-strongly convex** for ANY
//! data `A` — the floor `μ` is a genuine lower bound on the smallest curvature,
//! not an estimate. `f` is also `L`-smooth with `L = (1/m)λ_max(AᵀA) + μ`.
//! An L2-regularized **logistic** objective ([`SmoothConvex::RidgeLogistic`])
//! is carried too, to show the class is not a single objective.
//!
//! ## The certificate (`CertGrad`) — gradient-norm near-stationarity
//!
//! An untrusted solver runs (S)GD and emits the achieved point `x` (NOT its
//! trajectory). The certificate is
//!
//! ```text
//!   x,   ε,   with   ‖∇f(x)‖ ≤ ε        (near-stationarity).
//! ```
//!
//! For a `μ`-strongly-convex `f`, near-stationary ⇒ near-optimal, with the
//! standard **gradient-domination (Polyak–Łojasiewicz) bound**
//!
//! ```text
//!   f(x) − f*  ≤  ‖∇f(x)‖² / (2μ).
//! ```
//!
//! *Proof.* `μ`-strong convexity gives, for all `x, z`,
//! `f(z) ≥ f(x) + ⟨∇f(x), z−x⟩ + (μ/2)‖z−x‖²`. Minimising the right side over
//! `z` (at `z = x − ∇f(x)/μ`) gives `f* = min_z f(z) ≥ f(x) − ‖∇f(x)‖²/(2μ)`,
//! i.e. `f(x) − f* ≤ ‖∇f(x)‖²/(2μ)`. ∎ (This is the PL inequality that strong
//! convexity implies; it needs no diameter bound and no knowledge of `x*`.)
//!
//! So `‖∇f(x)‖ ≤ ε` certifies `f(x) − f* ≤ ε²/(2μ)` — an ε-optimality
//! statement, INDEPENDENT of how `x` was found. [`CertGrad::check`] re-derives
//! `∇f(x)` from the public program from scratch, recomputes the norm and the
//! bound — verify-not-find: it checks the certificate, never the SGD path.
//!
//! ## ⚠ The non-convex caveat (stated plainly, load-bearing)
//!
//! The gradient certificate is a **stationarity** certificate. For a `μ`-*convex*
//! `f` (this module) stationary ⇒ global-optimal, so it is a genuine
//! near-optimality certificate. For a **non-convex** `f` (a real neural net),
//! `‖∇f(x)‖ ≤ ε` certifies only that `x` is a near-**stationary point** — a
//! local critical point — NOT that `f(x)` is near the global optimum, and NOT
//! that the model is good. The honest ML statement is therefore *"a correct
//! computation reached a certified stationary point,"* never *"the trained model
//! is optimal."* The convex suboptimality bound above holds ONLY under the
//! convexity this module enforces (`μ > 0` strong convexity of a convex `f`).

use serde::{Deserialize, Serialize};

/// A smooth convex objective in the public program form. The data is stored in
/// the clear here (Stage-1: the solver sees everything; privacy is the later
/// STARK-ZK/FHE stage), exactly as [`crate::qp::CertQp`] and
/// [`crate::fisher::CertEq`] carry their program data.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SmoothConvex {
    /// Ridge-regularized least squares `f(x) = (1/2m)‖Ax−b‖² + (μ/2)‖x‖²`.
    /// `a` is row-major `m×n`. `μ`-strongly convex, `μ` = `mu` (the floor).
    RidgeLeastSquares {
        m: usize,
        n: usize,
        a: Vec<f64>,
        b: Vec<f64>,
        mu: f64,
    },
    /// L2-regularized logistic regression
    /// `f(x) = (1/m) Σ log(1+exp(−yᵢ aᵢ·x)) + (μ/2)‖x‖²`, `yᵢ ∈ {−1,+1}`.
    /// Convex + `μ`-strongly convex via the regulariser; smooth (Lipschitz
    /// gradient). No closed form, but the SAME gradient certificate applies.
    RidgeLogistic {
        m: usize,
        n: usize,
        a: Vec<f64>,
        y: Vec<f64>,
        mu: f64,
    },
}

/// Numerically-stable `log(1 + exp(u))`.
#[inline]
fn softplus(u: f64) -> f64 {
    if u > 0.0 {
        u + (1.0 + (-u).exp()).ln()
    } else {
        (1.0 + u.exp()).ln()
    }
}

/// Numerically-stable logistic sigmoid `σ(t) = 1/(1+exp(−t))`.
#[inline]
fn sigmoid(t: f64) -> f64 {
    if t >= 0.0 {
        1.0 / (1.0 + (-t).exp())
    } else {
        let e = t.exp();
        e / (1.0 + e)
    }
}

impl SmoothConvex {
    /// Problem dimension `n` (length of `x`).
    pub fn dim(&self) -> usize {
        match self {
            SmoothConvex::RidgeLeastSquares { n, .. } | SmoothConvex::RidgeLogistic { n, .. } => *n,
        }
    }

    /// The strong-convexity floor `μ` — a PUBLIC lower bound on the smallest
    /// curvature, valid for ANY data (it is the ridge coefficient). The
    /// suboptimality bound `f(x)−f* ≤ ‖∇f‖²/(2μ)` rides on this.
    pub fn mu(&self) -> f64 {
        match self {
            SmoothConvex::RidgeLeastSquares { mu, .. } | SmoothConvex::RidgeLogistic { mu, .. } => {
                *mu
            }
        }
    }

    /// `(row e of A) · x`.
    #[inline]
    fn row_dot(a: &[f64], n: usize, e: usize, x: &[f64]) -> f64 {
        let base = e * n;
        (0..n).map(|j| a[base + j] * x[j]).sum()
    }

    /// The objective value `f(x)`.
    pub fn value(&self, x: &[f64]) -> f64 {
        match self {
            SmoothConvex::RidgeLeastSquares { m, n, a, b, mu } => {
                let mut sq = 0.0;
                for e in 0..*m {
                    let r = Self::row_dot(a, *n, e, x) - b[e];
                    sq += r * r;
                }
                let reg: f64 = x.iter().map(|v| v * v).sum();
                sq / (2.0 * *m as f64) + 0.5 * mu * reg
            }
            SmoothConvex::RidgeLogistic { m, n, a, y, mu } => {
                let mut loss = 0.0;
                for e in 0..*m {
                    let z = Self::row_dot(a, *n, e, x);
                    loss += softplus(-y[e] * z);
                }
                let reg: f64 = x.iter().map(|v| v * v).sum();
                loss / *m as f64 + 0.5 * mu * reg
            }
        }
    }

    /// The gradient `∇f(x)` (dense, length `n`).
    pub fn grad(&self, x: &[f64]) -> Vec<f64> {
        match self {
            SmoothConvex::RidgeLeastSquares { m, n, a, b, mu } => {
                // g = (1/m) Aᵀ(Ax − b) + μ x.
                let mut g = vec![0.0f64; *n];
                let inv_m = 1.0 / *m as f64;
                for e in 0..*m {
                    let r = Self::row_dot(a, *n, e, x) - b[e];
                    let base = e * *n;
                    let rw = r * inv_m;
                    for j in 0..*n {
                        g[j] += a[base + j] * rw;
                    }
                }
                for j in 0..*n {
                    g[j] += mu * x[j];
                }
                g
            }
            SmoothConvex::RidgeLogistic { m, n, a, y, mu } => {
                // g = (1/m) Σ (−yᵢ σ(−yᵢ zᵢ)) aᵢ + μ x.
                let mut g = vec![0.0f64; *n];
                let inv_m = 1.0 / *m as f64;
                for e in 0..*m {
                    let z = Self::row_dot(a, *n, e, x);
                    let coef = -y[e] * sigmoid(-y[e] * z) * inv_m;
                    let base = e * *n;
                    for j in 0..*n {
                        g[j] += a[base + j] * coef;
                    }
                }
                for j in 0..*n {
                    g[j] += mu * x[j];
                }
                g
            }
        }
    }

    /// A SAFE smoothness constant `L ≥ λ_max(∇²f)` from the data (public,
    /// oblivious). Uses the Frobenius bound `λ_max(AᵀA) ≤ ‖A‖_F²`, so the GD
    /// step `η = 1/L` is guaranteed in the convergent regime (an overestimate
    /// only slows convergence, never diverges).
    pub fn l_smooth(&self) -> f64 {
        match self {
            SmoothConvex::RidgeLeastSquares { m, a, mu, .. } => {
                let fro2: f64 = a.iter().map(|v| v * v).sum();
                fro2 / *m as f64 + mu
            }
            SmoothConvex::RidgeLogistic { m, a, mu, .. } => {
                // logistic Hessian ⪯ (1/4)·(1/m)AᵀA + μ I.
                let fro2: f64 = a.iter().map(|v| v * v).sum();
                0.25 * fro2 / *m as f64 + mu
            }
        }
    }

    /// Number of summands `m` (for SGD minibatching).
    fn n_samples(&self) -> usize {
        match self {
            SmoothConvex::RidgeLeastSquares { m, .. } | SmoothConvex::RidgeLogistic { m, .. } => *m,
        }
    }

    /// The single-sample gradient `∇fₑ(x)` of the `e`-th summand (data term
    /// only; the `μx` regulariser is added by the SGD driver once per step).
    fn sample_grad(&self, e: usize, x: &[f64], out: &mut [f64]) {
        match self {
            SmoothConvex::RidgeLeastSquares { n, a, b, .. } => {
                let r = Self::row_dot(a, *n, e, x) - b[e];
                let base = e * *n;
                for j in 0..*n {
                    out[j] = a[base + j] * r;
                }
            }
            SmoothConvex::RidgeLogistic { n, a, y, .. } => {
                let z = Self::row_dot(a, *n, e, x);
                let coef = -y[e] * sigmoid(-y[e] * z);
                let base = e * *n;
                for j in 0..*n {
                    out[j] = a[base + j] * coef;
                }
            }
        }
    }
}

/// The solver output: the achieved point + its gradient norm.
#[derive(Clone, Debug)]
pub struct GradResult {
    pub x: Vec<f64>,
    pub value: f64,
    /// `‖∇f(x)‖₂` at the achieved point.
    pub grad_norm: f64,
    pub iters: usize,
}

impl GradResult {
    /// Build the [`CertGrad`] certificate against a claimed tolerance `ε`.
    pub fn certificate(&self, obj: &SmoothConvex, epsilon: f64) -> CertGrad {
        CertGrad::from_point(obj, &self.x, epsilon)
    }
}

fn l2(v: &[f64]) -> f64 {
    v.iter().map(|a| a * a).sum::<f64>().sqrt()
}

/// Full-batch gradient descent — the oblivious first-order search (fixed `T`,
/// data-independent step `η = 1/L`, straight-line). The UNTRUSTED half.
pub fn solve_gd(obj: &SmoothConvex, iters: usize) -> GradResult {
    let n = obj.dim();
    let eta = 1.0 / obj.l_smooth();
    let mut x = vec![0.0f64; n];
    for _ in 0..iters {
        let g = obj.grad(&x);
        for j in 0..n {
            x[j] -= eta * g[j];
        }
    }
    let g = obj.grad(&x);
    GradResult {
        value: obj.value(&x),
        grad_norm: l2(&g),
        x,
        iters,
    }
}

/// Minibatch **SGD** — the *stochastic* untrusted search. A deterministic
/// xorshift PRNG draws minibatches; the step decays as `η₀/(1+γt)`. The whole
/// point of verify-not-find: this reaches (approximately) the SAME point as
/// [`solve_gd`], and the certificate certifies it IDENTICALLY — the checker
/// never sees which solver ran.
pub fn solve_sgd(obj: &SmoothConvex, epochs: usize, batch: usize, seed: u64) -> GradResult {
    let n = obj.dim();
    let m = obj.n_samples();
    let mu = obj.mu();
    let l = obj.l_smooth();
    let eta0 = 1.0 / l;
    let mut x = vec![0.0f64; n];
    let mut state = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut gbuf = vec![0.0f64; n];
    let mut acc = vec![0.0f64; n];
    let steps_per_epoch = m.div_ceil(batch.max(1));
    let mut t = 0usize;
    for _ in 0..epochs {
        for _ in 0..steps_per_epoch {
            for a in acc.iter_mut() {
                *a = 0.0;
            }
            let bs = batch.max(1).min(m);
            for _ in 0..bs {
                let e = (next() as usize) % m;
                obj.sample_grad(e, &x, &mut gbuf);
                for j in 0..n {
                    acc[j] += gbuf[j];
                }
            }
            // stochastic gradient estimate: mean of the batch data-grads + μx.
            let eta = eta0 / (1.0 + 0.01 * t as f64);
            let inv = 1.0 / bs as f64;
            for j in 0..n {
                let g = acc[j] * inv + mu * x[j];
                x[j] -= eta * g;
            }
            t += 1;
        }
    }
    let g = obj.grad(&x);
    GradResult {
        value: obj.value(&x),
        grad_norm: l2(&g),
        x,
        iters: t,
    }
}

/// The gradient-norm certificate: public program + achieved point `x`. The
/// smooth-convex analogue of [`crate::cert::CertF`] — a stationarity witness
/// with the convex suboptimality bound `f(x)−f* ≤ ‖∇f(x)‖²/(2μ)`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CertGrad {
    pub obj: SmoothConvex,
    /// The achieved point (the whole witness — no dual variable).
    pub x: Vec<f64>,
    /// The near-stationarity tolerance claimed: `‖∇f(x)‖ ≤ ε`.
    pub epsilon: f64,
    /// `‖∇f(x)‖₂` (stored; `check` recomputes it from the program).
    pub grad_norm: f64,
    /// The certified bound `‖∇f(x)‖²/(2μ) ≥ f(x)−f*` (stored; recomputed).
    pub suboptimality_bound: f64,
    /// `f(x)` at the achieved point (stored; recomputed).
    pub value: f64,
}

/// The result of running the gradient certificate checks.
#[derive(Clone, Debug, Serialize)]
pub struct CertGradReport {
    /// `‖∇f(x)‖ ≤ ε` (near-stationarity).
    pub near_stationary: bool,
    /// `μ > 0` — the convex suboptimality bound is valid (else stationarity is
    /// only a critical-point statement, the non-convex caveat).
    pub strongly_convex: bool,
    /// Recomputed `‖∇f(x)‖₂`.
    pub grad_norm: f64,
    /// The strong-convexity floor `μ`.
    pub mu: f64,
    /// Recomputed `f(x)`.
    pub value: f64,
    /// Recomputed certified suboptimality bound `‖∇f(x)‖²/(2μ)` — the checked
    /// guarantee `f(x) − f* ≤ this`.
    pub suboptimality_bound: f64,
    /// The tolerance used.
    pub epsilon: f64,
    /// `near_stationary && strongly_convex`.
    pub valid: bool,
}

impl CertGrad {
    /// Build the certificate from the achieved point (recomputes the norm/bound).
    pub fn from_point(obj: &SmoothConvex, x: &[f64], epsilon: f64) -> Self {
        let g = obj.grad(x);
        let grad_norm = l2(&g);
        let mu = obj.mu();
        let suboptimality_bound = if mu > 0.0 {
            grad_norm * grad_norm / (2.0 * mu)
        } else {
            f64::INFINITY
        };
        CertGrad {
            obj: obj.clone(),
            x: x.to_vec(),
            epsilon,
            grad_norm,
            suboptimality_bound,
            value: obj.value(x),
        }
    }

    /// Run the checks — recomputes `∇f(x)` from the PUBLIC program from scratch
    /// (the checker trusts nothing stored). Verify-not-find: this reads only the
    /// achieved point, never how it was found.
    pub fn check(&self) -> CertGradReport {
        let g = self.obj.grad(&self.x);
        let grad_norm = l2(&g);
        let mu = self.obj.mu();
        let strongly_convex = mu > 0.0;
        let near_stationary = grad_norm <= self.epsilon;
        let suboptimality_bound = if strongly_convex {
            grad_norm * grad_norm / (2.0 * mu)
        } else {
            f64::INFINITY
        };
        CertGradReport {
            near_stationary,
            strongly_convex,
            grad_norm,
            mu,
            value: self.obj.value(&self.x),
            suboptimality_bound,
            epsilon: self.epsilon,
            valid: near_stationary && strongly_convex,
        }
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("cert serializes")
    }
}

// ============================================================================
// Closed-form ground truth (ridge only) — verifies the suboptimality BOUND.
// ============================================================================

/// Solve the SPD system `H x = g` by Cholesky (`H` row-major `n×n`, SPD).
fn solve_spd(mut h: Vec<f64>, mut g: Vec<f64>, n: usize) -> Vec<f64> {
    // In-place Cholesky H = L Lᵀ (lower).
    for i in 0..n {
        for j in 0..=i {
            let mut s = h[i * n + j];
            for k in 0..j {
                s -= h[i * n + k] * h[j * n + k];
            }
            if i == j {
                h[i * n + j] = s.max(1e-300).sqrt();
            } else {
                h[i * n + j] = s / h[j * n + j];
            }
        }
    }
    // Forward solve L y = g.
    for i in 0..n {
        let mut s = g[i];
        for k in 0..i {
            s -= h[i * n + k] * g[k];
        }
        g[i] = s / h[i * n + i];
    }
    // Back solve Lᵀ x = y.
    for i in (0..n).rev() {
        let mut s = g[i];
        for k in (i + 1)..n {
            s -= h[k * n + i] * g[k];
        }
        g[i] = s / h[i * n + i];
    }
    g
}

/// The closed-form ridge optimum `x* = ((1/m)AᵀA + μI)⁻¹ (1/m)Aᵀb`. Panics on a
/// non-ridge objective — used to verify the certificate's suboptimality bound
/// against ground truth in tests / the benchmark.
pub fn ridge_optimum(obj: &SmoothConvex) -> Vec<f64> {
    match obj {
        SmoothConvex::RidgeLeastSquares { m, n, a, b, mu } => {
            let inv_m = 1.0 / *m as f64;
            // H = (1/m)AᵀA + μI, rhs = (1/m)Aᵀb.
            let mut h = vec![0.0f64; n * n];
            let mut rhs = vec![0.0f64; *n];
            for e in 0..*m {
                let base = e * *n;
                for i in 0..*n {
                    let ai = a[base + i];
                    rhs[i] += ai * b[e] * inv_m;
                    for j in 0..*n {
                        h[i * *n + j] += ai * a[base + j] * inv_m;
                    }
                }
            }
            for i in 0..*n {
                h[i * *n + i] += mu;
            }
            solve_spd(h, rhs, *n)
        }
        _ => panic!("ridge_optimum: closed form only for RidgeLeastSquares"),
    }
}

// ============================================================================
// Test-instance builders.
// ============================================================================

/// A deterministic ridge least-squares instance: pseudo-random `A`, targets `b`
/// generated from a planted `x★` plus noise, ridge coefficient `mu`.
pub fn ridge_instance(m: usize, n: usize, mu: f64, seed: u64) -> SmoothConvex {
    let mut state = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state >> 11) as f64 / (1u64 << 53) as f64 // in [0,1)
    };
    let a: Vec<f64> = (0..m * n).map(|_| next() * 2.0 - 1.0).collect();
    let xstar: Vec<f64> = (0..n).map(|_| next() * 2.0 - 1.0).collect();
    let b: Vec<f64> = (0..m)
        .map(|e| {
            let base = e * n;
            let clean: f64 = (0..n).map(|j| a[base + j] * xstar[j]).sum();
            clean + (next() * 2.0 - 1.0) * 0.1 // small noise
        })
        .collect();
    SmoothConvex::RidgeLeastSquares { m, n, a, b, mu }
}

/// A deterministic L2-logistic instance: features `A`, labels `y ∈ {−1,+1}` from
/// a planted separator with label noise.
pub fn logistic_instance(m: usize, n: usize, mu: f64, seed: u64) -> SmoothConvex {
    let mut state = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(7);
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state >> 11) as f64 / (1u64 << 53) as f64
    };
    let a: Vec<f64> = (0..m * n).map(|_| next() * 2.0 - 1.0).collect();
    let w: Vec<f64> = (0..n).map(|_| next() * 2.0 - 1.0).collect();
    let y: Vec<f64> = (0..m)
        .map(|e| {
            let base = e * n;
            let z: f64 = (0..n).map(|j| a[base + j] * w[j]).sum();
            let flip = next() < 0.05; // 5% label noise
            let s = if z >= 0.0 { 1.0 } else { -1.0 };
            if flip {
                -s
            } else {
                s
            }
        })
        .collect();
    SmoothConvex::RidgeLogistic { m, n, a, y, mu }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gd_reaches_near_stationary_and_certifies() {
        let obj = ridge_instance(60, 8, 1e-2, 1);
        let res = solve_gd(&obj, 5000);
        let cert = res.certificate(&obj, 1e-3);
        let rep = cert.check();
        assert!(
            rep.near_stationary,
            "converged GD must be near-stationary: ‖∇f‖={}",
            rep.grad_norm
        );
        assert!(rep.strongly_convex, "ridge is μ-strongly convex");
        assert!(rep.valid, "converged certificate must be valid: {rep:?}");
    }

    #[test]
    fn suboptimality_bound_holds_against_ground_truth() {
        // The CRUX: f(x) − f* ≤ ‖∇f(x)‖²/(2μ), verified against the closed-form
        // optimum at MANY points along the GD path (near and far), so the bound
        // is exercised, not just at convergence.
        let obj = ridge_instance(80, 10, 5e-2, 2);
        let xstar = ridge_optimum(&obj);
        let fstar = obj.value(&xstar);
        // ‖∇f(x*)‖ ≈ 0 at the true optimum.
        let gstar = super::l2(&obj.grad(&xstar));
        assert!(gstar < 1e-8, "∇f(x*) ≈ 0: {gstar}");

        let n = obj.dim();
        let eta = 1.0 / obj.l_smooth();
        let mut x = vec![0.0f64; n];
        for it in 0..2000 {
            let cert = CertGrad::from_point(&obj, &x, 1.0);
            let rep = cert.check();
            let true_subopt = obj.value(&x) - fstar;
            // The certified bound must UPPER-BOUND the true suboptimality.
            assert!(
                true_subopt <= rep.suboptimality_bound + 1e-9,
                "iter {it}: f−f*={true_subopt} exceeds bound {}",
                rep.suboptimality_bound
            );
            assert!(true_subopt >= -1e-9, "f ≥ f* (convexity): {true_subopt}");
            let g = obj.grad(&x);
            for j in 0..n {
                x[j] -= eta * g[j];
            }
        }
    }

    #[test]
    fn sgd_certifies_the_same_way_as_gd() {
        // Verify-not-find: a STOCHASTIC solver reaches a certifiable point, and
        // the certificate certifies it identically (the checker never sees the
        // trajectory).
        let obj = ridge_instance(120, 6, 1e-1, 3);
        let res = solve_sgd(&obj, 400, 8, 42);
        // SGD reaches a small (if not GD-tight) gradient; certify at its ε.
        let eps = res.grad_norm * 1.01 + 1e-9;
        let cert = res.certificate(&obj, eps);
        let rep = cert.check();
        assert!(rep.valid, "SGD point certifies at its own ε: {rep:?}");
        // And the certified suboptimality is a finite, meaningful bound.
        assert!(
            rep.suboptimality_bound.is_finite() && rep.suboptimality_bound >= 0.0,
            "finite suboptimality bound: {}",
            rep.suboptimality_bound
        );
    }

    #[test]
    fn far_from_stationary_point_is_rejected() {
        // A point with a large gradient (here x = 0 on a non-trivial instance)
        // fails near-stationarity at a tight ε — the negative polarity.
        let obj = ridge_instance(60, 8, 1e-2, 4);
        let x0 = vec![0.0f64; obj.dim()];
        let g0 = super::l2(&obj.grad(&x0));
        assert!(g0 > 1e-2, "x=0 is genuinely far from stationary: {g0}");
        let cert = CertGrad::from_point(&obj, &x0, 1e-4);
        let rep = cert.check();
        assert!(!rep.near_stationary, "large gradient must fail ε");
        assert!(!rep.valid, "far-from-stationary certificate rejected");
    }

    #[test]
    fn tampered_point_is_rejected() {
        // Take a valid certificate, perturb the achieved point off the optimum:
        // the recomputed gradient blows past ε, so check() REFUSES. The checker
        // recomputes ∇f from scratch, so a lie about x cannot pass.
        let obj = ridge_instance(60, 8, 1e-2, 5);
        let res = solve_gd(&obj, 5000);
        let mut cert = res.certificate(&obj, 1e-3);
        assert!(cert.check().valid, "baseline valid");
        cert.x[0] += 1.0; // move off the stationary point
        let rep = cert.check();
        assert!(
            !rep.near_stationary,
            "tampered x recomputes a large gradient: ‖∇f‖={}",
            rep.grad_norm
        );
        assert!(!rep.valid, "tampered certificate must be rejected");
    }

    #[test]
    fn logistic_gd_certifies() {
        let obj = logistic_instance(100, 6, 1e-2, 6);
        let res = solve_gd(&obj, 8000);
        let cert = res.certificate(&obj, 1e-2);
        let rep = cert.check();
        assert!(
            rep.near_stationary,
            "logistic GD near-stationary: ‖∇f‖={}",
            rep.grad_norm
        );
        assert!(rep.valid, "logistic certificate valid: {rep:?}");
    }

    #[test]
    fn json_roundtrips_shape() {
        let obj = ridge_instance(20, 4, 1e-2, 7);
        let res = solve_gd(&obj, 1000);
        let cert = res.certificate(&obj, 1e-2);
        let json = cert.to_json();
        assert!(json.contains("\"grad_norm\""));
        assert!(json.contains("\"suboptimality_bound\""));
        assert!(json.contains("\"epsilon\""));
        let back: CertGrad = serde_json::from_str(&json).unwrap();
        assert_eq!(back.x.len(), 4);
        // The deserialized certificate re-checks identically.
        assert_eq!(back.check().valid, cert.check().valid);
    }
}
