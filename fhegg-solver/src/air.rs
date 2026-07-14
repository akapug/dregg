//! Cert-F as emittable AIR/circuit constraints — the Tier-1 STARK bridge.
//!
//! `CertF::check` (cert.rs) validates the certificate in Rust. This module emits
//! the SAME checks as a structured **constraint system** over the witness columns
//! `(f, π, s)` — the shape the Lean-verified Cert-F checker (the sibling
//! Lean-cores lane) and the in-STARK AIR both consume. It is deliberately NOT a
//! full STARK: it is the emittable constraint set + a self-check that the emitted
//! system accepts exactly the certificates `check()` accepts, so Stage-1
//! end-to-end (fast search → PROVEN certificate → STARK-ZK) is one wiring step
//! away.
//!
//! ## The constraints (PRIVATE-CONVEX-ENGINE §2.3, the `O(m + nnz A)` count)
//!
//! For the circulation LP `max wᵀf s.t. Af=0, 0≤f≤c` with dual `(π, s)`:
//!
//! | # | constraint | relation | count |
//! |---|---|---|---|
//! | conservation | `Σ_{head=i} f_e − Σ_{tail=i} f_e = 0` | `== 0` | `n` (nnz A terms) |
//! | box lower | `f_e ≥ 0` | `≥ 0` | `m` |
//! | box upper | `c_e − f_e ≥ 0` | `≥ 0` | `m` |
//! | slack sign | `s_e ≥ 0` | `≥ 0` | `m` |
//! | dual feas | `π_{head} − π_{tail} + s_e − w_e ≥ 0` | `≥ 0` | `m` |
//! | gap | `Σ c_e s_e − Σ w_e f_e ≤ ε` | `≤ ε` | `1` |
//!
//! Totals: `n + 4m + 1` constraints over `2m + n` witness cells, with
//! `O(m + nnz A)` terms — exactly the §2.3 size win (`O(T·m)` for proving the
//! iterations collapses to `O(m + nnz A)` for checking the certificate).
//!
//! ## How it plugs into the checker / STARK (the wiring note)
//!
//! - **Lean Cert-F checker.** Each row is a linear form over the witness; the
//!   Lean checker evaluates `expr {==0, ≥0, ≤ε}` on the committed columns. The
//!   emitted [`ConstraintSystem`] is that exact list — `evaluate` here mirrors
//!   what the Lean side proves sound.
//! - **STARK AIR.** Conservation + dual-feas + gap are boundary/transition
//!   constraints over the witness columns `f, π, s` (public `A, w, c` as
//!   selector constants). The `≥ 0` range constraints lower to the prover's
//!   range-check gadget (bit-decomposition), and the single `≤ ε` gap is one
//!   boundary comparison. The witness is the solver output; the AIR enforces the
//!   certificate, never the T iterations (untrusted search, checked output).

use crate::cert::CertF;
use serde::Serialize;

/// A witness cell the constraints reference.
#[derive(Clone, Copy, Debug, Serialize, PartialEq)]
pub enum Var {
    /// Primal flow `f_e`.
    F(usize),
    /// Dual potential `π_i`.
    Pi(usize),
    /// Dual slack `s_e`.
    S(usize),
}

/// The relation a constraint's affine form must satisfy.
#[derive(Clone, Copy, Debug, Serialize, PartialEq)]
pub enum Relation {
    /// `expr == 0`.
    Zero,
    /// `expr ≥ 0`.
    NonNeg,
    /// `expr ≤ ε`.
    AtMostEps,
}

/// One term `coeff · var` of a constraint's affine form.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Term {
    pub var: Var,
    pub coeff: f64,
}

/// One constraint: `Σ coeff·var + constant  {relation}`.
#[derive(Clone, Debug, Serialize)]
pub struct Constraint {
    pub label: &'static str,
    pub terms: Vec<Term>,
    pub constant: f64,
    pub relation: Relation,
}

/// The emitted Cert-F constraint system over the witness `(f, π, s)`.
#[derive(Clone, Debug, Serialize)]
pub struct ConstraintSystem {
    /// Column count: `m` (f) + `n` (π) + `m` (s).
    pub n_vars: usize,
    pub m_edges: usize,
    pub n_nodes: usize,
    pub epsilon: f64,
    pub constraints: Vec<Constraint>,
}

impl ConstraintSystem {
    /// Emit the Cert-F check as constraints (§2.3). `O(m + nnz A)` terms.
    pub fn emit(cert: &CertF) -> Self {
        let n = cert.n_nodes;
        let m = cert.m_edges;
        let mut constraints = Vec::with_capacity(n + 4 * m + 1);

        // 1. Conservation, one per node: Σ_{head=i} f_e − Σ_{tail=i} f_e = 0.
        let mut node_terms: Vec<Vec<Term>> = vec![Vec::new(); n];
        for (e, &(t, h)) in cert.edges.iter().enumerate() {
            node_terms[h as usize].push(Term {
                var: Var::F(e),
                coeff: 1.0,
            });
            node_terms[t as usize].push(Term {
                var: Var::F(e),
                coeff: -1.0,
            });
        }
        for (_i, terms) in node_terms.into_iter().enumerate() {
            constraints.push(Constraint {
                label: "conservation",
                terms,
                constant: 0.0,
                relation: Relation::Zero,
            });
        }

        // 2. Box lower f_e ≥ 0 ; 3. box upper c_e − f_e ≥ 0.
        for e in 0..m {
            constraints.push(Constraint {
                label: "box_lower",
                terms: vec![Term {
                    var: Var::F(e),
                    coeff: 1.0,
                }],
                constant: 0.0,
                relation: Relation::NonNeg,
            });
            constraints.push(Constraint {
                label: "box_upper",
                terms: vec![Term {
                    var: Var::F(e),
                    coeff: -1.0,
                }],
                constant: cert.c[e],
                relation: Relation::NonNeg,
            });
        }

        // 4. Slack sign s_e ≥ 0.
        for e in 0..m {
            constraints.push(Constraint {
                label: "slack_sign",
                terms: vec![Term {
                    var: Var::S(e),
                    coeff: 1.0,
                }],
                constant: 0.0,
                relation: Relation::NonNeg,
            });
        }

        // 5. Dual feasibility π_head − π_tail + s_e − w_e ≥ 0.
        for (e, &(t, h)) in cert.edges.iter().enumerate() {
            constraints.push(Constraint {
                label: "dual_feas",
                terms: vec![
                    Term {
                        var: Var::Pi(h as usize),
                        coeff: 1.0,
                    },
                    Term {
                        var: Var::Pi(t as usize),
                        coeff: -1.0,
                    },
                    Term {
                        var: Var::S(e),
                        coeff: 1.0,
                    },
                ],
                constant: -cert.w[e],
                relation: Relation::NonNeg,
            });
        }

        // 6. Gap Σ c_e s_e − Σ w_e f_e ≤ ε.
        let mut gap_terms = Vec::with_capacity(2 * m);
        for e in 0..m {
            gap_terms.push(Term {
                var: Var::S(e),
                coeff: cert.c[e],
            });
            gap_terms.push(Term {
                var: Var::F(e),
                coeff: -cert.w[e],
            });
        }
        constraints.push(Constraint {
            label: "duality_gap",
            terms: gap_terms,
            constant: 0.0,
            relation: Relation::AtMostEps,
        });

        ConstraintSystem {
            n_vars: 2 * m + n,
            m_edges: m,
            n_nodes: n,
            epsilon: cert.epsilon,
            constraints,
        }
    }

    /// Look up a witness value from the certificate columns.
    fn value(cert: &CertF, var: Var) -> f64 {
        match var {
            Var::F(e) => cert.f[e],
            Var::Pi(i) => cert.pi[i],
            Var::S(e) => cert.s[e],
        }
    }

    /// Evaluate the affine form of a constraint against the witness.
    pub fn eval_expr(cert: &CertF, cons: &Constraint) -> f64 {
        cons.terms
            .iter()
            .map(|t| t.coeff * Self::value(cert, t.var))
            .sum::<f64>()
            + cons.constant
    }

    /// Check every constraint holds against the certificate, at slack `tol`.
    /// This is what the Lean checker proves sound and the AIR enforces per row —
    /// it must accept exactly the certificates `CertF::check` accepts.
    pub fn evaluate(&self, cert: &CertF, tol: f64) -> AirReport {
        let mut violated: Vec<(&'static str, f64)> = Vec::new();
        for cons in &self.constraints {
            let v = Self::eval_expr(cert, cons);
            let ok = match cons.relation {
                Relation::Zero => v.abs() <= tol,
                Relation::NonNeg => v >= -tol,
                Relation::AtMostEps => v <= self.epsilon + tol,
            };
            if !ok {
                violated.push((cons.label, v));
            }
        }
        AirReport {
            n_constraints: self.constraints.len(),
            n_terms: self.constraints.iter().map(|c| c.terms.len()).sum(),
            violated,
        }
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("constraint system serializes")
    }
}

/// The result of evaluating the emitted constraint system against a certificate.
#[derive(Clone, Debug, Serialize)]
pub struct AirReport {
    pub n_constraints: usize,
    pub n_terms: usize,
    /// `(label, evaluated value)` for each violated constraint; empty ⇒ accepted.
    pub violated: Vec<(&'static str, f64)>,
}

impl AirReport {
    pub fn satisfied(&self) -> bool {
        self.violated.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pdhg::{cycle_lp, solve_cpu_exact};

    #[test]
    fn emitted_system_accepts_valid_certificate() {
        let lp = cycle_lp(4, &[4.0, 6.0, 2.0, 8.0], &[1.0; 4]);
        let (exact, _) = solve_cpu_exact(&lp, 10_000);
        let cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
        let sys = ConstraintSystem::emit(&cert);
        // Size is O(m + nnz A): n + 4m + 1 constraints.
        assert_eq!(sys.constraints.len(), lp.n_nodes + 4 * lp.m() + 1);
        let report = sys.evaluate(&cert, 1e-7);
        assert!(
            report.satisfied(),
            "emitted AIR must accept a valid certificate; violated: {:?}",
            report.violated
        );
        // The emitted system agrees with the Rust checker.
        assert!(cert.check_strict().valid);
    }

    #[test]
    fn emitted_system_rejects_tampered_certificate() {
        let lp = cycle_lp(4, &[4.0, 6.0, 2.0, 8.0], &[1.0; 4]);
        let (exact, _) = solve_cpu_exact(&lp, 10_000);
        let mut cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
        cert.f[0] += 1.0; // break conservation + box
        let sys = ConstraintSystem::emit(&cert);
        let report = sys.evaluate(&cert, 1e-7);
        assert!(
            !report.satisfied(),
            "tampered certificate must violate ≥1 constraint"
        );
        assert!(
            report.violated.iter().any(|(l, _)| *l == "conservation"),
            "conservation must be among the violations"
        );
    }

    #[test]
    fn emission_agrees_with_checker_on_boundary() {
        // A not-fully-converged certificate: the emitted system and CertF::check
        // must AGREE on accept/reject at the same tolerance.
        let lp = cycle_lp(4, &[4.0, 6.0, 2.0, 8.0], &[1.0; 4]);
        let (exact, _) = solve_cpu_exact(&lp, 200); // few iters → larger gap
        let cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
        let sys = ConstraintSystem::emit(&cert);
        let air_ok = sys.evaluate(&cert, 1e-7).satisfied();
        let check_ok = cert.check_strict().valid;
        assert_eq!(air_ok, check_ok, "AIR emission and CertF::check must agree");
    }

    #[test]
    fn constraint_system_json_shape() {
        let lp = cycle_lp(3, &[1.0; 3], &[1.0; 3]);
        let (exact, _) = solve_cpu_exact(&lp, 2000);
        let cert = CertF::from_solution(&lp, &exact.f, &exact.y, 0.1);
        let sys = ConstraintSystem::emit(&cert);
        let json = sys.to_json();
        assert!(json.contains("\"conservation\""));
        assert!(json.contains("\"duality_gap\""));
        assert!(json.contains("\"relation\""));
    }
}
