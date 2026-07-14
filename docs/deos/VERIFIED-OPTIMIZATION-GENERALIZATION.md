# Verified (Private) Optimization — the engine generalizes past LP/clearing

*Companion to `PRIVATE-CONVEX-ENGINE.md` and `NOVELTY-AND-PAPER-ASSESSMENT.md`. The private
convex engine doc showed the LP / convex-QP / equilibrium slice — programs whose optimality
witness is a **duality gap**. This doc states the general frame the slice sits inside: the engine
is **verify-not-find over an optimization CLASS, one certificate per class**, and clearing is one
instantiation. It records the smooth-convex/SGD generalization (built, `fhegg-solver/src/smooth.rs`)
and names the SDP axis. What-is, present tense; every claim carries its honest grade.*

---

## 0. The claim, and what is and is not ours

**The engine is a general verified-(private-)optimization substrate. A market clearing is one
application of it.** The substrate is *verify-not-find*: an untrusted solver proposes a candidate,
a per-class certificate disposes it, and the checker validates the certificate — never the solver's
search. Different optimization classes carry different certificates; the engine is the pattern, not
one rule.

**Honest attribution — this FOLLOWS Otti, it does not invent verify-not-find.** Otti
(Angel–Blumberg–Ioannidis–Woods, *Efficient Representation of Numerical Optimization Problems for
SNARKs*, USENIX Security 2022) is a SNARK compiler that proves the optimality of **LP, SDP, and SGD**
programs via weak-duality / stationarity certificates — "use the solver to find the witness, encode
the *certificate*, not the solver." That is exactly verify-not-find, and its breadth is already
**LP + SDP + SGD** (`NOVELTY-AND-PAPER-ASSESSMENT.md` row 3, verdict **KNOWN**). Certifying-algorithms
(McConnell–Mehlhorn–Näher–Schweitzer 2011) and certified-LP (Cheung–Gleixner–Steffy, IPCO 2017) are
older still. **We claim none of this as novel.** Our engine was, until this note, only the *convex
slice* (LP / convex-QP / Fisher / package). ember's generalization insight is that the same engine
reaches the rest of Otti's breadth — and the point of building it is to show the substrate is
general, honestly.

**What WE add (the defensible part, per `NOVELTY-AND-PAPER-ASSESSMENT.md` §2):** (1) the **privacy**
carrier — the oblivious-fold / reveal-nothing / MPC discipline extends to each class (Otti is a proof
system, not a private one); (2) **formal verification** — the certificate checker is (headed to be)
Lean-verified, not just a circuit. Neither is a new optimization primitive; both are the combination
+ engineering contribution the assessment already scoped.

---

## 1. The engine — verify-not-find over a class, certificate per class

A verified optimization is a pair *(untrusted solver, checked certificate)* for an optimization
**class**. The solver is out of the trusted base; the certificate is the whole of the trust. Each row
below is a class the engine certifies today (or names next), with the file that carries it.

| Class | Program | Certificate (the checked object) | Grade | File |
|---|---|---|---|---|
| **LP / circulation** | `max wᵀf s.t. Af=0, 0≤f≤c` | duality gap `cᵀs − wᵀf ≤ ε` + primal/dual feas (`Cert-F`, LINEAR) | built | `pdhg.rs`, `cert.rs` |
| **Convex QP** | `min ½xᵀPx+qᵀx s.t. l≤Ax≤u` | KKT residual `‖Px+q+Aᵀy‖ + feas ≤ ε` (`CertQp`) | built | `qp.rs` |
| **Pay-as-bid LP** | gains-from-trade winner-determination | 2-node flow-LP duality (`Cert-F` reuse) | built | `discriminatory.rs` |
| **Fisher / equilibrium** | `max Σ bᵢ log Uᵢ s.t. supply` | competitive-equilibrium KKT (`βu≤p`, CS ≈ 0; `CertEq`, bilinear) | built | `fisher.rs` |
| **CFMM routing** | `max Σ gᵢ(δᵢ) s.t. Σδ≤Δ` | water-filling KKT (`CertRoute`) | built | `cfmm.rs` |
| **Combinatorial 0/1** | `max Σ vᵢxᵢ s.t. Σdᵢxᵢ≤s, x∈{0,1}` | feasible integral `x` + weak-dual bound `W ≤ UB(y)` (`CertPackage`, certified approx) | built | `package.rs` |
| **Smooth-convex / SGD** | `min f(x)`, `f` `μ`-strongly convex + smooth | gradient norm `‖∇f(x)‖ ≤ ε` + bound `f(x)−f* ≤ ‖∇f‖²/(2μ)` (`CertGrad`) | **built (this note)** | `smooth.rs` |
| **SDP** | `min ⟨C,X⟩ s.t. ⟨Aᵢ,X⟩=bᵢ, X⪰0` | dual PSD slack `C − Σyᵢ Aᵢ ⪰ 0` + gap `⟨C,X⟩−bᵀy ≤ ε` | **named next** | — |

The first six rows are the *duality-gap* family (LP/QP/equilibrium): a primal-dual pair whose gap is
a linear-or-bilinear functional. The smooth-convex row is a **different certificate shape** — no dual
variable at all, just the gradient — which is why it is the load-bearing generalization: it shows the
engine is not "a duality-gap checker" but "verify-not-find, whatever the class's certificate is."

---

## 2. The smooth-convex / SGD generalization (built)

`fhegg-solver/src/smooth.rs` carries the second verify-not-find axis.

**The program.** A concrete smooth convex objective — ridge-regularized least squares
`f(x) = (1/2m)‖Ax−b‖² + (μ/2)‖x‖²` (equivalently a private tracking-error portfolio: track a
benchmark `b` under an L2 mandate), and an L2-regularized logistic objective. The ridge coefficient
`μ > 0` is **public** (part of the program form). The Hessian `∇²f = (1/m)AᵀA + μI ⪰ μI`, so `f` is
`μ`-strongly convex for ANY data — `μ` is a genuine curvature floor, not an estimate.

**The solver (untrusted).** Full-batch gradient descent (fixed-`T`, data-independent step `η = 1/L`
— the oblivious first-order shape of `PRIVATE-CONVEX-ENGINE.md §2.2`) and minibatch **SGD** (a
stochastic search). Both are out of the trusted base.

**The certificate (`CertGrad`).** The solver emits its achieved point `x` — NOT its trajectory. The
certificate is near-stationarity `‖∇f(x)‖ ≤ ε`. For a `μ`-strongly-convex `f`, the standard
**gradient-domination (Polyak–Łojasiewicz) bound** turns this into a suboptimality guarantee:

```
   f(x) − f*  ≤  ‖∇f(x)‖² / (2μ).
```

*Proof.* `μ`-strong convexity gives `f(z) ≥ f(x) + ⟨∇f(x), z−x⟩ + (μ/2)‖z−x‖²` for all `z`;
minimising the RHS over `z` (at `z = x − ∇f(x)/μ`) gives `f* ≥ f(x) − ‖∇f(x)‖²/(2μ)`. ∎ No diameter
bound, no knowledge of `x*`. So `‖∇f(x)‖ ≤ ε` certifies `f(x) − f* ≤ ε²/(2μ)`, **independent of how
`x` was found**. `CertGrad::check` re-derives `∇f(x)` from the public program from scratch — it reads
the achieved point, never the SGD path. Verify-not-find.

**Both polarities (genuine, tested).** A converged (S)GD point certifies; the benchmark brackets it
against the closed-form ridge optimum (`f(x)−f*` sits under `‖∇f‖²/(2μ)` in every row). A
far-from-stationary point (`x = 0` on a non-trivial instance, `‖∇f‖ ≈ 0.89`) fails a tight `ε`, and a
tampered point (converged, then `x₀ += 1`) recomputes a large gradient and is **rejected** — the
checker recomputes `∇f` so a lie about `x` cannot pass. 7 module tests + a benchmark
(`--bin smooth-bench`).

**⚠ The non-convex caveat (real, stated prominently).** The gradient certificate is a **stationarity**
certificate. For a `μ`-*convex* `f` (this module), stationary ⇒ global-optimal, so it is a genuine
near-optimality certificate. For a **non-convex** `f` (a real neural net), `‖∇f(x)‖ ≤ ε` certifies
only that `x` is a near-**stationary point** — a local critical point — NOT that `f(x)` is near the
global optimum, and NOT that the model is good. The convex suboptimality bound holds ONLY under the
convexity this module enforces. This is the honest boundary between "verified optimization" (this
engine) and "verified ML quality" (not claimed).

---

## 3. The SDP axis (named next)

The second generalization axis, not yet built, stated so the frame is complete. A semidefinite
program `min ⟨C,X⟩ s.t. ⟨Aᵢ,X⟩ = bᵢ, X ⪰ 0` is certified by a **dual PSD certificate**: a dual `y`
with the slack matrix `S = C − Σᵢ yᵢ Aᵢ ⪰ 0` (dual feasibility = a positive-semidefinite check, e.g.
a Cholesky / eigenvalue witness) and gap `⟨C,X⟩ − bᵀy ≤ ε`. Weak duality gives `bᵀy ≤ ⟨C,X⟩` for any
dual-feasible `y`, so the gap certifies ε-optimality — the exact `Cert-F` move with the LINEAR
`s ≥ 0` inequality replaced by the CONE inequality `S ⪰ 0`. This is the third of Otti's three classes
(LP, SDP, SGD); building it closes the engine onto Otti's full breadth. Grade: named, a spanning-axis
follow-up, not a banked result.

---

## 4. Clearing is one app — and the ML north star

**Clearing is one instantiation.** A uniform-price call auction is the `T=1` LP degenerate case
(`FHEGG-KERNEL.md`); the circulation LP, the Fisher equilibrium, the package auction are further
classes. They are *applications* of verify-not-find, each with its certificate. The engine is the
substrate; clearing is one product surface on it.

**The frontier app — verified private SGD → verified private ML.** The smooth-convex axis is the
on-ramp to the north star: **verified-private-SGD → verified-private-ML → the dark-model direction**.
The same engine (oblivious first-order search + a checked certificate) over the same private substrate
(MPC/FHE fold, reveal only the certified output) certifies that a training computation *ran correctly
and reached a certified point*, revealing nothing but that fact. Honestly graded:

- **What this earns:** a *correctness* + *stationarity* certificate for a private training run — the
  computation was faithful and reached a certified (stationary, for convex: optimal) point, with the
  data never revealed. For convex models (ridge/logistic/linear) it is a genuine near-optimality
  certificate today.
- **What it does NOT earn (the caveat, again):** for a non-convex net, `‖∇f‖ ≤ ε` is a **stationary
  point**, not the global optimum and not model quality. "Verified private ML" here means *verified
  correct computation reaching a certified stationary point*, NOT *verified the model is good*. That
  distinction is the whole honesty of the claim.
- **Otti already spans SGD.** Proving SGD stationarity in a SNARK is Otti's, not ours. Ours is the
  privacy carrier + the formal checker on top.

---

## 5. Honest summary

- **Verify-not-find is Otti's** (USENIX Security 2022), breadth **LP + SDP + SGD**; certifying
  algorithms are decades old. We claim no novelty in the technique or the breadth.
- **The engine now demonstrably certifies smooth-convex / SGD** (`smooth.rs`, `CertGrad`): a real
  gradient-norm near-stationarity certificate with the convex suboptimality bound
  `f(x)−f* ≤ ‖∇f‖²/(2μ)`, both polarities genuine, benchmarked, bracketed against ground truth. This
  is a class the engine reaches PAST LP/clearing.
- **What WE add:** privacy (the reveal-nothing / MPC discipline extends per class) + formal
  verification (the Lean checker). Combination + engineering, not a new primitive — exactly as
  `NOVELTY-AND-PAPER-ASSESSMENT.md` §2 scopes.
- **The non-convex caveat is load-bearing:** the gradient certificate is stationarity, not
  optimality; for real (non-convex) ML it certifies a correct computation reached a critical point,
  never model quality.
- **Clearing is one application** of a general verified-(private-)optimization substrate; the SDP axis
  is named as the next span onto Otti's full breadth; the ML north star is the frontier app.
