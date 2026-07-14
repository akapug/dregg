# fhEgg — Codex (GPT-5.6-sol) Mathematical Analysis, Captured + Assessed

*Companion to `FHEGG-MATHEMATICAL-BRIEF.md`. This is the captured output of a codex-exec run as a
mathematical analyst on that brief, curated and **honestly assessed** question-by-question — not a
paste. Each subsection states what codex proposed, then my read: **genuinely novel / a real
construction**, **a known result correctly applied**, **a correction to our brief**, or **hand-waving
/ needs verification**. The reusable pattern: brief → codex-analysis → capture+assess.*

**The run.** `codex exec --skip-git-repo-check --sandbox read-only "<full brief> + analyst ask"`,
codex-cli 0.144.1, GPT-5.6-sol. It ran several minutes, did ~40 web searches and read four repo docs
to ground itself, used **291,251 tokens**, and returned a complete, section-organized analysis (log:
`scratchpad/codex-fhegg.log`, final answer block). It engaged adversarially — it opened with seven
load-bearing corrections to our framing before answering, which is the behavior we want.

---

## Headline (the single most valuable insight)

**Certificate-carrying PDHG (`Cert-F`): prove the primal–dual duality gap, not the iteration trace.**
For the volume-max circulation LP `max wᵀf s.t. Af=0, 0≤f≤c`, a dual certificate `(π,s)` with `s≥0`,
`Aᵀπ+s ≥ w` satisfies `wᵀf ≤ cᵀs` for every feasible pair; so the hidden proof checks only

```
  Af = 0,   0 ≤ f ≤ c,   s ≥ 0,   Aᵀπ + s ≥ w,   cᵀs − wᵀf ≤ ε
```

certifying ε-optimality **independent of how `f,π,s` were found**. This collapses proof complexity
from `O(T·m)` clamp/range operations (proving `T` iterations) to `O(m + nnz A)` feasibility
constraints plus the gap inner-products. Codex then generalized it to arbitrary composite convex
programs `min g(x)+h(Kx)` via the **Fenchel gap** `g(x)+h(Kx)+g*(−Kᵀy)+h*(y) ≤ ε`, and proposed
**this be the private-convex compiler's principal IR**.

**Assessment — GOLD, and a clean independent hit.** This is exactly the crux that
`PRIVATE-CONVEX-ENGINE.md` names (convex duality → a self-certifying optimality witness whose gap is a
*linear* functional → run untrusted oblivious search, attest with a cheap linear duality-gap check =
translation validation / dregg's verify-not-find). That doc landed *after* the brief was frozen and
the brief did **not** contain the duality-certificate idea — it only stated the fixed-`T`
operator-splitting thesis. So codex reconstructed the insight **independently from the turn-kernel's
verify-not-find DNA in the brief**, and went *deeper* than our note in three ways: (i) it wrote the
exact `Cert-F` inequalities for the flow LP; (ii) it generalized to the Fenchel/Lagrangian gap for any
composite convex program, making it a compiler IR rather than one trick; (iii) it quantified the
proof-size win (`O(Tm) → O(m+nnz A)`). This is genuine, load-bearing value and it *converges with* our
own frontier doc — strong triangulation that this is the right architecture.

---

## Q1 — Homomorphic-native oblivious splitting method

**What codex proposed.**
- **Incidence-preconditioned PDHG (Chambolle–Pock) for the flow LP.** Saddle form
  `min_f max_y  I_{[0,c]}(f) − wᵀf + ⟨Af,y⟩`; the iteration is `y⁺ = y + ΣAf̄`, `f⁺ =
  clip_{[0,c]}(f + τ(w − Aᵀy⁺))`, `f̄⁺ = f⁺ + θ(f⁺−f)`. Every affine update is homomorphic-linear;
  **exactly one nonlinear layer per iteration** — the coordinatewise box clamp; fixed schedule and
  iteration count; no private pivot/active-set/residual-graph/stopping-time exposed.
- **A topology-only preconditioner.** With `τ = (ρ/2)I`, `Σ = ρD⁻¹` (`D` = vertex-degree matrix),
  `‖Σ^{1/2} A τ^{1/2}‖² ≤ ρ² < 1` because the normalized graph Laplacian has spectral radius ≤ 2.
  **Step sizes depend only on public topology** — no private line search or spectral estimation.
- **Fixed-`T` bound.** Ergodic gap `≤ (‖f−f⁰‖²_{τ⁻¹} + ‖y−y⁰‖²_{Σ⁻¹})/(2T)`; restricted over a public
  dual ball gives `G(f̂_T)−G(f*) + R‖Af̂_T‖ ≤ C_R/T`, so `T ≥ C_R/ε`. Honestly flagged: a
  data-independent `O(log 1/ε)` needs a *public* Hoffman/metric-subregularity bound; without it,
  `O(1/ε)` is the honest generic guarantee.
- **Homomorphic cost table.** ~`7m+n` ciphertext additions + `O(m+n)` public-scalar products per
  iteration, **no ciphertext×ciphertext multiplication**; nonlinear work = `m` clamps. Per regime:
  commitment+hiding-STARK = *zero bootstraps* (clamps proved by range lookups, `O(m)`/iter);
  RLWE/TFHE = ~2–3 PBS-equiv per packed ciphertext; SIMD = `2–3⌈m/s⌉` packed clamps.
- **Fixed-point / modulus discipline.** Pre-clamp affine bound `|u_e^t| ≤ C + ρW/2 + 2ρ²CT`; modulus
  `q > 2S(M_T + Δ_round + Δ_cert)`; precision `s ≥ ⌈log₂(2 C_quant T / ε)⌉` to keep the accumulated
  rounding error under `ε/2`. Lattice-specific: **commit only inputs/outputs, keep intermediate
  iterates under the STARK PCS** — else the homomorphic opening randomness grows with `T` and MSIS
  parameters must be sized to the accumulated opening norm.
- **`Cert-F`** (the headline above).
- **Uniform-price clearing should NOT use PDHG** — the direct histogram-fold + prefix-scan + crossing
  is strictly better; PDHG is for the *fractional circulation*, not the single-pair auction.

**Assessment.**
- The PDHG choice is **a known method correctly and aptly applied** — Chambolle–Pock is the right
  first-order method for `min g + h∘A` with cheap proxes, and its `O(1/T)` rate is textbook. Not novel
  in itself; correctly identified as the best fit (fixed iteration count, sparse `A`/`Aᵀ`, single
  clamp layer) versus simplex/MMCC/interior-point.
- The **topology-only preconditioner** is **genuinely sharp and, as far as I can tell, a real
  contribution in this setting**: exploiting the normalized-Laplacian spectral radius ≤ 2 to set
  oblivious step sizes purely from *public* graph structure is exactly what an oblivious method needs
  (no data-dependent step tuning = no leakage, no padded line-search). This is the cleanest technical
  idea in Q1 after `Cert-F`. It is a specialization of known diagonal PD preconditioning (Pock–
  Chambolle), so "novel application" rather than "novel theorem," but it is the right one and it is not
  obvious. **Worth verifying** the constant (the `≤ 2` bound is for the normalized Laplacian
  `D^{-1/2}(AAᵀ)D^{-1/2}` of the *underlying graph*; the mapping from directed incidence to that form
  should be checked against our actual `A`).
- The **fixed-point/modulus and "commit only endpoints, iterates under the PCS" discipline** is
  **correct, non-obvious, and directly actionable** — it is the honest answer to "does the additive
  homomorphism survive a `T`-fold?" (no, the opening norm blows up; keep the fold inside the STARK).
  This resolves a real question our brief left implicit.
- Honest limitation codex insisted on (correctly): **"one bootstrap per iteration regardless of `m`
  and private caps" is false in general** — heterogeneous private caps need compare+mux, ~2–3
  PBS-equiv per pack; only SIMD packing gets you to `2–3⌈m/s⌉`. Our brief's optimistic "amortize the
  one bootstrap" (Q6 prompt) is thus **tempered by codex** — a useful correction.

**Net for Q1:** `Cert-F` (gold) + the topology-only preconditioner (sharp, real) + the
modulus/opening discipline (correct, actionable). The rest is a correct, well-chosen application of
known first-order optimization. This is a strong, buildable answer to the open question.

---

## Q2 — The categorical / algebraic unification

**What codex proposed.** A single structure:

> a **resource-graded, proof-carrying, guarded traced symmetric monoidal category of open relations**,
> realized concretely by **decorated cospans** — call it `ZKOpenRel_R`, `R = ℤ^Asset` the typed
> resource group.

- **Objects** `X`: typed boundary ports + private state `S_X` + public quotient `q_X : S_X → P_X` +
  resource valuation `ν_X : S_X → R`.
- **Morphisms** `M : X → Y`: an open topology `X → N ← Y`, a private witness space `W_M`, a feasibility
  relation `Γ_M ⊆ S_X×W_M×S_Y`, a guard/fairness predicate, an optional convex cost `φ_M`, a
  **resource defect** `d_M ∈ R`, a public observation, and a proof relation `Verify_M`.
- **Composition** = relational/fiber-product; **defects add**: `d_{N∘M} = d_M + d_N` (and
  `d_{M⊗N} = d_M + d_N` for tensor). **Convex costs compose by infimal convolution**
  `φ_{N∘M}(x,z) = inf_y φ_M(x,y)+φ_N(y,z)` — the Fenchel-duality-respecting composition.
- **Conservation** = the **zero-defect subcategory** `{M : d_M = 0}`. **Ring** = **guarded trace**
  (feedback gluing an output interface to an input, imposing `Af=0`). **Optimization** = partial
  minimization. **Fairness** = a separate subrelation `Fair_M ↪ Γ_M` (explicitly *not* implied by
  conservation). **Privacy** = simulator natural transformation `View ≈ Sim∘Q` (statistical for the
  PCS layer, quantum-computational for the whole system because nullifier-unlinkability and
  hash-hiding are computational). **Validity reflection**: `Verify(π)=1 ⇒ ∃w. Γ_M(w) ∧ d_M(w)=0 ∧
  Fair_M(w)`.
- **The four requested instances** land as: turn-kernel = guarded proof-carrying endomorphism
  `T:S→S`, history `= T_n∘…∘T_1`; auction = orders merged by a **commutative Frobenius/monoid
  multiplication** `μ^{(N)} : C^{⊗N}→C` then a crossing observer `χ:C→P`; circulation = open-network
  morphism with witness-flow grade `Af`, zero-grade fiber `= ker A`, ring = trace; convex engine =
  public-instance-indexed endomorphism `U_θ:Z→Z`, fixed solver `U_θ^T`, semantic target an `Argmin`
  relation related by a **certificate/refinement 2-cell**.
- Honest evaluation of every candidate lens (chain complexes = best for conservation/flows but blind to
  authorization/optimization/privacy; traced monoidal = best skeleton but needs guards+grading;
  sheaves/topoi = only for genuine gluing questions, "mint is a degree-0 defect, not canonically a
  nonzero `H¹`"; tropical = shortest-path only; lenses/optics = good local turn semantics, weak global
  unifier). **Decorated cospans + guarded trace + resource grading = the smallest covering structure.**
- Named the **genuinely new mathematics**: not another adjunction slogan but the *compositionality
  theorem* for the combined resource-grade + convex-cost decoration + recursive-proof functor +
  computational-privacy simulator — **especially closure under feedback and adaptive sequential
  composition.**

**Assessment.**
- This is a **serious, coherent, and mostly-correct categorical proposal**, not a buzzword salad. The
  central moves are right and non-trivial:
  - **Decorated cospans** (Fong) genuinely *are* the standard machinery for open compositional systems
    with a special-commutative-Frobenius interface, and the auction-as-Frobenius-merge instance is apt
    (a commutative monoid multiply with a compatible comultiply/unit is exactly the "aggregate many
    into one, split one into many" structure a call auction and a shielded split/merge both need).
  - **"Resource defect `d_M` that adds under both composition and tensor, with conservation = the
    zero-defect subcategory"** is the correct categorical home for our `toBal`-homomorphism (T1) and
    `created_value_conservation` (T4). This is a real, checkable claim: `d` is a *strong monoidal
    functor to `(R,+,0)`* and conservation is `d⁻¹(0)`. It matches our Lean exactly and is the
    cleanest categorical statement of "the fold commutes with the measurement."
  - **Convex costs compose by infimal convolution** is the right and elegant fact (it *is* how Fenchel
    conjugation interacts with composition), and it ties Q2 back to the `Cert-F` duality of Q1 — the
    two answers are consistent, which is a good sign.
  - **Guarded trace for the ring** is the correct and honest refinement of "ring = feedback": codex
    explicitly warns that **an ordinary trace/compact-closure does *not* guarantee a feasible witness
    exists** — "tracing a relation can produce the empty relation; it wires a cycle, it does not prove
    the cycle clears." This is precisely the distinction our `shielded_ring_clears` non-vacuity teeth
    encode, and it kills the naive "just take the trace" temptation.
  - **Privacy as a simulator natural transformation `View ≈ Sim∘Q`** is the right categorical shape
    for the reveal-nothing theorem, and it *correctly predicts* our Component-3 crux: it forces the
    honest statement to be over a **leakage functor `Q`**, not "transcript independent of trades."
- **Corrections to our brief that I accept:**
  1. **The crossing is not automatically a Tarski fixpoint** just because the curves are monotone —
     you must define the update `F(j) = j if D(p_j)≤S(p_j) else min(j+1,K)` and take the least fixed
     point *assuming a crossing exists*. Our brief and `FHEGG-KERNEL.md` were loose here ("the Tarski
     fixpoint on the price chain"); codex is right that monotonicity of the curves ≠ monotonicity of
     the operator whose fixpoint is the crossing. Minor but worth fixing in the kernel doc.
  2. **A commitment functor cannot literally be both "faithful on conservation" and "trivial on
     values"** — hiding *intentionally* identifies value-distinct worlds observationally. The honest
     split: computational binding *reflects bounded resource equalities*; hiding makes same-leakage-
     class openings indistinguishable. This corrects a sloppy phrasing in the brief's Q2 prompt.
- **Where it is a program, not a theorem (honest limit):** codex is candid that the *new* content is
  the compositionality/closure theorem for the combined structure — and it does **not** prove it. So
  Q2's deliverable is a **well-posed research target with the right objects/morphisms/functors named**,
  not a finished unification. That is genuinely valuable (it tells us what to prove and in what
  category), but it should not be over-sold as "the unification is done." **Needs real work to
  discharge** — the feedback+adaptive-composition closure is exactly where categorical DeFi models
  tend to break.

**Net for Q2:** a **real, novel-in-assembly categorical proposal** (decorated cospans + guarded trace
+ resource grading + convex-cost decoration + proof/privacy functors) that (i) correctly recovers all
four of our objects as instances, (ii) matches the already-proved Lean at the conservation layer,
(iii) makes two correct corrections to our framing, and (iv) honestly isolates the one theorem that
needs proving. This is the deepest answer after `Cert-F` and it is the right skeleton — the individual
pieces are known category theory, but the *specific combination targeted at proof-carrying private
clearing* is a genuine contribution.

---

## Q3 — The oblivious private-LP frontier

**What codex proposed.** (i) **Exact all-or-nothing *selection* is NOT the easy case** — choosing a
max-volume balanced *subset* of all-or-nothing orders is `max Σ w_i x_i s.t. Σ x_i a_i = 0, x_i∈{0,1}`,
a 0-1 balancing problem that **can encode subset-sum / set-packing (NP-hard)**; a public topology does
not remove the integrality. Partial fills `x_i∈[0,1]` are exactly what *create* the tractable LP.
(ii) For continuous partial fills, **PDHG-F beats simplex/MMCC/interior-point** for obliviousness
(fixed public iteration count, sparse `A/Aᵀ`, one packed clamp/iter, `O(m/ε)` linear work). Use `A`
directly, **not** an explicit cycle basis (a fundamental cycle basis can be dense/ill-conditioned and
enlarges fixed-point bounds). (iii) For *integer* flow with an ordinary incidence matrix, **total
unimodularity** gives an integral LP optimum for free (not so for weighted stoichiometric `A`); a
padded **Goldberg–Tarjan cost-scaling** schedule is a better polynomial oblivious fallback than
oblivious simplex. (iv) Sharp **leakage profile** (leaks public matrix, `n,m`, batch size, bit widths,
public `T`, the chosen public output; hides caps/weights/residual-graph/active-set/pivots/stopping
iteration/individual flows) with the caveat that **memory access must be static** (fixed loop with
secret-indexed RAM is not oblivious). (v) **Define "volume" carefully** — `max Σ f_e` biases toward
long cycles; use numeraire-normalized `max wᵀf` or count intent quantities at source legs only.

**Assessment.** **Mostly known results, assembled correctly and honestly — with one important
correction to us.** The **all-or-nothing-selection-is-NP-hard** point is a **genuine and important
correction to our brief and `FHEGG-KERNEL.md`**, which repeatedly imply "exact intents → free
conservation check, only partial-fill is the frontier." That is true for a *fixed* book (T3), but
**choosing the best exact subset is integer-hard** — the tractability comes specifically from the
`[0,1]` relaxation. We should thread this distinction through the kernel doc. TU-integrality, cost-
scaling, and the leakage/obliviousness caveats are known but correctly applied; "use `A` not a dense
cycle basis" is a **practically sharp** and correct efficiency call that also corrects our brief's
framing (we leaned on the public cycle basis `B`; codex says the incidence `A` is the better object —
sparser, better-conditioned, keeps the traversal public). Net: **high-value corrections, correct
engineering judgment, low novelty.**

---

## Q4 — The PQ lattice-additive homomorphic fold

**What codex proposed.** A sound BDLOP-style template `Com(v;r) = Ar + Gv mod q` over
`R_q = ℤ_q[X]/(Xⁿ+1)`, additively homomorphic, binding = Module-SIS **provided the matrix distribution
and binding set match an actual reduction** ("one must not simply name an arbitrary `g` and declare
MSIS binding"), hiding = a *separate* MLWE/leftover-hash argument (not implied by binding). Aggregation
**changes the binding radius**: `r_agg = Σ r_i` has norm `O(σ√N)` (heuristic) or `O(Nβ)` (worst-case),
so MSIS parameters must use the *aggregate* radius. In-AIR verification of `Ar` is **not cheap just
because it's linear** — NTT `O(kℓn log n)` field ops + `O(ℓn)` range checks + coefficient reductions +
foreign-field carries unless `q = p_AIR`; a commitment of `k` ring elements is `≈ k·n·⌈log₂ q⌉` bits
(~2 KiB for `n=256,k=2,q≈2³¹`), so **the kilobyte cost is structurally real**. Verdict: **Option A
(hash-commitment + in-AIR field conservation) is strictly cleaner when all legs share one clearing
AIR**; the true lattice homomorphism earns its cost **only** when independent parties must aggregate
*asynchronously before a common proof exists* (a precise five-item list). Best hybrid: **lattice
commitments at ingress, aggregate publicly, then one per-batch bridge proof opens `C` to the private
aggregate used by the Poseidon/STARK clearing** — pay lattice arithmetic once per batch, not per leg.
Also: **a single ~31-bit BabyBear field output is not a 128-bit PQ commitment** — expose ≥256-bit
(eight-limb) digest.

**Assessment.** **Correct, current, and precisely the right engineering verdict — known crypto,
applied with care.** BDLOP is indeed the right starting point; the insistence that (a) binding needs a
real reduction not a named generator, (b) hiding is a *separate* theorem, and (c) the **aggregate**
opening radius (not the per-order one) governs MSIS parameters are all correct and are exactly the
traps a careless design falls into. The **"lattice at ingress, bridge once per batch, hash/STARK for
the rest"** hybrid is a **genuinely good architectural answer** to "when does the homomorphism earn
its kilobytes" — it isolates the *one* thing a true homomorphism buys (asynchronous cross-prover
aggregation) and quarantines its cost. This confirms and sharpens `PQ-SHIELDED-COMMITMENT.md`'s
Option-A-dominates verdict, and the ≥256-bit-digest catch is a concrete fix to our current
`value_binding`. **High practical value, correctly grounded, low novelty (as expected for Q4).**

---

## Q5 — Intricate private financial products

**What codex proposed.** The standout: an **influence-bounded private mark**. Each order carries an
inventory/collateral-capped influence weight `a_i`; the mark solves
`p† = argmin_p Σ a_i ρ_δ(p−ℓ_i) + (μ/2)(p−p₀)²` (Huber loss `ρ_δ`, `p₀` a lagged reference). Because
`|ρ_δ'| ≤ δ` and the objective is `μ`-strongly convex, **any coalition locking ≤ `A_adv` influence
moves the mark by at most `|Δp†| ≤ 2 A_adv δ / μ`** — a *publicly bounded* manipulation guarantee.
Then: **private risk-constrained clearing** (`max wᵀf − (λ/2)‖Lf‖² s.t. Af=0, 0≤f≤c, CVaR_α(−Rf)≤R₀`,
with CVaR's polyhedral epigraph adding only linear maps + ReLU proxes); **private portfolio/basket
rebalancing** as a QP (soft-threshold + box clamp — fits PDHG almost exactly); **private optimal
execution** over a fixed horizon (banded/tridiagonal public system + small box proxes); **private
multi-CFMM routing** (convex without gas/activation costs, MICP with them — cites Angeris et al.);
**private restricted-language Walrasian auctions** (tractable exactly at the gross-substitutes
boundary — cites Paes Leme–Wong). The genuine novelty is the **composition**: no-viewer encrypted
witness-finding + a mechanism-specific convex language + exact conservation/authorization at
settlement + a succinct primal-dual certificate + recursive proof aggregation + an explicit leakage
theorem + an economic influence bound.

**Assessment.** The **influence-bounded mark is the genuinely novel and valuable product idea here** —
and it directly answers a real hole codex itself flagged (a uniform-price mark is *not* automatically
manipulation-resistant). The `|Δp†| ≤ 2A_adv δ/μ` bound is a **clean, correct, and mechanism-
meaningful** sensitivity result: Huber-loss bounded gradient × strong-convexity modulus = Lipschitz
stability of the argmin in the adversarial weight, a standard perturbation argument, **correctly
instantiated into a manipulation theorem**. It converts "private ⇒ manipulation-resistant" (which we
overclaimed) into "private removes reactive spoofing; the *collateral-weighted strong-convex mark*
bounds endogenous manipulation" — a defensible, provable statement and a real product. **Verify the
constant** (addition vs replacement of adversarial orders changes it, as codex notes). The rest are
correct convex formulations of known mechanisms mapped onto the PDHG engine — good menu, mostly known,
with the honest MICP boundary for fixed costs. **Influence-bounded mark = novel and worth building;
the rest = a solid, correctly-typed product catalog.**

---

## Q6 — Efficiency

**What codex proposed (ranked).** (1) **Prove the certificate, not the solve** (`O(Tm)→O(m+nnz A)`;
Fenchel gap as the compiler IR — the Q1 headline, restated as the top efficiency win). (2) **Boundary
histograms** — a step curve is one boundary event, so aggregate boundary histograms then prefix/suffix
scan: `O(NK)→O(N+K)` scalar arithmetic (given secret-bucket insertion via one-hot proofs / packing /
DPFs / private proving). (3) **Dyadic crossing** — segment tree over the imbalance histogram finds the
first crossing in `O(log K)` comparisons (in a STARK witness; in FHE either oblivious tree-selection
or progressive-bit decryption of `p*`); two-pass coarse/fine `O(K/B+B)`, `B≈√K` gives `O(√K)`.
(4) **SIMD-pack the full curve** — `O(N⌈K/s⌉)` ciphertext additions, prefix scans by rotations in
`O(log K)` depth. (5) **Don't materialize a dense cycle basis** — use `A/Aᵀ`; if you need
`P_{ker A} = I − Aᵀ(AAᵀ)⁺A`, exploit public topology for offline Laplacian preconditioning / sparse
Cholesky / spectral sparsification. (6) **Batch independent markets as a direct sum** `A = ⊕ A_j`,
sharing trace commitments / FRI queries / Poseidon permutations / range tables in one recursive STARK.
(7) **Amortize marginal rationing** via quotient-remainder proofs `q_i R = Q x_i + r_i` + Montgomery
batch inversion (or a VRF-ranked unit lottery to avoid private division). (8) **CRT/RNS** helps exact
64-bit sums but **not comparisons** (order/sign aren't componentwise in residues). (9) **NTT is not a
first-order win** for the auction fold (it's histogram-add + prefix-scan, not convolution) — reserve
NTT for lattice-commitment multiply / batch-eval / convolutional risk models.

**Assessment.** **A strong, correctly-prioritized efficiency menu — mostly known techniques with
excellent judgment about which apply and which don't.** The **`O(NK)→O(N+K)` boundary-histogram**
reduction is the sharpest concrete win and is correct (with the honestly-named caveat that secret
bucket insertion isn't free — the real cost migrates into the one-hot/DPF/packing choice). Dyadic /
`O(√K)` crossing and direct-sum recursive batching are correct and directly actionable. The two
**"don't" corrections are the most valuable part**: **don't materialize a dense cycle basis** (use
`A`) and **CRT/RNS does not make comparisons free / NTT is not a fold win** — these correct exactly the
kind of cargo-cult "throw NTT/CRT at it" our Q6 prompt fished for. Low novelty, high correctness, real
prioritization value.

---

## Overall honest read — did codex add genuine novel value?

**Yes — decisively, and its strength (novel math) is where it delivered.** Concretely:

1. **`Cert-F` / certificate-carrying PDHG (Q1, Q6#1) — GOLD.** The single most valuable output: it
   independently reconstructed the duality-certificate crux (which our just-landed
   `PRIVATE-CONVEX-ENGINE.md` names), wrote the exact certificate, generalized it to the Fenchel gap as
   a *compiler IR*, and quantified the `O(Tm)→O(m+nnz A)` win. Independent convergence on our own
   frontier = the strongest possible validation that this is the right architecture.
2. **The categorical unification (Q2) — real and the right skeleton.** `ZKOpenRel_R` = resource-graded
   proof-carrying decorated cospans + guarded trace + convex-cost decoration, with conservation = the
   zero-defect (strong-monoidal-functor kernel) subcategory, ring = guarded trace, privacy = simulator
   natural transformation. It recovers all four objects, matches the proved Lean at the conservation
   layer, and isolates the one open theorem (feedback + adaptive-composition closure). Novel in
   assembly; the individual pieces are known category theory.
3. **The topology-only PDHG preconditioner (Q1)** and **the influence-bounded private mark with the
   `2A_adv δ/μ` manipulation bound (Q5)** are two smaller but genuinely-novel, concrete, provable
   constructions.
4. **Seven load-bearing corrections to our framing** (netting is quotient by `ker ∂` giving `im ∂`,
   *not* by `im ∂ᵀ` = the cut space; cross-asset needs a *typed stoichiometric* matrix, not plain
   incidence, for the homology to hold; hash-commitment hiding needs more than CR; additive commitment
   ≠ encryption so "no-viewer" needs FHE/MPC/distributed-proving and is a *different regime* from
   "transcript-private one-prover"; exact-subset *selection* is NP-hard, only the `[0,1]` relaxation is
   the tractable LP; the crossing is not automatically a Tarski fixpoint; a ~31-bit field output is not
   a 128-bit PQ commitment). Several of these should be threaded back into `FHEGG-KERNEL.md` and the
   brief — they are correct and we were loose.

**Where it is *not* magic (honest):** Q3–Q4–Q6 are predominantly **known results applied with good
judgment**, not new theorems — which is the correct outcome for those questions (they asked for the
best *existing* construction). Q2's unification is a **well-posed program, not a discharged proof** —
the hard compositionality theorem is named, not proven. And codex's most useful service throughout was
**adversarial precision** (killing our over-optimistic "one bootstrap regardless of `m`", "exact
intents are free", "private ⇒ manipulation-resistant", "trace = clearing") rather than fireworks.

**Verdict:** codex delivered **genuine novel value on exactly the two questions that mattered most**
(the splitting method and the categorical unification), independently hit our own duality-certificate
crux and went deeper, contributed two further concrete constructions, and corrected seven real
framing errors. This is **not mid** — it is a high-value second brilliant mind on the hard open
constructions, and the brief → codex → capture+assess pattern paid off. The immediate build
consequences: (i) make `Cert-F`/Fenchel-gap the private-convex proof IR (converges with
`PRIVATE-CONVEX-ENGINE.md`); (ii) adopt the topology-only preconditioner + the commit-endpoints /
iterates-under-PCS discipline; (iii) target `ZKOpenRel_R` as the categorical frame and prove the
feedback-closure theorem; (iv) fold the seven corrections into `FHEGG-KERNEL.md`.

---

*Provenance: full codex output at `scratchpad/codex-fhegg.log` (final answer block ~L5728–6757;
291,251 tokens; codex-cli 0.144.1 / GPT-5.6-sol; `--sandbox read-only`). Literature codex cited and I
did not re-verify line-by-line (flag for a proof pass): Fong decorated cospans (arXiv 1502.00872),
Joyal–Street–Verity traced monoidal, Chambolle–Pock + Pock–Chambolle preconditioning, BDLOP lattice
commitments (ePrint 2016/997) + Baum et al. lattice ZK (CRYPTO 2018), Goldberg–Tarjan cost-scaling,
Aly–Van Vyve secure network flow, Angeris–Chitra–Evans–Boyd CFMM routing (arXiv 2204.05238), Paes
Leme–Wong Walrasian, Stein–Samuelson compositional convex analysis (arXiv 2312.02291).*
