/-
# `Dregg2.Crypto.OneWayToHiding` — the One-Way-to-Hiding (O2H) lemma, PROVED from primitives.

Built on the Mathlib-grounded QROM model of `Dregg2.Crypto.QuantumOracle` (states = `EuclideanSpace ℂ B`,
unitaries = `LinearIsometryEquiv`, the reprogrammed-oracle difference packaged as `OracleDiffData`). No
quantum-specific infrastructure — just norms, isometries, triangle inequality, and Cauchy–Schwarz.

## The q-query adversary and Born-rule advantage

A `q`-query adversary is a state `ψ₀`, a threshold `q`, and a family of unitaries `U : ℕ → Unitary B`
interleaved with `q` oracle applications:
`A^O(ψ₀) = U_q (O (U_{q-1} (O (… (U_0 ψ₀)))))` — modeled by `Adversary.state`/`Adversary.run`.
Measurement is the Born rule: with an output projector `P₁` (`‖P₁ v‖ ≤ ‖v‖`), the *amplitude* is
`amp O := ‖P₁ (A^O ψ₀)‖` and the *probability* `bornProb O := ‖P₁ (A^O ψ₀)‖²` (`bornProb_eq_amp_sq`).
The advantage is `|amp_H − amp_{H'}|`.

## The three-step O2H skeleton (each proved)

1. **`oracle_diff_on_S`** — `‖O_H v − O_{H'} v‖ ≤ 2 ‖P_S v‖`: from the FACTORIZATION `(O_H − O_{H'}) =
   (O_H − O_{H'}) ∘ P_S` (`OracleDiffData.factor`, discharged concretely in `QuantumOracle.oracleDiff`),
   each oracle being an isometry, the difference is bounded by `2×` the `S`-amplitude.
2. **`hybrid_telescope`** — with hybrids `mixOracle` running `O_H` for the first `j` queries and `O_{H'}`
   after, adjacent hybrids differ by ONE oracle swap at query `j` (`hybrid_step`, via the propagation
   lemma `Adversary.propagate`: the surrounding unitaries preserve norm). Telescoping (`Finset.sum_range_sub`
   + triangle inequality `norm_sum_le`) gives `‖A^{O_H} − A^{O_{H'}}‖ ≤ ∑ₖ ‖(O_H − O_{H'}) ψₖ‖`.
3. **`cauchy_schwarz_queries`** — `∑ₖ ‖P_S ψₖ‖ ≤ √(q · ∑ₖ ‖P_S ψₖ‖²)`: Mathlib's power-mean
   `sq_sum_le_card_mul_sum_sq` (the SAME core as `HermineTSUF.forking`), now over ℝ≥0 amplitudes.

## Headline `o2h_bound`

`|amp_H − amp_{H'}| ≤ 2 · √(q · Pfind)`, with `Pfind := ∑ₖ ‖P_S ψₖ‖²` the semiclassical find probability.
This is the foundation the FO-QROM bookkeeping (ML-KEM IND-CCA) rides on. No `sorry`, `#assert_axioms`-clean.
-/
import Dregg2.Crypto.QuantumOracle
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Sqrt

open scoped BigOperators
open Dregg2.Crypto.QuantumOracle

namespace Dregg2.Crypto.OneWayToHiding

variable {B : Type*} [Fintype B]

/-! ## Step 1 — the oracle-difference bound. -/

/-- A unitary preserves the norm of a difference: `‖U a − U b‖ = ‖a − b‖` (it is linear + norm-preserving).
The workhorse for propagating a state-difference through the surrounding adversary unitaries. -/
theorem unitary_norm_sub (U : Unitary B) (a b : QState B) : ‖U a - U b‖ = ‖a - b‖ := by
  rw [← map_sub, U.norm_map]

/-- **`oracle_diff_on_S` (O2H Step 1).** From the factorization `(O_H − O_{H'}) = (O_H − O_{H'}) ∘ P_S`
(the two oracles agree off the reprogramming set), and each oracle being an isometry, the oracle difference
is bounded by twice the `S`-amplitude: `‖O_H v − O_{H'} v‖ ≤ 2 ‖P_S v‖`. -/
theorem oracle_diff_on_S (D : OracleDiffData B) (v : QState B) :
    ‖D.O v - D.O' v‖ ≤ 2 * ‖D.P v‖ := by
  rw [D.factor v]
  calc ‖D.O (D.P v) - D.O' (D.P v)‖
      ≤ ‖D.O (D.P v)‖ + ‖D.O' (D.P v)‖ := norm_sub_le _ _
    _ = ‖D.P v‖ + ‖D.P v‖ := by rw [D.O.norm_map, D.O'.norm_map]
    _ = 2 * ‖D.P v‖ := by ring

/-! ## The q-query adversary and its run under a per-query oracle choice. -/

/-- A **`q`-query adversary**: an initial state `ψ₀`, a query budget `q`, and a family of unitaries `U`
(only `U 0 … U q` are used). The run interleaves `U` with `q` oracle applications. -/
structure Adversary (B : Type*) [Fintype B] where
  /-- The query budget. -/
  q : ℕ
  /-- The adversary's own unitaries (work-register operations), `U 0 … U q`. -/
  U : ℕ → Unitary B
  /-- The initial state. -/
  ψ₀ : QState B

/-- **The state after `k` oracle queries**, given a per-query oracle choice `O` (with `O k` the oracle used
at query `k`): `state 0 = U₀ ψ₀`, `state (k+1) = U_{k+1} (O_k (state k))`. The state *entering* query `k` is
`state O k`. -/
noncomputable def Adversary.state (A : Adversary B) (O : ℕ → Unitary B) : ℕ → QState B
  | 0 => A.U 0 A.ψ₀
  | k + 1 => A.U (k + 1) (O k (A.state O k))

/-- **The run under a constant oracle** `Or`: `A^{Or}(ψ₀) = state (fun _ => Or) q`. -/
noncomputable def Adversary.run (A : Adversary B) (Or : Unitary B) : QState B := A.state (fun _ => Or) A.q

/-- **Congruence of runs on the prefix.** If two oracle choices agree on all queries `< k`, the states after
`k` queries coincide (the state at `k` depends only on oracles `0 … k−1`). -/
theorem Adversary.state_congr (A : Adversary B) (O1 O2 : ℕ → Unitary B) (k : ℕ)
    (h : ∀ i, i < k → O1 i = O2 i) : A.state O1 k = A.state O2 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hb : O1 n = O2 n := h n (Nat.lt_succ_self n)
    have hrec : A.state O1 n = A.state O2 n := ih (fun i hi => h i (hi.trans (Nat.lt_succ_self n)))
    simp only [Adversary.state, hb, hrec]

/-- **Propagation lemma (the heart of the telescoping).** If two oracle choices agree on every query `> j`,
then a difference introduced at query `j` propagates through the subsequent (norm-preserving) unitaries and
oracles WITHOUT changing norm: for all `m`,
`‖state O1 (j+1+m) − state O2 (j+1+m)‖ = ‖O1 j (state O1 j) − O2 j (state O2 j)‖`. -/
theorem Adversary.propagate (A : Adversary B) (O1 O2 : ℕ → Unitary B) (j : ℕ)
    (hafter : ∀ k, j < k → O1 k = O2 k) (m : ℕ) :
    ‖A.state O1 (j + 1 + m) - A.state O2 (j + 1 + m)‖
      = ‖O1 j (A.state O1 j) - O2 j (A.state O2 j)‖ := by
  induction m with
  | zero =>
    show ‖A.state O1 (j + 1) - A.state O2 (j + 1)‖ = _
    simp only [Adversary.state]
    rw [unitary_norm_sub (A.U (j + 1))]
  | succ n ih =>
    have hgt : j < j + 1 + n := by omega
    have hb : O1 (j + 1 + n) = O2 (j + 1 + n) := hafter _ hgt
    have he : j + 1 + (n + 1) = (j + 1 + n) + 1 := by ring
    rw [he]
    simp only [Adversary.state]
    rw [hb, unitary_norm_sub (A.U ((j + 1 + n) + 1)), unitary_norm_sub (O2 (j + 1 + n))]
    exact ih

/-! ## Step 2 — the hybrid telescope. -/

/-- **The hybrid oracle choice**: run `O_H` for queries `< j`, `O_{H'}` for queries `≥ j`. `mix 0` is
all-`O_{H'}`, `mix q` is all-`O_H` (on the used queries `0 … q−1`); adjacent hybrids `mix j`, `mix (j+1)`
differ only at query `j`. -/
def mixOracle (Oh Oh' : Unitary B) (j : ℕ) : ℕ → Unitary B := fun k => if k < j then Oh else Oh'

/-- **Adjacent hybrids differ by one oracle swap at query `j`.** The run-difference between hybrid `j+1` and
hybrid `j` equals the single oracle difference `‖O_H ψⱼ − O_{H'} ψⱼ‖` at the shared state `ψⱼ` entering
query `j` — the surrounding unitaries preserve the norm (`Adversary.propagate`). -/
theorem hybrid_step (A : Adversary B) (Oh Oh' : Unitary B) (j : ℕ) (hj : j < A.q) :
    ‖A.state (mixOracle Oh Oh' (j + 1)) A.q - A.state (mixOracle Oh Oh' j) A.q‖
      = ‖Oh (A.state (mixOracle Oh Oh' j) j) - Oh' (A.state (mixOracle Oh Oh' j) j)‖ := by
  have hafter : ∀ k, j < k → mixOracle Oh Oh' (j + 1) k = mixOracle Oh Oh' j k := by
    intro k hk; simp only [mixOracle]; rw [if_neg (by omega), if_neg (by omega)]
  have hbefore : A.state (mixOracle Oh Oh' (j + 1)) j = A.state (mixOracle Oh Oh' j) j := by
    apply A.state_congr; intro i hi; simp only [mixOracle]; rw [if_pos (by omega), if_pos (by omega)]
  have hO1j : mixOracle Oh Oh' (j + 1) j = Oh := by
    simp only [mixOracle]; rw [if_pos (Nat.lt_succ_self j)]
  have hO2j : mixOracle Oh Oh' j j = Oh' := by
    simp only [mixOracle]; rw [if_neg (Nat.lt_irrefl j)]
  have hm : j + 1 + (A.q - (j + 1)) = A.q := by omega
  rw [← hm, A.propagate _ _ j hafter (A.q - (j + 1)), hO1j, hO2j, hbefore]

/-- **`hybrid_telescope` (O2H Step 2).** Telescoping the hybrids (`Finset.sum_range_sub` + the triangle
inequality) bounds the total run-difference by the sum of per-query oracle differences:
`‖A^{O_H} − A^{O_{H'}}‖ ≤ ∑_{k<q} ‖O_H ψₖ − O_{H'} ψₖ‖`, where `ψₖ` is the state entering query `k`. -/
theorem hybrid_telescope (A : Adversary B) (Oh Oh' : Unitary B) :
    ‖A.run Oh - A.run Oh'‖
      ≤ ∑ j ∈ Finset.range A.q,
          ‖Oh (A.state (mixOracle Oh Oh' j) j) - Oh' (A.state (mixOracle Oh Oh' j) j)‖ := by
  have hfq : A.state (mixOracle Oh Oh' A.q) A.q = A.run Oh := by
    simp only [Adversary.run]
    apply A.state_congr; intro i hi; simp only [mixOracle]; rw [if_pos hi]
  have hf0 : A.state (mixOracle Oh Oh' 0) A.q = A.run Oh' := by
    simp only [Adversary.run]
    apply A.state_congr; intro i _; simp only [mixOracle]; rw [if_neg (Nat.not_lt_zero i)]
  have htel : A.state (mixOracle Oh Oh' A.q) A.q - A.state (mixOracle Oh Oh' 0) A.q
      = ∑ j ∈ Finset.range A.q,
          (A.state (mixOracle Oh Oh' (j + 1)) A.q - A.state (mixOracle Oh Oh' j) A.q) :=
    (Finset.sum_range_sub (fun j => A.state (mixOracle Oh Oh' j) A.q) A.q).symm
  rw [hfq, hf0] at htel
  rw [htel]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j hj
  rw [Finset.mem_range] at hj
  exact le_of_eq (hybrid_step A Oh Oh' j hj)

/-! ## Step 3 — Cauchy–Schwarz over the queries (the power-mean core). -/

/-- **`cauchy_schwarz_queries` (O2H Step 3).** For nonnegative per-query amplitudes,
`∑_{k<q} aₖ ≤ √(q · ∑_{k<q} aₖ²)`. This is Mathlib's `sq_sum_le_card_mul_sum_sq` (Chebyshev / power-mean,
`#(range q) = q`) — the SAME inequality `HermineTSUF.forking` uses, here over ℝ. -/
theorem cauchy_schwarz_queries (a : ℕ → ℝ) (q : ℕ) :
    ∑ j ∈ Finset.range q, a j ≤ Real.sqrt ((q : ℝ) * ∑ j ∈ Finset.range q, (a j) ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range q) (f := a)
  simpa using h

/-! ## Measurement (Born rule) and the headline. -/

/-- **The Born-rule amplitude** for output projector `P₁`: `amp O := ‖P₁ (A^O ψ₀)‖`. -/
noncomputable def Adversary.amp (A : Adversary B) (P₁ : QState B →ₗ[ℂ] QState B) (Or : Unitary B) : ℝ :=
  ‖P₁ (A.run Or)‖

/-- **The Born-rule probability** `Pr[A^O = 1] := ‖P₁ (A^O ψ₀)‖²`. -/
noncomputable def Adversary.bornProb (A : Adversary B) (P₁ : QState B →ₗ[ℂ] QState B) (Or : Unitary B) : ℝ :=
  ‖P₁ (A.run Or)‖ ^ 2

/-- The Born probability is the squared amplitude. -/
theorem Adversary.bornProb_eq_amp_sq (A : Adversary B) (P₁ : QState B →ₗ[ℂ] QState B) (Or : Unitary B) :
    A.bornProb P₁ Or = (A.amp P₁ Or) ^ 2 := rfl

/-- **The advantage is 1-Lipschitz in the run.** `|amp_H − amp_{H'}| ≤ ‖A^{O_H} − A^{O_{H'}}‖` — the
reverse triangle inequality plus the measurement being norm-nonincreasing. -/
theorem amp_sub_le (A : Adversary B) (P₁ : QState B →ₗ[ℂ] QState B)
    (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) (Oh Oh' : Unitary B) :
    |A.amp P₁ Oh - A.amp P₁ Oh'| ≤ ‖A.run Oh - A.run Oh'‖ := by
  unfold Adversary.amp
  calc |‖P₁ (A.run Oh)‖ - ‖P₁ (A.run Oh')‖|
      ≤ ‖P₁ (A.run Oh) - P₁ (A.run Oh')‖ := abs_norm_sub_norm_le _ _
    _ = ‖P₁ (A.run Oh - A.run Oh')‖ := by rw [map_sub]
    _ ≤ ‖A.run Oh - A.run Oh'‖ := hP1 _

/-- **The semiclassical find probability** `Pfind := ∑_{k<q} ‖P_S ψₖ‖²`, the total amplitude the adversary
places on the reprogrammed region across its queries. -/
noncomputable def Pfind (A : Adversary B) (D : OracleDiffData B) : ℝ :=
  ∑ j ∈ Finset.range A.q, ‖D.P (A.state (mixOracle D.O D.O' j) j)‖ ^ 2

/-- **`o2h_bound` — THE HEADLINE (One-Way-to-Hiding).** For any `q`-query adversary, reprogrammed-oracle
data `D` (oracles `O_H`, `O_{H'}` agreeing off `S`, projection `P_S`), and output projector `P₁`:
`|amp_H − amp_{H'}| ≤ 2 · √(q · Pfind)`.
The chain: `amp_sub_le` (Step 0) → `hybrid_telescope` (Step 2) → `oracle_diff_on_S` per query (Step 1) →
`cauchy_schwarz_queries` (Step 3). Every step is proved; nothing is assumed. -/
theorem o2h_bound (A : Adversary B) (D : OracleDiffData B) (P₁ : QState B →ₗ[ℂ] QState B)
    (hP1 : ∀ v, ‖P₁ v‖ ≤ ‖v‖) :
    |A.amp P₁ D.O - A.amp P₁ D.O'| ≤ 2 * Real.sqrt ((A.q : ℝ) * Pfind A D) := by
  -- ψₖ, and the per-query amplitude aₖ = ‖P_S ψₖ‖.
  set ψ : ℕ → QState B := fun j => A.state (mixOracle D.O D.O' j) j with hψ
  -- Step 0 + Step 2: the advantage is bounded by the sum of oracle differences.
  have h02 : |A.amp P₁ D.O - A.amp P₁ D.O'|
      ≤ ∑ j ∈ Finset.range A.q, ‖D.O (ψ j) - D.O' (ψ j)‖ :=
    (amp_sub_le A P₁ hP1 D.O D.O').trans (hybrid_telescope A D.O D.O')
  -- Step 1 per query: each oracle difference ≤ 2‖P_S ψₖ‖.
  have hstep1 : ∑ j ∈ Finset.range A.q, ‖D.O (ψ j) - D.O' (ψ j)‖
      ≤ ∑ j ∈ Finset.range A.q, 2 * ‖D.P (ψ j)‖ :=
    Finset.sum_le_sum (fun j _ => oracle_diff_on_S D (ψ j))
  -- Pull out the 2 and apply Step 3 (Cauchy–Schwarz over the queries).
  have hcs : ∑ j ∈ Finset.range A.q, 2 * ‖D.P (ψ j)‖
      ≤ 2 * Real.sqrt ((A.q : ℝ) * Pfind A D) := by
    rw [← Finset.mul_sum]
    have hcsq := cauchy_schwarz_queries (fun j => ‖D.P (ψ j)‖) A.q
    have hPfind : Pfind A D = ∑ j ∈ Finset.range A.q, ‖D.P (ψ j)‖ ^ 2 := rfl
    rw [hPfind]
    exact mul_le_mul_of_nonneg_left hcsq (by norm_num)
  exact h02.trans (hstep1.trans hcs)

#assert_all_clean [oracle_diff_on_S, unitary_norm_sub, Adversary.state_congr, Adversary.propagate,
  hybrid_step, hybrid_telescope, cauchy_schwarz_queries, amp_sub_le, o2h_bound,
  Adversary.bornProb_eq_amp_sq]

/-! ## Teeth — a concrete tiny instance where the bound FIRES non-vacuously.

`X = Bool`, `Y = ZMod 2`, `q = 1`. The oracle `toyH` is reprogrammed to `toyH'` on `S = {true}`. The
adversary (identity unitaries) starts with ALL amplitude on the reprogrammed coordinate `(true, 0)` — the
tight case. A `(true,1)`-selecting measurement separates the two oracles (`amp_H = 1`, `amp_{H'} = 0`), so
the advantage `= 1`, bounded by `2·√(1·Pfind) = 2` with `Pfind = 1`. -/

section Teeth

open Dregg2.Crypto.QuantumOracle

/-- The reprogrammed-oracle data for the toy: `toyH` vs `toyH'` on `S = {true}`. -/
noncomputable def toyD : OracleDiffData (Bool × ZMod 2) :=
  oracleDiff toyH toyH' ({true} : Finset Bool) toy_agree

/-- The toy initial state: all amplitude on the reprogrammed coordinate `(true, 0)` (`x = true ∈ S`). -/
noncomputable def toyPsi : QState (Bool × ZMod 2) := EuclideanSpace.single (true, (0 : ZMod 2)) (1 : ℂ)

/-- The toy 1-query adversary: identity work unitaries, `q = 1`, initial state `toyPsi`. -/
noncomputable def toyAdv : Adversary (Bool × ZMod 2) where
  q := 1
  U := fun _ => LinearIsometryEquiv.refl ℂ (QState (Bool × ZMod 2))
  ψ₀ := toyPsi

/-- A `(true,1)`-selecting output projector: keeps the amplitude at basis state `(true,1)`, zeroes the rest.
Norm-nonincreasing, so a legitimate measurement operator. -/
noncomputable def toyMeas : QState (Bool × ZMod 2) →ₗ[ℂ] QState (Bool × ZMod 2) where
  toFun v := WithLp.toLp 2 (fun p => if p = (true, (1 : ZMod 2)) then WithLp.ofLp v p else 0)
  map_add' u v := by ext p; by_cases h : p = (true, (1 : ZMod 2)) <;> simp [h]
  map_smul' c v := by ext p; by_cases h : p = (true, (1 : ZMod 2)) <;> simp [h]

@[simp] theorem toyMeas_apply (v : QState (Bool × ZMod 2)) (p : Bool × ZMod 2) :
    toyMeas v p = if p = (true, (1 : ZMod 2)) then v p else 0 := rfl

theorem toyMeas_norm_le (v : QState (Bool × ZMod 2)) : ‖toyMeas v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro p _
  simp only [toyMeas_apply]
  have hle : ‖(if p = (true, (1 : ZMod 2)) then v p else 0)‖ ≤ ‖v p‖ := by
    by_cases h : p = (true, (1 : ZMod 2)) <;> simp [h]
  gcongr

/-- `P_S` fixes `toyPsi` (all its amplitude is on `S = {true}`): `projSet {true} toyPsi = toyPsi`. -/
theorem toy_proj_fixes : projSet ({true} : Finset Bool) toyPsi = toyPsi := by
  ext ⟨x, y⟩
  simp only [projSet_apply, toyPsi]
  by_cases h : x = true
  · simp [h]
  · rw [if_neg (by simpa using h)]
    rw [PiLp.single_apply]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩; exact h rfl

/-- `‖P_S toyPsi‖ = 1` — the adversary places all (unit) amplitude on the reprogrammed region (tight case). -/
theorem toy_proj_norm : ‖projSet ({true} : Finset Bool) toyPsi‖ = 1 := by
  rw [toy_proj_fixes, toyPsi, PiLp.norm_single]; simp

/-- **The oracle-difference bound FIRES on genuinely nonzero data.** On `toyPsi` (all amplitude on `S`),
`‖O_H toyPsi − O_{H'} toyPsi‖ ≤ 2‖P_S toyPsi‖ = 2`, and the bounded quantity is NONZERO — the reprogramming
moves amplitude `(true,0) ↦ (true,1)` under `O_H` but not under `O_{H'}`, so the oracles genuinely differ. -/
theorem toy_oracle_diff_fires :
    ‖toyD.O toyPsi - toyD.O' toyPsi‖ ≤ 2 * ‖toyD.P toyPsi‖ ∧ 0 < ‖toyD.O toyPsi - toyD.O' toyPsi‖ := by
  refine ⟨oracle_diff_on_S toyD toyPsi, ?_⟩
  rw [norm_pos_iff, sub_ne_zero]
  -- O_H toyPsi = single (true,1) 1 ; O_{H'} toyPsi = single (true,0) 1 ; distinct.
  simp only [toyD, oracleDiff_O, oracleDiff_O', toyPsi, oracleUnitary_single]
  intro hcontra
  have := congrArg (fun w => w (true, (1 : ZMod 2))) hcontra
  simp only [PiLp.single_apply, toyH, toyH'] at this
  norm_num at this

/-- **The o2h_bound instance holds for the toy** (it is a genuine consequence of the general theorem). -/
theorem toy_o2h_bound :
    |toyAdv.amp toyMeas toyD.O - toyAdv.amp toyMeas toyD.O'|
      ≤ 2 * Real.sqrt ((toyAdv.q : ℝ) * Pfind toyAdv toyD) :=
  o2h_bound toyAdv toyD toyMeas toyMeas_norm_le

/-- `Pfind = 1` for the toy: the single query's state is `toyPsi`, all amplitude on `S`. Non-vacuous —
the bound `2·√(1·1) = 2` is a genuine positive number, not a vacuous `≤ ∞`/`≤ 0`. -/
theorem toy_Pfind : Pfind toyAdv toyD = 1 := by
  simp only [Pfind, toyAdv, Finset.sum_range_one]
  -- ψ₀ entering query 0 = U 0 ψ₀ = toyPsi (identity unitary).
  show ‖toyD.P (toyAdv.state (mixOracle toyD.O toyD.O' 0) 0)‖ ^ 2 = 1
  simp only [toyAdv, Adversary.state, LinearIsometryEquiv.coe_refl, id_eq]
  simp only [toyD, oracleDiff_P]
  rw [toy_proj_norm]; norm_num

-- Non-vacuity of the toy bound: q = 1 (definitional; toyAdv is noncomputable so use `rfl`, not `decide`).
example : toyAdv.q = 1 := rfl
-- The reprogramming genuinely changes the oracle on S (so the oracle difference is real, cf. toy_oracle_diff_fires).
#guard decide (toyH true ≠ toyH' true)

end Teeth

#assert_all_clean [toyMeas_norm_le, toy_proj_fixes, toy_proj_norm, toy_oracle_diff_fires,
  toy_o2h_bound, toy_Pfind]

end Dregg2.Crypto.OneWayToHiding
