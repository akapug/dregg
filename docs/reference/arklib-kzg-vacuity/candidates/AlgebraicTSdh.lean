/-
Novel candidate: ALGEBRAIC / GENERIC-GROUP t-SDH with a Schwartz–Zippel (Boneh–Boyen) bound.

NOT part of ArkLib. Scratch file supporting the novel repair proposal for the
`tSdhAssumption` vacuity (docs/reference/arklib-kzg-vacuity/candidates/novel.md).

The disease (mechanized in KzgVacuity.lean): `tSdhAssumption D error` quantifies over an
UNRESTRICTED adversary `srs → StateT … ProbComp (Option (ZMod p × G₁))`. Its input `srs`
contains `g₂^τ`, so `Classical.choice` (`exists_zmod_power_of_generator`) extracts τ and wins
with probability 1; the assumption is false for every `error < 1`.

The cure here is the ALGEBRAIC-ADVERSARY restriction of the AGM/GGM (Boneh–Boyen 2004,
Fuchsbauer–Kiltz–Loss 2018), reformulated so it is genuinely restrictive rather than "extra
free data": the adversary's winning group element is FORCED to be `g₁^(P τ)` for a committed
EXPONENT POLYNOMIAL `P` of degree ≤ D — the representation of its output over the SRS basis
`{g₁^(τ^i)}_{i≤D}` — and, crucially, `P` is committed WITHOUT access to τ. τ is sampled only
afterwards. So the win condition `(τ+c)·P(τ) = 1` is, for each fixed (c, P), an event over a
random τ, bounded by Schwartz–Zippel.

This file mechanizes, `sorry`-free, the LOAD-BEARING survival fact: the set of τ on which any
degree-≤D algebraic adversary wins has size ≤ D+1. In the original the winning set was the
WHOLE support (probability 1); here it is ≤ D+1 out of the ≥ p-1 nonzero samples, so the
advantage is ≤ (D+1)/(p-1) < 1. `Classical.choice` cannot escape it because the bound is a
theorem true of EVERY committed (c, P) — there is no τ in the adversary's scope to extract.
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import ArkLib.Commitments.Functional.KZG.Sampling

open Polynomial OracleSpec OracleComp
open scoped NNReal ENNReal

namespace AlgebraicTSdh

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The witness polynomial of an algebraic t-SDH winner at offset `c` and exponent polynomial
`P`: `Q c P = (X + C c) * P - 1`. A field element `τ` is a winning trapdoor for `(c, P)`
exactly when `(τ + c) * P.eval τ = 1`, i.e. `g₁^(P τ) = g₁^(1/(τ+c))`, i.e. `Q.eval τ = 0`. -/
noncomputable def witnessPoly (c : ZMod p) (P : (ZMod p)[X]) : (ZMod p)[X] :=
  (X + C c) * P - 1

@[simp] lemma witnessPoly_eval (c : ZMod p) (P : (ZMod p)[X]) (τ : ZMod p) :
    (witnessPoly c P).eval τ = (τ + c) * P.eval τ - 1 := by
  simp [witnessPoly]

/-- The witness polynomial is never the zero polynomial: its evaluation at any root would give
`(τ+c)·P(τ) = 1`, but as a *polynomial* it has a nonzero coefficient. Concretely `(X+C c)*P`
has zero constant-or-higher structure that a bare `-1` cannot cancel to `0`. -/
lemma witnessPoly_ne_zero (c : ZMod p) (P : (ZMod p)[X]) : witnessPoly c P ≠ 0 := by
  intro h
  -- If `(X + C c) * P - 1 = 0` then `(X + C c) * P = 1`; but `X + C c` has degree 1, so a
  -- degree count forbids the product from being the constant `1`.
  have hmul : (X + C c) * P = 1 := sub_eq_zero.mp h
  rcases eq_or_ne P 0 with hP0 | hP0
  · rw [hP0, mul_zero] at hmul; exact one_ne_zero hmul.symm
  · have hXc : (X + C c) ≠ 0 := by
      intro hc; rw [hc, zero_mul] at hmul; exact one_ne_zero hmul.symm
    have hdeg := natDegree_mul hXc hP0
    rw [hmul, natDegree_one, natDegree_X_add_C] at hdeg
    omega

/-- Degree bound on the witness polynomial: if `P` has degree ≤ D then `Q c P` has degree
≤ D + 1. -/
lemma witnessPoly_natDegree_le (c : ZMod p) (P : (ZMod p)[X]) (D : ℕ)
    (hP : P.natDegree ≤ D) : (witnessPoly c P).natDegree ≤ D + 1 := by
  unfold witnessPoly
  refine le_trans (natDegree_sub_le _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_X_add_C]; omega
  · simp

/-- **The Boneh–Boyen / Schwartz–Zippel survival bound (pure form).**

For any offset `c` and any exponent polynomial `P` of degree ≤ D, the set of trapdoors `τ` on
which the algebraic adversary `(c, P)` wins the t-SDH game — i.e. `(τ+c)·P(τ) = 1`, meaning its
committed group element `g₁^(P τ)` equals the target `g₁^(1/(τ+c))` — is FINITE with at most
`D + 1` elements.

This is the exact quantitative content that the trapdoor-extracting attack destroyed. In the
unrestricted game the winning set was the *whole* nonzero support (advantage 1); under the
algebraic restriction it is ≤ D+1 points, because `P` is committed before τ is sampled and a
nonzero degree-≤D+1 polynomial has ≤ D+1 roots. -/
theorem alg_winning_set_card_le (D : ℕ) (c : ZMod p) (P : (ZMod p)[X])
    (hP : P.natDegree ≤ D) :
    (witnessPoly c P).roots.toFinset.card ≤ D + 1 := by
  calc (witnessPoly c P).roots.toFinset.card
      ≤ Multiset.card (witnessPoly c P).roots := Multiset.toFinset_card_le _
    _ ≤ (witnessPoly c P).natDegree := card_roots' _
    _ ≤ D + 1 := witnessPoly_natDegree_le c P D hP

/-- The winning set of trapdoors, as a set, equals the (finite) root set of the witness
polynomial: `τ` wins iff `Q.eval τ = 0`. -/
theorem alg_winning_set_eq_roots (c : ZMod p) (P : (ZMod p)[X]) :
    {τ : ZMod p | (τ + c) * P.eval τ = 1} = {τ : ZMod p | (witnessPoly c P).IsRoot τ} := by
  ext τ
  simp only [Set.mem_setOf_eq, IsRoot.def, witnessPoly_eval, sub_eq_zero]

/-- Restated as a cardinality bound directly on the winning condition: the number of trapdoors
`τ` for which the algebraic adversary `(c, P)` (degree ≤ D) wins is ≤ D + 1. Uses `Set.ncard`
(instance-free), so it is stated purely about the winning set of the game. -/
theorem alg_num_winning_trapdoors_le (D : ℕ) (c : ZMod p) (P : (ZMod p)[X])
    (hP : P.natDegree ≤ D) :
    {τ : ZMod p | (τ + c) * P.eval τ = 1}.ncard ≤ D + 1 := by
  have hset : {τ : ZMod p | (τ + c) * P.eval τ = 1}
      = ↑((witnessPoly c P).roots.toFinset) := by
    ext τ
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset,
      mem_roots (witnessPoly_ne_zero c P), IsRoot.def, witnessPoly_eval, sub_eq_zero]
  rw [hset, Set.ncard_coe_finset]
  exact alg_winning_set_card_le D c P hP

/-! ### The probability-level survival: a POSITIVE mirror of `not_tSdhAssumption`

The `KzgVacuity` artifact proved `not_tSdhAssumption`: for the *unrestricted* adversary, the
experiment `Pr[win | sampleNonzeroZMod]` is `1`, refuting the assumption below error `1`. Here
we prove the exact opposite for the *algebraic* adversary: its experiment probability, over the
same `sampleNonzeroZMod` trapdoor distribution, is `≤ (D+1)/(p-1) < 1`. The bound holds for
EVERY `(c, P)` — including any built by `Classical.choice` — because `P` is committed before τ
is sampled, so there is nothing to extract.  -/

/-- A **deterministic algebraic t-SDH adversary** of degree bound `D`: it commits, with no
access to τ, to an offset `c` and an exponent polynomial `P` of degree ≤ D. Its (forced)
group-element output is `g₁^(P τ)` — the AGM/GGM algebraic representation over the SRS basis. -/
structure AlgAdversary (D : ℕ) where
  offset : ZMod p
  poly : (ZMod p)[X]
  hdeg : poly.natDegree ≤ D

/-- The success probability of an algebraic adversary in the t-SDH game, over the *same*
`sampleNonzeroZMod` trapdoor distribution the original game uses. The win condition
`(τ + c) * P.eval τ = 1` is exactly `g₁^(P τ) = g₁^(1/(τ+c))` in a prime-order group. -/
noncomputable def algExperiment (D : ℕ) (A : AlgAdversary (p := p) D) : ℝ≥0∞ :=
  Pr[fun τ => (τ + A.offset) * A.poly.eval τ = 1 | Groups.sampleNonzeroZMod (p := p)]

/-- Injectivity of the `sampleNonzeroZMod` index map `i ↦ (i+1 : ZMod p)` on `Fin (p-1)`. -/
lemma sample_index_injective :
    Function.Injective (fun i : Fin (p - 1) => ((i : ℕ) + 1 : ZMod p)) := by
  intro i j hij
  simp only at hij
  have hcast : ((i : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by
    have := add_right_cancel hij; exact_mod_cast this
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  have hi : (i : ℕ) < p := lt_trans i.isLt (by omega)
  have hj : (j : ℕ) < p := lt_trans j.isLt (by omega)
  have : (i : ℕ) = (j : ℕ) := by
    have := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
  exact Fin.ext this

/-- **The Boneh–Boyen / Schwartz–Zippel survival bound (probability form).**

Every algebraic (AGM/GGM) t-SDH adversary of degree bound `D` wins with probability at most
`(D+1)/(p-1)` over the trapdoor distribution — a genuine number strictly below `1`. This is the
positive counterpart of `KzgVacuity.not_tSdhAssumption`: the same experiment shape that was
provably `= 1` for the unrestricted adversary is provably `≤ (D+1)/(p-1)` here. No
`Classical.choice` inhabitant can exceed it: the bound is universally quantified over `(c, P)`
and each is a τ-independent commitment. -/
theorem algExperiment_le (D : ℕ) (A : AlgAdversary (p := p) D) :
    algExperiment D A ≤ (D + 1 : ℝ≥0∞) / ((p - 1 : ℕ) : ℝ≥0∞) := by
  classical
  haveI : NeZero (p - 1) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))⟩
  -- The count of winning indices is bounded by the number of winning trapdoors, ≤ D+1.
  have hcount : (Finset.univ.filter
        (fun i : Fin (p - 1) =>
          ((((i : ℕ) + 1 : ZMod p)) + A.offset) * A.poly.eval ((i : ℕ) + 1 : ZMod p) = 1)).card
      ≤ D + 1 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun i : Fin (p - 1) => ((i : ℕ) + 1 : ZMod p))
      ?_ (sample_index_injective.injOn)) (alg_winning_set_card_le D A.offset A.poly A.hdeg)
    intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    simp only [Finset.mem_coe, Multiset.mem_toFinset,
      mem_roots (witnessPoly_ne_zero A.offset A.poly), IsRoot.def, witnessPoly_eval, sub_eq_zero]
    exact hi
  -- Compute the experiment probability as (count / (p-1)) and bound it.
  unfold algExperiment Groups.sampleNonzeroZMod
  rw [probEvent_map, probEvent_uniformSample, Fintype.card_fin]
  gcongr
  calc ((Finset.univ.filter
          ((fun τ => (τ + A.offset) * A.poly.eval τ = 1) ∘
            fun i : Fin (p - 1) => ((i : ℕ) + 1 : ZMod p))).card : ℝ≥0∞)
      ≤ ((D + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hcount
    _ = (D : ℝ≥0∞) + 1 := by push_cast; ring

/-- **The GATE: the model survives the exact attack.**

For the standard KZG regime `p > D + 2` (which the sibling ARSDH statement already carries as
`hp : p ≥ n + 2`), *every* algebraic t-SDH adversary of degree bound `D` wins with probability
STRICTLY below `1`. This is the precise, quantitative refutation of the vacuity: the
unrestricted `tauExtractingAdversary` of `KzgVacuity.lean` won with probability `= 1`; here no
inhabitant — including any built by `Classical.choice` — can reach `1`, because its exponent
polynomial is committed with no access to the trapdoor τ. The disease was "a winner exists at
probability 1"; the cure makes every winner provably sub-`1`. -/
theorem alg_survives_attack (D : ℕ) (hp : D + 2 < p) (A : AlgAdversary (p := p) D) :
    algExperiment D A < 1 := by
  have hlt : (D + 1 : ℝ≥0∞) < ((p - 1 : ℕ) : ℝ≥0∞) := by
    have : D + 1 < p - 1 := by omega
    exact_mod_cast this
  refine lt_of_le_of_lt (algExperiment_le D A) ?_
  exact ENNReal.div_lt_of_lt_mul' (by rw [mul_one]; exact hlt)

/-- Canary (mirrors the disclosure's `givingUpAdversary`): the experiment genuinely
discriminates. An adversary committing the zero polynomial can never satisfy `(τ+c)·0 = 1`, so
its success probability is `0` — the `< 1` bound is not an artifact of the probability machinery
being everywhere `1`. -/
theorem algExperiment_zeroPoly (D : ℕ) (c : ZMod p) :
    algExperiment D { offset := c, poly := 0, hdeg := by simp } = 0 := by
  unfold algExperiment
  refine probEvent_eq_zero_iff .. |>.mpr ?_
  intro τ _
  simp

end AlgebraicTSdh
