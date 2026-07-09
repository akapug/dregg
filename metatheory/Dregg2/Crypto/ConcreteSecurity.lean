/-
# `Dregg2.Crypto.ConcreteSecurity` — the CONCRETE-SECURITY / ASYMPTOTIC substrate.

Everything the crypto tree proves at `Prop` level ("no forgery", "realizes `F_SIG`", "the two worlds
agree") should be RESTATABLE as an ADVANTAGE BOUND: a distinguisher's success, as an ENSEMBLE indexed by
the security parameter `λ`, is a NEGLIGIBLE function. This module builds that substrate from primitives —
negligible functions, a polynomial-step (PPT) machine model, and computational indistinguishability of
ensembles — and proves the closure lemmas the customers (`HermineTSUF`'s forking `ε²/q_H`,
`FoBookkeeping`'s FO game-hop terms, `OneWayToHiding`'s `2√(q·Pfind)`) need to compose their concrete
advantage terms and conclude negligibility.

## What is built (§-by-§)

  **§1 — NEGLIGIBLE FUNCTIONS.** `Negl f` is the textbook definition: for every exponent `c`, EVENTUALLY
  `|f n| < 1/nᶜ` (smaller than every inverse polynomial). The load-bearing content is the CLOSURE algebra:
  `Negl` is closed under addition (`negl_add`), under multiplication by a constant (`negl_const_mul`), by a
  monomial (`negl_mul_monomial`) and by a polynomial (`negl_mul_poly`), under a finite sum
  (`negl_finset_sum`), and dominated functions stay negligible (`negl_of_eventually_le`). BOTH TEETH: `2⁻ⁿ`
  IS negligible (`negl_two_pow`) and a nonzero constant is NOT (`not_negl_one`) — the definition is a real
  discriminator, not a vacuous predicate.

  **§2 — THE PPT / STEP-BOUND MACHINE MODEL.** A `StepBound` carries a step-count function `steps : ℕ → ℕ`;
  it is `PPT` iff `steps` is polynomially bounded (`PolyBoundedNat`). BOTH TEETH: a constant-step machine IS
  PPT (`constBound_ppt`), an exponential-step machine is NOT (`expBound_not_ppt`, via exp-dominates-poly).

  **§3 — ADVANTAGE / COMPUTATIONAL INDISTINGUISHABILITY.** An `Ensemble` is `ℕ → ℝ` (an advantage as a
  function of the security parameter). Two ensembles observed through a family of distinguishers are
  computationally indistinguishable (`CompIndist`) iff EVERY PPT distinguisher's advantage is negligible.
  BOTH TEETH: the all-zero advantage family is indistinguishable (`compIndist_zero`); a constant-`1`
  advantage for a PPT distinguisher is NOT (`not_compIndist_one`).

## No named-carrier laundering.

Nothing here is assumed. The only nontrivial external facts are Mathlib's exp-dominates-poly limit
(`tendsto_pow_const_div_const_pow_of_one_lt`) and the order/topology API — theorems, never `axiom`s. This
file introduces NO `def …Hard`; it is the pure asymptotic scaffolding the hardness floors ride on.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Dregg2.Tactics

open Filter
open scoped BigOperators Topology

namespace Dregg2.Crypto.ConcreteSecurity

/-! ## §1 — Negligible functions. -/

/-- **The security parameter** `λ : ℕ` and an **advantage ENSEMBLE** `ℕ → ℝ` (a real quantity as a
function of `λ`). All concrete-security statements are bounds on such ensembles. -/
abbrev SecParam : Type := ℕ

/-- An **advantage ensemble** — a real-valued quantity indexed by the security parameter. -/
abbrev Ensemble : Type := ℕ → ℝ

/-- **`Negl f` — `f` is NEGLIGIBLE.** For every exponent `c`, eventually (for all large `n`) the value is
below the inverse polynomial `1/nᶜ`. The textbook asymptotic definition; the whole crypto tree's
"advantage is negligible" statements instantiate this. -/
def Negl (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, |f n| < 1 / (n : ℝ) ^ c

/-! ### The exp-dominates-poly core (Mathlib), the engine behind `2⁻ⁿ` negligible and non-PPT exponential. -/

/-- **`nᵈ / 2ⁿ → 0`** — polynomial over exponential vanishes (Mathlib's
`tendsto_pow_const_div_const_pow_of_one_lt` at `r = 2`). The single analytic fact this file rests on. -/
theorem tendsto_pow_div_two_pow (d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ d / 2 ^ n) atTop (nhds 0) :=
  tendsto_pow_const_div_const_pow_of_one_lt d one_lt_two

/-- **`nᶜ < 2ⁿ` eventually** — the exponential eventually dominates every fixed monomial. From
`tendsto_pow_div_two_pow` (the ratio `→ 0`, hence `< 1` eventually). -/
theorem eventually_pow_lt_two_pow (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c < 2 ^ n := by
  have hlt : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c / 2 ^ n < 1 :=
    (tendsto_pow_div_two_pow c).eventually_lt_const (by norm_num)
  filter_upwards [hlt] with n hn
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rwa [div_lt_one hpos] at hn

/-! ### The load-bearing TEETH: `2⁻ⁿ` is negligible; a nonzero constant is not. -/

/-- **(TOOTH — a concrete NEGLIGIBLE function.)** `2⁻ⁿ` is negligible: for every `c`, eventually
`1/2ⁿ < 1/nᶜ`, i.e. `nᶜ < 2ⁿ` (`eventually_pow_lt_two_pow`). The positive pole — `Negl` is inhabited. -/
theorem negl_two_pow : Negl (fun n : ℕ => 1 / (2 : ℝ) ^ n) := by
  intro c
  filter_upwards [eventually_pow_lt_two_pow c, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnc : (0 : ℝ) < (n : ℝ) ^ c := by positivity
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ n)]
  exact one_div_lt_one_div_of_lt hnc hn

/-- **(TOOTH — a concrete NON-negligible function.)** The constant `1` is NOT negligible: at exponent
`c = 1` no `N` works, because for every `n ≥ 1` we have `1/n ≤ 1 = |1|`. The negative pole — `Negl` is a
genuine discriminator, false for a constant. -/
theorem not_negl_one : ¬ Negl (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  obtain ⟨n, hlt, hn1⟩ := ((h 1).and (eventually_ge_atTop 1)).exists
  simp only [abs_one, pow_one] at hlt
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hn]; exact_mod_cast hn1
  linarith

/-! ### The closure algebra. -/

/-- **`Negl 0`** — the zero ensemble is negligible (the distance-0 case the whole game-based tree lives at). -/
theorem negl_zero : Negl (fun _ : ℕ => (0 : ℝ)) := by
  intro c
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [abs_zero]
  exact one_div_pos.2 (by positivity)

/-- **DOMINATION.** A function eventually dominated (in absolute value) by a negligible function is
negligible. The squeeze the reductions use to conclude negligibility from a concrete advantage BOUND. -/
theorem negl_of_eventually_le {f g : ℕ → ℝ}
    (hle : ∀ᶠ n : ℕ in atTop, |g n| ≤ |f n|) (hf : Negl f) : Negl g := by
  intro c
  filter_upwards [hle, hf c] with n h1 h2
  exact lt_of_le_of_lt h1 h2

/-- **CLOSED UNDER ADDITION.** The sum of two negligible functions is negligible: bound each below
`1/n^{c+1}`, and for `n ≥ 2`, `2/n^{c+1} ≤ 1/nᶜ`. -/
theorem negl_add {f g : ℕ → ℝ} (hf : Negl f) (hg : Negl g) :
    Negl (fun n => f n + g n) := by
  intro c
  filter_upwards [hf (c + 1), hg (c + 1), eventually_ge_atTop 2] with n hfn hgn hn2
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnc : (0 : ℝ) < (n : ℝ) ^ c := by positivity
  have key : 2 * (1 / (n : ℝ) ^ (c + 1)) ≤ 1 / (n : ℝ) ^ c := by
    have h2n : (2 : ℝ) / n ≤ 1 := by rw [div_le_one hn]; exact_mod_cast hn2
    have e : 2 * (1 / (n : ℝ) ^ (c + 1)) = (2 / n) * (1 / (n : ℝ) ^ c) := by
      rw [pow_succ]; field_simp
    rw [e]
    calc (2 / n) * (1 / (n : ℝ) ^ c)
        ≤ 1 * (1 / (n : ℝ) ^ c) := by
          apply mul_le_mul_of_nonneg_right h2n; positivity
      _ = 1 / (n : ℝ) ^ c := one_mul _
  calc |f n + g n|
      ≤ |f n| + |g n| := abs_add_le _ _
    _ < 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := by linarith
    _ = 2 * (1 / (n : ℝ) ^ (c + 1)) := by ring
    _ ≤ 1 / (n : ℝ) ^ c := key

/-- **CLOSED UNDER MULTIPLICATION BY A MONOMIAL.** `nᵏ · f n` is negligible if `f` is: bound `f` below
`1/n^{c+k}`, and `nᵏ · (1/n^{c+k}) = 1/nᶜ` exactly (the `nᵏ` cancels). -/
theorem negl_mul_monomial (k : ℕ) {f : ℕ → ℝ} (hf : Negl f) :
    Negl (fun n => (n : ℝ) ^ k * f n) := by
  intro c
  filter_upwards [hf (c + k), eventually_ge_atTop 1] with n hfn hn1
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ k)]
  have hstep : (n : ℝ) ^ k * |f n| < (n : ℝ) ^ k * (1 / (n : ℝ) ^ (c + k)) :=
    mul_lt_mul_of_pos_left hfn (by positivity)
  refine hstep.trans_le (le_of_eq ?_)
  rw [pow_add]; field_simp

/-- **CLOSED UNDER MULTIPLICATION BY A CONSTANT.** `a · f n` is negligible if `f` is. For large `n`,
`|a| ≤ n`, so `|a · f n| ≤ |n · f n|`, dominated by the (negligible) linear monomial multiple. -/
theorem negl_const_mul (a : ℝ) {f : ℕ → ℝ} (hf : Negl f) :
    Negl (fun n => a * f n) := by
  refine negl_of_eventually_le ?_ (negl_mul_monomial 1 hf)
  filter_upwards [eventually_ge_atTop (Nat.ceil |a|)] with n hn
  have hle : |a| ≤ (n : ℝ) := (Nat.le_ceil |a|).trans (by exact_mod_cast hn)
  rw [abs_mul, abs_mul, pow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

/-- **POLYNOMIAL-BOUNDED** — `|p n| ≤ C · nᵈ` eventually. The shape of any polynomial factor (a session
count, a query bound `q`, a fixed degree). -/
def PolyBounded (p : ℕ → ℝ) : Prop :=
  ∃ (d : ℕ) (C : ℝ), ∀ᶠ n : ℕ in atTop, |p n| ≤ C * (n : ℝ) ^ d

/-- **CLOSED UNDER MULTIPLICATION BY A POLYNOMIAL.** `p n · f n` is negligible if `f` is and `p` is
polynomially bounded: `|p n · f n| ≤ (|C| · nᵈ) · |f n|`, dominated by the negligible `|C|·nᵈ·f`
(monomial then constant). This is the closure `HermineTSUF` needs (a `q_H` factor times a negligible
forking term stays negligible). -/
theorem negl_mul_poly {p f : ℕ → ℝ} (hp : PolyBounded p) (hf : Negl f) :
    Negl (fun n => p n * f n) := by
  obtain ⟨d, C, hpb⟩ := hp
  refine negl_of_eventually_le ?_ (negl_const_mul |C| (negl_mul_monomial d hf))
  filter_upwards [hpb, eventually_ge_atTop 1] with n hn hn1
  have hnd : (0 : ℝ) ≤ (n : ℝ) ^ d := by positivity
  simp only [abs_mul, abs_abs, abs_of_nonneg hnd]
  calc |p n| * |f n|
      ≤ (|C| * (n : ℝ) ^ d) * |f n| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact hn.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnd)
    _ = |C| * ((n : ℝ) ^ d * |f n|) := by ring

/-- **CLOSED UNDER A FINITE SUM.** A finite sum of negligible functions is negligible (iterated
`negl_add`). This is the union-bound step of a hybrid argument: `k` negligible per-instance advantages
summed over `k` instances stay negligible. -/
theorem negl_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (h : ∀ i ∈ s, Negl (f i)) : Negl (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using negl_zero
  | @insert a s ha ih =>
    have key : (fun n => ∑ i ∈ insert a s, f i n) = (fun n => f a n + ∑ i ∈ s, f i n) := by
      funext n; rw [Finset.sum_insert ha]
    rw [key]
    exact negl_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## §2 — The PPT / step-bound machine model. -/

/-- **`PolyBoundedNat t`** — `t : ℕ → ℕ` is bounded by a natural polynomial `C·nᵈ + C`. The complexity
counterpart of `PolyBounded`. -/
def PolyBoundedNat (t : ℕ → ℕ) : Prop :=
  ∃ (d C : ℕ), ∀ n, t n ≤ C * n ^ d + C

/-- **A `StepBound`** — an adversary/simulator abstracted to its step-count function `steps : λ ↦ #steps`.
Deliberately minimal (usable, not baroque): the only structure we need to state PPT. -/
structure StepBound where
  /-- The number of computation steps as a function of the security parameter. -/
  steps : ℕ → ℕ

/-- **`b.PPT`** — the machine runs in probabilistic-POLYNOMIAL time: its step count is polynomially
bounded. -/
def StepBound.PPT (b : StepBound) : Prop := PolyBoundedNat b.steps

/-- A **constant-step** machine (e.g. a simulator doing `O(1)` work per invocation). -/
def constBound (c : ℕ) : StepBound := ⟨fun _ => c⟩

/-- **(TOOTH — a PPT machine.)** Constant work is polynomial (`d = 0`). The positive pole. -/
theorem constBound_ppt (c : ℕ) : (constBound c).PPT :=
  ⟨0, c, fun n => by simp only [constBound, pow_zero, Nat.mul_one]; omega⟩

/-- An **exponential-step** machine — `2ⁿ` steps. -/
def expBound : StepBound := ⟨fun n => 2 ^ n⟩

/-- **(TOOTH — a NON-PPT machine.)** Exponential work is not polynomially bounded: `2ⁿ` eventually
exceeds every `C·nᵈ + C` (exp dominates poly, `tendsto_pow_div_two_pow`). The negative pole — `PPT` is a
genuine discriminator. -/
theorem expBound_not_ppt : ¬ expBound.PPT := by
  rintro ⟨d, C, h⟩
  have hR : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (C : ℝ) * (n : ℝ) ^ d + C := by
    intro n
    have hn := h n
    have : ((2 ^ n : ℕ) : ℝ) ≤ ((C * n ^ d + C : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at this ⊢
    linarith
  have ht : Tendsto (fun n : ℕ => ((C : ℝ) * (n : ℝ) ^ d + C) / 2 ^ n) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (C : ℝ) * ((n : ℝ) ^ d / 2 ^ n)) atTop (nhds ((C : ℝ) * 0)) :=
      (tendsto_pow_div_two_pow d).const_mul (C : ℝ)
    have h2 : Tendsto (fun n : ℕ => (C : ℝ) * ((n : ℝ) ^ 0 / 2 ^ n)) atTop (nhds ((C : ℝ) * 0)) :=
      (tendsto_pow_div_two_pow 0).const_mul (C : ℝ)
    have hsum := h1.add h2
    rw [mul_zero, add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  have hlt : ∀ᶠ n : ℕ in atTop, ((C : ℝ) * (n : ℝ) ^ d + C) / 2 ^ n < 1 :=
    ht.eventually_lt_const (by norm_num)
  obtain ⟨n, hn⟩ := hlt.exists
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_one h2n] at hn
  exact absurd (hR n) (not_le.2 hn)

/-! ## §3 — Advantage / computational indistinguishability. -/

/-- **`CompIndist ppt adv`** — two ensembles, observed through a family `D` of distinguishers with
efficiency predicate `ppt` and advantage `adv d : Ensemble` (the distinguisher `d`'s success `|Pr_real −
Pr_ideal|` as a function of `λ`), are COMPUTATIONALLY INDISTINGUISHABLE iff EVERY PPT distinguisher has
NEGLIGIBLE advantage. The standard definition; the target shape for every `Prop`-level indistinguishability
statement in the tree. -/
def CompIndist {D : Type*} (ppt : D → Prop) (adv : D → Ensemble) : Prop :=
  ∀ d, ppt d → Negl (adv d)

/-- **(TOOTH — indistinguishable.)** The all-zero advantage family is computationally indistinguishable
(every distinguisher, PPT or not, gets `Negl 0`). The positive pole. -/
theorem compIndist_zero {D : Type*} (ppt : D → Prop) :
    CompIndist ppt (fun _ => (fun _ => 0 : Ensemble)) :=
  fun _ _ => negl_zero

/-- **(TOOTH — distinguishable.)** If SOME PPT distinguisher has constant-`1` advantage, the ensembles are
NOT indistinguishable (`not_negl_one`). The negative pole — `CompIndist` is load-bearing. -/
theorem not_compIndist_one {D : Type*} (ppt : D → Prop) (d0 : D) (hd0 : ppt d0) :
    ¬ CompIndist ppt (fun _ => (fun _ => (1 : ℝ) : Ensemble)) :=
  fun h => not_negl_one (h d0 hd0)

#assert_all_clean [
  tendsto_pow_div_two_pow,
  eventually_pow_lt_two_pow,
  negl_two_pow,
  not_negl_one,
  negl_zero,
  negl_of_eventually_le,
  negl_add,
  negl_mul_monomial,
  negl_const_mul,
  negl_mul_poly,
  negl_finset_sum,
  constBound_ppt,
  expBound_not_ppt,
  compIndist_zero,
  not_compIndist_one
]

end Dregg2.Crypto.ConcreteSecurity
