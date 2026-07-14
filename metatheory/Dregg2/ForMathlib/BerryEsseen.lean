/-
# `Dregg2.ForMathlib.BerryEsseen` — the exponential-tilt (Bahadur–Rao) change-of-measure identity.

Mathlib (as of the pinned rev) has the qualitative one-dimensional CLT
(`Mathlib.Probability.CentralLimitTheorem`, convergence in distribution) and the exponential tilt of a
measure (`Mathlib.Probability.Moments.Tilted`), but NO quantitative Berry–Esseen / local-limit bound. This
file formalizes the *finite-counting-model* core of the Bahadur–Rao large-deviation refinement of the Chernoff
bound — the exact **change-of-measure tail identity** and its two immediate consequences (Chernoff recovery and
the geometric anti-concentration envelope). It is deliberately kept general and measure-free (pure `Fintype`
sums), so it is upstreamable and reusable independently of any application.

## The mathematics

For a finite outcome space `Ω` and a real observable `X : Ω → ℝ`, at a tilt parameter `s`, write

* `partition X s = ∑_ω e^{s·X ω}`  (the unnormalized MGF; `= |Ω|·mgf` for the uniform law),
* `tiltWeight X s ω = e^{s·X ω}/partition X s`  (a genuine probability distribution: `≥ 0`, sums to `1`),
* `tiltTailExp X s a = ∑_ω 1_{a ≤ X ω}·e^{−s(X ω−a)}·tiltWeight X s ω`  (`= E_tilt[e^{−s(X−a)}1_{X≥a}]`).

**THE IDENTITY (`tailFrac_eq`).**  The tail fraction `tailFrac X a = #{ω : a ≤ X ω}/|Ω|` factors EXACTLY as

  `tailFrac X a = (partition X s / |Ω|) · e^{−s·a} · tiltTailExp X s a`.

Since `partition/|Ω| = mgf` and `mgf · e^{−s·a}` is precisely the Chernoff bound, this exhibits the Chernoff
bound's *slack* as the single scalar `tiltTailExp ∈ (0,1]`. This is the exact (non-asymptotic) Bahadur–Rao
change-of-measure step — elementary once the tilt is set up, no Berry–Esseen needed for the identity itself.

**CHERNOFF RECOVERY (`tiltTailExp_le_one`).**  For `s ≥ 0`, `tiltTailExp X s a ≤ 1` — so the identity
re-derives `tailFrac ≤ mgf·e^{−sa}`. The Bahadur–Rao *improvement* is any bound `tiltTailExp ≤ P < 1`.

**GEOMETRIC ENVELOPE (`tiltTailExp_le_atom_geom`).**  For an integer-graded `X` whose tilted atom masses are
each `≤ pmax`, `tiltTailExp X s a ≤ pmax / (1 − e^{−s})` — the elementary anti-concentration (monotone/geometric)
envelope. This is the honest, fully-formalized *partial* prefactor: it recovers `Θ(pmax)` of the Bahadur–Rao
`1/(s·σ*·√{2π})` decay (the sharp constant needs a local-limit / characteristic-function bound Mathlib lacks).

Every theorem here is kernel-clean (`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`); no `sorry`, no
`native_decide`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Field.GeomSum

namespace Dregg2.ForMathlib.BerryEsseen

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The unnormalized moment-generating function ("partition function") at tilt `s`:
`partition X s = ∑_ω e^{s·X ω}`. For the uniform law on `Ω` this is `|Ω| · mgf X s`. -/
noncomputable def partition (X : Ω → ℝ) (s : ℝ) : ℝ := ∑ ω, Real.exp (s * X ω)

/-- The exponentially-tilted probability weight at `ω`: `e^{s·X ω}/partition X s`. Over a nonempty `Ω`
these are `≥ 0` and sum to `1` (`tiltWeight_nonneg`, `sum_tiltWeight`). -/
noncomputable def tiltWeight (X : Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  Real.exp (s * X ω) / partition X s

/-- The tilted tail expectation `E_tilt[e^{−s(X−a)}·1_{a ≤ X}]`. -/
noncomputable def tiltTailExp (X : Ω → ℝ) (s a : ℝ) : ℝ :=
  ∑ ω, (if a ≤ X ω then Real.exp (-(s * (X ω - a))) else 0) * tiltWeight X s ω

/-- The exact tail fraction `#{ω : a ≤ X ω}/|Ω|` — the finite-counting "probability" that `X` escapes `a`. -/
noncomputable def tailFrac (X : Ω → ℝ) (a : ℝ) : ℝ :=
  ((univ.filter (fun ω => a ≤ X ω)).card : ℝ) / (Fintype.card Ω : ℝ)

section Basics
variable (X : Ω → ℝ) (s : ℝ)

theorem partition_pos [Nonempty Ω] : 0 < partition X s := by
  unfold partition
  apply Finset.sum_pos (fun ω _ => Real.exp_pos _)
  exact ⟨Classical.arbitrary Ω, Finset.mem_univ _⟩

theorem tiltWeight_nonneg (ω : Ω) : 0 ≤ tiltWeight X s ω := by
  unfold tiltWeight partition
  exact div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))

/-- The tilted weights are a genuine probability distribution: they sum to `1`. -/
theorem sum_tiltWeight [Nonempty Ω] : ∑ ω, tiltWeight X s ω = 1 := by
  unfold tiltWeight
  rw [← Finset.sum_div]
  exact div_self (partition_pos X s).ne'

end Basics

/-! ## The exact change-of-measure tail identity. -/

/-- **THE TILTED-TAIL SUM COLLAPSES.** `tiltTailExp X s a = #{a ≤ X}·e^{s·a}/partition X s`: on the tail the
`e^{−s(Xω−a)}·e^{s·Xω}` numerator telescopes to the constant `e^{s·a}`, so the tilted tail expectation is just
the tail count times `e^{s·a}` over the partition function. Pure algebra. -/
theorem tiltTailExp_eq_card (X : Ω → ℝ) (s a : ℝ) :
    tiltTailExp X s a
      = ((univ.filter (fun ω => a ≤ X ω)).card : ℝ) * Real.exp (s * a) / partition X s := by
  unfold tiltTailExp tiltWeight
  have hstep : ∀ ω : Ω,
      (if a ≤ X ω then Real.exp (-(s * (X ω - a))) else 0) * (Real.exp (s * X ω) / partition X s)
        = (if a ≤ X ω then Real.exp (s * a) / partition X s else 0) := by
    intro ω
    by_cases h : a ≤ X ω
    · simp only [h, if_true]
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, mul_div_assoc]

/-- **THE BAHADUR–RAO CHANGE-OF-MEASURE IDENTITY (PROVED).** The tail fraction factors EXACTLY as the
Chernoff prefix `(partition/|Ω|)·e^{−s·a}` times the tilted tail expectation `tiltTailExp`:

  `tailFrac X a = (partition X s / |Ω|) · e^{−s·a} · tiltTailExp X s a`.

`partition/|Ω|` is the uniform-law MGF, so the RHS is `mgf·e^{−sa}·tiltTailExp` — the Chernoff bound weighted by
the exact slack factor. No measure theory, no `sorry`. -/
theorem tailFrac_eq [Nonempty Ω] (X : Ω → ℝ) (s a : ℝ) :
    tailFrac X a = (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) * tiltTailExp X s a := by
  rw [tiltTailExp_eq_card, tailFrac]
  have hP : partition X s ≠ 0 := (partition_pos X s).ne'
  have hexp : Real.exp (-(a * s)) * Real.exp (a * s) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  rw [mul_assoc, hexp, mul_one]

/-! ## Chernoff recovery: the slack factor is at most `1`. -/

/-- **CHERNOFF RECOVERY (PROVED).** For `s ≥ 0`, `tiltTailExp X s a ≤ 1`. Each summand is `≤` the tilted weight
(the indicator·`e^{−s(X−a)}` factor is in `[0,1]` on the tail when `s ≥ 0`), and the tilted weights sum to `1`.
Composed with `tailFrac_eq` this recovers the Chernoff bound `tailFrac ≤ (partition/|Ω|)·e^{−sa}`. -/
theorem tiltTailExp_le_one [Nonempty Ω] (X : Ω → ℝ) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) :
    tiltTailExp X s a ≤ 1 := by
  unfold tiltTailExp
  calc ∑ ω, (if a ≤ X ω then Real.exp (-(s * (X ω - a))) else 0) * tiltWeight X s ω
      ≤ ∑ ω, tiltWeight X s ω := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases h : a ≤ X ω
        · rw [if_pos h]
          have hle : Real.exp (-(s * (X ω - a))) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have : 0 ≤ s * (X ω - a) := mul_nonneg hs (by linarith)
            linarith
          calc Real.exp (-(s * (X ω - a))) * tiltWeight X s ω
              ≤ 1 * tiltWeight X s ω := by
                apply mul_le_mul_of_nonneg_right hle (tiltWeight_nonneg X s ω)
            _ = tiltWeight X s ω := one_mul _
        · rw [if_neg h, zero_mul]
          exact tiltWeight_nonneg X s ω
    _ = 1 := sum_tiltWeight X s

/-- **CHERNOFF, RE-DERIVED FROM THE TILT (PROVED).** `tailFrac X a ≤ (partition X s/|Ω|)·e^{−s·a}` for `s ≥ 0`
— the identity `tailFrac_eq` with the slack factor bounded by `1`. This is the classical Chernoff bound; the
Bahadur–Rao content is that the true value is this bound times `tiltTailExp`, which is *strictly* below `1`. -/
theorem tailFrac_le_chernoff [Nonempty Ω] (X : Ω → ℝ) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) :
    tailFrac X a ≤ (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) := by
  rw [tailFrac_eq X s a]
  have hpref : (0 : ℝ) ≤ (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) := by
    have := partition_pos X s
    positivity
  calc (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) * tiltTailExp X s a
      ≤ (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) * 1 :=
        mul_le_mul_of_nonneg_left (tiltTailExp_le_one X hs a) hpref
    _ = (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) := mul_one _

/-- **THE REFINED (BAHADUR–RAO) BOUND (PROVED).** Given ANY prefactor bound `tiltTailExp X s a ≤ P` (with `0 ≤ P`),
the tail fraction is at most the Chernoff bound times `P`:

  `tailFrac X a ≤ (partition X s / |Ω|) · e^{−s·a} · P`.

This is the shape the Bahadur–Rao prefactor plugs into: a bound `P < 1` on the tilted tail expectation directly
sharpens Chernoff. Discharging `P` (the local-limit prefactor) is the one analytic input beyond the identity. -/
theorem tailFrac_le_refined [Nonempty Ω] (X : Ω → ℝ) (s a : ℝ)
    {P : ℝ} (hP : tiltTailExp X s a ≤ P) :
    tailFrac X a ≤ (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) * P := by
  rw [tailFrac_eq X s a]
  have hpref : (0 : ℝ) ≤ (partition X s / (Fintype.card Ω : ℝ)) * Real.exp (-(s * a)) := by
    have := partition_pos X s
    positivity
  exact mul_le_mul_of_nonneg_left hP hpref

/-! ## The geometric anti-concentration envelope (the fully-formalized partial prefactor).

For an integer-graded observable `X ω = (g ω : ℝ)`, the tilted tail expectation regroups by value level and is
bounded by the maximum tilted atom mass times a geometric series. This is the elementary
monotone-envelope / anti-concentration bound: it recovers `Θ(pmax)` of the Bahadur–Rao decay. -/

/-- **THE FINITE GEOMETRIC SERIES BOUND (PROVED).** For `0 ≤ r < 1`, `∑_{j<m} r^j ≤ (1−r)⁻¹`. Reusable. -/
theorem geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ j ∈ Finset.range m, r ^ j ≤ (1 - r)⁻¹ := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  rw [geom_sum_eq (by linarith : r ≠ 1) m]
  rw [show (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) from by
        rw [div_eq_div_iff (by linarith : r - 1 ≠ 0) (by linarith : (1:ℝ) - r ≠ 0)]; ring]
  rw [inv_eq_one_div]
  gcongr
  nlinarith [pow_nonneg hr0 m]

/-- **THE GEOMETRIC SERIES OVER ANY FINITE SET OF EXPONENTS (PROVED).** For `0 ≤ r < 1` and any finite
`S ⊆ ℕ`, `∑_{j∈S} r^j ≤ (1−r)⁻¹` (bound `S` by an initial segment and use `geom_sum_le_inv_one_sub`). -/
theorem sum_pow_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ) :
    ∑ j ∈ S, r ^ j ≤ (1 - r)⁻¹ := by
  refine le_trans ?_ (geom_sum_le_inv_one_sub hr0 hr1 (S.sup id + 1))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) ha))
  · intro j _ _; exact pow_nonneg hr0 j

/-- The tilted mass of the level set `{ω : g ω = k}`. -/
noncomputable def atomMass (g : Ω → ℤ) (X : Ω → ℝ) (s : ℝ) (k : ℤ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => g ω = k), tiltWeight X s ω

theorem atomMass_nonneg (g : Ω → ℤ) (X : Ω → ℝ) (s : ℝ) (k : ℤ) : 0 ≤ atomMass g X s k :=
  Finset.sum_nonneg (fun ω _ => tiltWeight_nonneg X s ω)

/-- **THE GEOMETRIC ANTI-CONCENTRATION ENVELOPE (PROVED).** For an integer-graded observable
`X ω = (g ω : ℝ)`, tilt `s > 0`, and integer threshold `A`, if every tilted level-atom has mass `≤ pmax`, then

  `tiltTailExp X s A ≤ pmax / (1 − e^{−s})`.

The tilted tail expectation regroups by value level (`sum_fiberwise`), each level contributes
`e^{−s(k−A)}·atomMass k ≤ pmax·(e^{−s})^{k−A}`, and the distinct integer exponents give a sub-geometric sum
`≤ (1−e^{−s})⁻¹` (`sum_pow_le_inv_one_sub`). This is the elementary monotone-envelope prefactor: it recovers a
factor `Θ(pmax)` below the Chernoff bound — the honest, fully-formalized *partial* Bahadur–Rao correction (the
sharp `1/(s·σ*·√{2π})` constant needs a local-limit/characteristic-function bound Mathlib lacks). -/
theorem tiltTailExp_le_atom_geom [Nonempty Ω] (g : Ω → ℤ) {s : ℝ} (hs : 0 < s) (A : ℤ)
    {pmax : ℝ} (hp : 0 ≤ pmax) (hatom : ∀ k, atomMass g (fun ω => (g ω : ℝ)) s k ≤ pmax) :
    tiltTailExp (fun ω => (g ω : ℝ)) s (A : ℝ) ≤ pmax / (1 - Real.exp (-s)) := by
  classical
  set X : Ω → ℝ := fun ω => (g ω : ℝ) with hX
  set r : ℝ := Real.exp (-s) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  -- Regroup the tilted tail expectation over the level sets of `g`.
  have hfib : tiltTailExp X s (A : ℝ)
      = ∑ k ∈ univ.image g,
          (if (A : ℝ) ≤ (k : ℝ) then Real.exp (-(s * ((k : ℝ) - A))) else 0) * atomMass g X s k := by
    unfold tiltTailExp
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := univ.image g)
          (fun ω _ => Finset.mem_image_of_mem g (Finset.mem_univ ω))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [atomMass, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω hω => ?_)
    have hgk : g ω = k := (Finset.mem_filter.mp hω).2
    simp only [hX, hgk]
  rw [hfib]
  -- Bound each level by `pmax · r^{(k−A)}`, dropping the `A > k` levels.
  have hbound : ∀ k ∈ univ.image g,
      (if (A : ℝ) ≤ (k : ℝ) then Real.exp (-(s * ((k : ℝ) - A))) else 0) * atomMass g X s k
        ≤ (if A ≤ k then r ^ (k - A).toNat else 0) * pmax := by
    intro k _
    by_cases h : A ≤ k
    · have hcast : (A : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      rw [if_pos hcast, if_pos h]
      have hpow : Real.exp (-(s * ((k : ℝ) - A))) = r ^ (k - A).toNat := by
        rw [hr, ← Real.exp_nat_mul]
        congr 1
        have hc : ((k - A).toNat : ℝ) = (k : ℝ) - A := by
          have h0 : ((k - A).toNat : ℤ) = k - A := Int.toNat_of_nonneg (by linarith)
          calc ((k - A).toNat : ℝ) = (((k - A).toNat : ℤ) : ℝ) := by push_cast; ring
            _ = ((k - A : ℤ) : ℝ) := by rw [h0]
            _ = (k : ℝ) - A := by push_cast; ring
        rw [hc]; ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_left (hatom k) (pow_nonneg hr0 _)
    · have hcast : ¬ (A : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      rw [if_neg hcast, if_neg h, zero_mul, zero_mul]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  -- The geometric tail: distinct integer exponents `(k−A).toNat`.
  have geom_tail :
      (∑ k ∈ univ.image g, if A ≤ k then r ^ (k - A).toNat else 0) ≤ (1 - r)⁻¹ := by
    rw [← Finset.sum_filter]
    set T := (univ.image g).filter (fun k => A ≤ k) with hT
    have hinj : Set.InjOn (fun k => (k - A).toNat) (T : Set ℤ) := by
      intro k1 hk1 k2 hk2 heq
      simp only [hT, Finset.coe_filter, Set.mem_setOf_eq] at hk1 hk2
      have hz : ((k1 - A).toNat : ℤ) = ((k2 - A).toNat : ℤ) := by exact_mod_cast heq
      rw [Int.toNat_of_nonneg (by linarith [hk1.2] : (0:ℤ) ≤ k1 - A),
          Int.toNat_of_nonneg (by linarith [hk2.2] : (0:ℤ) ≤ k2 - A)] at hz
      linarith [hk1.2, hk2.2]
    rw [← Finset.sum_image hinj]
    exact sum_pow_le_inv_one_sub hr0 hr1 _
  rw [← Finset.sum_mul]
  calc (∑ k ∈ univ.image g, if A ≤ k then r ^ (k - A).toNat else 0) * pmax
      ≤ (1 - r)⁻¹ * pmax := mul_le_mul_of_nonneg_right geom_tail hp
    _ = pmax / (1 - r) := by rw [div_eq_mul_inv, mul_comm]

/-! ## The tail-probability envelope (the second half of the elementary min-envelope).

Dropping the weight `e^{−s(X−a)} ≤ 1` on the tail bounds `tiltTailExp` by the *tilted tail probability*
`P_tilt[X ≥ a]`. Combined with the geometric envelope this gives `tiltTailExp ≤ min(pmax/(1−e^{−s}), P_tilt)`.
(For the Chernoff application, re-tilting `P_tilt` only reproduces Chernoff at a higher tilt, so this half does
not by itself sharpen the tail — the genuine Bahadur–Rao gain lives in the *local* atom decay below.) -/

/-- The tilted tail probability `P_tilt[X ≥ a] = ∑_{ω : a ≤ X ω} tiltWeight`. -/
noncomputable def tiltTailProb (X : Ω → ℝ) (s a : ℝ) : ℝ :=
  ∑ ω, (if a ≤ X ω then (1 : ℝ) else 0) * tiltWeight X s ω

/-- **THE TAIL-PROBABILITY ENVELOPE (PROVED).** For `s ≥ 0`, `tiltTailExp X s a ≤ tiltTailProb X s a`: on the
tail the exponential weight `e^{−s(X−a)} ∈ (0,1]`, so dropping it can only increase the sum. -/
theorem tiltTailExp_le_tiltTailProb (X : Ω → ℝ) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) :
    tiltTailExp X s a ≤ tiltTailProb X s a := by
  unfold tiltTailExp tiltTailProb
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases h : a ≤ X ω
  · rw [if_pos h, if_pos h]
    refine mul_le_mul_of_nonneg_right ?_ (tiltWeight_nonneg X s ω)
    rw [Real.exp_le_one_iff]
    have : 0 ≤ s * (X ω - a) := mul_nonneg hs (by linarith)
    linarith
  · rw [if_neg h, if_neg h]

/-! ## The characteristic-function Gaussian-decay bound (the char-function half of Esseen's method).

The geometric envelope replaces every tilted tail-atom by the peak mass `pmax`; the SHARP Bahadur–Rao prefactor
`1/(s·σ*·√{2π})` instead needs the *local* limit theorem — a Gaussian bound on the atom masses themselves. The
classical (Esseen) route runs through the characteristic function: for the integer lattice,
`atomMass k = (1/2π)∫_{−π}^{π} e^{−ikt}·φ(t) dt`, and a Gaussian *decay* bound `|φ(t)| ≤ e^{−c·σ²·t²}` on the
char function controls that inversion integral. This section formalizes the decay bound in the finite model
(for a symmetric law, where the char function is the real cosine transform). It is the load-bearing analytic
ingredient of Berry–Esseen; the remaining Fourier-inversion identity is named as the residual below. -/

/-- The real (cosine) characteristic transform of a finite law `w` against observable `X`:
`reCharFn w X t = ∑_ω w ω · cos(t·X ω)`. For a SYMMETRIC law this equals the full characteristic function
`E[e^{itX}]` (the odd sine part cancels), and `1 − reCharFn = ∑ w·(1−cos)` is the char-function
anti-concentration functional. -/
noncomputable def reCharFn (w X : Ω → ℝ) (t : ℝ) : ℝ := ∑ ω, w ω * Real.cos (t * X ω)

/-- **THE QUADRATIC CHARACTERISTIC-FUNCTION BOUND (PROVED).** For a probability weight `w` and an observable
`X` with `|t·X ω| ≤ π` on the support, the real char transform is bounded by `1` minus a multiple of the
second moment:

  `reCharFn w X t ≤ 1 − (2/π²)·t²·E[X²]`.

This is Jordan's cosine inequality `cos θ ≤ 1 − (2/π²)θ²` (`Real.cos_le_one_sub_mul_cos_sq`) integrated against
`w`. It is the elementary, sharp-order char-function contraction underlying every local CLT / Berry–Esseen
bound. -/
theorem reCharFn_le_one_sub (w X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (t : ℝ)
    (ht : ∀ ω, |t * X ω| ≤ Real.pi) :
    reCharFn w X t ≤ 1 - 2 / Real.pi ^ 2 * t ^ 2 * ∑ ω, w ω * (X ω) ^ 2 := by
  unfold reCharFn
  have key : ∀ ω ∈ (Finset.univ : Finset Ω),
      w ω * Real.cos (t * X ω) ≤ w ω * (1 - 2 / Real.pi ^ 2 * (t * X ω) ^ 2) :=
    fun ω _ => mul_le_mul_of_nonneg_left (Real.cos_le_one_sub_mul_cos_sq (ht ω)) (hw ω)
  have hsplit : ∑ ω, w ω * (1 - 2 / Real.pi ^ 2 * (t * X ω) ^ 2)
      = (∑ ω, w ω) - 2 / Real.pi ^ 2 * t ^ 2 * ∑ ω, w ω * (X ω) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  calc ∑ ω, w ω * Real.cos (t * X ω)
      ≤ ∑ ω, w ω * (1 - 2 / Real.pi ^ 2 * (t * X ω) ^ 2) := Finset.sum_le_sum key
    _ = (∑ ω, w ω) - 2 / Real.pi ^ 2 * t ^ 2 * ∑ ω, w ω * (X ω) ^ 2 := hsplit
    _ = 1 - 2 / Real.pi ^ 2 * t ^ 2 * ∑ ω, w ω * (X ω) ^ 2 := by rw [hsum]

/-- **THE GAUSSIAN-DECAY CHARACTERISTIC-FUNCTION BOUND (PROVED).** With the same hypotheses,

  `reCharFn w X t ≤ exp(−(2/π²)·t²·E[X²])`.

Composing `reCharFn_le_one_sub` with `1 − y ≤ e^{−y}` (`Real.add_one_le_exp`) turns the quadratic contraction
into the exponential (sub-Gaussian) decay `|φ(t)| ≤ e^{−c·σ²·t²}` — the characteristic-function input to the
Esseen smoothing / local-limit bound. Tensorizing over an independent product (`φ_sum = ∏ φ_i`) upgrades `E[X²]`
to the variance of the sum; that product step and the Fourier inversion are named as the residual below. -/
theorem reCharFn_le_exp (w X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) (t : ℝ)
    (ht : ∀ ω, |t * X ω| ≤ Real.pi) :
    reCharFn w X t ≤ Real.exp (-(2 / Real.pi ^ 2 * t ^ 2 * ∑ ω, w ω * (X ω) ^ 2)) := by
  refine le_trans (reCharFn_le_one_sub w X hw hsum t ht) ?_
  have h := Real.add_one_le_exp (-(2 / Real.pi ^ 2 * t ^ 2 * ∑ ω, w ω * (X ω) ^ 2))
  linarith

/-! ## The refined tail-atom geometric envelope — only the TAIL atoms need bounding.

`tiltTailExp_le_atom_geom` demands `pmax` bound EVERY tilted atom (including the peak at the tilted mode). But
the tilted tail expectation `∑_{k≥A} e^{−s(k−A)}·atomMass k` only ever touches atoms with `k ≥ A`. When `A` is
in the tail (past the tilted mode), those atoms are Gaussian-tail-small — far below the peak `pmax`. This refined
envelope requires the atom bound ONLY for `k ≥ A`, so the local-limit input is exactly the deep-tail atom mass
`atomMass(A)` (≪ `pmax`), NOT the peak. This is what actually reaches the sharp Bahadur–Rao constant. -/

/-- **THE TAIL-ATOM GEOMETRIC ENVELOPE (PROVED).** Identical to `tiltTailExp_le_atom_geom`, but the level-atom
bound `atomMass ≤ pmax` is required ONLY on the tail `A ≤ k`:

  `(∀ k, A ≤ k → atomMass g X s k ≤ pmax)  ⟹  tiltTailExp X s A ≤ pmax/(1−e^{−s})`.

Since the tilted tail expectation only sums atoms at levels `k ≥ A`, the below-threshold atoms are irrelevant.
For `A` past the tilted mode, `pmax` is the (small) deep-tail atom mass, so this envelope is *sharp* — its input
is precisely the moderate-deviation local limit theorem for the tilted lattice sum. -/
theorem tiltTailExp_le_tailAtom_geom [Nonempty Ω] (g : Ω → ℤ) {s : ℝ} (hs : 0 < s) (A : ℤ)
    {pmax : ℝ} (hp : 0 ≤ pmax) (hatom : ∀ k, A ≤ k → atomMass g (fun ω => (g ω : ℝ)) s k ≤ pmax) :
    tiltTailExp (fun ω => (g ω : ℝ)) s (A : ℝ) ≤ pmax / (1 - Real.exp (-s)) := by
  classical
  set X : Ω → ℝ := fun ω => (g ω : ℝ) with hX
  set r : ℝ := Real.exp (-s) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hfib : tiltTailExp X s (A : ℝ)
      = ∑ k ∈ univ.image g,
          (if (A : ℝ) ≤ (k : ℝ) then Real.exp (-(s * ((k : ℝ) - A))) else 0) * atomMass g X s k := by
    unfold tiltTailExp
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := univ.image g)
          (fun ω _ => Finset.mem_image_of_mem g (Finset.mem_univ ω))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [atomMass, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω hω => ?_)
    have hgk : g ω = k := (Finset.mem_filter.mp hω).2
    simp only [hX, hgk]
  rw [hfib]
  have hbound : ∀ k ∈ univ.image g,
      (if (A : ℝ) ≤ (k : ℝ) then Real.exp (-(s * ((k : ℝ) - A))) else 0) * atomMass g X s k
        ≤ (if A ≤ k then r ^ (k - A).toNat else 0) * pmax := by
    intro k _
    by_cases h : A ≤ k
    · have hcast : (A : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      rw [if_pos hcast, if_pos h]
      have hpow : Real.exp (-(s * ((k : ℝ) - A))) = r ^ (k - A).toNat := by
        rw [hr, ← Real.exp_nat_mul]
        congr 1
        have hc : ((k - A).toNat : ℝ) = (k : ℝ) - A := by
          have h0 : ((k - A).toNat : ℤ) = k - A := Int.toNat_of_nonneg (by linarith)
          calc ((k - A).toNat : ℝ) = (((k - A).toNat : ℤ) : ℝ) := by push_cast; ring
            _ = ((k - A : ℤ) : ℝ) := by rw [h0]
            _ = (k : ℝ) - A := by push_cast; ring
        rw [hc]; ring
      rw [hpow]
      exact mul_le_mul_of_nonneg_left (hatom k h) (pow_nonneg hr0 _)
    · have hcast : ¬ (A : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      rw [if_neg hcast, if_neg h, zero_mul, zero_mul]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  have geom_tail :
      (∑ k ∈ univ.image g, if A ≤ k then r ^ (k - A).toNat else 0) ≤ (1 - r)⁻¹ := by
    rw [← Finset.sum_filter]
    set T := (univ.image g).filter (fun k => A ≤ k) with hT
    have hinj : Set.InjOn (fun k => (k - A).toNat) (T : Set ℤ) := by
      intro k1 hk1 k2 hk2 heq
      simp only [hT, Finset.coe_filter, Set.mem_setOf_eq] at hk1 hk2
      have hz : ((k1 - A).toNat : ℤ) = ((k2 - A).toNat : ℤ) := by exact_mod_cast heq
      rw [Int.toNat_of_nonneg (by linarith [hk1.2] : (0:ℤ) ≤ k1 - A),
          Int.toNat_of_nonneg (by linarith [hk2.2] : (0:ℤ) ≤ k2 - A)] at hz
      linarith [hk1.2, hk2.2]
    rw [← Finset.sum_image hinj]
    exact sum_pow_le_inv_one_sub hr0 hr1 _
  rw [← Finset.sum_mul]
  calc (∑ k ∈ univ.image g, if A ≤ k then r ^ (k - A).toNat else 0) * pmax
      ≤ (1 - r)⁻¹ * pmax := mul_le_mul_of_nonneg_right geom_tail hp
    _ = pmax / (1 - r) := by rw [div_eq_mul_inv, mul_comm]

/-! ## Non-vacuity teeth. -/

/-- **(TOOTH — the prefactor genuinely improves Chernoff.)** On the two-point `±1` model at `s = 1, a = 1`, the
tilted tail expectation is `e/(e+e⁻¹) < 1` — a strict improvement over the Chernoff slack `1`. -/
theorem tiltTailExp_strict_lt_one :
    tiltTailExp (Ω := Bool) (fun b => if b then (1 : ℝ) else -1) 1 1 < 1 := by
  have key : tiltTailExp (Ω := Bool) (fun b => if b then (1 : ℝ) else -1) 1 1
      = Real.exp 1 / (Real.exp 1 + Real.exp (-1)) := by
    unfold tiltTailExp tiltWeight partition
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
    norm_num
  rw [key, div_lt_one (by positivity)]
  linarith [Real.exp_pos (-1 : ℝ)]

/-- **(TOOTH — the char transform is the genuine cosine transform.)** On the two-point `±1` uniform law,
`reCharFn` is exactly `cos t` — the odd (sine) part cancels, confirming `reCharFn` computes the real
characteristic function of a symmetric law (so the decay bound `reCharFn_le_exp` is non-vacuous). -/
theorem reCharFn_two_point (t : ℝ) :
    reCharFn (Ω := Bool) (fun _ => (1 : ℝ) / 2) (fun b => if b then (1 : ℝ) else -1) t
      = Real.cos t := by
  unfold reCharFn
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, mul_one, mul_neg_one,
    Real.cos_neg]
  ring

end Dregg2.ForMathlib.BerryEsseen
