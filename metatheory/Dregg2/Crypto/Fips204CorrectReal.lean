/-
# `Dregg2.Crypto.Fips204CorrectReal` — the ML-DSA correctness round-trip at REAL ML-DSA-65 DIMENSION.

`Fips204Spec.lean` proves `fips204_correct` for ANY `MlDsaParams (R M N HB Hint Cbar Msg)` whose
`RoundingScheme` satisfies its two lemma-fields — GENERIC over the ring and a LINEAR `A : M →ₗ[R] N`.
`Fips204Verify.lean::realParams` instantiates it only at the SCALAR caricature (`A = LinearMap.id`,
`R = M = N = ℤ`, `n = 1`) — the round-trip is proven, but over a single integer, not over the ring.

THIS FILE instantiates the SAME generic `fips204_correct` at the REAL ML-DSA-65 dimension, so the
round-trip is proven over `R_q^k` with the genuine negacyclic ring `R_q = ℤ_q[X]/(X²⁵⁶+1)`:

* **THE RING IS REAL.** `Rq := AdjoinRoot (X²⁵⁶ + 1 : (ZMod q)[X])`, `q = 8380417` (BRICK 2's `q`).
  This is `ℤ_q[X]/(X²⁵⁶+1)` — char `q`, quotient degree `256`. `root_pow_256` proves `root²⁵⁶ = −1` in
  the ring (the negacyclic relation), `realDim` proves the power-basis dimension is exactly `256`. NOT a
  scalar, NOT `ℤ`, NOT `n = 1`.

* **THE MODULES ARE REAL.** `M := Fin ℓ → Rq` (`ℓ = 5`), `N := Fin k → Rq` (`k = 6`) — the genuine
  `R_q^ℓ`, `R_q^k` (ML-DSA-65's `(k, ℓ) = (6, 5)`), as `Rq`-modules (the automatic `Pi` instances). `A`
  is any concrete `R_q`-linear map (`fips204_correct` needs ONLY linearity, so it is a variable).

* **THE ROUNDING IS REAL, COMPONENTWISE.** `realRoundingK : RoundingScheme N _ _` applies the FIPS 204
  round-to-nearest decomposition (`highBits r = ⌊(r+γ₂)/α⌋`, `α = 523776`, `γ₂ = 261888`, `β = 196`) to
  EACH of the `k` polynomials, EACH of its `256` `ℤ_q`-coefficients — over the real `256·k` coefficient
  space, NOT `n = 1`. Its two `RoundingScheme` lemma-fields are PROVED at `N`:

    - `useHint_makeHint` — the hint round-trip. Holds per-coefficient by telescoping (the makeHint is the
      literal difference of high-bits), lifted through the `Fin k × Fin (256)` product by `funext`.
    - `highBits_stable` — high-bits stability under a `β`-small perturbation. This is THE load-bearing
      proof: per-coefficient it is the FIPS stability fact over `ℤ_q` (the `ZMod q` addition wraps mod
      `q`), discharged by `omega` over the deployed literals (`percoeff_highBits_stable`), then lifted
      through the coefficient product via the ADDITIVE coefficient map `rv` (`rv_add`, from
      `Basis.repr`'s `map_add` + `ZMod.val_add`).

* **THE ROUND-TRIP.** `fips204_correct_real` is `fips204_correct realParamsK` — the honest ML-DSA-65
  signature verifies, over `R_q^k`. `fips204_correct_real_accepts` exhibits a CONCRETE honest instance
  whose bounds all hold (a gapped commitment built from the power basis), so the hypotheses are NOT
  vacuous. `#print axioms` is `{propext, Classical.choice, Quot.sound}` — no `sorryAx`.

## HONEST BOUNDARY

The rounding is over the `ℤ`-lift of each `ℤ_q`-coefficient (`ZMod.val`), and `highBits_stable`'s
per-coefficient `omega` handles the `mod q` wrap of `ZMod q` addition on the constrained ranges the
`lowGap`/`betaSmall` predicates carve out. The FIPS `Decompose` `q−1` boundary special case is excluded
by `lowGap` (it requires the low part in `[β, α−β)` AND the value in `[β, q−β)`), exactly as in
`Fips204Verify.realRounding` — the same named number-theoretic residual, now over the real ring.
-/
import Dregg2.Crypto.Fips204Spec
import Dregg2.Crypto.MlDsaRing
import Mathlib

namespace Dregg2.Crypto.Fips204CorrectReal

open Dregg2.Crypto.Fips204Spec
open Polynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-! ## PART 1 — the REAL ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` and its power-basis coefficients. -/

/-- ML-DSA-65 modulus, `q = 8380417`. -/
abbrev q : ℕ := 8380417

/-- Reuse of BRICK 2's modulus: this `q` IS `MlDsaRing.q` (definitional). -/
theorem q_eq_ring : q = Dregg2.Crypto.MlDsaRing.q := rfl

theorem q_val : q = 8380417 := rfl

instance : Fact (1 < q) := ⟨by rw [q_val]; norm_num⟩
instance : NeZero q := ⟨by rw [q_val]; norm_num⟩

/-- `X²⁵⁶ + 1` is monic over `ℤ_q`. -/
theorem xpow_monic : (X ^ 256 + 1 : (ZMod q)[X]).Monic := by
  apply Monic.add_of_left (monic_X_pow 256)
  rw [degree_X_pow, degree_one]; norm_num

/-- `X²⁵⁶ + 1` has degree exactly `256` (the quotient degree). -/
theorem xpow_natDeg : (X ^ 256 + 1 : (ZMod q)[X]).natDegree = 256 := by compute_degree!

/-- **THE REAL RING** `R_q = ℤ_q[X]/(X²⁵⁶+1)` — char `q`, quotient degree `256`. -/
noncomputable abbrev Rq := AdjoinRoot (X ^ 256 + 1 : (ZMod q)[X])

/-- The `ℤ_q`-power basis of `R_q` (`1, root, …, root²⁵⁵`). -/
noncomputable def pb : PowerBasis (ZMod q) Rq := AdjoinRoot.powerBasis' xpow_monic

/-- **NON-VACUITY (dimension):** the ring's power-basis dimension is exactly `256` — this is a genuine
degree-`256` extension, not a scalar. -/
theorem realDim : pb.dim = 256 := by
  unfold pb; rw [AdjoinRoot.powerBasis'_dim]; exact xpow_natDeg

theorem dim_pos : 0 < pb.dim := by rw [realDim]; norm_num

/-- **NON-VACUITY (negacyclic relation):** `root²⁵⁶ = −1` in `R_q` — the `X²⁵⁶ = −1` law of the real
ML-DSA ring holds, so the quotient is genuine (not the trivial ring, not `ℤ`). -/
theorem root_pow_256 : (AdjoinRoot.root (X ^ 256 + 1 : (ZMod q)[X])) ^ 256 = -1 := by
  have h : AdjoinRoot.mk (X ^ 256 + 1 : (ZMod q)[X]) (X ^ 256 + 1) = 0 := AdjoinRoot.mk_self
  have hr : (AdjoinRoot.root (X ^ 256 + 1 : (ZMod q)[X])) ^ 256 + 1 = 0 := by
    simpa [map_add, map_pow, map_one, AdjoinRoot.mk_X] using h
  linear_combination hr

/-- The `ℤ`-lift of coefficient `j` of a ring element `x` (its `ℤ_q` power-basis coordinate, the
canonical representative in `[0, q)`). This is the object the componentwise rounding sees. -/
noncomputable def rv (x : Rq) (j : Fin pb.dim) : ℤ := ((pb.basis.repr x j).val : ℤ)

theorem rv_nonneg (x : Rq) (j : Fin pb.dim) : 0 ≤ rv x j := by
  unfold rv; positivity

theorem rv_lt (x : Rq) (j : Fin pb.dim) : rv x j < 8380417 := by
  unfold rv
  have h : (pb.basis.repr x j).val < q := ZMod.val_lt _
  have h2 : ((pb.basis.repr x j).val : ℤ) < ((q : ℕ) : ℤ) := by exact_mod_cast h
  simpa using h2

/-- **The coefficient map is ADDITIVE, modulo the `ℤ_q` wrap.** `rv (x + y) j = (rv x j + rv y j) % q`.
This is the bridge that lifts the per-coefficient rounding facts through the ring's additive structure:
`Basis.repr` is `ℤ_q`-linear (`map_add`), and `ZMod.val` of a sum wraps mod `q` (`ZMod.val_add`). -/
theorem rv_add (x y : Rq) (j : Fin pb.dim) : rv (x + y) j = (rv x j + rv y j) % 8380417 := by
  unfold rv
  rw [map_add, Finsupp.add_apply]
  rw [ZMod.val_add]
  push_cast
  ring

/-- Build a ring element with PRESCRIBED power-basis coordinates (used for the non-vacuity witness). -/
noncomputable def mkElt (cv : Fin pb.dim → ZMod q) : Rq := pb.basis.equivFun.symm cv

theorem mkElt_coeff (cv : Fin pb.dim → ZMod q) (j : Fin pb.dim) :
    pb.basis.repr (mkElt cv) j = cv j := by
  have h : pb.basis.equivFun (mkElt cv) = cv := LinearEquiv.apply_symm_apply _ _
  simpa using congrFun h j

/-! ## PART 2 — the REAL modules `R_q^ℓ`, `R_q^k` and the FIPS 204 deployed rounding literals. -/

/-- ML-DSA-65: `ℓ = 5`. -/
abbrev ell : ℕ := 5
/-- ML-DSA-65: `k = 6`. -/
abbrev kk : ℕ := 6

/-- The secret/response module `M = R_q^ℓ`. -/
abbrev M := Fin ell → Rq
/-- The commitment module `N = R_q^k`. -/
abbrev N := Fin kk → Rq

/-- The rounding high-bits/hint coefficient type: `k` polynomials × `256` coefficients of `ℤ`. -/
abbrev Coeffs := Fin kk → Fin pb.dim → ℤ

/-! ## PART 3 — the REAL componentwise `RoundingScheme` over `N = R_q^k`, its two lemmas DISCHARGED.

Deployed ML-DSA-65 literals (FIPS 204 Table 1): `q = 8380417`, `γ₂ = 261888`, `α = 2γ₂ = 523776`,
`β = τη = 196`, `γ₁ − β = 524092` — EXACTLY `Fips204Verify.realRounding`, now applied to each of the
`256·k` coefficients of `N`. -/

/-- **THE LOAD-BEARING PER-COEFFICIENT LEMMA — high-bits stability over `ℤ_q`.** For a coefficient value
`a ∈ [β, q−β)` whose low part `(a+γ₂) mod α` sits in the gap `[β, α−β)`, a `β`-small perturbation `b`
(represented in `[0, q)` as `≤ β` or `≥ q−β`, i.e. small ±) does not change the high bits — EVEN under
the `ℤ_q` wrap `(a+b) mod q`. Discharged by `omega` over the deployed literals (the FIPS 204 stability
fact; the `q−1` `Decompose` boundary is excluded by the `[β, q−β)` value constraint). -/
theorem percoeff_highBits_stable (a b : ℤ)
    (ha0 : 0 ≤ a) (haq : a < 8380417) (hb0 : 0 ≤ b) (hbq : b < 8380417)
    (hlo : 196 ≤ a) (hhi : a < 8380417 - 196)
    (hsmall : b ≤ 196 ∨ 8380417 - 196 ≤ b)
    (hgap1 : 196 ≤ (a + 261888) % 523776) (hgap2 : (a + 261888) % 523776 < 523776 - 196) :
    ((a + b) % 8380417 + 261888) / 523776 = (a + 261888) / 523776 := by
  omega

/-- **The REAL ML-DSA-65 rounding over `N = R_q^k`, applied COMPONENTWISE.** `highBits`/`makeHint`/
`useHint` apply the deployed `ℤ`-rounding to each polynomial's each coefficient (`rv`); the norm
predicates are the coefficientwise deployed bounds. Both `RoundingScheme` lemma-fields are PROVED at
`N`: `useHint_makeHint` telescopes per coefficient, `highBits_stable` lifts `percoeff_highBits_stable`
through the coefficient product via `rv_add`. -/
noncomputable def realRoundingK : RoundingScheme N Coeffs Coeffs where
  highBits x := fun i j => (rv (x i) j + 261888) / 523776
  makeHint z r := fun i j =>
    (rv ((r + z) i) j + 261888) / 523776 - (rv (r i) j + 261888) / 523776
  useHint h r := fun i j => (rv (r i) j + 261888) / 523776 + h i j
  nearGamma2 z := ∀ i j, rv (z i) j ≤ 261888 ∨ 8380417 - 261888 ≤ rv (z i) j
  betaSmall s := ∀ i j, rv (s i) j ≤ 196 ∨ 8380417 - 196 ≤ rv (s i) j
  lowGap r := ∀ i j, 196 ≤ rv (r i) j ∧ rv (r i) j < 8380417 - 196 ∧
    196 ≤ (rv (r i) j + 261888) % 523776 ∧ (rv (r i) j + 261888) % 523776 < 523776 - 196
  useHint_makeHint z r _ := by
    funext i j
    show (rv (r i) j + 261888) / 523776 +
      ((rv ((r + z) i) j + 261888) / 523776 - (rv (r i) j + 261888) / 523776)
      = (rv ((r + z) i) j + 261888) / 523776
    ring
  highBits_stable r s hlow hbeta := by
    funext i j
    show (rv ((r + s) i) j + 261888) / 523776 = (rv (r i) j + 261888) / 523776
    have hadd : rv ((r + s) i) j = (rv (r i) j + rv (s i) j) % 8380417 := by
      have : (r + s) i = r i + s i := rfl
      rw [this, rv_add]
    rw [hadd]
    obtain ⟨h1, h2, h3, h4⟩ := hlow i j
    exact percoeff_highBits_stable (rv (r i) j) (rv (s i) j)
      (rv_nonneg _ _) (rv_lt _ _) (rv_nonneg _ _) (rv_lt _ _) h1 h2 (hbeta i j) h3 h4

/-! ## PART 4 — the REAL ML-DSA-65 verify instance and the correctness ROUND-TRIP. -/

/-- **The REAL ML-DSA-65 verify instance over `R_q^k`.** `A` is a variable `R_q`-linear map (correctness
is generic over which matrix); the challenge is the constant `1` (`SampleInBall` abstracted, `c = 1`, so
the module action `1 • ·` is genuine); `hash` is abstract; the response gate is the deployed `‖z‖ <
γ₁−β = 524092` on each coefficient. This is `Fips204Verify.realParams` LIFTED from `n = 1` to `R_q^k`. -/
noncomputable def realParamsK (A : M →ₗ[Rq] N) : MlDsaParams Rq M N Coeffs Coeffs ℤ ℤ where
  A := A
  round := realRoundingK
  hash _ _ := 0
  challenge _ := 1
  zBoundB z := decide (∀ i j, rv (z i) j < 524092 ∨ 8380417 - 524092 < rv (z i) j)

/-- **`fips204_correct_real` — THE REAL-DIMENSION CORRECTNESS ROUND-TRIP.** For any `R_q`-linear `A` and
any honest ML-DSA-65 signing data whose post-rejection bounds hold, the verifier ACCEPTS — over the real
`R_q^k` (`R_q = ℤ_q[X]/(X²⁵⁶+1)`, `n = 256`, `(k,ℓ) = (6,5)`), NOT the scalar caricature. This is the
generic `Fips204Spec.fips204_correct` applied to `realParamsK`. -/
theorem fips204_correct_real (A : M →ₗ[Rq] N)
    (s1 : M) (s2 t0 thi : N) (μ : ℤ) (y : M) (c : Rq)
    (hc : c = (realParamsK A).challenge
      ((realParamsK A).hash μ ((realParamsK A).round.highBits ((realParamsK A).A y))))
    (hkey : (realParamsK A).A s1 + s2 = thi + t0)
    (hct0 : (realParamsK A).round.nearGamma2 (-(c • t0)))
    (hcs2 : (realParamsK A).round.betaSmall (-(c • s2)))
    (hlow : (realParamsK A).round.lowGap ((realParamsK A).A y))
    (hz : (realParamsK A).zBoundB (y + c • s1) = true) :
    (realParamsK A).verifyB thi μ ((realParamsK A).sign s1 s2 t0 μ y) = true :=
  fips204_correct (realParamsK A) s1 s2 t0 thi μ y c hc hkey hct0 hcs2 hlow hz

/-! ## PART 5 — NON-VACUITY: a CONCRETE honest instance whose bounds all hold, over `R_q^k`. -/

/-- A gapped ring element: every one of its `256` coefficients is `300000 ∈ [β, q−β)` with low part
`(300000+γ₂) mod α = 38112 ∈ [β, α−β)` — so `lowGap` holds. -/
noncomputable def gappedElt : Rq := mkElt (fun _ => (300000 : ZMod q))

theorem gappedElt_rv (j : Fin pb.dim) : rv gappedElt j = 300000 := by
  unfold rv gappedElt
  rw [mkElt_coeff]
  have hv : (300000 : ZMod q).val = 300000 := ZMod.val_ofNat_of_lt (by rw [q_val]; norm_num)
  rw [hv]
  norm_num

/-- The honest commitment `w = A·y`: the constant gapped vector in `R_q^k`. -/
noncomputable def wVec : N := fun _ => gappedElt

theorem wVec_lowGap : realRoundingK.lowGap wVec := by
  intro i j
  have h : rv (wVec i) j = 300000 := gappedElt_rv j
  show 196 ≤ rv (wVec i) j ∧ rv (wVec i) j < 8380417 - 196 ∧
    196 ≤ (rv (wVec i) j + 261888) % 523776 ∧ (rv (wVec i) j + 261888) % 523776 < 523776 - 196
  rw [h]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **The hypotheses are SATISFIABLE — `lowGap` (the restrictive commitment bound) is inhabited over the
real `R_q^k`.** So `fips204_correct_real` is a genuine instantiation, not vacuously true. -/
theorem lowGap_inhabited : ∃ w : N, realRoundingK.lowGap w := ⟨wVec, wVec_lowGap⟩

/-- The honest linear map realizing `A·y = w` for the unit mask: `A m = (m 0) • wVec`. -/
noncomputable def honestA : M →ₗ[Rq] N := (LinearMap.proj (0 : Fin ell)).smulRight wVec

/-- The unit mask `y` (`y 0 = 1`, rest `0`): small (`‖y‖ ≤ 1`), and `A·y = wVec`. -/
noncomputable def unitMask : M := Function.update (0 : M) 0 1

theorem honestA_unitMask : honestA unitMask = wVec := by
  unfold honestA unitMask
  rw [LinearMap.smulRight_apply, LinearMap.proj_apply, Function.update_self, one_smul]

theorem rv_zero (j : Fin pb.dim) : rv (0 : Rq) j = 0 := by
  unfold rv; rw [map_zero]; simp

theorem rv_one_le (j : Fin pb.dim) : rv (1 : Rq) j ≤ 1 := by
  have h0 : pb.basis ⟨0, dim_pos⟩ = (1 : Rq) := by
    rw [pb.basis_eq_pow]; simp
  unfold rv
  rw [← h0, pb.basis.repr_self_apply]
  rcases eq_or_ne (⟨0, dim_pos⟩ : Fin pb.dim) j with hj | hj
  · rw [if_pos hj, ZMod.val_one]; norm_num
  · rw [if_neg hj, ZMod.val_zero]; norm_num

theorem unitMask_zBound : (realParamsK honestA).zBoundB (unitMask + (1 : Rq) • (0 : M)) = true := by
  simp only [realParamsK, smul_zero, add_zero]
  rw [decide_eq_true_eq]
  intro i j
  left
  unfold unitMask
  rcases eq_or_ne i 0 with hi | hi
  · subst hi; rw [Function.update_self]; exact lt_of_le_of_lt (rv_one_le j) (by norm_num)
  · rw [Function.update_of_ne hi]; simp only [Pi.zero_apply]; rw [rv_zero]; norm_num

/-- **A CONCRETE honest ML-DSA-65 signature VERIFIES, over the real `R_q^k`.** Unit mask, gapped
commitment `A·y = wVec`, zero secret (`s₁ = s₂ = t₀ = 0`, so `t = thi = 0`), challenge `c = 1`: ALL the
post-rejection bounds hold on genuine `R_q^k` data, and `fips204_correct_real` fires. The `RoundingScheme`
hypotheses are therefore non-vacuous at the real dimension. -/
theorem fips204_correct_real_accepts :
    (realParamsK honestA).verifyB 0 0 ((realParamsK honestA).sign 0 0 0 0 unitMask) = true := by
  refine fips204_correct_real honestA 0 0 0 0 0 unitMask 1 rfl ?_ ?_ ?_ ?_ ?_
  · -- hkey : A·0 + 0 = 0 + 0
    simp
  · -- nearGamma2 (-(1 • 0))
    intro i j; left
    simp only [smul_zero, neg_zero, Pi.zero_apply]; rw [rv_zero]; norm_num
  · -- betaSmall (-(1 • 0))
    intro i j; left
    simp only [smul_zero, neg_zero, Pi.zero_apply]; rw [rv_zero]; norm_num
  · -- lowGap (A·unitMask) = lowGap wVec
    show realRoundingK.lowGap (honestA unitMask)
    rw [honestA_unitMask]; exact wVec_lowGap
  · -- zBoundB (unitMask + 1 • 0)
    exact unitMask_zBound

#assert_axioms realDim
#assert_axioms root_pow_256
#assert_axioms rv_add
#assert_axioms realRoundingK
#assert_axioms fips204_correct_real
#assert_axioms lowGap_inhabited
#assert_axioms fips204_correct_real_accepts

end Dregg2.Crypto.Fips204CorrectReal
