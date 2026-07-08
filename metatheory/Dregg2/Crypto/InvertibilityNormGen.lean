/-
# `Dregg2.Crypto.InvertibilityNormGen` — challenge-difference invertibility BEYOND the n=4/q=5 point.

(Header finalized at the end of the file's construction; see the bottom `#assert_axioms` block for
the certified inventory.)
-/
import Dregg2.Crypto.InvertibilityNorm
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Nat.Factorization.Defs

namespace Dregg2.Crypto.InvertibilityNormGen

open Dregg2.Crypto.InvertibilityNorm
open Quart (caval normInf)

/-! ## 0. Infrastructure: the ∞-norm on the pair model, and the centered integer lift -/

/-- The coefficient ∞-norm on `Quad q r` (the pair model of `ℤ_q[X]/(X² − r)`). -/
def normInf2 {q : ℕ} {r : ZMod q} (f : Quad q r) : ℕ := max (caval f.re) (caval f.im)

/-- `caval` (the parent file's centered absolute value) IS the absolute value of Mathlib's
minimal-absolute-value integer lift `ZMod.valMinAbs`. This is the bridge from the decided norm
to the integer geometry that powers the parametric bound. -/
theorem caval_eq_natAbs_valMinAbs {q : ℕ} [NeZero q] (x : ZMod q) :
    caval x = x.valMinAbs.natAbs := by
  have hlt : x.val < q := ZMod.val_lt x
  rw [ZMod.valMinAbs_def_pos]
  simp only [Quart.caval]
  split_ifs with h <;> omega

theorem abs_valMinAbs_le_of_caval_le {q : ℕ} [NeZero q] {x : ZMod q} {B : ℕ}
    (h : caval x ≤ B) : |x.valMinAbs| ≤ (B : ℤ) := by
  rw [Int.abs_eq_natAbs, ← caval_eq_natAbs_valMinAbs]
  exact_mod_cast h

/-- The integer-lift workhorse: an integer that vanishes mod `q` and sits in `[0, q)` is zero. -/
theorem int_eq_zero_of_zmod_zero_of_lt {q : ℕ} {N : ℤ}
    (hcast : (N : ZMod q) = 0) (h0 : 0 ≤ N) (hlt : N < (q : ℤ)) : N = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd N q).mp hcast)
    (by rwa [abs_of_nonneg h0])

/-- `2` is nonzero mod an odd prime. -/
theorem two_ne_zero_zmod {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h0
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp (by exact_mod_cast h0)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact (Fact.out : q.Prime).ne_one h
  · exact hq h

/-- Enumeration equivalence for the pair model (only to make small concrete `∀` facts decidable). -/
def quadEquivProd (q : ℕ) (r : ZMod q) : Quad q r ≃ ZMod q × ZMod q where
  toFun f := (f.re, f.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {q : ℕ} [NeZero q] {r : ZMod q} : Fintype (Quad q r) :=
  Fintype.ofEquiv _ (quadEquivProd q r).symm

/-! ## 1. The INERT case, parametric: n = 2, ALL primes q ≡ 3 (mod 4)

`HermineInvertibility` proved this for a single fixed `q`. Here it is for the whole residue
class at once: `X² + 1` is irreducible mod every prime `q ≡ 3 (mod 4)` (because `−1` is a
non-square), so `ℤ_q[X]/(X²+1) = 𝔽_{q²}` and EVERY nonzero challenge difference is a unit —
no norm hypothesis whatsoever. -/

section Inert

variable {q : ℕ} [Fact q.Prime]

/-- For prime `q ≡ 3 (mod 4)`, `−1` is a non-square mod `q`. -/
theorem neg_one_nonsquare (hq : q % 4 = 3) : ∀ x : ZMod q, x * x ≠ -1 := fun x hx =>
  (ZMod.exists_sq_eq_neg_one_iff.mp ⟨x, hx.symm⟩) hq

/-- **n = 2, all primes q ≡ 3 (mod 4)**: every nonzero element of `ℤ_q[X]/(X²+1)` is a unit,
with the inverse EXHIBITED by the parent file's anisotropic-norm construction. -/
theorem isUnit_of_ne_zero_inert (hq : q % 4 = 3) {f : Quad q (-1)} (hf : f ≠ 0) : IsUnit f :=
  Quad.isUnit_of_ne_zero (neg_one_nonsquare hq) hf

/-- The challenge-difference form of the inert case: distinct challenges always invert. -/
theorem challenge_diff_isUnit_inert (hq : q % 4 = 3) {c c' : Quad q (-1)} (hcc : c ≠ c') :
    IsUnit (c - c') :=
  isUnit_of_ne_zero_inert hq (sub_ne_zero.mpr hcc)

end Inert

/-! ### Non-vacuity of the inert case: q = 11 concrete, inverse exhibited; teeth at q = 13 -/

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- First fork challenge over `q = 11` (a fresh prime `≡ 3 mod 4`, beyond Hermine's fixed one). -/
def c11 : Quad 11 (-1) := ⟨1, 1⟩

def c11' : Quad 11 (-1) := ⟨0, 2⟩

theorem c11_distinct : c11 ≠ c11' := by decide

theorem c11_diff_isUnit : IsUnit (c11 - c11') :=
  challenge_diff_isUnit_inert (by norm_num) c11_distinct

/-- The difference is `1 − X` and its inverse is `6 + 6X`: `(1−X)(6+6X) = 6 − 6X² = 12 = 1`. -/
theorem c11_diff_eq : c11 - c11' = (⟨1, 10⟩ : Quad 11 (-1)) := by decide

theorem c11_inv_verifies : (⟨1, 10⟩ : Quad 11 (-1)) * ⟨6, 6⟩ = 1 := by decide

/-- TEETH: the inert hypothesis is load-bearing. At `q = 13 ≡ 1 (mod 4)` the ring is NOT a
field — `(8 + X)(5 + X) = 40 − 1 + 13X = 0`, a genuine zero-divisor pair. -/
theorem quad13_zero_divisor : (⟨8, 1⟩ : Quad 13 (-1)) * ⟨5, 1⟩ = 0 := by decide

theorem quad13_nonzero_nonunit : ¬ IsUnit ((⟨8, 1⟩ : Quad 13 (-1))) := by
  intro h
  have h5 : (⟨5, 1⟩ : Quad 13 (-1)) = 0 :=
    h.mul_left_cancel (by rw [quad13_zero_divisor, mul_zero])
  exact absurd h5 (by decide)

/-! ## 2. The SPLIT case: linear factors `X ∓ r` of `X² + 1` (q ≡ 1 mod 4), and
     THE PARAMETRIC MIN-NORM BOUND — the Lyubashevsky–Seiler threshold shape, all q at once -/

section Split

variable {q : ℕ}

/-- Evaluation at a root `a` of `X² + 1`: the factor map
`ℤ_q[X]/(X²+1) → ℤ_q[X]/(X − a) = ℤ_q` (well-defined when `a² = −1`). -/
def toLin (a : ZMod q) (f : Quad q (-1)) : ZMod q := f.re + a * f.im

@[simp] theorem toLin_def (a : ZMod q) (f : Quad q (-1)) : toLin a f = f.re + a * f.im := rfl

theorem toLin_mul {a : ZMod q} (ha : a * a = -1) (f g : Quad q (-1)) :
    toLin a (f * g) = toLin a f * toLin a g := by
  simp only [toLin, Quad.mul_re, Quad.mul_im]
  linear_combination (-(f.im * g.im)) * ha

/-- The factor map as a ring hom. -/
def toLinHom {a : ZMod q} (ha : a * a = -1) : Quad q (-1) →+* ZMod q where
  toFun := toLin a
  map_one' := by simp [toLin]
  map_mul' := toLin_mul ha
  map_zero' := by simp [toLin]
  map_add' f g := by simp only [toLin, Quad.add_re, Quad.add_im]; ring

@[simp] theorem toLinHom_apply {a : ZMod q} (ha : a * a = -1) (f : Quad q (-1)) :
    toLinHom ha f = toLin a f := rfl

/-- The heart of the d = 1 bound: an element of the kernel of the factor map has
`re² + im² = 0` — the Gaussian-integer norm form vanishes mod `q`. -/
theorem sq_add_sq_eq_zero_of_ker {r : ZMod q} (hr : r * r = -1) {f : Quad q (-1)}
    (hker : toLin r f = 0) : f.re ^ 2 + f.im ^ 2 = 0 := by
  simp only [toLin] at hker
  linear_combination (f.re - r * f.im) * hker + f.im ^ 2 * hr

/-- **THE PARAMETRIC MIN-NORM LEMMA (n = 2, d = 1) — the Lyubashevsky–Seiler bound, all q.**
For ANY modulus `q` and any root `r` of `X² + 1` mod `q`, every nonzero multiple of the linear
factor `X − r` in `ℤ_q[X]/(X²+1)` has coefficient ∞-norm `> B` whenever `2·B² < q` — i.e. the
ideal's min-norm is `> √(q/2)`, the true `q^(d/n)`-shape threshold (LS Corollary 1.2 at
`n = 2, d = 1`, constant `1/√2`). Proof: lift the two coefficients to their centered integer
representatives; the kernel condition forces the Gaussian norm `â² + b̂²` to vanish mod `q`,
but `0 ≤ â² + b̂² ≤ 2B² < q` pins it to zero, and the form is anisotropic over ℤ.
NOT a `decide` — one proof for the whole infinite family, no primality needed. -/
theorem minNorm_linear_factor [NeZero q] {r : ZMod q} (hr : r * r = -1) {B : ℕ}
    (hB : 2 * B ^ 2 < q) :
    ∀ f : Quad q (-1), toLin r f = 0 → f ≠ 0 → B + 1 ≤ normInf2 f := by
  intro f hker hf
  by_contra hlt
  rw [not_le, Nat.lt_succ_iff] at hlt
  have hre : caval f.re ≤ B := le_trans (le_max_left _ _) hlt
  have him : caval f.im ≤ B := le_trans (le_max_right _ _) hlt
  have haB := abs_le.mp (abs_valMinAbs_le_of_caval_le hre)
  have hbB := abs_le.mp (abs_valMinAbs_le_of_caval_le him)
  have hcast : ((f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 : ℤ) : ZMod q) = 0 := by
    push_cast [ZMod.coe_valMinAbs]
    exact sq_add_sq_eq_zero_of_ker hr hker
  have h0 : (0 : ℤ) ≤ f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 := by positivity
  have hlt2 : f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 < (q : ℤ) := by
    have hq : ((2 * B ^ 2 : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hB
    have h1 : f.re.valMinAbs ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq' haB.1 haB.2
    have h2 : f.im.valMinAbs ^ 2 ≤ (B : ℤ) ^ 2 := sq_le_sq' hbB.1 hbB.2
    push_cast at hq
    linarith
  have hzero : f.re.valMinAbs ^ 2 + f.im.valMinAbs ^ 2 = 0 :=
    int_eq_zero_of_zmod_zero_of_lt hcast h0 hlt2
  have ha0 : f.re.valMinAbs = 0 := by
    have h : f.re.valMinAbs ^ 2 = 0 := by nlinarith [sq_nonneg f.im.valMinAbs]
    exact sq_eq_zero_iff.mp h
  have hb0 : f.im.valMinAbs = 0 := by
    have h : f.im.valMinAbs ^ 2 = 0 := by nlinarith [sq_nonneg f.re.valMinAbs]
    exact sq_eq_zero_iff.mp h
  apply hf
  refine Quad.ext2 ?_ ?_
  · have h := ZMod.coe_valMinAbs f.re
    rw [ha0] at h
    simpa using h.symm
  · have h := ZMod.coe_valMinAbs f.im
    rw [hb0] at h
    simpa using h.symm

/-- The CRT ring isomorphism for the LINEAR splitting `X² + 1 = (X − r)(X + r)`, CONSTRUCTED
for any `q, r` with `r² = −1` and `2` invertible: `ℤ_q[X]/(X²+1) ≃+* ℤ_q × ℤ_q`. This is the
`q ≡ 1 (mod 8 or 4)` factor structure — LINEAR residue fields, complementing the parent file's
quadratic-factor `crtEquiv`. Both directions and both hom laws proved algebraically. -/
def crtLin {r half : ZMod q} (hr : r * r = -1) (h2 : 2 * half = 1) :
    Quad q (-1) ≃+* ZMod q × ZMod q where
  toFun f := (toLin r f, toLin (-r) f)
  invFun p := ⟨(p.1 + p.2) * half, (p.1 - p.2) * half * (-r)⟩
  left_inv f := by
    refine Quad.ext2 ?_ ?_ <;> simp only [toLin]
    · linear_combination f.re * h2
    · linear_combination (-(2 * f.im * half)) * hr + f.im * h2
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> simp only [toLin]
    · linear_combination (-((p.1 - p.2) * half)) * hr + p.1 * h2
    · linear_combination ((p.1 - p.2) * half) * hr + p.2 * h2
  map_mul' f g := Prod.ext (toLin_mul hr f g) (toLin_mul (by linear_combination hr) f g)
  map_add' f g := by
    refine Prod.ext ?_ ?_ <;>
      simp only [toLin, Quad.add_re, Quad.add_im, Prod.fst_add, Prod.snd_add] <;> ring

@[simp] theorem crtLin_apply {r half : ZMod q} (hr : r * r = -1) (h2 : 2 * half = 1)
    (f : Quad q (-1)) : crtLin hr h2 f = (toLin r f, toLin (-r) f) := rfl

/-- **The split-case unit theorem, parametric**: prime `q`, `r² = −1`, `2` invertible — every
nonzero `f` with `2·‖f‖∞² < q` is a unit. Min-norm bound at BOTH linear factors, chained
through the constructed CRT. -/
theorem low_norm_isUnit_split [Fact q.Prime] {r half : ZMod q} (hr : r * r = -1)
    (h2 : 2 * half = 1) {f : Quad q (-1)} (hf : f ≠ 0)
    (hν : 2 * normInf2 f ^ 2 < q) : IsUnit f := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hr' : (-r) * (-r) = -1 := by linear_combination hr
  have h₁ : toLin r f ≠ 0 :=
    factor_nonzero_of_norm_lt (toLin r) normInf2 (normInf2 f + 1)
      (minNorm_linear_factor hr hν) hf (Nat.lt_succ_self _)
  have h₂ : toLin (-r) f ≠ 0 :=
    factor_nonzero_of_norm_lt (toLin (-r)) normInf2 (normInf2 f + 1)
      (minNorm_linear_factor hr' hν) hf (Nat.lt_succ_self _)
  refine isUnit_of_map_isUnit (crtLin hr h2) ?_
  rw [crtLin_apply]
  exact Prod.isUnit_iff.mpr ⟨h₁.isUnit, h₂.isUnit⟩

/-- The split case packaged over the residue class: for every prime `q ≡ 1 (mod 4)`, every
nonzero `f ∈ ℤ_q[X]/(X²+1)` with `2·‖f‖∞² < q` is a unit — the root `r` of `−1` and the
half `2⁻¹` are OBTAINED, not assumed. -/
theorem low_norm_isUnit_mod_four_eq_one [Fact q.Prime] (hq : q % 4 = 1)
    {f : Quad q (-1)} (hf : f ≠ 0) (hν : 2 * normInf2 f ^ 2 < q) : IsUnit f := by
  obtain ⟨r, hr⟩ : IsSquare (-1 : ZMod q) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  have hq2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod (by omega)
  exact low_norm_isUnit_split hr.symm (mul_inv_cancel₀ hq2) hf hν

end Split

/-! ## 3. THE HEADLINE: n = 2 challenge-difference invertibility for EVERY odd prime q -/

/-- **THE GENERAL n = 2 LYUBASHEVSKY–SEILER THEOREM, ALL ODD PRIMES.** In
`R_q = ℤ_q[X]/(X²+1)` for ANY odd prime `q`: distinct challenges whose difference has
coefficient ∞-norm below the `√(q/2)` threshold (`2·‖c−c'‖∞² < q`) have INVERTIBLE difference.
`q ≡ 3 (mod 4)`: inert, no norm needed; `q ≡ 1 (mod 4)`: split, the parametric min-norm bound
at both linear CRT factors. One theorem, the whole infinite family, the true `q^(d/n)` = `√q`
threshold shape — not a per-`q` decision. -/
theorem challenge_diff_isUnit_all_odd_primes {q : ℕ} [Fact q.Prime] (hodd : q % 2 = 1)
    {c c' : Quad q (-1)} (hcc : c ≠ c') (hν : 2 * normInf2 (c - c') ^ 2 < q) :
    IsUnit (c - c') := by
  have h4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases h4 with h | h
  · exact low_norm_isUnit_mod_four_eq_one h (sub_ne_zero.mpr hcc) hν
  · exact challenge_diff_isUnit_inert h hcc

/-! ### Non-vacuity + sharpness of the split case, at q = 13 (and scaling demo at q = 101) -/

theorem five_sq_13 : (5 : ZMod 13) * 5 = -1 := by decide

set_option maxRecDepth 40000 in
/-- Cross-validation, decided route: the min-norm of the ideal `(X − 5)` in `ℤ₁₃[X]/(X²+1)` is
≥ 3, checked over all 169 elements. -/
theorem minNorm13_decided : ∀ f : Quad 13 (-1), toLin 5 f = 0 → f ≠ 0 → 3 ≤ normInf2 f := by
  decide

/-- Cross-validation, parametric route: the SAME statement falls out of `minNorm_linear_factor`
at `B = 2` (`2·2² = 8 < 13`) — the general theorem and the finite decision agree. -/
theorem minNorm13_parametric : ∀ f : Quad 13 (-1), toLin 5 f = 0 → f ≠ 0 → 3 ≤ normInf2 f :=
  minNorm_linear_factor five_sq_13 (by norm_num)

/-- Concrete challenge pair at `q = 13` with difference `1 − X` (∞-norm 1, threshold `2 < 13`). -/
def c13 : Quad 13 (-1) := ⟨1, 0⟩

def c13' : Quad 13 (-1) := ⟨0, 1⟩

theorem c13_distinct : c13 ≠ c13' := by decide

/-- The headline theorem fires on a real element at a split prime. -/
theorem c13_diff_isUnit : IsUnit (c13 - c13') :=
  challenge_diff_isUnit_all_odd_primes (by norm_num) c13_distinct (by decide)

/-- Same fact by exhibited inverse: `(1 − X)(7 + 7X) = 7 − 7X² = 14 = 1`. Two routes agree. -/
theorem c13_diff_eq : c13 - c13' = (⟨1, 12⟩ : Quad 13 (-1)) := by decide

theorem c13_inv_verifies : (⟨1, 12⟩ : Quad 13 (-1)) * ⟨7, 7⟩ = 1 := by decide

/-- **SHARPNESS of the parametric threshold at q = 13**: `3 + 2X` is nonzero, has ∞-norm
exactly 3 — just past the `2·B² < 13 ⇒ B ≤ 2` threshold — and is NOT a unit (it is a multiple
of `X − 5`, vanishing in that CRT factor). The `√(q/2)` shape cannot be relaxed. -/
def sharp13 : Quad 13 (-1) := ⟨3, 2⟩

theorem sharp13_ne_zero : sharp13 ≠ 0 := by decide

theorem sharp13_norm : normInf2 sharp13 = 3 := by decide

theorem sharp13_ker : toLin 5 sharp13 = 0 := by decide

theorem sharp13_not_unit : ¬ IsUnit sharp13 := by
  intro h
  have hu := h.map (toLinHom five_sq_13)
  rw [toLinHom_apply, sharp13_ker] at hu
  exact absurd (isUnit_zero_iff.mp hu) (by decide)

theorem norm_threshold_sharp_13 :
    ∃ f : Quad 13 (-1), f ≠ 0 ∧ normInf2 f = 3 ∧ ¬ 2 * normInf2 f ^ 2 < 13 ∧ ¬ IsUnit f :=
  ⟨sharp13, sharp13_ne_zero, sharp13_norm, by decide, sharp13_not_unit⟩

/-- Teeth at the parent file's `q = 5`: `3 + X` is a nonzero NON-unit of norm 2 — and the
parametric threshold correctly does NOT cover it (`2·2² = 8 ≥ 5`). The bound is honest at
small `q` too. -/
theorem q5_nonunit_outside_threshold :
    ¬ (2 * normInf2 ((⟨3, 1⟩ : Quad 5 (-1))) ^ 2 < 5) := by decide

theorem q5_ker : toLin 2 (⟨3, 1⟩ : Quad 5 (-1)) = 0 := by decide

theorem q5_not_unit : ¬ IsUnit ((⟨3, 1⟩ : Quad 5 (-1))) := by
  intro h
  have hu := h.map (toLinHom two_sq)
  rw [toLinHom_apply, q5_ker] at hu
  exact absurd (isUnit_zero_iff.mp hu) (by decide)

/-- Scaling demo at `q = 101` (split, `10² = −1`): a norm-7 element is certified a unit by the
PARAMETRIC theorem (`2·7² = 98 < 101`) — no 101²-element enumeration anywhere in the proof. -/
instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

theorem w101_isUnit : IsUnit ((⟨7, 6⟩ : Quad 101 (-1))) :=
  low_norm_isUnit_mod_four_eq_one (by norm_num) (by decide) (by decide)

#assert_axioms caval_eq_natAbs_valMinAbs
#assert_axioms int_eq_zero_of_zmod_zero_of_lt
#assert_axioms neg_one_nonsquare
#assert_axioms isUnit_of_ne_zero_inert
#assert_axioms challenge_diff_isUnit_inert
#assert_axioms c11_diff_isUnit
#assert_axioms c11_inv_verifies
#assert_axioms quad13_zero_divisor
#assert_axioms quad13_nonzero_nonunit
#assert_axioms toLin_mul
#assert_axioms sq_add_sq_eq_zero_of_ker
#assert_axioms minNorm_linear_factor
#assert_axioms crtLin
#assert_axioms low_norm_isUnit_split
#assert_axioms low_norm_isUnit_mod_four_eq_one
#assert_axioms challenge_diff_isUnit_all_odd_primes
#assert_axioms minNorm13_decided
#assert_axioms minNorm13_parametric
#assert_axioms c13_diff_isUnit
#assert_axioms c13_inv_verifies
#assert_axioms sharp13_not_unit
#assert_axioms norm_threshold_sharp_13
#assert_axioms q5_not_unit
#assert_axioms w101_isUnit

end Dregg2.Crypto.InvertibilityNormGen
