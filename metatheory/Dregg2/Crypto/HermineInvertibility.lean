/-
# `Dregg2.Crypto.HermineInvertibility` — challenge-difference invertibility PROVEN in a concrete `R_q`.

`Dregg2.Crypto.HermineDischarge.lossiness_discharges_nonzero` consumes `hinv : IsUnit (c − c')` — the
"challenge-difference invertibility" parameter fact — as a bare hypothesis. This file PROVES it for a
concrete lattice ring: the smallest honest cyclotomic quotient `R_q = ℤ_q[X]/(X² + 1)` (n = 2), modeled
as pairs `(a, b)` over `ZMod q` with the Gaussian multiplication
`(a,b)·(c,d) = (ac − bd, ad + bc)` — i.e. `ℤ_q[i]`. The `CommRing` axioms are proved (not assumed),
componentwise via `ring` over `ZMod q`.

* **The number theory.** For prime `q ≡ 3 (mod 4)`, `−1` is a non-square mod `q`
  (`ZMod.exists_sq_eq_neg_one_iff`), so the Gaussian norm `N(a,b) = a² + b²` vanishes only at `0`;
  every nonzero element has the explicit inverse `(a·N⁻¹, −b·N⁻¹)`, and `R_q` is a FIELD
  (a `Field` instance is provided). Hence ALL distinct challenge pairs have invertible difference:
  `challenge_diff_isUnit : c ≠ c' → IsUnit (c − c')` — the honest general statement at n = 2.
* **The concrete witness (anti-vacuity).** At `q = 7` (`7 ≡ 3 mod 4`), the challenge pair
  `c = (3,5)`, `c' = (2,4)` has difference `δ = (1,1) ≠ 0` (decided), and the EXHIBITED inverse
  `δ⁻¹ = (4,3)` satisfies `δ · δ⁻¹ = 1` by `decide` on the actual numbers (`N(δ) = 2`, `2·4 = 8 ≡ 1`).
  `IsUnit δ` is built from that inverse, not conjured.
* **The payoff.** The `hinv` hypothesis of `lossiness_discharges_nonzero` is DISCHARGED: over this
  `R_q` the discharge fires from `c ≠ c'` alone (`all_distinct_challenge_pairs_discharge`), and the
  concrete `q = 7` instance runs end-to-end with a real `ShortNorm` (the centered-lift L1 norm,
  axioms decided over all 49/2401 cases).

Honesty note: the general `n ≥ 256` Dilithium/Raccoon lemma (Lyubashevsky–Seiler: LOW-NORM
differences are invertible in `ℤ_q[X]/(Xⁿ+1)` via the full `Xⁿ+1` factorization into low-degree
prime factors) is the larger effort; what is fully proven here is the n = 2 case, where irreducibility
of `X² + 1` makes `R_q` a field and EVERY nonzero difference invertible.
-/
import Dregg2.Crypto.HermineDischarge
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

namespace Dregg2.Crypto.HermineInvertibility

open Dregg2.Crypto.Lattice

/-! ## The ring: `R_q = ℤ_q[X]/(X²+1)` as Gaussian pairs over `ZMod q` -/

/-- `R_q = ℤ_q[X]/(X² + 1)` at n = 2, modeled concretely: `re + im·X` with `X² = −1`
(so multiplication is the Gaussian rule). Computable and decidable — everything below is
checked on real numbers, not postulated. -/
structure GaussMod (q : ℕ) where
  re : ZMod q
  im : ZMod q
  deriving DecidableEq

namespace GaussMod

variable {q : ℕ}

@[ext] theorem ext2 {a b : GaussMod q} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; cases hre; cases him; rfl

instance : Zero (GaussMod q) := ⟨⟨0, 0⟩⟩
instance : One (GaussMod q) := ⟨⟨1, 0⟩⟩
instance : Add (GaussMod q) := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Neg (GaussMod q) := ⟨fun a => ⟨-a.re, -a.im⟩⟩
/-- The Gaussian multiplication: `(a + bX)(c + dX) = (ac − bd) + (ad + bc)X` since `X² = −1`. -/
instance : Mul (GaussMod q) := ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩

@[simp] theorem zero_re : (0 : GaussMod q).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussMod q).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussMod q).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussMod q).im = 0 := rfl
@[simp] theorem add_re (a b : GaussMod q) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : GaussMod q) : (a + b).im = a.im + b.im := rfl
@[simp] theorem neg_re (a : GaussMod q) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : GaussMod q) : (-a).im = -a.im := rfl
@[simp] theorem mul_re (a b : GaussMod q) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : GaussMod q) : (a * b).im = a.re * b.im + a.im * b.re := rfl

/-- The `CommRing` axioms, PROVED componentwise over `ZMod q` (associativity/commutativity/
distributivity of the Gaussian multiplication are polynomial identities, closed by `ring`). -/
instance : CommRing (GaussMod q) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  mul := (· * ·)
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp

/-- The evident equivalence with pairs — used only to ENUMERATE `R_q` for the decided
`ShortNorm` axioms below (the ring structure is NOT the componentwise one). -/
def equivProd (q : ℕ) : GaussMod q ≃ ZMod q × ZMod q where
  toFun a := (a.re, a.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [NeZero q] : Fintype (GaussMod q) := Fintype.ofEquiv _ (equivProd q).symm

/-! ## The Gaussian norm, and invertibility for `q ≡ 3 (mod 4)` -/

/-- The Gaussian norm `N(a + bX) = a² + b²` — the determinant of multiplication-by-the-element,
landing in the base `ZMod q`. -/
def gnorm (a : GaussMod q) : ZMod q := a.re * a.re + a.im * a.im

/-- The explicit inverse candidate: `(a + bX)⁻¹ = (a·N⁻¹) − (b·N⁻¹)X` where `N = gnorm`. -/
def ginv (a : GaussMod q) : GaussMod q := ⟨a.re * (gnorm a)⁻¹, -(a.im * (gnorm a)⁻¹)⟩

/-- **The number-theoretic heart.** For prime `q ≡ 3 (mod 4)`, `−1` is a NON-square mod `q`,
so `a² + b² = 0` forces `a = b = 0`: the Gaussian norm is anisotropic. (Were `b ≠ 0` with
`a² + b² = 0`, then `(a·b⁻¹)² = −1`, contradicting `ZMod.exists_sq_eq_neg_one_iff`.) -/
theorem gnorm_eq_zero_iff [Fact q.Prime] (hq : q % 4 = 3) (a : GaussMod q) :
    gnorm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h₀ : a.re * a.re + a.im * a.im = 0 := h
    by_cases him : a.im = 0
    · refine ext2 ?_ him
      have hre : a.re * a.re = 0 := by rw [him] at h₀; simpa using h₀
      simpa using mul_self_eq_zero.mp hre
    · exfalso
      have h2 : a.re * a.re = -(a.im * a.im) := by linear_combination h₀
      have key : (a.re * a.im⁻¹) * (a.re * a.im⁻¹) = -1 := by
        calc (a.re * a.im⁻¹) * (a.re * a.im⁻¹)
            = (a.re * a.re) * (a.im⁻¹ * a.im⁻¹) := by ring
          _ = (-(a.im * a.im)) * (a.im⁻¹ * a.im⁻¹) := by rw [h2]
          _ = -((a.im * a.im⁻¹) * (a.im * a.im⁻¹)) := by ring
          _ = -1 := by rw [mul_inv_cancel₀ him]; ring
      exact absurd hq (ZMod.exists_sq_eq_neg_one_iff.mp ⟨a.re * a.im⁻¹, key.symm⟩)
  · rintro rfl
    simp [gnorm]

/-- **The inverse WORKS**: for nonzero `a`, the exhibited `ginv a` really is a right inverse —
`a · a⁻¹ = 1`, componentwise: the re-part collapses to `N · N⁻¹ = 1`, the im-part to `0`. -/
theorem mul_ginv_cancel [Fact q.Prime] (hq : q % 4 = 3) {a : GaussMod q} (ha : a ≠ 0) :
    a * ginv a = 1 := by
  have hN : gnorm a ≠ 0 := fun h => ha ((gnorm_eq_zero_iff hq a).mp h)
  have hNN : (a.re * a.re + a.im * a.im) * (gnorm a)⁻¹ = 1 := mul_inv_cancel₀ hN
  refine ext2 ?_ ?_
  · show a.re * (a.re * (gnorm a)⁻¹) - a.im * (-(a.im * (gnorm a)⁻¹)) = 1
    linear_combination hNN
  · show a.re * (-(a.im * (gnorm a)⁻¹)) + a.im * (a.re * (gnorm a)⁻¹) = 0
    ring

/-- **Every nonzero element is a unit** — with the inverse EXHIBITED (`ginv`), not classically
summoned. This is `X² + 1` irreducible for `q ≡ 3 (mod 4)` doing its work. -/
theorem isUnit_of_ne_zero [Fact q.Prime] (hq : q % 4 = 3) {δ : GaussMod q} (hδ : δ ≠ 0) :
    IsUnit δ :=
  ⟨⟨δ, ginv δ, mul_ginv_cancel hq hδ,
    by rw [mul_comm]; exact mul_ginv_cancel hq hδ⟩, rfl⟩

/-- **THE GENERAL STATEMENT (n = 2).** Over `R_q = ℤ_q[X]/(X²+1)` with prime `q ≡ 3 (mod 4)`,
ALL distinct challenge pairs have invertible difference. This is the parameter fact
`HermineDischarge` consumes, PROVEN — no longer a hypothesis, derived from `c ≠ c'` alone. -/
theorem challenge_diff_isUnit [Fact q.Prime] (hq : q % 4 = 3) {c c' : GaussMod q}
    (hcc : c ≠ c') : IsUnit (c - c') :=
  isUnit_of_ne_zero hq (sub_ne_zero.mpr hcc)

/-- `R_q` is a FIELD for prime `q ≡ 3 (mod 4)` — `X² + 1` is irreducible, so the quotient is
`𝔽_{q²}`. The inverse is the computable `ginv`. -/
instance instField [Fact q.Prime] [Fact (q % 4 = 3)] : Field (GaussMod q) where
  inv := ginv
  exists_pair_ne :=
    ⟨0, 1, fun h => zero_ne_one (α := ZMod q) (congrArg GaussMod.re h)⟩
  mul_inv_cancel a ha := mul_ginv_cancel Fact.out ha
  inv_zero := by
    refine ext2 ?_ ?_ <;> show _ = (0 : ZMod q) <;> simp [ginv]
  nnqsmul := _
  qsmul := _

end GaussMod

/-! ## The concrete witness: `q = 7`, δ = (1,1), δ⁻¹ = (4,3) — decided on the numbers -/

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

open GaussMod in
example : Fintype.card (GaussMod 7) = 49 := by simp [Fintype.ofEquiv_card]

/-- First fork challenge in `R_7`: `c = 3 + 5X`. -/
def cFirst : GaussMod 7 := ⟨3, 5⟩

/-- Second fork challenge: `c' = 2 + 4X` — distinct from `c`. -/
def cSecond : GaussMod 7 := ⟨2, 4⟩

/-- The challenge difference `δ = c − c' = 1 + X`, computed by the ring's own subtraction. -/
def δ : GaussMod 7 := ⟨1, 1⟩

/-- The EXHIBITED inverse: `N(δ) = 1² + 1² = 2`, `2⁻¹ = 4` in `ZMod 7` (`2·4 = 8 ≡ 1`),
so `δ⁻¹ = (1·4, −1·4) = (4, 3)`. -/
def δInv : GaussMod 7 := ⟨4, 3⟩

/-- The difference really is `δ` — decided on the numbers, through the ring's `Sub`. -/
theorem challenge_diff_eq : cFirst - cSecond = δ := by decide

/-- Anti-vacuity leg 1: `δ` is a REAL nonzero element (decided, not assumed). -/
theorem δ_ne_zero : δ ≠ 0 := by decide

/-- The challenges are genuinely distinct. -/
theorem challenges_distinct : cFirst ≠ cSecond := by decide

/-- Anti-vacuity leg 2: the exhibited inverse VERIFIES — `δ · δ⁻¹ = 1`, decided:
`(1·4 − 1·3, 1·3 + 1·4) = (1, 7) = (1, 0) = 1` in `ZMod 7`. -/
theorem δ_mul_δInv : δ * δInv = 1 := by decide

/-- And on the left. -/
theorem δInv_mul_δ : δInv * δ = 1 := by decide

/-- `IsUnit δ` — BUILT from the exhibited, verified inverse. -/
theorem δ_isUnit : IsUnit δ := ⟨⟨δ, δInv, δ_mul_δInv, δInv_mul_δ⟩, rfl⟩

/-- **The flagged parameter fact, PROVEN at the concrete instance**: the challenge difference
`c − c'` is a unit of `R_7`. -/
theorem concrete_challenge_diff_isUnit : IsUnit (cFirst - cSecond) :=
  challenge_diff_eq ▸ δ_isUnit

/-- Cross-check: the same fact falls out of the GENERAL n = 2 theorem (`7 ≡ 3 mod 4`),
from distinctness alone. -/
theorem concrete_challenge_diff_isUnit' : IsUnit (cFirst - cSecond) :=
  GaussMod.challenge_diff_isUnit (by norm_num) challenges_distinct

/-! ## Feeding the discharge: `hinv` is no longer a hypothesis -/

/-- A real `ShortNorm` on `R_7`: the centered-lift L1 norm `|â| + |b̂|` where `x̂` is the
representative of minimal absolute value (`min val (7 − val)`). Zero, negation-invariance, and
the triangle inequality are DECIDED over all 49 (resp. 2401) cases. -/
instance : ShortNorm (GaussMod 7) where
  nrm a := min a.re.val (7 - a.re.val) + min a.im.val (7 - a.im.val)
  nrm_zero := by decide
  nrm_neg := by decide
  nrm_add_le := by decide

/-- **The discharge fires with NO invertibility hypothesis** at the concrete challenges: for any
lossy secret pair `s ≠ s'` and any forked responses, at least one extracted candidate is nonzero —
`hinv` supplied by `concrete_challenge_diff_isUnit`, which this file PROVED. -/
theorem concrete_discharge_fires (s s' z z' : GaussMod 7) (hss : s ≠ s') :
    (z - z') - (cFirst - cSecond) • s ≠ 0 ∨ (z - z') - (cFirst - cSecond) • s' ≠ 0 :=
  Dregg2.Crypto.HermineDischarge.lossiness_discharges_nonzero s s' cFirst cSecond z z' hss
    concrete_challenge_diff_isUnit

/-- **The general payoff (n = 2, any prime `q ≡ 3 mod 4`, any `R_q`-module):** the discharge
lemma's `hinv` is REPLACED by mere challenge distinctness — `lossiness_discharges_nonzero` fires
from `s ≠ s'` and `c ≠ c'` alone, invertibility derived. -/
theorem all_distinct_challenge_pairs_discharge {q : ℕ} [Fact q.Prime] (hq : q % 4 = 3)
    {M : Type*} [AddCommGroup M] [Module (GaussMod q) M] [ShortNorm M]
    (s s' : M) (c c' : GaussMod q) (z z' : M) (hss : s ≠ s') (hcc : c ≠ c') :
    (z - z') - (c - c') • s ≠ 0 ∨ (z - z') - (c - c') • s' ≠ 0 :=
  Dregg2.Crypto.HermineDischarge.lossiness_discharges_nonzero s s' c c' z z' hss
    (GaussMod.challenge_diff_isUnit hq hcc)

#assert_axioms GaussMod.gnorm_eq_zero_iff
#assert_axioms GaussMod.mul_ginv_cancel
#assert_axioms GaussMod.isUnit_of_ne_zero
#assert_axioms GaussMod.challenge_diff_isUnit
#assert_axioms challenge_diff_eq
#assert_axioms δ_ne_zero
#assert_axioms challenges_distinct
#assert_axioms δ_mul_δInv
#assert_axioms δInv_mul_δ
#assert_axioms δ_isUnit
#assert_axioms concrete_challenge_diff_isUnit
#assert_axioms concrete_challenge_diff_isUnit'
#assert_axioms concrete_discharge_fires
#assert_axioms all_distinct_challenge_pairs_discharge

end Dregg2.Crypto.HermineInvertibility
