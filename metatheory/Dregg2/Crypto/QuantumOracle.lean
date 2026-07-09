/-
# `Dregg2.Crypto.QuantumOracle` — a real quantum-adversary / QROM model in Lean, from Mathlib linear algebra.

No quantum-specific infrastructure: everything is grounded in Mathlib's finite-dimensional inner-product
spaces (`EuclideanSpace ℂ B = PiLp 2 (fun _ : B => ℂ)`), norm-preserving `LinearIsometryEquiv`s, and
`Finset` sums. "we don't need to be afraid that mathlib lacks. we can provide."

## The model

* **`QState B`** — a quantum state over a finite basis `B` is a vector of `EuclideanSpace ℂ B`. A *state* in
  the physical sense is a unit vector (`IsUnitVector`, `‖ψ‖ = 1`); the operators below are defined on the
  whole space and restrict to unit vectors because they are isometries.
* **`Unitary B`** — a unitary is a `QState B ≃ₗᵢ[ℂ] QState B` (a Mathlib `LinearIsometryEquiv`): a linear,
  norm-preserving bijection. `unitary_preserves_unit`: it maps unit vectors to unit vectors.
* **The random-oracle unitary `oracleUnitary H`** for `H : X → Y` (`Y` a finite additive group) is the
  BASIS PERMUTATION `|x, y⟩ ↦ |x, y + H x⟩` on `QState (X × Y)`. It is genuinely a permutation of the
  orthonormal basis (`oraclePerm H : (X × Y) ≃ (X × Y)`), hence a `LinearIsometryEquiv` by Mathlib's
  `LinearIsometryEquiv.piLpCongrLeft` (permuting an orthonormal basis is an isometry — proved by Mathlib,
  used here). `oracleUnitary_single` is the basis action; `oracleUnitary_apply` the coordinate action
  `(O_H v)(x,y) = v(x, y − H x)`; `oracleUnitary_norm` the isometry.
* **`projSet S`** — the projection onto basis states with `x ∈ S`: `(P_S v)(x,y) = if x ∈ S then v(x,y)
  else 0`. A genuine idempotent (`projSet_idempotent`) with `‖P_S v‖ ≤ ‖v‖` (`projSet_norm_le`).
* **`OracleDiffData`** — the interface the O2H lemma rides: two oracle unitaries `O, O'`, a projection `P`,
  the FACTORIZATION `(O − O') = (O − O') ∘ P` and the projection norm bound. `oracleDiff` BUILDS it from two
  oracles `H, H'` agreeing off a reprogramming set `S`: the factorization is proved from the coordinate
  action (`O_H` and `O_{H'}` agree on basis states with `x ∉ S`).

The reprogrammed oracle `H'` differs from `H` only on `S ⊆ X`; `projSet S` is the amplitude the adversary
places on the reprogrammed region. This is the whole foundation the FO-QROM bookkeeping (ML-KEM IND-CCA)
rides on. The One-Way-to-Hiding lemma itself is proved in `Dregg2.Crypto.OneWayToHiding`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Dregg2.Tactics

open scoped BigOperators

namespace Dregg2.Crypto.QuantumOracle

/-! ## Quantum states and unitaries over a finite basis. -/

/-- A **quantum state** over a finite basis `B`: a vector of the finite-dimensional complex inner-product
space `EuclideanSpace ℂ B = PiLp 2 (fun _ : B => ℂ)`. Physical states are the unit vectors below. -/
abbrev QState (B : Type*) [Fintype B] := EuclideanSpace ℂ B

/-- A **unit vector** — a bona fide quantum state (`‖ψ‖ = 1`). -/
def IsUnitVector {B : Type*} [Fintype B] (ψ : QState B) : Prop := ‖ψ‖ = 1

/-- A **unitary** on `QState B`: a linear, norm-preserving (hence inner-product-preserving) bijection —
exactly Mathlib's `LinearIsometryEquiv`. -/
abbrev Unitary (B : Type*) [Fintype B] := QState B ≃ₗᵢ[ℂ] QState B

/-- **A unitary preserves unit vectors** (maps states to states): `‖U ψ‖ = ‖ψ‖ = 1`. This is the sense in
which a `LinearIsometryEquiv` is a legitimate quantum evolution. -/
theorem unitary_preserves_unit {B : Type*} [Fintype B] (U : Unitary B) {ψ : QState B}
    (h : IsUnitVector ψ) : IsUnitVector (U ψ) := by
  unfold IsUnitVector at *; rw [U.norm_map]; exact h

/-- **Composition of unitaries is a unitary** — the `LinearIsometryEquiv.trans` of Mathlib (here spelled as
`U₂` after `U₁`). Included to witness that the model is closed under composition (the adversary interleaves
these with the oracle). -/
noncomputable def Unitary.after {B : Type*} [Fintype B] (U₂ U₁ : Unitary B) : Unitary B := U₁.trans U₂

@[simp] theorem Unitary.after_apply {B : Type*} [Fintype B] (U₂ U₁ : Unitary B) (ψ : QState B) :
    U₂.after U₁ ψ = U₂ (U₁ ψ) := rfl

/-! ## The random-oracle unitary `|x,y⟩ ↦ |x, y + H x⟩`. -/

section Oracle

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **The oracle basis permutation** `(x, y) ↦ (x, y + H x)`: a genuine bijection of the finite index set
`X × Y` (its inverse subtracts `H x`). Permuting an orthonormal basis is what makes the oracle unitary. -/
def oraclePerm (H : X → Y) : (X × Y) ≃ (X × Y) where
  toFun p := (p.1, p.2 + H p.1)
  invFun p := (p.1, p.2 - H p.1)
  left_inv := by rintro ⟨x, y⟩; simp
  right_inv := by rintro ⟨x, y⟩; simp

@[simp] theorem oraclePerm_apply (H : X → Y) (x : X) (y : Y) :
    oraclePerm H (x, y) = (x, y + H x) := rfl

@[simp] theorem oraclePerm_symm_apply (H : X → Y) (x : X) (y : Y) :
    (oraclePerm H).symm (x, y) = (x, y - H x) := rfl

/-- **The random-oracle unitary** `O_H` on `QState (X × Y)`: the basis permutation `oraclePerm H` lifted to
the state space by Mathlib's `LinearIsometryEquiv.piLpCongrLeft`. This IS a unitary by construction — a
permutation of the orthonormal basis is norm-preserving (Mathlib proves the `norm_map'` obligation). -/
noncomputable def oracleUnitary (H : X → Y) : Unitary (X × Y) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (oraclePerm H)

/-- **The basis action**: `O_H |x, y⟩ = |x, y + H x⟩` (the defining QROM action, on the orthonormal basis
vectors `EuclideanSpace.single`). -/
@[simp] theorem oracleUnitary_single (H : X → Y) (x : X) (y : Y) (a : ℂ) :
    oracleUnitary H (EuclideanSpace.single (x, y) a) = EuclideanSpace.single (x, y + H x) a := by
  simp only [oracleUnitary, LinearIsometryEquiv.piLpCongrLeft_single, oraclePerm_apply]

/-- **The coordinate action**: `(O_H v)(x, y) = v(x, y − H x)` (the amplitude at `(x, y)` is pulled back
through the permutation). This is the workhorse for the O2H oracle-difference computation. -/
theorem oracleUnitary_apply (H : X → Y) (v : QState (X × Y)) (x : X) (y : Y) :
    oracleUnitary H v (x, y) = v (x, y - H x) := by
  simp only [oracleUnitary, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  rfl

/-- **The oracle is an isometry** (norm-preserving): `‖O_H v‖ = ‖v‖`. This is `LinearIsometryEquiv.norm_map`
— the unitarity of `O_H`, ready for the O2H telescoping. -/
@[simp] theorem oracleUnitary_norm (H : X → Y) (v : QState (X × Y)) :
    ‖oracleUnitary H v‖ = ‖v‖ :=
  (oracleUnitary H).norm_map v

/-- **The oracle maps states to states** (preserves unit vectors) — it is a bona fide quantum unitary. -/
theorem oracleUnitary_preserves_unit (H : X → Y) {ψ : QState (X × Y)} (h : IsUnitVector ψ) :
    IsUnitVector (oracleUnitary H ψ) :=
  unitary_preserves_unit (oracleUnitary H) h

end Oracle

/-! ## The projection `P_S` onto basis states with `x ∈ S`. -/

section Projection

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **`projSet S`** — the projection onto basis states whose `X`-coordinate lies in `S`:
`(P_S v)(x, y) = if x ∈ S then v(x, y) else 0`. A genuine (idempotent) linear projection; `P_S v` is the
component of `v` supported on the reprogramming region. -/
noncomputable def projSet (S : Finset X) : QState (X × Y) →ₗ[ℂ] QState (X × Y) where
  toFun v := WithLp.toLp 2 (fun p => if p.1 ∈ S then WithLp.ofLp v p else 0)
  map_add' u v := by ext p; by_cases h : p.1 ∈ S <;> simp [h]
  map_smul' c v := by ext p; by_cases h : p.1 ∈ S <;> simp [h]

@[simp] theorem projSet_apply (S : Finset X) (v : QState (X × Y)) (p : X × Y) :
    projSet S v p = if p.1 ∈ S then v p else 0 := rfl

/-- **`P_S` is a projection** (idempotent): `P_S (P_S v) = P_S v`. -/
theorem projSet_idempotent (S : Finset X) (v : QState (X × Y)) :
    projSet S (projSet S v) = projSet S v := by
  ext p; simp only [projSet_apply]; by_cases h : p.1 ∈ S <;> simp [h]

/-- **`P_S` is norm-nonincreasing**: `‖P_S v‖ ≤ ‖v‖` (it deletes coordinates, never adds amplitude). -/
theorem projSet_norm_le (S : Finset X) (v : QState (X × Y)) : ‖projSet S v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro p _
  simp only [projSet_apply]
  have hle : ‖(if p.1 ∈ S then v p else 0)‖ ≤ ‖v p‖ := by
    by_cases h : p.1 ∈ S <;> simp [h]
  gcongr

end Projection

/-! ## The oracle-difference interface `OracleDiffData` (what the O2H lemma consumes). -/

/-- **`OracleDiffData B`** — the two-oracle data the One-Way-to-Hiding lemma rides:
* `O`, `O'` : two unitaries on `QState B` (the original oracle `O_H` and the reprogrammed `O_{H'}`);
* `P` : the projection onto the reprogrammed region (`P_S`);
* `factor` : the FACTORIZATION `O v − O' v = O (P v) − O' (P v)` — the two oracles agree off the range of
  `P`, so their difference sees only the `P`-component (the heart of O2H Step 1);
* `proj_norm_le` : `‖P v‖ ≤ ‖v‖`.
This is exactly the interface `oracleDiff` (below) discharges concretely for reprogrammed random oracles. -/
structure OracleDiffData (B : Type*) [Fintype B] where
  /-- The original oracle unitary `O_H`. -/
  O : Unitary B
  /-- The reprogrammed oracle unitary `O_{H'}`. -/
  O' : Unitary B
  /-- The projection onto the reprogrammed region. -/
  P : QState B →ₗ[ℂ] QState B
  /-- The two oracles differ only through the `P`-component: `(O − O') = (O − O') ∘ P`. -/
  factor : ∀ v : QState B, O v - O' v = O (P v) - O' (P v)
  /-- The projection is norm-nonincreasing. -/
  proj_norm_le : ∀ v : QState B, ‖P v‖ ≤ ‖v‖

section Concrete

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **The concrete oracle-difference data for reprogrammed random oracles.** Given two oracles `H, H'` that
AGREE off a reprogramming set `S` (`H x = H' x` for `x ∉ S`), `oracleUnitary H` and `oracleUnitary H'`
satisfy the `OracleDiffData` interface with projection `projSet S`. The FACTORIZATION is proved from the
coordinate action: for `x ∉ S`, `H x = H' x`, so `(O_H v)(x,y) = v(x, y−H x) = v(x, y−H' x) = (O_{H'} v)(x,y)`
— the difference vanishes off `S`, hence equals its `P_S`-restricted version. This is O2H Step 1's
factorization, discharged concretely (no assumption). -/
noncomputable def oracleDiff (H H' : X → Y) (S : Finset X) (hagree : ∀ x, x ∉ S → H x = H' x) :
    OracleDiffData (X × Y) where
  O := oracleUnitary H
  O' := oracleUnitary H'
  P := projSet S
  factor := by
    intro v
    ext ⟨x, y⟩
    simp only [PiLp.sub_apply, oracleUnitary_apply, projSet_apply]
    by_cases h : x ∈ S
    · simp [h]
    · rw [hagree x h]; simp [h]
  proj_norm_le := projSet_norm_le S

@[simp] theorem oracleDiff_O (H H' : X → Y) (S : Finset X) (hagree : ∀ x, x ∉ S → H x = H' x) :
    (oracleDiff H H' S hagree).O = oracleUnitary H := rfl

@[simp] theorem oracleDiff_O' (H H' : X → Y) (S : Finset X) (hagree : ∀ x, x ∉ S → H x = H' x) :
    (oracleDiff H H' S hagree).O' = oracleUnitary H' := rfl

@[simp] theorem oracleDiff_P (H H' : X → Y) (S : Finset X) (hagree : ∀ x, x ∉ S → H x = H' x) :
    (oracleDiff H H' S hagree).P = projSet S := rfl

end Concrete

/-! ## Toy instance — a genuine permutation-unitary, on `X = Bool`, `Y = ZMod 2`.

The oracle `H = id`-ish on `ZMod 2` is a real basis permutation; we witness its unitarity concretely. -/

section Toy

/-- The toy oracle: `H b = 1` for `b = true`, `0` for `b = false`, over `Y = ZMod 2`. -/
def toyH : Bool → ZMod 2 := fun b => if b then 1 else 0

/-- The reprogrammed toy oracle: flips the value at `b = true` (differs from `toyH` only on `S = {true}`). -/
def toyH' : Bool → ZMod 2 := fun _ => 0

/-- The reprogramming set: `toyH` and `toyH'` agree off `{true}`. -/
theorem toy_agree : ∀ b, b ∉ ({true} : Finset Bool) → toyH b = toyH' b := by
  decide

/-- **The toy oracle is unitary** (norm-preserving) on a concrete basis state:
`‖O_H |true, 0⟩‖ = ‖ |true, 0⟩ ‖ = 1`. The permutation-unitary preserves norm — proved, not asserted. -/
theorem toy_oracle_unitary :
    ‖oracleUnitary toyH (EuclideanSpace.single (true, (0 : ZMod 2)) (1 : ℂ))‖ = 1 := by
  rw [oracleUnitary_norm]
  simp

/-- **The toy basis action is a genuine permutation**: `O_H |true, 0⟩ = |true, 1⟩` (moves the basis vector,
`0 + H true = 0 + 1 = 1`) — a nontrivial permutation, not the identity. -/
theorem toy_oracle_permutes :
    oracleUnitary toyH (EuclideanSpace.single (true, (0 : ZMod 2)) (1 : ℂ))
      = EuclideanSpace.single (true, (1 : ZMod 2)) (1 : ℂ) := by
  rw [oracleUnitary_single]; norm_num [toyH]

end Toy

-- Toy sanity: the oracle really permutes (image basis index differs from the source).
#guard decide (((true, (1 : ZMod 2)) : Bool × ZMod 2) ≠ (true, 0))
-- The reprogramming genuinely changes the oracle on S = {true}: toyH true = 1 ≠ 0 = toyH' true.
#guard decide (toyH true ≠ toyH' true)
-- ... and leaves it fixed off S: toyH false = 0 = toyH' false.
#guard decide (toyH false = toyH' false)

#assert_all_clean [unitary_preserves_unit, oracleUnitary_single, oracleUnitary_apply, oracleUnitary_norm,
  oracleUnitary_preserves_unit, projSet_idempotent, projSet_norm_le, toy_oracle_unitary,
  toy_oracle_permutes, toy_agree]

end Dregg2.Crypto.QuantumOracle
