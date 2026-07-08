/-
# `Dregg2.Crypto.HermineConcrete` — the Hermine MSIS reduction, CONCRETE.

`Dregg2.Crypto.HermineMSIS` and `Dregg2.Crypto.HermineDischarge` prove the forking reduction
typeclass-abstractly: over ANY `[CommRing Rq]`, `[Module Rq M]`, `[ShortNorm M]`. This file
instantiates it over a REAL module with REAL numbers, so the reduction is demonstrably non-vacuous:
the abstract extractor, fed a concrete forked forgery on a concrete matrix, hands back an actual
short nonzero kernel vector, checked by `decide`.

* **The norm.** `ShortNorm` is instantiated on integer vectors `Fin d → ℤ` with the L1 norm
  `nrm v = Σᵢ |vᵢ|`. Honesty note: real lattice crypto measures shortness on the INTEGER LIFT of
  `R_q`-elements (coefficients lifted to `ℤ`, where the triangle inequality holds cleanly) — working
  over `ℤ` here is exactly that lift, not a simplification of it. The mod-`q` ring structure is what
  the abstract layer's `Rq` carries; the norm never lived there.
* **The instance.** `A = [1 2] : ℤ^2 → ℤ^1`, key `s = (1,0)`, lossy twin `s' = (3,-1)` (both map to
  `t = 1`), commitment `w = 0`, challenges `c = 1, c' = 0`. The forger answers with `s'`; the
  extractor's `u = (z−z') − (c−c')·s = (2,−1)` — nonzero, `‖u‖₁ = 3`, and `1·2 + 2·(−1) = 0`, i.e. a
  genuine MSIS solution. All facts are decided on the actual numbers.
* **The parameter facts, concretely.** `c − c' = 1` is a unit of `ℤ` (over `ℤ` the units are `±1`),
  feeding `lossiness_discharges_nonzero`; the lossiness itself is WITNESSED (`s ≠ s'`, `A s = A s'`),
  not assumed. Honesty note: the FULL-parameter invertibility — that ANY difference of two distinct
  Dilithium/Raccoon challenges is a unit of `R_q = ℤ_q[X]/(Xⁿ+1)` — is the deeper number-theoretic
  lemma this concrete cut does not prove; what is exhibited here is the exact SHAPE that lemma feeds.
-/
import Dregg2.Crypto.HermineDischarge
import Mathlib.Data.Fin.VecNotation

namespace Dregg2.Crypto.HermineConcrete

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineMSIS
open Dregg2.Crypto.HermineDischarge

/-! ## Target 1 — a concrete `ShortNorm`: the L1 norm on integer vectors -/

/-- The L1 norm `Σᵢ |vᵢ|` on integer vectors: a REAL `ShortNorm` instance (the integer-lift norm of
lattice crypto). Zero, negation-invariance, and the triangle inequality are proved pointwise from
`Int.natAbs`. -/
instance instShortNormIntVec (d : ℕ) : ShortNorm (Fin d → ℤ) where
  nrm v := ∑ i, (v i).natAbs
  nrm_zero := by simp
  nrm_neg a := by simp [Int.natAbs_neg]
  nrm_add_le a b :=
    calc ∑ i, ((a + b) i).natAbs
        = ∑ i, (a i + b i).natAbs := rfl
      _ ≤ ∑ i, ((a i).natAbs + (b i).natAbs) :=
          Finset.sum_le_sum fun i _ => Int.natAbs_add_le (a i) (b i)
      _ = (∑ i, (a i).natAbs) + ∑ i, (b i).natAbs := Finset.sum_add_distrib

/-! ## The concrete instance: matrix, keys, transcripts -/

/-- The concrete public matrix `A = [1 2] : ℤ² →ₗ ℤ¹` — compressing, so the kernel is nontrivial;
the MSIS content is that the extracted kernel vector is SHORT and NONZERO. -/
def Amat : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) where
  toFun v := fun _ => v 0 + 2 * v 1
  map_add' x y := by funext j; simp; ring
  map_smul' r x := by funext j; simp; ring

/-- The signer's short secret, `s = (1, 0)`; `‖s‖₁ = 1`; public key `t = A s = (1)`. -/
def svec : Fin 2 → ℤ := ![1, 0]

/-- The lossy twin, `s' = (3, −1)`: distinct from `s`, also short (`‖s'‖₁ = 4`), same key
(`3 + 2·(−1) = 1`). This is MLWE lossiness WITNESSED on the instance, not assumed. -/
def svec' : Fin 2 → ℤ := ![3, -1]

/-- The shared commitment `w = A·y` with mask `y = 0`. -/
def wcom : Fin 1 → ℤ := 0

/-- First fork challenge. -/
def cch : ℤ := 1

/-- Second fork challenge; `cch − cch' = 1`, a unit of `ℤ`. -/
def cch' : ℤ := 0

/-- The forger's first response — computed from the TWIN secret: `z = y + c·s' = (3, −1)`. -/
def zvec : Fin 2 → ℤ := ![3, -1]

/-- The forger's second response: `z' = y + c'·s' = (0, 0)`. -/
def zvec' : Fin 2 → ℤ := ![0, 0]

/-- The vector the abstract extractor produces on these numbers: `u = (z−z') − (c−c')·s = (2, −1)`. -/
def uvec : Fin 2 → ℤ := ![2, -1]

/-! ## Target 2 — the worked, decidable example: the reduction is NON-VACUOUS -/

/-- The L1 instance computes on real numbers: `‖(2, −1)‖₁ = 3`. -/
theorem nrm_uvec : nrm uvec = 3 := by decide

/-- Both forked transcripts VERIFY (the real `HermineThreshold.verify` relation `A z = w + c·t`
against the honest key `t = A svec`), checked on the numbers. -/
theorem forked_transcripts_verify :
    HermineThreshold.verify Amat (Amat svec) wcom cch zvec ∧
    HermineThreshold.verify Amat (Amat svec) wcom cch' zvec' := by
  constructor <;> · show _ = _; decide

/-- The fork is a real fork: distinct challenges. -/
theorem challenges_distinct : cch ≠ cch' := by decide

/-- **The abstract reduction fires on the concrete instance.** Feeding the concrete forked forgery to
`forked_forgery_yields_msis_solution` (the REAL abstract theorem, no restatement) produces an MSIS
solution at the extracted bound `βz + βz + βcs = 4 + 4 + 1 = 9`. Every hypothesis is discharged by
`decide` on the actual numbers. -/
theorem concrete_forked_forgery_yields_msis_solution :
    IsMSISSolution Amat 9 ((zvec - zvec') - (cch - cch') • svec) :=
  forked_forgery_yields_msis_solution Amat svec wcom cch cch' zvec zvec' 4 1
    (by decide) (by decide) (by decide)
    forked_transcripts_verify.1 forked_transcripts_verify.2
    (by decide)

/-- The extracted vector IS `(2, −1)` — the actual numbers, not a symbol. -/
theorem extracted_vector_is_uvec : (zvec - zvec') - (cch - cch') • svec = uvec := by decide

/-- **The non-vacuity payoff**: `u = (2, −1)` is a genuine Module-SIS solution for `A = [1 2]` at
bound 9 — produced BY the abstract reduction on this instance. -/
theorem concrete_msis_witness : IsMSISSolution Amat 9 uvec :=
  extracted_vector_is_uvec ▸ concrete_forked_forgery_yields_msis_solution

/-- Direct check of all three legs of the solution on the numbers, independently of the reduction:
`u ≠ 0`, `‖u‖₁ = 3 ≤ 9`, and `A u = 1·2 + 2·(−1) = 0`. -/
theorem concrete_msis_witness_checks : uvec ≠ 0 ∧ nrm uvec ≤ 9 ∧ Amat uvec = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Target 3 — the parameter facts, concretely -/

/-- The concrete challenge difference `cch − cch' = 1` is a unit (over `ℤ`, the units are `±1`). -/
theorem concrete_challenge_difference_isUnit : IsUnit (cch - cch') := by
  rw [show cch - cch' = 1 by decide]
  exact isUnit_one

/-- MLWE lossiness WITNESSED: two distinct short preimages of the same public key,
`s = (1,0) ≠ (3,−1) = s'` with `A s = A s' = (1)` and both L1-short (`1` and `4`). -/
theorem concrete_lossiness_witnessed :
    svec ≠ svec' ∧ Amat svec = Amat svec' ∧ nrm svec ≤ 4 ∧ nrm svec' ≤ 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The discharge lemma fires on the concrete unit + lossiness: at least one extracted candidate is
nonzero — `u ≠ 0` DERIVED, not hypothesized, on real numbers. -/
theorem concrete_nonzero_discharged :
    (zvec - zvec') - (cch - cch') • svec ≠ 0 ∨ (zvec - zvec') - (cch - cch') • svec' ≠ 0 :=
  lossiness_discharges_nonzero svec svec' cch cch' zvec zvec'
    (by decide) concrete_challenge_difference_isUnit

/-- **End-to-end on the discharged reduction**: the concrete forgery + witnessed lossiness + concrete
unit run through `forked_forgery_yields_msis_solution_discharged` (bound `4 + 4 + 4 = 12`, since `βcs`
must cover both `(c−c')·s` and `(c−c')·s'`) and produce an MSIS solution with NO `u ≠ 0` hypothesis
anywhere. -/
theorem concrete_discharged_reduction : ∃ u, IsMSISSolution Amat 12 u :=
  forked_forgery_yields_msis_solution_discharged Amat svec svec' wcom cch cch' zvec zvec' 4 4
    (by decide) (by decide) concrete_challenge_difference_isUnit
    (by decide) (by decide) (by decide) (by decide)
    forked_transcripts_verify.1 forked_transcripts_verify.2

#assert_axioms nrm_uvec
#assert_axioms forked_transcripts_verify
#assert_axioms challenges_distinct
#assert_axioms concrete_forked_forgery_yields_msis_solution
#assert_axioms extracted_vector_is_uvec
#assert_axioms concrete_msis_witness
#assert_axioms concrete_msis_witness_checks
#assert_axioms concrete_challenge_difference_isUnit
#assert_axioms concrete_lossiness_witnessed
#assert_axioms concrete_nonzero_discharged
#assert_axioms concrete_discharged_reduction

end Dregg2.Crypto.HermineConcrete
