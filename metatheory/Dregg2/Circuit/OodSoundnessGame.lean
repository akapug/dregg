/-
# `Dregg2.Circuit.OodSoundnessGame` — turning the two OOD residuals of `transferV3` into
PROVABLE Schwartz–Zippel bounds against the in-tree quantitative game frame (`ProbCrypto.winProb`).

The `transferV3` STARK soundness landing bottoms out (post-`MainAirAcceptF` migration) at exactly
`{hood, hnonexc}` carried by `FieldIntegerLift.OodInterpF` /
`ood_forces_mainAirAccept_field_of_residuals`. This file discharges the two pieces the
STARK-FLOOR-REDUCTION doc marks PROVABLE-NOW — with real proofs, no new assumption.

## REDUCTION 1 — `hnonexc` (Fiat–Shamir non-exceptionality) → a GAME with ε ≤ deg/|F|.

`hnonexc` asserts the OOD point ζ ∉ `exceptionalSet R_c`. This is NOT unconditional (the escape is
real — `OodQuotientConsistency.ood_exceptional_escape`), so the honest form is a bounded-advantage
game. We package the ALREADY-PROVED cardinality bound (`exceptionalSet_card_le : #exceptionalSet ≤
natDegree R`, `babybear_ood_soundness_error`) into `ProbCrypto.winProb` — the same finite
counting-probability game frame `ProtocolSoundnessQuant` / FRI's `fri_fold_soundness` use. The FS
non-exceptionality game's accept predicate is `acc ζ := ζ ∈ exceptionalSet R`, so its favorable set
IS `exceptionalSet R` and `winProb = #exceptionalSet / |F| ≤ natDegree R / |F|`
(`oodNonExc_winProb`, `oodNonExc_winProb_le`, `oodNonExc_soundness_error_babybear`). A CONCRETE
soundness-error bound, not an assumption.

## REDUCTION 2 — `hood.a` (RLC de-batching) → PROVABLE Schwartz–Zippel, no assumption.

`verifyAlgo` batches all constraints into one `constraintEval` via a random challenge Λ;
`MainAirAcceptF` wants the per-constraint identity. `batchResidual Λ := Σ_c Λ^c · R_c` is a
polynomial in the batching challenge; if ANY per-constraint residual `R_c ≠ 0` it is a nonzero
polynomial of degree `< #constraints`, so it vanishes at the sampled Λ only on the
`exceptionalSet`-bounded bad set (`batchResidual_natDegree_lt`, `_exceptionalSet_card_lt`, error
`≤ (#constraints−1)/|F|`). `rlc_debatch` reads off the per-constraint identities: batch accepted at a
NON-exceptional Λ ⟹ every `R_c = 0`. This is the identical `card_roots'` route
`LogUpSoundness.exceptionalSet_card_lt` runs on the LogUp bus, re-instantiated over the batching
challenge — via `OodQuotientConsistency.nonexceptional_eval_zero_forces_zero`.

## Residual after this file

`hnonexc` is reduced to the FS-game ε-bound (`ood_hnonexc_escape_prob_le`, ε ≤ deg/|F|), and the RLC
part of `hood` is DISCHARGED as a Lean lemma (`rlc_debatch`). `hood`'s residual is then exactly
`{hood.b commitment-binding → Poseidon2SpongeCR, hood.c FRI-LDT @ deployed params}`, plus the one
named unmodeled-plumbing wire (exhibiting the descriptor's actual Λ-column and per-constraint
residual layout — the same "column-layout is unmodeled" residual `LogUpSoundness §8` names for
`hbus`). No `sorry`, no `Finset.univ` enumerated over `|F|` (the bounds are polynomial-degree bounds
via `card_roots'`, never an enumeration of BabyBear).
-/
import Dregg2.Tactics
import Dregg2.Crypto.ProbCrypto
import Dregg2.Circuit.OodQuotientConsistency
import Dregg2.Circuit.FieldIntegerLift

namespace Dregg2.Circuit.OodSoundnessGame

open Polynomial
open Dregg2.Circuit.OodQuotientConsistency
open Dregg2.Crypto.ProbCrypto

/-! ## REDUCTION 1 — the Fiat–Shamir non-exceptionality game (ε ≤ deg/|F|).

The favorable set of the game is the exceptional set, whose cardinality is already bounded by
`exceptionalSet_card_le`. `winProb` of the game is therefore `#exceptionalSet / |F| ≤ deg / |F|`. -/

section NonExcGame

variable {F : Type*} [Fintype F] [CommRing F] [IsDomain F] [DecidableEq F]

/-- **The FS non-exceptionality game's accept predicate.** Over the challenge space `F` (the OOD point
domain), the "prover escapes" event is `ζ ∈ exceptionalSet R` — ζ is a root of the residual `R`, so
the tampered quotient passes the OOD identity even though `R ≠ 0`. -/
noncomputable def oodNonExcAcc (R : Polynomial F) : F → Bool := fun ζ => decide (ζ ∈ exceptionalSet R)

/-- **The game's winning probability is `#exceptionalSet / |F|`.** The favorable outcomes of the game
are EXACTLY the exceptional set (`filter (· ∈ exceptionalSet R) univ = exceptionalSet R`), so
`winProb` is its cardinality over the field size — a genuine probability, no enumeration of `|F|`. -/
theorem oodNonExc_winProb (R : Polynomial F) :
    winProb (oodNonExcAcc R) = ((exceptionalSet R).card : ℝ) / (Fintype.card F : ℝ) := by
  unfold winProb oodNonExcAcc
  have hfilter :
      (Finset.univ.filter (fun o => decide (o ∈ exceptionalSet R) = true)) = exceptionalSet R := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  rw [hfilter]

/-- **REDUCTION 1 — the FS-game ε-bound: `winProb ≤ natDegree R / |F|`.** The probability the
Fiat–Shamir challenge lands exceptional (violating `hnonexc`) is at most `deg R / |F|` — the
`exceptionalSet_card_le` Schwartz–Zippel bound, transported into the `winProb` game frame. A CONCRETE
soundness error, NOT an assumption; `hnonexc` is reduced to this bounded-advantage event. -/
theorem oodNonExc_winProb_le (R : Polynomial F) :
    winProb (oodNonExcAcc R) ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) := by
  rw [oodNonExc_winProb]
  gcongr
  exact_mod_cast exceptionalSet_card_le R

end NonExcGame

/-! ### REDUCTION 1 at the deployed field (BabyBear, `|F| = 2013265921`). -/

section NonExcBabyBear

open Dregg2.Circuit.BabyBearFriField

/-- The concrete BabyBear field cardinality (symbolic; NOT an enumeration of the `2·10⁹` elements). -/
theorem babybear_card : Fintype.card BabyBear = 2013265921 := by
  haveI : NeZero babyBearP := ⟨by norm_num⟩
  exact ZMod.card babyBearP

/-- **REDUCTION 1 @ BabyBear — the deployed FS-game soundness error `≤ natDegree R / 2013265921`.**
The probability a uniform OOD ζ escapes into the exceptional set of the residual `R` is at most
`deg R / |BabyBear|`. -/
theorem oodNonExc_soundness_error_babybear (R : Polynomial BabyBear) :
    winProb (oodNonExcAcc R) ≤ (R.natDegree : ℝ) / 2013265921 := by
  have h := oodNonExc_winProb_le R
  rwa [show (Fintype.card BabyBear : ℝ) = 2013265921 by exact_mod_cast babybear_card] at h

end NonExcBabyBear

/-! ### Teeth for REDUCTION 1 (both poles load-bearing), over the tiny field `ZMod 7`
(never over `|F|` — `ZMod 7` is 7 elements). -/

section NonExcTeeth

/-- `ZMod 7` is a field (needed for `IsDomain` in the teeth's residual polynomials). -/
private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- POSITIVE POLE (the game achieves a genuine positive probability): the residual `X` has exceptional
set `{0}` (its single root), so `winProb = 1/7` — the tampered-quotient escape probability is real and
positive. This is `natDegree X / |F| = 1/7`, TIGHT against `oodNonExc_winProb_le`. -/
theorem oodNonExc_winProb_fires :
    winProb (oodNonExcAcc (X : Polynomial (ZMod 7))) = 1 / 7 := by
  rw [oodNonExc_winProb]
  have hcard : (exceptionalSet (X : Polynomial (ZMod 7))).card = 1 := by
    unfold exceptionalSet
    rw [roots_X]
    decide
  rw [hcard, show Fintype.card (ZMod 7) = 7 from ZMod.card 7]
  norm_num

/-- NEGATIVE POLE (no escape): a nonzero constant residual `C 1` has NO roots (`roots_C = 0`), so its
exceptional set is empty and `winProb = 0` — an honest match escapes with probability zero. -/
theorem oodNonExc_winProb_bot :
    winProb (oodNonExcAcc (C (1 : ZMod 7))) = 0 := by
  rw [oodNonExc_winProb]
  have hcard : (exceptionalSet (C (1 : ZMod 7))).card = 0 := by
    unfold exceptionalSet; rw [roots_C]; simp
  rw [hcard]; simp

end NonExcTeeth

/-! ## REDUCTION 2 — RLC de-batching via Schwartz–Zippel (`rlc_debatch`), no assumption.

`verifyAlgo` folds the per-constraint residuals `R_c` into a single value via the batching challenge
Λ: `Σ_c R_c · Λ^c`. Viewed as a polynomial in Λ, this is `batchResidual R`. If any `R_c ≠ 0` it is a
nonzero polynomial (its `c`-th coefficient is `R_c`), so it vanishes at Λ only on its root set, which
has `< #constraints` elements. Off that exceptional set, the batched zero forces EVERY `R_c = 0` —
the per-constraint OOD identities. Identical `card_roots'` route as `LogUpSoundness`. -/

section Debatch

variable {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]

/-- **The RLC batching polynomial** `batchResidual R = Σ_c R_c · X^c` — the per-constraint residuals
`R : Fin n → F` weighted by powers of the batching challenge (here the indeterminate `X = Λ`). Its
value at a concrete Λ is `verifyAlgo`'s batched `constraintEval` residual. -/
noncomputable def batchResidual {n : ℕ} (R : Fin n → F) : Polynomial F :=
  ∑ c : Fin n, C (R c) * X ^ (c : ℕ)

/-- Its value at a challenge Λ is the batched sum `Σ_c R_c · Λ^c`. -/
theorem batchResidual_eval {n : ℕ} (R : Fin n → F) (Λ : F) :
    (batchResidual R).eval Λ = ∑ c : Fin n, R c * Λ ^ (c : ℕ) := by
  unfold batchResidual
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- **The `c`-th coefficient of `batchResidual R` is exactly `R c`.** Distinct Fin indices land in
distinct powers `X^c`, so coefficient extraction reads off each per-constraint residual — the reason a
nonzero residual forces a nonzero polynomial. -/
theorem batchResidual_coeff {n : ℕ} (R : Fin n → F) (j : Fin n) :
    (batchResidual R).coeff (j : ℕ) = R j := by
  unfold batchResidual
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, Fin.val_inj, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq j R

/-- **REDUCTION 2 — RLC de-batching, DISCHARGED.** If the batched residual polynomial vanishes at a
NON-exceptional challenge Λ (Λ ∉ its root set), then EVERY per-constraint residual `R_c = 0` — the
per-constraint OOD identities `MainAirAcceptF` demands. A real Schwartz–Zippel de-batch, via
`OodQuotientConsistency.nonexceptional_eval_zero_forces_zero`; NO assumption. -/
theorem rlc_debatch {n : ℕ} (R : Fin n → F) (Λ : F)
    (heval : (batchResidual R).eval Λ = 0)
    (hnonexc : Λ ∉ exceptionalSet (batchResidual R)) :
    ∀ c, R c = 0 := by
  have hzero : batchResidual R = 0 :=
    nonexceptional_eval_zero_forces_zero (batchResidual R) Λ heval hnonexc
  intro c
  have hc := batchResidual_coeff R c
  rw [hzero, coeff_zero] at hc
  exact hc.symm

/-- The batching polynomial has degree `< #constraints` — the Schwartz–Zippel degree the exceptional
set rides. (Coefficients at index `≥ n` vanish: every power `X^c` has `c < n`.) -/
theorem batchResidual_natDegree_lt {n : ℕ} (hn : 0 < n) (R : Fin n → F) :
    (batchResidual R).natDegree < n := by
  refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr ?_) (Nat.sub_lt hn Nat.one_pos)
  intro N hN
  unfold batchResidual
  rw [finsetSum_coeff]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [coeff_C_mul, coeff_X_pow, if_neg (by have hc := c.isLt; omega), mul_zero]

/-- **The RLC bad-Λ set is small: `< #constraints`.** So a uniform batching challenge misses it except
with probability `≤ (#constraints − 1)/|F|` — the residual soundness-error term ε_RLC. -/
theorem batchResidual_exceptionalSet_card_lt {n : ℕ} (hn : 0 < n) (R : Fin n → F) :
    (exceptionalSet (batchResidual R)).card < n :=
  lt_of_le_of_lt (exceptionalSet_card_le _) (batchResidual_natDegree_lt hn R)

end Debatch

/-! ### REDUCTION 2's soundness error at BabyBear, packaged in the `winProb` game frame. -/

section DebatchBabyBear

open Dregg2.Circuit.BabyBearFriField

/-- **REDUCTION 2 @ BabyBear — ε_RLC `≤ (#constraints − 1)/2013265921`.** The probability a uniform
batching challenge lands in the RLC bad set is at most `(n−1)/|BabyBear|`, via the `winProb` game on
`batchResidual` and its degree bound. Ties REDUCTION 2 to the same quantitative frame as REDUCTION 1. -/
theorem rlc_debatch_error_babybear {n : ℕ} (hn : 0 < n) (R : Fin n → BabyBear) :
    winProb (oodNonExcAcc (batchResidual R)) ≤ ((n - 1 : ℕ) : ℝ) / 2013265921 := by
  have hd : (batchResidual R).natDegree ≤ n - 1 := by
    have := batchResidual_natDegree_lt hn R; omega
  refine le_trans (oodNonExc_soundness_error_babybear (batchResidual R)) ?_
  gcongr <;> exact_mod_cast hd

end DebatchBabyBear

/-! ### Teeth for REDUCTION 2 (both poles load-bearing), over `ℤ` (an integral domain). -/

section DebatchTeeth

/-- FIRE: a genuinely nonzero per-constraint residual family makes `batchResidual` a NONZERO
polynomial (its `0`-th coefficient is `R 0 = 1`) — the de-batch soundness bite: the prover cannot hide
a nonzero constraint behind the batch. -/
theorem batchResidual_bites : batchResidual (fun _ : Fin 2 => (1 : ℤ)) ≠ 0 := by
  intro h
  have hc := batchResidual_coeff (fun _ : Fin 2 => (1 : ℤ)) 0
  rw [h, coeff_zero] at hc
  simp at hc

/-- FIRE, all the way through `rlc_debatch`: a batch that vanishes at the NON-exceptional Λ = 5 (the
all-zero residual family, whose batch polynomial is `0` with empty exceptional set) yields every
`R_c = 0`. The landing lemma is not vacuous. -/
theorem rlc_debatch_fires : ∀ c, (fun _ : Fin 2 => (0 : ℤ)) c = 0 := by
  refine rlc_debatch (fun _ : Fin 2 => (0 : ℤ)) 5 ?_ ?_
  · rw [batchResidual_eval]; simp
  · have hz : batchResidual (fun _ : Fin 2 => (0 : ℤ)) = 0 := by unfold batchResidual; simp
    rw [hz]; simp [exceptionalSet]

/-- ESCAPE POLE (proves `hnonexc` is load-bearing in REDUCTION 2 too): at the EXCEPTIONAL challenge
Λ = −1 the nonzero residual family `(1,1)` has a BALANCED batch (`1·(−1)^0 + 1·(−1)^1 = 0`) even
though not all `R_c = 0`. Without demanding Λ non-exceptional, `rlc_debatch` would be FALSE — the
batching exceptional set is genuinely non-vacuous. -/
theorem rlc_debatch_exceptional_escape :
    (batchResidual (fun _ : Fin 2 => (1 : ℤ))).eval (-1) = 0
      ∧ ¬ (∀ c, (fun _ : Fin 2 => (1 : ℤ)) c = 0) := by
  refine ⟨?_, ?_⟩
  · rw [batchResidual_eval, Fin.sum_univ_two]; norm_num
  · intro hh; have := hh 0; simp at this

end DebatchTeeth

/-! ## Wiring into the `transferV3` residual frontier.

`FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals` carries `hood` + `hnonexc` for the
residual `constraintPoly d t c − vanishingPoly t · qp c`. REDUCTION 1 bounds the probability that a
Fiat–Shamir ζ violates that exact `hnonexc`. -/

section Wiring

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.TraceColumnInterp
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.FieldIntegerLift

/-- **`hnonexc`, reduced to the FS-game ε-bound at the DEPLOYED residual.** The probability the
Fiat–Shamir OOD point ζ lands in `exceptionalSet (constraintPoly d t c − vanishingPoly t · qp c)` —
i.e. VIOLATES the `hnonexc` premise of `ood_forces_mainAirAccept_field_of_residuals` — is at most
`deg (residual) / 2013265921`. This is `hnonexc` in its honest, non-assumption form: a bounded-advantage
Fiat–Shamir game, ε ≤ deg/|F|. -/
theorem ood_hnonexc_escape_prob_le (d : EffectVmDescriptor2) (t : VmTrace)
    (qp : VmConstraint2 → Polynomial BabyBear) (c : VmConstraint2) :
    winProb (oodNonExcAcc (constraintPoly d t c - vanishingPoly t * qp c))
      ≤ ((constraintPoly d t c - vanishingPoly t * qp c).natDegree : ℝ) / 2013265921 :=
  oodNonExc_soundness_error_babybear _

end Wiring

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms oodNonExc_winProb
#assert_axioms oodNonExc_winProb_le
#assert_axioms oodNonExc_soundness_error_babybear
#assert_axioms oodNonExc_winProb_fires
#assert_axioms oodNonExc_winProb_bot
#assert_axioms batchResidual_eval
#assert_axioms batchResidual_coeff
#assert_axioms rlc_debatch
#assert_axioms batchResidual_natDegree_lt
#assert_axioms batchResidual_exceptionalSet_card_lt
#assert_axioms rlc_debatch_error_babybear
#assert_axioms batchResidual_bites
#assert_axioms rlc_debatch_fires
#assert_axioms rlc_debatch_exceptional_escape
#assert_axioms ood_hnonexc_escape_prob_le

end Dregg2.Circuit.OodSoundnessGame
