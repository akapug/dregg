/-
# `Dregg2.Circuit.RlcSoundnessBound` — the CONCRETE Schwartz–Zippel soundness bound for the
RLC constraint-batching split, over the DEPLOYED BabyBear field.

`OodQuotientConsistency` proved K′(c): a combined RLC identity `∑ᵢ Rᵢ·αⁱ = 0` at a
non-exceptional batching challenge `α` splits back to `∀ i, Rᵢ = 0`
(`rlc_batch_split_of_combined`). What it did NOT quantify is HOW LIKELY the escape is —
the batching analogue of `babybear_ood_soundness_error`. This file closes that number:

  * `rlcResidualPoly_natDegree_le` — the batching polynomial `P(α) = ∑_{i<n} rᵢ·αⁱ` has
    `natDegree ≤ n − 1`, UNCONDITIONALLY (over any `CommRing`; for `n = 0` the sum is `0`
    and `0 ≤ 0 − 1 = 0` in ℕ).
  * `rlcResidualPoly_natDegree_lt` — hence `natDegree < n` whenever `0 < n`. (Honesty
    note: the strict form needs NO hypothesis on `r` — `0 < n` alone suffices, since
    `natDegree ≤ n − 1 < n`. Demanding `r (n−1) ≠ 0` would buy exact degree `n − 1`,
    which the soundness bound never needs; we state the weaker, cleaner, TRUE hypothesis.)
  * `rlc_soundness_error` — over the DEPLOYED field `BabyBear = ZMod 2013265921`
    (`babyBearP`, not a toy): the exceptional set of the batching polynomial has
    `card ≤ n − 1`, and `Fintype.card BabyBear = 2013265921`. Read: a uniformly drawn
    batching challenge lands in the exceptional set — the ONLY way a genuinely tampered
    batch (`some rᵢ ≠ 0`) survives the split — with probability
    `≤ (n−1)/2013265921 < n/2013265921`.
  * `rlc_soundness_error_lt` — the strict `card < n` reading, for `0 < n`.

## Teeth (FIRE over the deployed field — every bound COMPUTES on a concrete witness)

`rFire = [1, −1]` is a concrete NONZERO residual vector over BabyBear (a genuine
per-constraint mismatch). `rlc_fire_nonzero` shows its batching polynomial is not the zero
polynomial (so the degree/card bounds are not vacuously about `P = 0`);
`rlc_fire_bounds` computes `natDegree < 2`, `card ≤ 1`, `|F| = 2013265921` on it;
`rlc_fire_catches` shows the concrete challenge `α = 2` CATCHES the tamper (combined value
`= −1 ≠ 0`); `rlc_fire_escape` shows the EXCEPTIONAL challenge `α = 1` lets the same
tamper pass (`hnonexc` is load-bearing over the deployed field, exactly as
`rlc_batch_exceptional_escape` showed over ℤ).
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Dregg2.Circuit.OodQuotientConsistency

namespace Dregg2.Circuit.RlcSoundnessBound

open Polynomial
open Dregg2.Circuit.OodQuotientConsistency
open Dregg2.Circuit.BabyBearFriField

/-! ## §1 — The degree bound on the batching polynomial (over any `CommRing`). -/

/-- **The batching polynomial is low-degree.** `P(α) = ∑_{i<n} rᵢ·αⁱ` sums monomials
`C (rᵢ)·Xⁱ` of degree `≤ i ≤ n − 1`, so `natDegree P ≤ n − 1` — unconditionally (for
`n = 0` the empty sum is `0`, with `natDegree 0 = 0 ≤ 0`). This is the degree input the
Schwartz–Zippel bound consumes. -/
theorem rlcResidualPoly_natDegree_le {F : Type*} [CommRing F] (n : ℕ) (r : ℕ → F) :
    (rlcResidualPoly n r).natDegree ≤ n - 1 := by
  unfold rlcResidualPoly
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_C_mul_X_pow_le (r i) i).trans
    (Nat.le_pred_of_lt (Finset.mem_range.mp hi))

/-- **Strict form: `natDegree < n` for any positive batch size.** No hypothesis on `r` is
needed (see the module header's honesty note): `natDegree ≤ n − 1 < n` once `0 < n`. -/
theorem rlcResidualPoly_natDegree_lt {F : Type*} [CommRing F] (n : ℕ) (hn : 0 < n)
    (r : ℕ → F) : (rlcResidualPoly n r).natDegree < n :=
  lt_of_le_of_lt (rlcResidualPoly_natDegree_le n r) (by omega)

/-! ## §2 — The concrete soundness error, at the DEPLOYED BabyBear field. -/

/-- **The RLC batching soundness error over `BabyBear = ZMod 2013265921`.** The exceptional
set of the batching polynomial — the only challenges `α` at which a genuinely tampered batch
(`some rᵢ ≠ 0`) can still satisfy the combined identity `∑ᵢ rᵢ·αⁱ = 0`
(`rlc_batch_split_of_combined` splits it everywhere else) — has at most `n − 1` elements,
out of `2013265921` field elements. A uniform Fiat–Shamir batching challenge therefore fails
to split the batch with probability `≤ (n−1)/2013265921 < n/2013265921` — the batching
analogue of `babybear_ood_soundness_error`, via `exceptionalSet_card_le` +
`rlcResidualPoly_natDegree_le` + `ZMod.card`. -/
theorem rlc_soundness_error (n : ℕ) (r : ℕ → BabyBear) :
    (exceptionalSet (rlcResidualPoly n r)).card ≤ n - 1 ∧
      Fintype.card BabyBear = 2013265921 :=
  ⟨(exceptionalSet_card_le _).trans (rlcResidualPoly_natDegree_le n r), by
    haveI : NeZero babyBearP := ⟨by norm_num⟩
    exact ZMod.card babyBearP⟩

/-- The strict `< n` reading of the error bound: for any positive batch size, STRICTLY
fewer than `n` of the `2013265921` challenges are exceptional. -/
theorem rlc_soundness_error_lt (n : ℕ) (hn : 0 < n) (r : ℕ → BabyBear) :
    (exceptionalSet (rlcResidualPoly n r)).card < n :=
  lt_of_le_of_lt (exceptionalSet_card_le _) (rlcResidualPoly_natDegree_lt n hn r)

/-! ## §3 — FIRE teeth over the deployed field: every bound computes on a concrete tamper. -/

/-- A concrete NONZERO residual vector over the deployed field: `r = [1, −1]` — a genuine
per-constraint mismatch (constraint 0 over-satisfied by `1`, constraint 1 by `−1`). -/
noncomputable def rFire : ℕ → BabyBear := fun i => if i = 0 then 1 else -1

/-- The concrete batching polynomial is NOT the zero polynomial (its coefficient `0` is
`1 ≠ 0` by `rlcResidualPoly_coeff`) — so the degree/card bounds below are about a genuine
tamper, not the vacuous `P = 0`. -/
theorem rlc_fire_nonzero : rlcResidualPoly 2 rFire ≠ 0 := by
  intro h
  have hc := rlcResidualPoly_coeff 2 rFire 0 (by norm_num)
  rw [h, coeff_zero] at hc
  simp [rFire] at hc

/-- The bounds COMPUTE on the concrete tamper: `natDegree < 2`, at most `1` exceptional
challenge out of `2013265921`. -/
theorem rlc_fire_bounds :
    (rlcResidualPoly 2 rFire).natDegree < 2 ∧
      (exceptionalSet (rlcResidualPoly 2 rFire)).card ≤ 1 ∧
      Fintype.card BabyBear = 2013265921 :=
  ⟨rlcResidualPoly_natDegree_lt 2 (by norm_num) rFire,
   (rlc_soundness_error 2 rFire).1, (rlc_soundness_error 2 rFire).2⟩

/-- FIRE (catch): the concrete NON-exceptional challenge `α = 2` catches the tamper — the
combined RLC value is `1·2⁰ + (−1)·2¹ = −1 ≠ 0`, so the verifier's combined check REJECTS. -/
theorem rlc_fire_catches :
    (∑ i ∈ Finset.range 2, rFire i * (2 : BabyBear) ^ i = -1) ∧ (-1 : BabyBear) ≠ 0 := by
  refine ⟨?_, neg_ne_zero.mpr one_ne_zero⟩
  simp [Finset.sum_range_succ, rFire]
  ring

/-- EXCEPTIONAL ESCAPE over the DEPLOYED field (`hnonexc` is load-bearing): at the
exceptional challenge `α = 1` — a root of the batching polynomial — the SAME tamper batches
to `1·1 + (−1)·1 = 0` and passes the combined check even though `rFire 0 = 1 ≠ 0`. The
exceptional set is real, and `rlc_soundness_error` is exactly the measure of how rare it is. -/
theorem rlc_fire_escape :
    (∑ i ∈ Finset.range 2, rFire i * (1 : BabyBear) ^ i = 0) ∧ rFire 0 ≠ 0 := by
  refine ⟨?_, by simp [rFire]⟩
  simp [Finset.sum_range_succ, rFire]

#assert_axioms rlcResidualPoly_natDegree_le
#assert_axioms rlcResidualPoly_natDegree_lt
#assert_axioms rlc_soundness_error
#assert_axioms rlc_soundness_error_lt
#assert_axioms rlc_fire_nonzero
#assert_axioms rlc_fire_bounds
#assert_axioms rlc_fire_catches
#assert_axioms rlc_fire_escape

end Dregg2.Circuit.RlcSoundnessBound
