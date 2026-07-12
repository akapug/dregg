/-
# Low-degree UNIQUENESS — interpolation uniqueness for the FriExtract discharge.

THE BRICK: in the unique-decoding regime, an accepted codeword determines AT MOST ONE
low-degree polynomial. This file proves the coding-theory half of that pin:

  **`lowDegree_agree_forces_eq`** — if `p, q` both have `natDegree < k` and agree on a set
  `S` of (distinct, Finset-enforced) points with `k ≤ S.card`, then `p = q`. Reason: the
  difference `p − q` has `natDegree < k` and vanishes at ≥ k points, so it is the zero
  polynomial (`Polynomial.eq_of_natDegree_lt_card_of_eval_eq'`, the `card_roots'` route the
  OOD/LogUp Schwartz–Zippel bricks already run on).

Specialized at the DEPLOYED field (`BabyBear = ZMod 2013265921`, the descriptor's
`field_modulus`): `lowDegree_agree_forces_eq_babyBear`.

Both polarities:
  * FIRE — `lowDegree_uniqueness_fires`: two syntactically different degree-2 BabyBear
    polynomials agreeing on 3 concrete points are forced EQUAL via the theorem (not by `ring`).
  * BITE-adjacent non-vacuity — `nonzero_lowDegree_somewhere_nonzero`: a NONZERO poly of
    `natDegree < k` cannot vanish on all of a size-≥k set (equivalently: it has < k roots,
    `lowDegree_roots_card_lt`); and `lowDegree_distinct_must_disagree`: two DISTINCT
    low-degree polys must visibly disagree at some point of any size-≥k set.

SCOPE (honest): this is the INTERPOLATION-UNIQUENESS half of "an accepted codeword pins a
unique low-degree polynomial". The PROXIMITY / list-decoding half — that a function within
the unique-decoding distance bound of the RS code has a nearby low-degree polynomial at all,
and that FRI acceptance certifies that proximity — is the SEPARATE deep half (BBHR18-style
distortion analysis) and is NOT attempted here.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Dregg2.Circuit.BabyBearFriField
import Dregg2.Tactics

namespace Dregg2.Circuit.LowDegreeUniqueness

open Polynomial
open Dregg2.Circuit.BabyBearFriField

variable {F : Type*} [CommRing F] [IsDomain F]

/-! ## §1 — Interpolation uniqueness over any integral domain. -/

/-- **Interpolation uniqueness (unique-decoding uniqueness).** Two polynomials of
`natDegree < k` that agree on a set `S` of at least `k` distinct points are EQUAL:
`p − q` has `natDegree < k` and ≥ k roots, hence is `0`. This is why a codeword in the
unique-decoding regime determines its low-degree polynomial — there is no second one. -/
theorem lowDegree_agree_forces_eq {k : ℕ} (p q : Polynomial F) (S : Finset F)
    (hp : p.natDegree < k) (hq : q.natDegree < k) (hcard : k ≤ S.card)
    (hagree : ∀ x ∈ S, p.eval x = q.eval x) : p = q :=
  Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p q S hagree
    ((max_lt hp hq).trans_le hcard)

/-- **A low-degree polynomial has fewer than `k` (distinct) roots.** The root-count face of
the same coin (stated for all `p`; Mathlib sets `(0 : F[X]).roots = 0`, so the bound is
unconditional — the NONZERO content is `nonzero_lowDegree_somewhere_nonzero` below). -/
theorem lowDegree_roots_card_lt {k : ℕ} [DecidableEq F] (p : Polynomial F)
    (hd : p.natDegree < k) :
    p.roots.toFinset.card < k :=
  ((Multiset.toFinset_card_le _).trans (card_roots' p)).trans_lt hd

/-- **Non-vacuity: a NONZERO low-degree polynomial cannot vanish on a size-≥k set.** The
`p ≠ 0` hypothesis is load-bearing: were `p = 0` it would vanish everywhere. Contrapositive
of `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` — the "< k roots" fact in effective form. -/
theorem nonzero_lowDegree_somewhere_nonzero {k : ℕ} (p : Polynomial F) (hne : p ≠ 0)
    (hd : p.natDegree < k) (S : Finset F) (hcard : k ≤ S.card) :
    ∃ x ∈ S, p.eval x ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S h
    (hd.trans_le hcard))

/-- **BITE — distinct low-degree polynomials must visibly disagree.** If `p ≠ q` (both
`natDegree < k`), then on ANY size-≥k set some point separates them. This is the reject
direction: a prover claiming a SECOND low-degree polynomial for the same ≥k agreements is
caught at some query point. -/
theorem lowDegree_distinct_must_disagree {k : ℕ} (p q : Polynomial F) (hne : p ≠ q)
    (hp : p.natDegree < k) (hq : q.natDegree < k) (S : Finset F) (hcard : k ≤ S.card) :
    ∃ x ∈ S, p.eval x ≠ q.eval x := by
  by_contra h
  push Not at h
  exact hne (lowDegree_agree_forces_eq p q S hp hq hcard h)

/-! ## §2 — Specialization at the DEPLOYED field (`BabyBear = ZMod 2013265921`). -/

/-- **Interpolation uniqueness over BabyBear** — the deployed prover's field
(`p = 2³¹ − 2²⁷ + 1 = 2013265921`). Pure instantiation of `lowDegree_agree_forces_eq`
(BabyBear is a field, hence an integral domain). -/
theorem lowDegree_agree_forces_eq_babyBear {k : ℕ} (p q : Polynomial BabyBear)
    (S : Finset BabyBear)
    (hp : p.natDegree < k) (hq : q.natDegree < k) (hcard : k ≤ S.card)
    (hagree : ∀ x ∈ S, p.eval x = q.eval x) : p = q :=
  lowDegree_agree_forces_eq p q S hp hq hcard hagree

/-! ## §3 — FIRE: the theorem CONCLUDES on concrete deployed-field data. -/

/-- **FIRE.** `(X + 1)² = X² + 2X + 1` over BabyBear, derived VIA interpolation uniqueness
(not `ring`): both sides have `natDegree = 2 < 3`, and they agree at the 3 distinct points
`{0, 1, 2}` — so the theorem forces them equal as polynomials. -/
theorem lowDegree_uniqueness_fires :
    (X + C 1 : Polynomial BabyBear) ^ 2 = X ^ 2 + C 2 * X + C 1 := by
  refine lowDegree_agree_forces_eq_babyBear (k := 3) _ _ ({0, 1, 2} : Finset BabyBear)
    ?_ ?_ ?_ ?_
  · -- natDegree ((X + 1)²) = 2·1 < 3
    rw [natDegree_pow, natDegree_X_add_C]
    norm_num
  · -- natDegree (X² + 2X + 1) ≤ 2 < 3
    have h2 : (X ^ 2 + C 2 * X + C 1 : Polynomial BabyBear).natDegree ≤ 2 := by
      compute_degree
    omega
  · -- the 3 points are distinct in BabyBear
    decide
  · intro x _
    simp only [eval_pow, eval_add, eval_mul, eval_X, eval_C]
    ring

/-! ## §4 — Axiom hygiene: every theorem kernel-clean. -/

#assert_axioms lowDegree_agree_forces_eq
#assert_axioms lowDegree_roots_card_lt
#assert_axioms nonzero_lowDegree_somewhere_nonzero
#assert_axioms lowDegree_distinct_must_disagree
#assert_axioms lowDegree_agree_forces_eq_babyBear
#assert_axioms lowDegree_uniqueness_fires

end Dregg2.Circuit.LowDegreeUniqueness
