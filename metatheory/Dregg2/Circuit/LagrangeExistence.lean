/-
# Lagrange EXISTENCE — the constructive companion to `lowDegree_agree_forces_eq`.

`LowDegreeUniqueness.lean` proved the AT-MOST-ONE half: two low-degree polynomials agreeing
on ≥ k points are equal. This file proves the AT-LEAST-ONE half the FriExtract decoder needs
to actually PRODUCE a polynomial from queried values:

  **`interpolant_exists`** — over a field, given a nonempty Finset `S` of (distinct,
  Finset-enforced) nodes and ANY value function `v : F → F`, there EXISTS a polynomial `p`
  with `p.natDegree < S.card` matching `v` on all of `S`. Witness: Mathlib's
  `Lagrange.interpolate S id v` (nodal map `id`, injective on any set).

  **`interpolant_unique`** — existence + `lowDegree_agree_forces_eq` = EXISTS-AND-UNIQUE
  (`∃!`): exactly one polynomial of `natDegree < S.card` takes the prescribed values.
  Uniqueness gives well-definedness of the decoded polynomial; existence gives the witness.

Specialized at the DEPLOYED field (`BabyBear = ZMod 2013265921`):
`interpolant_exists_babyBear`, `interpolant_unique_babyBear`.

FIRE (hypotheses genuinely discharged on concrete deployed-field data):
  * `lagrange_fire_witness` — the ACTUAL `Lagrange.interpolate` of the values `x² + 1` at
    the 3 distinct BabyBear nodes `{0, 1, 2}` IS the polynomial `X² + 1` (the constructed
    witness is computed and pinned, not merely asserted to exist).
  * `lagrange_fire_evals` — that constructed interpolant evaluates correctly at every node.
  * `interpolant_unique_fires` — the `∃!` statement instantiated and discharged at the same
    concrete data (nonemptiness and node-distinctness discharged by `decide`).
  * `lagrange_fire_pins` — the uniqueness tooth on the same data: ANY polynomial of
    `natDegree < 3` matching those 3 values is FORCED to be `X² + 1`.

SCOPE (honest): this is pure interpolation existence/uniqueness — the witness-producing half
of unique decoding. The PROXIMITY half (that FRI acceptance certifies the queried function is
close to SOME low-degree polynomial) is the separate BBHR18 distortion analysis, not here.
-/
import Mathlib.LinearAlgebra.Lagrange
import Dregg2.Circuit.LowDegreeUniqueness
import Dregg2.Tactics

namespace Dregg2.Circuit.LagrangeExistence

open Polynomial
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.LowDegreeUniqueness

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## §1 — Existence of the interpolant over any field. -/

/-- The Lagrange interpolant at nodal map `id` has `natDegree < S.card` when `S` is nonempty
(`natDegree` truncates `⊥` to `0`, so the zero interpolant also lands below a positive card). -/
theorem natDegree_interpolate_lt (S : Finset F) (hS : S.Nonempty) (v : F → F) :
    (Lagrange.interpolate S id v).natDegree < S.card := by
  rcases eq_or_ne (Lagrange.interpolate S id v) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    exact hS.card_pos
  · rw [natDegree_lt_iff_degree_lt h0]
    exact Lagrange.degree_interpolate_lt v (Set.injOn_id _)

/-- **Existence of the interpolant.** For any nonempty node set `S` (distinctness is
Finset-enforced) and any value function `v`, SOME polynomial of `natDegree < S.card` takes
value `v x` at every `x ∈ S`. The witness is `Lagrange.interpolate S id v` — this is the
polynomial the FriExtract decoder actually PRODUCES from queried values. -/
theorem interpolant_exists (S : Finset F) (hS : S.Nonempty) (v : F → F) :
    ∃ p : Polynomial F, p.natDegree < S.card ∧ ∀ x ∈ S, p.eval x = v x :=
  ⟨Lagrange.interpolate S id v, natDegree_interpolate_lt S hS v,
    fun _x hx => Lagrange.eval_interpolate_at_node v (Set.injOn_id _) hx⟩

/-! ## §2 — Existence AND uniqueness (`∃!`). -/

/-- **Exists-and-unique interpolant.** Combining `interpolant_exists` with the uniqueness
brick `lowDegree_agree_forces_eq`: EXACTLY ONE polynomial of `natDegree < S.card` takes the
prescribed values on `S`. Existence gives the decoder its witness; uniqueness gives
well-definedness (no second decoding). -/
theorem interpolant_unique (S : Finset F) (hS : S.Nonempty) (v : F → F) :
    ∃! p : Polynomial F, p.natDegree < S.card ∧ ∀ x ∈ S, p.eval x = v x := by
  obtain ⟨p, hpd, hpe⟩ := interpolant_exists S hS v
  refine ⟨p, ⟨hpd, hpe⟩, ?_⟩
  rintro q ⟨hqd, hqe⟩
  exact lowDegree_agree_forces_eq q p S hqd hpd le_rfl
    fun x hx => (hqe x hx).trans (hpe x hx).symm

/-! ## §3 — Specialization at the DEPLOYED field (`BabyBear = ZMod 2013265921`). -/

/-- **Interpolant existence over BabyBear** — the deployed prover's field
(`p = 2³¹ − 2²⁷ + 1 = 2013265921`). Pure instantiation of `interpolant_exists`. -/
theorem interpolant_exists_babyBear (S : Finset BabyBear) (hS : S.Nonempty)
    (v : BabyBear → BabyBear) :
    ∃ p : Polynomial BabyBear, p.natDegree < S.card ∧ ∀ x ∈ S, p.eval x = v x :=
  interpolant_exists S hS v

/-- **Exists-and-unique interpolant over BabyBear.** -/
theorem interpolant_unique_babyBear (S : Finset BabyBear) (hS : S.Nonempty)
    (v : BabyBear → BabyBear) :
    ∃! p : Polynomial BabyBear, p.natDegree < S.card ∧ ∀ x ∈ S, p.eval x = v x :=
  interpolant_unique S hS v

/-! ## §4 — FIRE: the construction COMPUTES on concrete deployed-field data. -/

/-- **FIRE (witness pinned).** The actual `Lagrange.interpolate` of the concrete values
`x² + 1` at the 3 distinct BabyBear nodes `{0, 1, 2}` IS `X² + 1` — the existence witness is
identified, not just asserted. (Via `eq_interpolate_of_eval_eq`: `X² + 1` has degree `2 < 3`
and matches the values at every node.) -/
theorem lagrange_fire_witness :
    Lagrange.interpolate ({0, 1, 2} : Finset BabyBear) id (fun x => x ^ 2 + 1)
      = X ^ 2 + C 1 := by
  have hcard : ({0, 1, 2} : Finset BabyBear).card = 3 := by decide
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (Set.injOn_id _) ?_ ?_
  · rw [hcard, degree_X_pow_add_C (by norm_num : 0 < 2) (1 : BabyBear)]
    decide
  · intro x _
    simp

/-- **FIRE (evaluation checked).** The constructed interpolant really does evaluate to the
prescribed value at every node of the concrete node set. -/
theorem lagrange_fire_evals :
    ∀ x ∈ ({0, 1, 2} : Finset BabyBear),
      (Lagrange.interpolate ({0, 1, 2} : Finset BabyBear) id fun y => y ^ 2 + 1).eval x
        = x ^ 2 + 1 := by
  intro x _
  rw [lagrange_fire_witness]
  simp

/-- **FIRE (`∃!` discharged on concrete data).** The exists-and-unique statement holds at the
concrete BabyBear instance — nonemptiness genuinely discharged (`0 ∈ {0,1,2}`), so the
hypotheses of `interpolant_unique` are satisfiable, not vacuous. -/
theorem interpolant_unique_fires :
    ∃! p : Polynomial BabyBear,
      p.natDegree < ({0, 1, 2} : Finset BabyBear).card ∧
        ∀ x ∈ ({0, 1, 2} : Finset BabyBear), p.eval x = x ^ 2 + 1 :=
  interpolant_unique_babyBear _ ⟨0, Finset.mem_insert_self 0 _⟩ _

/-- **FIRE (uniqueness tooth).** ANY polynomial of `natDegree < 3` matching the values
`x² + 1` at the 3 concrete nodes is FORCED to be `X² + 1` — the decoded polynomial is
pinned by the data. -/
theorem lagrange_fire_pins (p : Polynomial BabyBear) (hpd : p.natDegree < 3)
    (hpe : ∀ x ∈ ({0, 1, 2} : Finset BabyBear), p.eval x = x ^ 2 + 1) :
    p = X ^ 2 + C 1 := by
  have hqd : (X ^ 2 + C 1 : Polynomial BabyBear).natDegree < 3 := by
    have h2 : (X ^ 2 + C 1 : Polynomial BabyBear).natDegree ≤ 2 := by
      compute_degree
    omega
  have hcard : (3 : ℕ) ≤ ({0, 1, 2} : Finset BabyBear).card := by decide
  refine lowDegree_agree_forces_eq p _ ({0, 1, 2} : Finset BabyBear) hpd hqd hcard ?_
  intro x hx
  rw [hpe x hx]
  simp

/-! ## §5 — Axiom hygiene: every theorem kernel-clean. -/

#assert_axioms natDegree_interpolate_lt
#assert_axioms interpolant_exists
#assert_axioms interpolant_unique
#assert_axioms interpolant_exists_babyBear
#assert_axioms interpolant_unique_babyBear
#assert_axioms lagrange_fire_witness
#assert_axioms lagrange_fire_evals
#assert_axioms interpolant_unique_fires
#assert_axioms lagrange_fire_pins

end Dregg2.Circuit.LagrangeExistence
