/-
# `Dregg2.Crypto.Smudging` — the noise-flooding (smudging) lemma: wide noise hides a bounded shift.

This is the load-bearing core of Hermine's KEY-HIDING property — the one leg that turns "the algebra is
correct and unforgeable" into "signing is SAFE." A Raccoon/Hermine signature is `z = y + c·s`; over a
lattice `y` and `c·s` are both short, so naively `z`'s distribution DEPENDS on the secret `s` and leaks
it. Noise-flooding fixes this: sample `y` from a WIDE distribution, so wide that shifting it by the
bounded `c·s` barely changes it — the shift is "smudged out," and `z` becomes (statistically) independent
of `s`.

We formalize this with the total-variation (statistical) distance, over exact rationals, with uniform
noise — a genuine, complete key-hiding argument. (Raccoon uses discrete-Gaussian noise + a Rényi-
divergence bound for tighter parameters; that is the harder formalization and the tightening, noted here.
The uniform+TV version below is itself a sound noise-flooding technique.)

**The smudging lemma** (`smudge_bound`): if the shifted noise support differs from the original in at
most `B` elements, the statistical distance between the two is `≤ B/M` — small exactly when the noise
support `M` dwarfs the shift budget `B`. That `B/M` is the leakage; noise-flooding drives it negligible.
-/
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Int.Interval

namespace Dregg2.Crypto.Smudging

variable {α : Type*} [DecidableEq α]

/-- The uniform distribution over a finite set `S` as an exact-rational mass function. -/
noncomputable def unif (S : Finset α) : α → ℚ := fun x => if x ∈ S then (S.card : ℚ)⁻¹ else 0

/-- Total-variation (statistical) distance between two mass functions over a support `s`. -/
def statDist (s : Finset α) (p q : α → ℚ) : ℚ := (∑ x ∈ s, |p x - q x|) / 2

/-- Per-element: over sets `S`, `T` of equal size `M`, the pointwise absolute difference of the two
uniforms is `M⁻¹` on the symmetric difference and `0` elsewhere. -/
theorem abs_diff_unif {S T : Finset α} (hcard : S.card = T.card) (x : α) :
    |unif S x - unif T x| = if x ∈ (S \ T) ∪ (T \ S) then (S.card : ℚ)⁻¹ else 0 := by
  have hnn : (0 : ℚ) ≤ (T.card : ℚ)⁻¹ := by positivity
  simp only [unif, hcard]
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;>
    simp [hS, hT, Finset.mem_union, Finset.mem_sdiff, abs_of_nonneg hnn]

/-- **The smudging lemma (finite-set form).** For uniforms over equal-size sets `S`, `T` (`M > 0`), the
statistical distance is `|S \ T| / M`. (When `|S| = |T|`, `|S \ T| = |T \ S|`, so the symmetric
difference contributes `2|S \ T|`, halved by the `/2` in `statDist`.) -/
theorem statDist_unif_eq {S T : Finset α} (hcard : S.card = T.card) (hpos : 0 < S.card) :
    statDist (S ∪ T) (unif S) (unif T) = (S \ T).card / (S.card : ℚ) := by
  have hMne : (S.card : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  -- |S\T| = |T\S|
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at h2
  have hsdiff : (S \ T).card = (T \ S).card := by omega
  -- the symmetric-difference set sits inside S ∪ T
  have hDsub : (S \ T) ∪ (T \ S) ⊆ S ∪ T := by
    intro x hx; simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢; tauto
  unfold statDist
  rw [Finset.sum_congr rfl (fun x _ => abs_diff_unif hcard x)]
  -- ∑ over S∪T of (if x ∈ D then M⁻¹ else 0)  =  ∑ over the filtered set of M⁻¹
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hDsub,
      Finset.sum_const, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  rw [hsdiff, nsmul_eq_mul]
  -- ((T\S).card + (T\S).card) • M⁻¹ / 2 = (T\S).card / M  (and (S\T).card = (T\S).card)
  rw [← hsdiff]
  push_cast
  field_simp
  ring

/-- **Leakage is bounded by `B/M`.** If the shifted set differs from the original in at most `B`
elements (`(S \ T).card ≤ B`), the statistical distance is `≤ B / M` — the noise-flooding bound: make
the noise support `M` dwarf the shift budget `B` and the leakage is negligible. -/
theorem smudge_bound {S T : Finset α} (B : ℕ) (hcard : S.card = T.card) (hpos : 0 < S.card)
    (hB : (S \ T).card ≤ B) :
    statDist (S ∪ T) (unif S) (unif T) ≤ (B : ℚ) / (S.card : ℚ) := by
  rw [statDist_unif_eq hcard hpos]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hB) (by positivity)

/-- **Translation form.** A shift `σ : α → α` injective on the ambient type (e.g. `y ↦ y + Δ` over `ℤ`)
sends the uniform over `S` to the uniform over `S.image σ`, and the smudging distance is
`|S \ S.image σ| / M`. This is the interface the signature-hiding argument uses. -/
theorem statDist_unif_image {S : Finset α} (σ : α → α) (hσ : Function.Injective σ)
    (hpos : 0 < S.card) :
    statDist (S ∪ S.image σ) (unif S) (unif (S.image σ))
      = (S \ S.image σ).card / (S.card : ℚ) := by
  apply statDist_unif_eq _ hpos
  rw [Finset.card_image_of_injective S hσ]

/-- Concrete non-vacuous instance: shift the uniform on `{0, …, 9} ⊂ ℤ` by `+1`; the supports
overlap in 9 of 10 points, so the statistical distance is exactly `1/10`. -/
theorem smudge_example :
    statDist ((Finset.Ico (0:ℤ) 10) ∪ ((Finset.Ico (0:ℤ) 10).image (· + 1)))
      (unif (Finset.Ico (0:ℤ) 10)) (unif ((Finset.Ico (0:ℤ) 10).image (· + 1)))
      = 1 / 10 := by
  have hinj : Function.Injective (fun y : ℤ => y + 1) := fun a b h => by simpa using h
  rw [statDist_unif_image _ hinj (by decide)]
  norm_num [show ((Finset.Ico (0:ℤ) 10) \ ((Finset.Ico (0:ℤ) 10).image (· + 1))).card = 1
              from by decide,
            show (Finset.Ico (0:ℤ) 10).card = 10 from by decide]

#assert_axioms abs_diff_unif
#assert_axioms statDist_unif_eq
#assert_axioms smudge_bound
#assert_axioms statDist_unif_image
#assert_axioms smudge_example

end Dregg2.Crypto.Smudging
