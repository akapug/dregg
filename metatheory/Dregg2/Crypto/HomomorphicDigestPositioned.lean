/-
# `Dregg2.Crypto.HomomorphicDigestPositioned` — the position-indexed encoding: `SumInjective` DISCHARGED

`HomomorphicDigest` proves binding-under-MSIS for the SIS digest `digest A encode S = A (∑ i ∈ S,
encode i)` — but CARRIES `SumInjective encode` (distinct histories ⇒ distinct encode sums) as a
hypothesis, with teeth showing it is load-bearing. This file makes it STRUCTURAL: pick the
position-indexed message module `ι →₀ R` and

    positionEncode val i  :=  Finsupp.single i (val i)        (each `val i ≠ 0`)

so turn `i` writes its value into its OWN coordinate. Then `∑ i ∈ S, positionEncode val i` is the
finitely-supported function equal to `val i` on `S` and `0` elsewhere — the sum REMEMBERS the
history as its support (`positionEncode_sum_support : (∑ …).support = S`), and sum-injectivity is a
THEOREM (`positionIndexed_sumInjective`), not an assumption. The support argument is real: `S` is
recovered from the sum by literally taking `Finsupp.support`, which needs every `val i ≠ 0` — and
the teeth (`val_nonzero_load_bearing`) show that condition is itself load-bearing: one zero value
makes its index invisible, so `{i}` and `∅` collide and sum-injectivity FAILS.

The payoff is `digest_binds_positionIndexed` (+ the bounded-capacity variant): binding for the
position-indexed digest whose ONLY cryptographic hypothesis is `MSISHard` — the `SumInjective` leg
of `digest_binds_under_msis` is discharged by construction. The shortness leg is fully connected
too: `ShortNorm (ι →₀ R)` is instantiated as the coordinate ∞-norm (`Finset.sup` of coordinate
norms over the support), under which `nrm (positionEncode val i) = nrm (val i)` exactly, so the
per-turn shortness bound is a bound on the VALUES alone.

## Honest scope

`MSISHard` remains the named floor, with all the caveats documented on it in `Lattice.lean` (it is
an existence-refutation, vacuous at compressing deployed parameters — see `CryptoFloorTeeth`).
Nothing here upgrades that; what this file removes is the OTHER hypothesis. The construction is
also parameter-honest about capacity: `ι →₀ R` grows with the history (one coordinate per turn), so
a deployed instantiation fixes `ι` finite and `A`'s domain accordingly — the bounded-capacity
corollary (`digest_binds_bounded_positionIndexed`) is the shape that matches.

Sorry-free; `#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `native_decide`.
-/
import Dregg2.Crypto.HomomorphicDigest
import Mathlib.Data.Finsupp.Single
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul

namespace Dregg2.Crypto.HomomorphicDigestPositioned

set_option linter.unusedSectionVars false

open Dregg2.Crypto.Lattice Dregg2.Crypto.HomomorphicDigest

variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [AddCommGroup R]

/-! ## §1 — the encoding, and the support argument that makes it sum-injective. -/

/-- The position-indexed encoding: turn `i` writes its value into its OWN coordinate of `ι →₀ R`.
Distinct turns occupy disjoint coordinates, so their contributions can never cancel or merge —
this is what turns `SumInjective` from an assumption into a theorem. -/
noncomputable def positionEncode (val : ι → R) : ι → (ι →₀ R) := fun i => Finsupp.single i (val i)

/-- The encode sum, read at a coordinate: `val j` if `j` is in the history, `0` otherwise. -/
theorem positionEncode_sum_apply (val : ι → R) (S : Finset ι) (j : ι) :
    (∑ i ∈ S, positionEncode val i) j = if j ∈ S then val j else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [positionEncode, Finsupp.single_apply]
  exact Finset.sum_ite_eq' S j fun i => val i

/-- Membership is readable off the sum: `j ∈ S` iff the sum is nonzero at coordinate `j`.
This is where `val j ≠ 0` is spent. -/
theorem mem_iff_apply_ne_zero {val : ι → R} (hval : ∀ i, val i ≠ 0) (S : Finset ι) (j : ι) :
    j ∈ S ↔ (∑ i ∈ S, positionEncode val i) j ≠ 0 := by
  rw [positionEncode_sum_apply]
  by_cases hj : j ∈ S
  · simp [hj, hval j]
  · simp [hj]

/-- **THE MECHANISM.** The encode sum carries the history as its `support`: the history is
RECOVERED from the sum by a projection, so distinct histories cannot share a sum. -/
theorem positionEncode_sum_support {val : ι → R} (hval : ∀ i, val i ≠ 0) (S : Finset ι) :
    (∑ i ∈ S, positionEncode val i).support = S := by
  ext j
  rw [Finsupp.mem_support_iff]
  exact (mem_iff_apply_ne_zero hval S j).symm

/-- **THE STRUCTURAL DISCHARGE.** For the position-indexed encoding with nonzero values,
`SumInjective` is a theorem: equal sums have equal supports, and the support IS the history. -/
theorem positionIndexed_sumInjective {val : ι → R} (hval : ∀ i, val i ≠ 0) :
    SumInjective (positionEncode val) := fun S T hsum => by
  rw [← positionEncode_sum_support hval S, ← positionEncode_sum_support hval T, hsum]

/-! ## §2 — TEETH: `val i ≠ 0` is load-bearing, not decorative. -/

/-- **PROVE-THE-CONDITION-NECESSARY.** If some `val i = 0`, sum-injectivity FAILS: index `i` is
invisible (its single is `0`), so the distinct histories `{i}` and `∅` have the same encode sum. -/
theorem val_nonzero_load_bearing {val : ι → R} (i : ι) (hzero : val i = 0) :
    ¬ SumInjective (positionEncode val) := by
  intro hsi
  have hcollide : (∑ j ∈ ({i} : Finset ι), positionEncode val j)
      = ∑ j ∈ (∅ : Finset ι), positionEncode val j := by
    simp [positionEncode, hzero]
  exact Finset.singleton_ne_empty i (hsi {i} ∅ hcollide)

/-! ## §3 — the norm leg: `ShortNorm (ι →₀ R)` as the coordinate ∞-norm. -/

/-- The coordinate ∞-norm on the position-indexed module: the largest coordinate norm
(`Finset.sup` over the support; off-support coordinates are `0`, of norm `0`). -/
instance instShortNormFinsupp [ShortNorm R] : ShortNorm (ι →₀ R) where
  nrm f := f.support.sup fun i => nrm (f i)
  nrm_zero := by simp
  nrm_neg a := by
    rw [Finsupp.support_neg]
    exact Finset.sup_congr rfl fun i _ => by rw [Finsupp.neg_apply, nrm_neg]
  nrm_add_le a b := by
    refine Finset.sup_le fun i _ => ?_
    rw [Finsupp.add_apply]
    refine le_trans (nrm_add_le _ _) (Nat.add_le_add ?_ ?_)
    · by_cases h : a i = 0
      · rw [h, nrm_zero]; exact Nat.zero_le _
      · exact Finset.le_sup (f := fun j => nrm (a j)) (Finsupp.mem_support_iff.mpr h)
    · by_cases h : b i = 0
      · rw [h, nrm_zero]; exact Nat.zero_le _
      · exact Finset.le_sup (f := fun j => nrm (b j)) (Finsupp.mem_support_iff.mpr h)

/-- The instance's norm, unfolded (for calculation). -/
theorem nrm_finsupp_def [ShortNorm R] (f : ι →₀ R) :
    nrm f = f.support.sup fun i => nrm (f i) := rfl

/-- Under the coordinate ∞-norm, a position-indexed encoding is EXACTLY as short as its value. -/
theorem nrm_positionEncode [ShortNorm R] (val : ι → R) (i : ι) :
    nrm (positionEncode val i) = nrm (val i) := by
  simp only [positionEncode, nrm_finsupp_def]
  by_cases h : val i = 0
  · rw [h, Finsupp.single_zero, nrm_zero]
    simp
  · rw [Finsupp.support_single i h, Finset.sup_singleton, Finsupp.single_eq_same]

/-- The shortness side-condition of the digest theorems, reduced to a bound on the VALUES. -/
theorem positionEncode_isShort [ShortNorm R] {val : ι → R} {β₀ : ℕ}
    (hβ : ∀ i, nrm (val i) ≤ β₀) (i : ι) : IsShort β₀ (positionEncode val i) := by
  show nrm (positionEncode val i) ≤ β₀
  rw [nrm_positionEncode]
  exact hβ i

/-! ## §4 — the payoff: binding whose only cryptographic hypothesis is the MSIS floor. -/

variable {Rq : Type*} [CommRing Rq] [Module Rq R]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **BINDING, `SumInjective` DISCHARGED.** For the position-indexed encoding, two histories with
the same digest are the same history — under `MSISHard` alone. The hypotheses left are about the
VALUES (`val i ≠ 0`, `nrm (val i) ≤ β₀`) and the floor; the sum-injectivity leg of
`digest_binds_under_msis` is supplied by `positionIndexed_sumInjective`, not assumed.
(`MSISHard`'s own deployment caveats are documented in `Lattice.lean` and unchanged here.) -/
theorem digest_binds_positionIndexed [ShortNorm R]
    (A : (ι →₀ R) →ₗ[Rq] N) (val : ι → R) (β₀ : ℕ)
    (hval : ∀ i, val i ≠ 0) (hβ : ∀ i, nrm (val i) ≤ β₀)
    {S T : Finset ι} (hard : MSISHard A ((S.card + T.card) * β₀))
    (hcol : digest A (positionEncode val) S = digest A (positionEncode val) T) :
    S = T :=
  digest_binds_under_msis A (positionEncode val) β₀
    (positionEncode_isShort hβ) (positionIndexed_sumInjective hval) hard hcol

/-- **BOUNDED-CAPACITY BINDING, `SumInjective` DISCHARGED.** One `MSISHard A (2·Nmax·β₀)` floor
binds every history of at most `Nmax` turns — the bounded-scan-state shape, now with no
sum-injectivity assumption. -/
theorem digest_binds_bounded_positionIndexed [ShortNorm R]
    (A : (ι →₀ R) →ₗ[Rq] N) (val : ι → R) (β₀ : ℕ)
    (hval : ∀ i, val i ≠ 0) (hβ : ∀ i, nrm (val i) ≤ β₀)
    {Nmax : ℕ} (hard : MSISHard A (2 * Nmax * β₀))
    {S T : Finset ι} (hS : S.card ≤ Nmax) (hT : T.card ≤ Nmax)
    (hcol : digest A (positionEncode val) S = digest A (positionEncode val) T) :
    S = T :=
  digest_binds_bounded A (positionEncode val) β₀
    (positionEncode_isShort hβ) (positionIndexed_sumInjective hval) hard hS hT hcol

/-! ## §5 — non-vacuity: a concrete instantiation, both directions. -/

/-- Concrete witness (non-vacuous): unit values in `ℤ`, positions `ℕ` — sum-injective. -/
theorem demo_unitVals_sumInjective : SumInjective (positionEncode fun _ : ℕ => (1 : ℤ)) :=
  positionIndexed_sumInjective fun _ => one_ne_zero

/-- Concrete counter-witness: all-zero values — sum-injectivity genuinely fails. -/
theorem demo_zeroVals_not_sumInjective : ¬ SumInjective (positionEncode fun _ : ℕ => (0 : ℤ)) :=
  val_nonzero_load_bearing 0 rfl

#assert_axioms positionEncode_sum_apply
#assert_axioms mem_iff_apply_ne_zero
#assert_axioms positionEncode_sum_support
#assert_axioms positionIndexed_sumInjective
#assert_axioms val_nonzero_load_bearing
#assert_axioms nrm_positionEncode
#assert_axioms positionEncode_isShort
#assert_axioms digest_binds_positionIndexed
#assert_axioms digest_binds_bounded_positionIndexed
#assert_axioms demo_unitVals_sumInjective
#assert_axioms demo_zeroVals_not_sumInjective

end Dregg2.Crypto.HomomorphicDigestPositioned
