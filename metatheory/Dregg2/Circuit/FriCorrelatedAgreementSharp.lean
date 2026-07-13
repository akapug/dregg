import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.FriProximityGapWitness

/-!
# `WrapCorrelatedAgreementSharp` — the δ-PRESERVING (Johnson-radius) residual, REDUCED to the
BCIKS20 affine-line correlated-agreement primitive, and the primitive NAMED as a Lean `Prop`.

`FriProximityGapWitness.lean` pushed the Fisher/packing method to its exact ceiling:
`wrap_badChallengePoly_johnson` proves `BadChallengePoly friSetupWrapRate 112 42 26` — `L = 26` at
the Johnson OUTER radius `dOut = 112` but with `dIn = 42` (relative `21/32`), NOT the folded code's
own Johnson radius `dIn = 56` (relative `7/8`). The obstruction is arithmetic and sharp: the packing
quadratic `a² > n·M` (`a = 64 − dIn`, `n = 64`, `M = 7`) FAILS for `dIn ≥ 43` (`a ≤ 21`,
`a² ≤ 441 < 448`). So the packing radius is *dead* at `dIn = 56` (`a = 8`, `a² = 64 ≪ 448`):
farness degrades across the fold (`7/8 → 21/32`) rather than being δ-preserved (`7/8 → 7/8`).

That named residual is `WrapCorrelatedAgreementSharp L := BadChallengePoly friSetupWrapRate 112 56 L`
(`FriProximityGapWitness.lean §F`). This file does not fake it. It does two honest things.

## §1. The exact remaining primitive, NAMED (`CorrelatedAgreementLine`).

BCIKS20's *correlated agreement for an affine line* over a code `C'`: viewing the FRI fold
`Fold α f = E f + α·O f` as the affine line `{u + α·v}` (`u = E f`, `v = O f`) of functions on the
folded domain, if MORE than `L` challenges `α` fold `f` to within `dIn` of `C'`, then there is a
SINGLE common agreement — codewords `ge, go ∈ C'` and a set of fibers `S` with
`|S| ≥ |κ| − dIn` on which `E f = ge` and `O f = go` SIMULTANEOUSLY. The threshold `|κ| − dIn` is the
**δ-preserving** (relative `1 − δ`) agreement — the sharp BCIKS20 statement, beyond the packing reach.
`CorrelatedAgreementLineAt S dIn L agree` carries the agreement threshold as a parameter so the
δ-preserving version (`agree = |κ| − dIn`) and the two-point version (`agree = |κ| − 2·dIn`) share one
shape.

This primitive is NOT assumed anywhere in the deployed chain (which consumes
`wrap_friProximityGap_johnson`, a theorem). It is stated so the residual is a Lean `Prop`, not prose.

## §2. The REDUCTION (`sharp_of_correlatedAgreementLine`) — a THEOREM, no `sorry`.

`CorrelatedAgreementLine friSetupWrapRate 56 L → WrapCorrelatedAgreementSharp L`. The mechanism is
the deployed dimension-`2` collapse already proved in `FriProximityGapWitness.lean`: on the wrap
setup `C'` is the CONSTANTS, so the correlated-agreement codewords are `ge = const a`, `go = const b`,
and their common agreement set is EXACTLY `Φ⁻¹(a, b) = {y | E f y = a ∧ O f y = b}`. δ-preservation
forces `|Φ⁻¹(a,b)| ≥ 64 − 56 = 8`, but `far_fiber_card` / `wrap_fiber_le_seven` cap it at
`(128 − 112 − 1)/2 = 7` for a `112`-far word. `8 ≤ 7` is absurd, so the good set has `≤ L` elements —
and the BCIKS20 witness polynomial `∏_{α good}(X − C α)` (nonzero, degree `≤ L`) is exhibited exactly
as in `wrap_badChallengePoly_johnson`. This is where the sharp `7/8 → 7/8` δ-preservation lives: the
one place `far_fiber_card`'s `M = 7` *beats* the `δ = 7/8` agreement floor of `8`.

## §3. Non-vacuity / genuine-strengthening certificate (`correlatedAgreementLineAt_twoPoint`).

The primitive is not a black box: at `L = 1` its WEAK form (`agree = |κ| − 2·dIn`) is a THEOREM,
proved by the BBHR18 two-point reconstruction (the same Vandermonde solve behind
`fold_close_of_two_alpha`): two good challenges pin `E f = Ge`, `O f = Go` off the union of the two
disagreement sets, giving common agreement on `≥ |κ| − 2·dIn` fibers with `Ge, Go ∈ C'`. So the
`∃ ge go, agree ≤ …` SHAPE is inhabited and provable; the SOLE gap to the sharp statement is the
strengthening of the agreement floor from `|κ| − 2·dIn` (two-point) to `|κ| − dIn` (δ-preserving) —
which is precisely BCIKS20's correlated-agreement content, and precisely what is left open, named,
and NOT `sorry`'d.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `axiom`, no `sorry`.
-/

namespace Dregg2.Circuit.FriCorrelatedAgreementSharp

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriLdtJohnson
open Dregg2.Circuit.FriProximityGapListDecoding
open Dregg2.Circuit.FriProximityGapWitness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriDeployedInstance (friSetupWrapRate)
open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## §1. The named BCIKS20 affine-line correlated-agreement primitive. -/

/-- **BCIKS20 correlated agreement for the FRI affine line, at agreement floor `agree`.** If more
than `L` folding challenges `α` fold `f` to within `dIn` of the folded code `C'`, then a SINGLE pair
of folded codewords `ge, go ∈ C'` agrees with `(E f, O f)` on at least `agree` fibers SIMULTANEOUSLY.

The δ-preserving (sharp) instance is `agree = |κ| − dIn`; the two-point (unique-decoding) instance is
`agree = |κ| − 2·dIn` (`§3`). -/
def CorrelatedAgreementLineAt (S : FriSetup F ι κ) (dIn L agree : ℕ) : Prop :=
  ∀ {f : ι → F} (Good : Finset F),
    (∀ α ∈ Good, closeN S.C' dIn (Fold S.geom α f)) → L < Good.card →
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      agree ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card

/-- **The δ-PRESERVING correlated-agreement primitive** — the sharp BCIKS20 statement: the common
agreement set is of relative size `1 − δ` (`|κ| − dIn` fibers), matching the OUTER far-ness's relative
size. This is the exact content beyond the packing quadratic's `21/32` reach. -/
def CorrelatedAgreementLine (S : FriSetup F ι κ) (dIn L : ℕ) : Prop :=
  CorrelatedAgreementLineAt S dIn L (Fintype.card κ - dIn)

/-! ## §3 (stated first — the non-vacuity certificate). The two-point reconstruction gives the WEAK
agreement floor `|κ| − 2·dIn`, so the primitive's `∃ ge go, agree ≤ …` shape is inhabited. -/

/-- **Two good challenges reconstruct a common agreement set of `≥ |κ| − 2·dIn` fibers.** The BBHR18
Vandermonde solve (as in `fold_close_of_two_alpha`): off the union `T` of the two disagreement sets
(`|T| ≤ 2·dIn`), the fold equations `E f + αᵢ·O f = gᵢ` pin `E f = Ge`, `O f = Go`, with
`Ge, Go ∈ C'` the reconstructed folded codewords. So `Tᶜ` (of card `≥ |κ| − 2·dIn`) lies in the
common agreement set. -/
theorem correlatedAgreementLine_twoPoint (S : FriSetup F ι κ) {f : ι → F} {α₁ α₂ : F}
    (hα : α₁ ≠ α₂) {d : ℕ}
    (h1 : closeN S.C' d (Fold S.geom α₁ f)) (h2 : closeN S.C' d (Fold S.geom α₂ f)) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      Fintype.card κ - 2 * d ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card := by
  classical
  obtain ⟨g₁, hg₁, hc₁⟩ := h1
  obtain ⟨g₂, hg₂, hc₂⟩ := h2
  set G := S.geom with hG
  have hne : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hα
  set inv : F := (α₁ - α₂)⁻¹ with hinv
  set Go : κ → F := inv • (g₁ - g₂) with hGo
  set Ge : κ → F := inv • (α₁ • g₂ - α₂ • g₁) with hGe
  have hGoC : Go ∈ S.C' := S.C'.smul_mem _ (S.C'.sub_mem hg₁ hg₂)
  have hGeC : Ge ∈ S.C' :=
    S.C'.smul_mem _ (S.C'.sub_mem (S.C'.smul_mem _ hg₂) (S.C'.smul_mem _ hg₁))
  set T : Finset κ := disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂ with hT
  refine ⟨Ge, hGeC, Go, hGoC, ?_⟩
  -- `Tᶜ` lies in the common agreement set.
  have hkey : Tᶜ ⊆ Finset.univ.filter (fun y : κ => E G f y = Ge y ∧ O G f y = Go y) := by
    intro y hy
    rw [Finset.mem_compl, hT, Finset.mem_union, not_or] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have e1 : E G f y + α₁ * O G f y = g₁ y := by
      have h := hy1; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have e2 : E G f y + α₂ * O G f y = g₂ y := by
      have h := hy2; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have hGoy : Go y = inv * (g₁ y - g₂ y) := by
      simp only [hGo, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hGey : Ge y = inv * (α₁ * g₂ y - α₂ * g₁ y) := by
      simp only [hGe, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hGey, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination α₁ * e2 - α₂ * e1
    · rw [hGoy, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination e1 - e2
  -- `|T| ≤ 2d`, so `|Tᶜ| = |κ| − |T| ≥ |κ| − 2d`, and the agreement set is even bigger.
  have hTcard : T.card ≤ 2 * d := by
    rw [hT]
    calc (disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂).card
        ≤ (disagree (Fold G α₁ f) g₁).card + (disagree (Fold G α₂ f) g₂).card :=
          Finset.card_union_le _ _
      _ ≤ 2 * d := by omega
  have hcompl : Tᶜ.card = Fintype.card κ - T.card := by rw [Finset.card_compl]
  calc Fintype.card κ - 2 * d
      ≤ Tᶜ.card := by rw [hcompl]; omega
    _ ≤ _ := Finset.card_le_card hkey

/-- **The primitive is inhabited at `L = 1` with the WEAK (two-point) agreement floor.** This
certifies the `∃ ge go, agree ≤ …` shape is provable — the sole gap to the sharp `CorrelatedAgreementLine`
is the strengthening of the floor from `|κ| − 2·dIn` to `|κ| − dIn`, i.e. exactly δ-PRESERVATION. -/
theorem correlatedAgreementLineAt_twoPoint (S : FriSetup F ι κ) (dIn : ℕ) :
    CorrelatedAgreementLineAt S dIn 1 (Fintype.card κ - 2 * dIn) := by
  intro f Good hGood hcard
  obtain ⟨α₁, hα₁, α₂, hα₂, hne⟩ := Finset.one_lt_card.mp hcard
  exact correlatedAgreementLine_twoPoint S hne (hGood α₁ hα₁) (hGood α₂ hα₂)

/-! ## §2. The REDUCTION: the δ-preserving primitive discharges `WrapCorrelatedAgreementSharp`. -/

/-- **The good-challenge card bound at the SHARP inner radius, from correlated agreement.** Given the
δ-preserving line-correlated-agreement primitive at `dIn = 56`, a `112`-far word has at most `L`
folding challenges whose fold is `56`-close to the constants. The contradiction is the deployed
dimension-`2` collapse: correlated agreement would force `≥ 8` fibers onto a single point `(a, b)` of
`F²`, but `wrap_fiber_le_seven` caps that at `7`. -/
theorem wrap_good_challenge_card_le_sharp {f : Fin (2 ^ 7) → BabyBear} {L : ℕ}
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L)
    (hfar : farN friSetupWrapRate.C 112 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ L := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨ge, hge, go, hgo, hbig⟩ := hCA Good hGood hcon
  obtain ⟨a, rfl⟩ := mem_wrap_C'.mp hge
  obtain ⟨b, rfl⟩ := mem_wrap_C'.mp hgo
  have hle7 := wrap_fiber_le_seven hfar a b
  have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  -- `hbig : |κ| − 56 ≤ |Φ⁻¹(a,b)|`; beta-reduce the constants `(fun _ => a) y ↦ a`.
  simp only at hbig
  rw [hn] at hbig
  omega

/-- **THE REDUCTION — `WrapCorrelatedAgreementSharp L` from the BCIKS20 line primitive.**
`CorrelatedAgreementLine friSetupWrapRate 56 L → BadChallengePoly friSetupWrapRate 112 56 L`. For a
`112`-far `f` the good set has card `≤ L` (`wrap_good_challenge_card_le_sharp`), so the vanishing
polynomial `∏_{α good}(X − C α)` is the nonzero degree-`≤ L` witness whose roots contain every good
challenge — the δ-PRESERVING (`dIn = 56 = (7/8)·64`) proximity-gap witness, at the folded code's OWN
Johnson radius. No `sorry`: the SOLE hypothesis is the precisely-named correlated-agreement `Prop`. -/
theorem sharp_of_correlatedAgreementLine (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    WrapCorrelatedAgreementSharp L := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ L :=
    wrap_good_challenge_card_le_sharp hCA hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- **The δ-preserving proximity gap, from the primitive** — routed through the framework's own
reduction `friProximityGap_of_badChallengePoly`. `dIn = 56` is the folded code's Johnson radius
(relative `7/8`), so farness is PRESERVED across the fold (`7/8 → 7/8`), not degraded to the packing
method's `21/32`. -/
theorem wrap_friProximityGap_sharp (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    FriProximityGapChallenges friSetupWrapRate 112 56 L :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 112 56 L
    (sharp_of_correlatedAgreementLine L hCA)

/-- **The sharp witness FIRES on the concrete `112`-far `fSqWrap`** (conditional on the primitive):
at most `L` folding challenges fold it `56`-close to the constants, exhibited as the roots of an
actual nonzero degree-`≤ L` polynomial. Non-vacuous: `fSqWrap_far` supplies the hypothesis. -/
theorem wrap_sharp_witness_fires (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ L ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  sharp_of_correlatedAgreementLine L hCA fSqWrap_far

/-! ## §3b. THE δ-PRESERVING PRIMITIVE, PROVED (Guruswami–Sudan / correlated-agreement core).

`correlatedAgreementLineAt_twoPoint` gave the primitive only at the *weak* floor `|κ| − 2·dIn`
(vacuous at `dIn = 56`). Here the SHARP floor `|κ| − dIn` is PROVED for the deployed wrap setup —
the exact BCIKS20 correlated-agreement content — by the deployed dimension-`2` collapse, WITHOUT the
general Guruswami–Sudan interpolation machinery. The list size is loose (`|κ|² = 4096`, not the tight
linear-in-`n` BCIKS bound), but the RADIUS is sharp: `dIn = 56 = (7/8)·64`, δ-preserving.

**The argument (an ordered-pair / Fisher injection, dual to the packing bound).** Fix `f`. Suppose
NO constant point `(a,b) ∈ F²` is rich — every fiber `Φ⁻¹(a,b) = {y | E f y = a ∧ O f y = b}` has
`< 8` fibers. Then the good-challenge set injects into `κ × κ`, so `|Good| ≤ 64² = 4096`:

* Each good `α` folds `f` to a constant `c_α` on `≥ 8` fibers: `|S_α| ≥ 8`, `S_α = {y | E f y + α·O f y = c_α}`.
* Not all of `S_α` shares one `Φ`-value (else that value is an `≥ 8` rich point). So pick
  `y_α ≠ y'_α ∈ S_α` with `Φ y_α ≠ Φ y'_α`.
* Because `C'` is the CONSTANTS, `E f y_α + α·O f y_α = E f y'_α + α·O f y'_α` (both `= c_α`), so
  `Φ y_α ≠ Φ y'_α` forces `O f y_α ≠ O f y'_α` and PINS
  `α = (E f y'_α − E f y_α)/(O f y_α − O f y'_α)` — determined by the pair `(y_α, y'_α)` ALONE
  (the constant `c_α` cancels). Hence `α ↦ (y_α, y'_α)` is injective on `Good`.

This is where the constant folded code makes the general GS weighted-list-decoding collapse to a
finite injection — the same dimension-`2` lever that made `RSListBound` elementary. -/

set_option maxRecDepth 4000 in
/-- **THE δ-PRESERVING CORRELATED-AGREEMENT PRIMITIVE, PROVED at the deployed wrap setup.**
`CorrelatedAgreementLine friSetupWrapRate 56 4096`: for ANY `f`, if more than `4096` folding
challenges fold `f` to within `56 = (7/8)·64` of the constants, a SINGLE constant pair `(a,b)` agrees
with `(E f, O f)` on `≥ |κ| − 56 = 8` fibers simultaneously — the sharp `1 − δ` (δ-preserving) floor,
beyond the `|κ| − 2·dIn` two-point reach and beyond the packing method's `21/32` radius. No `sorry`,
no hypothesis: the sole caveat is the loose list size `4096` (vs. BCIKS's tight linear bound). -/
theorem wrap_correlatedAgreementLine :
    CorrelatedAgreementLine friSetupWrapRate 56 4096 := by
  classical
  intro f Good hclose hL
  set G := friSetupWrapRate.geom with hG
  -- Either some constant point is rich (`≥ 8` fibers) — the conclusion — or none is, and then
  -- the good set injects into `κ × κ`, contradicting `4096 < |Good|`.
  rcases em (∃ a b : BabyBear,
      8 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) => E G f y = a ∧ O G f y = b)).card)
    with hrich | hnorich
  · -- Rich point → the δ-preserving agreement pair.
    obtain ⟨a, b, hab⟩ := hrich
    refine ⟨(fun _ => a), mem_wrap_C'.mpr ⟨a, rfl⟩, (fun _ => b), mem_wrap_C'.mpr ⟨b, rfl⟩, ?_⟩
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    rw [hn]
    simpa using hab
  · -- No rich point: build the injection `Good ↪ κ × κ`.
    exfalso
    -- For each good `α`, a witness pair of fibers with equal fold but distinct `Φ`-value.
    have hwit : ∀ α ∈ Good, ∃ y y' : Fin (2 ^ 6),
        Fold G α f y = Fold G α f y' ∧ ¬(E G f y = E G f y' ∧ O G f y = O G f y') := by
      intro α hα
      obtain ⟨g, hgC, hgcard⟩ := hclose α hα
      obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
      set S := Finset.univ.filter (fun y : Fin (2 ^ 6) => Fold G α f y = c) with hS
      have hcompl : S = (disagree (Fold G α f) (fun _ => c))ᶜ := by
        ext y
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
          mem_disagree, not_not]
      have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
      have hcc : S.card
          = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => c)).card := by
        rw [hcompl, Finset.card_compl]
      have hScard : 8 ≤ S.card := by rw [hcc, hn]; omega
      have hSne : S.Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨y0, hy0⟩ := hSne
      have hy0S : Fold G α f y0 = c := by
        have h := hy0; rw [hS, Finset.mem_filter] at h; exact h.2
      by_cases hall : ∀ y ∈ S, (E G f y, O G f y) = (E G f y0, O G f y0)
      · -- All of `S` shares `Φ y0` → that constant point is rich, contradicting `hnorich`.
        exact absurd
          ⟨E G f y0, O G f y0,
            le_trans hScard (Finset.card_le_card (by
              intro y hy
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have h := hall y hy; rw [Prod.ext_iff] at h; exact h))⟩
          hnorich
      · push_neg at hall
        obtain ⟨y1, hy1S, hy1ne⟩ := hall
        have hy1 : Fold G α f y1 = c := by
          have h := hy1S; rw [hS, Finset.mem_filter] at h; exact h.2
        refine ⟨y0, y1, by rw [hy0S, hy1], ?_⟩
        rintro ⟨hE, hO⟩
        exact hy1ne (by rw [Prod.ext_iff]; exact ⟨hE.symm, hO.symm⟩)
    choose! yy yy' hpair using hwit
    -- The fold equation on the witness pair pins `α`: `α·(O y − O y') = E y' − E y`, denom ≠ 0.
    have hform : ∀ α ∈ Good, O G f (yy α) ≠ O G f (yy' α) ∧
        α * (O G f (yy α) - O G f (yy' α)) = E G f (yy' α) - E G f (yy α) := by
      intro α hα
      obtain ⟨hFold, hne⟩ := hpair α hα
      have heq : E G f (yy α) + α * O G f (yy α)
               = E G f (yy' α) + α * O G f (yy' α) := hFold
      have hmul : α * (O G f (yy α) - O G f (yy' α)) = E G f (yy' α) - E G f (yy α) := by
        linear_combination heq
      refine ⟨?_, hmul⟩
      intro hOeq
      apply hne
      have hz : (0 : BabyBear) = E G f (yy' α) - E G f (yy α) := by
        rw [← hmul, hOeq]; ring
      exact ⟨(sub_eq_zero.mp hz.symm).symm, hOeq⟩
    -- `α ↦ (yy α, yy' α)` is injective on `Good`.
    have hinj : Set.InjOn (fun α => (yy α, yy' α)) ↑Good := by
      intro α hα γ hγ heqp
      simp only [Prod.mk.injEq] at heqp
      obtain ⟨h1, h2⟩ := heqp
      obtain ⟨hαden, hαmul⟩ := hform α hα
      obtain ⟨hγden, hγmul⟩ := hform γ hγ
      rw [h1, h2] at hαmul hαden
      have hDne : O G f (yy γ) - O G f (yy' γ) ≠ 0 := sub_ne_zero.mpr hγden
      have hcancel : α * (O G f (yy γ) - O G f (yy' γ))
                   = γ * (O G f (yy γ) - O G f (yy' γ)) := by rw [hαmul, hγmul]
      exact mul_right_cancel₀ hDne hcancel
    -- Injection into `κ × κ` (card `4096`) contradicts `4096 < |Good|`.
    have hcardle : Good.card ≤ (Finset.univ : Finset (Fin (2 ^ 6) × Fin (2 ^ 6))).card :=
      Finset.card_le_card_of_injOn (fun α => (yy α, yy' α))
        (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    have hn : (Finset.univ : Finset (Fin (2 ^ 6) × Fin (2 ^ 6))).card = 4096 := by simp
    rw [hn] at hcardle
    omega

/-- **`WrapCorrelatedAgreementSharp 4096`, PROVED (no hypothesis).** The δ-preserving proximity-gap
witness at the folded code's OWN Johnson radius (`dIn = 56 = (7/8)·64`), discharged by feeding the
now-proved line primitive into the reduction. This is `BadChallengePoly friSetupWrapRate 112 56 4096`
as an unconditional theorem — the residual named in `FriProximityGapWitness.lean §F`, CLOSED. -/
theorem wrap_correlatedAgreement_sharp_proved : WrapCorrelatedAgreementSharp 4096 :=
  sharp_of_correlatedAgreementLine 4096 wrap_correlatedAgreementLine

/-- **The δ-PRESERVING FRI proximity gap, PROVED unconditionally.**
`FriProximityGapChallenges friSetupWrapRate 112 56 4096`: a `112`-far word has at most `4096` folding
challenges whose fold is `56`-close (relative `7/8`) to the constants — farness PRESERVED across the
fold (`7/8 → 7/8`), the sharp radius the Fisher/packing method (`wrap_friProximityGap_johnson`,
`21/32`) could not reach. No hypothesis remains. -/
theorem wrap_friProximityGap_sharp_proved :
    FriProximityGapChallenges friSetupWrapRate 112 56 4096 :=
  wrap_friProximityGap_sharp 4096 wrap_correlatedAgreementLine

/-- **The sharp gap FIRES on the concrete `112`-far `fSqWrap`, unconditionally**: at most `4096`
folding challenges fold it `56`-close to the constants, exhibited as the roots of an actual nonzero
polynomial of degree `≤ 4096`. Non-vacuous (`fSqWrap_far` supplies the far hypothesis), no
correlated-agreement hypothesis assumed. -/
theorem wrap_sharp_witness_fires_proved :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ 4096 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  wrap_correlatedAgreement_sharp_proved fSqWrap_far

/-! ## §4. Axiom hygiene. -/

#assert_axioms correlatedAgreementLine_twoPoint
#assert_axioms correlatedAgreementLineAt_twoPoint
#assert_axioms wrap_good_challenge_card_le_sharp
#assert_axioms sharp_of_correlatedAgreementLine
#assert_axioms wrap_friProximityGap_sharp
#assert_axioms wrap_sharp_witness_fires
#assert_axioms wrap_correlatedAgreementLine
#assert_axioms wrap_correlatedAgreement_sharp_proved
#assert_axioms wrap_friProximityGap_sharp_proved
#assert_axioms wrap_sharp_witness_fires_proved

end Dregg2.Circuit.FriCorrelatedAgreementSharp
