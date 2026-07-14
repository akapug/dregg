import Dregg2.Tactics
import Dregg2.Circuit.Poseidon2KeyedBridge
import Dregg2.Circuit.LightClientFusion

/-!
# `Dregg2.Circuit.S5Closure` — discharging the COMPUTATIONAL half of the LightClientFusion §5 residual.

This module is ADDITIVE: it edits nothing in `Poseidon2KeyedBridge`/`LightClientFusion`/
`CommitmentReduction`. It closes the part of the §5 residual that is a genuine Lean construction and
names — precisely, as typed obligations — the part that is not.

## What §5 carried, and what is discharged here

`LightClientFusion.deployed_fooling_advantage_negl` (§5) bounds the advantage of a **supplied**
`foolingRootEquivocator D xs xs'` — the finder is an INPUT. That leaves the computational half assuming
what it should construct: the map from an actual deployed fooling to a concrete
`CollisionFinder (poseidon2KeyedFamily D)`.

Here the finder is CONSTRUCTED from a concrete colliding pair and its refutation of the keyed floor is a
STANDALONE reduction:

  * `deployed_collision_refutes_domainSepCR` — a genuine collision of `D.hashAt` at ANY tag builds the
    fixed-pair finder, whose advantage is a POSITIVE CONSTANT (`collisionAdv_pos`), contradicting
    `DomainSeparatedCR D` (`not_negl_const_pos`). The finder is a real term of the fooling data, not a
    re-assumed input.
  * `deployed_unfoolable_of_domainSepCR` — the §5 headline at the deployed surface:
    `DomainSeparatedCR D ⟹ ¬ Foolable (dVerify R) (dProduced S kstep)`, resting on the keyed-CR floor.
    The ONLY carried hypothesis is `hextract` — the fooling→collision EXTRACTION — which is the §5
    residual reduced to its crispest typed form (a fooling yields a colliding pair). The finder,
    advantage, and floor-refutation are all built inside, not assumed.

Non-vacuity is EVALUATED (`foolingFinder_brokenDomainSep_wins`, `foolingFinder_brokenDomainSep_adv_pos`):
a concrete fooling (the constant-`0` broken sponge, distinct pair `([0],[1])`) yields a concretely
WINNING constructed finder of positive advantage, computed — not a laundered `True`.

## The precise remaining residuals (NAMED, not forced — see §6)

The composition does NOT reach a full-strength real-params discharge, for two independent reasons this
file proves or pins:

  * **R2 — the floor object is vacuous at real params.** `poseidon2KeyedFamily D` keys by
    `Key n := fun _ => D.Tag` — a FIXED finite tag space INDEPENDENT of the security parameter `n`. So a
    hardcoded-collision finder has an `n`-independent (constant) advantage; a real Poseidon2 into BabyBear
    has collisions by pigeonhole. Hence `DomainSeparatedCR D` FORCES `D.hashAt t` injective for every `t`
    (`domainSepCR_forces_injective`) and is outright FALSE at the BabyBear field bound
    (`domainSepCR_false_babyBear`). Its only satisfying witnesses are injective sponges — the same "false
    comfort" `HashFloorHonesty` flags for the old injective floor. A real-params floor needs a key space
    that GROWS with `n`; the domain-separation tag is a label, not a growing key.
  * **R1 — the fooling→collision extraction is unmodeled (carried as `hextract`).** A deployed `Foolable`
    yields an accepting-but-unpinned run that decodes-and-pins `pi` but FAILS `kstep`; it does NOT hand
    two distinct kernels colliding on one committed root. Moreover the deployed state commitment
    `S.commit = recStateCommit` is a NESTED TREE `cmb[ compress[ compressN(leaves), compress(CH s, CH d) ],
    RH k ]` over FOUR differently-typed primitives, not a single `D.hashAt t`. A `StateBreak` is therefore
    a four-way disjunction (`SpongeCollision compressN ∨ CompressCollision cmb ∨ CompressCollision compress
    ∨ CellCollision CH`) whose carriers (`ℤ×ℤ`, `CellId×Value`, `List ℤ`) are TYPE-INCOMPATIBLE with a
    `poseidon2KeyedFamily D` collision (a `List ℤ` pair) — only the `compressN`/`SpongeCollision` leg
    matches, and only after a presentation factoring each primitive through `D.sponge` at distinct
    injective-encoded tags that the tree does not carry.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`/
fresh `axiom`.
-/

namespace Dregg2.Circuit.S5Closure

open Dregg2.Circuit.HashFloorHonesty (CollisionFinder CollisionResistant collisionAdv)
open Dregg2.Circuit.Poseidon2KeyedBridge
  (DomainSeparatedSponge DomainSeparatedCR poseidon2KeyedFamily brokenDomainSep)
open Dregg2.Circuit.LightClientFusion (foolingRootEquivocator foolingRootEquivocator_wins_iff)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Exec (RecChainedState)
open Dregg2.Crypto.LightClientUC (Foolable)
open Dregg2.Crypto.ProbCrypto (winProb not_negl_const_pos)
open Dregg2.Crypto.ConcreteSecurity (Negl)

/-! ## §1 — the constructed finder and its POSITIVE advantage.

The finder is `foolingRootEquivocator` — the fixed-pair `CollisionFinder (poseidon2KeyedFamily D)` reused
from `LightClientFusion` (do not reinvent). Its win event at a tag is a genuine deployed collision
(`foolingRootEquivocator_wins_iff`), and — because the family key space `Key n = D.Tag` ignores `n` — its
advantage is CONSTANT in `n`. -/

/-- A `winProb` with at least one winning outcome over a nonempty finite space is POSITIVE. -/
theorem winProb_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (win : Ω → Bool) (a : Ω)
    (ha : win a = true) : 0 < winProb win := by
  unfold winProb
  apply div_pos
  · have hmem : a ∈ Finset.univ.filter (fun o => win o = true) := by
      simp [ha]
    exact_mod_cast Finset.card_pos.2 ⟨a, hmem⟩
  · exact_mod_cast (Fintype.card_pos (α := Ω))

/-- The finder's advantage against `poseidon2KeyedFamily D` is INDEPENDENT of the security parameter `n`
— because the family key space `Key n = D.Tag` and hash `H n` both ignore `n`. This is the fact that
makes a single hardcoded collision NON-negligible (a constant, not a `1/superpoly(n)`), and hence R2. -/
theorem collisionAdv_const (D : DomainSeparatedSponge) (xs xs' : List ℤ) :
    collisionAdv (poseidon2KeyedFamily D) (foolingRootEquivocator D xs xs')
      = fun _ => collisionAdv (poseidon2KeyedFamily D) (foolingRootEquivocator D xs xs') 0 := by
  funext n
  rfl

/-- Given a GENUINE collision of the deployed domain-separated sponge at SOME tag `t`, the constructed
fixed-pair finder wins at least at `t`, so its (n-independent) advantage is a POSITIVE constant. -/
theorem collisionAdv_pos (D : DomainSeparatedSponge) (xs xs' : List ℤ) (t : D.Tag)
    (hne : xs ≠ xs') (hcol : D.hashAt t xs = D.hashAt t xs') :
    0 < collisionAdv (poseidon2KeyedFamily D) (foolingRootEquivocator D xs xs') 0 := by
  have hwin : (foolingRootEquivocator D xs xs').wins 0 t = true :=
    (foolingRootEquivocator_wins_iff D xs xs' 0 t).2 ⟨hne, hcol⟩
  unfold collisionAdv
  exact @winProb_pos ((poseidon2KeyedFamily D).Key 0) ((poseidon2KeyedFamily D).keyFintype 0)
    ((poseidon2KeyedFamily D).keyNonempty 0)
    (fun k => (foolingRootEquivocator D xs xs').wins 0 k) t hwin

/-! ## §2 — THE STANDALONE REDUCTION: a constructed finder refutes the keyed floor. -/

/-- **THE CONSTRUCTED REFUTATION.** A genuine collision of `D.hashAt` at ANY tag gives the CONSTRUCTED
fixed-pair finder a non-negligible (positive-constant) advantage — refuting `DomainSeparatedCR D`. The
finder is `foolingRootEquivocator D xs xs'`, a real term of `(xs, xs')`; nothing is re-assumed. -/
theorem deployed_collision_refutes_domainSepCR (D : DomainSeparatedSponge)
    (hD : DomainSeparatedCR D) (xs xs' : List ℤ) (t : D.Tag)
    (hne : xs ≠ xs') (hcol : D.hashAt t xs = D.hashAt t xs') : False := by
  have hnegl : Negl (collisionAdv (poseidon2KeyedFamily D) (foolingRootEquivocator D xs xs')) :=
    hD (foolingRootEquivocator D xs xs')
  rw [collisionAdv_const D xs xs'] at hnegl
  exact not_negl_const_pos (collisionAdv_pos D xs xs' t hne hcol) hnegl

/-! ## §3 — THE §5 HEADLINE at the deployed surface (the map DISCHARGED modulo the named extraction).

`deployed_unfoolable_of_domainSepCR : DomainSeparatedCR D ⟹ ¬ Foolable (dVerify R) (dProduced S kstep)`.
The deployed unfoolability now RESTS on the keyed-CR floor `DomainSeparatedCR D`. The only carried
hypothesis is `hextract` — the fooling→colliding-pair extraction (R1, §6). Compare
`LightClientFusion.deployed_fooling_advantage_negl`, which carried a whole `CollisionFinder`: here the
finder, its advantage, and the floor-refutation are all CONSTRUCTED inside; only the raw collision
witness is carried. -/

/-- **THE §5 CLOSURE.** Under the deployed keyed collision-resistance floor `DomainSeparatedCR D`, and the
named fooling→collision extraction `hextract`, the deployed light client is UNFOOLABLE — no environment
fools `dVerify R` into accepting a non-`dProduced` state. The discharge routes any fooling through
`hextract` to a concrete colliding pair, CONSTRUCTS `foolingRootEquivocator` from it, and refutes the
floor via `deployed_collision_refutes_domainSepCR`. -/
theorem deployed_unfoolable_of_domainSepCR
    (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (R : Registry) (S : CommitSurface)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hextract : Foolable (Dregg2.Circuit.LightClientFusion.dVerify R)
        (Dregg2.Circuit.LightClientFusion.dProduced S kstep) →
      ∃ (t : D.Tag) (xs xs' : List ℤ), xs ≠ xs' ∧ D.hashAt t xs = D.hashAt t xs') :
    ¬ Foolable (Dregg2.Circuit.LightClientFusion.dVerify R)
        (Dregg2.Circuit.LightClientFusion.dProduced S kstep) := by
  intro hFool
  obtain ⟨t, xs, xs', hne, hcol⟩ := hextract hFool
  exact deployed_collision_refutes_domainSepCR D hD xs xs' t hne hcol

/-! ## §4 — NON-VACUITY, EVALUATED: a concrete fooling → a concrete winning constructed finder.

At the broken (constant-`0`) sponge, the distinct pair `([0], [1])` is a genuine collision, and the
CONSTRUCTED finder `foolingRootEquivocator brokenDomainSep [0] [1]` wins — COMPUTED, not assumed — with
positive advantage. So the construction is real: it produces an actually-winning finder on a concrete
input. (Consistent with `Poseidon2KeyedBridge.brokenDomainSep_not_CR`, independently.) -/

/-- **EVALUATED WIN.** The constructed finder wins on the broken sponge at the deployed tag — computed. -/
theorem foolingFinder_brokenDomainSep_wins :
    (foolingRootEquivocator brokenDomainSep ([0] : List ℤ) [1]).wins 0 () = true := by
  simp [CollisionFinder.wins, foolingRootEquivocator, poseidon2KeyedFamily, brokenDomainSep]

/-- **EVALUATED POSITIVE ADVANTAGE.** The constructed finder's advantage on the broken sponge is a
positive constant — a concrete, non-vacuous witness that the reduction produces a real winner. -/
theorem foolingFinder_brokenDomainSep_adv_pos :
    0 < collisionAdv (poseidon2KeyedFamily brokenDomainSep)
      (foolingRootEquivocator brokenDomainSep ([0] : List ℤ) [1]) 0 := by
  refine collisionAdv_pos brokenDomainSep [0] [1] () (by decide) ?_
  simp [Dregg2.Circuit.Poseidon2KeyedBridge.DomainSeparatedSponge.hashAt, brokenDomainSep]

/-! ## §5 — R2 EXPOSED: `DomainSeparatedCR D` forces injectivity and is FALSE at real params. -/

/-- **R2, part 1.** `DomainSeparatedCR D` forbids EVERY collision of `D.hashAt` at every tag — i.e. it
forces `D.hashAt t` INJECTIVE for all `t`. The keyed floor collapses to injectivity because the key does
not grow with `n`. -/
theorem domainSepCR_forces_injective (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (t : D.Tag) : Function.Injective (D.hashAt t) := by
  intro xs xs' hcol
  by_contra hne
  exact deployed_collision_refutes_domainSepCR D hD xs xs' t hne hcol

/-- **R2, part 2.** If the deployed sponge lands in a finite set of field elements (every real Poseidon2
into BabyBear), `D.hashAt t` is non-injective (pigeonhole), so `DomainSeparatedCR D` is FALSE — the same
disease `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` proves for the injective floor. -/
theorem domainSepCR_false_of_finite_range (D : DomainSeparatedSponge) (t : D.Tag)
    (hfin : (Set.range (D.hashAt t)).Finite) : ¬ DomainSeparatedCR D := fun hD =>
  HashFloorHonesty.not_injective_of_finite_range (D.hashAt t) hfin
    (domainSepCR_forces_injective D hD t)

/-- **R2, deployed form.** At the real BabyBear field bound (`0 ≤ · < p`), every deployed sponge refutes
`DomainSeparatedCR` — the floor object is unsatisfiable at real params; a real-params floor needs a key
space growing with the security parameter. -/
theorem domainSepCR_false_babyBear (D : DomainSeparatedSponge) (t : D.Tag)
    (hb : ∀ xs, 0 ≤ D.hashAt t xs ∧ D.hashAt t xs < (2013265921 : ℤ)) :
    ¬ DomainSeparatedCR D :=
  domainSepCR_false_of_finite_range D t
    (HashFloorHonesty.finite_range_of_field_bound (D.hashAt t) _ hb)

/-! ## §6 — axiom hygiene. -/

#assert_axioms winProb_pos
#assert_axioms collisionAdv_const
#assert_axioms collisionAdv_pos
#assert_axioms deployed_collision_refutes_domainSepCR
#assert_axioms deployed_unfoolable_of_domainSepCR
#assert_axioms foolingFinder_brokenDomainSep_wins
#assert_axioms foolingFinder_brokenDomainSep_adv_pos
#assert_axioms domainSepCR_forces_injective
#assert_axioms domainSepCR_false_of_finite_range
#assert_axioms domainSepCR_false_babyBear

end Dregg2.Circuit.S5Closure
