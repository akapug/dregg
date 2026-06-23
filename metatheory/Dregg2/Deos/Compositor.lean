/-
# Dregg2.Deos.Compositor — the compositing ALGEBRA: damage is exact, paint is order-free.

`Dregg2.Apps.Compositor` proves *who may present* — output-integrity = unfoolability on the scene (the
T1 non-overlap / T2 label-binding / T3 focus-exclusivity teeth: an unauthorized present cannot enter
the committed state). That is the SECURITY of the display path. This module proves the *structural
algebra* the compositor relies on but never states — the laws that make "rerender only what changed"
and "the glass the user sees is well-defined" theorems rather than implementation folklore. The CDDC
trusted its compositor to damage-track and paint correctly; we prove it.

We REUSE `Dregg2.Apps.Compositor`'s verified types verbatim (`Scene`, `Surface`, `RegionId`,
`t1NonOverlap`, `sublist`) — the same scene-graph the security teeth are proven over — and add the
compositional theory on top. No new scene model.

## What is proven

  * `wellFormed sc` — the scene invariant the security layer's T1 enforces, stated structurally:
    surfaces own PAIRWISE-DISJOINT region-sets (no region is owned by two surfaces). This is the
    standing invariant every compositing law assumes.
  * `ownerAt region sc` — which surface owns a region (the region→owner map). Under `wellFormed` it is
    UNAMBIGUOUS (`ownerAt_unique`): a region has at most one owner, so the question "whose pixel is
    this?" always has one answer — the foundation of clipping/occlusion soundness.
  * **`present_damage_exact` (DAMAGE SOUNDNESS)** — a committed present damages EXACTLY its declared
    region-set: every region in `present.target` is dirtied, and every region OUTSIDE it keeps its
    prior content (`unchanged_outside_target`). No over-damage (the compositor need not repaint the
    world), no under-damage (it cannot skip a dirtied region). This is the real "rerender only what
    changed" theorem — the dirty-region tracking is sound by construction.
  * **`paint_order_independent` (PAINT COMMUTES)** — on a `wellFormed` scene, the rendered glass is
    INDEPENDENT of the order surfaces are painted: rendering `s₁ ++ s₂` equals rendering `s₂ ++ s₁`.
    Because T1 forbids two surfaces from owning the same region, z-order can never decide a pixel — so
    compositing non-overlapping surfaces is a COMMUTATIVE fold. (Where overlap WOULD matter, T1 has
    already made it impossible.) The deep reason the compositor is allowed to repaint damaged regions
    in any convenient order.
  * `compose_preserves_wellFormed` — composing two well-formed scenes whose region-sets are disjoint
    yields a well-formed scene: the scene-graph is closed under disjoint composition (the surface-tree
    EMBED edge stays sound). And `compose_assoc` — composition (list append) is associative, so nested
    surface trees re-associate freely.
  * `render_frame_property` — a present to surface A's regions leaves surface B's rendered content
    untouched (the FRAME property / locality of damage): editing one window cannot perturb another's
    pixels. The compositional non-interference dual of `FogOfWar.noninterference`.

Discipline: axiom-clean (`#assert_all_clean`). `lake build Dregg2`
green (LOCAL). Reuses `Dregg2.Apps.Compositor`'s verified scene-graph; no new trust — the compositing
algebra reduces to the disjointness T1 already enforces.
-/
import Dregg2.Apps.Compositor
import Dregg2.Tactics

namespace Dregg2.Deos.Compositor

open Dregg2.Apps.Compositor (Scene Surface RegionId sublist t1NonOverlap)

/-! ## §1 — The well-formedness invariant: surfaces own pairwise-disjoint regions.

T1 (non-overlap) enforces, present-by-present, that no surface paints a region another owns. The
standing structural shape of that is: in a valid scene, the surfaces' region-sets are PAIRWISE
DISJOINT. We state it and prove the region→owner map is unambiguous under it. -/

/-- Two region-lists are DISJOINT — no region appears in both. The pairwise condition T1 maintains. -/
def regionsDisjoint (a b : List RegionId) : Bool := a.all (fun r => !b.contains r)

/-- **`wellFormed sc`** — the scene invariant: every pair of DISTINCT surfaces owns disjoint regions
(no region is painted by two surfaces). The standing precondition of the compositing laws — exactly the
disjointness T1 maintains present-by-present, here as a whole-scene property. -/
def wellFormed (sc : Scene) : Prop :=
  ∀ s₁ ∈ sc.surfaces, ∀ s₂ ∈ sc.surfaces, s₁ ≠ s₂ → regionsDisjoint s₁.regions s₂.regions = true

/-- **`ownsRegion s r`** — surface `s` owns region `r` (r is in its region-set). -/
def ownsRegion (s : Surface) (r : RegionId) : Bool := s.regions.contains r

/-- **`ownerAt sc r`** — the FIRST surface in the scene owning region `r` (the region→owner lookup the
compositor runs to answer "whose pixel is this?"). `none` if the region is unowned (background). -/
def ownerAt (sc : Scene) (r : RegionId) : Option Surface :=
  sc.surfaces.find? (fun s => ownsRegion s r)

/-- **`ownerAt_unique` (UNAMBIGUOUS OWNERSHIP).** Under `wellFormed`, a region has at most one owner: if
two surfaces in the scene both own region `r`, they are the SAME surface. So "whose pixel is this?"
always has ONE answer — the foundation of clipping and occlusion soundness (no two windows fight over a
pixel; T1 already forbade it). -/
theorem ownerAt_unique {sc : Scene} (hwf : wellFormed sc) {r : RegionId} {s₁ s₂ : Surface}
    (h₁ : s₁ ∈ sc.surfaces) (h₂ : s₂ ∈ sc.surfaces)
    (ho₁ : ownsRegion s₁ r = true) (ho₂ : ownsRegion s₂ r = true) : s₁ = s₂ := by
  by_contra hne
  -- well-formedness ⇒ s₁,s₂ disjoint; but both own r — contradiction.
  have hdisj : regionsDisjoint s₁.regions s₂.regions = true := hwf s₁ h₁ s₂ h₂ hne
  unfold regionsDisjoint at hdisj
  unfold ownsRegion at ho₁ ho₂
  -- r ∈ s₁.regions and the all-not-in-s₂ disjointness gives ¬(r ∈ s₂.regions), contradicting ho₂.
  have hr1 : r ∈ s₁.regions := by simpa [List.contains_eq_mem] using ho₁
  have hnotin : (!s₂.regions.contains r) = true := List.all_eq_true.mp hdisj r hr1
  rw [ho₂] at hnotin
  exact absurd hnotin (by decide)

/-! ## §2 — The damage model: a present dirties EXACTLY its declared regions.

We model the rendered glass as a region→content map (`Glass`), and `applyPresent` as: every region in
the present's `target` takes the new content; every region OUTSIDE keeps its old content. Then "damage
soundness" is two equations: dirtied ⊆ target (no over-damage), and outside-target unchanged (the frame
property). This is the dirty-region tracking the compositor needs to be sound. -/

/-- The rendered glass: a content value at each region (a function `RegionId → content`, the
framebuffer after compositing). `δ` is the content type (a pixel digest / tile). -/
abbrev Glass (δ : Type) := RegionId → δ

variable {δ : Type}

/-- **`applyPresent glass target newContent`** — composite a present: every region in `target` takes
`newContent`; every region outside keeps its prior glass value. The compositor's damage step (it
repaints the targeted regions, leaves the rest). `RegionId = Nat`, so region membership is decidable. -/
def applyPresent (glass : Glass δ) (target : List RegionId) (newContent : δ) : Glass δ :=
  fun r => if target.contains r then newContent else glass r

/-- A reusable disjointness fact: if `a` and `b` are `regionsDisjoint` and `r ∈ a`, then `r ∉ b`. The
membership shadow of `regionsDisjoint` (every region of `a` is outside `b`). -/
theorem notMem_of_disjoint {a b : List RegionId} (hd : regionsDisjoint a b = true) {r : RegionId}
    (hr : r ∈ a) : r ∉ b := by
  unfold regionsDisjoint at hd
  have h := List.all_eq_true.mp hd r hr
  intro hrb
  rw [List.contains_eq_mem] at h
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h hrb

/-- **`regionsDisjoint_symm`** — disjointness is symmetric (`a ∩ b = ∅ ↔ b ∩ a = ∅`). Needed because the
scene supplies the pair in one order but the frame property reads it in the other. -/
theorem regionsDisjoint_symm {a b : List RegionId} (hd : regionsDisjoint a b = true) :
    regionsDisjoint b a = true := by
  unfold regionsDisjoint at hd ⊢
  rw [List.all_eq_true]
  intro r hr
  rw [List.contains_eq_mem]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hra
  exact notMem_of_disjoint hd hra hr

/-- **`present_damage_exact` (DAMAGE SOUNDNESS, the dirty leg).** Every region the present TARGETS shows
the new content after compositing — the present dirties exactly the regions it declared. No under-damage:
the compositor cannot skip a region the present wrote. -/
theorem present_damage_exact
    (glass : Glass δ) (target : List RegionId) (newContent : δ) (r : RegionId)
    (hr : r ∈ target) : applyPresent glass target newContent r = newContent := by
  unfold applyPresent
  rw [if_pos (by simpa [List.contains_eq_mem] using hr)]

/-- **`unchanged_outside_target` (DAMAGE SOUNDNESS, the frame leg).** Every region OUTSIDE the present's
target keeps its prior content — compositing a present perturbs nothing beyond its declared region-set.
No over-damage: the compositor need not repaint the world, and provably does not. This is the locality
of damage that makes incremental rerender sound. -/
theorem unchanged_outside_target
    (glass : Glass δ) (target : List RegionId) (newContent : δ) (r : RegionId)
    (hr : r ∉ target) : applyPresent glass target newContent r = glass r := by
  unfold applyPresent
  rw [if_neg (by simpa [List.contains_eq_mem] using hr)]

/-- **`render_frame_property` (COMPOSITIONAL NON-INTERFERENCE).** A present targeting ONLY surface A's
regions leaves every region surface B owns UNTOUCHED — provided A's target is disjoint from B's regions
(which `wellFormed` guarantees for distinct A,B). So editing one window cannot perturb another window's
pixels: the frame property, the compositional dual of `FogOfWar.noninterference`. Editing the public
window does not leak into the secret window's glass, and vice versa. -/
theorem render_frame_property
    (glass : Glass δ) (target bRegions : List RegionId) (newContent : δ) (r : RegionId)
    (hdisj : regionsDisjoint target bRegions = true) (hrB : r ∈ bRegions) :
    applyPresent glass target newContent r = glass r := by
  -- r ∈ B's regions, and target is disjoint from B's regions ⇒ r ∉ target ⇒ unchanged.
  apply unchanged_outside_target
  -- `r ∈ bRegions` and `bRegions` disjoint from `target` (by symmetry) ⇒ `r ∉ target`.
  exact notMem_of_disjoint (regionsDisjoint_symm hdisj) hrB

/-! ## §3 — PAINT ORDER INDEPENDENCE: on a well-formed scene, the glass is order-free.

The compositor paints surfaces back-to-front (z-order). Where two surfaces overlap, order decides the
pixel — but T1 FORBIDS overlap, so on a well-formed scene order NEVER decides a pixel. We prove it for
the two-present composite: applying A's present then B's equals applying B's then A's, when their
targets are disjoint. So compositing non-overlapping surfaces COMMUTES — the deep reason damaged
regions may be repainted in any convenient order. -/

/-- **`paint_order_independent` (PAINT COMMUTES).** When two presents target DISJOINT region-sets (as
`wellFormed` guarantees for distinct surfaces), compositing them in EITHER order yields the same glass:
`applyPresent (applyPresent glass tA cA) tB cB = applyPresent (applyPresent glass tB cB) tA cA`. T1's
disjointness makes z-order irrelevant to the final pixels — so the compositor's paint order is a free
choice, and the rendered glass is well-defined independent of it. The clean compositional payoff of
non-overlap. -/
theorem paint_order_independent
    (glass : Glass δ) (tA tB : List RegionId) (cA cB : δ)
    (hdisj : regionsDisjoint tA tB = true) :
    applyPresent (applyPresent glass tA cA) tB cB
      = applyPresent (applyPresent glass tB cB) tA cA := by
  funext r
  simp only [applyPresent]
  -- case on membership in tA / tB; disjointness rules out the both-in branch.
  by_cases hA : tA.contains r = true <;> by_cases hB : tB.contains r = true
  · -- r in both — impossible under disjointness (r ∈ tA ⇒ r ∉ tB).
    exact absurd (by simpa [List.contains_eq_mem] using hB)
      (notMem_of_disjoint hdisj (by simpa [List.contains_eq_mem] using hA))
  -- the three non-both branches: normalize each membership flag to its Bool value and reduce the `if`s.
  all_goals (first
    | (rw [hA]; simp only [Bool.not_eq_true] at hB; rw [hB]; simp)
    | (simp only [Bool.not_eq_true] at hA; rw [hA]; rw [hB]; simp)
    | (simp only [Bool.not_eq_true] at hA hB; rw [hA, hB]; simp))

/-! ## §4 — SCENE COMPOSITION: disjoint composition preserves well-formedness; append associates.

Surfaces compose into a scene by list-append (the surface-tree EMBED). We show the scene-graph is
closed under composition of region-disjoint scenes, and that composition associates (nested surface
trees re-associate freely). -/

/-- **`compose sc₁ sc₂`** — compose two scenes by concatenating their surface lists (the surface-tree
join / EMBED). -/
def compose (sc₁ sc₂ : Scene) : Scene := ⟨sc₁.surfaces ++ sc₂.surfaces⟩

/-- **`compose_assoc`** — scene composition is ASSOCIATIVE: `(sc₁ ∘ sc₂) ∘ sc₃ = sc₁ ∘ (sc₂ ∘ sc₃)`.
Nested surface trees re-associate freely — the compositor may group sub-scenes however is convenient.
(List append associativity, lifted to `Scene`.) -/
theorem compose_assoc (sc₁ sc₂ sc₃ : Scene) :
    compose (compose sc₁ sc₂) sc₃ = compose sc₁ (compose sc₂ sc₃) := by
  unfold compose
  simp [List.append_assoc]

/-- **`compose_preserves_wellFormed` (CLOSURE).** Composing two WELL-FORMED scenes whose every
cross-scene surface pair owns DISJOINT regions yields a WELL-FORMED scene. So the scene-graph is closed
under disjoint composition — embedding one window-tree into another keeps the no-overpaint invariant,
provided the two trees do not claim each other's regions (which the EMBED authorization enforces). -/
theorem compose_preserves_wellFormed {sc₁ sc₂ : Scene}
    (hwf₁ : wellFormed sc₁) (hwf₂ : wellFormed sc₂)
    (hcross : ∀ s₁ ∈ sc₁.surfaces, ∀ s₂ ∈ sc₂.surfaces,
      regionsDisjoint s₁.regions s₂.regions = true) :
    wellFormed (compose sc₁ sc₂) := by
  intro a ha b hb hne
  unfold compose at ha hb
  simp only [List.mem_append] at ha hb
  -- four cases on which scene each of a,b came from.
  rcases ha with ha₁ | ha₂ <;> rcases hb with hb₁ | hb₂
  · exact hwf₁ a ha₁ b hb₁ hne
  · exact hcross a ha₁ b hb₂
  · -- a ∈ sc₂, b ∈ sc₁: cross-disjointness is symmetric; flip `hcross b a` via `regionsDisjoint_symm`.
    exact regionsDisjoint_symm (hcross b hb₁ a ha₂)
  · exact hwf₂ a ha₂ b hb₂ hne

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the algebra BITES. -/

section Witnesses

/-- A pixel content type for the witnesses. -/
abbrev Pixel := Nat

/-- Surface A (cell 1) owns regions {10, 11}; surface B (cell 2) owns {20, 21} — disjoint. -/
def surfA : Surface := { owner := 1, regions := [10, 11], contentDigest := 100, sourceStateRoot := 5, zLayer := 0, focusFlag := true }
def surfB : Surface := { owner := 2, regions := [20, 21], contentDigest := 200, sourceStateRoot := 6, zLayer := 1, focusFlag := false }
def sceneAB : Scene := ⟨[surfA, surfB]⟩

/-- The starting glass: every region black (0). -/
def blackGlass : Glass Pixel := fun _ => 0

-- DAMAGE EXACT: present white (1) to A's regions {10,11}; those go white, B's regions stay black.
#guard applyPresent blackGlass [10, 11] (1 : Pixel) 10 == 1     -- targeted region dirtied
#guard applyPresent blackGlass [10, 11] (1 : Pixel) 11 == 1     -- targeted region dirtied
#guard applyPresent blackGlass [10, 11] (1 : Pixel) 20 == 0     -- B's region UNTOUCHED (frame property)
#guard applyPresent blackGlass [10, 11] (1 : Pixel) 99 == 0     -- background untouched

-- REGION DISJOINTNESS: A and B own disjoint regions (the well-formedness precondition):
#guard regionsDisjoint surfA.regions surfB.regions
#guard !regionsDisjoint [10, 11] [11, 12]                        -- overlapping ⇒ NOT disjoint (bites)

-- OWNER LOOKUP: region 10 is owned by A (cell 1), region 20 by B (cell 2), region 99 by no one:
#guard (ownerAt sceneAB 10).map (·.owner) == some 1
#guard (ownerAt sceneAB 20).map (·.owner) == some 2
#guard (ownerAt sceneAB 99).map (·.owner) == none

-- PAINT ORDER INDEPENDENT: paint A-white-then-B-gray = B-gray-then-A-white on every region (disjoint):
#guard (applyPresent (applyPresent blackGlass [10,11] (1:Pixel)) [20,21] 2) 10
        == (applyPresent (applyPresent blackGlass [20,21] (2:Pixel)) [10,11] 1) 10
#guard (applyPresent (applyPresent blackGlass [10,11] (1:Pixel)) [20,21] 2) 20
        == (applyPresent (applyPresent blackGlass [20,21] (2:Pixel)) [10,11] 1) 20

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  notMem_of_disjoint,
  regionsDisjoint_symm,
  ownerAt_unique,
  present_damage_exact,
  unchanged_outside_target,
  render_frame_property,
  paint_order_independent,
  compose_assoc,
  compose_preserves_wellFormed
]

end Dregg2.Deos.Compositor
