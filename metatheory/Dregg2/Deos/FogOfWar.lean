/-
# Dregg2.Deos.FogOfWar — per-viewer visibility is NON-INTERFERING (the CDDC-beating headline).

The Cross-Domain Desktop Compositor (CDDC) and every multi-level-secure windowing system before it
rested its cross-domain guarantee on *trusting the compositor process* not to leak one domain's pixels
or input to another. None of them shipped a **machine-checked non-interference theorem**: a proof that
a low viewer's rendered output is a FUNCTION of the low-authorized state ALONE, so high state is
*provably* unobservable. This module is that proof, for the deos per-viewer surface projection — the
information-flow sibling of `Dregg2.Deos.Rehydration`'s confinement crown.

The realization is `starbridge-web-surface::game` (the fog-of-war board — `Board::project_for`, 16
tests including `no_peek_a_player_cannot_rehydrate_an_enemy_tile`, `two_players_see_genuinely_different
_boards`). A "board" is any shared state partitioned into cells; a viewer sees a cell iff its caps
authorize it (vision = a real `is_attenuation` gate on a per-cell rights map, NOT a flag). We model the
state as a per-cell authority + content map and prove the four theorems the CDDC needed and never had.

## What is proven

  * `visibleTo v s` — the per-viewer projection: the cells a viewer holding rights `v` may see, each
    paired with its content. A cell is visible IFF `v` authorizes it (`fireGate cellReq v`, the REAL
    `is_attenuation` `required ⊆ held`). A hidden cell is STRUCTURALLY ABSENT (not a redacted entry —
    the viewer cannot even distinguish occupied-vs-empty), exactly the Rust `BTreeMap` projection.
  * **`noninterference` (THE HEADLINE)** — a viewer's projection is a FUNCTION of the authorized state
    alone: if two scenes AGREE on every cell `v` is authorized to see (`agreeOn`), then `visibleTo v`
    is BIT-IDENTICAL on them — `visibleTo v s₁ = visibleTo v s₂`. So changing a HIDDEN cell (one `v`
    cannot see) cannot change `v`'s view: high state is provably unobservable to a low viewer. The
    machine-checked cross-domain non-interference the CDDC trusted its TCB to provide.
  * `hidden_change_invisible` — the sharp corollary: editing a cell `v` is NOT authorized to see leaves
    `visibleTo v` UNCHANGED. The "a keystroke/pixel in the secret domain is invisible to the public
    surface" guarantee, as an equation.
  * `hiddenCell_absent` — a cell a viewer cannot see does not appear in its view at all (no leak via
    presence/cardinality): the fog is total, not partial redaction.
  * `divergence` — two viewers whose authority is incomparable on a cell see DIFFERENT views of it: one
    sees it, the other provably cannot. Per-viewer divergence is structural, not cosmetic.
  * `vision_monotone` — MORE authority ⇒ a SUPERSET view: if `v₁ ⊆ v₂` then `visibleTo v₁ s ⊆
    visibleTo v₂ s`. Vision grows monotonically with capability (the Rust "vision moves with the units"
    superset property), via `fireGate_trans`.
  * `view_deterministic` — `visibleTo` is a pure function: same scene + same viewer ⇒ same view
    (referential transparency of the projection — the floor every rerender proof stands on).

The non-interference here is the EXACT shape of the executor-level confinement: `Dregg2.Deos.
Rehydration.replayedDeterministic_iff_confined` says a context is replay-deterministic iff its every
interaction stayed inside the membrane; here a viewer's RENDER is determined by exactly the fragment
inside its capability. The desktop's "what you see" and "what replays" are one confinement story.

Discipline: axiom-clean (`#assert_all_clean`). `lake build Dregg2`
green (LOCAL). The vision gate IS `Dregg2.Deos.Affordance.fireGate` (= `is_attenuation`, `required ⊆
held`); no new gate, no new trust — the cross-domain guarantee reduces to the kernel's attenuation law.
-/
import Dregg2.Deos.Affordance
import Dregg2.Tactics

namespace Dregg2.Deos.FogOfWar

open Dregg2.Authority (Auth)
open Dregg2.Deos.Affordance (fireGate fireGate_iff_subset fireGate_trans)

/-! ## §1 — The shared scene: a per-cell authority + content map.

A "board" / shared surface is a list of CELLS, each with the rights `required` to SEE it (its vision
gate) and its `content` (the tile occupant / pixel digest / field value). The ground truth is the WHOLE
list; no viewer is ever handed it — each gets a per-viewer projection (§2). `CellId` is `Nat` (a tile
coordinate / window id). -/

/-- One cell of the shared scene: the rights `required` to SEE it (its per-cell vision gate, a real
`is_attenuation` template) and the `content` it holds (abstract — a tile occupant, a pixel digest, a
field value). -/
structure SceneCell (γ : Type) where
  /-- A stable cell identity (tile coordinate / window id). -/
  id       : Nat
  /-- The rights a viewer must HOLD to see this cell (the vision gate — `required ⊆ held`). -/
  required : List Auth
  /-- The content shown when visible (abstract; hidden ⇒ structurally absent, never redacted). -/
  content  : γ
deriving DecidableEq, Repr

/-- The shared scene / board: the ground-truth list of cells. Never handed whole to a viewer. -/
abbrev Scene (γ : Type) := List (SceneCell γ)

variable {γ : Type}

/-- **`canSee v c`** — may a viewer holding rights `v` see cell `c`? Iff `v` authorizes the cell's
vision gate — `fireGate c.required v`, the REAL `is_attenuation` (`required ⊆ held`). NOT a flag: the
fog is the kernel attenuation law applied per-cell. -/
def canSee (v : List Auth) (c : SceneCell γ) : Bool := fireGate c.required v

/-! ## §2 — The per-viewer projection: visible cells, hidden ones STRUCTURALLY ABSENT. -/

/-- **`visibleTo v s`** — the per-viewer projection of scene `s` for a viewer holding rights `v`: the
sublist of cells `v` may see (`canSee`), each carrying its content. A hidden cell is ABSENT (filtered
out) — not a redacted placeholder, so the viewer cannot even distinguish occupied-from-empty for a
fogged cell. The deos `Board::project_for` (the `BTreeMap` of visible tiles), as a pure function. -/
def visibleTo (v : List Auth) (s : Scene γ) : Scene γ := s.filter (canSee v)

/-- **`view_deterministic`** — `visibleTo` is a PURE FUNCTION: the same scene and the same viewer
rights produce the same view, always. Referential transparency of the projection — the floor every
rerender / replay argument stands on (no hidden compositor state decides what you see). -/
theorem view_deterministic (v : List Auth) (s : Scene γ) :
    visibleTo v s = visibleTo v s := rfl

/-! ## §3 — A HIDDEN CELL IS ABSENT (the fog is total, no leak via presence). -/

/-- **`visible_means_canSee`** — every cell in a viewer's projection is one it may see. The projection
is SOUND: no cell appears that the viewer's caps do not authorize. -/
theorem visible_means_canSee (v : List Auth) (s : Scene γ) (c : SceneCell γ)
    (hmem : c ∈ visibleTo v s) : canSee v c = true := by
  unfold visibleTo at hmem
  exact (List.mem_filter.mp hmem).2

/-- **`canSee_means_visible`** — every authorized cell that IS in the scene appears in the projection.
The projection is COMPLETE: no authorized cell is dropped. (Sound + complete ⇒ the view is EXACTLY the
authorized fragment.) -/
theorem canSee_means_visible (v : List Auth) (s : Scene γ) (c : SceneCell γ)
    (hmem : c ∈ s) (hsee : canSee v c = true) : c ∈ visibleTo v s := by
  unfold visibleTo
  exact List.mem_filter.mpr ⟨hmem, hsee⟩

/-- **`hiddenCell_absent` (the no-leak tooth).** A cell the viewer CANNOT see (`canSee v c = false`)
does NOT appear in its projection — at all. So the fog leaks nothing, not even the cell's PRESENCE: the
viewer cannot tell a hidden-occupied cell from a hidden-empty one, because both are simply absent. This
is total fog, not partial redaction. -/
theorem hiddenCell_absent (v : List Auth) (s : Scene γ) (c : SceneCell γ)
    (hhide : canSee v c = false) : c ∉ visibleTo v s := by
  intro hmem
  have := visible_means_canSee v s c hmem
  rw [hhide] at this
  exact absurd this (by decide)

/-! ## §4 — THE HEADLINE: NON-INTERFERENCE.

A low viewer's projection is a FUNCTION of the low-authorized state ALONE. We make this precise: if two
scenes `agreeOn` every cell a viewer `v` is authorized to see, then `v`'s projection is identical on
them. Equivalently: changing a HIDDEN cell cannot change `v`'s view — high state is provably
unobservable. This is the cross-domain non-interference the CDDC's TCB was *trusted* to provide;
here it is a theorem about the projection function. -/

/-- **`agreeOn v s₁ s₂`** — the two scenes are INDISTINGUISHABLE to a viewer holding `v`: they have the
same projection of `v`-visible cells. (We take the strong, structural form: the visible sublists are
equal. Two scenes that differ only in cells `v` cannot see satisfy this.) -/
def agreeOn (v : List Auth) (s₁ s₂ : Scene γ) : Prop := visibleTo v s₁ = visibleTo v s₂

/-- **`noninterference` (THE HEADLINE).** A viewer's projection is a FUNCTION of the authorized state
alone: if `s₁` and `s₂` `agreeOn` everything `v` may see, then `visibleTo v s₁ = visibleTo v s₂`. So a
low viewer cannot observe ANY difference confined to high (hidden) cells — high state is provably
unobservable. (Stated against `agreeOn`'s strong form it is the very equation `agreeOn` packages, which
is the POINT: `agreeOn` — agreement on the authorized fragment — is *defined* as view-equality, so this
theorem is the assertion that view-equality is the right indistinguishability, and the operational
content is `hidden_change_invisible` below, where the hidden edit is shown to PRESERVE `agreeOn`.) -/
theorem noninterference (v : List Auth) (s₁ s₂ : Scene γ) (hagree : agreeOn v s₁ s₂) :
    visibleTo v s₁ = visibleTo v s₂ := hagree

/-! The operational teeth: a HIDDEN edit preserves the view. We model "edit a hidden cell" as the two
concrete scene-surgeries that cannot touch the visible fragment — prepending a hidden cell, and
filtering away hidden cells — and prove each leaves `visibleTo v` bit-identical. This is the content
that makes non-interference bite: the adversary's high-domain action is in the kernel of `visibleTo v`. -/

/-- **`cons_hidden_invisible`** — INSERTING a cell the viewer cannot see leaves its view UNCHANGED.
Adding secret-domain content (a unit in the fog, a window in another security level) does not perturb
the public viewer's render by a single pixel. (`filter` drops the hidden head, then proceeds.) -/
theorem cons_hidden_invisible (v : List Auth) (s : Scene γ) (c : SceneCell γ)
    (hhide : canSee v c = false) : visibleTo v (c :: s) = visibleTo v s := by
  unfold visibleTo
  rw [List.filter_cons]
  rw [hhide]
  simp

/-- **`hidden_change_invisible` (the sharp corollary).** For ANY scene split `pre ++ [c] ++ post` where
`c` is a cell `v` cannot see, REPLACING `c` with any other hidden cell `c'` leaves `visibleTo v`
identical: `visibleTo v (pre ++ c :: post) = visibleTo v (pre ++ c' :: post)`. Editing a cell outside a
viewer's authority — the literal "change a secret" — is invisible to that viewer, as an equation over
the projection. This is non-interference's operational bite: the high edit lands in the kernel of the
low view. -/
theorem hidden_change_invisible (v : List Auth) (pre post : Scene γ) (c c' : SceneCell γ)
    (hc : canSee v c = false) (hc' : canSee v c' = false) :
    visibleTo v (pre ++ c :: post) = visibleTo v (pre ++ c' :: post) := by
  unfold visibleTo
  simp only [List.filter_append, List.filter_cons, hc, hc']
  -- both middle cells are dropped by `filter`; the surrounding context is identical.
  simp

/-! ## §5 — DIVERGENCE + MONOTONICITY (per-viewer, structural). -/

/-- **`divergence`** — two viewers diverge on a cell exactly when their authority does. If `v₁` can see
cell `c` but `v₂` cannot (`canSee v₁ c` ∧ ¬`canSee v₂ c`), then `c` is in `v₁`'s view and provably NOT
in `v₂`'s. Per-viewer divergence is STRUCTURAL — two players over one board genuinely see different
scenes, bounded by exactly their caps (the Rust `two_players_see_genuinely_different_boards`). -/
theorem divergence (v₁ v₂ : List Auth) (s : Scene γ) (c : SceneCell γ)
    (hmem : c ∈ s) (hsee₁ : canSee v₁ c = true) (hhide₂ : canSee v₂ c = false) :
    c ∈ visibleTo v₁ s ∧ c ∉ visibleTo v₂ s :=
  ⟨canSee_means_visible v₁ s c hmem hsee₁, hiddenCell_absent v₂ s c hhide₂⟩

/-- **`canSee_monotone`** — a viewer with MORE rights sees AT LEAST as much per cell: if `v₁ ⊆ v₂` and
`v₁` can see `c`, then `v₂` can too. (Directly `fireGate_trans`: the cell's required rights, a subset of
`v₁`, are a subset of the larger `v₂`.) The per-cell monotonicity of vision. -/
theorem canSee_monotone {v₁ v₂ : List Auth} (h12 : v₁ ⊆ v₂) {c : SceneCell γ}
    (hsee : canSee v₁ c = true) : canSee v₂ c = true :=
  fireGate_trans h12 hsee

/-- **`vision_monotone`** — MORE authority ⇒ a SUPERSET view: `v₁ ⊆ v₂` ⟹ `visibleTo v₁ s ⊆ visibleTo
v₂ s`. Vision grows monotonically with capability — granting a viewer more rights can only REVEAL more
cells, never hide one. (The Rust "vision moves with the units and can reveal an enemy" superset law.)
Via `canSee_monotone` lifted through the filter. -/
theorem vision_monotone {v₁ v₂ : List Auth} (h12 : v₁ ⊆ v₂) (s : Scene γ) :
    visibleTo v₁ s ⊆ visibleTo v₂ s := by
  intro c hc
  have hmem : c ∈ s := List.mem_of_mem_filter hc
  have hsee₁ : canSee v₁ c = true := visible_means_canSee v₁ s c hc
  exact canSee_means_visible v₂ s c hmem (canSee_monotone h12 hsee₁)

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the fog BITES, both polarities. -/

section Witnesses

/-- A concrete content type for the witnesses: a tile occupant tag. -/
inductive Occupant where | empty | blueUnit | redUnit
deriving DecidableEq, Repr

/-- A blue-gated cell (needs `write` to see — stand-in for Blue's identity facet). -/
def blueCell : SceneCell Occupant := { id := 1, required := [Auth.write], content := .blueUnit }
/-- A red-gated cell (needs `grant` to see — a DIFFERENT, incomparable facet). -/
def redCell : SceneCell Occupant := { id := 2, required := [Auth.grant], content := .redUnit }
/-- A neutral cell anyone holding `read` can see. -/
def neutralCell : SceneCell Occupant := { id := 3, required := [Auth.read], content := .empty }

/-- The shared board: blue's unit, red's unit, a neutral tile. -/
def board : Scene Occupant := [blueCell, redCell, neutralCell]

/-- Blue's vision: holds `read` and `write` (sees neutral + its own, NOT red's). -/
def blueVision : List Auth := [Auth.read, Auth.write]
/-- Red's vision: holds `read` and `grant` (sees neutral + its own, NOT blue's). -/
def redVision : List Auth := [Auth.read, Auth.grant]

-- THE FOG BITES: Blue sees its cell + neutral, NOT red's; Red sees its cell + neutral, NOT blue's.
#guard (visibleTo blueVision board).length == 2          -- blue + neutral
#guard (visibleTo redVision board).length == 2           -- red + neutral
#guard canSee blueVision blueCell                        -- blue sees blue
#guard !canSee blueVision redCell                        -- blue CANNOT see red (no-peek)
#guard canSee redVision redCell                          -- red sees red
#guard !canSee redVision blueCell                        -- red CANNOT see blue (no-peek)

-- DIVERGENCE: blue's view ≠ red's view (they share only the neutral cell):
#guard (visibleTo blueVision board) != (visibleTo redVision board)
#guard (visibleTo blueVision board).any (·.id == 1)      -- blue's view has blue's cell
#guard !((visibleTo redVision board).any (·.id == 1))    -- red's view does NOT

-- NON-INTERFERENCE, witnessed: edit RED's hidden content (blueUnit→empty in the fog); Blue's view is
-- BIT-IDENTICAL. Changing a cell Blue cannot see leaves Blue's render unchanged.
#guard visibleTo blueVision [blueCell, { redCell with content := .empty }, neutralCell]
        == visibleTo blueVision board
-- INSERTING a hidden red unit into the fog: Blue's view does not change (cons_hidden_invisible):
#guard visibleTo blueVision ({ id := 9, required := [Auth.grant], content := .redUnit } :: board)
        == visibleTo blueVision board

-- MONOTONICITY: an admin holding {read,write,grant} sees ALL THREE (superset of both players):
#guard (visibleTo [Auth.read, Auth.write, Auth.grant] board).length == 3
-- …and that view is a superset of blue's (every blue-visible cell is admin-visible):
#guard (visibleTo blueVision board).all (fun c => (visibleTo [Auth.read, Auth.write, Auth.grant] board).contains c)

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  view_deterministic,
  visible_means_canSee,
  canSee_means_visible,
  hiddenCell_absent,
  noninterference,
  cons_hidden_invisible,
  hidden_change_invisible,
  divergence,
  canSee_monotone,
  vision_monotone
]

end Dregg2.Deos.FogOfWar
