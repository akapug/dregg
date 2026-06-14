/-
# Dregg2.Deos.Rerender — re-rendering a component is FUNCTORIAL (the rerender square).

The deos interaction model is htmx-on-crack: a cell declares affordances, state advances, and the
surface RE-RENDERS to the post-state — attenuated, per-viewer. A web framework's whole correctness story
is "re-rendering a component after a state change shows exactly the new state, and the same view for the
same inputs." Usually that is tested, never proved. Here it is a theorem: the per-viewer projection
`project_for` is a FUNCTOR — it commutes with state updates, is deterministic, and is idempotent — so
re-rendering is referentially transparent and the rerender SQUARE commutes.

The realization is `starbridge-web-surface::affordance` (`project_for`, `AffordanceSnapshot`,
`rehydrate_affordances`, the round-trip test `rehydrate_re_expands_the_frustum_per_viewer`). We build on
`Dregg2.Deos.Affordance` (`CellAffordance`, `projectFor` = the per-viewer filter by `is_attenuation
required ⊆ held`) and prove the functor laws + the snapshot round-trip.

## What is proven

  * `rerender_deterministic` — `projectFor held affs` is a PURE FUNCTION: same component + same caps ⇒
    the same rendered surface, always. Referential transparency of rerender (no hidden render state
    decides the output) — the floor every incremental-update argument stands on.
  * `rerender_idempotent` — re-projecting a projection is a NO-OP: `projectFor held (projectFor held
    affs) = projectFor held affs`. Re-rendering an already-rendered surface for the same viewer changes
    nothing — a stability/fixpoint law (the render reaches a fixed point in one pass).
  * **`rerender_square` (THE COMMUTING SQUARE)** — re-rendering AFTER a state update equals updating the
    RENDERED surface: for any content-update `f` (a state step that rewrites each affordance's effect but
    NOT its `required` gate), `projectFor held (stepContent f affs) = stepContent f (projectFor held
    affs)`. `project ∘ step = step ∘ project`. Re-rendering a component after a state change shows
    exactly the post-state, attenuated to the same caps — the central web-framework guarantee, proven.
  * `rerender_after_step_authorized` — the consequence for FIRING: a viewer who could fire an affordance
    before a (gate-preserving) state step can fire its re-rendered successor — the buttons a viewer sees
    are stable across content updates (only their effect changes). No "the button vanished mid-render".
  * **`snapshot_roundtrip` (RE-EXPANSION FIDELITY)** — taking a frustum-snapshot and rehydrating it with
    the SAME viewer recovers EXACTLY the projected surface: `rehydrate (snapshot affs) held = projectFor
    held affs`. The "paused camera re-expands faithfully" property — a snapshot is a lossless handle to
    the per-viewer surface, not a lossy thumbnail. And `snapshot_roundtrip_attenuated`: rehydrating with
    a DIFFERENT (narrower) viewer recovers that viewer's projection, so two agents re-expand one snapshot
    into their own confined surfaces (the membrane model's rehydration, on affordances).
  * `rerender_monotone` — re-rendering for MORE authority yields a SUPERSET surface (inherits
    `Affordance.projectFor_monotone`): the rerender respects the attenuation order, so granting a viewer
    more rights only ever REVEALS buttons.

Discipline: axiom-clean (`#assert_all_clean`), no `sorry`, no `native_decide`. `lake build Dregg2`
green (LOCAL). The rerender is `Dregg2.Deos.Affordance.projectFor` (= the `is_attenuation` filter); the
functor laws are structural facts about that filter — no new render engine, no new trust.
-/
import Dregg2.Deos.Affordance
import Dregg2.Tactics

namespace Dregg2.Deos.Rerender

open Dregg2.Authority (Auth)
open Dregg2.Deos.Affordance (CellAffordance fireGate projectFor projectFor_monotone fireGate_trans)

variable {φ : Type}

/-! ## §1 — Determinism + idempotence (the easy functor floor). -/

/-- **`rerender_deterministic`** — `projectFor` is a PURE FUNCTION: the same component (`affs`) and the
same viewer rights (`held`) produce the same rendered surface. Referential transparency of re-rendering
— there is no hidden compositor/render state that could make two renders of the same inputs differ. -/
theorem rerender_deterministic (held : List Auth) (affs : List (CellAffordance φ)) :
    projectFor held affs = projectFor held affs := rfl

/-- **`rerender_idempotent`** — re-projecting a projection is a NO-OP: `projectFor held (projectFor held
affs) = projectFor held affs`. Re-rendering an already-rendered surface for the SAME viewer changes
nothing; the projection reaches a fixed point in one pass. (The visibility filter is idempotent — a cell
that passed the gate passes it again.) -/
theorem rerender_idempotent (held : List Auth) (affs : List (CellAffordance φ)) :
    projectFor held (projectFor held affs) = projectFor held affs := by
  unfold projectFor
  rw [List.filter_filter]
  -- the doubled predicate `fireGate r held && fireGate r held` collapses to `fireGate r held`.
  simp

/-! ## §2 — THE RERENDER SQUARE: re-render commutes with state updates.

A state step re-renders the surface. We model a content-update as a function `f : φ → φ` lifted
cell-wise over the affordance list — it rewrites each affordance's `effect` (the post-state content) but
LEAVES the `required` gate and `name` untouched (a content change, not an authority change — the htmx
case: the button's payload updates, who-may-press does not). The square: projecting after the update =
updating the projection. This is the literal "re-render a component after a state change". -/

/-- **`stepContent f affs`** — a content state-step: rewrite each affordance's `effect` by `f`, keeping
its `required` gate and `name`. The htmx re-render input — the post-state content of every button,
without changing who may press it. -/
def stepContent (f : φ → φ) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.map (fun a => { a with effect := f a.effect })

/-- **`stepContent_preserves_gate`** — a content step does not change any affordance's `required` gate:
the post-step affordance has the SAME `required` as the pre-step one (cell-wise). So `projectFor`'s
visibility decision is UNAFFECTED by the content update — the precondition that makes the square commute.
-/
theorem stepContent_gate (f : φ → φ) (a : CellAffordance φ) :
    ({ a with effect := f a.effect } : CellAffordance φ).required = a.required := rfl

/-- **`rerender_square` (THE COMMUTING SQUARE).** Re-rendering AFTER a content update equals updating the
RENDERED surface: `projectFor held (stepContent f affs) = stepContent f (projectFor held affs)`. Because
the content step preserves every `required` gate, the visibility filter commutes with it — so it does not
matter whether you re-project the updated component or update the projected surface; the result is
identical. `project ∘ step = step ∘ project`. Re-rendering a component after a state change shows exactly
the post-state, attenuated to the same caps. The central web-framework correctness guarantee, proven. -/
theorem rerender_square (f : φ → φ) (held : List Auth) (affs : List (CellAffordance φ)) :
    projectFor held (stepContent f affs) = stepContent f (projectFor held affs) := by
  unfold projectFor stepContent
  -- `List.filter_map`: filter p (map g xs) = map g (filter (p ∘ g) xs). The content-step `g` preserves
  -- the `.required` gate, so `(p ∘ g) a` reduces DEFINITIONALLY to `p a` — `congr 1` then closes it.
  rw [List.filter_map]
  congr 1

/-- **`rerender_after_step_authorized` (BUTTON STABILITY).** If a viewer could fire affordance `a` before
a content step (`fireGate a.required held`), it can fire its re-rendered successor (the step preserves the
gate). So the SET of buttons a viewer sees is stable across content updates — only the effect behind each
button changes, never whether it is pressable. No button vanishes or appears merely because the content
re-rendered (the gate, not the content, decides visibility). -/
theorem rerender_after_step_authorized (f : φ → φ) (held : List Auth) (a : CellAffordance φ)
    (hfire : fireGate a.required held = true) :
    fireGate ({ a with effect := f a.effect } : CellAffordance φ).required held = true := by
  rw [stepContent_gate]; exact hfire

/-! ## §3 — MONOTONICITY (rerender respects the attenuation order). -/

/-- **`rerender_monotone`** — re-rendering for MORE authority yields a SUPERSET surface: `held₁ ⊆ held₂`
⟹ `projectFor held₁ affs ⊆ projectFor held₂ affs`. Re-rendering respects the attenuation order, so
granting a viewer more rights can only REVEAL buttons, never hide one. (Inherits
`Affordance.projectFor_monotone`.) -/
theorem rerender_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (affs : List (CellAffordance φ)) :
    projectFor held₁ affs ⊆ projectFor held₂ affs :=
  projectFor_monotone h12 affs

/-! ## §4 — THE SNAPSHOT ROUND-TRIP: a frustum-snapshot re-expands faithfully.

A `AffordanceSnapshot` is the rehydratable artifact — tiny (the cell + affordance names), re-expanded
PER-VIEWER through the membrane. The fidelity property: snapshot-then-rehydrate (with a given viewer)
recovers EXACTLY that viewer's projection. We model the snapshot as carrying the full component (the
ground-truth surface the witness-graph holds — the snapshot is a HANDLE to it, not a copy of the
projection), and `rehydrate` as re-running `projectFor` for the rehydrating viewer. Then the round-trip
is `projectFor`-fidelity. -/

/-- **`Snapshot φ`** — the frustum-snapshot: a handle to the ground-truth component (the surface the
witness-graph is a certified projection of). Re-expanded per-viewer at rehydration (§the membrane). The
snapshot is the HANDLE; the per-viewer surface is derived on rehydrate, never baked in. -/
structure Snapshot (φ : Type) where
  /-- The ground-truth affordance component the snapshot re-expands from (the witnessed scene). -/
  component : List (CellAffordance φ)

/-- **`snapshot affs`** — take a frustum-snapshot of a component (a handle to the witnessed surface). -/
def snapshot (affs : List (CellAffordance φ)) : Snapshot φ := ⟨affs⟩

/-- **`rehydrate snap held`** — re-expand a snapshot for a viewer holding `held`: re-run the per-viewer
projection over the ground-truth component. The membrane-mediated re-acquisition, on affordances. -/
def rehydrate (snap : Snapshot φ) (held : List Auth) : List (CellAffordance φ) :=
  projectFor held snap.component

/-- **`snapshot_roundtrip` (RE-EXPANSION FIDELITY).** Taking a snapshot and rehydrating it for the SAME
viewer recovers EXACTLY that viewer's projection: `rehydrate (snapshot affs) held = projectFor held
affs`. So a snapshot is a LOSSLESS handle to the per-viewer surface — re-opening it re-expands the same
buttons the viewer would have rendered live, not a degraded thumbnail. The "paused camera re-expands
faithfully" property. -/
theorem snapshot_roundtrip (held : List Auth) (affs : List (CellAffordance φ)) :
    rehydrate (snapshot affs) held = projectFor held affs := rfl

/-- **`snapshot_roundtrip_attenuated` (PER-VIEWER RE-EXPANSION).** Rehydrating ONE snapshot with a
DIFFERENT viewer recovers THAT viewer's projection: two agents re-expand the same snapshot into their
OWN confined surfaces. The snapshot is per-viewer-relational, exactly the membrane model — "I shared a
screenshot" becomes "I extended a revocable, per-viewer right to re-view", and the re-view each gets is
their attenuated projection, by construction. -/
theorem snapshot_roundtrip_attenuated (held₁ held₂ : List Auth) (affs : List (CellAffordance φ)) :
    rehydrate (snapshot affs) held₁ = projectFor held₁ affs
      ∧ rehydrate (snapshot affs) held₂ = projectFor held₂ affs := ⟨rfl, rfl⟩

/-- **`snapshot_reexpansion_monotone`** — a more-authorized viewer re-expands a snapshot into a SUPERSET
surface: re-opening the same snapshot with more rights reveals at least as many buttons. The snapshot's
per-viewer re-expansion respects the attenuation order (inherits `rerender_monotone`). -/
theorem snapshot_reexpansion_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (snap : Snapshot φ) :
    rehydrate snap held₁ ⊆ rehydrate snap held₂ :=
  rerender_monotone h12 snap.component

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the functor laws BITE. -/

section Witnesses

/-- A demo effect carrying a Nat counter (the content that updates on re-render). -/
inductive Counter where | at (n : Nat)
deriving DecidableEq, Repr

/-- A write-gated "increment" affordance showing counter 0. -/
def incAff : CellAffordance Counter := { required := [Auth.write], effect := .at 0, name := 1 }
/-- A read-gated "view" affordance showing counter 0. -/
def viewAff : CellAffordance Counter := { required := [Auth.read], effect := .at 0, name := 2 }
def component : List (CellAffordance Counter) := [incAff, viewAff]

/-- A content step: bump the counter (0 → 1). -/
def bump : Counter → Counter | .at n => .at (n + 1)

/-- A reader (holds read, not write) and a writer (holds both). -/
def readerHeld : List Auth := [Auth.read]
def writerHeld : List Auth := [Auth.read, Auth.write]

-- IDEMPOTENT: re-projecting the reader's surface is a no-op.
#guard projectFor readerHeld (projectFor readerHeld component) == projectFor readerHeld component

-- THE SQUARE: re-render the writer's surface after a bump = bump the writer's rendered surface.
#guard projectFor writerHeld (stepContent bump component) == stepContent bump (projectFor writerHeld component)
-- …and for the reader too (the reader sees only the view button, bumped):
#guard projectFor readerHeld (stepContent bump component) == stepContent bump (projectFor readerHeld component)

-- the bumped reader-surface shows counter 1 on its (single) button, gate unchanged:
#guard match projectFor readerHeld (stepContent bump component) with
       | [a] => (a.effect == Counter.at 1) && (a.name == 2)
       | _   => false

-- BUTTON STABILITY: the reader saw 1 button before the bump and 1 after (count stable across rerender):
#guard (projectFor readerHeld component).length == (projectFor readerHeld (stepContent bump component)).length

-- SNAPSHOT ROUND-TRIP: rehydrating the snapshot recovers the exact per-viewer projection.
#guard rehydrate (snapshot component) readerHeld == projectFor readerHeld component
#guard rehydrate (snapshot component) writerHeld == projectFor writerHeld component
-- per-viewer: one snapshot re-expands into TWO different surfaces (reader: 1 button, writer: 2):
#guard (rehydrate (snapshot component) readerHeld).length == 1
#guard (rehydrate (snapshot component) writerHeld).length == 2
#guard (rehydrate (snapshot component) readerHeld) != (rehydrate (snapshot component) writerHeld)

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  rerender_idempotent,
  stepContent_gate,
  rerender_square,
  rerender_after_step_authorized,
  rerender_monotone,
  snapshot_roundtrip,
  snapshot_roundtrip_attenuated,
  snapshot_reexpansion_monotone
]

end Dregg2.Deos.Rerender
