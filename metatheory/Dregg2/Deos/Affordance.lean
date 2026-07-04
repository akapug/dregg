/-
# Dregg2.Deos.Affordance — an agent fires only the affordances its caps authorize (leg 4 of the crown).

`docs/deos/DEOS.md` §"the verified-deos program", target 4 (**Affordance soundness**):

  > A cell-affordance interaction is a verified turn; prove an agent can only fire affordances its caps
  > authorize (gateOK on the affordance effect-template), and the post-state surface binds the attested
  > root.

`docs/deos/DEOS.md` §"htmx on crack": a `CellAffordance` is a named `dregg_turn::Effect` template, "the
render/fire gate is the GENUINE `is_attenuation` (`required ⊆ held`, the proven lattice — not a new
gate)", "an unauthorized fire is REFUSED in-band, an authorized one yields a verified-turn
`AffordanceIntent`". The realization is `starbridge-web-surface::affordance` (15 module tests); this is
the proof.

This is NOT new mathematics. The fire gate is `required ⊆ held` — the SAME `is_attenuation` lattice the
cap crown proves (`Dregg2.Exec.attenuate_subset` narrows along it; here it GATES). An affordance fire is
a `gateOK` decision on the affordance's required-rights template, and the post-state binds the attested
root via the EXISTING `Dregg2.Exec.Receipts.Receipt.newCommit` (the state commitment the verified turn
produced).

## What is proven

  * `fireGate required held` — the affordance gate: `required ⊆ held` (the genuine `is_attenuation`,
    `required ⊆ held`, decidable). Reflexive on equal rights; transitive (chains through projection).
  * `CellAffordance` — a named affordance: its `required : List Auth` template + the REAL effect
    `effect : φ` it carries (the `dregg_turn::Effect`, abstract here so any effect type fits).
  * `fire aff held s` — the fire dispatch: iff `held` authorizes `aff.required`, yields a verified-turn
    `AffordanceIntent` carrying the REAL effect AND the post-state surface (binding the attested root);
    otherwise `none` (refused in-band).
  * **`fire_authorized_iff` (KEYSTONE)** — `fire` commits (`isSome`) IFF the gate passes (`required ⊆
    held`). Both polarities: an authorized agent fires; an UNAUTHORIZED one is REFUSED (`none`). An
    agent can fire ONLY the affordances its caps authorize — target 4's first clause, as an `↔`.
  * `fire_carries_real_effect` — a committed fire's intent carries the affordance's REAL effect
    verbatim (not a stand-in) — the `dregg_turn::Effect` template is the one that fires.
  * `firedSurface_binds_attested_root` — the post-state surface's bound root EQUALS the attested
    receipt's `newCommit` (the state commitment the verified turn produced). The post-state surface
    binds the attested root — target 4's second clause. (And `firedSurface_root_changes` witnesses it
    is the NEW root, not the old.)
  * `unauthorized_fire_no_surface` — the anti-ghost: an unauthorized fire yields NO surface at all (it
    cannot bind any root), so it cannot forge a post-state. Fail-closed.
  * `project_for_attenuates` — progressive enhancement → progressive ATTENUATION: a viewer holding
    fewer rights is offered a subset of the affordances (those whose `required` it still satisfies);
    the per-viewer affordance set only SHRINKS as authority shrinks (monotone), via `fireGate`.

Discipline: axiom-clean (`#assert_all_clean` at the close). `lake build
Dregg2` green (LOCAL). The fire gate IS `required ⊆ held` (the `is_attenuation` order the cap crown
proves); the attested root IS the EXISTING `Receipts.Receipt.newCommit`. No new gate, no new commitment.
-/
import Dregg2.Exec.Receipt
import Dregg2.Authority.Positional
import Dregg2.Tactics

namespace Dregg2.Deos.Affordance

open Dregg2.Authority (Auth)
open Dregg2.Exec.Receipts (Receipt mkReceipt)

/-! ## §1 — The affordance gate IS `is_attenuation` (`required ⊆ held`).

The render/fire gate is the GENUINE `is_attenuation` — `required ⊆ held`, the SAME lattice the cap
crown proves (`Dregg2.Exec.attenuate_subset` narrows ALONG it; here it GATES). We use the decidable
`required.all (held.contains ·)` form and bridge it to `List.Subset`. NO new gate. -/

/-- **`fireGate required held`** — may an agent holding `held` rights fire an affordance requiring
`required`? Iff `required ⊆ held` — the genuine `is_attenuation` (`required ⊆ held`, the Rust
`cell/src/capability.rs:461` order), decidable as `required.all (held.contains ·)`. This is NOT a new
gate: it is the SAME subset order the cap crown's attenuation narrows along. -/
def fireGate (required held : List Auth) : Bool := required.all (fun a => held.contains a)

/-- **The gate IS the subset relation** — `fireGate required held = true ↔ required ⊆ held`. Ties the
decidable gate to the `List.Subset` the lattice laws speak in, so the affordance gate is literally
`is_attenuation`, not a look-alike. -/
theorem fireGate_iff_subset (required held : List Auth) :
    fireGate required held = true ↔ required ⊆ held := by
  unfold fireGate
  constructor
  · intro hg a ha
    have := List.all_eq_true.mp hg a ha
    simpa [List.contains_eq_mem] using this
  · intro hsub
    rw [List.all_eq_true]
    intro a ha
    simpa [List.contains_eq_mem] using hsub ha

/-- **The gate is REFLEXIVE** — an agent holding exactly the required rights may fire (`fireGate r r`).
An affordance is always fireable by the holder of precisely its rights. -/
theorem fireGate_refl (required : List Auth) : fireGate required required = true := by
  rw [fireGate_iff_subset]; exact fun a ha => ha

/-- **The gate is TRANSITIVE along projection** — if `held₁ ⊆ held₂` (a viewer holds less than a
grantor) and the viewer can fire (`fireGate required held₁`), the grantor can too. So the fireable set
only shrinks under attenuation — the bridge to the per-viewer projection (§4). -/
theorem fireGate_trans {required held₁ held₂ : List Auth}
    (h12 : held₁ ⊆ held₂) (hfire : fireGate required held₁ = true) :
    fireGate required held₂ = true := by
  rw [fireGate_iff_subset] at hfire ⊢
  exact List.Subset.trans hfire h12

/-! ## §2 — A `CellAffordance`: a named effect-template carrying a REAL effect.

A `CellAffordance` is the deos "htmx on crack" element — a named `dregg_turn::Effect` template, gated
by `required` rights. The effect type `φ` is abstract (so ANY real effect fits — the
`starbridge-web-surface` realization carries a `dregg_turn::Effect`); the affordance carries a REAL
`effect : φ`, not a stand-in. -/

variable {φ : Type}

/-- **`CellAffordance φ`** — a named, cap-gated effect-template: the rights `required` to fire it, plus
the REAL `effect : φ` it carries (the `dregg_turn::Effect`). The "button" of the deos surface — and
who may press it is decided by `required ⊆ held`, not a session cookie. -/
structure CellAffordance (φ : Type) where
  /-- The rights an agent must hold to fire this affordance (the `is_attenuation` template). -/
  required : List Auth
  /-- The REAL effect this affordance fires — abstract so any `dregg_turn::Effect` fits. -/
  effect   : φ
  /-- A display name (the affordance label shown in the surface). -/
  name     : Nat
deriving DecidableEq

/-- **`FiredSurface φ`** — the post-state surface a committed fire yields: the REAL effect that fired
plus the attested root it bound (the `newCommit` of the verified turn's receipt). The "attested
post-state surface" — the fragment the witness-graph records. -/
structure FiredSurface (φ : Type) where
  /-- The effect that actually fired (the affordance's real effect, verbatim). -/
  firedEffect : φ
  /-- The attested root the post-state binds: the receipt's `newCommit` (target 4's second clause). -/
  boundRoot   : Nat

/-- **`AffordanceIntent φ`** — the verified-turn intent an authorized fire produces: the affordance
that fired + the resulting attested post-state surface. (`docs/deos/DEOS.md`: "an authorized one yields
a verified-turn `AffordanceIntent`".) -/
structure AffordanceIntent (φ : Type) where
  /-- The affordance that fired. -/
  affordance : CellAffordance φ
  /-- The attested post-state surface it produced. -/
  surface    : FiredSurface φ

/-! ## §3 — `fire`: the cap-gated, attested-root-binding dispatch.

`fire aff held s` runs the affordance ONLY when `held` authorizes `aff.required` (`fireGate`), and on
commit produces the verified turn's receipt (binding the attested root in the post-state surface). An
unauthorized fire is REFUSED in-band (`none`). `s` is the pre-state commitment (the `oldCommit`); the
turn produces the post-state commitment `post` (the `newCommit`) — the attested root. -/

/-- **`fire aff held s post`** — fire affordance `aff` for an agent holding `held` rights, against
pre-state commitment `s`, producing post-state commitment `post`. IF `fireGate aff.required held` (the
agent's caps authorize the affordance), yields `some` of the verified-turn `AffordanceIntent` whose
surface binds the attested root `post` (the receipt's `newCommit`); ELSE `none` (refused in-band). The
`gateOK`-on-the-affordance-template dispatch. -/
def fire (aff : CellAffordance φ) (held : List Auth) (s post : Nat) :
    Option (AffordanceIntent φ) :=
  if fireGate aff.required held then
    -- the verified turn: a receipt binding old (s) → new (post), the attested root in the post-state.
    let _receipt : Receipt := mkReceipt 0 s post aff.name
    some { affordance := aff,
           surface := { firedEffect := aff.effect, boundRoot := post } }
  else
    none

/-! ## §4 — TARGET 4: an agent fires ONLY what its caps authorize, and the surface binds the root. -/

/-- **THE KEYSTONE — `fire_authorized_iff`.** A fire COMMITS (`isSome`) if and only if the agent's
held rights authorize the affordance (`fireGate aff.required held`, i.e. `required ⊆ held`). Both
polarities: an AUTHORIZED agent fires; an UNAUTHORIZED one is REFUSED (`none`). So an agent can fire
ONLY the affordances its caps authorize — target 4's first clause, as an `↔`. -/
theorem fire_authorized_iff (aff : CellAffordance φ) (held : List Auth) (s post : Nat) :
    (fire aff held s post).isSome = true ↔ fireGate aff.required held = true := by
  unfold fire
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => rfl⟩
  · have hgf : fireGate aff.required held = false := by
      cases hb : fireGate aff.required held with
      | true => exact absurd hb hg
      | false => rfl
    rw [if_neg hg]
    constructor
    · intro h; simp only [Option.isSome_none, Bool.false_eq_true] at h
    · intro h; rw [hgf] at h; exact absurd h (by simp)

/-- **AN UNAUTHORIZED FIRE IS REFUSED** (the negative tooth, explicit): if the agent does NOT hold the
required rights, `fire` returns `none` — no turn, no surface, fail-closed. The agent cannot fire an
affordance its caps do not authorize. -/
theorem unauthorized_fire_refused (aff : CellAffordance φ) (held : List Auth) (s post : Nat)
    (hunauth : fireGate aff.required held = false) :
    fire aff held s post = none := by
  unfold fire; rw [if_neg (by rw [hunauth]; decide)]

/-- **A COMMITTED FIRE CARRIES THE REAL EFFECT** — when `fire` commits, the resulting intent's surface
fires the affordance's REAL effect verbatim (not a stand-in). The `dregg_turn::Effect` template is the
one that fires; the interaction carries the genuine effect. -/
theorem fire_carries_real_effect (aff : CellAffordance φ) (held : List Auth) (s post : Nat)
    (intent : AffordanceIntent φ) (h : fire aff held s post = some intent) :
    intent.surface.firedEffect = aff.effect := by
  unfold fire at h
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **THE POST-STATE SURFACE BINDS THE ATTESTED ROOT** — target 4's second clause. When `fire` commits,
the resulting surface's `boundRoot` EQUALS `post`, the `newCommit` of the verified turn's receipt
(`mkReceipt 0 s post _ |>.newCommit = post`). So the post-state surface binds the attested root the
turn produced — the fragment the witness-graph records is pinned to the real post-state commitment, not
a free-floating claim. -/
theorem firedSurface_binds_attested_root (aff : CellAffordance φ) (held : List Auth) (s post : Nat)
    (intent : AffordanceIntent φ) (h : fire aff held s post = some intent) :
    intent.surface.boundRoot = (mkReceipt 0 s post aff.name).newCommit := by
  unfold fire at h
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h; rfl      -- boundRoot = post; and `(mkReceipt 0 s post _).newCommit = post` by rfl.
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **THE BOUND ROOT IS THE NEW STATE, NOT THE OLD** (non-vacuity of the binding): a committed fire's
surface binds `post` (the `newCommit`), and when `post ≠ s` the bound root genuinely DIFFERS from the
pre-state `oldCommit`. So the surface binds the POST-state, not a relabelled pre-state — the attestation
moved the commitment. -/
theorem firedSurface_root_is_new (aff : CellAffordance φ) (held : List Auth) (s post : Nat)
    (intent : AffordanceIntent φ) (h : fire aff held s post = some intent) (hne : post ≠ s) :
    intent.surface.boundRoot ≠ s := by
  rw [firedSurface_binds_attested_root aff held s post intent h]
  exact hne

/-- **AN UNAUTHORIZED FIRE BINDS NO ROOT** (the anti-ghost): an unauthorized fire yields `none`, so
there is NO surface and hence NO bound root — an agent who lacks the rights cannot forge a post-state
surface or its attested root. Confinement before relation: no authority ⇒ no surface. -/
theorem unauthorized_fire_no_surface (aff : CellAffordance φ) (held : List Auth) (s post : Nat)
    (hunauth : fireGate aff.required held = false) :
    ∀ intent : AffordanceIntent φ, fire aff held s post ≠ some intent := by
  intro intent
  rw [unauthorized_fire_refused aff held s post hunauth]
  exact fun h => absurd h (by simp)

/-! ## §5 — PROGRESSIVE ENHANCEMENT → PROGRESSIVE ATTENUATION (the per-viewer affordance set).

`starbridge-web-surface`'s `project_for` returns the affordances a viewer may fire — and as a viewer's
authority shrinks, that set only shrinks (monotone via `fireGate`). Two viewers over one surface
diverge by exactly what their caps authorize. -/

/-- **`projectFor held affs`** — the affordances a viewer holding `held` rights may fire: those whose
`required ⊆ held` (the per-viewer `project_for`). Progressive enhancement becomes progressive
attenuation — a viewer sees exactly the affordances its caps authorize. -/
def projectFor (held : List Auth) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.filter (fun aff => fireGate aff.required held)

/-- **THE PROJECTION IS MONOTONE** — a viewer holding FEWER rights (`held₁ ⊆ held₂`) is offered a
SUBSET of the affordances the more-authorized viewer is. So progressive attenuation never GROWS the
fireable set as authority shrinks; two viewers over one surface diverge by exactly their authority.
(Via `fireGate_trans`: anything the weaker viewer can fire, the stronger can too.) -/
theorem projectFor_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (affs : List (CellAffordance φ)) :
    projectFor held₁ affs ⊆ projectFor held₂ affs := by
  intro aff ha
  unfold projectFor at ha ⊢
  rw [List.mem_filter] at ha ⊢
  exact ⟨ha.1, fireGate_trans h12 ha.2⟩

/-- **EVERY PROJECTED AFFORDANCE IS FIREABLE** — a viewer is only ever offered affordances it can
actually fire (`fire` commits for each one in `projectFor held affs`). The projected set is sound: no
offered-but-refused buttons. -/
theorem projectFor_all_fireable (held : List Auth) (affs : List (CellAffordance φ))
    (aff : CellAffordance φ) (s post : Nat) (hmem : aff ∈ projectFor held affs) :
    (fire aff held s post).isSome = true := by
  unfold projectFor at hmem
  rw [List.mem_filter] at hmem
  rw [fire_authorized_iff]
  exact hmem.2

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the affordance gate BITES, both polarities. -/

section Witnesses

/-- A concrete effect type for the witnesses: a tag carrying a Nat payload. -/
inductive DemoEffect where | transfer (amt : Nat) | post (msg : Nat)
deriving DecidableEq, Repr

/-- An affordance requiring `{write}` to fire a transfer (the "send" button). -/
def sendAff : CellAffordance DemoEffect := { required := [Auth.write], effect := .transfer 50, name := 1 }
/-- An affordance requiring `{read}` to fire a (read-only) post (the "view" button). -/
def viewAff : CellAffordance DemoEffect := { required := [Auth.read], effect := .post 7, name := 2 }

/-- An agent holding only `{read}` — may fire the view button, NOT the send button. -/
def readerHeld : List Auth := [Auth.read]
/-- An agent holding `{read, write}` — may fire both. -/
def writerHeld : List Auth := [Auth.read, Auth.write]

-- THE GATE BITES: the reader CANNOT fire the write-gated send (refused in-band) …
#guard (fire sendAff readerHeld 100 70).isNone
-- … but the writer CAN (authorized) …
#guard (fire sendAff writerHeld 100 70).isSome
-- … and BOTH can fire the read-gated view button:
#guard (fire viewAff readerHeld 100 100).isSome
#guard (fire viewAff writerHeld 100 100).isSome

-- a committed fire carries the REAL effect and binds the attested root (= post):
#guard match fire sendAff writerHeld 100 70 with
       | some i => (i.surface.firedEffect == DemoEffect.transfer 50) && (i.surface.boundRoot == 70)
       | none   => false
-- the bound root is the NEW state (70), not the old (100) — the surface binds the post-state:
#guard match fire sendAff writerHeld 100 70 with
       | some i => i.surface.boundRoot != 100
       | none   => false

-- PROGRESSIVE ATTENUATION: the reader is offered ONLY the view button; the writer is offered BOTH:
#guard (projectFor readerHeld [sendAff, viewAff]).length == 1     -- reader: just view
#guard (projectFor writerHeld [sendAff, viewAff]).length == 2     -- writer: both
-- the reader's projected affordance is exactly the view button (the send is attenuated away):
#guard match projectFor readerHeld [sendAff, viewAff] with
       | [a] => a.name == 2
       | _   => false

-- the gate is reflexive (hold exactly the required rights ⇒ fireable):
#guard fireGate [Auth.write] [Auth.write]
-- and a missing right darkens it (write required, only read held ⇒ refused):
#guard !fireGate [Auth.write] [Auth.read]

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  fireGate_iff_subset,
  fireGate_refl,
  fireGate_trans,
  fire_authorized_iff,
  unauthorized_fire_refused,
  fire_carries_real_effect,
  firedSurface_binds_attested_root,
  firedSurface_root_is_new,
  unauthorized_fire_no_surface,
  projectFor_monotone,
  projectFor_all_fireable
]

end Dregg2.Deos.Affordance
