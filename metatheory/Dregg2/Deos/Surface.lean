/-
# Dregg2.Deos.Surface — a deos window IS a capability (leg 1 of the verified-deos crown).

`docs/deos/DEOS.md` §"the verified-deos program", target 1 (**Surface-as-capability**):

  > `Target::Surface(cell)` is a point on the existing `(target, rights)` gradation; prove a
  > window confers no authority beyond its rights (the same shape as `notifyCap_confers_no_edge`).

This is NOT new mathematics. A deos surface (`Target::Surface(cell)` in
`starbridge-web-surface`) is *literally* a `Dregg2.Authority.Cap.endpoint cell rights` — a point on
the existing capability gradation. So "a window confers no authority beyond its rights" is the
EXISTING `Dregg2.Authority.capAuthConferred` law restated for surfaces, and "a view-only surface
grants no Granovetter introduction" is `Dregg2.Firmament.NotifyAuthority.notifyCap_confers_no_edge`
restated: the SAME `Dregg2.Exec.confersEdgeTo` gate, on a surface cap.

## What is proven (all by REUSE — no surface-local cap algebra)

  * `surfaceConfersExactly` — a `Surface cell rights` confers EXACTLY `rights` (the
    `capAuthConferred` law: a window is its rights and nothing more). The kernel `Cap` IS the deos
    surface; there is no extra authority hiding behind the pixels.
  * `viewSurface_confers_no_edge` — a VIEW-only surface (`[.read]`, the "look, don't touch" window)
    confers NO connectivity edge to its cell (`confersEdgeTo = false`), because `confersEdgeTo`
    requires `write`. So opening a read-only window grants no Granovetter introduction — exactly the
    `notifyCap_confers_no_edge` shape, on a surface. (Contrast: an INTERACTIVE `[.write]` surface DOES
    confer the edge — the distinction is real, `interactiveSurface_confers_edge`.)
  * `notifySurface_confers_no_edge` — a NOTIFY-only surface (the "may ping me, may not drive me"
    window — a live tile that can wake but not message) likewise confers no edge: `notify` is not
    `write`. The async-signal surface is invisible at the connectivity gate.
  * `surface_attenuate_no_amplify` — attenuating a surface to a NARROWER rights set confers a SUBSET
    of the original surface's authority. This IS `Dregg2.Exec.attenuate_subset` (constructor-agnostic,
    a `List.filter` on `keep`), so "downgrade a window to view-only" is provably non-amplifying by the
    EXISTING kernel theorem. (The realization: `starbridge-web-surface`'s `project_for` returns a
    per-viewer attenuated surface — this is the proof that projection cannot amplify.)
  * `viewProjection_drops_write` — projecting an interactive `[.write, .read]` surface to view-only
    keeps `read`, drops `write` (the positive direction, witnessed): the "render a read-only copy for
    a less-authorized viewer" move, on the real lattice.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2` green (LOCAL). NO core-`Auth`/`Cap` edit — every name is the REAL kernel lattice
(`Dregg2.Authority.Cap` / `capAuthConferred` / `Dregg2.Exec.attenuate` / `confersEdgeTo`); the deos
surface is a NAMING of the existing endpoint cap, not a new object.
-/
import Dregg2.Exec.AuthTurn
import Dregg2.Tactics

namespace Dregg2.Deos.Surface

open Dregg2.Authority (Cap Auth Label capAuthConferred)
open Dregg2.Exec (attenuate attenuate_subset confersEdgeTo)

/-! ## §1 — A deos surface IS a kernel capability.

`Target::Surface(cell)` (the `starbridge-web-surface` window target) is a point on the existing
`(target, rights)` gradation. We name it as exactly a `Cap.endpoint cell rights` — NO new constructor,
NO new lattice. The deos "window" is the kernel endpoint cap, viewed as pixels. -/

/-- **`Surface cell rights`** — the capability a deos window IS: a `Cap.endpoint` to `cell` carrying
`rights`. This is a NAMING (a `def`, not a new type) so every surface theorem below reduces to an
existing kernel-`Cap` theorem. A window confers exactly what this cap confers — no pixels add
authority. -/
def Surface (cell : Label) (rights : List Auth) : Cap := Cap.endpoint cell rights

/-- A **view-only** surface: the "look, don't touch" window — read rights only. Confers no edge. -/
def viewSurface (cell : Label) : Cap := Surface cell [Auth.read]

/-- A **notify-only** surface: the "may ping me, may not drive me" live tile — wake rights only.
Confers no edge (a wake is not a message). -/
def notifySurface (cell : Label) : Cap := Surface cell [Auth.notify]

/-- An **interactive** surface: a window the viewer may DRIVE — carries `write`. Confers the edge. -/
def interactiveSurface (cell : Label) : Cap := Surface cell [Auth.write, Auth.read]

/-! ## §2 — A window confers EXACTLY its rights (the `capAuthConferred` law, on a surface). -/

/-- **A SURFACE CONFERS EXACTLY ITS RIGHTS** — for any cell/rights, the authority a deos surface
confers is precisely its `rights` list, nothing more. This IS the `capAuthConferred` law
(`.endpoint _ r ↦ r`); the deos restatement: a window is its rights, and the pixels add no hidden
authority. The bedrock of "the desktop adds ZERO new trust". -/
theorem surfaceConfersExactly (cell : Label) (rights : List Auth) :
    capAuthConferred (Surface cell rights) = rights := rfl

/-- A view-only surface confers exactly `[.read]` — it grants the right to LOOK and nothing else. -/
theorem viewSurface_confers_read (cell : Label) :
    capAuthConferred (viewSurface cell) = [Auth.read] := rfl

/-- A view-only surface does NOT confer `write` — looking is not driving. -/
theorem viewSurface_not_write (cell : Label) :
    Auth.write ∉ capAuthConferred (viewSurface cell) := by
  show Auth.write ∉ [Auth.read]
  decide

/-! ## §3 — NO GRANOVETTER EDGE: a view/notify surface grants no introduction.

The sharpest "a window confers no authority beyond its rights": at the executor's connectivity gate
(`Dregg2.Exec.confersEdgeTo`, the SAME `.any` body the reconstructed `execGraph` reads, which requires
`rights.contains Auth.write`), a VIEW-only or NOTIFY-only surface is INVISIBLE. Opening such a window
is not a message — it grants no edge. This is `notifyCap_confers_no_edge` restated for surfaces. -/

/-- **A VIEW-ONLY SURFACE CONFERS NO EDGE** (the executor-edge tooth, surface form). `confersEdgeTo`
requires `node t` OR (`endpoint t r` ∧ `r.contains write`); a `[.read]` surface has neither, so it
confers no connectivity edge to its cell. Opening a read-only window grants no Granovetter
introduction — exactly the right behaviour: a view is not a message. (Mirror of
`Dregg2.Firmament.NotifyAuthority.notifyCap_confers_no_edge`.) -/
theorem viewSurface_confers_no_edge (cell : Label) :
    confersEdgeTo cell (viewSurface cell) = false := by
  simp [confersEdgeTo, viewSurface, Surface]

/-- **A NOTIFY-ONLY SURFACE CONFERS NO EDGE** — the "may ping me, may not drive me" live tile is also
invisible at the connectivity gate: `notify ≠ write`, so a wake-only surface grants no introduction.
A surface that can wake you but not message you confers no authority over its cell. -/
theorem notifySurface_confers_no_edge (cell : Label) :
    confersEdgeTo cell (notifySurface cell) = false := by
  simp [confersEdgeTo, notifySurface, Surface]

/-- …and an INTERACTIVE (`write`-carrying) surface DOES confer the edge — so the distinction is REAL,
not vacuous: the SAME cell, view-only vs interactive, gives opposite connectivity verdicts. A window
you may DRIVE is a genuine introduction; a window you may only LOOK at is not. -/
theorem interactiveSurface_confers_edge (cell : Label) :
    confersEdgeTo cell (interactiveSurface cell) = true := by
  simp [confersEdgeTo, interactiveSurface, Surface]

/-! ## §4 — NON-AMPLIFICATION: projecting a surface to fewer rights cannot amplify.

`starbridge-web-surface`'s `project_for` returns a per-viewer surface attenuated to the rights that
viewer holds (progressive enhancement → progressive *attenuation*). We model that projection as
`Dregg2.Exec.attenuate`, and its non-amplification IS the EXISTING `attenuate_subset`: the projected
surface confers a SUBSET of the original's authority. No surface-local proof — the kernel theorem,
constructor-agnostic, applies verbatim. -/

/-- **PROJECTING A SURFACE NEVER AMPLIFIES** (the keystone, surface form). Attenuating a surface to
keep only `keep` confers a SUBSET of the original surface's authority. This IS
`Dregg2.Exec.attenuate_subset` (a `List.filter` on `keep`, constructor-agnostic), restated for
surfaces: `project_for` (the per-viewer render) can only SHRINK what a window grants, never grow it.
The proof that the realization's projection is non-amplifying — by the existing kernel theorem. -/
theorem surface_attenuate_no_amplify (keep : List Auth) (cell : Label) (rights : List Auth) :
    capAuthConferred (attenuate keep (Surface cell rights))
      ⊆ capAuthConferred (Surface cell rights) :=
  attenuate_subset keep (Surface cell rights)

/-- **PROJECT-TO-VIEW DROPS `write`, KEEPS `read`** (the positive direction, witnessed): projecting an
interactive `[.write, .read]` surface to keep only `[.read]` confers exactly `[.read]` — the
`write`-right is dropped, the `read`-right retained. The "render a read-only copy for a less-authorized
viewer" move, on the real lattice. So a viewer who holds only `read` sees only a view-only surface,
by construction. -/
theorem viewProjection_drops_write (cell : Label) :
    capAuthConferred (attenuate [Auth.read] (interactiveSurface cell)) = [Auth.read] := by
  simp [attenuate, interactiveSurface, Surface, capAuthConferred]

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the surface distinctions BITE. -/

section Witnesses

/-- A concrete interactive surface on cell `7`: a window the holder may drive (write) and read. -/
def egInteractive : Cap := interactiveSurface 7
/-- A concrete view-only surface on cell `7`: a window the holder may only look at. -/
def egView : Cap := viewSurface 7

-- A surface confers EXACTLY its rights (the window is its rights, no hidden authority):
#guard capAuthConferred (Surface 7 [Auth.read, Auth.write]) == [Auth.read, Auth.write]
#guard capAuthConferred egView == [Auth.read]
-- View/notify surfaces confer NO edge; an interactive surface DOES (the distinction bites):
#guard !(confersEdgeTo 7 egView)
#guard !(confersEdgeTo 7 (notifySurface 7))
#guard (confersEdgeTo 7 egInteractive)
-- Projecting the interactive surface to view-only drops write, keeps read (non-amplifying, witnessed):
#guard capAuthConferred (attenuate [Auth.read] egInteractive) == [Auth.read]
-- …and the projected view-only surface now confers NO edge — projection darkened the introduction:
#guard !(confersEdgeTo 7 (attenuate [Auth.read] egInteractive))
-- the ORIGINAL still confers the edge — projection strictly shrank authority (both polarities):
#guard (confersEdgeTo 7 egInteractive)

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  surfaceConfersExactly,
  viewSurface_confers_read,
  viewSurface_not_write,
  viewSurface_confers_no_edge,
  notifySurface_confers_no_edge,
  interactiveSurface_confers_edge,
  surface_attenuate_no_amplify,
  viewProjection_drops_write
]

end Dregg2.Deos.Surface
