/-
# Dregg2.Exec.GuardedHole — the WEAK guarded hole, first-class + PROVED.

The guarded-hole study (`metatheory/docs/GUARDED-HOLES-METATHEORY.md`) split the idea two ways:
- the **WEAK guarded hole** — a `Pred` guard on a late-filled slot (an `EventualRef`), discharged at
  fill time — is ELEGANT, composes, and is *mostly already code* ("predicated pipelining");
- the **STRONG guarded hole** — a hole in a conservation/authority position (an UNDETERMINED δ / a
  lazy SHAPE) — is a flaw in the *idea*, and is INEXPRESSIBLE in dregg (no non-zero-δ primitive; safe
  by inexpressibility), so it is deliberately NOT built here.

This module builds the weak one as a first-class object. The shape is the study's verdict
**"determination is EAGER, witness is LAZY"**: a contribution's SHAPE — which field, whose write,
under which `guard` — is fixed when the hole is created; only the VALUE (`n`, the resolved
`Dregg2.Exec.ConditionalTurn` `EventualRef` output slot) arrives later. The keystone
`holeFill_binds_in_circuit` is the genuinely-new theorem with teeth named by the study: a fill cannot
commit without binding BOTH its δ (the exact `stateStep` write) AND its guard (the discharged `Pred`)
into the proven post-state — the predicate analogue of the cap-bridge, the SAME forcing principle as
the light-client-trust goal (you can only trust what the proof FORCES).

The three reused pieces are all already code (the study's "3 of 4"):
- guard as a domain-restrictor subobject — `predStateStepGuarded` (`PredAlgebra.lean:580`);
- the fill is the guarded `put` (commits the `stateStep` write iff the guard admits) — same def;
- fail-closed on a violating value — `predStateStepGuarded_violation_fails`.
-/
import Dregg2.Exec.PredAlgebra

namespace Dregg2.Exec.Holes

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Exec.EffectsState (stateStep fieldOf)

/-- **`GuardedHole`** — a late-filled slot carrying the `Pred`-caveats a future filler MUST discharge.
The EAGER SHAPE: `field` (the slot the fill writes — an `EventualRef`'s landing field), `actor` (who
fills), `target` (the cell written), and `guard` (the predicate promised up front). Only the VALUE is
lazy. -/
structure GuardedHole where
  field  : FieldName
  actor  : CellId
  target : CellId
  guard  : List PredCaveat

/-- **`fillGuarded h s n`** — install the late-arriving value `n` (the resolved `EventualRef` output)
into the hole. THE FILL IS `predStateStepGuarded` — the guarded `put`: it commits the underlying
`stateStep` write IFF every `Pred`-caveat of `h.guard` admits the `(actor, old, n)` transition.
Fail-closed: a value violating the guard does NOT fill. This is the once-installed partial section of
the slot, defined only over the guard's admitting subdomain. -/
def fillGuarded (h : GuardedHole) (s : RecChainedState) (n : Int) : Option RecChainedState :=
  predStateStepGuarded h.guard s h.field h.actor h.target n

/-- **`holeFill_binds_in_circuit` — THE KEYSTONE (the study's genuinely-new theorem with teeth).**
A successful guarded fill BINDS both legs into the committed post-state `s'`:
- its **δ** — the post-state is EXACTLY the underlying `stateStep` write (no hidden mutation), and
- its **guard** — every `Pred`-caveat of the hole was discharged (`predCaveatsAdmit = true`).
So a hole CANNOT be filled without committing its effect AND the predicate it promised. The "lazy
witness over an eager shape" closes SAFELY — the late value is admitted only on the terms the hole
fixed up front. This is the predicate analogue of the cap-bridge and the same forcing principle as the
light-client-trust goal. -/
theorem holeFill_binds_in_circuit (h : GuardedHole) {s s' : RecChainedState} {n : Int}
    (hfill : fillGuarded h s n = some s') :
    stateStep s h.field h.actor h.target (.int n) = some s'
    ∧ predCaveatsAdmit h.guard s.kernel h.field h.target n = true :=
  ⟨predStateStepGuarded_eq hfill, predStateStepGuarded_admits hfill⟩

/-- **`holeFill_rejects_guard_violation` — the NEGATIVE TOOTH (fail-closed).** A value that violates
the hole's guard does NOT fill: the late witness cannot escape the eager shape the hole fixed. -/
theorem holeFill_rejects_guard_violation (h : GuardedHole) (s : RecChainedState) (n : Int)
    (hviol : predCaveatsAdmit h.guard s.kernel h.field h.target n = false) :
    fillGuarded h s n = none :=
  predStateStepGuarded_violation_fails h.guard s h.field h.actor h.target n hviol

/-! ### Non-vacuity — a concrete guarded hole whose guard is TWO-VALUED (admits one value, rejects
another), and whose fill concretely fails on the violating value (the tooth FIRES, not vacuous). -/

/-- A concrete hole on slot `"v"` guarded by `vCaveat` (the `PredAlgebra` policy: admits `50`,
rejects `55`). -/
def demoHole : GuardedHole := { field := "v", actor := 0, target := 0, guard := [vCaveat] }

/-- A concrete bare chained state (the all-zero `kbare` kernel, empty log). -/
def demoState : RecChainedState := { kernel := kbare, log := [] }

-- The guard is genuinely two-valued on this hole (NOT trivially true):
#guard (predCaveatsAdmit demoHole.guard demoState.kernel demoHole.field demoHole.target 50)           -- admits 50
#guard (predCaveatsAdmit demoHole.guard demoState.kernel demoHole.field demoHole.target 55) == false  -- REJECTS 55
-- …and the fill concretely fails on the violating value — the negative tooth FIRES:
#guard (fillGuarded demoHole demoState 55).isNone

#assert_axioms holeFill_binds_in_circuit
#assert_axioms holeFill_rejects_guard_violation

end Dregg2.Exec.Holes
