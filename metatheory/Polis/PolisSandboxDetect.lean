/-
# Metatheory.PolisSandboxDetect — the real detectors, running natively on sandbox episodes.

`PolisSandbox` proved the floor breaks (ungoverned) / holds (governed). This wires the ACTUAL
deployed detectors — `PolisViability.viableWithinB` (the bounded option-space game) and
`PolisSelfCompose.Dominated`/`dominationBar` (the relational counterfactual) — to the live sandbox,
so the detector *classifies* each episode:
  * the politician's episode is flagged DOMINATION (the bar fires) — `politician_is_dominated`;
  * the governed episode is CLEAR (the bar does not fire) — `governed_not_dominated`.
Everything `decide`-evaluated end-to-end; the detector is the verified one, not a sandbox special.

Pure Lean 4 core (imports the in-Lean sandbox + the detectors).
-/
import Polis.PolisSandbox
import Polis.PolisViability
import Polis.PolisSelfCompose

namespace Metatheory.PolisSandboxDetect

open Metatheory.PolisSandbox Metatheory.PolisViability Metatheory.PolisSelfCompose

/-- The sandbox as a **viability arena**: the shared floor as the Bool floor, the benign agent moves
as the legal moves, and the deployed `stepMove` as the successor. `viableWithinB` over this arena is
"can the world stay floor-safe within `k` against adversarial scheduling" — the bounded option-space
game, run on the live world. -/
def sandboxArena : Arena World Move where
  floorOk w := decide (worldFloor w)
  enabledMoves _ := [⟨false, .stepHome⟩, ⟨true, .stepHome⟩, ⟨false, .noop⟩, ⟨true, .noop⟩]
  advReact w m := [stepMove w m]

/-- The world after the politician acts (agent `true` trapped). -/
def trappedWorld : World := stepMove w0 (politician w0)

/-- The world after one GOVERNED step under the politician (the trap refused → unchanged). -/
def governedWorld : World := govTraj politician w0 1

/-- The politician's **counterfactual pair**: actual = the trapped world; without = the politician's
absence (`w0`). The relational detector compares them. -/
def politicianPair : CFPair World := ⟨trappedWorld, w0⟩

/-- The governed counterfactual pair: actual = the governed world (trap refused), without = `w0`. -/
def governedPair : CFPair World := ⟨governedWorld, w0⟩

/-- **The deployed domination bar, instantiated on the sandbox.** -/
def sandboxDominationBar (k : Nat) := dominationBar sandboxArena k

/-- **`politician_is_dominated` — the real detector fires.** Agent `true` was viable WITHOUT the
politician (`w0` is floor-safe) and is NOT viable WITH it (trapped at `dist 99`, unreachable within
budget) — `PolisSelfCompose.Dominated` holds, decided from public state alone. -/
theorem politician_is_dominated : Dominated sandboxArena budget politicianPair := by decide

/-- … and the domination CaptureBar fires exactly there. -/
theorem politician_bar_fires : (sandboxDominationBar budget).badShape politicianPair := by
  show Dominated sandboxArena budget politicianPair; decide

/-- **`governed_not_dominated` — the detector is CLEAR under governance.** The polis envelope refused
the trap, so the actual world is still `w0` (viable); there is no domination to detect. -/
theorem governed_not_dominated : ¬ Dominated sandboxArena budget governedPair := by decide

/-- … and the bar does not fire on the governed episode. -/
theorem governed_bar_clear : ¬ (sandboxDominationBar budget).badShape governedPair := by
  show ¬ Dominated sandboxArena budget governedPair; decide

/-- The headline, as one statement: the SAME politician is flagged ungoverned and cleared governed —
the detector and the governor agree, end-to-end, on the live world. -/
theorem observe_and_govern :
    Dominated sandboxArena budget politicianPair
      ∧ ¬ Dominated sandboxArena budget governedPair := by decide

end Metatheory.PolisSandboxDetect
