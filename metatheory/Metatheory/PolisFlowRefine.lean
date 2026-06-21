/-
# Metatheory.PolisFlowRefine — the multi-trace politician, governed by the DEPLOYED Büchi game.

gpt5.5's "full CaptureBar / FlowRefine frontier": the politician composes lawful moves into
domination, and for the FLOW/POLICY fragment the question "does A's online behaviour stay
within the floor flow F?" is the reactive-rung refinement `A ≤ᶠ F` — which dregg DECIDES,
**sound + complete**, by a σ-free simulation (Büchi / DupSim) game
(`Dregg2.Deos.FlowRefine.decideRefines_iff`, the dregg analogue of Pradic's Thm 1.4). So a
flow-refinement capture-shape is a CONCRETE `CaptureBar` whose `badShape` is publicly DECIDABLE
with NO interior inspection — govern trace-shape, not motive, with a *deployed decision
procedure* rather than a hand-rolled predicate. This is the first weld of the temporal-politics
frontier onto the deployed substrate; the broader interleaved-multi-agent hyperproperty family
remains the named research object.
-/
import Metatheory.Polis
import Dregg2.Tactics
import Dregg2.Deos.FlowRefine

namespace Metatheory.PolisFlowRefine

open Metatheory.Polis Dregg2.Deos.FlowAlgebra Dregg2.Deos.FlowRefine

/-- A flow `A` **violates the floor flow** `F` iff its online behaviour escapes `F`'s — it does
NOT refine `F` in the reactive simulation order. (The floor `F` is the polis's permitted flow;
a politician strategy that escapes it is the flow-capture.) -/
def ViolatesFlowFloor (F A : Proc) : Prop := ¬ (A ≤ᶠ F)

/-- The publicly-checkable bad-shape: the deployed decision procedure returns `false`. -/
def flowBadShape (F A : Proc) : Prop := decideRefines A F = false

instance (F A : Proc) : Decidable (flowBadShape F A) :=
  inferInstanceAs (Decidable (decideRefines A F = false))

/-- Bad-shape ⇔ floor-violation — the deployed `decideRefines_iff` (sound + complete) carried
to the polis: zero false positives (a barred flow really escapes the floor) and zero misses
(every escaping flow is barred). -/
theorem flowBadShape_iff_violates (F A : Proc) :
    flowBadShape F A ↔ ViolatesFlowFloor F A := by
  unfold flowBadShape ViolatesFlowFloor
  rw [← decideRefines_iff]
  cases decideRefines A F <;> simp

/-- **`flowCaptureBar` — a CONCRETE CaptureBar over the DEPLOYED flow-refinement order.** The
politician's flow/policy capture (escaping the floor flow `F`) is barred EXACTLY when it occurs
and is DECIDABLE from the public flow alone (no motive) — the abstract `CaptureBar` interface
inhabited by a deployed Büchi-game decision (`decideRefines`), sound + complete by
`decideRefines_iff`. -/
def flowCaptureBar (F : Proc) : CaptureBar Proc (ViolatesFlowFloor F) where
  badShape := flowBadShape F
  publicDecidable := fun A => inferInstanceAs (Decidable (decideRefines A F = false))
  loadBearing := fun A h => (flowBadShape_iff_violates F A).mp h
  leastRestrictive := fun A h => (flowBadShape_iff_violates F A).mpr h

-- The constitution's flow-refinement decision tool, re-pinned: deployed, sound + complete,
-- kernel-clean. The reactive-rung politician question is a DECISION, not a hope.
#assert_axioms Dregg2.Deos.FlowRefine.decideRefines_iff

end Metatheory.PolisFlowRefine
