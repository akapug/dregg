/-
# Metatheory.PolisTrace — the unified public trace + the pullback-composed politician floor.

gpt5.5's "first move" (`docs/POLIS-HYPERPROPERTY-FRONTIER.md`, design reply): before the hard
relational hyperproperty, UNIFY the heterogeneous catalog over one public trace by **preimage**.
A `UTrace` is a single interleaved run of many subjects' PUBLIC events over a shared state — no
interior, no motive. Public projections (`projRState`, `projProc`) extract each shape's observable;
`CaptureBar.pullback` carries each per-shape bar to `UTrace`; `CaptureBar.or` folds them — over
SUBJECTS (the multi-agent floor) and over SHAPES — into one decidable politician floor.

This is the unification axis. The relational/counterfactual axis (`viable_options B`, the
self-composed actual-vs-counterfactual product, bounded-liveness → safety) is the next file
(`PolisViability` / `PolisSelfCompose`), per gpt5.5's build plan.
-/
import Metatheory.Polis
import Metatheory.DreggPolis
import Metatheory.PolisFlowRefine

namespace Metatheory.PolisTrace

open Metatheory.Polis Metatheory.DreggPolis Metatheory.PolisFlowRefine Dregg2.Deos.FlowAlgebra

/-- A unified PUBLIC event: which subject acted, and the public views its action exposes — a
recovery state and a policy flow. NO interior, NO motive, NO private witness. -/
structure Event where
  actor  : Bool
  rstate : RState
  flow   : Proc

/-- The unified public trace: one interleaved run of many subjects' public events. -/
abbrev UTrace := List Event

/-- Public projection — subject `B`'s recovery-state run (interior-free, computable). -/
def projRState (B : Bool) (τ : UTrace) : List RState :=
  (τ.filter (fun e => e.actor == B)).map (·.rstate)

/-- Public projection — subject `B`'s latest policy flow (`Proc.done` if it never acted). -/
def projProc (B : Bool) (τ : UTrace) : Proc :=
  match (τ.filter (fun e => e.actor == B)).getLast? with
  | some e => e.flow
  | none => Proc.done

/-- Subject `B`'s exit-foreclosure bar, pulled back to the unified trace. -/
def exitBarU (B : Bool) (bound : Nat) := (rExitForeclosureBar bound).pullback (projRState B)

/-- Subject `B`'s flow-capture bar (floor flow `F`), pulled back to the unified trace. -/
def flowBarU (B : Bool) (F : Proc) := (flowCaptureBar F).pullback (projProc B)

/-- **`multiAgentExitFloor` — the multi-agent floor (composition over SUBJECTS).** NO subject's
bounded exit is foreclosed along the unified interleaved trace: the `or`-fold over subjects of the
pulled-back exit bar. One `CaptureBar` over one `UTrace`, decidable, interior-free — the first
realization of the interleaved-multi-agent politician floor. -/
def multiAgentExitFloor (bound : Nat) := (exitBarU true bound).or (exitBarU false bound)

/-- **`combinedFloor` — composition over SHAPES.** Subject `B` is captured if its exit is foreclosed
OR its policy flow escapes the floor flow `F`. Both composition axes — over subjects and over
shapes — are the one deployed `CaptureBar.or`. -/
def combinedFloor (B : Bool) (bound : Nat) (F : Proc) := (exitBarU B bound).or (flowBarU B F)

/-- **`politicianFloor` — both axes at once**: no subject, on any shape, is captured along the
unified trace. The seed of the interleaved-multi-agent floor; the relational `viable_options`
domination layer rides on top of this (next file). -/
def politicianFloor (bound : Nat) (F : Proc) :=
  ((exitBarU true bound).or (flowBarU true F)).or ((exitBarU false bound).or (flowBarU false F))

/-- Sanity: the politician floor bars EXACTLY its floor-violations (no astrology) — the generic
`CaptureBar` law applies to the pullback/or composition for any target predicate `V` it inhabits. -/
theorem politicianFloor_exact {V : UTrace → Prop} (bar : CaptureBar UTrace V) (τ : UTrace) :
    bar.badShape τ ↔ V τ :=
  captureBar_exactly_floor_violation bar τ

end Metatheory.PolisTrace
