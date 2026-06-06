/-
# Dregg2.Verify.ChoreographyBridge — blue/red choreography ↔ Hatchery contracts.

* **Blue** (I-confluent) interactions commit per-cell; their invariants are `CellContract.forever`
  safety crowns on `trajG` (`Spec.Choreography.blue_needs_no_hyperedge`).
* **Red** (coupled) interactions project to `Hyperedge` atomic commits
  (`Spec.Choreography.red_projects_to_hyperedge`); operational anchors include `JointCell` CG-5 and
  the gated `launderFullForestG` cross-cell move on `execForestG`.
-/
import Dregg2.Verify.Contract
import Dregg2.Verify.Catalog
import Dregg2.Spec.Choreography
import Dregg2.Spec.Coherence
import Dregg2.Exec.JointCell
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.RecordKernel

namespace Dregg2.Verify

open Dregg2.Boundary
open Dregg2.Spec
open Dregg2.Exec
open Dregg2.Exec.JointCell
open Dregg2.Exec.FullForest (fmaDeleg)

open Dregg2.Exec.FullForestAuth (execFullForestG)
open Dregg2.Exec.StarbridgeGated (execForestG launderFullForestG)
open Production

/-! ## Blue — per-cell `CellContract.forever` on production trajectories. -/

theorem identity_blue_forever (s : RecChainedState) (h : 42 ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, 42 ∈ (trajG s sched n).kernel.revoked :=
  (revokedPersists 42).forever h sched

theorem log_mono_blue_forever (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  log_mono_forever_production s sched

/-! ## Red — coupled commits: hyperedge CG-5 + gated operational teeth. -/

/-- Demo bilateral HTLC swap (the `ClockDAG/Model` witness). -/
def jointDemoSwap : BiTurn :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 42 }

/-- Bilateral HTLC swap: half-edges sum to zero (the operational Σ=0 the hyperedge bridge abstracts). -/
theorem joint_demo_halves_balance :
    halfA jointDemoSwap + halfB jointDemoSwap = 0 := by
  simp [halfA, halfB, jointDemoSwap]

/-- Abstract weave: red interaction binding ⇒ cross-cell conservation (`Spec.Coherence`). -/
/-- Operational red crown: combined asset-0 + asset-1 total is `□` along every `trajG`. -/
theorem red_combined_total_forever (sched : SchedG) :
    ∀ n, cellObsA (trajG fma0 sched n) 0 + cellObsA (trajG fma0 sched n) 1
       = cellObsA fma0 0 + cellObsA fma0 1 :=
  gateAutomaton.forever rfl sched

theorem red_binding_implies_cross_cell_conservation
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {Bal : Type u} [AddCommMonoid Bal] {S : Type u} [Confluence.MergeState S]
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (hred : P.IsRed) {xs : ι → T.Carrier} (b : RedBinding (Bal := Bal) (S := S) P xs) :
    conservedInDomain Domain.crossCell (hyperedgeDeltas b.toHyperedge) :=
  choreography_red_conserves P hred b

#guard (halfA jointDemoSwap + halfB jointDemoSwap == 0)
#guard (recTotalAsset fmaDeleg.kernel 0 + recTotalAsset fmaDeleg.kernel 1 == 112)
#guard ((execFullForestG fmaDeleg launderFullForestG).map
        (fun s => recTotalAsset s.kernel 0 + recTotalAsset s.kernel 1) == some (112 : ℤ))

#assert_axioms identity_blue_forever
#assert_axioms log_mono_blue_forever
#assert_axioms joint_demo_halves_balance
#assert_axioms red_combined_total_forever
#assert_axioms red_binding_implies_cross_cell_conservation

end Dregg2.Verify