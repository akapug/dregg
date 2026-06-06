/-
# Dregg2.Verify.LivenessContract — Hatchery liveness tier (`◇` on `trajG`).

Safety contracts (`CellContract`) carry `□` along `trajG`. Liveness needs van Glabbeek justness
(`Proof/Fairness.lean`) and the CTL just-paths gate (`Proof/CTLLiveness.lean`). This module packages
the honest `◇` fragment: a `LivenessContract` names a goal and discharges it via `just_progress`.

Production `EventuallyG` and the erasure lift live in `LivenessBridge`. Kernel witnesses and the
canonical gated schedules are discharged here.
-/
import Dregg2.Verify.LivenessBridge
import Dregg2.Verify.Contract
import Dregg2.Proof.Fairness
import Dregg2.Proof.CTLLiveness
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.StarbridgeGated
  (logBumpForestG logBumpForestG_turn_delta_zero logBumpForestG_commits logBumpForestG_log_one
    transferSchedG transferForestCG)
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Proof.Temporal (Eventually transferSched)
open Dregg2.Proof.Fairness (Just JustProgress just_progress Pgoal BReg)
open Dregg2.Proof.CTLLiveness (AF_just)

/-- First-class liveness object: a goal discharged by the justness gate (never faked without `Just`). -/
structure LivenessContract where
  Goal : RecChainedState → Prop

namespace LivenessContract

theorem eventually_of_just_progress {B s sched} (L : LivenessContract)
    (jp : JustProgress B L.Goal s sched) :
    Eventually L.Goal s sched :=
  just_progress jp

theorem eventuallyG_of_just_progress {B s schedG} (L : LivenessContract)
    (jp : JustProgress B L.Goal s (eraseSchedG schedG))
    (hTraj : ∀ n, trajG s schedG n = trajA s (eraseSchedG schedG) n) :
    EventuallyG L.Goal s schedG :=
  just_progressG jp hTraj

theorem af_just_of_just_progress {B s} (L : LivenessContract)
    (h : ∀ sched, Just B s sched → JustProgress B L.Goal s sched) :
    AF_just B L.Goal s :=
  fun sched hj => eventually_of_just_progress L (h sched hj)

end LivenessContract

/-- Kernel-forest refund demonstrator — the inhabited `◇` witness from `Fairness`. -/
def refundDemoContract : LivenessContract where
  Goal := Pgoal

theorem refund_demo_kernel_eventually : Eventually Pgoal fma0 transferSched :=
  Dregg2.Proof.Fairness.refund_demo_eventually

/-! ## Production schedule packaging. -/

noncomputable def logBumpForestCG : ConservingGatedForest :=
  ⟨logBumpForestG, logBumpForestG_turn_delta_zero⟩

noncomputable def logBumpSched : SchedG := fun _ => logBumpForestCG

def gatedLogGoal (s : RecChainedState) : Prop := 1 ≤ s.log.length

def gatedLogContract : LivenessContract where
  Goal := gatedLogGoal

example : gatedLogGoal = Pgoal := rfl

theorem trajG_logBump_one : (trajG fma0 logBumpSched 1).log.length = 1 := by
  rcases Option.isSome_iff_exists.mp logBumpForestG_commits with ⟨s', hs'⟩
  dsimp [trajG, cellNextG, logBumpSched, logBumpForestCG, execForestG]
  rw [hs', Option.getD_some, logBumpForestG_log_one hs']

theorem gated_log_eventually : EventuallyG gatedLogGoal fma0 logBumpSched :=
  ⟨1, by
    show 1 ≤ (trajG fma0 logBumpSched 1).log.length
    rw [trajG_logBump_one]⟩

theorem gated_transfer_eventually : EventuallyG Pgoal fma0 transferSchedG :=
  refund_demo_production_eventually

#guard ((trajA fma0 transferSched 1).log.length == 1)
#guard ((execFullForestG fma0 logBumpForestG).map (fun s => s.log.length) == some 1)

#assert_axioms refund_demo_kernel_eventually
#assert_axioms trajG_logBump_one
#assert_axioms gated_log_eventually
#assert_axioms gated_transfer_eventually

end Dregg2.Verify