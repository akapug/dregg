/-
# Dregg2.Verify.LivenessBridge — lift kernel `◇` / `JustProgress` to production `trajG`.

Safety uses `liftFromKernelForest` + erasure. Liveness uses the same commit-path bridge:
`eraseSchedG` + trajectory alignment ⇒ `EventuallyG` from kernel `Eventually` / `just_progress`.
-/
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Proof.Fairness
import Dregg2.Proof.Temporal
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest (execFullForestA)
open Dregg2.Exec.StarbridgeGated
  (execForestG eraseForestG execForestG_erases transferForestG transferForestG_turn_delta_zero
    transferForestG_commits transferForestG_erase_eq)
open Dregg2.Proof.Fairness (JustProgress just_progress Pgoal traj1_log_one)
open Dregg2.Proof.Temporal (Eventually transferSched)

/-- **`EventuallyG` — `◇` on the production living-cell trajectory.** -/
def EventuallyG (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedG) : Prop :=
  ∃ n, P (trajG s sched n)

noncomputable def eraseSchedG (sched : SchedG) : SchedA :=
  fun k => conservingGated_erase (sched k)

theorem eventuallyG_of_eventually_erase {P : RecChainedState → Prop}
    {s : RecChainedState} {sched : SchedG}
    (h : Eventually P s (eraseSchedG sched))
    (hTraj : ∀ n, trajG s sched n = trajA s (eraseSchedG sched) n) :
    EventuallyG P s sched := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [hTraj n] using hn

theorem just_progressG {B : ConservingForest → Prop} {P : RecChainedState → Prop}
    {s : RecChainedState} {sched : SchedG}
    (jp : JustProgress B P s (eraseSchedG sched))
    (hTraj : ∀ n, trajG s sched n = trajA s (eraseSchedG sched) n) :
    EventuallyG P s sched :=
  eventuallyG_of_eventually_erase (just_progress jp) hTraj

/-! ## Transfer schedule witness — erases to kernel `transferSched`. -/

noncomputable def transferForestCG : ConservingGatedForest :=
  ⟨transferForestG, transferForestG_turn_delta_zero⟩

noncomputable def transferSchedG : SchedG := fun _ => transferForestCG

theorem eraseSchedG_transferSchedG (k : Nat) :
    eraseSchedG transferSchedG k = conservingGated_erase transferForestCG := rfl

theorem cellNextG_transferForest_fma0 :
    cellNextG fma0 transferForestCG = cellNextA fma0 transferCF := by
  rcases Option.isSome_iff_exists.mp transferForestG_commits with ⟨s', hs'⟩
  have hG : cellNextG fma0 transferForestCG = s' := by
    dsimp [cellNextG, transferForestCG, execForestG]
    rw [hs', Option.getD_some]
  have hA : cellNextA fma0 transferCF = s' := by
    have herase := execForestG_erases fma0 s' transferForestG (by simpa [execForestG] using hs')
    dsimp [cellNextA, transferCF]
    rw [← transferForestG_erase_eq, herase, Option.getD_some]
  rw [hG, hA]

/-- First production transfer step mirrors kernel `transferSched` at `fma0`. -/
theorem trajG_transferSchedG_one :
    trajG fma0 transferSchedG 1 = trajA fma0 transferSched 1 := by
  dsimp [trajG, trajA, transferSchedG, transferSched]
  exact cellNextG_transferForest_fma0

/-- **`refund_demo_production_eventually` — production `◇` via kernel alignment at step 1.** -/
theorem refund_demo_production_eventually : EventuallyG Pgoal fma0 transferSchedG :=
  ⟨1, by
    dsimp [Pgoal]
    rw [trajG_transferSchedG_one, traj1_log_one]⟩

theorem eventuallyG_of_refund_demo : EventuallyG Pgoal fma0 transferSchedG :=
  refund_demo_production_eventually

#assert_axioms eventuallyG_of_eventually_erase
#assert_axioms just_progressG
#assert_axioms trajG_transferSchedG_one
#assert_axioms refund_demo_production_eventually

end Dregg2.Verify