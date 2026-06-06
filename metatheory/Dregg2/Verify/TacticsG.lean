/-
# Dregg2.Verify.TacticsG — Hatchery Tier 1 on the gated executor.
-/
import Dregg2.Verify.FramesG
import Dregg2.Exec.CellExecutor

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated (execForestG)
open Lean Elab Tactic

macro "carry_foreverG" Good:term : tactic =>
  `(tactic| refine livingCellG_carries $Good ?hpres _ ?hinit _)

theorem logMonoG_via_tactics (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length := by
  carry_foreverG (fun s' => s.log.length ≤ s'.log.length)
  case hpres =>
    intro s' cg h
    unfold cellNextG
    cases hc : execForestG s' cg.val with
    | none    => simp only [Option.getD_none]; exact h
    | some st => simp only [Option.getD_some]; exact le_trans h (execFullForestG_logMono s' st cg.val hc)
  case hinit => exact le_refl _

theorem revoked_growG_via_tactics (rev0 : List Nat) (s : RecChainedState)
    (hinit : rev0 ⊆ s.kernel.revoked) (sched : SchedG) :
    ∀ n, rev0 ⊆ (trajG s sched n).kernel.revoked := by
  carry_foreverG (fun s' => rev0 ⊆ s'.kernel.revoked)
  case hpres =>
    intro s' cg h
    unfold cellNextG
    cases hc : execForestG s' cg.val with
    | none    => simp only [Option.getD_none]; exact h
    | some st => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestG_revoked_subset_grow s' st cg.val hc)
  case hinit => exact hinit

theorem identity_revoked_foreverG_via_tactics (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked := by
  intro n
  have h := revoked_growG_via_tactics [credNul] s
    (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

#assert_axioms logMonoG_via_tactics
#assert_axioms revoked_growG_via_tactics
#assert_axioms identity_revoked_foreverG_via_tactics

end Dregg2.Verify