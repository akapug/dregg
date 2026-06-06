/-
# Dregg2.Verify.FramesG — gated forest-monotone combinator + erasure-lifted grow lemmas.
-/
import Dregg2.Verify.Frames
import Dregg2.Exec.CellExecutor

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated (DForest execForestG execForestG_erases eraseForestG)

theorem execFullForestG_revoked_subset_grow (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.kernel.revoked ⊆ s'.kernel.revoked := by
  have er := execForestG_erases s s' f h
  exact Dregg2.Apps.Identity.execFullForestA_revoked_grow s s' (eraseForestG f) er

theorem execFullForestG_commitments_grow (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.kernel.commitments ⊆ s'.kernel.commitments := by
  have er := execForestG_erases s s' f h
  exact execFullForestA_commitments_grow s s' (eraseForestG f) er

theorem execFullForestG_nullifiers_grow (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.kernel.nullifiers ⊆ s'.kernel.nullifiers := by
  have er := execForestG_erases s s' f h
  exact execFullForestA_nullifiers_grow s s' (eraseForestG f) er

theorem execFullForestG_logMono (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.log.length ≤ s'.log.length := by
  have er := execForestG_erases s s' f h
  exact execFullForestA_logMono s s' (eraseForestG f) er

theorem cellNextG_carries_rel {α : Type _} (R : α → α → Prop) [Trans R R R]
    (proj : RecChainedState → α)
    (forestGrowG : ∀ (s s' : RecChainedState) (f : DForest),
      execForestG s f = some s' → R (proj s) (proj s'))
    {base : α} {s : RecChainedState} (h : R base (proj s)) (cg : ConservingGatedForest) :
    R base (proj (cellNextG s cg)) := by
  dsimp [cellNextG]
  cases hc : execForestG s cg.val with
  | some s' => simp only [Option.getD_some]
               exact Trans.trans h (forestGrowG s s' cg.val hc)
  | none    => simp only [Option.getD_none]; exact h

attribute [aesop safe apply (rule_sets := [Dregg2])]
  execFullForestG_revoked_subset_grow
  execFullForestG_commitments_grow
  execFullForestG_nullifiers_grow

#assert_axioms execFullForestG_revoked_subset_grow
#assert_axioms execFullForestG_commitments_grow
#assert_axioms execFullForestG_nullifiers_grow
#assert_axioms execFullForestG_logMono
#assert_axioms cellNextG_carries_rel

end Dregg2.Verify