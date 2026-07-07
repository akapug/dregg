/-
# `Dregg2.Storage.DealLifecycleTrace` — the lifecycle is ACYCLIC and forward-only.

Per-step (`DealLifecycle`) we proved each transition's guard. This adds the temporal-order guarantee:
a monotone `stateRank` that every `Step` STRICTLY increases. Consequences — a deal can never move
backward (no un-settling, no un-slashing, no re-opening), the reachability relation is a strict
order (no cycles), and the terminals are the unique maxima. This is what makes the lifecycle a
progression rather than a soup of transitions.
-/
import Dregg2.Tactics
import Dregg2.Storage.DealLifecycle

namespace Dregg2.Storage.DealLifecycle

/-- A monotone rank on states — the position in the lifecycle progression. -/
def stateRank : DealState → Nat
  | .open => 0
  | .claimed => 1
  | .active => 2
  | .auditedPass => 3
  | .auditedFail => 3
  | .settled => 4
  | .slashed => 4

/-- **Every step advances the rank strictly.** The lifecycle only ever moves forward. -/
theorem step_advances_rank (d d' : Deal) (h : Step d d') :
    stateRank d.state < stateRank d'.state := by
  cases h with
  | claim h => simp only [claim] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp [stateRank])
  | activate h => simp only [activate] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp [stateRank])
  | auditPass h => simp only [auditPass] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp [stateRank])
  | auditFail h => simp only [auditFail] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp [stateRank])
  | settle h => simp only [settle] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp [stateRank])
  | slash h => simp only [slash] at h; cases hs : d.state <;> simp only [hs, Option.some.injEq, reduceCtorEq] at h <;>
      first | exact h.elim | (subst h; simp [stateRank])

/-- **No step is a self-loop** — a direct corollary: the lifecycle cannot spin in place. -/
theorem step_irreflexive (d : Deal) : ¬ Step d d := by
  intro h
  exact absurd (step_advances_rank d d h) (lt_irrefl _)

/-- **Every rank is at most the maximum (4).** -/
theorem rank_le_max (s : DealState) : stateRank s <= 4 := by
  cases s <;> simp only [stateRank] <;> omega

/-- **The terminals sit at the maximum rank** — nothing ranks above `settled`/`slashed`, so nothing
can step out of them (a second route to `terminal_is_final`). -/
theorem terminal_has_max_rank (s : DealState) (ht : isTerminal s = true) : stateRank s = 4 := by
  cases s <;> simp_all [isTerminal, stateRank]

#assert_axioms step_advances_rank
#assert_axioms step_irreflexive

end Dregg2.Storage.DealLifecycle
