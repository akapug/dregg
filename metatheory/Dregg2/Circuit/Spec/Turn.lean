/-
# Dregg2.Circuit.Spec.Turn — declarative turn spec layer (the list-fold over per-action steps).

This is the GENERIC turn-composition spec: a committed `List FullActionA` turn is characterized
recursively as an all-or-nothing chain of per-action steps. The nil turn is identity; a cons is an
existential intermediate state stepped by the head action, then the tail turn.

The headline bridge is **`execFullTurnA_iff_turnSpec`**: IF each single action's executor commit
`execFullA s a = some s'` is equivalent to a parameterized per-action spec `step s a s'`, THEN the
whole-turn executor `execFullTurnA` is equivalent to `turnSpec step` — proved by induction on the
action list, mirroring `execFullTurnA`'s definitional fold.

`turnSpec_append` carries the same associativity shape as `execFullTurnA_append` (the forest
flattening rests on this). Concrete per-action specs (mint, burn, balance, …) plug in as `step`;
this module stays executor-generic.

Import `TurnExecutorFull` only.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.Turn

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Per-action step type and the turn fold. -/

/-- A single-action declarative step: pre-state, one `FullActionA`, post-state. -/
abbrev ActionStep := RecChainedState → FullActionA → RecChainedState → Prop

/-- **`turnSpec`** — the declarative all-or-nothing turn: fold a list of actions through `step`.
Nil is identity; cons requires an intermediate state. -/
def turnSpec (step : ActionStep) (s : RecChainedState) : List FullActionA → RecChainedState → Prop
  | [], s' => s = s'
  | a :: rest, s' => ∃ s1, step s a s1 ∧ turnSpec step s1 rest s'

/-! ## §2 — Structural lemmas (mirror `execFullTurnA` / `execFullTurnA_append`). -/

/-- **`turnSpec_nil`** — the empty turn is the identity step. -/
theorem turnSpec_nil (step : ActionStep) (s : RecChainedState) : turnSpec step s [] s := rfl

/-- **`turnSpec_singleton`** — a one-action turn reduces to that action's step. -/
theorem turnSpec_singleton (step : ActionStep) (s s' : RecChainedState) (a : FullActionA) :
    turnSpec step s [a] s' ↔ step s a s' := by
  simp only [turnSpec]
  constructor
  · intro ⟨s1, hstep, hnil⟩
    subst hnil
    exact hstep
  · intro hstep
    exact ⟨s', hstep, rfl⟩

/-- **`turnSpec_append`** — concatenating turns is running the prefix then the suffix (the
`execFullTurnA_append` associativity shape for the declarative layer). -/
theorem turnSpec_append (step : ActionStep) (s : RecChainedState) (xs ys : List FullActionA)
    (s' : RecChainedState) :
    turnSpec step s (xs ++ ys) s' ↔ ∃ s1, turnSpec step s xs s1 ∧ turnSpec step s1 ys s' := by
  induction xs generalizing s with
  | nil =>
      simp only [List.nil_append, turnSpec]
      constructor
      · intro h; exact ⟨s, rfl, h⟩
      · intro ⟨s1, heq, hys⟩
        subst heq
        exact hys
  | cons a rest ih =>
      simp only [List.cons_append, turnSpec]
      constructor
      · intro ⟨s1, hhead, htail⟩
        rcases (ih s1).mp htail with ⟨s2, hrest, hys⟩
        exact ⟨s2, ⟨s1, hhead, hrest⟩, hys⟩
      · intro ⟨s2, ⟨s1, hhead, hrest⟩, hys⟩
        refine ⟨s1, hhead, ?_⟩
        exact (ih s1).mpr ⟨s2, hrest, hys⟩

/-! ## §3 — The executor bridge (generic, per-action step assumed). -/

/-- **`execFullTurnA_iff_turnSpec`** — the headline: whole-turn executor ⟺ declarative turn spec,
given a per-action executor⟺step equivalence. Proved by induction on the action list, mirroring
`execFullTurnA`'s fold. -/
theorem execFullTurnA_iff_turnSpec (step : ActionStep)
    (hstep : ∀ s a s', execFullA s a = some s' ↔ step s a s') :
    ∀ s acts s', execFullTurnA s acts = some s' ↔ turnSpec step s acts s' := by
  intro s acts
  induction acts generalizing s with
  | nil =>
      intro s'
      simp only [execFullTurnA, turnSpec]
      constructor
      · intro h; simpa using h
      · intro h; simpa using h
  | cons a rest ih =>
      intro s'
      simp only [execFullTurnA, turnSpec]
      constructor
      · intro h
        cases ha : execFullA s a with
        | none => simp [execFullTurnA, ha] at h
        | some s1 =>
          simp only [execFullTurnA, ha] at h
          refine ⟨s1, (hstep s a s1).mp ha, ?_⟩
          exact (ih s1 s').mp h
      · intro ⟨s1, hstep', hrest⟩
        have ha : execFullA s a = some s1 := (hstep s a s1).mpr hstep'
        simp only [execFullTurnA, ha]
        exact (ih s1 s').mpr hrest

/-! ## §4 — Axiom-hygiene tripwires. -/

#assert_axioms turnSpec_nil
#assert_axioms turnSpec_singleton
#assert_axioms turnSpec_append
#assert_axioms execFullTurnA_iff_turnSpec

end Dregg2.Circuit.Spec.Turn