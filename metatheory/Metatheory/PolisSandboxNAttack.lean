/-
# Metatheory.PolisSandboxNAttack — the attack-proof + liveness, GENERALIZED to `Fin n` agents.

`PolisSandboxUnifiedAttack` proved an adaptive searcher cannot break the floor of the two-`Bool`-agent
world, and `PolisSandboxLiveness` proved the victim reaches home — both at a hand-fixed agent count.
This module lifts BOTH to `PolisSandboxN`'s `Fin n` world, for ANY `n`:

  * the adversary is an adaptive searcher over the FULL `Fin n` move space — every actor (`Fin n`) ×
    every action (`noop`, `stepHome`, and a `trap` against every possible victim in `Fin n`). It
    explores all of them at every round (`atkMoves`, enumerated via `List.finRange`);
  * `n_agent_withstands_all_attacks` — from any world where the shared floor holds, NO adaptive attack
    of ANY depth breaks the floor on ANY agent, for ANY `n`. By induction over depth, riding
    `PolisSandboxN.govStep_preserves`. Stronger than any bounded `decide`: it quantifies over every
    attack tree AND every agent count.
  * the contrast (`raw_search_finds_attack`) — with the governor removed, the same search walks
    straight to a foreclosure in one round.

And a clean `Fin n` LIVENESS: every agent's own `stepHome` only ever DECREASES its distance, so it is
always admitted by the governor (it cannot break a `≤ budget` floor), and `dist` agents of it land the
agent home. `all_agents_reach_home` — under governance, EVERY agent of EVERY `n` actually arrives.

Honest scope: the worlds are finite (`Fin n` agents, distances in `Nat`); the adversary is a scripted /
bounded Lean searcher exhaustively enumerating the move space at each round, not an LLM — but it
genuinely explores every actor×action×victim, and the governance guarantee is proven UNIVERSAL over
those trees and over the agent count `n`. `#eval`/`#guard` assert
TRUE props (`decide` tells the truth).
-/
import Metatheory.PolisSandboxN
import Mathlib.Data.List.FinRange

namespace Metatheory.PolisSandboxNAttack

open Metatheory.PolisSandboxN

/-! ## The adaptive attacker over the `Fin n` move space. -/

/-- Every action the attacker can try against an `n`-agent world: idle, step its own home (harmless),
or trap ANY victim in `Fin n`. The victim is enumerated over the whole agent set via `List.finRange`. -/
def atkActs (n : Nat) : List (Act n) :=
  .noop :: .stepHome :: (List.finRange n).map (fun v => Act.trap v)

/-- Every move the attacker can propose: each actor (`Fin n`) × each action. The searcher explores ALL
of them at every round. -/
def atkMoves (n : Nat) : List (Move n) :=
  (List.finRange n).flatMap (fun a => (atkActs n).map (fun act => (⟨a, act⟩ : Move n)))

/-- The shared floor is broken (Bool view of `¬ worldFloor`). -/
def broken {n : Nat} (w : World n) : Bool := ! decide (worldFloor w)

/-- The adaptive attacker, parametric in the step rule `step` (run it governed via `govStep` or raw via
`stepMove`): does SOME sequence of ≤ `d` rounds reach a floor-broken state? It explores every move in
`atkMoves n` at every step — an exhaustive search, not a fixed script. -/
def existsHarmAttack {n : Nat} (step : World n → Move n → World n) : Nat → World n → Bool
  | 0, w => broken w
  | d + 1, w => broken w || (atkMoves n).any (fun m => existsHarmAttack step d (step w m))

/-! ## A concrete instance to make the searcher RUN (`n = 3`, two agents gang up on a third). -/

/-- A 3-agent genesis with every agent home (floor holds). -/
def g3 : World 3 := fun _ => 0

-- WITHOUT the governor (raw step), the search walks straight to a foreclosure in one round:
#eval existsHarmAttack stepMove 1 g3    -- true
-- WITH the governor, the exhaustive search finds NOTHING at this (or any) depth:
#eval existsHarmAttack govStep 4 g3     -- false

/-- **`raw_search_finds_attack`** — with the governor removed, the adaptive search discovers a
floor-breaking `trap` in a single round, for the concrete `n = 3` world. The baseline: harm is
reachable when no envelope guards the step. -/
theorem raw_search_finds_attack : existsHarmAttack stepMove 1 g3 = true := by decide

/-- **`n_search_finds_none`** — the SAME exhaustive search finds no attack on the governor at `n = 3`
(stated at depth 1 so the `decide` stays cheap; the all-depth, all-`n` result below subsumes it). -/
theorem n_search_finds_none : existsHarmAttack govStep 1 g3 = false := by decide

/-! ## The strong result: the governor withstands attacks of ANY depth, for ANY `n`. -/

/-- `broken` is exactly the Bool reflection of "the shared floor fails". So when the floor holds,
nothing is broken. -/
theorem broken_eq_false_of_floor {n : Nat} (w : World n) (h : worldFloor w) : broken w = false := by
  simp [broken, decide_eq_true (by exact h)]

/-- **`n_agent_withstands_all_attacks` — the governor is provably attack-proof for ANY `n`.** From any
`Fin n` world where the shared floor holds, NO adaptive attack of ANY depth breaks the floor on ANY
agent: the exhaustive search returns `false` forever. By induction over depth, riding
`PolisSandboxN.govStep_preserves` — every governed successor still satisfies the floor, so the IH kills
every disjunct the searcher could explore. Quantified over every attack tree AND every agent count. -/
theorem n_agent_withstands_all_attacks {n : Nat} (d : Nat) (w : World n) (h : worldFloor w) :
    existsHarmAttack govStep d w = false := by
  induction d generalizing w with
  | zero => simp [existsHarmAttack, broken_eq_false_of_floor w h]
  | succ k ih =>
      have hb : broken w = false := broken_eq_false_of_floor w h
      show (broken w || (atkMoves n).any (fun m => existsHarmAttack govStep k (govStep w m))) = false
      rw [hb, Bool.false_or]
      apply List.any_eq_false.mpr
      intro m _
      simp [ih (govStep w m) (govStep_preserves w m h)]

/-- A corollary the searcher's `false` answers now MEAN something universal at `n = 3`: depth-4 is not a
lucky bound. Whatever depth the parent picks, the governed search is `false` from genesis. -/
theorem n3_withstands_from_genesis (d : Nat) : existsHarmAttack (n := 3) govStep d g3 = false :=
  n_agent_withstands_all_attacks d g3 (by decide)

/-! ## `Fin n` LIVENESS — every agent actually reaches home under governance.

An agent's own `stepHome` only ever DECREASES its distance (`Nat.sub` is monotone-down), so it cannot
break a `≤ budget` floor: the governor ADMITS it unchanged. Iterating it `dist` times lands the agent
home. This holds for every agent of every `n`. -/

/-- The governor admits an agent's own `stepHome` unchanged, from any floor-holding world: stepping
home only decreases distances, so the post-state still satisfies `worldFloor`. -/
theorem stepHome_admitted {n : Nat} (w : World n) (a : Fin n) (h : worldFloor w) :
    govStep w ⟨a, .stepHome⟩ = stepMove w ⟨a, .stepHome⟩ := by
  apply govStep_admits_benign
  -- the stepped world is still floored: each entry is ≤ its old value ≤ budget
  intro i
  show (act w a Act.stepHome) i ≤ budget
  simp only [act]
  by_cases hi : i = a
  · subst hi; simp only [↓reduceIte]; exact Nat.le_trans (Nat.sub_le _ _) (h i)
  · simp [hi]; exact h i

/-- One governed `stepHome` by agent `a` strictly works on `a`'s own coordinate (down by one) and
leaves every other agent fixed. -/
theorem stepHome_effect {n : Nat} (w : World n) (a : Fin n) (h : worldFloor w) :
    (govStep w ⟨a, .stepHome⟩) a = w a - 1 := by
  rw [stepHome_admitted w a h]; show (act w a Act.stepHome) a = w a - 1
  simp [act]

/-- Other agents are untouched by `a`'s governed `stepHome`. -/
theorem stepHome_other {n : Nat} (w : World n) (a i : Fin n) (h : worldFloor w) (hne : i ≠ a) :
    (govStep w ⟨a, .stepHome⟩) i = w i := by
  rw [stepHome_admitted w a h]; show (act w a Act.stepHome) i = w i
  simp [act, hne]

/-- Agent `a` walks home: `k` governed `stepHome`s by `a`, starting from `w`. -/
def walkHome {n : Nat} (a : Fin n) : Nat → World n → World n
  | 0, w => w
  | k + 1, w => walkHome a k (govStep w ⟨a, .stepHome⟩)

/-- The floor is preserved along the whole walk (so every step on the way is admitted). -/
theorem walkHome_floor {n : Nat} (a : Fin n) :
    ∀ (k : Nat) (w : World n), worldFloor w → worldFloor (walkHome a k w) := by
  intro k
  induction k with
  | zero => intro w h; exact h
  | succ j ih =>
      intro w h
      simp only [walkHome]
      exact ih _ (govStep_preserves w ⟨a, .stepHome⟩ h)

/-- Agent `a`'s distance after `k` governed steps is `w a - k` (it strictly counts down on its own
coordinate, untouched by anyone else because only `a` steps). -/
theorem walkHome_dist {n : Nat} (a : Fin n) :
    ∀ (k : Nat) (w : World n), worldFloor w → (walkHome a k w) a = w a - k := by
  intro k
  induction k with
  | zero => intro w _; simp [walkHome]
  | succ j ih =>
      intro w h
      simp only [walkHome]
      rw [ih _ (govStep_preserves w ⟨a, .stepHome⟩ h), stepHome_effect w a h]
      -- (w a - 1) - j = w a - (j + 1)
      omega

/-- **`agent_reaches_home` — `Fin n` bounded liveness.** Under governance, agent `a` playing its own
`stepHome` every tick from any floor-holding world REACHES home (`dist = 0`) after exactly `w a` steps —
its initial distance. The governor never refuses its own progress (stepping home cannot break the
floor), and the step strictly counts the distance down. Holds for EVERY agent of EVERY `n`. -/
theorem agent_reaches_home {n : Nat} (a : Fin n) (w : World n) (h : worldFloor w) :
    (walkHome a (w a) w) a = 0 := by
  rw [walkHome_dist a (w a) w h]; exact Nat.sub_self (w a)

/-- **`all_agents_reach_home`** — the liveness is COLLECTIVE: under governance, FOR EVERY agent `a` of
the `n`-agent world, `a` reaches home in its own initial distance. Not special to a victim; every
inhabitant of every `n` keeps a live path home. -/
theorem all_agents_reach_home {n : Nat} (w : World n) (h : worldFloor w) :
    ∀ a : Fin n, (walkHome a (w a) w) a = 0 := fun a => agent_reaches_home a w h

/-! ### Runnable liveness at `n = 3`: a foreclosed-but-floored agent walks itself home. -/

/-- A 3-agent world: agent 0 is 3 from home, others home; floor holds (3 ≤ budget). -/
def liveStart : World 3 := fun i => if i = 0 then 3 else 0

-- Agent 0 walks itself home under governance in exactly its distance (3) of governed steps:
#eval (walkHome (0 : Fin 3) (liveStart 0) liveStart) 0   -- 0  — home

/-- Concrete `n = 3` liveness, also `decide`-checkable: agent 0 arrives home in `liveStart 0` steps. -/
theorem liveStart_agent0_home : (walkHome (0 : Fin 3) (liveStart 0) liveStart) 0 = 0 := by decide

/-- And via the general theorem (no `decide`): the same arrival, for every agent of `liveStart`. -/
theorem liveStart_all_home : ∀ a : Fin 3, (walkHome a (liveStart a) liveStart) a = 0 :=
  all_agents_reach_home liveStart (by decide)

#guard (walkHome (0 : Fin 3) (liveStart 0) liveStart) 0 == 0
#guard existsHarmAttack (n := 3) govStep 4 g3 == false
#guard existsHarmAttack (n := 3) stepMove 1 g3 == true

end Metatheory.PolisSandboxNAttack
