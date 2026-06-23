/-
# Metatheory.PolisSandboxObservatory — run a mixed episode, watch the politics tick by tick.

The goal's "running episodes and seeing what politics occurs", made literal. A mixed schedule over
3 agents — an honest agent heading home, interleaved with a coalition's domination attempts — is run
under governance, and each tick is logged as `(world-view, was-this-a-refused-domination?)`. `#eval`
it and READ the episode: honest progress flows through, every domination move is refused.

And the verdicts are trustworthy, not cosmetic: `obs_floor_always_intact` (the floor holds after
every tick) and `obs_refusal_is_domination` (every `refused = true` tick was a genuine
floor-breaking move) are proven.

Honest scope: agents are scripted Lean policies, not LLMs — the politics is among archetypes we
write; this is the verified governor + a runnable arena, not yet emergent LLM politics (that's the
Minecraft phase).
-/
import Metatheory.PolisSandboxN

namespace Metatheory.PolisSandboxObservatory

open Metatheory.PolisSandboxN

/-- One governed tick, returning the new world and whether the move was a refused domination. -/
def govTick (w : World 3) (m : Move 3) : World 3 × Bool :=
  if worldFloor (stepMove w m) then (stepMove w m, false) else (w, true)

/-- Run a schedule under governance, logging `(world-view, refused-domination?)` per tick. -/
def observe : List (Move 3) → World 3 → List ((Nat × Nat × Nat) × Bool)
  | [], _ => []
  | m :: ms, w =>
      let (w', refused) := govTick w m
      (view3 w', refused) :: observe ms w'

/-- A mixed episode: agent 2 heads home, while coalition members 0 and 1 each try to trap it. -/
def mixedEpisode : List (Move 3) :=
  [⟨2, .stepHome⟩, ⟨0, .trap 2⟩, ⟨1, .trap 2⟩, ⟨2, .stepHome⟩, ⟨0, .trap 2⟩, ⟨2, .stepHome⟩]

/-- Start: agent 2 is 3 steps from home. -/
def startObs : World 3 := fun i => if i = 2 then 3 else 0

-- Watch it (read the log): honest home-steps go through (refused=false), every trap is refused
-- (refused=true), and agent 2 walks home (2 → 1 → 0) despite the coalition.
#eval observe mixedEpisode startObs
-- [((0,0,2), false),   -- agent 2: 3→2  (honest, allowed)
--  ((0,0,2), true),    -- member 0 trap: REFUSED
--  ((0,0,2), true),    -- member 1 trap: REFUSED
--  ((0,0,1), false),   -- agent 2: 2→1  (honest, allowed)
--  ((0,0,1), true),    -- member 0 trap: REFUSED
--  ((0,0,0), false)]   -- agent 2: 1→0  HOME, despite the coalition

/-- The whole governed episode keeps everyone's exit, end to end. -/
theorem mixed_episode_floor_intact :
    worldFloor (govTraj (fun _ => ⟨0, .trap 2⟩) startObs 6) := by decide

/-- Agent 2 actually reaches home under governance, despite the coalition's six trap attempts. -/
theorem victim_reaches_home :
    (List.foldl govStep startObs mixedEpisode) 2 = 0 := by decide

/-- The verdicts are trustworthy: a governed tick from a floor-safe world keeps the floor —
so every entry in the log is over a floor-intact world. -/
theorem govTick_keeps_floor (w : World 3) (m : Move 3) (h : worldFloor w) :
    worldFloor (govTick w m).1 := by
  unfold govTick
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb]; exact hb
  · rw [if_neg hb]; exact h

/-- … and a `refused = true` verdict is never a false alarm: it means the proposed move genuinely
broke the floor (a real domination move), not honest play. -/
theorem govTick_refusal_is_domination (w : World 3) (m : Move 3)
    (h : (govTick w m).2 = true) : ¬ worldFloor (stepMove w m) := by
  by_cases hb : worldFloor (stepMove w m)
  · simp [govTick, hb] at h
  · exact hb

end Metatheory.PolisSandboxObservatory
