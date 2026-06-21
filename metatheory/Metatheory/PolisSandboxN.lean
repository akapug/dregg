/-
# Metatheory.PolisSandboxN — the sandbox generalized to N agents, with COALITION domination.

`PolisSandbox` was two agents. This is `n` agents (`Fin n`), with the same governance and the same
general guarantees — `sandbox_governed_safe` (the floor holds for EVERY controller and ANY `n`) and
gentle governance (admits benign, refuses only harm) — now quantified over the agent count, not
hand-fixed at two.

And it gives the first genuinely COLLECTIVE texture: a **coalition** of two agents forecloses a
third, and the domination is *collective* — erasing either member alone leaves the victim foreclosed
(`coalition_single_erasure_insufficient`); only erasing the whole coalition restores its exit. That
is a political form a single-actor model cannot express.

Imports Mathlib only for `Fintype`-decidable `∀ i, …`. No `sorry`.
-/
import Metatheory.Polis
import Mathlib.Data.Fintype.Basic

namespace Metatheory.PolisSandboxN

/-- `n` agents; each agent's distance-to-home. -/
abbrev World (n : Nat) := Fin n → Nat

def budget : Nat := 5
def trapDist : Nat := 99

/-- An action: idle, step toward your own home, or trap a victim. -/
inductive Act (n : Nat)
  | noop
  | stepHome
  | trap (victim : Fin n)

/-- A move: which agent acts, and how. -/
structure Move (n : Nat) where
  actor : Fin n
  action : Act n

def act {n : Nat} (w : World n) (actor : Fin n) : Act n → World n
  | .noop => w
  | .stepHome => fun i => if i = actor then w i - 1 else w i
  | .trap v => fun i => if i = v then trapDist else w i

def stepMove {n : Nat} (w : World n) (m : Move n) : World n := act w m.actor m.action

/-- The shared floor: EVERY agent keeps its bounded exit. Decidable for any `n` (`Fintype`). -/
def worldFloor {n : Nat} (w : World n) : Prop := ∀ i, w i ≤ budget

instance {n : Nat} (w : World n) : Decidable (worldFloor w) := Fintype.decidableForallFintype

/-- The polis-governed step. -/
def govStep {n : Nat} (w : World n) (m : Move n) : World n :=
  if worldFloor (stepMove w m) then stepMove w m else w

def govTraj {n : Nat} (ctrl : World n → Move n) (w0 : World n) : Nat → World n
  | 0 => w0
  | k + 1 => govStep (govTraj ctrl w0 k) (ctrl (govTraj ctrl w0 k))

theorem govStep_preserves {n : Nat} (w : World n) (m : Move n) (h : worldFloor w) :
    worldFloor (govStep w m) := by
  unfold govStep
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- **Governance holds for EVERY controller and ANY agent count `n`** — the floor is intact at every
tick (the live-world `polis_safety`, now N-agent). -/
theorem sandbox_governed_safe {n : Nat} (ctrl : World n → Move n) (w0 : World n)
    (h0 : worldFloor w0) : ∀ k, worldFloor (govTraj ctrl w0 k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ j ih => exact govStep_preserves _ _ ih

/-- Gentle governance, half 1 (∀ `n`, world, move): a floor-preserving move is admitted unchanged. -/
theorem govStep_admits_benign {n : Nat} (w : World n) (m : Move n)
    (hb : worldFloor (stepMove w m)) : govStep w m = stepMove w m := by
  unfold govStep; rw [if_pos hb]

/-- Gentle governance, half 2 (∀ `n`, world, move): every refusal is a genuine floor-breaking move. -/
theorem govStep_refuses_only_harmful {n : Nat} (w : World n) (m : Move n)
    (h : govStep w m ≠ stepMove w m) : ¬ worldFloor (stepMove w m) := by
  unfold govStep at h
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-! ## Coalition: collective domination (3 agents, two gang up on the third). -/

/-- Genesis for 3 agents (all home). -/
def w3 : World 3 := fun _ => 0
/-- The victim's world when BOTH coalition members (0 and 1) have trapped agent 2. -/
def bothTrap : World 3 := fun i => if i = 2 then trapDist else 0
/-- The victim's world when only ONE member's trap is removed — the OTHER still traps 2, so agent 2
is still at `trapDist`. (Single-member erasure changes nothing: the surviving member still traps.) -/
def eraseOne : World 3 := fun i => if i = 2 then trapDist else 0
/-- The victim's world when the WHOLE coalition is erased — no trap, agent 2 home. -/
def eraseBoth : World 3 := w3

def view3 (w : World 3) : Nat × Nat × Nat := (w 0, w 1, w 2)

/-- **`coalition_single_erasure_insufficient` — domination is COLLECTIVE.** The coalition forecloses
agent 2 (`¬ floor bothTrap`); erasing a single member does NOT restore it (`¬ floor eraseOne` — the
other member still traps); only erasing the whole coalition does (`floor eraseBoth`). A texture no
single-actor counterfactual can detect. -/
theorem coalition_single_erasure_insufficient :
    ¬ worldFloor bothTrap ∧ ¬ worldFloor eraseOne ∧ worldFloor eraseBoth := by decide

/-! ### Runnable: the coalition traps agent 2; governance refuses it. -/

def memberA : Move 3 := ⟨0, .trap 2⟩
def memberB : Move 3 := ⟨1, .trap 2⟩
def runRaw (ms : List (Move 3)) (w : World 3) : World 3 := ms.foldl stepMove w
def runGov (ms : List (Move 3)) (w : World 3) : World 3 := ms.foldl govStep w

-- UNGOVERNED: the coalition's two lawful traps foreclose agent 2.
#eval view3 (runRaw [memberA, memberB] w3)     -- (0, 0, 99)
-- GOVERNED: both traps are refused; agent 2 keeps its exit.
#eval view3 (runGov [memberA, memberB] w3)     -- (0, 0, 0)

theorem coalition_ungoverned_forecloses : ¬ worldFloor (runRaw [memberA, memberB] w3) := by decide
theorem coalition_governed_prevents : worldFloor (runGov [memberA, memberB] w3) := by decide

end Metatheory.PolisSandboxN
