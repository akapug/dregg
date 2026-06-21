/-
# Metatheory.PolisViability — the ∀-opaque public option-space, as a decidable bounded game.

gpt5.5's answer to the crux (`docs/POLIS-HYPERPROPERTY-FRONTIER.md` Q2): the politician's
"`viable_options B`" must be measured over `B`'s PUBLIC option-space — what `B` can still lawfully
do — never over `B`'s private controller (the `∀`-opacity result is non-negotiable). The right
object is a **bounded public winning region**: `B` has a public legal strategy guaranteeing its
floor within `k` steps against adversarial scheduling. This is svenvs `cwithin … B` lifted to a
two-player game; with finite public moves/responses it is **decidable** (Bool), hence governable.
Domination = that region is empty (`Foreclosed`) — the generalized exit-foreclosure as a GAME,
not a single trajectory. (Pull it onto the unified `UTrace` of `PolisTrace` with
`(viabilityBar Ar k).pullback projConfig`.)
-/
import Metatheory.Polis

namespace Metatheory.PolisViability

open Metatheory.Polis

variable {Config Move : Type}

/-- A PUBLIC arena: the decidable floor, the subject's legal public moves (finite), and the
adversary's legal responses to each (finite). Everything is PUBLIC and interior-free — the
arena is the public rules, not anyone's private intent. -/
structure Arena (Config Move : Type) where
  floorOk : Config → Bool
  enabledMoves : Config → List Move
  advReact : Config → Move → List Config

/-- **`viableWithinB` — the bounded public winning region (Bool, governable).** `B` can GUARANTEE
its floor within `k` public steps iff the floor already holds, OR `B` has a legal move after which,
for EVERY legal adversary response, `B` can still guarantee it within `k-1`. The ∃-move / ∀-response
alternation IS the game — `B`'s public strategy against adversarial scheduling. -/
def viableWithinB (Ar : Arena Config Move) : Nat → Config → Bool
  | 0,     C => Ar.floorOk C
  | k + 1, C => Ar.floorOk C ||
      (Ar.enabledMoves C).any (fun m => (Ar.advReact C m).all (fun C' => viableWithinB Ar k C'))

/-- `B`'s bounded option-space is **viable** at `C` (it can still reach its floor). -/
def Viable (Ar : Arena Config Move) (k : Nat) (C : Config) : Prop := viableWithinB Ar k C = true

/-- … and **foreclosed** when it is not — the option-space domination, public and decidable. -/
def Foreclosed (Ar : Arena Config Move) (k : Nat) (C : Config) : Prop := viableWithinB Ar k C = false

instance (Ar : Arena Config Move) (k : Nat) (C : Config) : Decidable (Viable Ar k C) :=
  inferInstanceAs (Decidable (viableWithinB Ar k C = true))
instance (Ar : Arena Config Move) (k : Nat) (C : Config) : Decidable (Foreclosed Ar k C) :=
  inferInstanceAs (Decidable (viableWithinB Ar k C = false))

/-- **`viabilityBar` — the option-space CaptureBar.** The politician's domination — driving `B`'s
public option-space below its bounded floor — is barred EXACTLY when `B`'s bounded winning region is
empty (`Foreclosed`), DECIDABLE from the public arena alone, with NO interior inspection. This is
gpt5.5's `viable_options B` realized: the generalized exit-foreclosure as a two-player public game.
-/
def viabilityBar (Ar : Arena Config Move) (k : Nat) :
    CaptureBar Config (fun C => Foreclosed Ar k C) where
  badShape := fun C => Foreclosed Ar k C
  publicDecidable := fun C => inferInstanceAs (Decidable (viableWithinB Ar k C = false))
  loadBearing := fun _ h => h
  leastRestrictive := fun _ h => h

/-! ### Non-vacuity: a discriminating arena — recovery by decrement, budget 5. -/

/-- Distance-to-home arena: `floorOk C := C = 0`, the move recovers by one (adversary cannot
prevent it here — a clean witness). -/
def demoArena : Arena Nat Unit where
  floorOk C := C == 0
  enabledMoves _ := [()]
  advReact C _ := [C - 1]

/-- A subject 3 steps out keeps its bounded exit within budget 5 (3 → 2 → 1 → 0). -/
example : Viable demoArena 5 3 := by decide
/-- A subject 10 steps out is foreclosed at budget 5 — domination detected from the public game. -/
example : Foreclosed demoArena 5 10 := by decide
/-- And the bar fires exactly there. -/
example : (viabilityBar demoArena 5).badShape 10 := by show Foreclosed demoArena 5 10; decide
example : ¬ (viabilityBar demoArena 5).badShape 3 := by show ¬ Foreclosed demoArena 5 3; decide

end Metatheory.PolisViability
