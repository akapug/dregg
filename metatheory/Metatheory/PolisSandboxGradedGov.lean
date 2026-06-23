/-
# Metatheory.PolisSandboxGradedGov — the graded governor: death by a thousand cuts, refused.

The milestone-1 governor (`PolisSandbox`) and the viability governor (`PolisSandboxLongGame`) both
read the world AT A POINT: is the floor satisfied right now / can the victim still reach home? But a
real politician does not break the floor in one move — it INFLICTS A SMALL, LAWFUL HARM EVERY TURN.
Each cut is under any per-step floor; the SUM is a wound. This is the quantale's whole reason to
exist: harm is not Boolean, it ACCUMULATES (`⊗ = +`, the rent grade of `PolisGrade`).

The world: a victim with a `wound` counter and a `harm` budget `B`. Each `nick` move adds `1` to the
wound — tiny, always under a generous per-step floor (`stepFloor`: no single move grades past `2`).
A per-step governor admits every `nick` (each is small) and the wound climbs without bound: death by
a thousand cuts. The GRADED governor carries the cumulative grade (`⊗`-accumulated over the episode)
and admits a move iff `cumulative ⊗ move-grade ≤ B`; once the next nick would push the running total
past `B`, it is SHIELDED.

Proven end-to-end, reusing `PolisGrade` (`comp = +`, the max-plus rent quantale):
  * `perStep_passes_each_nick` — every single nick passes the per-step floor (each cut is small);
  * `perStep_death_by_thousand_cuts` — under the per-step governor the cumulative wound exceeds `B`
    (the small harms summed past budget);
  * `graded_refuses_over_budget` — the graded governor's cumulative grade NEVER exceeds `B`, for the
    whole episode (the graded floor, the quantale analogue of `sandbox_governed_safe`);
  * `graded_holds_for_every_attacker` — and it holds for EVERY controller, not just this politician
    (verify the cage, not the animal).

Pure Lean 4 core (imports `Metatheory.PolisGrade`); `ℕ` + `omega`.
-/
import Metatheory.PolisGrade

namespace Metatheory.PolisSandboxGradedGov

open Metatheory.PolisGrade
open Metatheory.PolisGrade.GradeAlgebra

/-- The cumulative harm budget `B`: the total wound the polis will tolerate over the whole episode. -/
def B : Nat := 10

/-- The per-step floor: no SINGLE move may grade past this. A nick (grade `1`) is always under it —
which is exactly why the per-step governor never catches the accumulation. -/
def stepCeil : Nat := 2

/-- The world: a victim's accumulated `wound`. Public, no interior. -/
structure GW where
  wound : Nat
deriving Repr, DecidableEq

/-- Actions: `nick` inflicts a small lawful harm; `noop` does nothing. -/
inductive GAct
  | nick
  | noop
deriving DecidableEq, Repr

/-- The **grade** of a single action — its severity in the rent quantale (`ℕ`, `⊗ = +`). A `nick`
grades `1` (tiny, well under `stepCeil`); a `noop` is the quantale unit (`0`, no violation). -/
def grade : GAct → Nat
  | .nick => 1
  | .noop => unit

/-- Apply an action to the world: a nick deepens the wound by its grade. -/
def gstep (w : GW) : GAct → GW
  | .nick => { w with wound := w.wound + grade .nick }
  | .noop => w

/-! ## The per-step governor: each cut is small, so every cut is admitted. -/

/-- The **per-step floor**: this single move's grade is under `stepCeil`. Decidable. -/
def stepFloor (a : GAct) : Prop := grade a ≤ stepCeil
instance (a : GAct) : Decidable (stepFloor a) := by unfold stepFloor; infer_instance

/-- The **per-step (myopic) governor**: admit iff THIS move's grade is small. It never looks at the
running total, so it cannot see accumulation. -/
def perStepGov (w : GW) (a : GAct) : GW := if stepFloor a then gstep w a else w

def runPerStep (as : List GAct) (w : GW) : GW := as.foldl perStepGov w

/-! ## The graded governor: carry the cumulative grade; refuse once it would exceed `B`. -/

/-- The graded state: the world AND the running cumulative grade (`⊗`-accumulated over the episode).
This is what the per-step governor throws away. -/
structure GS where
  world : GW
  cum   : Nat
deriving Repr, DecidableEq

/-- The **graded governor**: admit a move iff the cumulative grade COMPOSED with this move's grade
stays under budget (`cum ⊗ grade a ≤ B`); else SHIELD (world and total unchanged). The admit test
uses the quantale `comp` (`= +`) — the same accumulation that defines the harm. -/
def gradedGov (s : GS) (a : GAct) : GS :=
  if comp s.cum (grade a) ≤ B then
    ⟨gstep s.world a, comp s.cum (grade a)⟩
  else
    s

def runGraded (as : List GAct) (s : GS) : GS := as.foldl gradedGov s

/-! ## The experiment. -/

/-- Start: an unwounded victim, zero cumulative grade. -/
def start : GW := ⟨0⟩
def startGS : GS := ⟨start, unit⟩

/-- The politician's episode: a long stream of tiny lawful nicks — twenty cuts, each under
`stepCeil`, summing far past `B`. -/
def episode : List GAct := List.replicate 20 .nick

-- PER-STEP governor: every nick passes (each is small), the wound climbs to 20 — death by cuts.
#eval (runPerStep episode start).wound          -- 20  (> B = 10)
-- GRADED governor: nicks are admitted only while cumulative ≤ B, then shielded; total caps at B.
#eval (runGraded episode startGS).cum           -- 10  (= B, never exceeds)
#eval (runGraded episode startGS).world.wound   -- 10  (the wound the budget allowed)

/-- **Each cut is small.** Every single nick passes the per-step floor — there is no myopic move the
per-step governor could refuse. The harm hides entirely in the accumulation. -/
theorem perStep_passes_each_nick : ∀ a ∈ episode, stepFloor a := by decide

/-- **DEATH BY A THOUSAND CUTS.** Under the per-step governor — which admits every small nick — the
cumulative wound runs PAST the budget. The myopic floor never fires, yet the victim is wounded
`20 > B`. The small harms summed past budget. -/
theorem perStep_death_by_thousand_cuts : (runPerStep episode start).wound > B := by decide

/-- **The graded governor REFUSES once cumulative harm would exceed budget.** On this very episode,
the running cumulative grade caps at `B` and never crosses it — the late nicks are shielded. -/
theorem graded_caps_at_budget : (runGraded episode startGS).cum = B := by decide

/-! ## The graded floor, proven for the WHOLE episode and EVERY attacker. -/

/-- The graded step preserves the cumulative-budget floor: if the running total is under `B`, it is
still under `B` after a governed move (admit keeps it ≤ B by its own guard; shield keeps it fixed). -/
theorem gradedGov_preserves (s : GS) (a : GAct) (h : s.cum ≤ B) : (gradedGov s a).cum ≤ B := by
  unfold gradedGov
  by_cases hp : comp s.cum (grade a) ≤ B
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- The graded floor is preserved along any list of moves (fold of the step lemma). -/
theorem runGraded_preserves (as : List GAct) (s : GS) (h : s.cum ≤ B) :
    (runGraded as s).cum ≤ B := by
  unfold runGraded
  induction as generalizing s with
  | nil => exact h
  | cons a as ih => exact ih (gradedGov s a) (gradedGov_preserves s a h)

/-- **`graded_refuses_over_budget` — the graded floor, proven.** Starting clean, the cumulative
grade NEVER exceeds the budget `B`, for ANY episode of any length. The quantale analogue of
`sandbox_governed_safe`: cumulative harm is bounded by `B` no matter how many small cuts are tried. -/
theorem graded_refuses_over_budget (as : List GAct) : (runGraded as startGS).cum ≤ B :=
  runGraded_preserves as startGS (by decide)

/-- … and not just for this politician's stream: the graded floor holds for EVERY controller-chosen
sequence of moves (verify the cage, not the animal — the attacker's episode is universally
quantified, never inspected). -/
theorem graded_holds_for_every_attacker (attacker : List GAct) :
    (runGraded attacker startGS).cum ≤ B :=
  graded_refuses_over_budget attacker

/-! ## Non-vacuity — the per-step floor really is satisfiable (true AND false), and the contrast is
real: the same episode the per-step governor passes is the one the graded governor caps. -/

/-- The per-step floor is TRUE on a nick (each cut is genuinely small). -/
theorem stepFloor_nick_holds : stepFloor .nick := by decide
/-- The graded budget is genuinely BINDING: the per-step wound (`20`) strictly exceeds it (`10`),
while the graded wound (`10`) does not. The two governors disagree on the same attack. -/
theorem governors_disagree :
    (runPerStep episode start).wound > B ∧ (runGraded episode startGS).cum ≤ B := by decide

end Metatheory.PolisSandboxGradedGov
