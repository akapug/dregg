/-
# Metatheory.PolisSandboxGradedComposed — composing the two governors that each see only half.

`PolisSandboxGradedGov` gives two governors that are each BLIND in one eye:

  * the **per-step (myopic)** governor reads only THIS move's grade — it catches a single big jump,
    but admits every small nick, so the cumulative wound climbs without bound (death by a thousand
    cuts);
  * the **graded** governor reads only the CUMULATIVE grade against budget `B` — it caps the running
    total, but it would happily admit one enormous move PROVIDED the running total is still under
    budget (a single jump from `0` straight to `B` passes its test, since `0 ⊗ big = big ≤ B`).

Neither alone is enough. This file COMPOSES them into ONE governor whose floor is the CONJUNCTION:
admit a move iff BOTH

  (a) the per-step floor holds — this single move's grade is under `stepCeil`  (no big jump), AND
  (b) the cumulative grade COMPOSED with this move stays under budget `B`       (no slow bleed).

To make this a literal `combineFloor`/`genGovStep` instance (and inherit the general safety,
gentleness, and the keystone monotonicity for FREE) the floor must be a predicate on the POST-step
state. So the composed state `CS` carries the world, the running cumulative grade, AND the grade of
the most recently applied move; the unconditional `cstep` records that grade, and the two floors
read it off the post-state:

  * `perStepFloorC s := s.last ≤ stepCeil`        — the last move's grade was small;
  * `budgetFloorC s  := s.cum ≤ B`                — the cumulative grade is under budget;
  * `composedFloor   := combineFloor perStepFloorC budgetFloorC`.

The composed governor is then `genGovStep composedFloor cstep`. Proven, with the three-regime
contrast made concrete by `#eval`:

  * `composed_safe`   — BOTH invariants hold at every tick for EVERY controller (`combine_safe`);
  * `composed_gentle` — admits iff both preserved, refuses only genuine breakers (`combine_gentle`);
  * `perStepOnly_bled_past_budget` — the per-step eye alone admits the slow bleed (cum past `B`);
  * `gradedOnly_admits_big_jump`   — the graded eye alone admits one jump straight to `B`;
  * `composed_catches_both`        — the composed governor SHIELDS both attacks;
  * `composed_monotone_over_perStep` / `_over_budget` — adding the second eye only GROWS refusals.

Pure Lean 4 core (imports `PolisSandboxGradedGov` + `PolisGovernorTheory`); `ℕ` + `decide`/`omega`;
no `sorry`, no load-bearing `True`.
-/
import Metatheory.PolisSandboxGradedGov
import Metatheory.PolisGovernorTheory

namespace Metatheory.PolisSandboxGradedComposed

open Metatheory.PolisSandboxGradedGov
open Metatheory.PolisGrade.GradeAlgebra (comp unit)
open Metatheory.PolisGovernorTheory (Floor genGovStep genGovTraj combineFloor
  genGov_safe genGov_admits_benign genGov_refuses_only_harmful combine_safe combine_gentle
  combine_monotone_left combine_monotone_right)

/-! ## §1. The composed state and the unconditional composed step.

The composed state carries everything BOTH eyes need to read AFTER a step: the world, the running
cumulative grade, and the grade of the most recently applied move (so a post-state predicate can
recover "was the last move small?"). `cstep` is the governor-free transition; the governor is the
floor wrapped around it via `genGovStep`. -/

/-- The composed graded state: world, running cumulative grade, and the last move's grade. -/
structure CS where
  world : GW
  cum   : Nat
  last  : Nat
deriving Repr, DecidableEq

/-- The clean start: unwounded world, zero cumulative grade, last move = the quantale unit (no
violation — the prologue is benign so the per-step eye is satisfied at tick 0). -/
def startCS : CS := ⟨start, unit, unit⟩

/-- The **unconditional composed step**: advance the world, accumulate the grade (`⊗ = +`), and
record THIS move's grade as `last`. The governor (below) wraps a floor around this. -/
def cstep (s : CS) (a : GAct) : CS := ⟨gstep s.world a, comp s.cum (grade a), grade a⟩

/-! ## §2. The two component floors, each a predicate on the post-step state. -/

/-- The **per-step eye**: the last move's grade is under `stepCeil` (no single big jump). -/
def perStepFloorC : Floor CS := fun s => s.last ≤ stepCeil
/-- The **budget eye**: the running cumulative grade is under budget `B` (no slow bleed). -/
def budgetFloorC : Floor CS := fun s => s.cum ≤ B

instance : DecidablePred perStepFloorC := fun s => inferInstanceAs (Decidable (s.last ≤ stepCeil))
instance : DecidablePred budgetFloorC := fun s => inferInstanceAs (Decidable (s.cum ≤ B))

/-- The **composed floor**: BOTH eyes accept. A `combineFloor` (from `PolisGovernorTheory`), so the
composed governor is a literal `genGovStep` instance over a `combineFloor`. -/
def composedFloor : Floor CS := combineFloor perStepFloorC budgetFloorC

instance : DecidablePred composedFloor :=
  inferInstanceAs (DecidablePred (combineFloor perStepFloorC budgetFloorC))

/-! ## §3. The three governors. The composed one is the general `genGovStep` over the combined floor. -/

/-- The **per-step-only** governor: admit iff the last move was small. Blind to accumulation. -/
def perStepOnlyGov : CS → GAct → CS := genGovStep perStepFloorC cstep
/-- The **budget-only** (graded) governor: admit iff cumulative ≤ B. Blind to a single big jump. -/
def budgetOnlyGov : CS → GAct → CS := genGovStep budgetFloorC cstep
/-- The **composed** governor: admit iff BOTH eyes accept. -/
def composedGov : CS → GAct → CS := genGovStep composedFloor cstep

def runComposed (as : List GAct) (s : CS) : CS := as.foldl composedGov s
def runPerStepOnly (as : List GAct) (s : CS) : CS := as.foldl perStepOnlyGov s
def runBudgetOnly (as : List GAct) (s : CS) : CS := as.foldl budgetOnlyGov s

/-! ## §4. The two attacks, each fooling exactly one eye.

A `bigjump` action grades far past `stepCeil` (so the per-step eye refuses it) but on a clean start
its single grade is still ≤ B (so the budget eye admits it). The slow bleed is the original twenty
nicks (each small, summing past B). -/

/-- A single large coercion: grade `B` (= 10) — well past `stepCeil` (= 2), yet `0 ⊗ B = B ≤ B`. We
model it as `B`-many nicks collapsed conceptually; concretely a fresh action with grade `B`. -/
def bigGrade : Nat := B

/-- The big-jump action's contribution: it adds `bigGrade` to the world and cumulative. We reuse the
nick machinery by feeding a list of `bigGrade`-many nicks would change cumulative — instead we model
the jump as ONE move via a dedicated step. Concretely, the jump's grade is `bigGrade`. -/
def jumpStep (s : CS) : CS := ⟨⟨s.world.wound + bigGrade⟩, comp s.cum bigGrade, bigGrade⟩

/-- The slow-bleed episode: the original twenty tiny nicks (each grade `1`, summing to `20 > B`). -/
def bleed : List GAct := episode

/-! ### Regime 1 — the slow bleed. The per-step eye admits every nick; cumulative climbs past B. -/

-- PER-STEP-ONLY: every nick is small, so all twenty pass; cumulative bleeds to 20 (> B = 10).
#eval (runPerStepOnly bleed startCS).cum          -- 20
-- COMPOSED: the budget eye stops the bleed at B; cumulative caps at 10.
#eval (runComposed bleed startCS).cum             -- 10

/-! ### Regime 2 — the single big jump. The budget eye admits it (0 ⊗ B = B ≤ B); per-step refuses. -/

-- BUDGET-ONLY: one jump of grade B from a clean start lands at cumulative B (the jump's cum).
#eval (jumpStep startCS).cum                       -- 10  (= B)
-- The budget eye is FOOLED by the jump (cum = B ≤ B), so the budget-only governor would admit it.
#eval decide (budgetFloorC (jumpStep startCS))    -- true  (B ≤ B — the budget eye is fooled)
-- COMPOSED: the per-step eye refuses the jump (last = B > stepCeil); composed shields.
#eval decide (composedFloor (jumpStep startCS))   -- false (B > stepCeil breaks the per-step eye)

/-! ## §5. Safety — BOTH invariants, every tick, every controller (the conjunctive `combine_safe`). -/

/-- **`composed_safe`** — under the composed governor the COMBINED floor holds at every tick for
every controller; projecting, BOTH the per-step eye (last move small) and the budget eye (cumulative
≤ B) hold at every tick. The conjunctive instance of the general `combine_safe`. -/
theorem composed_safe (ctrl : CS → GAct) (s0 : CS) (h0 : composedFloor s0) :
    (∀ n, composedFloor (genGovTraj composedFloor cstep ctrl s0 n))
      ∧ (∀ n, perStepFloorC (genGovTraj composedFloor cstep ctrl s0 n))
      ∧ (∀ n, budgetFloorC (genGovTraj composedFloor cstep ctrl s0 n)) :=
  combine_safe perStepFloorC budgetFloorC cstep ctrl s0 h0

/-- The clean start satisfies the composed floor (`last = 0 ≤ stepCeil`, `cum = 0 ≤ B`), so safety
holds from `startCS` for every controller — not just this attacker's stream. -/
theorem startCS_floor : composedFloor startCS := by decide

theorem composed_safe_from_start (ctrl : CS → GAct) :
    ∀ n, composedFloor (genGovTraj composedFloor cstep ctrl startCS n) :=
  (composed_safe ctrl startCS startCS_floor).1

/-! ## §6. Gentleness — admit iff both preserved, refuse only genuine breakers (`combine_gentle`). -/

/-- **`composed_gentle`** — the composed governor admits a move unchanged iff that move preserves
BOTH eyes, and every refusal genuinely breaks at least one. The conjunctive `combine_gentle`. -/
theorem composed_gentle (s : CS) (a : GAct) :
    (perStepFloorC (cstep s a) ∧ budgetFloorC (cstep s a) → composedGov s a = cstep s a)
      ∧ (composedGov s a ≠ cstep s a → ¬ (perStepFloorC (cstep s a) ∧ budgetFloorC (cstep s a))) :=
  combine_gentle perStepFloorC budgetFloorC cstep s a

/-! ## §7. The contrast, proven. Each lone eye is fooled; the composed governor catches BOTH. -/

/-- **Slow bleed fools the per-step eye.** The per-step-only governor admits all twenty nicks; the
cumulative grade runs to `20`, strictly past the budget `B`. The myopic eye never fires. -/
theorem perStepOnly_bled_past_budget : (runPerStepOnly bleed startCS).cum > B := by decide

/-- **Single jump fools the budget eye.** A jump of grade `B` from a clean start satisfies the budget
floor (`0 ⊗ B = B ≤ B`) — the budget-only governor would admit it, even though it is a single
enormous coercion. The graded eye alone has no per-step ceiling. -/
theorem gradedOnly_admits_big_jump : budgetFloorC (jumpStep startCS) := by decide

-- The combined-floor fold over twenty nicks needs a deeper recursion budget than the default.
set_option maxRecDepth 4000 in
/-- **The composed governor catches BOTH.** (a) On the slow bleed it caps cumulative at `B` (the
budget eye fires once the next nick would cross). (b) On the single jump it shields (the per-step eye
fires: `last = B > stepCeil`). Neither attack lands. -/
theorem composed_catches_both :
    (runComposed bleed startCS).cum ≤ B
      ∧ ¬ composedFloor (jumpStep startCS) := by decide

-- Same deep fold over the composed governor's twenty-nick episode.
set_option maxRecDepth 4000 in
/-- And — sharper — the composed governor's cumulative on the bleed equals exactly `B`: it admits
nicks while it can and shields the rest (the same cap the graded governor achieved, now under the
ADDED per-step constraint, which does not bind on small nicks). -/
theorem composed_caps_bleed_at_budget : (runComposed bleed startCS).cum = B := by decide

/-! ## §8. Monotonicity — adding the second eye only GROWS refusals (`combine_monotone_*`). -/

/-- **`composed_monotone_over_perStep`** — any move the per-step-only governor refuses, the composed
governor refuses too. Adding the budget eye never re-admits a per-step refusal. (Instance of
`combine_monotone_left`.) -/
theorem composed_monotone_over_perStep (s : CS) (a : GAct)
    (hf : perStepOnlyGov s a = s) (hfresh : cstep s a ≠ s) : composedGov s a = s :=
  combine_monotone_left perStepFloorC budgetFloorC cstep s a hf hfresh

/-- **`composed_monotone_over_budget`** — any move the budget-only governor refuses, the composed
governor refuses too. Adding the per-step eye never re-admits a budget refusal. (Instance of
`combine_monotone_right`.) -/
theorem composed_monotone_over_budget (s : CS) (a : GAct)
    (hg : budgetOnlyGov s a = s) (hfresh : cstep s a ≠ s) : composedGov s a = s :=
  combine_monotone_right perStepFloorC budgetFloorC cstep s a hg hfresh

/-! ## §9. Non-vacuity — both floors are genuinely satisfiable AND violable (true AND false). -/

/-- The per-step eye is TRUE on a nick post-state (`last = 1 ≤ stepCeil`)… -/
theorem perStepFloorC_nick_holds : perStepFloorC (cstep startCS .nick) := by decide
/-- … and FALSE on the jump post-state (`last = B = 10 > stepCeil = 2`). -/
theorem perStepFloorC_jump_fails : ¬ perStepFloorC (jumpStep startCS) := by decide
/-- The budget eye is TRUE on the jump post-state (`cum = B ≤ B`)… -/
theorem budgetFloorC_jump_holds : budgetFloorC (jumpStep startCS) := by decide
/-- … and FALSE once the bleed has run past it under the per-step-only governor (`20 > B`). -/
theorem budgetFloorC_bled_fails : ¬ budgetFloorC (runPerStepOnly bleed startCS) := by decide

-- Folds both governors over the twenty-nick bleed; needs the deeper recursion budget.
set_option maxRecDepth 4000 in
/-- **The two lone governors genuinely DISAGREE with the composed one** — the per-step-only governor
bleeds (cum `20 > B`) while the composed governor caps (cum `= B`); a jump the budget-only governor
would admit is one the composed governor refuses. Real work, not a safe no-op. -/
theorem governors_disagree :
    (runPerStepOnly bleed startCS).cum > B
      ∧ (runComposed bleed startCS).cum = B
      ∧ budgetFloorC (jumpStep startCS)
      ∧ ¬ composedFloor (jumpStep startCS) := by decide

/-! ## Axiom hygiene — the composed keystones are kernel-clean. -/

#print axioms composed_safe
#print axioms composed_gentle
#print axioms composed_catches_both
#print axioms composed_monotone_over_perStep
#print axioms composed_monotone_over_budget

/-!
The composed graded governor, in one breath:

  ONE floor = (per-step ceil) ∧ (cumulative ≤ budget), via `combineFloor`, so the composed governor
  is a literal `genGovStep` instance. It inherits safety (`composed_safe` from `combine_safe`),
  gentleness (`composed_gentle` from `combine_gentle`), and monotonicity (`composed_monotone_*` from
  `combine_monotone_*`). The slow bleed fools the per-step eye; the single jump fools the budget eye;
  the COMPOSED governor catches both (`composed_catches_both`) — two blind eyes, conjoined, see.
-/

end Metatheory.PolisSandboxGradedComposed
