/-
# Dregg2.Games.AutomataflAir — the ABSTRACT staged board-transition AIR relation, refining `applyTurn`.

⚠ RESOLUTION (see `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`, Class B). "CONNECTED" and "discharges
`air.Refines` for the emitted circuit" below are NOT machine-checked connections to the deployed
circuit. What is PROVEN is about the ABSTRACT `MoveGadget`/`StepGadget` structures (OPAQUE
`resolve`/`step` functions). `MoveSound`/`StepSound` are discharged ONLY for the IDEAL gadgets
(`idealMoveGadget`/`idealStepGadget`), which are LITERALLY the reference stages (sound by `rfl`) —
NOT the deployed `dregg-automatafl/src/{air.rs::automaton_gadget, moves.rs}`, which is never shown
to satisfy them. So `concreteAutomataflAIR_refines` / `automatafl_air_refines_applyTurn_concrete`
discharge `Refines` PARAMETRICALLY over an abstract gadget pair, NOT for the emitted Rust circuit.
The deployed AIR is hand-written Rust with no `@[export]`, no Rust loader, and no emitted artifact
linking it to these Lean gadgets. "The deployed circuit IS this Lean object" is UNPROVEN future
work (Step 1/T4 of the boundary doc).

`Automatafl.lean` states the game-level refinement obligation abstractly (§7):
`BoardTransitionAIR.Refines air` says a HYPOTHESIZED transition AIR admits
`(old, moves, new)` iff `new = applyTurn old moves`, and
`automatafl_air_refines_applyTurn` is the empty-carrier version (the AIR predicate is a
bare hypothesis, `applyTurnAIR` merely witnesses the contract is inhabited). This file
CONNECTS that obligation to the CONCRETE staged circuit
(`dregg-automatafl/src/{air.rs, moves.rs, reference.rs}`): the deployed board-transition
AIR is TRANSLATION VALIDATION — it recomputes `apply_turn(old, moves)` in-circuit through
two composed gadgets and asserts equality with the claimed `new`:

  * the MOVE gadget (`moves.rs::{validate_move, validate_occlusion, write_mid_witnessed}` +
    the D3 fork/collide/survive truth table) — validity filter → conflict-resolve →
    apply-all, producing the intermediate `mid` board;
  * the AUTOMATON gadget (`air.rs::automaton_gadget`) — the four raycasts, the
    per-axis `evaluate_axis` decision, `choose_offset` by score comparison, and the
    one-step relocation, producing `new` from `mid`.

## The mapping (air.rs / moves.rs / reference.rs → this file)

  * **The deployed move gadget** (`write_mid_witnessed ∘ conflict-resolve ∘ validity`) ↦
    `MoveGadget.resolve` — an ABSTRACT function `Board → List Move → Board`. It is opaque
    here because the correctness of its range-gadget / one-hot arithmetization is the
    STARK-soundness remainder, not re-proven; `MoveSound` is the bridge that a satisfying
    witness forces it to equal the reference stages.
  * **The deployed automaton gadget** (`automaton_gadget`) ↦ `StepGadget.step` — an
    ABSTRACT `Board → Board`, with `StepSound` the bridge to `automatonStep`.
  * **The composed translation-validation check** `new == apply_turn(old, moves)` ↦
    `airAutomatafl MG SG old moves new := new = SG.step (MG.resolve old moves)`.
  * **The D3 n=2 selection truth table** (`fork / collide / survive` re-derived from the
    witnessed pattern bits `eq_ff / eq_tt / vac_fa / vac_fb`) ↦ `d3Fork / d3Collide` and
    `conflictResolve_pair`, which PROVES the reference `conflictResolve` on a two-move list
    IS exactly that fork/collide/survive selection — the automatafl analogue of
    `MultiwayTug.legalB_iff` (the circuit's own selection predicate == the model guard).

## What is PROVEN here (the connected refinement — real, non-vacuous, `#assert_axioms`-clean)

`airAutomatafl_iff_applyTurn`: the concrete staged circuit's admission relation IS the graph
of `applyTurn` — the automatafl analogue of `MultiwayTug.airPlay_iff_applyAction`. The
`MoveSound` / `StepSound` bridges are LOAD-BEARING: drop either and the correspondence fails
(it is not a `P → P` tautology). `concreteAutomataflAIR_refines` packages the concrete AIR as
a `BoardTransitionAIR` satisfying `Refines`, and `automatafl_air_refines_applyTurn_concrete`
FEEDS it into the upstream §7 obligation — discharging `air.Refines` for the abstract staged AIR
(parametric in the gadgets; ⚠ NOT the emitted Rust circuit — see the resolution note atop the file)
rather than leaving it a bare hypothesis. `conflictResolve_pair` proves the D3 selection
truth table matches the reference resolution; `airAutomatafl_functional` inherits determinism;
the `idealMoveGadget` / `idealStepGadget` correspondence witnesses (a legal resolved move IS an
`applyTurn` step; a forged `new` is refused) are concrete.

## The OBLIGATION remaining (STATED, honestly, NOT discharged here)

  1. **The deployed STARK's soundness** — that the emitted DSL constraints (range gadgets,
     one-hot reads, the fork/collide/survive gate table) ACCEPT a witness row only if the
     intermediate `mid` board is genuinely `applyMoves (conflictResolve (validity-filter))`
     and `new` is genuinely `automatonStep mid`. Modelled as `MoveSound MG` / `StepSound SG`
     and CARRIED as hypotheses (like `MerkleSound` / `AirSpec` upstream), NOT axioms — so
     `#assert_axioms` stays clean. Discharging them is the deployed circuit's job (the STARK
     soundness of the linking tower + the gadget arithmetizations), not re-proven in this pure
     model.
  2. **The N>2 occlusion + selection** — the concrete gadget is staged D1/D2/D3 (n≤2 moves);
     the general N=11 segmented-indicator occlusion scan and full-SCC resolution are the
     labeled residuals already noted in `Automatafl.lean` §4 and `moves.rs`.
-/
import Dregg2.Games.Automatafl
import Dregg2.Tactics  -- `#assert_axioms` (the build-time axiom-hygiene gate) + Mathlib list simp/tauto

namespace Dregg2.Games.Automatafl

/-! ## 1. The two gadget abstractions + their soundness bridges (the STARK remainder) -/

/-- The deployed MOVE gadget (`moves.rs`): validity filter → conflict-resolve → apply-all,
producing the intermediate `mid` board. Abstract here — its range-gadget / one-hot
arithmetization correctness is the STARK-soundness remainder. -/
structure MoveGadget where
  /-- The in-circuit move-resolution function (`write_mid_witnessed ∘ …`). -/
  resolve : Board → List Move → Board

/-- **`MoveSound MG` — the move gadget's arithmetization soundness (a carried HYPOTHESIS).**
A satisfying witness for the emitted move gadget forces its output to equal the reference
stages: validity filter, then `conflictResolve`, then `applyMoves`. This is the deployed
STARK's soundness for the move gadget — NOT re-proven; carried like `AirSpec` upstream, so
`#assert_axioms` never sees it as an axiom. -/
def MoveSound (MG : MoveGadget) : Prop :=
  ∀ (b : Board) (ms : List Move),
    MG.resolve b ms = applyMoves b (conflictResolve b (ms.filter (moveValidB b)))

/-- The deployed AUTOMATON gadget (`air.rs::automaton_gadget`): raycasts → per-axis decision →
`choose_offset` → one-step relocation. Abstract here for the same reason. -/
structure StepGadget where
  /-- The in-circuit automaton-step function. -/
  step : Board → Board

/-- **`StepSound SG` — the automaton gadget's arithmetization soundness (a carried HYPOTHESIS).**
A satisfying witness forces the gadget output to equal the reference `automatonStep`. -/
def StepSound (SG : StepGadget) : Prop :=
  ∀ b : Board, SG.step b = automatonStep b

/-! ## 2. The concrete staged admission relation + THE CONNECTED REFINEMENT -/

/-- **`airAutomatafl MG SG old moves new` — the CONCRETE staged AIR admission relation.**
The emitted translation-validation circuit admits `(old, moves, new)` when the claimed `new`
is the automaton step (gadget `SG`) of the move-resolved board (gadget `MG`) — the Lean shadow
of `build_d3`'s two composed gadgets (`write_mid_witnessed` ∘ `automaton_on_mid`, each asserting
`new == apply_turn(old, moves)` cell-by-cell). -/
def airAutomatafl (MG : MoveGadget) (SG : StepGadget)
    (old : Board) (moves : List Move) (new : Board) : Prop :=
  new = SG.step (MG.resolve old moves)

/-- **`airAutomatafl_iff_applyTurn` (THE ABSTRACT STAGED REFINEMENT — ⚠ NOT connected to the deployed
Rust circuit; see the resolution note atop this file).** The abstract staged circuit's
admission relation is EXACTLY the graph of `applyTurn` — the automatafl analogue of
`MultiwayTug.airPlay_iff_applyAction`. Both gadget-soundness bridges are LOAD-BEARING: the move
gadget must compute the validity/conflict/apply stages and the automaton gadget must compute the
step; drop either `MoveSound` / `StepSound` and the correspondence no longer closes. NON-vacuous
— the admission relation is the composed staged form, not literally `new = applyTurn`. -/
theorem airAutomatafl_iff_applyTurn (MG : MoveGadget) (SG : StepGadget)
    (hM : MoveSound MG) (hS : StepSound SG)
    (old : Board) (moves : List Move) (new : Board) :
    airAutomatafl MG SG old moves new ↔ new = applyTurn old moves := by
  unfold airAutomatafl applyTurn
  rw [hM, hS]

/-- **`airAutomatafl_functional` (the circuit inherits `applyTurn`'s determinism).** The staged
AIR admits at most one successor per `(old, moves)` — the emitted circuit is functional. -/
theorem airAutomatafl_functional (MG : MoveGadget) (SG : StepGadget)
    (hM : MoveSound MG) (hS : StepSound SG)
    {old : Board} {moves : List Move} {n₁ n₂ : Board}
    (h₁ : airAutomatafl MG SG old moves n₁) (h₂ : airAutomatafl MG SG old moves n₂) :
    n₁ = n₂ :=
  ((airAutomatafl_iff_applyTurn MG SG hM hS old moves n₁).mp h₁).trans
    ((airAutomatafl_iff_applyTurn MG SG hM hS old moves n₂).mp h₂).symm

/-! ## 3. Connection to the §7 obligation — discharging `air.Refines` for the abstract staged AIR
(parametric in the gadgets; ⚠ NOT the emitted Rust circuit — see the resolution note atop the file) -/

/-- The concrete circuit packaged as a `BoardTransitionAIR` (§7): its `admits` is the staged
`airAutomatafl`, NOT the monolithic `applyTurn`. -/
def concreteAutomataflAIR (MG : MoveGadget) (SG : StepGadget) : BoardTransitionAIR where
  admits := airAutomatafl MG SG

/-- **`concreteAutomataflAIR_refines`** — the abstract staged AIR (parametric in the gadgets)
SATISFIES the §7 contract `Refines`. Where `applyTurnAIR` (Automatafl.lean §7) trivially realizes
the contract by `admits := applyTurn`, this proves the STAGED gadget circuit refines it, given the
gadget soundness bridges. ⚠ It is NOT shown for the deployed `air.rs`/`moves.rs` (only the IDEAL
gadgets satisfy the bridges by `rfl`) — see the resolution note atop this file. -/
theorem concreteAutomataflAIR_refines (MG : MoveGadget) (SG : StepGadget)
    (hM : MoveSound MG) (hS : StepSound SG) :
    (concreteAutomataflAIR MG SG).Refines :=
  fun b ms nb => airAutomatafl_iff_applyTurn MG SG hM hS b ms nb

/-- **`automatafl_air_refines_applyTurn_concrete`** — the upstream §7 obligation
(`automatafl_air_refines_applyTurn`), now DISCHARGED for the abstract staged AIR (⚠ parametric in
the gadgets, NOT the emitted Rust circuit — see the resolution note atop this file): it feeds
`concreteAutomataflAIR` + its proven `Refines` into the obligation, so `air.Refines` is no
longer a bare hypothesis but a THEOREM for the abstract staged AIR (instantiated only by the
IDEAL/reference gadgets). -/
theorem automatafl_air_refines_applyTurn_concrete (MG : MoveGadget) (SG : StepGadget)
    (hM : MoveSound MG) (hS : StepSound SG)
    (b : Board) (ms : List Move) (nb : Board) :
    (concreteAutomataflAIR MG SG).admits b ms nb ↔ nb = applyTurn b ms :=
  automatafl_air_refines_applyTurn (concreteAutomataflAIR MG SG)
    (concreteAutomataflAIR_refines MG SG hM hS) b ms nb

/-! ## 4. The D3 n=2 selection truth table == the reference `conflictResolve`

The concrete D3 gadget (`moves.rs`) re-derives `fork / collide / survive` from the witnessed
pattern bits and drops/keeps the two moves accordingly. This section PROVES the reference
`conflictResolve` on a two-move list IS exactly that selection — the automatafl analogue of
`MultiwayTug.legalB_iff` (the circuit's own selection predicate == the model resolution). -/

/-- The D3 fork condition (`moves.rs`: `fork = eq_ff ∧ ¬eq_tt`): one source, two distinct
destinations. -/
def d3Fork (ma mb : Move) : Prop := ma.frm = mb.frm ∧ ma.to ≠ mb.to

/-- The D3 collide condition (`moves.rs`: `collide = eq_tt ∧ ¬eq_ff ∧ ¬vac_fa ∧ ¬vac_fb`):
one destination, two distinct NON-VACUUM sources. -/
def d3Collide (b : Board) (ma mb : Move) : Prop :=
  ma.to = mb.to ∧ ma.frm ≠ mb.frm
    ∧ ¬ (b.cellAt ma.frm).isVacuum ∧ ¬ (b.cellAt mb.frm).isVacuum

instance (ma mb : Move) : Decidable (d3Fork ma mb) := by unfold d3Fork; exact inferInstance
instance (b : Board) (ma mb : Move) : Decidable (d3Collide b ma mb) := by
  unfold d3Collide; exact inferInstance

/-- **`conflictResolve_pair` (the D3 selection correspondence).** On a two-move list the
reference `conflictResolve` drops BOTH moves exactly when they fork or collide, and keeps both
otherwise — the `survive = ¬fork ∧ ¬collide` truth table the D3 gadget re-derives in-circuit
(`moves.rs`). NON-vacuous: it unfolds the genuine per-move `hasTwoDistinct` conflict filter and
pins it to the concrete `d3Fork` / `d3Collide` predicates — the automatafl analogue of
`MultiwayTug.legalB_iff` (the circuit's own selection predicate == the model resolution). -/
theorem conflictResolve_pair (b : Board) (ma mb : Move) :
    conflictResolve b [ma, mb] =
      (if d3Fork ma mb ∨ d3Collide b ma mb then [] else [ma, mb]) := by
  simp only [conflictResolve, frmConflict, toConflict, hasTwoDistinct, d3Fork, d3Collide,
    List.filter, ne_eq]
  by_cases hff : ma.frm = mb.frm <;> by_cases htt : ma.to = mb.to <;>
    by_cases hva : (b.cellAt ma.frm).isVacuum = true <;>
    by_cases hvb : (b.cellAt mb.frm).isVacuum = true <;>
    simp_all [eq_comm (a := mb.frm) (b := ma.frm), eq_comm (a := mb.to) (b := ma.to)]

/-! ## 5. Win as a bound public output (the win-safety leaf) -/

/-- **`winBound b goals winPI`** — the terminal win leaf's public win bit `winPI` pinned to the
model win fact (`hasWon`), the `game-turn-slice` range-gadget public output. Safety of the win
itself (no spurious win) is `Automatafl.winner_sound` upstream. -/
def winBound (b : Board) (goals : List (Coord × Pid)) (winPI : Bool) : Prop :=
  winPI = true ↔ hasWon b goals = true

/-- The public win bit IS the model win fact (the PI binding). -/
theorem winBound_pins (b : Board) (goals : List (Coord × Pid)) (winPI : Bool)
    (h : winBound b goals winPI) : winPI = true ↔ hasWon b goals = true := h

/-- Non-vacuity of the win binding (a real win): the Automaton stepped onto the goal binds
`winPI = true`. -/
theorem winBound_win : winBound (automatonStep demoBoard) [(⟨2, 3⟩, 3)] true := by
  unfold winBound; decide

/-- Teeth (a non-win): off any goal binds `winPI = false`. -/
theorem winBound_off : winBound demoBoard [(⟨0, 0⟩, 7)] false := by
  unfold winBound; decide

/-! ## 6. The IDEAL gadgets + the correspondence witnesses (concrete, no carried hypothesis) -/

/-- The IDEAL move gadget: the reference stages themselves. Its `MoveSound` holds by `rfl`. -/
def idealMoveGadget : MoveGadget where
  resolve := fun b ms => applyMoves b (conflictResolve b (ms.filter (moveValidB b)))

theorem idealMoveGadget_sound : MoveSound idealMoveGadget := fun _ _ => rfl

/-- The IDEAL automaton gadget: the reference `automatonStep`. Its `StepSound` holds by `rfl`. -/
def idealStepGadget : StepGadget where
  step := automatonStep

theorem idealStepGadget_sound : StepSound idealStepGadget := fun _ => rfl

/-- **`airAutomatafl_move_is_applyTurn` (THE CORRESPONDENCE WITNESS).** A legal single-move
transition IS admitted by the concrete staged AIR: the honest `apply_turn(moveBoard, [demoMove])`
satisfies `airAutomatafl`. -/
theorem airAutomatafl_move_is_applyTurn :
    airAutomatafl idealMoveGadget idealStepGadget moveBoard [demoMove]
      (applyTurn moveBoard [demoMove]) :=
  (airAutomatafl_iff_applyTurn idealMoveGadget idealStepGadget
    idealMoveGadget_sound idealStepGadget_sound moveBoard [demoMove]
    (applyTurn moveBoard [demoMove])).mpr rfl

/-- A forged next board: the honest result with the Automaton relocated to a wrong cell. -/
def forgedNext : Board := { applyTurn moveBoard [demoMove] with automaton := ⟨0, 0⟩ }

/-- **`airAutomatafl_forged_refused` (TEETH — a forged `new` is NOT admitted).** A next board
whose Automaton is not where `applyTurn` places it has no satisfying witness — the refusal is
real, not vacuous. -/
theorem airAutomatafl_forged_refused :
    ¬ airAutomatafl idealMoveGadget idealStepGadget moveBoard [demoMove] forgedNext := by
  intro h
  have he := (airAutomatafl_iff_applyTurn idealMoveGadget idealStepGadget
    idealMoveGadget_sound idealStepGadget_sound moveBoard [demoMove] forgedNext).mp h
  have hb : forgedNext.automaton = (applyTurn moveBoard [demoMove]).automaton := by rw [he]
  revert hb
  decide

/-! ### `#guard` smoke — the decidable core of the correspondence -/

-- The D3 selection matches the reference on the fork case (both dropped): forkA/forkB from
-- `Automatafl.lean` §8 share source (0,0) with distinct dests → fork → conflictResolve drops both.
#guard conflictResolve moveBoard [forkA, forkB] = ([] : List Move)
#guard decide (d3Fork forkA forkB)                        -- the fork predicate genuinely fires
#guard ¬ decide (d3Collide moveBoard forkA forkB)         -- (and it is not a collide)
-- The pair-characterization holds on the concrete fork instance (drops both).
#guard conflictResolve moveBoard [forkA, forkB]
          = (if d3Fork forkA forkB ∨ d3Collide moveBoard forkA forkB then [] else [forkA, forkB])

/-! ## 7. Axiom hygiene — the connected refinement pinned to the standard kernel triple.

`MoveSound` / `StepSound` (the deployed STARK's soundness) are CARRIED hypotheses, not axioms,
so `#assert_axioms` (blind to hypotheses) stays clean on `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms airAutomatafl_iff_applyTurn
#assert_axioms airAutomatafl_functional
#assert_axioms concreteAutomataflAIR_refines
#assert_axioms automatafl_air_refines_applyTurn_concrete
#assert_axioms conflictResolve_pair
#assert_axioms winBound_pins
#assert_axioms winBound_win
#assert_axioms winBound_off
#assert_axioms idealMoveGadget_sound
#assert_axioms idealStepGadget_sound
#assert_axioms airAutomatafl_move_is_applyTurn
#assert_axioms airAutomatafl_forged_refused

#print axioms airAutomatafl_iff_applyTurn
#print axioms conflictResolve_pair
#print axioms airAutomatafl_forged_refused

end Dregg2.Games.Automatafl
