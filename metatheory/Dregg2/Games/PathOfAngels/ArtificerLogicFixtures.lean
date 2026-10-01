/-
# Artificer Logic — the measured-design EVALUATION, out of the crypto archive's build

`ArtificerLogic.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its measured design properties ran twenty-five `native_decide` evaluations at
elaboration — including the full 1197-state × 24-action parametric closure — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The properties' STATEMENTS
remain in `ArtificerLogic.lean` as evaluation-free `check_* : Bool` definitions over
`stepR`/`certainWithin`/`rowFor` — the same functions the emitter tabulates and the judge
runs; THIS module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction in `ArtificerLogic.lean` consumes a
`native_decide` proof as data, so every pin moved.
-/
import Dregg2.Games.PathOfAngels.ArtificerLogic

namespace Dregg2.Games.PathOfAngels.ArtificerLogic

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The same fact as a count: sixteen rules, sixteen distinct signatures.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_manual_signatures_are_distinct : Bool :=
  decide ((manual.map signature).eraseDups.length = manual.length)

/-- ⚠ **And the check goes red.**  A manual that repeats an entry fails
`manual_signatures_are_distinct`'s test, so the pin above is a gate and not a
decoration.  The first conjunct asserts the mutation HAPPENED — a falsifier whose
mutation silently became a no-op has stopped falsifying twice in this
repository. -/
def repeatedManual : List Rule := Rule.uniform Metal.brass :: manual

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_repeated_manual_is_caught : Bool :=
  decide (repeatedManual ≠ manual) &&
  decide ((repeatedManual.map signature).eraseDups.length ≠ repeatedManual.length)

/-- ⚑ **Four charges are enough.**  From the full manual, on the worst answers the
mechanism can give, four cuts always reach a single rule.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_four_charges_are_enough : Bool := certainWithin PROBE_BUDGET manual

/-- ⚑ **And three are not.**  Sixteen rules over binary charges cannot be
separated in three cuts — the budget is the information floor and the slack is
ZERO.  These two checks together are the whole sizing argument.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_three_charges_are_not : Bool := !(certainWithin (PROBE_BUDGET - 1) manual)

/-- How many rules of the manual the mechanism turns on, for this charge. -/
def turningCount (c : Charge) : Nat := (manual.filter (fun r => r.accepts c)).length

/-- Does opening with this charge leave a run able to finish inside the budget? -/
def keepsTheBudget (c : Charge) : Bool :=
  splitsB manual c &&
  certainWithin (PROBE_BUDGET - 1) (manual.filter (fun r => r.accepts c)) &&
  certainWithin (PROBE_BUDGET - 1) (manual.filter (fun r => !(r.accepts c)))

/-- ⚑ **An even split is not the same as a good one.**  FOUR of the eight opening
charges cut the sixteen rules exactly in half; only THREE of those four leave a
run able to reach certainty in the three charges that remain.  The fourth is the
trap, and a player who opens on it has already lost the guarantee without
spending anything they can see.

The third conjunct is what makes this a statement and not a coincidence: every
charge that keeps the budget IS an even cut, so evenness is necessary and not
sufficient — exactly the lesson the opening is for.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_an_even_split_is_not_a_good_one : Bool :=
  decide ((allCharges.filter (fun c => decide (turningCount c = 8))).length = 4) &&
  decide ((allCharges.filter keepsTheBudget).length = 3) &&
  allCharges.all (fun c => !keepsTheBudget c || decide (turningCount c = 8))

def parametricRowCount : Nat := parametricStates.length * allActions.length

/-- ⚑ **The layers are the clock.**  Every state in layer `n` has spent exactly
`n`, which is why the layered enumeration is complete and why the concatenation
above needs no cross-layer deduplication.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_parametric_layers_are_the_clock : Bool :=
  (List.range (ACTION_LIMIT + 1)).all (fun n =>
    (parametricLayer n).all (fun s => decide (s.spent = n)))

/-- ⚑ **The table is closed.**  Every successor any row names is a state the
descriptor declares, so a client can never be handed an id it does not have.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_parametric_closure_is_closed : Bool :=
  parametricStates.all (fun s =>
    allActions.all (fun a =>
      (rowSuccessors s a).all (fun n => parametricStates.contains n)))

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_parametric_states_nodup : Bool :=
  decide (parametricStates.eraseDups = parametricStates)

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_initial_state_is_declared : Bool := parametricStates.contains initialState

/-- ⚑ **No declared state is empty.**  A candidate set can never be narrowed to
nothing, because the hidden rule always survives — so the state a mistaken
naming would produce from a SINGLE candidate is never named by any row.  This is
`truth_survives`, visible in the enumeration.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_no_declared_state_is_empty : Bool :=
  parametricStates.all (fun s => decide (0 < s.candidates.length))

/-- ⚑ **Resolve rows name two different states**, so the gate's "the oracle bit is
not consulted and the row should be an accept" refusal cannot fire.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_resolve_rows_name_two_states : Bool :=
  parametricStates.all (fun s => allActions.all (fun a =>
    match rowFor s a with
    | .resolve m f => decide (m ≠ f)
    | _ => true))

/-- ⚑ **The table really consults the instance.** -/
def resolveRowCount : Nat :=
  (parametricStates.flatMap (fun s =>
    allActions.filter (fun a =>
      match rowFor s a with | .resolve _ _ => true | _ => false))).length

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_the_table_consults_the_instance : Bool := decide (0 < resolveRowCount)

/-- ⚑ **Every open probe resolves.**  A charge that cannot split is refused, so
there is no accepted probe whose row names one successor: every experiment a
player is allowed to run is one whose answer they do not already hold.  This is
requirement "which charge, not whether", as a property of the emitted table.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_every_open_probe_resolves : Bool :=
  parametricStates.all (fun s => allCharges.all (fun c =>
    match rowFor s (.probe c) with
    | .advance _ => false
    | _ => true))

/-- The refusal reasons the emitted table actually carries. -/
def emittedReasons : List String :=
  (parametricStates.flatMap (fun s =>
    allActions.filterMap (fun a =>
      match rowFor s a with | .refuse reason => some reason | _ => none))).eraseDups

/-- ⚑ **Every declared refusal reason is reachable, and no other is emitted.**  A
reason a client can render but the kernel can never produce is a lie in the UI;
a reason the kernel produces but the vocabulary does not name is a string the
client cannot translate.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_every_declared_reason_is_reachable : Bool :=
  refusalVocabulary.all (fun r => emittedReasons.contains r) &&
  emittedReasons.all (fun r => refusalVocabulary.contains r)

/-- The first charge that keeps certainty reachable on BOTH answers. -/
def bestProbe (s : State) : Option Charge :=
  allCharges.find? (fun c =>
    splitsB s.candidates c &&
    certainWithin (chargesLeft s - 1) (s.candidates.filter (fun r => r.accepts c)) &&
    certainWithin (chargesLeft s - 1) (s.candidates.filter (fun r => !(r.accepts c))))

/-- The line a player who never wastes a cut would walk against this instance. -/
def perfectLine (hidden : Rule) : Nat → State → List Action
  | 0, s => match s.candidates with | [r] => [Action.declare r] | _ => []
  | fuel + 1, s =>
      match s.candidates with
      | [r] => [Action.declare r]
      | _ =>
          match bestProbe s with
          | none => []
          | some c =>
              Action.probe c ::
                perfectLine hidden fuel (stepAns (hidden.accepts c) s (.probe c))

def identifies (hidden : Rule) : Bool :=
  match replayR hidden initialState (perfectLine hidden ACTION_LIMIT initialState) with
  | none => false
  | some s => decide (s.verdict = Verdict.identified)

/-- ⚑ **Every instance is identifiable, and the line is exactly the budget.**  No
draw is a dead mission — for all sixteen hidden rules the never-waste-a-cut line
names the rule, and it takes all five actions to do it.  Same shape as
`DeckDescent.every_board_can_be_banked`, and the same argument: a family with an
unwinnable member is a family with a coin flip in it.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_every_rule_is_identifiable : Bool :=
  manual.all identifies &&
  manual.all (fun r =>
    decide ((perfectLine r ACTION_LIMIT initialState).length = ACTION_LIMIT))

/-- States from which the run must name a rule with more than one candidate still
standing: out of charges, and holding a wager. -/
def wagerStates : Nat :=
  (parametricStates.filter (fun s =>
    decide (s.verdict = Verdict.probing) &&
    decide (2 ≤ s.candidates.length) &&
    decide (PROBE_BUDGET ≤ s.spent))).length

/-- ⚑ **The run can be lost.**  A player who spends a cut badly reaches a state
with charges gone and more than one rule standing; from there naming is a wager
and the run can end mistaken.  A design in which this count is zero is one where
the budget never binds. (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_the_run_can_be_lost : Bool := decide (0 < wagerStates)

/-- Reachable states from which certainty is still available. -/
def certifiableCount : Nat := (parametricStates.filter certifiableB).length

/-- Reachable live states from which it is NOT. -/
def luckOnlyCount : Nat :=
  (parametricStates.filter (fun s =>
    decide (s.verdict = Verdict.probing) && !certifiableB s)).length

/-- ⚑ **Both sides of the skill/luck line are reachable.**  There are live states
that can still be brought to certainty and live states that cannot, so
`certifiable` is a field that says something — a flag that is constant is a flag
that is decoration. (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_the_skill_line_is_real : Bool :=
  decide (0 < certifiableCount) && decide (0 < luckOnlyCount)

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_rule_tags_are_distinct : Bool :=
  decide ((manual.map Rule.tag).eraseDups.length = manual.length)

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_action_tags_are_distinct : Bool :=
  decide ((allActions.map Action.tag).eraseDups.length = allActions.length)

/-- ⚑ **Ids separate states.**  Two declared states never share an id, so the
transition table's string references are unambiguous.
(Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_state_ids_are_distinct : Bool :=
  decide ((parametricStates.map stateId).eraseDups.length = parametricStates.length)

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_parametric_shape_is_measured : Bool :=
  decide (parametricStates.length = 1197) && decide (allActions.length = 24) &&
  decide (parametricRowCount = 28728)

/-- (Pinned `= true` in `ArtificerLogicFixtures`.) -/
def check_action_codes_are_distinct : Bool :=
  decide ((allActions.map actionCode).eraseDups.length = allActions.length)

theorem manual_signatures_are_distinct :
    check_manual_signatures_are_distinct = true := by native_decide

theorem repeated_manual_is_caught :
    check_repeated_manual_is_caught = true := by native_decide

theorem four_charges_are_enough :
    check_four_charges_are_enough = true := by native_decide

theorem three_charges_are_not :
    check_three_charges_are_not = true := by native_decide

theorem an_even_split_is_not_a_good_one :
    check_an_even_split_is_not_a_good_one = true := by native_decide

theorem parametric_layers_are_the_clock :
    check_parametric_layers_are_the_clock = true := by native_decide

theorem parametric_closure_is_closed :
    check_parametric_closure_is_closed = true := by native_decide

theorem parametric_states_nodup :
    check_parametric_states_nodup = true := by native_decide

theorem initial_state_is_declared :
    check_initial_state_is_declared = true := by native_decide

theorem no_declared_state_is_empty :
    check_no_declared_state_is_empty = true := by native_decide

theorem resolve_rows_name_two_states :
    check_resolve_rows_name_two_states = true := by native_decide

theorem the_table_consults_the_instance :
    check_the_table_consults_the_instance = true := by native_decide

theorem every_open_probe_resolves :
    check_every_open_probe_resolves = true := by native_decide

theorem every_declared_reason_is_reachable :
    check_every_declared_reason_is_reachable = true := by native_decide

theorem every_rule_is_identifiable :
    check_every_rule_is_identifiable = true := by native_decide

theorem the_run_can_be_lost :
    check_the_run_can_be_lost = true := by native_decide

theorem the_skill_line_is_real :
    check_the_skill_line_is_real = true := by native_decide

theorem rule_tags_are_distinct :
    check_rule_tags_are_distinct = true := by native_decide

theorem action_tags_are_distinct :
    check_action_tags_are_distinct = true := by native_decide

theorem state_ids_are_distinct :
    check_state_ids_are_distinct = true := by native_decide

theorem parametric_shape_is_measured :
    check_parametric_shape_is_measured = true := by native_decide

theorem action_codes_are_distinct :
    check_action_codes_are_distinct = true := by native_decide

#assert_compiled manual_signatures_are_distinct
#assert_compiled repeated_manual_is_caught
#assert_compiled four_charges_are_enough
#assert_compiled three_charges_are_not
#assert_compiled an_even_split_is_not_a_good_one
#assert_compiled parametric_layers_are_the_clock
#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled no_declared_state_is_empty
#assert_compiled resolve_rows_name_two_states
#assert_compiled the_table_consults_the_instance
#assert_compiled every_open_probe_resolves
#assert_compiled every_declared_reason_is_reachable
#assert_compiled every_rule_is_identifiable
#assert_compiled the_run_can_be_lost
#assert_compiled the_skill_line_is_real
#assert_compiled rule_tags_are_distinct
#assert_compiled action_tags_are_distinct
#assert_compiled state_ids_are_distinct
#assert_compiled parametric_shape_is_measured
#assert_compiled action_codes_are_distinct

end Dregg2.Games.PathOfAngels.ArtificerLogic
