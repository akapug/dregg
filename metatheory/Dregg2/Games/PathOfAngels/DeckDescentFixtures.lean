/-
# Deck Descent — measured design assurance and the exhaustive blind-script search

The compiled proofs in this module check the actual `stepB`/`replayB`/`rowFor`
functions used by the emitter and judge. `PathOfAngelsGuards` roots this module,
so a plain `lake build` evaluates every existing pin; the runtime FFI import
closure does not import it.

The 2026-08-08 split moved `native_decide` evaluations out of runtime elaboration,
but the closed Bool definitions retained in `DeckDescent.lean` still evaluate in
native module initialization. On 2026-09-18 the six declarations implementing the
exhaustive blind-script search and its check moved here with unchanged bodies.
The search remains exhaustive and its result is checked by the same theorem and
`#assert_compiled` assertion. Other closed measurements still live in the runtime
module; this move makes no claim to have removed their startup cost.

All existing theorem names, statements and compiled assertions are preserved.
-/
import Dregg2.Games.PathOfAngels.DeckDescent

namespace Dregg2.Games.PathOfAngels.DeckDescent

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ### The falsifier: the best script there is

The playtest's experiment, made a kernel computation.  A blind line is a fixed
list of actions, replayed against every board at once; a board is lost the moment
the script's next action is refused there or the run is doomed; `bestBlind` is
the largest number of draws ANY script of the budget's length banks.  The search
is exhaustive over the whole nine-action alphabet to depth `AIR`. -/

def blindBanked (ss : List (Option State)) : Nat :=
  (ss.filter (fun s => match s with | some t => t.banked | none => false)).length

def blindAlive (ss : List (Option State)) : Nat :=
  (ss.filter (fun s => match s with | some t => !t.banked | none => false)).length

def blindStep (ss : List (Option State)) (a : Action) : List (Option State) :=
  (boardTable.zip ss).map (fun p =>
    match p.2 with
    | none => none
    | some s => if s.banked then some s else stepB p.1 s a)

def bestBlindFrom : Nat → List (Option State) → Nat
  | 0, ss => blindBanked ss
  | fuel + 1, ss =>
      if blindAlive ss = 0 then blindBanked ss
      else allActions.foldl
        (fun best a => Nat.max best (bestBlindFrom fuel (blindStep ss a)))
        (blindBanked ss)

/-- The best score any blind script achieves, over the whole family. -/
def bestBlind : Nat := bestBlindFrom AIR (boardTable.map (fun _ => some initialState))

/-- ⚑ **NO BLIND LINE BANKS EVERY BOARD** — and this is the best one's score, not
a claim that one does not exist.  Exhaustive over every script of nine actions:
the best banks FOUR of the six draws.  The same search on the shipped rules
answered EIGHT of eight, with seven distinct nine-action scripts achieving it.
This is the property the whole repair exists to make true.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_no_blind_line_banks_every_board : Bool :=
  decide (bestBlind = 4) && decide (bestBlind < boardTable.length)

theorem every_board_can_be_banked :
    check_every_board_can_be_banked = true := by native_decide

theorem the_answer_selects_the_branch :
    check_the_answer_selects_the_branch = true := by native_decide

/-- ⚑ The falsifier of 2026-08-09: exhaustive over every nine-action script. -/
theorem no_blind_line_banks_every_board :
    check_no_blind_line_banks_every_board = true := by native_decide

theorem the_junction_is_one_state :
    check_the_junction_is_one_state = true := by native_decide

theorem the_look_is_worth_its_air :
    check_the_look_is_worth_its_air = true := by native_decide

theorem budgets_are_incomparable :
    check_budgets_are_incomparable = true := by native_decide

theorem every_board_forks :
    check_every_board_forks = true := by native_decide

theorem every_board_can_be_lost :
    check_every_board_can_be_lost = true := by native_decide

theorem family_shape_is_measured :
    check_family_shape_is_measured = true := by native_decide

theorem the_mirror_is_broken :
    check_the_mirror_is_broken = true := by native_decide

theorem declared_states_fit_the_sling :
    check_declared_states_fit_the_sling = true := by native_decide

theorem walking_in_blind_costs_a_body :
    check_walking_in_blind_costs_a_body = true := by native_decide

theorem the_deck_keeps_what_you_could_not_carry :
    check_the_deck_keeps_what_you_could_not_carry = true := by native_decide

theorem a_sound_shaft_keeps_both_relics :
    check_a_sound_shaft_keeps_both_relics = true := by native_decide

theorem parametric_closure_is_closed :
    check_parametric_closure_is_closed = true := by native_decide

theorem parametric_states_nodup :
    check_parametric_states_nodup = true := by native_decide

theorem initial_state_is_declared :
    check_initial_state_is_declared = true := by native_decide

theorem parametric_shape_is_measured :
    check_parametric_shape_is_measured = true := by native_decide

theorem the_table_consults_the_instance :
    check_the_table_consults_the_instance = true := by native_decide

theorem state_ids_are_distinct :
    check_state_ids_are_distinct = true := by native_decide

theorem state_ids_are_identifiers :
    check_state_ids_are_identifiers = true := by native_decide

#assert_compiled every_board_can_be_banked
#assert_compiled the_answer_selects_the_branch
#assert_compiled no_blind_line_banks_every_board
#assert_compiled the_junction_is_one_state
#assert_compiled the_look_is_worth_its_air
#assert_compiled budgets_are_incomparable
#assert_compiled every_board_forks
#assert_compiled every_board_can_be_lost
#assert_compiled family_shape_is_measured
#assert_compiled the_mirror_is_broken
#assert_compiled declared_states_fit_the_sling
#assert_compiled walking_in_blind_costs_a_body
#assert_compiled the_deck_keeps_what_you_could_not_carry
#assert_compiled a_sound_shaft_keeps_both_relics
#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled parametric_shape_is_measured
#assert_compiled the_table_consults_the_instance
#assert_compiled state_ids_are_distinct
#assert_compiled state_ids_are_identifiers

end Dregg2.Games.PathOfAngels.DeckDescent
