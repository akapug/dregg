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

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

theorem takeDamage_position (s : State) : (takeDamage s).position = s.position := rfl
theorem cross_position (s : State) (l : Lore) : (cross s l).position = s.position := by
  unfold cross; split
  · exact takeDamage_position s
  · rfl

def playsOutB (b : Board) (acts : List Action) : Bool :=
  match replayB b initialState acts with
  | none => false
  | some s => s.banked

/-- ⚑ **Every instance is winnable — and only by a play that reads an answer.**
The two scouted lines are the two branches of one policy: sound the west spur,
then descend the spur the answer leaves dry.  Between them they bank all six
draws, so no seed is a dead mission and a player who plays correctly never loses.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_every_board_can_be_banked : Bool :=
  (List.finRange 6).all (fun i =>
    playsOutB (boardAt i) scoutedWestLine || playsOutB (boardAt i) scoutedEastLine)

/-- ⚑ **And the ANSWER is what selects the branch.**  On every board the branch
that banks is exactly the one that walks into the spur the survey found dry.
Without this, the check above would say only that some line works — not that the
look is what tells a player which.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_the_answer_selects_the_branch : Bool :=
  (List.finRange 6).all (fun i =>
    if (boardAt i).west = Passage.sound then playsOutB (boardAt i) scoutedWestLine
    else playsOutB (boardAt i) scoutedEastLine)

/-- Timber the mouth, enter it, take its relic.  Three actions that read nothing:
the mouth is shored before it is crossed, so the state after them is the same
under every draw. -/
def junctionPrefix : List Action := [.shore, .descend, .lift]

/-- ⚑ The junction is ONE state under SIX instances — nothing has been observed
yet — which is what makes the spur choice a single decision under uncertainty
rather than six decisions under six certainties.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_the_junction_is_one_state : Bool :=
  match replayB (boardAt 0) initialState junctionPrefix with
  | none => false
  | some j =>
      (List.finRange 6).all (fun i =>
        decide (replayB (boardAt i) initialState junctionPrefix = some j))

/-- How many draws a continuation from the junction still banks. -/
def banksFromJunction (rest : List Action) : Nat :=
  ((List.finRange 6).filter (fun i =>
    playsOutB (boardAt i) (junctionPrefix ++ rest))).length

/-- ⚑ **The look is worth its air, and the budget is sized for exactly one.**
From the junction six air remain.  Committing straight down a spur costs five of
them and banks FOUR of the six draws, whichever spur it picks.  Spending ONE of
the six on the answer first and then committing banks all six — and lands on
nine actions exactly.  The information verb is not decoration and it is not
dominated: it is the difference between four and six.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_the_look_is_worth_its_air : Bool :=
  decide (banksFromJunction [.descend, .lift, .ascend, .ascend, .extract] = 4) &&
  decide (banksFromJunction [.descendEast, .lift, .ascend, .ascend, .extract] = 4) &&
  check_the_answer_selects_the_branch &&
  decide (scoutedWestLine.length = AIR)

/-- ⚑ **The two budgets are still incomparable.**  The scouted line spends the
whole clock and the whole supply and takes no damage; the sweep spends the whole
clock, no supply at all, and wagers every bit.  Neither cost vector dominates the
other, and no action converts air into supply or supply into air. -/
def lineCost (b : Board) (acts : List Action) : Option (Nat × Nat × Nat) :=
  match replayB b initialState acts with
  | none => none
  | some s => some (AIR - s.air, SHORING - s.shoring, s.damage)

/-- (Pinned `= true` in `DeckDescentFixtures`.) -/
def check_budgets_are_incomparable : Bool :=
  decide (lineCost (boardAt 0) scoutedWestLine = some (9, 1, 0)) &&
  decide (lineCost (boardAt 0) sweepLine = some (9, 0, 0)) &&
  playsOutB (boardAt 0) sweepLine &&
  decide (banksFromJunction [.descend, .lift, .ascend, .ascend, .extract] < 6)

def forksAtB (b : Board) (s : State) : Bool :=
  (allActions.any fun a =>
    match stepB b s a with
    | none => false
    | some t => reachableBankB t || t.banked) &&
  (allActions.any fun a =>
    match stepB b s a with
    | none => false
    | some t => doomedB t)

def reachableStates (b : Board) : List State := reachableWithin b AIR

def forkCount (b : Board) : Nat :=
  ((reachableStates b).filter (forksAtB b)).length

def doomCount (b : Board) : Nat :=
  ((reachableStates b).filter doomedB).length

def familyTotal (f : Board → Nat) : Nat :=
  (List.finRange 6).foldl (fun acc i => acc + f (boardAt i)) 0

/-- ⚑ **Every board offers an outcome-changing fork.**
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_every_board_forks : Bool := decide (∀ i : Fin 6, 0 < forkCount (boardAt i))

/-- ⚑ **Every board can be lost.** (Pinned `= true` in `DeckDescentFixtures`.) -/
def check_every_board_can_be_lost : Bool :=
  decide (∀ i : Fin 6, 0 < doomCount (boardAt i))

/-- The measured shape of the family, per board and summed.  These are the
numbers `scripts/poa-design-gate.py` must independently arrive at from the
emitted table; they are stated here so a disagreement is loud.  Eight boards and
two timbers gave 4688 / 1360 / 2469; six boards and one timber give the triple
below, and the drop is the state space the second timber was buying.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_family_shape_is_measured : Bool :=
  decide (familyTotal (fun b => (reachableStates b).length) = 2928) &&
  decide (familyTotal forkCount = 871) &&
  decide (familyTotal doomCount = 1469)

/-- One board's census, as a comparable shape. -/
def boardShape (b : Board) : Nat × Nat × Nat :=
  ((reachableStates b).length, forkCount b, doomCount b)

/-- ⚑ **The mirror is broken.**  All six draws are distinct games: no two boards
share a (reachable, forks, doomed) shape.  Before the east spur's second relic a
board and its west/east reflection were the same game and the draws collapsed —
0.42 of a bit of the instance doing no work, the gate's `the-family-collapses`
finding.  The second relic still does that work: the spurs hold ONE and TWO, so
`(·, flooded, sound)` and `(·, sound, flooded)` are different games even though
the bulkhead makes them the two halves of one draw.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_the_mirror_is_broken : Bool :=
  decide (((List.finRange 6).map (fun i => boardShape (boardAt i))).Nodup)

/-- The scout decision, named.  From the hatch on a flooded mouth, walking in
blind costs a point of damage that nothing in a descent restores; looking first
and shoring blind both cost a unit of air and no body.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_walking_in_blind_costs_a_body : Bool :=
  decide ((match stepB (boardAt 3) initialState .descend with
    | none => none
    | some t => some t.damage) = some 1) &&
  decide ((match stepB (boardAt 3) initialState .survey with
    | none => none
    | some t => some t.damage) = some 0) &&
  decide ((match stepB (boardAt 3) initialState .shore with
    | none => none
    | some t => some t.damage) = some 0)

/-- ⚑ **Extraction debt, and the deck's cut.**  Walk in blind on a flooded mouth,
take the mouth and west relics, and turn round: the second crossing of the same
flood is the second point of damage, capacity falls to one, and the deck keeps
the relic reached furthest for.  The run reaches the hatch holding one — with air
to spare and no way to use it. -/
def blindGrabLine : List Action :=
  [.descend, .lift, .descend, .lift, .ascend, .ascend]

/-- (Pinned `= true` in `DeckDescentFixtures`.) -/
def check_the_deck_keeps_what_you_could_not_carry : Bool :=
  match replayB (boardAt 3) initialState blindGrabLine with
  | none => false
  | some s =>
      decide (s.position = Node.hatch) && decide (s.damage = 2) &&
      decide (capacity s = 1) && decide (s.sling.count = 1) &&
      decide (0 < s.air) && doomedB s

/-- The same six actions on a sound shaft come home with both.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_a_sound_shaft_keeps_both_relics : Bool :=
  match replayB (boardAt 0) initialState blindGrabLine with
  | none => false
  | some s =>
      decide (s.position = Node.hatch) && decide (s.damage = 0) &&
      decide (s.sling.count = 2) && reachableBankB s

def parametricRowCount : Nat := parametricStates.length * allActions.length

/-- ⚑ **The table is closed.**  Every successor any row names is a state the
descriptor declares, so a client can never be handed an id it does not have.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_parametric_closure_is_closed : Bool :=
  parametricStates.all (fun s =>
    allActions.all (fun a =>
      (rowSuccessors s a).all (fun n => parametricStates.contains n)))

/-- (Pinned `= true` in `DeckDescentFixtures`.) -/
def check_parametric_states_nodup : Bool :=
  decide (parametricStates.eraseDups = parametricStates)

/-- (Pinned `= true` in `DeckDescentFixtures`.) -/
def check_initial_state_is_declared : Bool := parametricStates.contains initialState

/-- The emitted shape, stated so the descriptor's size is a number a reader has
before they open the file.  Before the second relic: 1598 states, 14382 rows;
with two timbers and eight boards: 1924 states, 17316 rows.  One timber removes a
whole supply level from the closure.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_parametric_shape_is_measured : Bool :=
  decide (parametricStates.length = 1692) && decide (allActions.length = 9) &&
  decide (parametricRowCount = 15228)

/-- `Sling.count` is unbounded as a TYPE — the counts are `Nat` — but capacity
is the wall the transition enforces: no declared state carries more than
`BASE_CAPACITY` relics.  This replaces the old `Sling.count_le_three`, which was
a fact about the type and is false of it now.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_declared_states_fit_the_sling : Bool :=
  parametricStates.all (fun s => decide (s.sling.count ≤ BASE_CAPACITY))

/-- ⚑ **The table really consults the instance.**  Some rows resolve, so the
gate's `no-oracle-row` FAIL — "every transition is deterministic, so the instance
cannot affect play" — cannot fire. -/
def resolveRowCount : Nat :=
  (parametricStates.flatMap (fun s =>
    allActions.filter (fun a => match rowFor s a with | .resolve _ _ => true | _ => false)))
  |>.length

/-- (Pinned `= true` in `DeckDescentFixtures`.) -/
def check_the_table_consults_the_instance : Bool := decide (0 < resolveRowCount)

/-- ⚑ **Ids separate states.**  Two declared states never share an id, so the
transition table's string references are unambiguous.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_state_ids_are_distinct : Bool :=
  decide ((parametricStates.map stateId).eraseDups.length = parametricStates.length)

/-- ⚑ **Every id a client is handed is an identifier.**  This is the pin that
`?` and `+` walked past; it is stated over the SAME `stateId` the descriptor
renders, so re-introducing either character goes red here.
(Pinned `= true` in `DeckDescentFixtures`.) -/
def check_state_ids_are_identifiers : Bool :=
  parametricStates.all (fun s => isPoag1Identifier (stateId s))

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
