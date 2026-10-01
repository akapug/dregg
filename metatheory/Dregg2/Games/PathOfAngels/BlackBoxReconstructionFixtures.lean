/-
# Black Box Reconstruction — the pin EVALUATION, out of the crypto archive's build

`BlackBoxReconstruction.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 it ran six `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The pins' STATEMENTS remain in `BlackBoxReconstruction.lean` as evaluation-free
`check_* : Bool` definitions; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. Named residue: none — every evaluation moved.
-/
import Dregg2.Games.PathOfAngels.BlackBoxReconstruction

namespace Dregg2.Games.PathOfAngels.BlackBoxReconstruction

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def permutationRows : List (List Fragment) :=
  candidateRows.filter (fun row => decide row.Nodup)

/-- The image of the seed space is EXACTLY the set of permutations, measured
against the independently enumerated 5^5 candidate domain.

⚑ The evaluation moved out of the `Dregg2.FFI` closure (2026-08-08): a
`native_decide` here made every game-fixture regression a hard failure of every
Rust proving target. Statements stay as evaluation-free `check_* : Bool` defs;
each is pinned `= true` by `native_decide` + `#assert_compiled` in
`BlackBoxReconstructionFixtures.lean`, rooted in the `PathOfAngelsGuards`
library. Named residue: none — every evaluation moved.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_order_space_is_exactly_the_permutations : Bool :=
  decide (permutationRows.length = ORDER_SPACE) &&
  permutationRows.all (fun row => decide (row ∈ allOrderRows))

/-- A probe SETTLED iff the recorder answered `placed`. -/
def hitB (order : Fin ORDER_SPACE) (p : Probe) : Bool :=
  decide (answerOf order p = Answer.placed)

/-- ⚑ `placed` and "named the right fragment" are the same event, so every
theorem below that reads `hitB` reads the recorder and not a second rule. -/
theorem hit_iff_named_the_held_fragment (order : Fin ORDER_SPACE) (p : Probe) :
    hitB order p = (orderAt order p.1 == p.2) := by
  simp only [hitB, answerOf]
  rcases Nat.lt_trichotomy (orderAt order p.1).val p.2.val with h | h | h
  · simp [h, Fin.ext_iff, Nat.ne_of_lt h]
  · simp [h, Fin.ext_iff]
  · simp [Nat.not_lt.mpr (Nat.le_of_lt h), Fin.ext_iff, Nat.ne_of_gt h]

/-- One position of the hint-IGNORING sweep: try the still-unsettled fragments in
order and stop at the match.  This is the shipped reference policy, kept as the
foil the budget is measured against. -/
def scanForSlot (order : Fin ORDER_SPACE) (remaining : List Fragment) (slot : Slot) :
    List Action × List Fragment :=
  let correct := orderAt order slot
  let tried := remaining.takeWhile (fun f => f != correct)
  ((tried ++ [correct]).map (Action.probe slot),
    remaining.filter (fun f => f != correct))

def scanActions (order : Fin ORDER_SPACE) : List Action :=
  (allSlots.foldl
    (fun acc slot =>
      let out := scanForSlot order acc.2 slot
      (acc.1 ++ out.1, out.2))
    (([] : List Action), allFragments)).1

def scanWinsB (order : Fin ORDER_SPACE) : Bool :=
  decide ((scanActions order).length ≤ MAX_TURNS) &&
  (match replay order initialState (scanActions order) with
   | none => false
   | some s => solvedB order s)

def scanLengths : List Nat :=
  (List.finRange ORDER_SPACE).map (fun order => (scanActions order).length)

/-- How many of the 120 draws the hint-ignoring sweep still banks. -/
def scanWinCount : Nat :=
  ((List.finRange ORDER_SPACE).filter scanWinsB).length

private def bisectAux (order : Fin ORDER_SPACE) (slot : Slot) :
    Nat → List Fragment → List Action
  | 0, _ => []
  | _, [] => []
  | fuel + 1, cands =>
      let g := cands.getD (cands.length / 2) ⟨0, by decide⟩
      let a := Action.probe slot g
      match answerOf order (slot, g) with
      | .placed => [a]
      | .earlier => a :: bisectAux order slot fuel (cands.filter (fun f => decide (f.val < g.val)))
      | .later => a :: bisectAux order slot fuel (cands.filter (fun f => decide (g.val < f.val)))

def bisectActions (order : Fin ORDER_SPACE) : List Action :=
  (allSlots.foldl
    (fun acc slot =>
      (acc.1 ++ bisectAux order slot SLOT_COUNT acc.2,
        acc.2.filter (fun f => f != orderAt order slot)))
    (([] : List Action), allFragments)).1

def bisectWinsB (order : Fin ORDER_SPACE) : Bool :=
  decide ((bisectActions order).length ≤ MAX_TURNS) &&
  (match replay order initialState (bisectActions order) with
   | none => false
   | some s => solvedB order s)

def bisectLengths : List Nat :=
  (List.finRange ORDER_SPACE).map (fun order => (bisectActions order).length)

/-- ⚑ **Every instance is winnable inside the budget.**  Without this the game
could ship unplayable on some seeds — the design gate's `unwinnable-instance`
FAIL — and a player who plays perfectly could still lose, which is the one thing
a budget must never do.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_every_instance_is_winnable_inside_the_budget : Bool :=
  (List.finRange ORDER_SPACE).all bisectWinsB

/-- ⚑ **The budget is attained, so it is not slack.**  Some instance costs the
listening policy all eleven probes, and none costs more.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_the_budget_is_the_listening_policy_worst_case : Bool :=
  bisectLengths.all (fun n => decide (n ≤ MAX_TURNS)) && decide (MAX_TURNS ∈ bisectLengths)

/-- ⚑ **THE FALSIFIER: the scan that ignores the answer no longer wins.**  This
is the playtest finding, turned into a number the kernel keeps.  The shipped
left-to-right sweep banked 120 of 120 at the old budget; it banks 91 now, and its
worst case is fifteen against a budget of eleven.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_the_hint_ignoring_scan_no_longer_wins : Bool :=
  decide (scanWinCount = 91) && decide (scanWinCount < ORDER_SPACE) &&
  decide (scanLengths.foldl Nat.max 0 = 15)

/-- ⚑ **And listening is what closes the gap.**  Same instances, same budget, same
alphabet of actions: the only difference is whether the run reads `earlier` and
`later`.  This is the statement that the third answer class does WORK.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_listening_is_what_closes_the_gap : Bool :=
  decide (scanWinCount < ORDER_SPACE) &&
  ((List.finRange ORDER_SPACE).all bisectWinsB) &&
  decide (bisectLengths.foldl Nat.max 0 < scanLengths.foldl Nat.max 0)

/-- ⚑ **A run can be lost.**  The design gate names `cannot-lose` as a WARN for a
reason: if failure is unrepresentable then no choice carries a consequence.
Fail-closed: a refused replay answers `false`.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_a_run_can_be_lost : Bool :=
  match replay 0 initialState losingTranscript with
  | none => false
  | some s => !solvedB 0 s && decide (s.turns = MAX_TURNS)

/-- A witness FIRES when its prefix is accepted at every step and the further
probe is refused with exactly the reason it names. -/
def witnessFiresB (w : RefusalWitness) : Bool :=
  match replay w.order initialState w.history with
  | none => false
  | some s => decide (refusal? w.order s w.probe = some w.reason)

/-- ⚑ **Every declared refusal reason is reachable.**  Not "one theorem per
reason asserted in prose" — every witness replays, and every constructor of
`Refusal` is named by one.  The design gate re-derives all five from the emitted
artifact. -/
def everyRefusalIsWitnessedB : Bool :=
  refusalWitnesses.all witnessFiresB &&
    allRefusals.all fun r => refusalWitnesses.any fun w => decide (w.reason = r)

/-- (Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_every_refusal_is_witnessed : Bool := everyRefusalIsWitnessedB

/-- The falsifier, constructed rather than asserted: a witness whose prefix is
legal and whose further probe is NOT refused at all does not fire.  Probing
`(0,1)` after `(0,2)` on the identity is a perfectly ordinary accepted move, so
`witnessFiresB` must reject any claim that it refuses.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_a_probe_that_is_accepted_witnesses_nothing : Bool :=
  !(allRefusals.any fun r =>
    witnessFiresB { reason := r, order := 0, history := [.probe 0 2],
                    probe := .probe 0 1 })

theorem order_space_is_exactly_the_permutations :
    check_order_space_is_exactly_the_permutations = true := by native_decide

theorem every_instance_is_winnable_inside_the_budget :
    check_every_instance_is_winnable_inside_the_budget = true := by native_decide

theorem the_budget_is_the_listening_policy_worst_case :
    check_the_budget_is_the_listening_policy_worst_case = true := by native_decide

/-- ⚑ The playtest falsifier of 2026-08-09, kept as a number. -/
theorem the_hint_ignoring_scan_no_longer_wins :
    check_the_hint_ignoring_scan_no_longer_wins = true := by native_decide

theorem listening_is_what_closes_the_gap :
    check_listening_is_what_closes_the_gap = true := by native_decide

theorem a_run_can_be_lost :
    check_a_run_can_be_lost = true := by native_decide

theorem every_refusal_is_witnessed :
    check_every_refusal_is_witnessed = true := by native_decide

theorem a_probe_that_is_accepted_witnesses_nothing :
    check_a_probe_that_is_accepted_witnesses_nothing = true := by native_decide

#assert_compiled order_space_is_exactly_the_permutations
#assert_compiled every_instance_is_winnable_inside_the_budget
#assert_compiled the_budget_is_the_listening_policy_worst_case
#assert_compiled the_hint_ignoring_scan_no_longer_wins
#assert_compiled listening_is_what_closes_the_gap
#assert_compiled a_run_can_be_lost
#assert_compiled every_refusal_is_witnessed
#assert_compiled a_probe_that_is_accepted_witnesses_nothing

end Dregg2.Games.PathOfAngels.BlackBoxReconstruction
