/-
# Finite POAG1 tables — the EVALUATION, out of the crypto archive's build

`FiniteTables.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 it ran fourteen `native_decide` pins at elaboration — every relay board's
closure and every one of the ninety salvage machines — so a game-fixture regression was a
hard failure of every Rust proving target in the workspace (the compilation-unit coupling
the stale-fixture outage measured).  The STATEMENTS remain in `FiniteTables.lean` as
evaluation-free `check_* : Bool` definitions, beside the closure machinery they are about;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  ⚠ The eight relay statements were `∀ i : Fin 8`; they
are now `(List.finRange 8).all` Bools, which range over the same eight boards.

No construction proof lives in this module's parent: `FiniteTables` builds no
proof-carrying `Config`, so there is no residue and every pin moved.
-/
import Dregg2.Games.PathOfAngels.FiniteTables

namespace Dregg2.Games.PathOfAngels.FiniteTables

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def relayTableClosedB (board : RelayRepair.Board) : Bool :=
  (relayTransitions board).all fun transition =>
    match transition.next with
    | none => true
    | some next => decide (next ∈ relayStates board)

def relayStatesNodupB (board : RelayRepair.Board) : Bool := (relayStates board).Nodup

def relayStateIdsUniqueB (board : RelayRepair.Board)
    (stateId : RelayRepair.State → String) : Bool :=
  ((relayStates board).map stateId).Nodup

/-- The complete refusal vocabulary.  A reason no run of the emitted FAMILY can ever
provoke would be a badge no client can earn; `relayRefusalReasons_family_live` is
that check, and `relayRefusalReasons_live_per_board` measures which boards provoke
which — they do NOT all provoke all five. -/
def relayRefusalVocabulary : List String :=
  ["solved", "turn-limit", "already-installed", "no-spares", "stranded"]

def relayRefusalReasonsCompleteB (board : RelayRepair.Board) : Bool :=
  (relayTransitions board).all fun transition =>
    match transition.next, relayRefusalReason board transition.state transition.action with
    | some _, none => true
    | none, some _ => true
    | _, _ => false

/-- Which declared reasons a run against THIS board can actually provoke. -/
def relayLiveRefusalReasons (board : RelayRepair.Board) : List String :=
  relayRefusalVocabulary.filter fun reason =>
    (relayTransitions board).any fun transition =>
      relayRefusalReason board transition.state transition.action == some reason

/-- Every declared reason is provoked by some reachable (state, action) pair OF THE
FAMILY.  ⚠ Not of every board: see `relayRefusalReasons_live_per_board`. -/
def relayRefusalReasonsFamilyLiveB : Bool :=
  relayRefusalVocabulary.all fun reason =>
    (List.finRange 8).any fun i =>
      (relayLiveRefusalReasons (RelayRepair.boardAt i)).contains reason

/-- Conversely, no row invents a reason outside the vocabulary. -/
def relayRefusalReasonsDeclaredB (board : RelayRepair.Board) : Bool :=
  (relayTransitions board).all fun transition =>
    match relayRefusalReason board transition.state transition.action with
    | none => true
    | some reason => relayRefusalVocabulary.contains reason

/-- Every board's transition table is closed: no accepted successor leaves the board's own
enumerated state closure. (Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayTable_closed : Bool :=
  (List.finRange 8).all fun i => relayTableClosedB (RelayRepair.boardAt i)

/-- Every board's state closure is duplicate-free.
(Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayStates_nodup : Bool :=
  (List.finRange 8).all fun i => relayStatesNodupB (RelayRepair.boardAt i)

/-- Every board's rows refuse exactly when a declared reason fires.
(Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayRefusalReasons_complete : Bool :=
  (List.finRange 8).all fun i => relayRefusalReasonsCompleteB (RelayRepair.boardAt i)

/-- ⚑ **REFUTED AND RESTATED.**  The claim carried here until 2026-08-05 was that
every one of the five declared reasons is provoked on every one of the eight boards.
It is FALSE, and `native_decide` said so: boards 0 and 6 carry enough spares that no
reachable (state, action) pair can ever refuse with `"no-spares"`.  The vector below
is the measurement, not a restatement of the hope.
`RESTATED` rather than weakened for convenience — the property that matters is that
the emitted vocabulary is exercised by the emitted FAMILY (no reason is a badge no
run can earn) and that no board invents a reason outside it
(`relayRefusalReasons_declared`).  Which reasons a PARTICULAR board can provoke is a
fact about that board's spare budget, and stating it per board is the strongest true
form. (Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayRefusalReasons_live_per_board : Bool :=
  decide (((List.finRange 8).map fun i => relayLiveRefusalReasons (RelayRepair.boardAt i)) =
    [ ["solved", "turn-limit", "already-installed", "stranded"]
    , ["solved", "turn-limit", "already-installed", "no-spares", "stranded"]
    , ["solved", "turn-limit", "already-installed", "no-spares", "stranded"]
    , ["solved", "turn-limit", "already-installed", "no-spares", "stranded"]
    , ["solved", "turn-limit", "already-installed", "no-spares", "stranded"]
    , ["solved", "turn-limit", "already-installed", "no-spares", "stranded"]
    , ["solved", "turn-limit", "already-installed", "stranded"]
    , ["solved", "turn-limit", "already-installed", "no-spares", "stranded"] ])

/-- No declared reason is dead across the whole emitted family.
(Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayRefusalReasons_family_live : Bool := relayRefusalReasonsFamilyLiveB

/-- No board invents a reason outside the declared vocabulary.
(Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayRefusalReasons_declared : Bool :=
  (List.finRange 8).all fun i => relayRefusalReasonsDeclaredB (RelayRepair.boardAt i)

/-- Every board's emitted state ids are unique, so a client can key on them.
(Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayStateIds_unique : Bool :=
  (List.finRange 8).all fun i => relayStateIdsUniqueB (RelayRepair.boardAt i) relayStateId

/-- Per-board closure sizes.  They are NOT all equal: the crate and the pricing
change how much of the panel lattice is reachable, so a client cannot be told one
number.  Board 2 is 25, which is the value the deleted `relayStates_count` pinned. -/
def relayStateCounts : List Nat :=
  (List.finRange 8).map fun i => (relayStates (RelayRepair.boardAt i)).length

/-- The eight per-board closure sizes, pinned as a vector.
(Pinned `= true` in `FiniteTablesFixtures`.) -/
def check_relayStateCounts_pinned : Bool :=
  decide (relayStateCounts = [26, 19, 25, 18, 18, 22, 26, 25])

/-! ## Relay Repair — the whole board family -/

theorem relayTable_closed : check_relayTable_closed = true := by native_decide

theorem relayStates_nodup : check_relayStates_nodup = true := by native_decide

theorem relayRefusalReasons_complete :
    check_relayRefusalReasons_complete = true := by native_decide

theorem relayRefusalReasons_live_per_board :
    check_relayRefusalReasons_live_per_board = true := by native_decide

theorem relayRefusalReasons_family_live :
    check_relayRefusalReasons_family_live = true := by native_decide

theorem relayRefusalReasons_declared :
    check_relayRefusalReasons_declared = true := by native_decide

theorem relayStateIds_unique : check_relayStateIds_unique = true := by native_decide

theorem relayStateCounts_pinned : check_relayStateCounts_pinned = true := by native_decide

/-! ## Salvage Lock — the parametric machine -/

theorem salvage_machine_shape_is_seed_independent :
    check_salvage_machine_shape_is_seed_independent () = true := by native_decide

theorem salvage_parametric_table_is_the_kernel :
    check_salvage_parametric_table_is_the_kernel () = true := by native_decide

theorem salvage_parametric_table_is_well_formed :
    check_salvage_parametric_table_is_well_formed () = true := by native_decide

theorem salvageParametricStates_count :
    check_salvageParametricStates_count () = true := by native_decide

theorem salvageParametricTransitions_count :
    check_salvageParametricTransitions_count () = true := by native_decide

theorem parametric_closure_covers_every_board :
    check_parametric_closure_covers_every_board () = true := by native_decide

#assert_compiled relayTable_closed
#assert_compiled relayStates_nodup
#assert_compiled relayRefusalReasons_complete
#assert_compiled relayRefusalReasons_live_per_board
#assert_compiled relayRefusalReasons_family_live
#assert_compiled relayRefusalReasons_declared
#assert_compiled relayStateIds_unique
#assert_compiled relayStateCounts_pinned
#assert_compiled salvage_machine_shape_is_seed_independent
#assert_compiled salvage_parametric_table_is_the_kernel
#assert_compiled salvage_parametric_table_is_well_formed
#assert_compiled salvageParametricStates_count
#assert_compiled salvageParametricTransitions_count
#assert_compiled parametric_closure_covers_every_board

end Dregg2.Games.PathOfAngels.FiniteTables
