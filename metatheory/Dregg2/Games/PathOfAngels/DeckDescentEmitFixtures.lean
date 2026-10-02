/-
# Deck Descent wire — the descriptor-pin EVALUATION, out of the crypto archive's build

`DeckDescentEmit.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its descriptor pins ran fifteen `native_decide` evaluations at
elaboration — parsing the rendered bytes back and comparing all 17,316 rows against `rowFor`,
plus the four constructively-built falsifiers — so any descriptor regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `DeckDescentEmit.lean` as
evaluation-free `check_* : Bool` definitions over the live validators and falsifiers; THIS
module is where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable
from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — every pin moved.
-/
import Dregg2.Games.PathOfAngels.DeckDescentEmit

namespace Dregg2.Games.PathOfAngels.DeckDescentEmit

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EmitJson
open Dregg2.Games.PathOfAngels.DeckDescent

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The first row that consults the instance, flattened into a plain accept on
its sound branch.  Schema-legal — it is a well-formed `accept` row — and wrong,
which is exactly the mutation a schema check cannot catch. -/
def flattenedResolveRows : List DescentRow :=
  let flatten : DescentRow → DescentRow := fun t =>
    match t.row with
    | .resolve m _ => { t with row := .advance m }
    | _ => t
  match descentRows.findIdx? (fun t => match t.row with | .resolve _ _ => true | _ => false) with
  | none => descentRows
  | some i => descentRows.modify i flatten

def flattenedResolveDescriptor : String :=
  descriptorFrom descentStates flattenedResolveRows descentPracticeBoards

/-- One row short.  Catches a table that is no longer total. -/
def truncatedDescriptor : String :=
  descriptorFrom descentStates descentRows.tail descentPracticeBoards

/-- Five of the six boards.  ⚠ This is a LEAK and not merely a shortage: a
family missing a member has told every reader which board the run is not playing,
out of the ~2.58 bits the descriptor exists to withhold. -/
def sevenBoardDescriptor : String :=
  descriptorFrom descentStates descentRows (descentPracticeBoards.eraseIdx 3)

/-- Six boards, one of them a duplicate of another — so the family is five
distinct instances wearing six names, and a reader who counts is told that one
board is twice as likely as the rest. -/
def duplicatedBoardDescriptor : String :=
  descriptorFrom descentStates descentRows
    (descentPracticeBoards.set 3
      { mouth := .sound, west := .sound, east := .flooded })

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_exact_schema : Bool :=
  decide (validateDescentDescriptor deckDescentDescriptorJson = .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_table_is_the_kernel : Bool :=
  decide (descentTableRefinesKernel deckDescentDescriptorJson = .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_views_are_the_kernel : Bool :=
  decide (descentViewsRefineKernel deckDescentDescriptorJson = .ok ())

/-- ⚠ The mutation happened, and it is caught.  The first conjunct is the guard
against a falsifier that stopped falsifying: without it, a `flattenedResolveRows`
that found no resolve row would emit the honest bytes and this check would
report a working adversary while testing nothing.
(Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_flattened_resolve_is_caught : Bool :=
  decide (flattenedResolveDescriptor ≠ deckDescentDescriptorJson) &&
  decide (descentTableRefinesKernel flattenedResolveDescriptor ≠ .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_truncated_table_is_caught : Bool :=
  decide (truncatedDescriptor ≠ deckDescentDescriptorJson) &&
  decide (validateDescentDescriptor truncatedDescriptor ≠ .ok ()) &&
  decide (descentTableRefinesKernel truncatedDescriptor ≠ .ok ())

/-- (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_descentDescriptor_practice_is_the_kernel : Bool :=
  decide (descentPracticeRefinesKernel deckDescentDescriptorJson = .ok ())

/-- ⚠ A family short one board, caught twice — once by the declared space and
once against the kernel's own table.
(Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_a_missing_board_is_caught : Bool :=
  decide (sevenBoardDescriptor ≠ deckDescentDescriptorJson) &&
  decide (validateDescentDescriptor sevenBoardDescriptor ≠ .ok ()) &&
  decide (descentPracticeRefinesKernel sevenBoardDescriptor ≠ .ok ())

/-- ⚠ The one a count cannot see.  Six rows, so `instance_space` agrees and the
schema check passes; the family is still wrong, and only a comparison against the
kernel's boards catches it. (Pinned `= true` in `DeckDescentEmitFixtures`.) -/
def check_a_duplicated_board_is_caught : Bool :=
  decide (duplicatedBoardDescriptor ≠ deckDescentDescriptorJson) &&
  decide (validateDescentDescriptor duplicatedBoardDescriptor = .ok ()) &&
  decide (descentPracticeRefinesKernel duplicatedBoardDescriptor ≠ .ok ())

theorem descentDescriptor_exact_schema :
    check_descentDescriptor_exact_schema = true := by native_decide

theorem descentDescriptor_table_is_the_kernel :
    check_descentDescriptor_table_is_the_kernel = true := by native_decide

theorem descentDescriptor_views_are_the_kernel :
    check_descentDescriptor_views_are_the_kernel = true := by native_decide

theorem flattened_resolve_is_caught :
    check_flattened_resolve_is_caught = true := by native_decide

theorem truncated_table_is_caught :
    check_truncated_table_is_caught = true := by native_decide

theorem descentDescriptor_practice_is_the_kernel :
    check_descentDescriptor_practice_is_the_kernel = true := by native_decide

theorem a_missing_board_is_caught :
    check_a_missing_board_is_caught = true := by native_decide

theorem a_duplicated_board_is_caught :
    check_a_duplicated_board_is_caught = true := by native_decide

#assert_compiled descentDescriptor_exact_schema
#assert_compiled descentDescriptor_table_is_the_kernel
#assert_compiled descentDescriptor_views_are_the_kernel
#assert_compiled flattened_resolve_is_caught
#assert_compiled truncated_table_is_caught
#assert_compiled descentDescriptor_practice_is_the_kernel
#assert_compiled a_missing_board_is_caught
#assert_compiled a_duplicated_board_is_caught

end Dregg2.Games.PathOfAngels.DeckDescentEmit
