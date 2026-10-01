/-
# Artificer Logic wire — the descriptor-pin EVALUATION, out of the crypto archive's build

`ArtificerLogicEmit.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its descriptor pins ran thirteen `native_decide` evaluations at
elaboration — parsing the rendered bytes back and comparing all 28,728 rows against `rowFor`,
plus the three constructively-built falsifiers — so any descriptor regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `ArtificerLogicEmit.lean` as
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
import Dregg2.Games.PathOfAngels.ArtificerLogicEmit

namespace Dregg2.Games.PathOfAngels.ArtificerLogicEmit

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EmitJson
open Dregg2.Games.PathOfAngels.ArtificerLogic

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- ⚑ **THE FALSIFIER THAT MATTERS FOR THIS GAME.**  `even-brass` is rendered
carrying `mirrored`'s signature, so the published manual holds two entries no
experiment can separate.  Schema-legal — it is a well-formed manual — and it is
exactly the defect the distinguishability gate exists to catch: a player who runs
all eight charges perfectly is left with two candidates and a coin.

⚠ The rule is not otherwise touched, so the STATE MACHINE is unchanged and every
row still refines the kernel.  A gate that only checked rows would pass this. -/
def synonymTurns (r : ArtificerLogic.Rule) : List ArtificerLogic.Charge :=
  if r = ArtificerLogic.Rule.evenBrass then engagesOn ArtificerLogic.Rule.mirrored
  else engagesOn r

def synonymManualDescriptor : String := descriptorFrom synonymTurns logicStates logicRows

/-- The first row that consults the instance, flattened into a plain accept on its
turning branch.  Schema-legal and wrong, which is the mutation a schema check
cannot catch. -/
def flattenedResolveRows : List LogicRow :=
  let flatten : LogicRow → LogicRow := fun t =>
    match t.row with
    | .resolve m _ => { t with row := .advance m }
    | _ => t
  match logicRows.findIdx? (fun t => match t.row with | .resolve _ _ => true | _ => false) with
  | none => logicRows
  | some i => logicRows.modify i flatten

def flattenedResolveDescriptor : String :=
  descriptorFrom engagesOn logicStates flattenedResolveRows

/-- One row short.  Catches a table that is no longer total. -/
def truncatedDescriptor : String := descriptorFrom engagesOn logicStates logicRows.tail

/-- (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_logicDescriptor_exact_schema : Bool :=
  decide (validateLogicDescriptor artificerLogicDescriptorJson = .ok ())

/-- (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_logicDescriptor_manual_is_the_kernel : Bool :=
  decide (logicManualRefinesKernel artificerLogicDescriptorJson = .ok ())

/-- ⚑ **The published lattice has no unwinnable pair**, checked against the bytes
a client downloads and not against the kernel's own definitions.
(Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_logicDescriptor_manual_is_distinguishing : Bool :=
  decide (logicManualIsDistinguishing artificerLogicDescriptorJson = .ok ())

/-- (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_logicDescriptor_table_is_the_kernel : Bool :=
  decide (logicTableRefinesKernel artificerLogicDescriptorJson = .ok ())

/-- (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_logicDescriptor_views_are_the_kernel : Bool :=
  decide (logicViewsRefineKernel artificerLogicDescriptorJson = .ok ())

/-- ⚠ **The synonym is caught, and ONLY by the manual check.**  The three
conjuncts are the whole argument: the mutation happened; the distinguishability
check refuses it; and the TABLE check still passes, which is why a row-by-row
differential is not sufficient for an induction game and this module carries a
second, manual-shaped one. (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_synonym_manual_is_caught : Bool :=
  decide (synonymManualDescriptor ≠ artificerLogicDescriptorJson) &&
  decide (logicManualIsDistinguishing synonymManualDescriptor ≠ .ok ()) &&
  decide (logicTableRefinesKernel synonymManualDescriptor = .ok ())

/-- (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_flattened_resolve_is_caught : Bool :=
  decide (flattenedResolveDescriptor ≠ artificerLogicDescriptorJson) &&
  decide (logicTableRefinesKernel flattenedResolveDescriptor ≠ .ok ())

/-- (Pinned `= true` in `ArtificerLogicEmitFixtures`.) -/
def check_truncated_table_is_caught : Bool :=
  decide (truncatedDescriptor ≠ artificerLogicDescriptorJson) &&
  decide (validateLogicDescriptor truncatedDescriptor ≠ .ok ()) &&
  decide (logicTableRefinesKernel truncatedDescriptor ≠ .ok ())

theorem logicDescriptor_exact_schema :
    check_logicDescriptor_exact_schema = true := by native_decide

theorem logicDescriptor_manual_is_the_kernel :
    check_logicDescriptor_manual_is_the_kernel = true := by native_decide

theorem logicDescriptor_manual_is_distinguishing :
    check_logicDescriptor_manual_is_distinguishing = true := by native_decide

theorem logicDescriptor_table_is_the_kernel :
    check_logicDescriptor_table_is_the_kernel = true := by native_decide

theorem logicDescriptor_views_are_the_kernel :
    check_logicDescriptor_views_are_the_kernel = true := by native_decide

theorem synonym_manual_is_caught :
    check_synonym_manual_is_caught = true := by native_decide

theorem flattened_resolve_is_caught :
    check_flattened_resolve_is_caught = true := by native_decide

theorem truncated_table_is_caught :
    check_truncated_table_is_caught = true := by native_decide

#assert_compiled logicDescriptor_exact_schema
#assert_compiled logicDescriptor_manual_is_the_kernel
#assert_compiled logicDescriptor_manual_is_distinguishing
#assert_compiled logicDescriptor_table_is_the_kernel
#assert_compiled logicDescriptor_views_are_the_kernel
#assert_compiled synonym_manual_is_caught
#assert_compiled flattened_resolve_is_caught
#assert_compiled truncated_table_is_caught

end Dregg2.Games.PathOfAngels.ArtificerLogicEmit
