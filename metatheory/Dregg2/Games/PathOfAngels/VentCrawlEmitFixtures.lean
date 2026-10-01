/-
# Vent Crawl wire — the descriptor-pin EVALUATION, out of the crypto archive's build

`VentCrawlEmit.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its descriptor pins ran nineteen `native_decide` evaluations at elaboration
— parsing the rendered bytes back and comparing all 102 rows against `VentCrawl.rowFor`,
plus the five constructively-built falsifiers — so any descriptor regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The pins' STATEMENTS remain in `VentCrawlEmit.lean` as
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
import Dregg2.Games.PathOfAngels.VentCrawlEmit

namespace Dregg2.Games.PathOfAngels.VentCrawlEmit

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EmitJson
open Dregg2.Games.PathOfAngels.VentCrawl

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- One map ladder, against the kernel function that renders it. -/
private def checkMapLadder (payout : Json) (key : String) (f : Nat → Nat) :
    Except String Unit := do
  let arr ← (payout.getObjVal? key) >>= Json.getArr?
  if arr.size != VentCrawl.DEPTH_CAP + 1 then
    throw s!"POAG1 vent-crawl {key} covers {arr.size} depths, kernel has \
{VentCrawl.DEPTH_CAP + 1}"
  for i in List.range (VentCrawl.DEPTH_CAP + 1) do
    match arr[i]? with
    | none => throw s!"POAG1 vent-crawl {key} has no entry for depth {i}"
    | some entry =>
        if (← entry.getNat?) != f i then
          throw s!"POAG1 vent-crawl {key} pays a map at depth {i} the kernel does not"

/-- ⚑ **The consolation on the wire IS the consolation the kernel pays.**  This is
the half `ventCrawlTableRefinesKernel` cannot see: the map ladders are not rows,
they are the payout, and `scripts/poa-design-gate.py` derives a whole risk
posture from them.  A descriptor whose `map_drowned` said `depth` where the
kernel pays `depth / 2` would carry a table that is right in every row and a
consolation that makes the deepest crawl a free roll — which is the exact defect
the pricing fixed.  `unpriced_map_is_caught` is that mutation, rendered by this
file's own encoder and refused here. -/
def ventCrawlPayoutRefinesKernel (bytes : String) : Except String Unit := do
  let document ← Json.parse bytes
  let vent ← document.getObjVal? "vent"
  let payout ← vent.getObjVal? "payout"
  exactKeys payout ["banked", "drowned", "map_banked", "map_drowned"]
  checkMapLadder payout "map_banked" VentCrawl.mapBanked
  checkMapLadder payout "map_drowned" VentCrawl.mapDrowned

/-- The first wager, flattened into a plain accept on its first haul.  This is a
descriptor that tells a client the next rung is safe and pays a fixed amount:
schema-legal, and a lie about both the water and the day. -/
def flattenedWagerRows : List VentRow :=
  let flatten : VentRow → VentRow := fun t =>
    match t.row with
    | .wager _ _ ((_, n) :: _) => { t with row := .advance n }
    | _ => t
  match ventRows.findIdx? (fun t =>
      match t.row with | .wager _ _ (_ :: _) => true | _ => false) with
  | none => ventRows
  | some i => ventRows.modify i flatten

def flattenedWagerDescriptor : String :=
  descriptorFrom ventStates flattenedWagerRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-- ⚠ A row whose PUBLISHED ODDS are softened while its successors stay right.
This is the mutation the whole design is exposed to: the hazard is the one thing
the descriptor is trusted to state, and a client that renders 1/8 where the
kernel compares against 4/8 has been handed a game with different arithmetic and
identical behaviour on every transcript that does not drown. -/
def softenedOddsRows : List VentRow :=
  let soften : VentRow → VentRow := fun t =>
    match t.row with
    | .wager fb onFlood hauls => { t with row := .wager (fb - 1) onFlood hauls }
    | _ => t
  match ventRows.findIdx? (fun t =>
      match t.row with | .wager fb _ _ => 1 < fb | _ => false) with
  | none => ventRows
  | some i => ventRows.modify i soften

def softenedOddsDescriptor : String :=
  descriptorFrom ventStates softenedOddsRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-- ⚠ A wager that drops one of its hauls — a descriptor that has quietly ruled
out a day that is still on the table.  It is the mutation that would let a
descriptor leak the instance one vein at a time. -/
def prunedHaulRows : List VentRow :=
  let prune : VentRow → VentRow := fun t =>
    match t.row with
    | .wager fb onFlood hauls => { t with row := .wager fb onFlood hauls.tail }
    | _ => t
  match ventRows.findIdx? (fun t =>
      match t.row with | .wager _ _ hauls => 1 < hauls.length | _ => false) with
  | none => ventRows
  | some i => ventRows.modify i prune

def prunedHaulDescriptor : String :=
  descriptorFrom ventStates prunedHaulRows VentCrawl.mapBanked VentCrawl.mapDrowned

/-- One row short.  Catches a table that is no longer total. -/
def truncatedDescriptor : String :=
  descriptorFrom ventStates ventRows.tail VentCrawl.mapBanked VentCrawl.mapDrowned

/-- ⚠ **The consolation, unpriced** — a descriptor that pays a drowned run the
WHOLE map instead of half of it.  Every row is right, every state view is right,
the schema is exact, and the game it describes has a free roll in it: a crawler
paid in map is never punished for going deeper, so one of the two verbs is
strictly better everywhere and there is no wager.  This is the mutation the
design gate's `posture-with-no-tradeoff` found in the real descriptor, rendered
here so the check that catches it cannot quietly stop catching it. -/
def unpricedMapDescriptor : String :=
  descriptorFrom ventStates ventRows VentCrawl.mapBanked VentCrawl.mapBanked

/-- (Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_ventCrawlDescriptor_exact_schema : Bool :=
  decide (validateVentCrawlDescriptor ventCrawlDescriptorJson = .ok ())

/-- (Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_ventCrawlDescriptor_table_is_the_kernel : Bool :=
  decide (ventCrawlTableRefinesKernel ventCrawlDescriptorJson = .ok ())

/-- (Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_ventCrawlDescriptor_views_are_the_kernel : Bool :=
  decide (ventCrawlViewsRefineKernel ventCrawlDescriptorJson = .ok ())

/-- (Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_ventCrawlDescriptor_payout_is_the_kernel : Bool :=
  decide (ventCrawlPayoutRefinesKernel ventCrawlDescriptorJson = .ok ())

/-- ⚠ **The unpriced consolation is caught, and every other check passes it.**
The three conjuncts in the middle are the point: the mutation is schema-legal and
its table and views are byte-identical to the honest ones, so nothing but the
payout check can see it.  A wire that carried it would hand the design gate a
posture with no tradeoff and hand a player a crawl with no downside.
(Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_unpriced_map_is_caught : Bool :=
  decide (unpricedMapDescriptor ≠ ventCrawlDescriptorJson) &&
  decide (validateVentCrawlDescriptor unpricedMapDescriptor = .ok ()) &&
  decide (ventCrawlTableRefinesKernel unpricedMapDescriptor = .ok ()) &&
  decide (ventCrawlViewsRefineKernel unpricedMapDescriptor = .ok ()) &&
  decide (ventCrawlPayoutRefinesKernel unpricedMapDescriptor ≠ .ok ())

/-- ⚠ The mutation happened, and it is caught.  The first conjunct is the guard
against a falsifier that stopped falsifying: without it, a `flattenedWagerRows`
that found no wager would emit the honest bytes and this check would report a
working adversary while testing nothing.
(Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_flattened_wager_is_caught : Bool :=
  decide (flattenedWagerDescriptor ≠ ventCrawlDescriptorJson) &&
  decide (ventCrawlTableRefinesKernel flattenedWagerDescriptor ≠ .ok ())

/-- ⚠ **The published odds are checked, not decorative.**  Softening one
numerator by one changes no successor and no verdict, and it is still caught.
(Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_softened_odds_are_caught : Bool :=
  decide (softenedOddsDescriptor ≠ ventCrawlDescriptorJson) &&
  decide (validateVentCrawlDescriptor softenedOddsDescriptor = .ok ()) &&
  decide (ventCrawlTableRefinesKernel softenedOddsDescriptor ≠ .ok ())

/-- (Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_pruned_haul_is_caught : Bool :=
  decide (prunedHaulDescriptor ≠ ventCrawlDescriptorJson) &&
  decide (ventCrawlTableRefinesKernel prunedHaulDescriptor ≠ .ok ())

/-- (Pinned `= true` in `VentCrawlEmitFixtures`.) -/
def check_truncated_table_is_caught : Bool :=
  decide (truncatedDescriptor ≠ ventCrawlDescriptorJson) &&
  decide (validateVentCrawlDescriptor truncatedDescriptor ≠ .ok ()) &&
  decide (ventCrawlTableRefinesKernel truncatedDescriptor ≠ .ok ())

theorem ventCrawlDescriptor_exact_schema :
    check_ventCrawlDescriptor_exact_schema = true := by native_decide

theorem ventCrawlDescriptor_table_is_the_kernel :
    check_ventCrawlDescriptor_table_is_the_kernel = true := by native_decide

theorem ventCrawlDescriptor_views_are_the_kernel :
    check_ventCrawlDescriptor_views_are_the_kernel = true := by native_decide

theorem ventCrawlDescriptor_payout_is_the_kernel :
    check_ventCrawlDescriptor_payout_is_the_kernel = true := by native_decide

theorem unpriced_map_is_caught :
    check_unpriced_map_is_caught = true := by native_decide

theorem flattened_wager_is_caught :
    check_flattened_wager_is_caught = true := by native_decide

theorem softened_odds_are_caught :
    check_softened_odds_are_caught = true := by native_decide

theorem pruned_haul_is_caught :
    check_pruned_haul_is_caught = true := by native_decide

theorem truncated_table_is_caught :
    check_truncated_table_is_caught = true := by native_decide

#assert_compiled ventCrawlDescriptor_exact_schema
#assert_compiled ventCrawlDescriptor_table_is_the_kernel
#assert_compiled ventCrawlDescriptor_views_are_the_kernel
#assert_compiled ventCrawlDescriptor_payout_is_the_kernel
#assert_compiled flattened_wager_is_caught
#assert_compiled softened_odds_are_caught
#assert_compiled pruned_haul_is_caught
#assert_compiled truncated_table_is_caught
#assert_compiled unpriced_map_is_caught

end Dregg2.Games.PathOfAngels.VentCrawlEmit
