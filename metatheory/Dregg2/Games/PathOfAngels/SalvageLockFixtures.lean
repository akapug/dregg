/-
# Salvage lock — the seed-space EVALUATION, out of the crypto archive's build

`SalvageLock.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and until
2026-08-08 its seed-space enumerations ran four `native_decide` pins at elaboration — 6^6
candidate partner rows, 3^6 candidate glyph rows and all 90 seeds — so any change to the seed
space was a hard failure of every Rust proving target in the workspace (the compilation-unit
coupling the stale-fixture outage measured). The pins' STATEMENTS remain in `SalvageLock.lean`
as evaluation-free `check_* : Bool` definitions, beside the independently enumerated domains
they compare against; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged — including
`SalvageLock.seed_space_is_exactly_the_two_of_each_boards`, which `Emit.lean`'s docblock cites.

⚠ Named residue: NONE. Nothing in the parent demands a proof as data, so all four pins moved.
-/
import Dregg2.Games.PathOfAngels.SalvageLock

namespace Dregg2.Games.PathOfAngels.SalvageLock

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The partner of each plate, plate 0 first: the matching as a function. -/
def partnerRow (seed : Fin SEED_SPACE) : List (Fin 6) :=
  let ps := pairsOf seed
  allSlots.map fun slot =>
    match ps.find? (fun pr => pr.1 == slot || pr.2 == slot) with
    | some pr => if pr.1 == slot then pr.2 else pr.1
    | none => slot

/-- Every row of length `n` over an alphabet. -/
def rowsOver {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (rowsOver alphabet n).flatMap fun row => alphabet.map fun x => x :: row

/-- A perfect matching of the six plates is exactly a fixed-point-free involution of
them: no plate is its own partner, and partnering twice returns. -/
def isPerfectMatchingB (row : List (Fin 6)) : Bool :=
  (List.finRange 6).all fun i =>
    let j := row.getD i.val i
    j != i && row.getD j.val j == i

/-- All perfect matchings of six plates, over all 6^6 candidate partner rows. -/
def allMatchings : List (List (Fin 6)) :=
  (rowsOver (List.finRange 6) 6).filter isPerfectMatchingB

/-- All six-plate boards carrying two copies of each glyph, over all 3^6 candidate
glyph rows. -/
def allBoards : List (List (Fin 3)) :=
  (rowsOver (List.finRange 3) 6).filter fun row =>
    (List.finRange 3).all fun g => (row.filter (fun x => x == g)).length == 2

/-- The matchings the seed space actually produces. -/
def realizedMatchings : List (List (Fin 6)) :=
  ((List.finRange SEED_SPACE).map partnerRow).eraseDups

/-- The boards the seed space actually produces. -/
def realizedBoards : List (List (Fin 3)) :=
  ((List.finRange SEED_SPACE).map boardRow).eraseDups

/-- Six plates admit exactly 15 perfect matchings; every seed names one of them, and
every one of them is named by some seed.  This is the statement the old board failed:
its 3 seeds named ONE matching.
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_seed_space_realizes_every_perfect_matching : Bool :=
  allMatchings.length == 15 &&
  realizedMatchings.length == 15 &&
  realizedMatchings.all isPerfectMatchingB &&
  allMatchings.all (fun m => realizedMatchings.contains m)

/-- The 90 seeds name 90 distinct boards, and those are exactly the boards carrying
two copies of each glyph: the seed-to-board map is a bijection onto them, so the
seed space is neither degenerate nor redundant.
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_seed_space_is_exactly_the_two_of_each_boards : Bool :=
  allBoards.length == SEED_SPACE &&
  realizedBoards.length == SEED_SPACE &&
  allBoards.all (fun b => realizedBoards.contains b)

/-- Six seeds share each matching — the 3! relabellings of its pairs — so a glyph
name carries no information about the pairing beyond agreement with a glyph already
seen.  A canonical labelling would leak: "this plate shows glyph 0" would mean "this
plate is plate 0's partner".
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_every_matching_has_all_six_labellings : Bool :=
  realizedMatchings.all fun m =>
    ((List.finRange SEED_SPACE).filter (fun s => partnerRow s == m)).length == 6

def glyphPopulation (seed : Fin SEED_SPACE) (glyph : Fin 3) : Nat :=
  (allSlots.filter (fun slot => glyphAt seed slot = glyph)).length

/-- Generated boards contain exactly two of each glyph, for every seed.
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_glyph_population_two : Bool :=
  (List.finRange SEED_SPACE).all fun seed =>
    (List.finRange 3).all fun glyph => glyphPopulation seed glyph == 2

theorem seed_space_realizes_every_perfect_matching :
    check_seed_space_realizes_every_perfect_matching = true := by native_decide

theorem seed_space_is_exactly_the_two_of_each_boards :
    check_seed_space_is_exactly_the_two_of_each_boards = true := by native_decide

theorem every_matching_has_all_six_labellings :
    check_every_matching_has_all_six_labellings = true := by native_decide

theorem glyph_population_two :
    check_glyph_population_two = true := by native_decide

#assert_compiled seed_space_realizes_every_perfect_matching
#assert_compiled seed_space_is_exactly_the_two_of_each_boards
#assert_compiled every_matching_has_all_six_labellings
#assert_compiled glyph_population_two

end Dregg2.Games.PathOfAngels.SalvageLock
