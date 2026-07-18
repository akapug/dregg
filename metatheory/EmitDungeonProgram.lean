/-
# EmitDungeonProgram — the descent cell-program emit executable.

Prints the checked-in JSON artifact for the DEPLOYED descent teeth
(`Dregg2.Games.Dungeon.Prog.dungeonProgram`), the Lean-sourced object
`dungeon-on-dregg/src/descent.rs::Deployment::program()` loads. The bytes are the
byte-exact output of this verified emit; the checked-in
`dungeon-on-dregg/program/dungeon_program.json` is a CACHE of this emission (Lean is the
source of truth), regenerate-and-diff gated by `dungeon-on-dregg/program/regen.sh`.

Run:  lake env lean --run EmitDungeonProgram.lean
-/
import Dregg2.Games.DungeonProgram

open Dregg2.Games.Dungeon.Prog (dungeonProgram emitJson)

def main : IO Unit :=
  IO.print (emitJson dungeonProgram)
