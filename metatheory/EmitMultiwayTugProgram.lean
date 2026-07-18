/-
# EmitMultiwayTugProgram — the multiway-tug cell-program emit executable.

Prints the checked-in JSON artifact for the DEPLOYED tug play-teeth
(`Dregg2.Games.MultiwayTug.Prog.multiwayTugProgram`), the Lean-sourced object
`dregg-multiway-tug/src/state.rs::Deployment::program()` loads. The bytes are the byte-exact
output of this verified emit; the checked-in
`dregg-multiway-tug/program/multiway_tug_program.json` is a CACHE of this emission (Lean is the
source of truth), regenerate-and-diff gated by `dregg-multiway-tug/program/regen.sh`.

Run:  lake env lean --run EmitMultiwayTugProgram.lean
-/
import Dregg2.Games.MultiwayTugProgram

open Dregg2.Games.MultiwayTug.Prog (multiwayTugProgram emitJson)

def main : IO Unit :=
  IO.print (emitJson multiwayTugProgram)
