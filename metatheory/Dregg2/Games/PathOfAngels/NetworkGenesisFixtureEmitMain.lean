/-
# Network-genesis fixture emit driver

The four `dregg-lean-ffi/tests/fixtures/poa-network-genesis-*-v1.json` files are a RENDER of
`NetworkGenesis.fixtureInput`, not a second source of truth.  This driver writes them from Lean
(`emit`) and refuses when the files on disk differ from what Lean renders (`check`).

| file          | Lean render                                         |
|---------------|-----------------------------------------------------|
| `input`       | `fixtureInputBytes`  (= `fixtureInput.toJson`)      |
| `output`      | `fixtureOutputBytes` (= `networkGenesisFFI` of it)  |
| `config`      | `fixtureConfigJson`                                 |
| `canon`       | `fixtureCanonJson`                                  |

Each file is the render followed by exactly one `\n`.  `check` compares the WHOLE file
byte-for-byte, so a one-byte edit anywhere — a hex digit, a counter, a dropped newline — refuses
and names the file.

## Why this exists (2026-10-01)

The frozen input sat at content counter 2 for eight weeks while Lean's constants and the signed
POAG1 bundle moved on.  The only tie between Lean's `fixtureInputBytes` and the file was a
one-off `#eval` a lane ran by hand.  `scripts/check-poa-genesis-fixture.sh` runs this driver in
`check` mode and is a `scripts/local-gates.sh` row (`poa-genesis-fixture`, with a `-red` row that
plants a one-byte edit in a scratch copy and requires the refusal).

## Modes

    emit  (default)                writes the four files
    POA_GENESIS_FIXTURE_MODE=check re-renders and refuses on any byte of drift

Directory: `POA_GENESIS_FIXTURE_DIR`, default `../dregg-lean-ffi/tests/fixtures` (relative to
the `metatheory/` working directory `lake env lean --run` is invoked from).

    cd metatheory && POA_GENESIS_FIXTURE_MODE=check \
      lake env lean --run Dregg2/Games/PathOfAngels/NetworkGenesisFixtureEmitMain.lean

Before writing or accepting anything the driver requires that Lean itself accepts the fixture:
the input re-decodes to `fixtureInput`, the evaluator emits a non-empty output, and that output is
the exact authorized re-emission (`decodeValidatedGenesisOutput`).  A fixture Lean refuses is
never written.
-/
-- `NetworkGenesisFixtures` re-exports `NetworkGenesis`, and is where the fixture laboratory
-- lives once `node-init-86` moves it out of the runtime module; importing it keeps this driver
-- correct on both sides of that move.
import Dregg2.Games.PathOfAngels.NetworkGenesisFixtures

open Dregg2.Games.PathOfAngels.NetworkGenesis
open Dregg2.Games.PathOfAngels.NetworkGenesisWire

set_option autoImplicit false

namespace Dregg2.Games.PathOfAngels.NetworkGenesisFixtureEmit

def refuse {α : Type} (what : String) : IO α :=
  throw (IO.userError s!"REFUSED: {what}")

def require (what : String) : Bool → IO Unit
  | true => pure ()
  | false => refuse what

/-- The four renders, by file stem. -/
def renders : List (String × String) :=
  [("input", fixtureInputBytes), ("output", fixtureOutputBytes),
   ("config", fixtureConfigJson), ("canon", fixtureCanonJson)]

def fileOf (dir : System.FilePath) (stem : String) : System.FilePath :=
  dir / s!"poa-network-genesis-{stem}-v1.json"

def fixtureDir : IO System.FilePath := do
  pure ⟨(← IO.getEnv "POA_GENESIS_FIXTURE_DIR").getD "../dregg-lean-ffi/tests/fixtures"⟩

/-- Lean must accept its own fixture before any byte of it is written or vouched for. -/
def requireLeanAccepts : IO Unit := do
  require "fixtureInputBytes does not re-decode to fixtureInput"
    (decide (decodeGenesisInput fixtureInputBytes = some fixtureInput))
  require "the Lean evaluator refuses fixtureInputBytes" (fixtureOutputBytes != "")
  require "the evaluator's output is not the exact authorized re-emission"
    (decodeValidatedGenesisOutput fixtureInputBytes fixtureOutputBytes).isSome

def writeAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let staged := System.FilePath.mk (path.toString ++ ".partial")
  IO.FS.writeFile staged contents
  IO.FS.rename staged path

def emitMode : IO Unit := do
  requireLeanAccepts
  let dir ← fixtureDir
  for (stem, body) in renders do
    writeAtomic (fileOf dir stem) (body ++ "\n")
    IO.println s!"wrote {fileOf dir stem} ({(body ++ "\n").utf8ByteSize} bytes)"

def checkMode : IO Unit := do
  requireLeanAccepts
  let dir ← fixtureDir
  let mut drift : List String := []
  for (stem, body) in renders do
    let path := fileOf dir stem
    if !(← path.pathExists) then
      drift := drift ++ [s!"MISSING {path}"]
    else
      let onDisk ← IO.FS.readFile path
      if onDisk != body ++ "\n" then
        drift := drift ++ [s!"DRIFT {path}"]
  if drift.isEmpty then
    IO.println s!"poa network-genesis fixtures are Lean's render, byte-exact ({renders.length} files)"
  else
    for line in drift do IO.eprintln line
    refuse s!"{drift.length} of {renders.length} network-genesis fixture file(s) differ from \
      Lean's render; re-emit with `lake env lean --run \
      Dregg2/Games/PathOfAngels/NetworkGenesisFixtureEmitMain.lean` from metatheory/ and \
      review the diff — never hand-edit them"

end Dregg2.Games.PathOfAngels.NetworkGenesisFixtureEmit

open Dregg2.Games.PathOfAngels.NetworkGenesisFixtureEmit in
def main : IO Unit := do
  match (← IO.getEnv "POA_GENESIS_FIXTURE_MODE").getD "emit" with
  | "emit" => emitMode
  | "check" => checkMode
  | other => refuse s!"unknown POA_GENESIS_FIXTURE_MODE `{other}`"
