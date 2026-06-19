/-
# EmitWideRegistryProbe — ADDITIVE full wide-registry descriptor emit (STAGED slice 2).

Prints ONE TSV line per member of the verified `v3RegistryCapOpenWide` (the 45 emit-source members
made 8-felt-wide via the proven `wideAppend`):

  `<member.name>\t<member.name>\t<emitVmJson2 (wide member)>`

(the key column is the descriptor's own `.name`, so the Rust roundtrips look the member up by name).
This is the byte source of the ADDITIVE Rust artifact `circuit/descriptors/rotation-wide-registry-
staged.tsv` the per-family wide-roundtrip slice consumes — NOTHING on the live 1-felt wire path
changes (`v3RegistryCapOpen` / the live TSV / FP / VK are UNTOUCHED). The wide transfer single-line
TSV (`EmitWideTransferProbe.lean`) stays beside this, byte-identical — this is the FULL cohort.

SCRATCH executable: `lake env lean --run EmitWideRegistryProbe.lean`.
-/
import Dregg2.Circuit.Emit.CapOpenEmit

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.CapOpenEmit (v3RegistryCapOpenWide)

def main : IO Unit := do
  -- the 45 wide members, one `key\tname\tjson` line each (key = the live registry key, mirroring
  -- `rotation-v3-staged-registry.tsv` so the Rust roundtrips look the wide member up by its
  -- familiar key `burnVmDescriptor2R24` etc.).
  for (key, d) in v3RegistryCapOpenWide do
    IO.println s!"{key}\t{d.name}\t{emitVmJson2 d}"
