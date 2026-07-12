/-
# EmitWideTransferProbe — ADDITIVE wide-transfer descriptor emit (STAGED slice).

Prints ONE TSV line:

  `transferVmDescriptor2R24Wide\t<name>\t<emitVmJson2 (wide transfer)>`

from the verified wide registry `v3RegistryWide` (the transfer member at index 0 =
`wideAppend transferV3 bb (bb+239)`, host + the 960-column wide appendix). This is the byte source of the
ADDITIVE Rust artifact `circuit/descriptors/rotation-wide-transfer-staged.tsv` the wide-roundtrip
slice consumes — NOTHING on the live 1-felt wire path changes (`v3RegistryCapOpen` / the live TSV
are UNTOUCHED). SCRATCH executable: `lake env lean --run EmitWideTransferProbe.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (v3RegistryWide)

def main : IO Unit := do
  -- transfer is index 0 of the wide cohort (member-for-member with the live registry).
  match v3RegistryWide with
  | (_, d) :: _ =>
      IO.println s!"transferVmDescriptor2R24Wide\t{d.name}\t{emitVmJson2 d}"
  | [] => IO.eprintln "v3RegistryWide is empty"
