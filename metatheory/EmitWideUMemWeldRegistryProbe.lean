/-
# EmitWideUMemWeldRegistryProbe — the Lean-emitted WIDE+UMEM WELDED registry TSV (STAGED slice).

Prints ONE TSV line per WELDED wide member, in the EXACT order + key set of
`CapOpenEmit.v3RegistryCapOpenWide` (so the welded registry is a member-for-member, name-stable
COVER of the wide registry's emit-source members):

  `<live key>\t<welded member.name>\t<emitVmJson2 (welded member)>`

Each welded member is the purely-ADDITIVE `weldUMemIntoWide host (wideKeyUMemDomain key)` of the
corresponding wide member — the single-domain cohort `umemOp` over 7 fresh columns + the
`umemory` / `umem_boundary` tables appended PAST the wide carriers, `piCount` UNCHANGED (the 16
wide-commit PIs / the 8-felt anchors ride through, NO narrowing).

This is the byte source of the ADDITIVE Rust artifact
`circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv` (pinned by
`WIDE_UMEM_WELD_REGISTRY_FP`). NOTHING on the live wire changes — the deployed bare wide registry /
FP / VK are UNTOUCHED, `umem_witness_enabled` stays false.

SCRATCH executable: `lake env lean --run EmitWideUMemWeldRegistryProbe.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide (weldedWideRegistry)

def main : IO Unit := do
  for (key, d) in weldedWideRegistry do
    IO.println s!"{key}\t{d.name}\t{emitVmJson2 d}"
