/-
# Dregg2.Circuit.Emit.EmitGraduate — focused scratch emitter for the cutover-graduating descriptors.

Prints `<defName>\t<descriptor.name>\t<emitVmJson descriptor>` for ONLY the descriptors whose Lean
emit modules already tick the runtime nonce (the EmitAllJson runner is currently broken by the
parameterized queue descriptors, so this avoids importing them). Run:

  `lake env lean --run Dregg2/Circuit/Emit/EmitGraduate.lean`
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair
import Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize

open Dregg2.Circuit.Emit.EffectVmEmit (emitVmJson)

def main : IO Unit := do
  IO.println s!"createSealPairVmDescriptor\t{(Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair.createSealPairVmDescriptor).name}\t{emitVmJson Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair.createSealPairVmDescriptor}"
  IO.println s!"bridgeFinalizeVmDescriptor\t{(Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize.bridgeFinalizeVmDescriptor).name}\t{emitVmJson Dregg2.Circuit.Emit.EffectVmEmitBridgeFinalize.bridgeFinalizeVmDescriptor}"
