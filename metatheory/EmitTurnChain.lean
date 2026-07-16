/-
# EmitTurnChain — the byte source for the turn-chain binding descriptor.

Prints `<name>\t<emitVmJson2 descriptor>` for `dregg-turn-chain-binding-v2`, the Lean authorship of
what `circuit-prove/src/ivc_turn_chain.rs::TurnChainBindingAir` hand-authors in 14 sites (the deployed
whole-history chain proof `grain-verify/src/r3.rs:139` runs). Same mechanism as `EmitRotationV3.lean`:
run it, byte-pin the output as the descriptor JSON + the emit-gate `GOLDEN_JSON`.

    lake env lean --run EmitTurnChain.lean

Law #1: the constraints are AUTHORED in `Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean` (proved
there, with refutation teeth); this file only SERIALIZES them. Rust interprets; Rust authors nothing.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding (turnChainBindingDescriptor)

def main : IO Unit :=
  IO.println s!"{turnChainBindingDescriptor.name}\t{emitVmJson2 turnChainBindingDescriptor}"
