/-
# EmitCertF — the byte source for the ring-3 Cert-F IR2 descriptor.

Prints `emitVmJson2 certFDescriptor` — the artifact `circuit-prove/src/cert_f_air.rs:297`
`include_str!`s as `circuit/descriptors/dregg-cert-f-ir2.json`.

Until this file, `dregg-cert-f-ir2.json` was the ONLY flat descriptor no emitter reproduced (a
routing gap `GOAL-STARK-KILL.md` tracks): it is `include_str!`d into a live AIR yet sat outside the
`scripts/emit-descriptors.sh` re-derivation, so the drift gate could not see it move.

Law #1: the descriptor is AUTHORED in `Market/CertFDescriptor.lean` (`certFDescriptorOf ring3Prog`,
byte-pinned there by `#guard emitVmJson2 certFDescriptor == Market.CertFGolden.CERT_F_RING3_GOLDEN`
at :207); this file only SERIALIZES it.

    lake env lean --run EmitCertF.lean
-/
import Market.CertFDescriptor

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main : IO Unit :=
  IO.println (emitVmJson2 Market.CertFDescriptor.certFDescriptor)
