/-
# EmitCertFMarket4 — the byte source for the market4 (3-asset / 4-order) Cert-F IR2 descriptor.

Prints `emitVmJson2 certFMarket4Descriptor` — the artifact `circuit-prove/src/cert_f_air.rs`
`include_str!`s as `circuit/descriptors/dregg-cert-f-market4-ir2.json`.

Law #1: the descriptor is AUTHORED in `Market/CertFDescriptor.lean` (`certFDescriptorOf
market4Prog`, byte-pinned there by `#guard emitVmJson2 certFMarket4Descriptor ==
Market.CertFGolden.CERT_F_MARKET4_GOLDEN`); this file only SERIALIZES it. Its emit-soundness is
NOT a per-program proof: `certFDescriptor_emit_sound` is generic over `p : CertFProg`.

    lake env lean --run EmitCertFMarket4.lean
-/
import Market.CertFDescriptor

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main : IO Unit :=
  IO.println (emitVmJson2 Market.CertFDescriptor.certFMarket4Descriptor)
