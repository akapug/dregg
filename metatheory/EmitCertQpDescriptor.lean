import Market.CertQpDescriptor

open Market.CertQpDescriptor
open Dregg2.Circuit.DescriptorIR2

def main : IO Unit :=
  IO.println (emitVmJson2 portfolioDescriptor)

