import Dregg2.Games.PrivateShuffleFairDescriptor

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main : IO Unit :=
  IO.println (emitVmJson2
    Dregg2.Games.PrivateShuffleFairDescriptor.privateShuffleFairN8Descriptor)
