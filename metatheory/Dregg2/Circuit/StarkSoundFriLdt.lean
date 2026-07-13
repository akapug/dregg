import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.StarkSoundDischarge

namespace Dregg2.Circuit.StarkSoundFriLdt

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.AlgoStarkSoundTransferV3
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **StarkSound for deployed transferV3 from the canonical `FriLdtExtractV3` bundle — carrier-free.**
Composes `algoStarkSound_transferV3` (AlgoStarkSound from the FRI-LDT extraction bundle + Poseidon2 CR)
with `starkSound_of_algoStarkSound` (StarkSound from AlgoStarkSound, DeployedRefines discharged), at the
deployed config. Reduces the apex to `FriLdtExtractV3` — whose fields are the honest FS/commitment floor
(the ε ≤ deg/|F| bounded-advantage form) — plus Poseidon2 CR and the cfgView/cfg* KAT floor. -/
theorem starkSound_of_friLdtExtract_transferV3
    (sponge : List Int → Int) (hCR : Poseidon2SpongeCR sponge) (hash : List Int → Int)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView) :
    StarkSound hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3) :=
  @starkSound_of_algoStarkSound hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3)
    (algoStarkSound_transferV3 sponge hCR hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView hfri)

#assert_axioms starkSound_of_friLdtExtract_transferV3

end Dregg2.Circuit.StarkSoundFriLdt
