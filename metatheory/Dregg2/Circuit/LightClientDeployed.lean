import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.StarkSoundDischarge

/-!
# The TOP theorem, deployed: `lightclient_unfoolable` for transferV3 on the honest floor

`lightclient_unfoolable_via_algo` (FriVerifierBridge) is the apex light-client soundness statement — a
verifying batch pins the pre/post kernel state — but it still TAKES `[AlgoStarkSound]` and
`href : DeployedRefines` as assumptions. This file discharges BOTH at the deployed config:
`AlgoStarkSound` from `algoStarkSound_transferV3` (the canonical `FriLdtExtractV3` bundle + Poseidon2 CR),
and `DeployedRefines` from `deployedRefines_cfg` (a theorem, since `verifyBatch` is now a `def`). The
result: the end-to-end light-client theorem for the deployed transferV3 slice, through the reduced
`verifyBatch`, resting on exactly the honest floor — `FriLdtExtractV3` (FS-soundness, ROM) + Poseidon2 CR
+ the surface refinement (`kstep`/`hrefines`/`hwitdec`) + the `cfgView`/`cfg*` KAT wire. No `[StarkSound]`
carrier, no `[AlgoStarkSound]` carrier, no `DeployedRefines` assumption.
-/

namespace Dregg2.Circuit.LightClientDeployed

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.AlgoStarkSoundTransferV3
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec

/-- **`lightclient_unfoolable` for the deployed transferV3, on the honest floor.** A batch that the
reduced `verifyBatch` accepts pins the pre/post kernel state (`StateDecode` + `kstep` + the commitment
equalities) — with `[AlgoStarkSound]` discharged from the `FriLdtExtractV3` bundle and `DeployedRefines`
discharged by `deployedRefines_cfg`. The remaining inputs are exactly the honest floor: the FS-soundness
bundle `hfri`, the two collision-resistance facts, and the surface refinement. -/
theorem lightclient_unfoolable_deployed_transferV3
    (sponge : List Int → Int) (hCR_sponge : Poseidon2SpongeCR sponge)
    (hash : List Int → Int) (hCR : Poseidon2SpongeCR hash)
    (S : CommitSurface)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash
      ((fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3) e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3) S pi)
    (hacc : verifyBatch (vkOfRegistry (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3)) pi π
      = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  @lightclient_unfoolable_via_algo hash S
    (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3)
    cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView
    (algoStarkSound_transferV3 sponge hCR_sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore
      cfgA cfgInitState cfgLogN cfgView hfri)
    (deployedRefines_cfg (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3))
    hCR kstep hrefines pi π hwitdec hacc

#assert_axioms lightclient_unfoolable_deployed_transferV3

end Dregg2.Circuit.LightClientDeployed
