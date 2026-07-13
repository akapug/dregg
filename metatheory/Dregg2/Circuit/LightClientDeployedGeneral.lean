import Dregg2.Circuit.StarkSoundColumnCfg
import Dregg2.Circuit.StarkSoundDischarge

/-!
# The TOP theorem, deployed, for ANY registry — `lightclient_unfoolable` on the honest floor, general R

The transferV3 knot (`LightClientDeployed`) tied the apex to the honest floor for the deployed transfer
slice. This ties it for an ARBITRARY registry `R`. The base `lightclient_unfoolable` (CircuitSoundness)
takes `[StarkSound hash R]`; `starkSound_of_columnDecode_cfg` (StarkSoundColumnCfg) PRODUCES exactly that
for any `R` — through the reduced `verifyBatch`, with `DeployedRefines` discharged by `deployedRefines_cfg`
and the commitment binding resting on the PROVED `commitmentOpening_binds_of_poseidon2CR`. So the
top-level unfoolability statement for any effect rests on the honest floor: the `ColumnDecodeBridge` + the
per-accept `hood` (proximity ⟹ satisfying trace) + Poseidon2 CR + the `cfgView`/`cfg*` KAT wire — no
`[StarkSound]` carrier assumed anywhere.
-/

namespace Dregg2.Circuit.LightClientDeployedGeneral

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.FriColumnDecode
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.StarkSoundColumnCfg
open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt memLog mapLog opRow)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DeployedTraceExtract
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Exec

/-- **`lightclient_unfoolable` for an ARBITRARY registry, on the honest floor.** A batch the reduced
`verifyBatch` accepts pins the pre/post kernel state, for any effect `R` — with `[StarkSound]` discharged
by `starkSound_of_columnDecode_cfg`. The remaining inputs are the honest floor: a `ColumnDecodeBridge`,
the per-accept `hood` (proximity ⟹ satisfying trace), Poseidon2 CR, and the surface refinement. -/
theorem lightclient_unfoolable_deployed_general
    (hash : List Int → Int) (hCR : Poseidon2SpongeCR hash) (S : CommitSurface) (R : Registry)
    (B : ColumnDecodeBridge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN cfgView)
    (hood : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN
          (cfgView pi π).1 (cfgView pi π).2 = true →
      decodeColumn (B.column pi π) ∈ friSetupK8.C →
      ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
          (_ood : Dregg2.Circuit.FieldIntegerLift.OodInterpF (R pi.effect) t),
        (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
            c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
        (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
        (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
        maddrs.Nodup ∧
        (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
        MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
        MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
        t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
        t.tf .mapOps = mapLog (R pi.effect) t ∧
        tracePublishedCommit t = pi.toPublished)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  @lightclient_unfoolable hash S R hCR
    (starkSound_of_columnDecode_cfg hash R B hood) kstep hrefines pi π hwitdec hacc

#assert_axioms lightclient_unfoolable_deployed_general

end Dregg2.Circuit.LightClientDeployedGeneral
