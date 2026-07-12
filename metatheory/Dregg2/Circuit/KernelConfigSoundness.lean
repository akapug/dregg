/-
# `Dregg2.Circuit.KernelConfigSoundness` — THE HONEST CONFIG-EVOLUTION CAPSTONE.

The kernel STARK object `AlgoStarkSoundKernel.algoStarkSound_kernel` lands at `Satisfied2` (trace
satisfaction). The apex `CircuitSoundnessAssembled.lightclient_unfoolable_assembled` lands at the
config transition `kstepAll` but CARRIES the config bridge as the opaque `∀ e, EffectDecodeBridge`.
This module assembles the two at the RIGHT altitude and stops re-assuming the bridge:

  **`kernelConfigSound`** — `verifyBatch`-accept over the LIVE registry `Rfix`  ⟹  a REAL
  frame-respecting kernel-config transition `fullActionStep pre fa post` (the proved declarative
  kernel `⟺ execFullA`), with `actionTag fa = pi.effect`, decoded endpoints `StateDecode`, and the
  published-commitment frame. This is `kstepAll pi.effect pre post` UNFOLDED to expose the genuine
  transition `∃ fa, actionTag fa = pi.effect ∧ fullActionStep pre fa post` at the surface.

## How it is assembled (composition, not a new bridge)

  * **STARK layer** — the ENUMERATED kernel object, not an opaque `[StarkSound]`:
    `AlgoStarkSoundKernel.algoStarkSound_kernel` builds `AlgoStarkSound hash Rfix` from its named
    floor; `FriVerifierBridge.starkSound_of_verifyAlgo` lifts it (with the code-refinement
    `DeployedRefines`) to the apex carrier `StarkSound hash Rfix`. So the STARK carrier is the
    per-effect fan-out object, not a smuggled class.
  * **CONFIG layer** — the ASSEMBLED bridge, not a re-assumed one:
    `ClosureFanoutGenuine.lightclient_unfoolable_closed_final_genuine` reaches `kstepAll` through
    `closedLogExtract_all_genuine` (the 36-way `actionTag` split, EVERY slot calling its proven
    `<e>_closedLog` rung). The config bridge `Satisfied2 ⟹ kstepAll` is therefore the assembled
    `closedLogExtract_all_genuine`, NOT a re-assumed `EffectDecodeBridge`.
  * **UNFOLD** — `kstepAll = CircuitSoundness.dispatchArm`, and `dispatchArm e pre post =
    ∃ fa, actionTag fa = e ∧ fullActionStep pre fa post` (definitionally). So the capstone concludes
    the REAL config transition `fullActionStep` — the proved declarative kernel over
    `RecordKernelState` (heap/nullifier/commitment/balance/caps evolution), with per-effect frame.

## The HONEST residual of `kernelConfigSound` — stated precisely, nothing laundered

The conclusion rests on EXACTLY the following, all NAMED hypotheses (never axioms, never opaque
`StarkSound`/`EffectDecodeBridge`):

  ALLOWED FLOOR (the crypto modulus — do NOT discharge):
    * `Poseidon2SpongeCR hash` + `Poseidon2SpongeCR sponge` — the commitment-binding hash floor.
    * `hfri : ∀ e, FriLdtExtract … (Rfix e)` — the `{FRI-LDT @ deployed}` extraction, per effect tag.

  THE ONE GENUINE ASSUMPTION beyond the allowed modulus (the residual the SCOPE doc names,
  `docs/reference/CONFIG-EVOLUTION-SOUNDNESS-SCOPE.md` §Layer-1.3):
    * `hrec : ∀ e, MapReconcileFamily … (Rfix e)` — its ONLY non-vacuous content is the
      `CanonicalHeapTree` knowledge-extraction at the 7 mapOp effects (tags 17/27/28 accumulator
      inserts, 56 heapWrite, 39 refusal fields-write, 19 spawn, 18 factory); VACUOUS at every
      lookup-shaped member. This is `CanonicalHeapExtract`, pending its own modeling lane.

  NAMED-BUT-NOT-YET-DISCHARGED (the honest gap vs the aspiration: the SCOPE doc's "NEEDS-A-LEMMA"
  wiring items — NO discharger exists in the tree; carried, NOT claimed discharged):
    * `hbusF : ∀ e, BusModelFamily … (Rfix e)` — the LogUp bus models (SCOPE §Layer-1.2: reduces
      into `{Poseidon2SpongeCR, FRI-LDT}` by a wiring lemma that is NOT yet proven).
    * `hasm : ∀ e, MapTableAssembly … (Rfix e)` — the table-assembly faithfulness (SCOPE §Layer-1.4:
      near-floor, bundle-able with `FriLdtExtract`; wiring lemma NOT yet proven).
    * `rds : ClosureReadouts …` — the per-effect `<e>TraceReadout` (`Satisfied2 ⟹ <e>Encodes`
      limb-decode; SCOPE §Layer-2: the `WitnessDecodes`-class extraction floor).
    * `hwitdec : WitnessDecodes hash Rfix S pi` — the witness→kernel-state existence rung.
    * `href : DeployedRefines Rfix …` — the Rust `verify_batch` ↔ Lean `verifyAlgo` code refinement.
    * `mkLog` — `StateDecode ⟹ StateDecodeLog` (structural, the commitment-surface log projection).

So the residual is HONESTLY LARGER than the aspirational `{Poseidon2, FRI-LDT, CanonicalHeapExtract}`:
the bus/table modeling (`hbusF`/`hasm`), the per-effect decode readout bundle (`rds`), the witness
existence + code-refinement + log-projection wiring remain carried, because the discharge lemmas the
SCOPE doc classifies as "NEEDS-A-LEMMA" are NOT present in the tree and cannot be manufactured
soundly here. Nothing is faked: every carried fact is a named `Prop`/`Type` hypothesis, the STARK
carrier is the enumerated `algoStarkSound_kernel` (not opaque `[StarkSound]`), and the config bridge
is the assembled `closedLogExtract_all_genuine` (not a re-assumed `EffectDecodeBridge`).

## Discipline

Sorry-free; no `decide`/`Fintype` over field-sized objects (BabyBear never computed — the composition
is term-level plumbing); no axiom beyond Lean's own. NEW file; imports read-only; builds targeted
(`lake build Dregg2.Circuit.KernelConfigSoundness`).
-/
import Dregg2.Circuit.AlgoStarkSoundKernel
import Dregg2.Circuit.ClosureFanoutGenuine
import Dregg2.Circuit.FriVerifierBridge

namespace Dregg2.Circuit.KernelConfigSoundness

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts lightclient_unfoolable_closed_final_genuine)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.DescriptorIR2 (VmTrace)
open Dregg2.Circuit.FriVerifierBridge
  (AlgoStarkSound ProofView DeployedRefines starkSound_of_verifyAlgo)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith fullChecks)
open Dregg2.Circuit.AlgoStarkSoundGeneral (FriLdtExtract BusModelFamily)
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory (MapReconcileFamily MapTableAssembly)
open Dregg2.Circuit.AlgoStarkSoundKernel (algoStarkSound_kernel)
open Dregg2.Circuit.ActionDispatch (actionTag fullActionStep)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA)

set_option autoImplicit false

section
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}

local notation "Slive" =>
  S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-- **`kernelConfigSound` — verifyBatch-accept over `Rfix` ⟹ a REAL kernel-config transition.**

From the STARK-side floor (Poseidon2 CR ×2, `FriLdtExtract`, `BusModelFamily`, `MapReconcileFamily`,
`MapTableAssembly`, `DeployedRefines`) composed through `algoStarkSound_kernel` +
`starkSound_of_verifyAlgo`, and the config-side genuine readout bundle (`ClosureReadouts`, `mkLog`,
`WitnessDecodes`) composed through `closedLogExtract_all_genuine`, a `verifyBatch`-accepted batch at
ANY published effect tag yields decoded endpoints `pre`/`post` and a GENUINE action `fa` with
`actionTag fa = pi.effect` performing the proved declarative kernel step `fullActionStep pre fa post`
(the real heap/nullifier/commitment/balance/caps transition, `⟺ execFullA`, with per-effect frame),
whose endpoints commit to the published `(pi.pre, pi.post)`. The light client RAN NOTHING.

This is `lightclient_unfoolable_closed_final_genuine`'s `kstepAll pi.effect pre post` UNFOLDED
(`kstepAll = dispatchArm`, definitionally the `∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`
arm), with the opaque `[StarkSound]` REPLACED by the enumerated kernel STARK object. See the module
header for the EXACT residual (the config bridge is the assembled `closedLogExtract_all_genuine`, NOT
a re-assumed `EffectDecodeBridge`). -/
theorem kernelConfigSound
    {F : Type*} [Field F] [DecidableEq F]
    {State : Type} {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (LH : List Turn → ℤ)
    -- the ONE shared commitment hash + its collision-resistance floor
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    -- the STARK-side FRI/constraint sponge + its collision-resistance floor
    (sponge : List ℤ → ℤ) (hCRs : Poseidon2SpongeCR sponge)
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : EffectIdx → BatchPublicInputs → BatchProof → VmTrace)
    -- ★ ALLOWED FLOOR: FRI-LDT @ the deployed descriptor, per effect tag.
    (hfri : ∀ e : EffectIdx, FriLdtExtract sponge perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    -- ★ NEEDS-A-LEMMA (carried, NOT discharged): the LogUp bus models.
    (hbusF : ∀ e : EffectIdx, BusModelFamily fp embed perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    -- ★ THE ONE GENUINE ASSUMPTION: CanonicalHeapExtract at the 7 mapOp effects (vacuous elsewhere).
    (hrec : ∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    -- ★ NEEDS-A-LEMMA (carried, NOT discharged): the table-assembly faithfulness pair.
    (hasm : ∀ e : EffectIdx, MapTableAssembly perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    -- ★ code-refinement residual: Rust verify_batch ↔ Lean verifyAlgo.
    (href : DeployedRefines Rfix perm RATE toNat params vk
        (fullChecks core A toNat params.powBits) initState logN view)
    -- ★ the config-side per-effect decode readouts (WitnessDecodes-class) + log projection.
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode Slive pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash Rfix Slive pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ (pre post : RecChainedState) (fa : FullActionA),
      StateDecode Slive pi.toPublished pre post ∧
      actionTag fa = pi.effect ∧
      fullActionStep pre fa post ∧
      pi.pre = (Slive).commit pre.kernel pi.turn ∧
      pi.post = (Slive).commit post.kernel pi.turn := by
  -- STARK layer: the ENUMERATED kernel object → AlgoStarkSound → StarkSound (opaque carrier gone).
  haveI hAlgo : AlgoStarkSound hash Rfix perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
    algoStarkSound_kernel sponge hCRs hash hCRh fp embed perm RATE toNat params vk core A
      initState logN view tr hfri hbusF hrec hasm
  haveI hSS : StarkSound hash Rfix :=
    starkSound_of_verifyAlgo hash Rfix perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view href
  -- CONFIG layer: closedLogExtract_all_genuine (the ASSEMBLED bridge) → kstepAll.
  obtain ⟨pre, post, hdec, hstep, hc1, hc2⟩ :=
    lightclient_unfoolable_closed_final_genuine hash LH hCRh rds mkLog pi π hwitdec hacc
  -- UNFOLD kstepAll = dispatchArm to expose the REAL config transition fullActionStep.
  obtain ⟨fa, htag, hfull⟩ := hstep
  exact ⟨pre, post, fa, hdec, htag, hfull, hc1, hc2⟩

end

/-! ## Kernel-clean keystone (0 sorries; axiom floor is Lean's own). -/

#assert_axioms kernelConfigSound

end Dregg2.Circuit.KernelConfigSoundness
