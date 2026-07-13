/-
# `Dregg2.Circuit.StarkSoundReduce` — the TRACE-COMMITMENT sponge side of StarkSound, DE-VACUATED.

`AlgoStarkSoundTransferV3` rests its Merkle/commitment-opening step on `Poseidon2SpongeCR sponge` —
full sponge injectivity, PROVEN FALSE at any real compressing hash — so at deployment the chain
`hood_of_reductions → mainAirAcceptF_of_floor → algoStarkSound_transferV3 →
lightclient_unfoolable_deployed apex` fired only under an unsatisfiable premise (that apex is now
deleted; this module is its replacement). This module
builds the reduction-form (`OrBreak`) twins of that whole chain, DROPPING `Poseidon2SpongeCR sponge`
everywhere and threading the single sponge-CR appeal (the commitment-opening binding on the two
Merkle-recompute clauses) through the unconditional dichotomy
`commitmentOpening_binds_or_collision` (via the `opening_orBreak` leaf):

  * `hood_of_reductions_orBreak`       — the per-constraint OOD identity, unless a sponge collision;
  * `mainAirAcceptF_of_floor_orBreak`  — `MainAirAcceptF d t`, unless a sponge collision;
  * `algoExtract_transferV3_orBreak`   — the `AlgoStarkSound`-content extract (a `Satisfied2` witness
        publishing `pi.toPublished`, per accepting run), unless a sponge collision;
  * `lightclient_unfoolable_deployedR_transferV3` — THE DEPLOYED APEX TWIN: this sponge side merged
        (via `OrBreak.weaken`) with the hash side of `DescriptorRefinesReduce`, concluding
        state-pinning UNLESS a collision in EITHER commitment hash — NO `Poseidon2SpongeCR`
        premise anywhere.

Recoveries (`*_of_no_sponge_collision`, `lightclient_unfoolable_deployed_of_no_collisions`) resolve
each twin back to its original under `¬ SpongeCollision`, so nothing downstream is lost — the twins
SUBSUME the originals (`algoStarkSound_transferV3_of_no_sponge_collision` rebuilds the full class
from the twin extract, not by re-invoking the original).

FIRE (§5): at the concretely broken `constHash` (collision exhibited, `Poseidon2SpongeCR` refuted —
the original chain is UNUSABLE there), the exact equivocating-opening instance the twins thread
(committed `0`, opened `1`, both recomputing the same root over the same path — recompute facts
discharged by `rfl`) FORCES the dichotomy into the break branch: the good branch (`1 = 0`) is false,
so a real collision is EXTRACTED. And the apex twin cannot fake its good branch: at the impossible
step relation, any inhabitant of the twin's conclusion IS a collision in one of the two hashes.
-/
import Dregg2.Circuit.CollisionReduce
import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.DescriptorRefinesReduce
import Dregg2.Circuit.StarkSoundDischarge

namespace Dregg2.Circuit.StarkSoundReduce

open Dregg2.Circuit.CollisionReduce
open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks FriCore FieldArith
   TableOpening fullChecks)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof tracePublishedCommit CommitSurface EffectIdx StateDecode
   WitnessDecodes verifyBatch vkOfRegistry Verdict
   cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgChecks cfgInitState cfgLogN cfgView)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Satisfied2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet verifyAlgo_accept_forces_table_identity)
open Dregg2.Circuit.OodSoundnessGame (batchResidual rlc_debatch)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.AlgoStarkSoundTransferV3
  (isArithB_iff arithList Rfam FriLdtExtractV3 hood_of_reductions mainAirAcceptF_of_floor
   algoStarkSound_transferV3)
open Dregg2.Circuit.DescriptorRefinesReduce
  (descriptorRefinesR spongeCR_of_no_collision no_collision_of_spongeCR
   constHash constHash_collision constHash_not_CR)
open Dregg2.Circuit.AirLegsDischarged (airAccept_forces_satisfied2_transferV3)
open Dregg2.Circuit.StarkSoundDischarge (deployedRefines_cfg)
open Dregg2.Exec (RecChainedState)

/-! ## §1 — `hood`, de-vacuated: the per-constraint OOD identity UNLESS a sponge collision.

The twin of `AlgoStarkSoundTransferV3.hood_of_reductions`: same hypotheses MINUS
`Poseidon2SpongeCR sponge`. The single sponge-CR appeal — `commitmentOpening_binds_of_poseidon2CR`
on the two Merkle-recompute clauses — is replaced by the unconditional dichotomy (the
`opening_orBreak` leaf); everything downstream of the binding (`verifyAlgo_accept_forces_table_identity`,
the column layout, `rlc_debatch`) is CR-free and threads through the good branch untouched. -/

/-- **`hood_of_reductions_orBreak`** — `hood` derived with NO injectivity premise: for every
arithmetic constraint the OOD identity holds, UNLESS the equivocating opening hands over a concrete
sponge collision. -/
theorem hood_of_reductions_orBreak
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp))) :
    OrBreak (SpongeCollision sponge)
      (∀ c ∈ d.constraints, isArith c →
        (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ) := by
  -- (1) acceptance forces the batched OOD identity (THEOREM, CR-free):
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity perm RATE toNat params vk core A initState logN
      proof pub ood hoodPt topen hmem hacc
  -- (2) the opened value binds OR a collision is extracted — the de-vacuated hood.b:
  refine OrBreak.imp (fun hbind => ?_) (opening_orBreak sponge hCommitted hOpened)
  -- good branch: `topen.constraintEval = vCommitted`; the rest is the original argument verbatim.
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta := hbind.symm.trans htable
  have heval : (batchResidual (Rfam d t ζ qp)).eval Λ = 0 := by
    rw [hlayout, hvc]; exact sub_self _
  -- (3) RLC de-batch at the non-exceptional Λ (THEOREM) — hood.a:
  have hRzero : ∀ j, Rfam d t ζ qp j = 0 := rlc_debatch (Rfam d t ζ qp) Λ heval hLam
  -- (4) read off the per-constraint identity:
  intro c hc harith
  have hcf : c ∈ arithList d := List.mem_filter.mpr ⟨hc, (isArithB_iff c).mpr harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  have hj0 : Rfam d t ζ qp ⟨i, hlt⟩ = 0 := hRzero ⟨i, hlt⟩
  simp only [Rfam, List.get_eq_getElem, hget] at hj0
  exact sub_eq_zero.mp hj0

/-- Recovery: no sponge collision resolves the twin to the ORIGINAL `hood_of_reductions`
conclusion — the twin subsumes the original rung. -/
theorem hood_of_reductions_of_no_sponge_collision
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hNo : ¬ SpongeCollision sponge)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp))) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ :=
  OrBreak.resolve hNo
    (hood_of_reductions_orBreak d sponge perm RATE toNat params vk core A initState logN
      proof pub hacc t ζ Λ qp topen ood vCommitted root idx siblings
      hoodPt hmem hCommitted hOpened hlayout hLam)

/-! ## §2 — `MainAirAcceptF`, de-vacuated. -/

/-- **`mainAirAcceptF_of_floor_orBreak`** — `MainAirAcceptF d t` from the honest floor with NO
`Poseidon2SpongeCR` premise: the derived `hood` twin feeds
`ood_forces_mainAirAccept_field_of_residuals` through the good branch; the collision branch is
sticky. Descriptor-polymorphic, exactly like the original. -/
theorem mainAirAcceptF_of_floor_orBreak
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hcap : t.rows.length ≤ domainSize)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp)))
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    OrBreak (SpongeCollision sponge) (MainAirAcceptF d t) :=
  OrBreak.imp
    (fun hood => ood_forces_mainAirAccept_field_of_residuals d t hcap ζ qp hood hnonexc)
    (hood_of_reductions_orBreak d sponge perm RATE toNat params vk core A initState logN
      proof pub hacc t ζ Λ qp topen ood vCommitted root idx siblings
      hoodPt hmem hCommitted hOpened hlayout hLam)

/-! ## §3 — the `AlgoStarkSound` content, de-vacuated.

`AlgoStarkSound` is a class, so the twin states its `extract` field directly in `OrBreak` form: per
accepting run, a `Satisfied2` witness publishing `pi.toPublished` exists UNLESS a sponge collision.
The recovery rebuilds the FULL class from the twin (not by re-invoking the original theorem), so the
twin genuinely subsumes `algoStarkSound_transferV3`. -/

/-- **`algoExtract_transferV3_orBreak`** — the `AlgoStarkSound.extract` content for the deployed
`transferV3` slice, with NO `Poseidon2SpongeCR` premise: every `verifyAlgo`-accepted batch yields a
genuine `Satisfied2` witness whose published commitments are `pi.toPublished`, UNLESS the opening
equivocation hands over a concrete sponge collision. -/
theorem algoExtract_transferV3_orBreak
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3 sponge hash perm RATE toNat params vk core A initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true) :
    OrBreak (SpongeCollision sponge)
      (∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash transferV3 minit mfin maddrs t ∧
          tracePublishedCommit t = pi.toPublished) := by
  obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc,
    hbus, hMem, hMap, hPub⟩ := hfri pi π hacc
  refine OrBreak.imp (fun hAir => ?_)
    (mainAirAcceptF_of_floor_orBreak transferV3 sponge perm RATE toNat params vk core A
      initState logN (view pi π).1 (view pi π).2 hacc t ζ Λ qp topen ood vCommitted root
      idx siblings hcap hoodPt hmem hCommitted hOpened hlayout hLam hnonexc)
  exact ⟨fun _ => 0, fun _ => (0, 0), [], t,
    airAccept_forces_satisfied2_transferV3 hash (fun _ => 0) (fun _ => (0, 0)) t
      hAir hbus hMem hMap, hPub⟩

/-- **Recovery / subsumption**: no sponge collision rebuilds the FULL `AlgoStarkSound` class for
the deployed `transferV3` slice FROM THE TWIN (`OrBreak.resolve` per accepting run) — the twin
subsumes `algoStarkSound_transferV3` (whose `Poseidon2SpongeCR sponge` premise implies
`¬ SpongeCollision sponge` via `no_collision_of_spongeCR`, so this statement is strictly weaker
in hypothesis). -/
theorem algoStarkSound_transferV3_of_no_sponge_collision
    (sponge : List ℤ → ℤ) (hNo : ¬ SpongeCollision sponge)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3 sponge hash perm RATE toNat params vk core A initState logN view) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view where
  extract := fun pi π hacc =>
    OrBreak.resolve hNo
      (algoExtract_transferV3_orBreak sponge hash perm RATE toNat params vk core A
        initState logN view hfri pi π hacc)

/-! ## §4 — THE DEPLOYED APEX TWIN: state-pinned unless a collision in EITHER commitment hash.

The sponge side (§3, the trace-commitment Merkle openings inside `verifyAlgo`) merges with the hash
side (`DescriptorRefinesReduce.descriptorRefinesR`, the per-effect published-PI↔limb binding) via
`OrBreak.weaken` into the joint break `SpongeCollision sponge ∨ SpongeCollision hash`. NO
`Poseidon2SpongeCR` premise anywhere; the conclusion's good branch is VERBATIM the
the deployed light-client apex (its vacuous form now deleted; this is the replacement) conclusion. -/

/-- **`lightclient_unfoolable_deployedR_transferV3`** — the deployed apex, de-vacuated: a batch the
reduced `verifyBatch` accepts pins the pre/post kernel state (`StateDecode` + `kstep` + the
commitment equalities) UNLESS the adversary produced a concrete collision in the trace-commitment
sponge OR the published-PI hash. The floors are `FriLdtExtractV3` (FS-soundness, ROM), the
reduction-form surface refinement `hrefinesR`, and the `WitnessDecodes` existence rung — no
injectivity carrier of either hash. -/
theorem lightclient_unfoolable_deployedR_transferV3
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (S : CommitSurface)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefinesR : ∀ e, descriptorRefinesR S hash transferV3 (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash (fun _ => transferV3) S pi)
    (hacc : verifyBatch (vkOfRegistry (fun _ => transferV3)) pi π = Verdict.accept) :
    OrBreak (SpongeCollision sponge ∨ SpongeCollision hash)
      (∃ pre post : RecChainedState,
        StateDecode S pi.toPublished pre post ∧
        kstep pi.effect pre post ∧
        pi.pre = S.commit pre.kernel pi.turn ∧
        pi.post = S.commit post.kernel pi.turn) := by
  -- (0) the DISCHARGED deployment refinement: `verifyBatch` accept forces `verifyAlgo` accept.
  have haccAlgo : verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState
      cfgLogN (cfgView pi π).1 (cfgView pi π).2 = true :=
    deployedRefines_cfg (fun _ => transferV3) pi π hacc
  -- (1) the SPONGE side: the de-vacuated extract, weakened into the joint break.
  refine OrBreak.bind
    (OrBreak.weaken Or.inl
      (algoExtract_transferV3_orBreak sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
        cfgCore cfgA cfgInitState cfgLogN cfgView hfri pi π haccAlgo))
    (fun hex => ?_)
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ := hex
  -- (2) the carried existence rung supplies the decoded kernel boundary.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- (3) the HASH side: the reduction-form per-effect rung, weakened into the joint break, mapped
  --     into the apex conclusion (faithfulness re-exports the published commitments).
  refine OrBreak.imp (fun hstep => ⟨pre, post, hdecode, hstep, ?_, ?_⟩)
    (OrBreak.weaken Or.inr
      (hrefinesR pi.effect minit mfin maddrs t pi.toPublished pre post hsat hdecode))
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-- **Recovery / subsumption of the deployed apex**: no collision in EITHER hash resolves the twin
to VERBATIM the the deployed light-client apex (its vacuous form now deleted; this is the replacement) conclusion — with the original's two
`Poseidon2SpongeCR` premises replaced by the (strictly weaker) no-collision facts. -/
theorem lightclient_unfoolable_deployed_of_no_collisions
    (sponge : List ℤ → ℤ) (hNoS : ¬ SpongeCollision sponge)
    (hash : List ℤ → ℤ) (hNoH : ¬ SpongeCollision hash)
    (S : CommitSurface)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefinesR : ∀ e, descriptorRefinesR S hash transferV3 (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash (fun _ => transferV3) S pi)
    (hacc : verifyBatch (vkOfRegistry (fun _ => transferV3)) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  OrBreak.resolve (fun hbrk => hbrk.elim hNoS hNoH)
    (lightclient_unfoolable_deployedR_transferV3 sponge hash S hfri kstep hrefinesR
      pi π hwitdec hacc)

/-! ## §5 — FIRE: the twins are forced into the break branch at a colliding sponge.

At `constHash` (everything hashes to `0`) the ORIGINAL chain is UNUSABLE — `Poseidon2SpongeCR
constHash` is refuted (`constHash_not_CR`), so `hood_of_reductions`/`algoStarkSound_transferV3`
cannot even be invoked. The twins still apply, and on the exact equivocating-opening instance they
thread (two DISTINCT values recomputing the same root over the same path — the recompute
hypotheses hold by `rfl`, i.e. the instance is CONCRETE, not assumed) the good branch is FALSE, so
the dichotomy is FORCED to extract a real collision. -/

/-- At the broken sponge every one-sibling recompute lands on `0` — the equivocation instance is
concretely realizable (proved by `rfl`, no hypotheses). -/
theorem constHash_recompute (v : ℤ) : merkleRecomputeZ constHash 0 v [37] = 0 := rfl

/-- **FIRE 1 — the opening leaf FORCED into the break branch.** The equivocating opening at
`constHash` (committed `0`, opened `1`, same root `0`, same path `[37]`) satisfies both recompute
hypotheses of `hood_of_reductions_orBreak`'s binding step OUTRIGHT, and its good branch (`1 = 0`)
is FALSE — so the `opening_orBreak` dichotomy the twin threads cannot take the good branch: a real
`SpongeCollision` is EXTRACTED through it. The break arm is load-bearing, not decorative. -/
theorem opening_forced_break_at_constHash : SpongeCollision constHash := by
  rcases opening_orBreak constHash (constHash_recompute 0) (constHash_recompute 1) with h | h
  · exact absurd h one_ne_zero
  · exact h

/-- **FIRE 2 — the apex twin cannot fake its good branch.** At the IMPOSSIBLE step relation, any
inhabitant of the apex twin's conclusion type IS a collision in one of the two commitment hashes:
the good branch demands the (false) step, so only the break branch can carry the proof. The twin's
`∨` genuinely separates — the conclusion is never satisfied by a vacuous good arm. -/
theorem apexR_conclusion_forces_collision
    (sponge hash : List ℤ → ℤ) (S : CommitSurface) (pi : BatchPublicInputs)
    (h : OrBreak (SpongeCollision sponge ∨ SpongeCollision hash)
      (∃ pre post : RecChainedState,
        StateDecode S pi.toPublished pre post ∧
        False ∧
        pi.pre = S.commit pre.kernel pi.turn ∧
        pi.post = S.commit post.kernel pi.turn)) :
    SpongeCollision sponge ∨ SpongeCollision hash := by
  rcases h with ⟨_, _, _, hFalse, _⟩ | hbrk
  · exact hFalse.elim
  · exact hbrk

#assert_axioms hood_of_reductions_orBreak
#assert_axioms hood_of_reductions_of_no_sponge_collision
#assert_axioms mainAirAcceptF_of_floor_orBreak
#assert_axioms algoExtract_transferV3_orBreak
#assert_axioms algoStarkSound_transferV3_of_no_sponge_collision
#assert_axioms lightclient_unfoolable_deployedR_transferV3
#assert_axioms lightclient_unfoolable_deployed_of_no_collisions
#assert_axioms constHash_recompute
#assert_axioms opening_forced_break_at_constHash
#assert_axioms apexR_conclusion_forces_collision

end Dregg2.Circuit.StarkSoundReduce
