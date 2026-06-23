/-
# Dregg2.Circuit.TurnEmit — turn-level witnesses linked to per-effect emitted AIRs.

Maps each `FullActionA` constructor to its Inst AIR name (`actionAirName`), checks per-step
`StepEmittedSat` against a descriptor lookup, and folds whole-turn satisfaction (`turnEmittedSat`)
through an abstract root-compress chain (reusing `TurnWitness.foldStepRoots`). Soundness composes
per-step emitted→spec refinement (EffectRefinement diamonds where available, or generic circuit step)
to `turnSpec`, then to `execFullTurnA` via `ActionDispatch.execFullTurnA_iff_turnSpec`.

POLICY: no lurking holes — unproved per-step arms are explicit open holes (never silent fallback).
-/
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectEmittedRefinement
import Dregg2.Circuit.EffectEmitRegistry
import Dregg2.Circuit.TurnEffectRefinement
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.setProgramA
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Circuit.Inst.heapWriteA
import Dregg2.Circuit.WitnessExtract
import Dregg2.Exec.CircuitEmit
import Dregg2.Exec.RecordKernel

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnEmit

open Dregg2.Circuit
open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness stepWitnessDigest foldStepRoots turnWitnessSatisfies)
open Dregg2.Circuit.ActionDispatch
  (actionTag fullActionStep turnSpec turnSpec_eq_spec execFullTurnA_iff_turnSpec)
open Dregg2.Circuit.TurnRefinement (turnSpec_of_turnStateChain)
open Dregg2.Circuit.EffectEmitRegistry
  (effectEmitRegistry actionAirName createObligationAHoleName releaseCommittedEscrowAHoleName
   refundCommittedEscrowAHoleName holeAirNames actionAirNameCoverage registryCoverage)
open Dregg2.Circuit.Inst.MintA (mintAirName mintEmitted mintDescriptorJson)
open Dregg2.Circuit.Inst.BurnA (burnAirName burnEmitted burnDescriptorJson)
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.EffectCommit2 (encodeE2)
open Dregg2.Circuit.EffectCommit2Dual (encodeE2Dual)
open Dregg2.Circuit.EffectCommit3 (encodeE2Triple)
open Dregg2.Circuit.EffectCommit5 (encodeE2Quint)
open Dregg2.Circuit.EffectCommit (encodeE)
open Dregg2.Circuit.EffectInstances (setFieldE)
open Dregg2.Exec.CircuitEmit (EmittedDescriptor satisfiedEmitted emitDescriptorJson)
open Dregg2.Circuit.EffectEmittedRefinement
open Dregg2.Circuit.TurnEffectRefinement
  (fullActionCircuitStep fullActionCircuitStepInst fullAction_circuit_refines_spec hole_circuit_step)
open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs)
open Dregg2.Circuit.Inst.NoteCreateA (NoteCreateArgs)
open Dregg2.Circuit.Inst.CreateCellA (CreateCellArgs)
open Dregg2.Circuit.Inst.SpawnA (SpawnArgs)
open Dregg2.Circuit.Inst.MintA (MintArgs)
open Dregg2.Circuit.Inst.BurnA (BurnArgs)
open Dregg2.Circuit.Inst.Delegate (DelegateArgs)
open Dregg2.Circuit.Inst.Revoke (RevokeArgs)
open Dregg2.Circuit.Inst.BalanceA (BalanceArgs balanceAE)
open Dregg2.Circuit.Inst.MintA (mintE)
open Dregg2.Circuit.Inst.BurnA (burnE)
open Dregg2.Circuit.Inst.Delegate (delegateE)
open Dregg2.Circuit.Inst.CreateCellA (createCellE)
open Dregg2.Circuit.Inst.SpawnA (spawnE)
open Dregg2.Circuit.Inst.NoteSpendA (noteSpendE)
open Dregg2.Circuit.Inst.NoteCreateA (noteCreateE)
open Dregg2.Circuit.Inst.Revoke (revokeE)
open Dregg2.Circuit.StateCommit
  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.Inst.Delegate (RestIffNoCaps)
open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
open Dregg2.Circuit.Inst.SpawnA (RestIffNoSpawnTouched)
open Dregg2.Circuit.Inst.NoteCreateA (RestIffNoCommitments)
open Dregg2.Circuit.Inst.AttenuateA (attenuateE AttenuateArgs)
open Dregg2.Circuit.Inst.EmitEventA (emitEventE EmitEventArgs)
open Dregg2.Circuit.Inst.IncrementNonceA (incrementNonceE incrementNonceAAirName IncrementNonceArgs)
open Dregg2.Circuit.Inst.SetPermissionsA (setPermissionsE setPermissionsAAirName SetPermissionsArgs)
open Dregg2.Circuit.Inst.SetVKA (setVKE setVKAAirName SetVKArgs)
open Dregg2.Circuit.Inst.SetProgramA (setProgramE setProgramAAirName SetProgramArgs)
open Dregg2.Circuit.Inst.DelegateAttenA (delegateAttenE DelegateAttenArgs)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
  (createFromFactoryE createCellFromFactoryAAirName CreateFromFactoryArgs RestIffNoFactoryTouched)
open Dregg2.Circuit.Inst.MakeSovereignA (makeSovereignE makeSovereignAAirName MakeSovereignArgs)
open Dregg2.Circuit.Inst.RefusalA (refusalE refusalAAirName RefusalArgs)
open Dregg2.Circuit.Inst.ReceiptArchiveA (receiptArchiveE receiptArchiveAAirName ReceiptArchiveArgs)
open Dregg2.Circuit.Inst.PipelinedSendA (pipelinedSendE pipelinedSendAAirName PipelinedSendArgs)
open Dregg2.Circuit.Inst.CellSealA (cellSealE CellSealArgs RestIffNoLifecycle)
open Dregg2.Circuit.Inst.CellUnsealA (cellUnsealE CellUnsealArgs)
open Dregg2.Circuit.Inst.CellDestroyA (cellDestroyE CellDestroyArgs RestIffNoLifecycleDeathCert)
open Dregg2.Circuit.Inst.RefreshDelegationA (refreshDelegationE RefreshDelegationArgs RestIffNoDelegations)
open Dregg2.Circuit.Inst.HeapWriteA (heapWriteE HeapWriteArgs)
open Dregg2.Circuit.BornEmptyCommit (BornEmptyAuthorityTables)

/-! ## §0 — decidability (for concrete `#guard`s / `#eval`s). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — `actionAirName` + registry (re-exported from `EffectEmitRegistry`). -/

/-! ## §2 — Descriptor lookup + per-step emitted satisfaction. -/

/-- AIR-name registry lookup: the Rust `lean_descriptor_air` registry portal. -/
abbrev DescriptorLookup := String → Option EmittedDescriptor

/-- Decode abstract wire bytes (`List ℤ`) into a circuit `Assignment` (out-of-range wires = 0). -/
def assignmentOf (ws : List ℤ) : Assignment :=
  fun v => ws.getD v 0

/-- **`stepEmittedSat`** / **`StepEmittedSat`** — one step's emitted witness: tag matches the action,
and the looked-up descriptor is satisfied on the step's assignment bytes. -/
def stepEmittedSat (lookup : DescriptorLookup) (sw : StepWitness)
    (_st _st' : RecChainedState) (fa : FullActionA) : Prop :=
  sw.tag = actionTag fa ∧
  ∃ d, lookup (actionAirName fa) = some d ∧
    satisfiedEmitted d (assignmentOf sw.assignment)

/-- Alias matching the Wave-1 naming convention (`StepEmittedSat`). -/
abbrev StepEmittedSat := stepEmittedSat

/-- **`descriptorLookup_of_actionAirName`** — when the registry resolves `actionAirName fa`, per-step
emitted satisfaction reduces to tag match + `satisfiedEmitted` on the resolved descriptor. -/
theorem descriptorLookup_of_actionAirName (lookup : DescriptorLookup) (fa : FullActionA)
    (d : EmittedDescriptor) (hlookup : lookup (actionAirName fa) = some d) :
    ∀ sw (st st' : RecChainedState), stepEmittedSat lookup sw st st' fa ↔
      sw.tag = actionTag fa ∧ satisfiedEmitted d (assignmentOf sw.assignment) := by
  intro sw st st'
  dsimp [stepEmittedSat]
  constructor
  · rintro ⟨htag, d', hfind, hsat⟩
    have : d' = d := Option.some.inj (hfind.symm.trans hlookup)
    subst this
    exact ⟨htag, hsat⟩
  · rintro ⟨htag, hsat⟩
    exact ⟨htag, d, hlookup, hsat⟩

/-! ## §3 — Default registry (central `EffectEmitRegistry`). -/

/-- **`defaultDescriptorLookup`** — the Wave-2 central registry (53 Inst/commit AIRs + coordinated). -/
abbrev defaultDescriptorLookup : DescriptorLookup := effectEmitRegistry

/-- Mint+burn demo lookup (alias of the default registry). -/
abbrev demoMintBurnLookup : DescriptorLookup := defaultDescriptorLookup

/-! ## §4 — Whole-turn emitted satisfaction (root chain + state chain + per-step emitted). -/

/-- **`TurnEmittedChain`** — turn-level emitted witness: boundary roots fold under `compress`
(`TurnWitness.foldStepRoots`), states chain left-to-right, and every step satisfies its emitted AIR. -/
structure TurnEmittedChain (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (s : RecChainedState) (acts : List FullActionA)
    (s' : RecChainedState) (w : TurnWitness) where
  steps_len : acts.length = w.steps.length
  root_chain : turnWitnessSatisfies compress stepRoot w
  chain : List RecChainedState
  chain_len : chain.length = acts.length + 1
  chain_head : chain[0]'(by rw [chain_len]; omega) = s
  chain_last : chain[acts.length]'(by rw [chain_len]; omega) = s'
  step_sat :
    ∀ (i : Fin acts.length),
      stepEmittedSat lookup (w.steps[i]) (chain[i.val]'(by rw [chain_len]; omega))
        (chain[i.val + 1]'(by rw [chain_len]; omega)) acts[i]

/-- **`turnEmittedSat`** — alias for a bundled `TurnEmittedChain` (the turn emission portal). -/
abbrev turnEmittedSat (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (s s' : RecChainedState) (acts : List FullActionA)
    (w : TurnWitness) : Prop :=
  Nonempty (TurnEmittedChain lookup compress stepRoot s acts s' w)

/-! ## §5 — Soundness: emitted turn ⊑ `turnSpec` ⊑ `execFullTurnA`. -/

/-- **`turn_emitted_refines_turnSpec`** — if each step's emitted witness refines `fullActionStep`
(via EffectRefinement diamonds where available, or a generic circuit-step hypothesis), the whole
turn refines `turnSpec`. -/
theorem turn_emitted_refines_turnSpec
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    turnSpec s acts s' :=
  (turnSpec_eq_spec s acts s').mpr <|
    turnSpec_of_turnStateChain fullActionStep s s' acts {
      chain := h.chain
      chain_len := h.chain_len
      chain_head := h.chain_head
      chain_last := h.chain_last
      step_witness := fun i => hstep _ _ _ _ (h.step_sat i) }

/-- **`turn_emitted_refines_exec`** — compose emitted-turn soundness with the executor bridge.

CAVEAT: this is parametric in a per-step refinement hypothesis `hstep`. When `hstep` is
discharged via `step_emitted_refines_fullActionStep`, BOTH of that lemma's conditionalities flow
through here: (1) it leaves explicit open holes where per-effect arms are unproved, so the composed
result is NOT `#assert_axioms`-pinned, and (2) it establishes only honest-encoded-trace soundness, NOT
adversarial-trace soundness (the encoder-agreement hypothesis is dead in the per-step proof). Do
not read this as whole-turn adversarial soundness of the executor bridge. -/
theorem turn_emitted_refines_exec
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    execFullTurnA s acts = some s' :=
  (execFullTurnA_iff_turnSpec s s' acts).mpr
    (turn_emitted_refines_turnSpec lookup hstep s s' acts w compress stepRoot h)

/-! ## §5b — Per-step emitted ⊑ `fullActionStep` (registry + honest encoder). -/

/-- `RestIffNoCaps` is duplicated per Inst module; bridge Delegate's portal to Revoke's for dispatch. -/
private theorem restIffNoCaps_delegate_to_revoke (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.Revoke.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.Revoke.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_attenuate (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_delegateAtten (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps]
  exact h

private theorem restIffNoLifecycle_seal_to_unseal (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle RH) :
    Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle RH := by
  dsimp [Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle,
    Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle]
  exact h

private theorem restIffNoLifecycle_seal_to_archive (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle RH) :
    Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.RestIffNoLifecycle RH := by
  dsimp [Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle,
    Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.RestIffNoLifecycle]
  exact h


def stepEmittedEncodeAgrees
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA) : Prop :=
  match fa with
  | .balanceA t a =>
      assignmentOf sw.assignment = encodeE2 S (balanceAE D_bal hD_bal) st ⟨t, a⟩ st'
  | .delegate del rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨del, rec, t⟩ st'
  | .mintA actor cell a amt =>
      assignmentOf sw.assignment = encodeE2 S (mintE D_bal hD_bal) st ⟨actor, cell, a, amt⟩ st'
  | .burnA actor cell a amt =>
      assignmentOf sw.assignment = encodeE2 S (burnE D_bal hD_bal) st ⟨actor, cell, a, amt⟩ st'
  | .introduceA intro rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨intro, rec, t⟩ st'
  | .createCellA actor newCell =>
      assignmentOf sw.assignment =
        encodeE2Triple S (createCellE LE_cell cN hN hLE_cell DBal hDBal DSide hDSide) st
          ⟨actor, newCell⟩ st'
  | .spawnA actor child target =>
      assignmentOf sw.assignment =
        encodeE2Quint S (spawnE LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) st
          ⟨actor, child, target⟩ st'
  | .bridgeMintA actor cell a value =>
      assignmentOf sw.assignment = encodeE2 S (mintE D_bal hD_bal) st ⟨actor, cell, a, value⟩ st'
  | .noteSpendA nf actor spendProof =>
      assignmentOf sw.assignment =
        encodeE2 S (noteSpendE LE_null cN hN hLE_null) st ⟨nf, actor, spendProof⟩ st'
  | .noteCreateA cm actor =>
      assignmentOf sw.assignment =
        encodeE2 S (noteCreateE LE_null cN hN hLE_null) st ⟨cm, actor⟩ st'
  | .revoke holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .revokeDelegationA holder t =>
      -- §EPOCH: the deployed cap-edge wire CONJOINED with the NAMED epoch residual (parent epoch bump +
      -- child snapshot stale) — the FAITHFUL emitted relation for `.revokeDelegationA`.
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
      ∧ Dregg2.Circuit.EffectRefinement.RevokeDelegationEpochResidual st holder t st'
  | .setFieldA actor cell f v =>
      assignmentOf sw.assignment = encodeE CS setFieldE st { actor, cell, f, v } st'
  | .emitEventA actor cell topic data =>
      assignmentOf sw.assignment = encodeE CS emitEventE st ⟨actor, cell, topic, data⟩ st'
  | .incrementNonceA actor cell n =>
      assignmentOf sw.assignment = encodeE CS incrementNonceE st ⟨actor, cell, n⟩ st'
  | .setPermissionsA actor cell p =>
      assignmentOf sw.assignment = encodeE CS setPermissionsE st ⟨actor, cell, p⟩ st'
  | .setVKA actor cell vk =>
      assignmentOf sw.assignment = encodeE CS setVKE st ⟨actor, cell, vk⟩ st'
  | .setProgramA actor cell prog =>
      assignmentOf sw.assignment = encodeE CS setProgramE st ⟨actor, cell, prog⟩ st'
  | .delegateAttenA del rec t keep =>
      assignmentOf sw.assignment =
        encodeE2 S (delegateAttenE D_caps hD_caps) st ⟨del, rec, t, keep⟩ st'
  | .attenuateA actor idx keep =>
      assignmentOf sw.assignment = encodeE2 S (attenuateE D_caps hD_caps) st ⟨actor, idx, keep⟩ st'
  | .createCellFromFactoryA actor newCell vk =>
      assignmentOf sw.assignment =
        encodeE2Quint S (createFromFactoryE LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
          st ⟨actor, newCell, vk⟩ st'
  | .makeSovereignA actor cell =>
      assignmentOf sw.assignment = encodeE CS makeSovereignE st ⟨actor, cell⟩ st'
  | .refusalA actor cell =>
      assignmentOf sw.assignment = encodeE CS refusalE st ⟨actor, cell⟩ st'
  | .receiptArchiveA actor cell =>
      assignmentOf sw.assignment = encodeE CS receiptArchiveE st ⟨actor, cell⟩ st'
  | .pipelinedSendA actor =>
      assignmentOf sw.assignment = encodeE CS pipelinedSendE st ⟨actor⟩ st'
  | .cellSealA actor cell =>
      assignmentOf sw.assignment = encodeE2 S (cellSealE DLife hDLife) st ⟨actor, cell⟩ st'
  | .cellUnsealA actor cell =>
      assignmentOf sw.assignment = encodeE2 S (cellUnsealE DLife hDLife) st ⟨actor, cell⟩ st'
  | .cellDestroyA actor cell certHash =>
      assignmentOf sw.assignment =
        encodeE2Dual S (cellDestroyE DLife hDLife DDC hDDC) st ⟨actor, cell, certHash⟩ st'
  | .refreshDelegationA actor child =>
      assignmentOf sw.assignment =
        encodeE2 S (refreshDelegationE DDgs hDDgs) st ⟨actor, child⟩ st'
  | .heapWriteA actor target addr v newRoot =>
      assignmentOf sw.assignment =
        encodeE2Dual S (heapWriteE DCell hDCell DHeaps hDHeaps) st
          ⟨actor, target, addr, v, newRoot⟩ st'
  | fa' =>
      assignmentOf sw.assignment = assignmentOf sw.assignment ∧ fa' = fa'

/-- **`step_emitted_refines_fullActionStep`** — `stepEmittedSat` on the central registry + honest
encoder refines to `fullActionStep` for every effect with an emitted diamond; other arms defer to
the circuit dispatch (`fullAction_circuit_refines_spec`).

CAVEAT (this is NOT whole-turn adversarial soundness):

1. **All arms CLOSED.** The `exerciseA` arm discharges through
   `fullAction_circuit_refines_spec` (its inner-turn fold is a REAL composite circuit step).
   F1b: the escrow/obligation/bridge-L/F/C constructors are GONE, so every surviving arm has a
   real emitted (or circuit-dispatch) discharge — no declarative fallback remains.

2. **Honest-trace only (dead `hEnc`).** The `hEnc` hypothesis (`stepEmittedEncodeAgrees`)
   is carried in the signature but is NEVER used in the proof body. Consequently this proves
   "honest-encoded trace ⇒ `fullActionStep`", i.e. soundness against an honestly-produced
   witness — it does NOT establish adversarial-trace soundness (a maliciously crafted witness
   is not constrained by `hEnc` here). The dead hypothesis should not be read as load-bearing. -/
theorem step_emitted_refines_fullActionStep
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH)  (hRestCommitments : RestIffNoCommitments S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH)
    (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hRestCellHeaps : Dregg2.Circuit.Inst.HeapWriteA.RestIffNoCellHeaps S.RH)
    (hLog : logHashInjective S.LH)
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA)
    (h : stepEmittedSat defaultDescriptorLookup sw st st' fa)
    (hEnc : stepEmittedEncodeAgrees S D_bal hD_bal D_caps hD_caps LE_cell LE_null
      cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg hDLeg
      DCaps hDCaps DDel hDDel DDgs hDDgs DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps
      sw st st' fa)
    (hcircuit :
      fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN
        hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg hDLeg
        DCaps hDCaps DDel hDDel DDgs hDDgs DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps
        st fa st') :
    fullActionStep st fa st' := by
  unfold fullActionCircuitStepInst fullActionCircuitStep at hcircuit
  match fa with
  | .balanceA t a =>
      simp only [fullActionStep]
      exact balanceA_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨t, a⟩ st'
        ((balanceA_emitted_equiv_circuit S D_bal hD_bal st ⟨t, a⟩ st').mpr hcircuit)
  | .delegate del rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st ⟨del, rec, t⟩ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st ⟨del, rec, t⟩ st').mpr hcircuit)
  | .mintA actor cell a amt =>
      simp only [fullActionStep]
      exact mint_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨actor, cell, a, amt⟩ st'
        ((mint_emitted_equiv_circuit S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st').mpr hcircuit)
  | .burnA actor cell a amt =>
      simp only [fullActionStep]
      exact burn_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨actor, cell, a, amt⟩ st'
        ((burn_emitted_equiv_circuit S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st').mpr hcircuit)
  | .introduceA intro rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st ⟨intro, rec, t⟩ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st ⟨intro, rec, t⟩ st').mpr hcircuit)
  | .createCellA actor newCell =>
      simp only [fullActionStep]
      exact createCell_emitted_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts
        hLog st ⟨actor, newCell⟩ st'
        ((createCell_emitted_equiv_circuit S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide st ⟨actor, newCell⟩ st').mpr
          hcircuit)
  | .spawnA actor child target =>
      simp only [fullActionStep]
      -- `hcircuit` is the FAITHFUL `spawnFullCircuitStep` (deployed quint + the birth epoch-stamp residual);
      -- it forces the STRENGTHENED `SpawnFullSpec` (born child FRESH) the dispatch spec table now demands.
      exact Dregg2.Circuit.EffectRefinement.spawn_full_circuit_refines_spec S LE_cell cN hN hLE_cell
        DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRestSpawn hLog st ⟨actor, child, target⟩ st' hcircuit
  | .bridgeMintA actor cell a value =>
      simp only [fullActionStep]
      exact mint_emitted_refines_spec S D_bal hD_bal hRestBal hLog st ⟨actor, cell, a, value⟩ st'
        ((mint_emitted_equiv_circuit S D_bal hD_bal st ⟨actor, cell, a, value⟩ st').mpr hcircuit)
  | .noteSpendA nf actor spendProof =>
      simp only [fullActionStep]
      exact noteSpend_emitted_refines_spec S LE_null cN hN hLE_null hRestNull hLog st ⟨nf, actor, spendProof⟩ st'
        ((noteSpend_emitted_equiv_circuit S LE_null cN hN hLE_null st ⟨nf, actor, spendProof⟩ st').mpr hcircuit)
  | .noteCreateA cm actor =>
      simp only [fullActionStep]
      exact noteCreate_emitted_refines_spec S LE_null cN hN hLE_null hRestCommitments hLog st ⟨cm, actor⟩ st'
        ((noteCreate_emitted_equiv_circuit S LE_null cN hN hLE_null st ⟨cm, actor⟩ st').mpr hcircuit)
  | .revoke holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st ⟨holder, t⟩ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st ⟨holder, t⟩ st').mpr hcircuit)
  | .setFieldA actor cell f v =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setField_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, f, v⟩ st' hwf hwf'
        ((setField_emitted_equiv_circuit CS st ⟨actor, cell, f, v⟩ st').mpr hc)
  | .revokeDelegationA holder t =>
      simp only [fullActionStep]
      -- §EPOCH: the FAITHFUL `RevokeDelegationFullSpec` from the emitted cap-edge wire PLUS the NAMED
      -- epoch residual (`revokeDelegationEmittedStep` conjoins them).
      obtain ⟨hwire, hresidual⟩ := hcircuit
      exact revokeDelegation_emitted_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog st ⟨holder, t⟩ st'
        ⟨(revoke_emitted_equiv_circuit S D_caps hD_caps st ⟨holder, t⟩ st').mpr hwire, hresidual⟩
  | .emitEventA actor cell topic data =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact emitEventA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, topic, data⟩ st'
        hwf hwf' ((emitEventA_emitted_equiv_circuit CS st ⟨actor, cell, topic, data⟩ st').mpr hc)
  | .incrementNonceA actor cell newNonce =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact incrementNonceA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, newNonce⟩ st'
        hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS incrementNonceE incrementNonceAAirName st
            ⟨actor, cell, newNonce⟩ st').mpr hc)
  | .setPermissionsA actor cell perms =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setPermissionsA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, perms⟩ st'
        hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS setPermissionsE setPermissionsAAirName st
            ⟨actor, cell, perms⟩ st').mpr hc)
  | .setVKA actor cell vk =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setVKA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, vk⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS setVKE setVKAAirName st ⟨actor, cell, vk⟩ st').mpr hc)
  | .setProgramA actor cell prog =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setProgramA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell, prog⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS setProgramE setProgramAAirName st ⟨actor, cell, prog⟩ st').mpr hc)
  | .delegateAttenA del rec t keep =>
      simp only [fullActionStep]
      exact delegateAttenA_emitted_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_delegateAtten S.RH hRestCaps) hLog st ⟨del, rec, t, keep⟩ st'
        ((delegateAttenA_emitted_equiv_circuit S D_caps hD_caps st ⟨del, rec, t, keep⟩ st').mpr hcircuit)
  | .attenuateA actor idx keep =>
      simp only [fullActionStep]
      exact attenuateA_emitted_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_attenuate S.RH hRestCaps) hLog st ⟨actor, idx, keep⟩ st'
        ((attenuateA_emitted_equiv_circuit S D_caps hD_caps st ⟨actor, idx, keep⟩ st').mpr hcircuit)
  | .exerciseA actor target inner =>
      -- CLOSED: the `fullActionCircuitStep` exerciseA arm is now a REAL composite (hold-gate ∘ inner
      -- CIRCUIT fold); `fullAction_circuit_refines_spec` discharges circuit ⊑ spec, and
      -- `hcircuit` is exactly that circuit acceptance.
      exact fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS hCSN hCSL hRestFrame
        hLogCS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DLife hDLife
        DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
        hRestCommitments hRestFactory
        hRestLifecycle hRestLifecycleDeathCert hRestDelegations hRestCellHeaps hLog st (.exerciseA actor target inner)
        st' hcircuit
  | .createCellFromFactoryA actor newCell vk =>
      simp only [fullActionStep]
      exact createCellFromFactoryA_emitted_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth hRestFactory hLog st ⟨actor, newCell, vk⟩ st'
        ((effect2quint_emitted_equiv_circuit_local S
            (createFromFactoryE LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
            createCellFromFactoryAAirName st ⟨actor, newCell, vk⟩ st').mpr hcircuit)
  | .makeSovereignA actor cell =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact makeSovereignA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS makeSovereignE makeSovereignAAirName st ⟨actor, cell⟩ st').mpr
          hc)
  | .refusalA actor cell =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact refusalA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor, cell⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS refusalE refusalAAirName st ⟨actor, cell⟩ st').mpr hc)
  | .receiptArchiveA actor cell =>
      simp only [fullActionStep]
      exact receiptArchiveLifecycleA_emitted_refines_spec S DLife hDLife
        (restIffNoLifecycle_seal_to_archive S.RH hRestLifecycle) hLog st ⟨actor, cell⟩ st'
        ((receiptArchiveLifecycleA_emitted_equiv_circuit S DLife hDLife st ⟨actor, cell⟩ st').mpr hcircuit)
  | .pipelinedSendA actor =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact pipelinedSendA_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st ⟨actor⟩ st' hwf hwf'
        ((effect1_emitted_equiv_circuit_local CS pipelinedSendE pipelinedSendAAirName st ⟨actor⟩ st').mpr hc)
  | .cellSealA actor cell =>
      simp only [fullActionStep]
      exact cellSealA_emitted_refines_spec S DLife hDLife hRestLifecycle hLog st ⟨actor, cell⟩ st'
        ((cellSealA_emitted_equiv_circuit S DLife hDLife st ⟨actor, cell⟩ st').mpr hcircuit)
  | .cellUnsealA actor cell =>
      simp only [fullActionStep]
      exact cellUnsealA_emitted_refines_spec S DLife hDLife (restIffNoLifecycle_seal_to_unseal S.RH hRestLifecycle)
        hLog st ⟨actor, cell⟩ st'
        ((cellUnsealA_emitted_equiv_circuit S DLife hDLife st ⟨actor, cell⟩ st').mpr hcircuit)
  | .cellDestroyA actor cell certHash =>
      simp only [fullActionStep]
      exact cellDestroyA_emitted_refines_spec S DLife hDLife DDC hDDC hRestLifecycleDeathCert hLog st
        ⟨actor, cell, certHash⟩ st'
        ((cellDestroyA_emitted_equiv_circuit S DLife hDLife DDC hDDC st ⟨actor, cell, certHash⟩ st').mpr hcircuit)
  | .refreshDelegationA actor child =>
      simp only [fullActionStep]
      -- `hcircuit` is the FAITHFUL `refreshDelegationFullCircuitStep` (deployed func-descriptor + the
      -- freshness-restore stamp residual); it forces the STRENGTHENED `RefreshDelegationFullSpec`.
      exact Dregg2.Circuit.EffectRefinementBatch2.refreshDelegation_full_circuit_refines_spec
        S DDgs hDDgs hRestDelegations hLog st ⟨actor, child⟩ st' hcircuit
  | .heapWriteA actor target addr v newRoot =>
      -- THE ROTATION: the emitted heap-write diamond ⊑ the leaf `HeapWriteSpec`.
      simp only [fullActionStep]
      exact heapWriteA_emitted_refines_spec S DCell hDCell DHeaps hDHeaps hRestCellHeaps hLog
        st ⟨actor, target, addr, v, newRoot⟩ st'
        ((heapWriteA_emitted_equiv_circuit S DCell hDCell DHeaps hDHeaps st
            ⟨actor, target, addr, v, newRoot⟩ st').mpr hcircuit)

/-! ## §5c — REPRESENTATIVE adversarial-witness EXTRACTION (mint), killing the dead `hEnc`.

`step_emitted_refines_fullActionStep` carries `hEnc` (the whole-trace honest-encoder equation) as a
DEAD hypothesis, so it proves only "honest-encoded trace ⇒ state". The genuine ZK obligation is an
EXTRACTOR: an ARBITRARY satisfying trace, pinned by the verifier's public-input check to the committed
digests, determines the state — with NO whole-trace `hEnc`. We discharge that here for the mint effect
(the validated reference; the generic machinery in `WitnessExtract` lifts to every v2 effect by the
same shape, see the design note at the foot).

The witness `a : Assignment` is NOT assumed equal to `encodeE2` over all 72 wires; the adversary keeps
the un-gated root wires `64/65` and every `w ≥ 72`. What it IS pinned to is `PIBindsDigests` — the six
digest wires + the guard bit — exactly what a real verifier's boundary/public-input check enforces
against the committed root (injective by the Poseidon2 CR ground). From that alone the FULL declarative
`MintASpec` is extracted. -/
open Dregg2.Circuit.WitnessExtract (PIBindsDigests effect2_extract effect2_extract_emitted
  effect2_extract_rejects_wrong_component effect2_extract_rejects_frame_tamper
  effect2_extract_rejects_log_forge)
open Dregg2.Circuit.Inst.MintA (mintE mintRestFrameDecodes mintGuardDecodes apex_iff_mintASpec)
open Dregg2.Circuit.Spec.SupplyCreation (MintASpec)
open Dregg2.Circuit.EffectCommit2 (satisfiedE2 emittedEffect2)
open Dregg2.Circuit.StateCommit (logHashInjective)

/-- **`mintA_extract`** — the adversarial-witness extractor for mint. An ARBITRARY assignment `a` that
(1) satisfies the mint effect circuit and (2) is `PIBindsDigests`-pinned (the verifier's public-input
check binds its six digest wires + guard bit to the committed values for the claimed `(s, args, s')`)
proves the COMPLETE declarative `MintASpec` — NO dead `hEnc` over the whole trace. This is the genuine
state-extraction the dead hypothesis was smuggling: the satisfying trace DETERMINES the post-state. -/
theorem mintA_extract
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedE2 S (mintE D hD) a)
    (hPI : PIBindsDigests S (mintE D hD) s args s' a) :
    MintASpec s args.actor args.cell args.a args.amt s' :=
  (apex_iff_mintASpec D hD s args s').mp
    (effect2_extract S (mintE D hD) (mintRestFrameDecodes S D hD hRest) hLog (mintGuardDecodes D hD)
      s args s' a hsat hPI)

/-- **`mintA_extract_emitted`** — the same extractor against the EMITTED (Rust-prover) wire form: a
satisfying emitted descriptor on an arbitrary PI-bound `a` extracts `MintASpec`. -/
theorem mintA_extract_emitted
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) (a : Assignment)
    (hsat : satisfiedEmitted (emittedEffect2 mintAirName (mintE D hD)) a)
    (hPI : PIBindsDigests S (mintE D hD) s args s' a) :
    MintASpec s args.actor args.cell args.a args.amt s' :=
  (apex_iff_mintASpec D hD s args s').mp
    (effect2_extract_emitted S (mintE D hD) (mintRestFrameDecodes S D hD hRest) hLog
      (mintGuardDecodes D hD) mintAirName s args s' a hsat hPI)

/-- **`mintA_extract_rejects_wrong_supply`** — ANTI-GHOST tooth (W1): a claimed mint post `s'`
whose ledger is NOT the issuer-move write `recTransferBal … a cell a amt` (a forged supply — e.g. a
credit that skipped the well-debit, the pre-W1 inflation) has NO satisfying PI-bound witness. The
extractor REJECTS supply forgery — the bind gate + injective `bal` digest make it UNSAT. -/
theorem mintA_extract_rejects_wrong_supply
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigests S (mintE D hD) s args s' a)
    (htamper : s'.kernel.bal ≠ recTransferBal s.kernel.bal args.a args.cell args.a args.amt) :
    ¬ satisfiedE2 S (mintE D hD) a :=
  effect2_extract_rejects_wrong_component S (mintE D hD) s args s' a hPI htamper

/-! ## §5d — `hEnc` MADE LOAD-BEARING in the per-step refinement (no assumed circuit step).

`step_emitted_refines_fullActionStep` (§5b) takes the per-step circuit relation `hcircuit` as a free
hypothesis and leaves BOTH `h` (`stepEmittedSat`) and `hEnc` (`stepEmittedEncodeAgrees`) dead. The
deepest soundness content is that `h` and `hEnc` TOGETHER *determine* the circuit step — no circuit
relation need be assumed. We discharge that as a generic, reusable extractor over the whole v2-effect
class, then wire it through to `fullActionStep` for `mintA` as the validated reference.

`effect2_step_extracts_circuit`: given the registry resolves the action's AIR name to `emittedEffect2
name E`, the step witness *satisfies* that descriptor (`h`), and the witness bytes ARE the honest
encoder for the claimed `(pre, args, post)` (`hEnc`), the v2 circuit relation `satisfiedE2 S E (encodeE2
…)` HOLDS. `hEnc` is consumed by the `rw` (it rewrites the satisfied bytes onto the honest encoding);
`h` supplies the satisfied descriptor. Neither is dead. This is the genuine witness-extraction the dead
hypothesis was smuggling, lifted to a single lemma every v2 arm can call. -/

open Dregg2.Circuit.EffectCommit2 (emitEffect2Faithful)
open Dregg2.Circuit.EffectRefinement (mintCircuitStep mint_circuit_refines_spec)

theorem effect2_step_extracts_circuit
    {Args : Type}
    (S : Surface2) (E : Dregg2.Circuit.EffectCommit2.EffectSpec2 RecChainedState Args) (name : String)
    (sw : StepWitness) (fa : FullActionA)
    (pre : RecChainedState) (args : Args) (post : RecChainedState)
    (st st' : RecChainedState)
    (hreg : defaultDescriptorLookup (actionAirName fa) = some (emittedEffect2 name E))
    (h : stepEmittedSat defaultDescriptorLookup sw st st' fa)
    (hEnc : assignmentOf sw.assignment = encodeE2 S E pre args post) :
    satisfiedE2 S E (encodeE2 S E pre args post) := by
  obtain ⟨_htag, d, hlook, hsat⟩ := h
  have hd : d = emittedEffect2 name E := Option.some.inj (hlook.symm.trans hreg)
  subst hd
  rw [hEnc] at hsat
  exact (emitEffect2Faithful name E _).mpr hsat

/-- **`mint_step_refines_fullActionStep_extracted`** — the §5b headline pattern for `mintA` with the
circuit step DERIVED from `h` + `hEnc`, NOT assumed. From `stepEmittedSat` (registry-resolved, satisfied)
plus the encoder-agreement `hEnc`, the FULL `fullActionStep` (= `MintASpec`) is obtained. `hEnc` is
load-bearing here: drop it and the satisfied bytes are an arbitrary trace, not pinned to `(st, …, st')`.
This is the dead-`hEnc` kill made real on a concrete arm; `effect2_step_extracts_circuit` lifts the same
shape to every v2 arm (each supplies its own registry `rfl` and `*_circuit_refines_spec`). -/
theorem mint_step_refines_fullActionStep_extracted
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (sw : StepWitness) (st st' : RecChainedState)
    (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : stepEmittedSat defaultDescriptorLookup sw st st' (.mintA actor cell a amt))
    (hEnc : assignmentOf sw.assignment
      = encodeE2 S (mintE D hD) st ⟨actor, cell, a, amt⟩ st') :
    fullActionStep st (.mintA actor cell a amt) st' := by
  show MintASpec st actor cell a amt st'
  exact mint_circuit_refines_spec S D hD hRest hLog st ⟨actor, cell, a, amt⟩ st'
    (effect2_step_extracts_circuit S (mintE D hD) mintAirName sw (.mintA actor cell a amt)
      st ⟨actor, cell, a, amt⟩ st' st st' rfl h hEnc)

/-! ### NON-VACUITY of the §5d extractor (anti-vacuous teeth).

Decidable `satisfiedEmitted` so the `#guard`s below are real evaluation, not `rfl` on a trivial Prop. -/

instance (c : Dregg2.Exec.CircuitEmit.EmittedConstraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Dregg2.Exec.CircuitEmit.EmittedConstraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (d : EmittedDescriptor) (a : Assignment) : Decidable (satisfiedEmitted d a) := by
  unfold satisfiedEmitted; exact List.decidableBAll _ _

-- TOOTH 1 (conclusion is NON-TRIVIAL): the all-zero witness FAILS `mintEmitted` (mint pins `var 0 = 1`).
-- So `effect2_step_extracts_circuit`'s conclusion is a real constraint, not `True`; a stripped/forged
-- witness is rejected by `satisfiedEmitted`.
#guard decide (satisfiedEmitted mintEmitted (fun _ => 0)) == false
-- TOOTH 2 (premise `hreg` is TAMPERABLE): a wrong AIR-name resolves to `none`, so the descriptor-identity
-- premise FAILS for any tampered name — extraction cannot fire on a mismatched descriptor.
#guard (defaultDescriptorLookup "dregg-NOT-AN-AIR" == none)
-- HOLDS witness: the mint action's AIR name resolves to exactly `mintEmitted` (the `rfl` the extractor uses).
#guard (defaultDescriptorLookup (actionAirName (.mintA 0 1 0 100)) == some mintEmitted)

#assert_axioms effect2_step_extracts_circuit
#assert_axioms mint_step_refines_fullActionStep_extracted

/-! ## §6 — Demo: mint + burn two-step turn via `defaultDescriptorLookup`. -/

/-- **`turn_emitted_demo_mint_burn`** — the default registry resolves mint and burn AIR identities
to their Inst-emitted descriptors (the two-step supply demo chain). -/
theorem turn_emitted_demo_mint_burn :
    defaultDescriptorLookup mintAirName = some mintEmitted ∧
    defaultDescriptorLookup burnAirName = some burnEmitted := ⟨rfl, rfl⟩

#eval actionAirName (.mintA 0 1 0 100)
#eval actionAirName (.burnA 0 1 0 50)
#eval defaultDescriptorLookup mintAirName |>.map (·.name)
#eval defaultDescriptorLookup burnAirName |>.map (·.name)
#eval defaultDescriptorLookup Dregg2.Circuit.Inst.Delegate.delegateAirName |>.map (·.name)
#eval defaultDescriptorLookup Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName |>.map (·.name)

#guard (actionAirName (.mintA 0 1 0 100) == mintAirName)
#guard (actionAirName (.burnA 0 1 0 50) == burnAirName)
#guard (actionAirName (.balanceA ⟨0, 0, 1, 0⟩ 0) == Dregg2.Circuit.Inst.BalanceA.balanceAAirName)
#guard (actionAirName (.delegate 0 1 2) == Dregg2.Circuit.Inst.Delegate.delegateAirName)
#guard (actionAirName (.exerciseA 0 1 []) == Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName)
#guard (actionAirName (.setFieldA 0 0 "balance" 0) == Dregg2.Circuit.SetFieldCommit.setFieldAirName)
#guard (actionAirName (.bridgeMintA 0 0 0 0) == mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup burnAirName) == some burnAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup Dregg2.Circuit.Inst.Delegate.delegateAirName) ==
  some Dregg2.Circuit.Inst.Delegate.delegateAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup burnAirName) == some burnAirName)
#guard (burnDescriptorJson == emitDescriptorJson burnEmitted)
#guard (mintDescriptorJson == emitDescriptorJson mintEmitted)
#guard mintEmitted.name == mintAirName
#guard burnEmitted.name == burnAirName
#guard burnEmitted.traceWidth == 72
#guard (defaultDescriptorLookup createObligationAHoleName == none)
#guard (defaultDescriptorLookup releaseCommittedEscrowAHoleName == none)
#guard (defaultDescriptorLookup refundCommittedEscrowAHoleName == none)
#guard (∀ name ∈ holeAirNames, defaultDescriptorLookup name == none)
#guard registryCoverage == 32

#assert_axioms descriptorLookup_of_actionAirName
#assert_axioms turn_emitted_demo_mint_burn
#assert_axioms turn_emitted_refines_turnSpec
#assert_axioms turn_emitted_refines_exec
-- The adversarial-witness extractor (mint reference).
#assert_axioms mintA_extract
#assert_axioms mintA_extract_emitted
#assert_axioms mintA_extract_rejects_wrong_supply
end Dregg2.Circuit.TurnEmit