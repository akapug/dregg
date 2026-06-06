/-
# Dregg2.Circuit.TurnEmit — turn-level witnesses linked to per-effect emitted AIRs.

Maps each `FullActionA` constructor to its Inst AIR name (`actionAirName`), checks per-step
`StepEmittedSat` against a descriptor lookup, and folds whole-turn satisfaction (`turnEmittedSat`)
through an abstract root-compress chain (reusing `TurnWitness.foldStepRoots`). Soundness composes
per-step emitted→spec refinement (EffectRefinement diamonds where available, or generic circuit step)
to `turnSpec`, then to `execFullTurnA` via `ActionDispatch.execFullTurnA_iff_turnSpec`.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Transfer
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.CoordinatedTurnEmit
import Dregg2.Exec.CircuitEmit

namespace Dregg2.Circuit.TurnEmit

open Dregg2.Circuit
open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness stepWitnessDigest foldStepRoots turnWitnessSatisfies)
open Dregg2.Circuit.ActionDispatch
  (actionTag fullActionStep turnSpec turnSpec_eq_spec execFullTurnA_iff_turnSpec)
open Dregg2.Circuit.TurnRefinement (turnSpec_of_turnStateChain)
open Dregg2.Circuit.Inst.MintA (mintAirName mintEmitted mintDescriptorJson)
open Dregg2.Circuit.Inst.BurnA (burnAirName burnEmitted burnDescriptorJson)
open Dregg2.Circuit.Transfer (transferAirName emittedTransfer transferDescriptorJson)
open Dregg2.Circuit.SetFieldCommit (setFieldAirName emittedSetField)
open Dregg2.Circuit.CoordinatedTurnEmit (coordinatedTurnAirName emittedCoordinatedTurn)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.CircuitEmit (EmittedDescriptor satisfiedEmitted emitDescriptorJson)

/-! ## §0 — decidability (for concrete `#guard`s / `#eval`s). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — `actionAirName`: `FullActionA` → Inst AIR identity. -/

/-- Fallback AIR name for constructors whose per-effect Inst emission is not yet wired. -/
def unknownAirName : String := "dregg-unknown"

/-- **`actionAirName`** — map each `FullActionA` constructor to its Inst / commit AIR name.
Mapped arms use real emitted descriptors from Inst / commit modules; the rest default to
`unknownAirName` until their Inst emission lands (Wave 2+). -/
def actionAirName : FullActionA → String
  | .balanceA _ _ => transferAirName
  | .delegate _ _ _ => unknownAirName       -- caps: Inst emission Wave 2
  | .revoke _ _ => unknownAirName
  | .mintA _ _ _ _ => mintAirName
  | .burnA _ _ _ _ => burnAirName
  | .setFieldA _ _ _ _ => setFieldAirName
  | .emitEventA _ _ _ _ => unknownAirName
  | .incrementNonceA _ _ _ => unknownAirName
  | .setPermissionsA _ _ _ => unknownAirName
  | .setVKA _ _ _ => unknownAirName
  | .introduceA _ _ _ => unknownAirName
  | .delegateAttenA _ _ _ _ => unknownAirName
  | .attenuateA _ _ _ => unknownAirName
  | .dropRefA _ _ => unknownAirName
  | .revokeDelegationA _ _ => unknownAirName
  | .validateHandoffA _ _ _ => unknownAirName
  | .exerciseA _ _ _ => unknownAirName
  | .createCellA _ _ => unknownAirName
  | .createCellFromFactoryA _ _ _ => unknownAirName
  | .spawnA _ _ _ => unknownAirName
  | .bridgeMintA _ _ _ _ => mintAirName
  | .createEscrowA _ _ _ _ _ _ => unknownAirName
  | .releaseEscrowA _ _ => unknownAirName
  | .refundEscrowA _ _ => unknownAirName
  | .createObligationA _ _ _ _ _ _ => unknownAirName
  | .fulfillObligationA _ _ => unknownAirName
  | .slashObligationA _ _ => unknownAirName
  | .noteSpendA _ _ => unknownAirName
  | .noteCreateA _ _ => unknownAirName
  | .createCommittedEscrowA _ _ _ _ _ _ _ => unknownAirName
  | .releaseCommittedEscrowA _ _ => unknownAirName
  | .refundCommittedEscrowA _ _ => unknownAirName
  | .bridgeLockA _ _ _ _ _ _ => unknownAirName
  | .bridgeFinalizeA _ _ _ _ => unknownAirName
  | .bridgeCancelA _ _ => unknownAirName
  | .sealA _ _ _ => unknownAirName
  | .unsealA _ _ _ => unknownAirName
  | .createSealPairA _ _ _ _ => unknownAirName
  | .makeSovereignA _ _ => unknownAirName
  | .refusalA _ _ => unknownAirName
  | .receiptArchiveA _ _ => unknownAirName
  | .queueAllocateA _ _ _ _ => unknownAirName
  | .queueEnqueueA _ _ _ _ _ _ _ => unknownAirName
  | .queueDequeueA _ _ _ _ _ => unknownAirName
  | .queueResizeA _ _ _ _ => unknownAirName
  | .queueAtomicTxA _ _ => unknownAirName
  | .queuePipelineStepA _ _ _ _ => unknownAirName
  | .pipelinedSendA _ => unknownAirName
  | .exportSturdyRefA _ _ _ _ _ => unknownAirName
  | .enlivenRefA _ _ _ _ => unknownAirName
  | .swissHandoffA _ _ _ _ => unknownAirName
  | .swissDropA _ _ _ => unknownAirName
  | .cellSealA _ _ => unknownAirName
  | .cellUnsealA _ _ => unknownAirName
  | .cellDestroyA _ _ _ => unknownAirName
  | .refreshDelegationA _ _ => unknownAirName

/-- Coverage count: every `FullActionA` constructor has an `actionAirName` arm. -/
def actionAirNameCoverage : Nat := 56

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
    ∀ sw _ _ _, stepEmittedSat lookup sw _ _ fa ↔
      sw.tag = actionTag fa ∧ satisfiedEmitted d (assignmentOf sw.assignment) := by
  intro sw _ _ _
  dsimp [stepEmittedSat]
  constructor
  · rintro ⟨htag, d', hfind, hsat⟩
    have : d' = d := (Option.some.inj (hfind.trans hlookup.symm)).symm
    subst this
    exact ⟨htag, hsat⟩
  · rintro ⟨htag, hsat⟩
    exact ⟨htag, d, hlookup, hsat⟩

/-! ## §3 — Default registry (all exported `*AirName`/`*Emitted` pairs). -/

/-- **`defaultDescriptorLookup`** — the default AIR-name registry: every effect that exports an
`*AirName`/`*Emitted` pair from Inst / commit modules (mint, burn, transfer, setField, coordinated).
Unmapped names return `none` (delegate, noteSpend, createEscrow, … await Wave-2 Inst emission). -/
def defaultDescriptorLookup : DescriptorLookup := fun name =>
  if name == mintAirName then some mintEmitted
  else if name == burnAirName then some burnEmitted
  else if name == transferAirName then some emittedTransfer
  else if name == setFieldAirName then some emittedSetField
  else if name == coordinatedTurnAirName then some emittedCoordinatedTurn
  else none

/-- Mint+burn demo lookup (alias of the default registry restricted to supply effects). -/
def demoMintBurnLookup : DescriptorLookup := defaultDescriptorLookup

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

/-- **`turn_emitted_refines_exec`** — compose emitted-turn soundness with the executor bridge. -/
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
#eval defaultDescriptorLookup transferAirName |>.map (·.name)
#eval defaultDescriptorLookup setFieldAirName |>.map (·.name)
#eval defaultDescriptorLookup coordinatedTurnAirName |>.map (·.name)

#guard (actionAirName (.mintA 0 1 0 100) == mintAirName)
#guard (actionAirName (.burnA 0 1 0 50) == burnAirName)
#guard (actionAirName (.balanceA ⟨0, 0, 1, 0⟩ 0) == transferAirName)
#guard (actionAirName (.setFieldA 0 0 "balance" 0) == setFieldAirName)
#guard (actionAirName (.bridgeMintA 0 0 0 0) == mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup burnAirName) == some burnAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup transferAirName) == some transferAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup setFieldAirName) == some setFieldAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup coordinatedTurnAirName) ==
  some coordinatedTurnAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup burnAirName) == some burnAirName)
#guard (burnDescriptorJson == emitDescriptorJson burnEmitted)
#guard (mintDescriptorJson == emitDescriptorJson mintEmitted)
#guard mintEmitted.name == mintAirName
#guard burnEmitted.name == burnAirName
#guard burnEmitted.traceWidth == 72
#guard emittedTransfer.name == transferAirName
#guard (defaultDescriptorLookup unknownAirName == none)

#assert_axioms descriptorLookup_of_actionAirName
#assert_axioms turn_emitted_demo_mint_burn
#assert_axioms turn_emitted_refines_turnSpec
#assert_axioms turn_emitted_refines_exec

end Dregg2.Circuit.TurnEmit