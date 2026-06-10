/-
# Dregg2.Circuit.Inst.queueAtomicTxA — the v2 (`EffectCommit2`) VALIDATION for `queueAtomicTxA`.

F1b: the deposit/refund legs are GONE with the kernel escrow holding-store — the atomic batch is a
fold of bare bal-NEUTRAL FIFO sub-ops, so the instance collapses from the verb-era v2-TRIPLE
(`queues`+`bal`+`escrows`) to the SINGLE `queues` `listComponent` (with `bal` now FROZEN by the rest
frame).

THE VALIDATION: `queueAtomicTxA_full_sound ⇒ QueueAtomicTxSpec` THROUGH the framework (the apex truth
in `Dregg2/Circuit/Spec/queueatomictx.lean`, whose executor corner is
`execFullA_queueAtomicTxA_iff_spec`).
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queueatomictx
import Dregg2.Circuit.Inst.queueEnqueueA

namespace Dregg2.Circuit.Inst.QueueAtomicTxA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — args + guard plumbing. -/

structure AtomicTxArgs where
  actor : CellId
  ops   : List QueueTxOpA

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The atomic-batch guard — the all-or-nothing fold COMMITS. -/
def atomicTxGuardProp (s : RecChainedState) (args : AtomicTxArgs) : Prop :=
  match queueAtomicTxChainA s args.ops with
  | some _ => True
  | none   => False

instance (s : RecChainedState) (args : AtomicTxArgs) : Decidable (atomicTxGuardProp s args) := by
  unfold atomicTxGuardProp
  cases queueAtomicTxChainA s args.ops with
  | none   => simp; infer_instance
  | some _ => simp; infer_instance

def atomicTxGuardEncode (s : RecChainedState) (args : AtomicTxArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (atomicTxGuardProp s args) else 0

def atomicTxGuardGates : ConstraintSystem := [cBitGuard]

theorem atomicTxGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied atomicTxGuardGates a ↔ satisfied atomicTxGuardGates b := by
  unfold satisfied atomicTxGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- Canonical post-`queues` after the atomic batch fold (pure function of pre+args). -/
def atomicTxPostQueues (s : RecChainedState) (args : AtomicTxArgs) : List QueueRecord :=
  match queueAtomicTxChainA s args.ops with
  | some s1 => s1.kernel.queues
  | none    => s.kernel.queues

def queuesComponent (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ) :
    ActiveComponent RecChainedState AtomicTxArgs :=
  listComponent (·.queues) LQ cN hN hLQ atomicTxPostQueues

/-- **`queueAtomicTxE`** — the `EffectSpec2` for the deposit-free atomic batch. -/
def queueAtomicTxE (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ) :
    EffectSpec2 RecChainedState AtomicTxArgs where
  view         := chainView
  active       := queuesComponent LQ cN hN hLQ
  logUpdate    := some (fun s args =>
    match queueAtomicTxChainA s args.ops with
    | some s1 => escrowReceiptA args.actor :: s1.log
    | none    => s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats
      ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := atomicTxGuardGates
  guardProp    := atomicTxGuardProp
  guardWidth   := 1
  guardEncode  := atomicTxGuardEncode
  guardLocal   := atomicTxGuardLocal
  guardWidth_le := by decide

/-! ### §2a — per-effect obligations. -/

theorem atomicTxGuardDecodes (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ) :
    GuardDecodes2 (queueAtomicTxE LQ cN hN hLQ) := by
  intro s args s' hsat
  change satisfied atomicTxGuardGates (atomicTxGuardEncode s args s') at hsat
  show atomicTxGuardProp s args
  have hg := hsat cBitGuard (by simp [atomicTxGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, atomicTxGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem atomicTxGuardEncodes (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ) :
    GuardEncodes2 (queueAtomicTxE LQ cN hN hLQ) := by
  intro s args s' hg
  show satisfied atomicTxGuardGates (atomicTxGuardEncode s args s')
  intro c hc
  simp only [atomicTxGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, atomicTxGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem atomicTxRestFrameDecodes (S : Surface2) (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ)
    (hRest : Dregg2.Circuit.Inst.QueueEnqueueA.RestIffNoQueuesBalEscrows S.RH) :
    RestFrameDecodes2 S (queueAtomicTxE LQ cN hN hLQ) := by
  intro k k' h
  obtain ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif, hDC, hDel,
    hDgs, hSB, hDE, hDEA⟩ := (hRest k k').mp h
  exact ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif, hDC, hDel,
    hDgs, hSB, hDE, hDEA⟩

/-! ### §2b — helpers: guard ↔ spec guard, post shape, batch frames. -/

theorem atomicTxGuardProp_iff_atomicTxGuard (s : RecChainedState) (args : AtomicTxArgs) :
    atomicTxGuardProp s args ↔ atomicTxGuard s args.ops := by
  unfold atomicTxGuardProp atomicTxGuard
  cases hf : queueAtomicTxChainA s args.ops with
  | none   => simp [hf]
  | some s1 => simp [hf]

theorem atomicTxPostQueues_some (s : RecChainedState) (args : AtomicTxArgs) (s1 : RecChainedState)
    (hf : queueAtomicTxChainA s args.ops = some s1) :
    atomicTxPostQueues s args = s1.kernel.queues := by
  unfold atomicTxPostQueues; rw [hf]

/-- F1b: each atomic sub-op is bal-FRAME (the deposit-free FIFO ops never touch `bal`). -/
private theorem queueTxOpStepA_balFrame {s s' : RecChainedState} {op : QueueTxOpA}
    (h : queueTxOpStepA s op = some s') : s'.kernel.bal = s.kernel.bal := by
  cases op with
  | enqueue id m actor cell =>
      simp only [queueTxOpStepA] at h
      rcases (queueEnqueueChainA_iff_spec s id m actor cell s').mp h with
        ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩
      exact hbal
  | dequeue id actor cell =>
      simp only [queueTxOpStepA] at h
      rcases (queueDequeueChainA_iff_spec s id actor cell s').mp h with
        ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩
      exact hbal

/-- The batch fold is bal-FRAME (induction over the sub-ops). -/
private theorem queueAtomicTxChainA_balFrame {s s' : RecChainedState} {ops : List QueueTxOpA}
    (h : queueAtomicTxChainA s ops = some s') : s'.kernel.bal = s.kernel.bal := by
  induction ops generalizing s with
  | nil => simp only [queueAtomicTxChainA, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainA] at h
      cases hop : queueTxOpStepA s op with
      | none => rw [hop] at h; exact absurd h (by simp)
      | some s1 => rw [hop] at h; rw [ih h, queueTxOpStepA_balFrame hop]

/-- Kernel extensionality (18 fields). -/
private theorem recordKernel_eq_of_fields {k k' : RecordKernelState}
    (haccounts : k.accounts = k'.accounts) (hcell : k.cell = k'.cell) (hcaps : k.caps = k'.caps)
    (hnullifiers : k.nullifiers = k'.nullifiers)
    (hrevoked : k.revoked = k'.revoked) (hcommitments : k.commitments = k'.commitments)
    (hbal : k.bal = k'.bal) (hqueues : k.queues = k'.queues) (hswiss : k.swiss = k'.swiss)
    (hslotCaveats : k.slotCaveats = k'.slotCaveats) (hfactories : k.factories = k'.factories)
    (hlifecycle : k.lifecycle = k'.lifecycle) (hdeathCert : k.deathCert = k'.deathCert)
    (hdelegate : k.delegate = k'.delegate) (hdelegations : k.delegations = k'.delegations)
    (hsealedBoxes : k.sealedBoxes = k'.sealedBoxes)
    (hdelegationEpoch : k.delegationEpoch = k'.delegationEpoch)
    (hdelegationEpochAt : k.delegationEpochAt = k'.delegationEpochAt) : k = k' := by
  cases k; cases k'; simp_all

/-! ### §2c — apex ↔ `QueueAtomicTxSpec`. -/

theorem apex_iff_queueAtomicTxSpec (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState) :
    (queueAtomicTxE LQ cN hN hLQ).apex s args s' ↔
      QueueAtomicTxSpec s args.actor args.ops s' := by
  show (atomicTxGuardProp s args
        ∧ s'.kernel.queues = atomicTxPostQueues s args
        ∧ s'.log = (match queueAtomicTxChainA s args.ops with
            | some s1 => escrowReceiptA args.actor :: s1.log
            | none    => s.log)
        ∧ ((queueAtomicTxE LQ cN hN hLQ).restFrame s.kernel s'.kernel))
       ↔ QueueAtomicTxSpec s args.actor args.ops s'
  unfold QueueAtomicTxSpec queueAtomicTxE
  constructor
  · rintro ⟨hg, hq, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB, hDE, hDEA⟩
    rcases atomicTxGuardProp_iff_atomicTxGuard s args |>.mp hg with ⟨s1, hf⟩
    rcases queueAtomicTxChainA_preserves_rest hf with
      ⟨hAccF, hCellF, hCapsF, hNulF, hRevF, hComF, hSwF, hSCF, hFacF, hLifF, hDCF, hDelF, hDgsF,
       hSBF, hDEF, hDEAF⟩
    have hBalF := queueAtomicTxChainA_balFrame hf
    refine ⟨s1, hf, ?_, ?_⟩
    · refine recordKernel_eq_of_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact hAcc.trans hAccF.symm
      · exact hCell.trans hCellF.symm
      · exact hCaps.trans hCapsF.symm
      · exact hNul.trans hNulF.symm
      · exact hRev.trans hRevF.symm
      · exact hCom.trans hComF.symm
      · exact hBal.trans hBalF.symm
      · exact hq.trans (atomicTxPostQueues_some s args s1 hf)
      · exact hSw.trans hSwF.symm
      · exact hSC.trans hSCF.symm
      · exact hFac.trans hFacF.symm
      · exact hLif.trans hLifF.symm
      · exact hDC.trans hDCF.symm
      · exact hDel.trans hDelF.symm
      · exact hDgs.trans hDgsF.symm
      · exact hSB.trans hSBF.symm
      · exact hDE.trans hDEF.symm
      · exact hDEA.trans hDEAF.symm
    · rw [hf] at hlog; exact hlog
  · rintro ⟨s1, hf, hker, hlog⟩
    have hg : atomicTxGuardProp s args :=
      atomicTxGuardProp_iff_atomicTxGuard s args |>.mpr ⟨s1, hf⟩
    have hkq := atomicTxPostQueues_some s args s1 hf
    rcases queueAtomicTxChainA_preserves_rest hf with
      ⟨hAccF, hCellF, hCapsF, hNulF, hRevF, hComF, hSwF, hSCF, hFacF, hLifF, hDCF, hDelF, hDgsF,
       hSBF, hDEF, hDEAF⟩
    have hBalF := queueAtomicTxChainA_balFrame hf
    refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (congrArg (fun k => k.queues) hker).trans hkq.symm
    · rw [hf]; exact hlog
    · exact (congrArg (fun k => k.accounts) hker).trans hAccF
    · exact (congrArg (fun k => k.cell) hker).trans hCellF
    · exact (congrArg (fun k => k.caps) hker).trans hCapsF
    · exact (congrArg (fun k => k.nullifiers) hker).trans hNulF
    · exact (congrArg (fun k => k.revoked) hker).trans hRevF
    · exact (congrArg (fun k => k.commitments) hker).trans hComF
    · exact (congrArg (fun k => k.bal) hker).trans hBalF
    · exact (congrArg (fun k => k.swiss) hker).trans hSwF
    · exact (congrArg (fun k => k.slotCaveats) hker).trans hSCF
    · exact (congrArg (fun k => k.factories) hker).trans hFacF
    · exact (congrArg (fun k => k.lifecycle) hker).trans hLifF
    · exact (congrArg (fun k => k.deathCert) hker).trans hDCF
    · exact (congrArg (fun k => k.delegate) hker).trans hDelF
    · exact (congrArg (fun k => k.delegations) hker).trans hDgsF
    · exact (congrArg (fun k => k.sealedBoxes) hker).trans hSBF
    · exact (congrArg (fun k => k.delegationEpoch) hker).trans hDEF
    · exact (congrArg (fun k => k.delegationEpochAt) hker).trans hDEAF

/-! ### §2d — THE VALIDATION. -/

theorem queueAtomicTxA_full_sound
    (S : Surface2) (LQ : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLQ : listLeafInjective LQ)
    (hRest : Dregg2.Circuit.Inst.QueueEnqueueA.RestIffNoQueuesBalEscrows S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueAtomicTxE LQ cN hN hLQ)
          (encodeE2 S (queueAtomicTxE LQ cN hN hLQ) s args s')) :
    QueueAtomicTxSpec s args.actor args.ops s' := by
  have hapex : (queueAtomicTxE LQ cN hN hLQ).apex s args s' :=
    effect2_circuit_full_sound S (queueAtomicTxE LQ cN hN hLQ)
      (atomicTxRestFrameDecodes S LQ cN hN hLQ hRest) hLog (atomicTxGuardDecodes LQ cN hN hLQ)
      s args s' h
  exact (apex_iff_queueAtomicTxSpec LQ cN hN hLQ s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueAtomicTxEWire : EffectSpec2 RecChainedState AtomicTxArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := atomicTxGuardGates
  guardProp    := atomicTxGuardProp
  guardWidth   := 1
  guardEncode  := atomicTxGuardEncode
  guardLocal   := atomicTxGuardLocal
  guardWidth_le := by decide

def queueAtomicTxAAirName : String := "dregg-queueAtomicTxA-v2"

def queueAtomicTxAEmitted : EmittedDescriptor := emittedEffect2 queueAtomicTxAAirName queueAtomicTxEWire

#guard queueAtomicTxAEmitted.name == queueAtomicTxAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms atomicTxGuardLocal
#assert_axioms atomicTxGuardDecodes
#assert_axioms atomicTxGuardEncodes
#assert_axioms apex_iff_queueAtomicTxSpec
#assert_axioms queueAtomicTxA_full_sound

end Dregg2.Circuit.Inst.QueueAtomicTxA
