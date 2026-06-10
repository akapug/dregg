/-
# Dregg2.Circuit.Witness.QueueAtomicTxWitness — the WITNESS GENERATOR for `queueAtomicTxA` (v2).

Mirrors the mint/noteCreate/noteSpend witness generators, for `queueAtomicTxA` — the FIFO-queue
allocate (touched component = the `queues` LIST of `QueueRecord`; guard = state-authority ∧
id-freshness; the log GROWS by the allocate receipt). The concrete digest reads each `QueueRecord`'s
`id`/`owner`/`capacity`/`buffer`-length positionally, so a forged queue-list (a tampered bystander
queue record) is visible to the BIND gate.

Reuses (not re-proved): `Inst.QueueAtomicTxA.queueAtomicTxA_full_sound`,
`effect2_circuit_full_complete`, `encodeE2`.
-/
import Dregg2.Circuit.Inst.queueAtomicTxA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueAtomicTxWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.QueueAtomicTxA
open Dregg2.Circuit.Inst.QueueEnqueueA (RestIffNoQueues)
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

instance {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (a : Assignment) :
    Decidable (satisfiedE2 S E a) := by unfold satisfiedE2; infer_instance

/-! ## §1 — the REAL (Poseidon2 CR-grounded) commitment surface.

The queue-list digest is now `Poseidon2Surface.refP2` (the CR-grounded reference sponge realizing the
REAL `babyBearD4W16` Poseidon2) over the FIELD-BINDING `encQueueRec` (which binds the WHOLE buffer, not
just `buffer.length % 1000`, and `capacity` in full). The log hash binds `src`/`dst` (the old
`lhConcrete` dropped them). -/

open Dregg2.Circuit.Poseidon2Surface (recListDigest encQueueRec turnLogDigest)

def qDigConcrete : List QueueRecord → ℤ := recListDigest encQueueRec

/-- Concrete rest hash: a field-count of the non-`queues` components. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
            + (k.commitments.length : ℤ) * 11

/-- Concrete log hash: the REAL `refP2` sponge over the FULL `encTurnRec` (binds `src`/`dst`). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `ActiveComponent` for queueAllocate: digest equality on the queue list. -/
def qActiveConcrete : ActiveComponent RecChainedState AtomicTxArgs where
  digest    := fun k => qDigConcrete k.queues
  expected  := fun s args => qDigConcrete (atomicTxPostQueues s args)
  postClause := fun s args post =>
    qDigConcrete post.queues = qDigConcrete (atomicTxPostQueues s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueAtomicTxEConcrete : EffectSpec2 RecChainedState AtomicTxArgs where
  view         := chainView
  active       := qActiveConcrete
  logUpdate    := some (fun s args =>
    match queueAtomicTxChainA s args.ops with
    | some s1 => escrowReceiptA args.actor :: s1.log
    | none    => s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := atomicTxGuardGates
  guardProp    := atomicTxGuardProp
  guardWidth   := 1
  guardEncode  := atomicTxGuardEncode
  guardLocal   := atomicTxGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState) : List Int :=
  (List.range queueAtomicTxEConcrete.traceWidth).map
    (fun w => encodeE2 SC queueAtomicTxEConcrete s args s' w)

def queueAtomicTxWitnessVec (s : RecChainedState) (args : AtomicTxArgs) : List Int :=
  match execFullA s (.queueAtomicTxA args.actor args.ops) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueAtomicTxWitnessVec_commit {s s' : RecChainedState} {args : AtomicTxArgs}
    (h : execFullA s (.queueAtomicTxA args.actor args.ops) = some s') :
    queueAtomicTxWitnessVec s args = witnessOf s args s' := by
  unfold queueAtomicTxWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueAtomicTxEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2 SC queueAtomicTxEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (hspec : QueueAtomicTxSpec s args.actor args.ops s') :
    satisfiedE2 S (queueAtomicTxE LE cN hN hLE) (encodeE2 S (queueAtomicTxE LE cN hN hLE) s args s') := by
  refine effect2_circuit_full_complete S (queueAtomicTxE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (atomicTxGuardEncodes LE cN hN hLE) s args s' ?_
  exact (apex_iff_queueAtomicTxSpec LE cN hN hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AtomicTxArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueAtomicTxE LE cN hN hLE) (encodeE2 S (queueAtomicTxE LE cN hN hLE) s args s')) :
    QueueAtomicTxSpec s args.actor args.ops s' :=
  queueAtomicTxA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}, an existing queue (id 5, owner 0, cap 4, empty buffer).
Actor 0 = cell 0 (self-auth + owner), lifecycle default Live. -/
def kQ0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 0, capacity := 4, buffer := [] }] }

def sQ0 : RecChainedState := { kernel := kQ0, log := [] }

/-- The good batch: enqueue 8 onto queue 5, then dequeue it back — the all-or-nothing pair. -/
def goodQAArgs : AtomicTxArgs :=
  { actor := 0, ops := [QueueTxOpA.enqueue 5 8 0 0, QueueTxOpA.dequeue 5 0 0] }

def goodQAPost : RecChainedState :=
  (execFullA sQ0 (.queueAtomicTxA goodQAArgs.actor goodQAArgs.ops)).getD sQ0

/-- **THE FORGERY:** the batch is honest, but the post-buffer claims the message SURVIVED the dequeue
([⟩] → [8]) — a tampered FIFO buffer. The BIND digest gate catches it. -/
def forgedThirdQueue : RecChainedState :=
  { goodQAPost with kernel := { goodQAPost.kernel with
      queues := [{ id := 5, owner := 0, capacity := 4, buffer := [8] }] } }

def honestWitness : List Int := queueAtomicTxWitnessVec sQ0 goodQAArgs
def forgedWitness : List Int := witnessOf sQ0 goodQAArgs forgedThirdQueue

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfiedE2 SC queueAtomicTxEConcrete (encodeE2 SC queueAtomicTxEConcrete sQ0 goodQAArgs goodQAPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfiedE2 SC queueAtomicTxEConcrete (encodeE2 SC queueAtomicTxEConcrete sQ0 goodQAArgs forgedThirdQueue)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueAtomicTxDescriptorJson : String := emitDescriptorJson queueAtomicTxAEmitted

#guard (queueAtomicTxDescriptorJson.length > 0)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueAtomicTxWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueAtomicTxWitness
