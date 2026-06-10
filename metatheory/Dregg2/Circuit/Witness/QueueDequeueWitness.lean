/-
# Dregg2.Circuit.Witness.QueueDequeueWitness — the WITNESS GENERATOR for `queueDequeueA` (v2).

Mirrors the mint/noteCreate/noteSpend witness generators, for `queueDequeueA` — the FIFO-queue
allocate (touched component = the `queues` LIST of `QueueRecord`; guard = state-authority ∧
id-freshness; the log GROWS by the allocate receipt). The concrete digest reads each `QueueRecord`'s
`id`/`owner`/`capacity`/`buffer`-length positionally, so a forged queue-list (a tampered bystander
queue record) is visible to the BIND gate.

Reuses (not re-proved): `Inst.QueueDequeueA.queueDequeueA_full_sound`,
`effect2_circuit_full_complete`, `encodeE2`.
-/
import Dregg2.Circuit.Inst.queueDequeueA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueDequeueWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.QueueDequeueA
open Dregg2.Circuit.Spec.QueueFifoCore
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
def qActiveConcrete : ActiveComponent RecChainedState DequeueArgs where
  digest    := fun k => qDigConcrete k.queues
  expected  := fun s args => qDigConcrete (dequeuePostQueues s args)
  postClause := fun s args post =>
    qDigConcrete post.queues = qDigConcrete (dequeuePostQueues s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueDequeueEConcrete : EffectSpec2 RecChainedState DequeueArgs where
  view         := chainView
  active       := qActiveConcrete
  logUpdate    := some (fun s args => dequeueReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := dequeueGuardGates
  guardProp    := dequeueGuardProp
  guardWidth   := 1
  guardEncode  := dequeueGuardEncode
  guardLocal   := dequeueGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState) : List Int :=
  (List.range queueDequeueEConcrete.traceWidth).map
    (fun w => encodeE2 SC queueDequeueEConcrete s args s' w)

def queueDequeueWitnessVec (s : RecChainedState) (args : DequeueArgs) : List Int :=
  match execFullA s (.queueDequeueA args.id args.actor args.cell) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueDequeueWitnessVec_commit {s s' : RecChainedState} {args : DequeueArgs}
    (h : execFullA s (.queueDequeueA args.id args.actor args.cell) = some s') :
    queueDequeueWitnessVec s args = witnessOf s args s' := by
  unfold queueDequeueWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueDequeueEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2 SC queueDequeueEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (hspec : QueueDequeueSpec s args.id args.actor args.cell s') :
    satisfiedE2 S (queueDequeueE LE cN hN hLE) (encodeE2 S (queueDequeueE LE cN hN hLE) s args s') := by
  refine effect2_circuit_full_complete S (queueDequeueE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (dequeueGuardEncodes LE cN hN hLE) s args s' ?_
  exact (apex_iff_queueDequeueSpec LE cN hN hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueDequeueE LE cN hN hLE) (encodeE2 S (queueDequeueE LE cN hN hLE) s args s')) :
    QueueDequeueSpec s args.id args.actor args.cell s' :=
  queueDequeueA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}, an existing queue (id 5, owner 0, cap 4, buffer [8, 9]).
Actor 0 (the OWNER) dequeues; lifecycle default Live. -/
def kQ0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 0, capacity := 4, buffer := [8, 9] }] }

def sQ0 : RecChainedState := { kernel := kQ0, log := [] }

/-- The good dequeue args: owner 0 pops the head of queue 5 over cell 0. -/
def goodQAArgs : DequeueArgs := { id := 5, actor := 0, cell := 0 }

def goodQAPost : RecChainedState :=
  (execFullA sQ0 (.queueDequeueA goodQAArgs.id goodQAArgs.actor goodQAArgs.cell)).getD sQ0

/-- **THE FORGERY:** the pop is honest, but the post-buffer claims the WRONG remainder ([9] → [8]) —
a tampered FIFO buffer (the pop dropped the TAIL, not the head). The BIND digest gate catches it. -/
def forgedThirdQueue : RecChainedState :=
  { goodQAPost with kernel := { goodQAPost.kernel with
      queues := [{ id := 5, owner := 0, capacity := 4, buffer := [8] }] } }

def honestWitness : List Int := queueDequeueWitnessVec sQ0 goodQAArgs
def forgedWitness : List Int := witnessOf sQ0 goodQAArgs forgedThirdQueue

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfiedE2 SC queueDequeueEConcrete (encodeE2 SC queueDequeueEConcrete sQ0 goodQAArgs goodQAPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfiedE2 SC queueDequeueEConcrete (encodeE2 SC queueDequeueEConcrete sQ0 goodQAArgs forgedThirdQueue)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueDequeueDescriptorJson : String := emitDescriptorJson queueDequeueAEmitted

#guard (queueDequeueDescriptorJson.length > 0)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueDequeueWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueDequeueWitness
