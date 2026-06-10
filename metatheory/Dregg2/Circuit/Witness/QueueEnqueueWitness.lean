/-
# Dregg2.Circuit.Witness.QueueEnqueueWitness — the WITNESS GENERATOR for `queueEnqueueA` (v2).

Mirrors the mint/noteCreate/noteSpend witness generators, for `queueEnqueueA` — the FIFO-queue
allocate (touched component = the `queues` LIST of `QueueRecord`; guard = state-authority ∧
id-freshness; the log GROWS by the allocate receipt). The concrete digest reads each `QueueRecord`'s
`id`/`owner`/`capacity`/`buffer`-length positionally, so a forged queue-list (a tampered bystander
queue record) is visible to the BIND gate.

Reuses (not re-proved): `Inst.QueueEnqueueA.queueEnqueueA_full_sound`,
`effect2_circuit_full_complete`, `encodeE2`.
-/
import Dregg2.Circuit.Inst.queueEnqueueA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueEnqueueWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.QueueEnqueueA
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
def qActiveConcrete : ActiveComponent RecChainedState EnqueueArgs where
  digest    := fun k => qDigConcrete k.queues
  expected  := fun s args => qDigConcrete (enqueuePostQueues s args)
  postClause := fun s args post =>
    qDigConcrete post.queues = qDigConcrete (enqueuePostQueues s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueEnqueueEConcrete : EffectSpec2 RecChainedState EnqueueArgs where
  view         := chainView
  active       := qActiveConcrete
  logUpdate    := some (fun s args => enqueueReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := enqueueGuardGates
  guardProp    := enqueueGuardProp
  guardWidth   := 1
  guardEncode  := enqueueGuardEncode
  guardLocal   := enqueueGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) : List Int :=
  (List.range queueEnqueueEConcrete.traceWidth).map
    (fun w => encodeE2 SC queueEnqueueEConcrete s args s' w)

def queueEnqueueWitnessVec (s : RecChainedState) (args : EnqueueArgs) : List Int :=
  match execFullA s (.queueEnqueueA args.id args.m args.actor args.cell) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueEnqueueWitnessVec_commit {s s' : RecChainedState} {args : EnqueueArgs}
    (h : execFullA s (.queueEnqueueA args.id args.m args.actor args.cell) = some s') :
    queueEnqueueWitnessVec s args = witnessOf s args s' := by
  unfold queueEnqueueWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueEnqueueEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2 SC queueEnqueueEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (hspec : QueueEnqueueSpec s args.id args.m args.actor args.cell s') :
    satisfiedE2 S (queueEnqueueE LE cN hN hLE) (encodeE2 S (queueEnqueueE LE cN hN hLE) s args s') := by
  refine effect2_circuit_full_complete S (queueEnqueueE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (enqueueGuardEncodes LE cN hN hLE) s args s' ?_
  exact (apex_iff_queueEnqueueSpec LE cN hN hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueEnqueueE LE cN hN hLE) (encodeE2 S (queueEnqueueE LE cN hN hLE) s args s')) :
    QueueEnqueueSpec s args.id args.m args.actor args.cell s' :=
  queueEnqueueA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}, an existing queue (id 5, owner 0, cap 4, empty buffer).
Actor 0 = cell 0 (self-auth), lifecycle default Live. -/
def kQ0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 0, capacity := 4, buffer := [] }] }

def sQ0 : RecChainedState := { kernel := kQ0, log := [] }

/-- The good enqueue args: actor 0 enqueues message 8 onto queue 5 over cell 0. -/
def goodQAArgs : EnqueueArgs := { id := 5, m := 8, actor := 0, cell := 0 }

def goodQAPost : RecChainedState :=
  (execFullA sQ0 (.queueEnqueueA goodQAArgs.id goodQAArgs.m goodQAArgs.actor goodQAArgs.cell)).getD sQ0

/-- **THE FORGERY:** the enqueue is honest, but the queue's buffer is rewritten to a wrong message
(8 → 999) — a tampered FIFO buffer. The BIND digest gate catches the forged list. -/
def forgedThirdQueue : RecChainedState :=
  { goodQAPost with kernel := { goodQAPost.kernel with
      queues := [{ id := 5, owner := 0, capacity := 4, buffer := [999] }] } }

def honestWitness : List Int := queueEnqueueWitnessVec sQ0 goodQAArgs
def forgedWitness : List Int := witnessOf sQ0 goodQAArgs forgedThirdQueue

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfiedE2 SC queueEnqueueEConcrete (encodeE2 SC queueEnqueueEConcrete sQ0 goodQAArgs goodQAPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfiedE2 SC queueEnqueueEConcrete (encodeE2 SC queueEnqueueEConcrete sQ0 goodQAArgs forgedThirdQueue)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueEnqueueDescriptorJson : String := emitDescriptorJson queueEnqueueAEmitted

#guard (queueEnqueueDescriptorJson.length > 0)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueEnqueueWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueEnqueueWitness
