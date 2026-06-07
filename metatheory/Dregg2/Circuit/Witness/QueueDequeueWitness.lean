/-
# Dregg2.Circuit.Witness.QueueDequeueWitness — the WITNESS GENERATOR for `queueDequeueA` (v3 / triple).

`queueDequeueA` touches THREE non-`cell` components (`queues` + `bal` + `escrows`): pop the FIFO head,
refund the parked deposit to the dequeuer, mark the escrow resolved. This module supplies the
executor-derived witness generator (76-wide, three bind gates), mirroring `QueueEnqueueWitness`. A
forged ANY-of-the-three component (a tampered bystander queue / a wrong refund / an un-resolved escrow)
is visible to its bind gate.

Reuses (not re-proved): `Inst.QueueDequeueA.queueDequeueA_full_sound`,
`effect2triple_circuit_full_complete`, `encodeE2Triple`. No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Circuit.Inst.queueDequeueA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.QueueDequeueWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit3
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

instance {St Args : Type} (S : Surface2) (E : EffectSpec2Triple St Args) (a : Assignment) :
    Decidable (satisfiedE2Triple S E a) := by unfold satisfiedE2Triple; infer_instance

/-! ## §1 — the REAL (Poseidon2 CR-grounded) commitment surface.

Every component digest is now `Poseidon2Surface.refP2` (the CR-grounded reference sponge realizing the
REAL `babyBearD4W16` Poseidon2) over FIELD-BINDING encoders. The OLD toy folds dropped fields
(`capacity % 1000`, `amount % 1000`, `src`/`dst` in the log); these bind every field. -/

open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest encQueueRec encEscrowRec turnLogDigest)

def qDigConcrete : List QueueRecord → ℤ := recListDigest encQueueRec
def eDigConcrete : List EscrowRecord → ℤ := recListDigest encEscrowRec

def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 [bal 0 0, bal 1 0, bal 0 1]

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7 + (k.commitments.length : ℤ) * 11

def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def eqComponent {β : Type} (read : RecordKernelState → β) (Dg : β → ℤ)
    (expectedVal : RecChainedState → DequeueArgs → β) : ActiveComponent RecChainedState DequeueArgs where
  digest    := fun k => Dg (read k)
  expected  := fun s args => Dg (expectedVal s args)
  postClause := fun s args post => Dg (read post) = Dg (expectedVal s args)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def queueDequeueEConcrete : EffectSpec2Triple RecChainedState DequeueArgs where
  view         := chainView
  active1      := eqComponent (·.queues)  qDigConcrete   (fun s args => dequeuePostQueues s args)
  active2      := eqComponent (·.bal)     balDigConcrete (fun s args => dequeuePostBal s args)
  active3      := eqComponent (·.escrows) eDigConcrete   (fun s args => dequeuePostEscrows s args)
  logUpdate    := some (fun s args =>
    dequeueReceipt args.actor args.cell (dequeueRefundAmount s.kernel args.depId) :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
      ∧ k'.swiss = k.swiss ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate
      ∧ k'.delegations = k.delegations ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := dequeueGuardGates
  guardProp    := dequeueGuardProp
  guardWidth   := 1
  guardEncode  := dequeueGuardEncode
  guardLocal   := dequeueGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState) : List Int :=
  (List.range queueDequeueEConcrete.traceWidth).map
    (fun w => encodeE2Triple SC queueDequeueEConcrete s args s' w)

def queueDequeueWitnessVec (s : RecChainedState) (args : DequeueArgs) : List Int :=
  match execFullA s (.queueDequeueA args.id args.actor args.cell args.depId) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem queueDequeueWitnessVec_commit {s s' : RecChainedState} {args : DequeueArgs}
    (h : execFullA s (.queueDequeueA args.id args.actor args.cell args.depId) = some s') :
    queueDequeueWitnessVec s args = witnessOf s args s' := by
  unfold queueDequeueWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < queueDequeueEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2Triple SC queueDequeueEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
  (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
  (hLQ : ListCommit.listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
  (hNE : compressNInjective cNE) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (hspec : QueueDequeueSpec s args.id args.actor args.cell args.depId s') :
    satisfiedE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
      (encodeE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s') := by
  refine effect2triple_circuit_full_complete S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (fun k k' h => (hRest k k').mpr h) (dequeueGuardEncodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    s args s' ?_
  exact (apex_iff_queueDequeueSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (h : satisfiedE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
        (encodeE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')) :
    QueueDequeueSpec s args.id args.actor args.cell args.depId s' :=
  queueDequeueA_full_sound S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

The pre-state is the canonical POST of a deposit-enqueue: queue 5 (owner 0) holds one buffered message
88; the parked deposit escrow (id 7, recipient 0, amount 30, asset 0, bound to queue 5 + message 88) is
unresolved; actor 0's ledger was already debited. Dequeue pops 88, refunds 30 to actor 0, resolves the
escrow. -/

def kD0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    queues := [{ id := 5, owner := 0, capacity := 4, buffer := [88] }]
    bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0
    escrows := [{ id := 7, creator := 0, recipient := 0, amount := 30, resolved := false,
                  asset := 0, bridge := false, queueDep := some 5, queueMsg := some 88 }] }

def sD0 : RecChainedState := { kernel := kD0, log := [] }

/-- The good dequeue args: actor 0 (owner) dequeues queue 5 over cell 0, refunding deposit 7 (30). -/
def goodDQArgs : DequeueArgs := { id := 5, actor := 0, cell := 0, depId := 7 }

def goodDQPost : RecChainedState :=
  (execFullA sD0 (.queueDequeueA goodDQArgs.id goodDQArgs.actor goodDQArgs.cell goodDQArgs.depId)).getD sD0

/-- **THE FORGERY:** the dequeue is honest, but the refunded ledger is forged (actor 0 claims 999
instead of the honest 70 + 30 = 100) — a tampered ledger. The bal BIND gate (70 ≠ 71) catches it. -/
def forgedRefund : RecChainedState :=
  { goodDQPost with kernel := { goodDQPost.kernel with
      bal := fun c a => if c = 0 ∧ a = 0 then 999 else goodDQPost.kernel.bal c a } }

def honestWitness : List Int := queueDequeueWitnessVec sD0 goodDQArgs
def forgedWitness : List Int := witnessOf sD0 goodDQArgs forgedRefund

#guard honestWitness.length == 76
#guard forgedWitness.length == 76

#guard decide (satisfiedE2Triple SC queueDequeueEConcrete (encodeE2Triple SC queueDequeueEConcrete sD0 goodDQArgs goodDQPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0
#guard honestWitness.getD 74 0 == honestWitness.getD 75 0

#guard decide (satisfiedE2Triple SC queueDequeueEConcrete (encodeE2Triple SC queueDequeueEConcrete sD0 goodDQArgs forgedRefund)) == false
#guard !(forgedWitness.getD 70 0 == forgedWitness.getD 71 0)   -- bal compDigPost ≠ expected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 68 0 == forgedWitness.getD 69 0      -- queues honest
#guard forgedWitness.getD 72 0 == forgedWitness.getD 73 0      -- escrows honest

/-! ### §4b — RECEIPT-AMOUNT SOUNDNESS TOOTH (P2 canonical-semantics).

The dequeue receipt's `amt` is the named deposit RECORD's own `amount` (`dequeueRefundAmount`), NOT a
caller-supplied number. Honest record `id 7` carries `amount := 30`, so the committed receipt logs `30`.
A second fixture whose record carries `amount := 55` logs `55` — the receipt TRACKS the record. A
flag/constant or a caller-forgeable field could not state this; the only way to change the logged amount
is to change the on-record amount. -/

/-- Pre-state identical to `kD0` except the parked deposit record's `amount` is 55 (and the ledger sized
to match: actor 0 was debited 55, so honest refund returns to 45 + 55 = 100). -/
def kD55 : RecordKernelState :=
  { kD0 with
    bal := fun c a => if c = 0 ∧ a = 0 then 45 else 0
    escrows := [{ id := 7, creator := 0, recipient := 0, amount := 55, resolved := false,
                  asset := 0, bridge := false, queueDep := some 5, queueMsg := some 88 }] }

def sD55 : RecChainedState := { kernel := kD55, log := [] }

-- A fallback receipt row for the partial `headD` (never reached — the dequeues below commit).
def zeroTurn : Turn := { actor := 0, src := 0, dst := 0, amt := 0 }

-- Honest dequeue receipt amount = the RECORD's amount (30), read off the head of the committed log.
#guard ((execFullA sD0 (.queueDequeueA 5 0 0 7)).map (fun s => (s.log.headD zeroTurn).amt)) == some 30
-- The SAME dequeue against the `amount := 55` record logs 55 — the receipt tracks the record, not a
-- constant or a caller field.
#guard ((execFullA sD55 (.queueDequeueA 5 0 0 7)).map (fun s => (s.log.headD zeroTurn).amt)) == some 55
-- `dequeueRefundAmount` IS the per-record amount the executor uses (the source of the receipt).
#guard (dequeueRefundAmount kD0 7 == 30)
#guard (dequeueRefundAmount kD55 7 == 55)
-- A non-existent deposit record refunds nothing — the amount helper is fail-safe `0`.
#guard (dequeueRefundAmount kD0 999 == 0)

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def queueDequeueDescriptorJson : String := emitDescriptorJson queueDequeueAEmitted

#guard (queueDequeueDescriptorJson == r#"{"name":"dregg-queueDequeueA-v2","trace_width":76,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}},{"lhs":{"t":"var","v":74},"rhs":{"t":"var","v":75}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms queueDequeueWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueDequeueWitness
