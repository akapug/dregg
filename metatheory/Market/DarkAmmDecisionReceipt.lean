/-
# Market.DarkAmmDecisionReceipt — the durable one-bit AMM commit protocol.

`fhegg-fhe/src/decision_attestation.rs` carries a strict public receipt for the
party-MPC equality decision.  Its public fields bind the exact encrypted
candidate/session, circuit shape, roster, reveal-only transcript, and released
bit; a replay guard consumes the receipt before the candidate can mutate the
pool.  This file authors that protocol state machine in Lean.

The cryptographic carrier remains an explicit premise. `TrustedMeaning` says
that the authenticated equality bit refines `invariantDecision` and that the
separate range/source certificate refines `dy ≤ y`.  From exactly those two
claims, a true receipt commits the semantic `post`; a false receipt consumes
its replay id while holding the byte-identical reserve state.  Signatures are
modeled as an injected verifier rather than falsely proved secure in Lean.
-/

import Market.DarkAmmPrivateSwap
import Dregg2.Tactics

namespace Market.DarkAmmDecisionReceipt

set_option autoImplicit false

open DarkAmmPrivateSwap

/-- Independently reconstructed public binding for one encrypted candidate. -/
structure Expected where
  candidateNonce : Nat
  equalitySession : Nat
  rosterDigest : Nat
  tripleDigest : Nat
  nParties : Nat
  valueBits : Nat
  deriving DecidableEq, Repr

/-- Public content of the durable `FHDAR001` receipt, abstracting byte digests
as naturals. No reserve, amount, operand, product residue, or share appears. -/
structure Receipt where
  receiptId : Nat
  candidateNonce : Nat
  equalitySession : Nat
  rosterDigest : Nat
  tripleDigest : Nat
  nParties : Nat
  valueBits : Nat
  transcriptDigest : Nat
  equal : Bool
  deriving DecidableEq, Repr

def Binds (expected : Expected) (receipt : Receipt) : Prop :=
  receipt.candidateNonce = expected.candidateNonce ∧
  receipt.equalitySession = expected.equalitySession ∧
  receipt.rosterDigest = expected.rosterDigest ∧
  receipt.tripleDigest = expected.tripleDigest ∧
  receipt.nParties = expected.nParties ∧
  receipt.valueBits = expected.valueBits

def bindsCheck (expected : Expected) (receipt : Receipt) : Bool :=
  receipt.candidateNonce == expected.candidateNonce &&
  receipt.equalitySession == expected.equalitySession &&
  receipt.rosterDigest == expected.rosterDigest &&
  receipt.tripleDigest == expected.tripleDigest &&
  receipt.nParties == expected.nParties &&
  receipt.valueBits == expected.valueBits

theorem bindsCheck_iff (expected : Expected) (receipt : Receipt) :
    bindsCheck expected receipt = true ↔ Binds expected receipt := by
  simp [bindsCheck, Binds, and_assoc]

/-- Persistent protocol state. The receipt id is consumed on either released
bit; only an authenticated/bound/range-valid true bit changes reserves. -/
structure MachineState where
  reserves : Reserves
  usedReceiptIds : List Nat
  deriving DecidableEq, Repr

/-- Fail-closed application of one durable decision receipt.

`signatureValid` is the configured threshold-roster verifier and `rangeValid`
is the separately verified amount/no-overdraw certificate bit. `none` means no
state is authorized. A valid false decision returns a state with only the
one-use replay id advanced. -/
def applyReceipt
    (signatureValid : Receipt → Bool)
    (rangeValid : Bool)
    (expected : Expected)
    (amounts : Amounts)
    (state : MachineState)
    (receipt : Receipt) : Option MachineState :=
  if !bindsCheck expected receipt then none
  else if !signatureValid receipt then none
  else if receipt.receiptId ∈ state.usedReceiptIds then none
  else if !receipt.equal then
    some { state with usedReceiptIds := receipt.receiptId :: state.usedReceiptIds }
  else if !rangeValid then none
  else some {
    reserves := post state.reserves amounts
    usedReceiptIds := receipt.receiptId :: state.usedReceiptIds }

/-- Exact external cryptographic/refinement obligation. The equality receipt
and range/source carrier together reveal only the decision needed by the
semantic AMM relation. -/
def TrustedMeaning (rangeValid : Bool) (state : MachineState)
    (amounts : Amounts) (receipt : Receipt) : Prop :=
  (receipt.equal = true ↔ invariantDecision state.reserves amounts = true) ∧
  (rangeValid = true ↔ amounts.dy ≤ state.reserves.y)

theorem wrong_binding_refused
    (signatureValid : Receipt → Bool) (rangeValid : Bool)
    (expected : Expected) (amounts : Amounts) (state : MachineState)
    (receipt : Receipt) (hbind : bindsCheck expected receipt = false) :
    applyReceipt signatureValid rangeValid expected amounts state receipt = none := by
  simp [applyReceipt, hbind]

theorem replay_refused
    (signatureValid : Receipt → Bool) (rangeValid : Bool)
    (expected : Expected) (amounts : Amounts) (state : MachineState)
    (receipt : Receipt) (hbind : bindsCheck expected receipt = true)
    (hsig : signatureValid receipt = true)
    (hreplay : receipt.receiptId ∈ state.usedReceiptIds) :
    applyReceipt signatureValid rangeValid expected amounts state receipt = none := by
  simp [applyReceipt, hbind, hsig, hreplay]

/-- A valid false decision is durable but atomic: it consumes the replay id
and holds the exact reserve state. -/
theorem false_receipt_holds_state
    (signatureValid : Receipt → Bool) (rangeValid : Bool)
    (expected : Expected) (amounts : Amounts) (state : MachineState)
    (receipt : Receipt) (hbind : bindsCheck expected receipt = true)
    (hsig : signatureValid receipt = true)
    (hfresh : receipt.receiptId ∉ state.usedReceiptIds)
    (hfalse : receipt.equal = false) :
    applyReceipt signatureValid rangeValid expected amounts state receipt =
      some { state with usedReceiptIds := receipt.receiptId :: state.usedReceiptIds } := by
  simp [applyReceipt, hbind, hsig, hfresh, hfalse]

theorem true_receipt_commits_post
    (signatureValid : Receipt → Bool) (expected : Expected)
    (amounts : Amounts) (state : MachineState) (receipt : Receipt)
    (hbind : bindsCheck expected receipt = true)
    (hsig : signatureValid receipt = true)
    (hfresh : receipt.receiptId ∉ state.usedReceiptIds)
    (htrue : receipt.equal = true) :
    applyReceipt signatureValid true expected amounts state receipt = some {
      reserves := post state.reserves amounts
      usedReceiptIds := receipt.receiptId :: state.usedReceiptIds } := by
  simp [applyReceipt, hbind, hsig, hfresh, htrue]

/-- The central composition law: once the two cryptographic carriers refine
their declared meanings, a released true bit and range bit imply the exact
private-swap relation. -/
theorem true_receipt_implies_admissible
    {rangeValid : Bool} {state : MachineState}
    {amounts : Amounts} {receipt : Receipt}
    (hmeaning : TrustedMeaning rangeValid state amounts receipt)
    (htrue : receipt.equal = true) (hrange : rangeValid = true) :
    Admissible state.reserves amounts := by
  apply (range_and_decision_iff_admissible state.reserves amounts).mp
  exact ⟨hmeaning.2.mp hrange, hmeaning.1.mp htrue⟩

/-- An authorized true transition is exactly semantic commit, not a freely
chosen next state. -/
theorem authorized_true_refines_commit
    {signatureValid : Receipt → Bool} {expected : Expected}
    {amounts : Amounts} {state : MachineState} {receipt : Receipt}
    (hbind : bindsCheck expected receipt = true)
    (hsig : signatureValid receipt = true)
    (hfresh : receipt.receiptId ∉ state.usedReceiptIds)
    (hmeaning : TrustedMeaning true state amounts receipt)
    (htrue : receipt.equal = true) :
    ∃ next,
      applyReceipt signatureValid true expected amounts state receipt = some next ∧
      next.reserves = commit state.reserves amounts ∧
      receipt.receiptId ∈ next.usedReceiptIds := by
  let next : MachineState := {
    reserves := post state.reserves amounts
    usedReceiptIds := receipt.receiptId :: state.usedReceiptIds }
  have hadmit : Admissible state.reserves amounts :=
    true_receipt_implies_admissible hmeaning htrue rfl
  refine ⟨next, ?_, ?_, by simp [next]⟩
  · exact true_receipt_commits_post signatureValid expected amounts state receipt
      hbind hsig hfresh htrue
  · simp [next, admitted_commits_post hadmit]

/-! Executable binding/replay teeth. -/

def fixtureExpected : Expected :=
  { candidateNonce := 11, equalitySession := 12, rosterDigest := 13,
    tripleDigest := 14, nParties := 3, valueBits := 16 }

def fixtureReceipt : Receipt :=
  { receiptId := 99, candidateNonce := 11, equalitySession := 12,
    rosterDigest := 13, tripleDigest := 14, nParties := 3, valueBits := 16,
    transcriptDigest := 15, equal := true }

def fixtureState : MachineState :=
  { reserves := pool, usedReceiptIds := [] }

#guard bindsCheck fixtureExpected fixtureReceipt
#guard !bindsCheck { fixtureExpected with candidateNonce := 10 } fixtureReceipt
#guard applyReceipt (fun _ => true) true fixtureExpected exact fixtureState fixtureReceipt ==
  some { reserves := post pool exact, usedReceiptIds := [99] }
#guard applyReceipt (fun _ => true) true fixtureExpected exact
  { fixtureState with usedReceiptIds := [99] } fixtureReceipt == none
#guard applyReceipt (fun _ => true) true fixtureExpected exact fixtureState
  { fixtureReceipt with equal := false } ==
  some { reserves := pool, usedReceiptIds := [99] }

#assert_all_clean [
  Market.DarkAmmDecisionReceipt.bindsCheck_iff,
  Market.DarkAmmDecisionReceipt.wrong_binding_refused,
  Market.DarkAmmDecisionReceipt.replay_refused,
  Market.DarkAmmDecisionReceipt.false_receipt_holds_state,
  Market.DarkAmmDecisionReceipt.true_receipt_commits_post,
  Market.DarkAmmDecisionReceipt.true_receipt_implies_admissible,
  Market.DarkAmmDecisionReceipt.authorized_true_refines_commit]

end Market.DarkAmmDecisionReceipt
