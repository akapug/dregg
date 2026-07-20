/-
# Market.PrivateComparison — semantics for the one-bit party-MPC comparator.

`fhegg-fhe/src/mpc_party.rs` implements a party-owned strict comparison over
mod-`t` arithmetic shares and releases only `left < right`.  The runtime's
range precondition is that both reconstructed operands are canonical below the
declared bit bound; malicious input binding remains a cryptographic carrier
obligation.  This file authors the meaning reused by allocation, preference,
matchmaking, and bounded AMM predicates.
-/

import Dregg2.Tactics

namespace Market.PrivateComparison

set_option autoImplicit false

def strictDecision (left right : Nat) : Bool := decide (left < right)

theorem strictDecision_true_iff (left right : Nat) :
    strictDecision left right = true ↔ left < right := by
  simp [strictDecision]

theorem strictDecision_false_iff (left right : Nat) :
    strictDecision left right = false ↔ right ≤ left := by
  simp [strictDecision]

/-- Compose two private comparisons into a bounded-range predicate without
revealing the secret value or either difference. -/
def windowDecision (lower upper secret : Nat) : Bool :=
  decide (lower ≤ secret) && strictDecision secret upper

theorem windowDecision_true_iff (lower upper secret : Nat) :
    windowDecision lower upper secret = true ↔ lower ≤ secret ∧ secret < upper := by
  simp [windowDecision, strictDecision]

/-- Exact comparison predicate needed for a future floor-rounded constant
product swap. This theorem does not choose the protocol's next public `k`; it
only fixes the hidden arithmetic window honestly. -/
def floorInvariantDecision (k postX product : Nat) : Bool :=
  windowDecision k (k + postX) product

theorem floorInvariantDecision_true_iff (k postX product : Nat) :
    floorInvariantDecision k postX product = true ↔
      k ≤ product ∧ product < k + postX := by
  exact windowDecision_true_iff k (k + postX) product

/-- Stable pairwise preference: lower score wins and equality keeps the left
candidate. The strict comparison bit is sufficient; no score is an output. -/
def preferLeft (leftScore rightScore : Nat) : Bool :=
  !strictDecision rightScore leftScore

theorem preferLeft_true_iff (leftScore rightScore : Nat) :
    preferLeft leftScore rightScore = true ↔ leftScore ≤ rightScore := by
  simp [preferLeft, strictDecision]

/-- Abstract public transcript schema. Masked openings are intentionally
uninterpreted; the only semantic output is the comparison bit. -/
structure PublicView where
  session : Nat
  nParties : Nat
  valueBits : Nat
  maskedOpenings : List (Bool × Bool)
  lessThan : Bool
  deriving DecidableEq, Repr

def SameDeclaredLeakage (left right : PublicView) : Prop :=
  left.session = right.session ∧
  left.nParties = right.nParties ∧
  left.valueBits = right.valueBits ∧
  left.maskedOpenings.length = right.maskedOpenings.length ∧
  left.lessThan = right.lessThan

theorem same_decision_same_declared_output
    {a b c d : Nat} (h : (a < b) ↔ (c < d)) :
    strictDecision a b = strictDecision c d := by
  by_cases hab : a < b
  · have hcd : c < d := h.mp hab
    simp [strictDecision, hab, hcd]
  · have hcd : ¬ c < d := fun hcd => hab (h.mpr hcd)
    simp [strictDecision, hab, hcd]

/-! Durable comparison authorization, mirroring runtime `FHCAR001`. -/

structure ExpectedReceipt where
  session : Nat
  rosterDigest : Nat
  nParties : Nat
  valueBits : Nat
  deriving DecidableEq, Repr

structure ComparisonReceipt where
  receiptId : Nat
  session : Nat
  rosterDigest : Nat
  nParties : Nat
  valueBits : Nat
  transcriptDigest : Nat
  lessThan : Bool
  deriving DecidableEq, Repr

def ReceiptBinds (expected : ExpectedReceipt) (receipt : ComparisonReceipt) : Prop :=
  receipt.session = expected.session ∧
  receipt.rosterDigest = expected.rosterDigest ∧
  receipt.nParties = expected.nParties ∧
  receipt.valueBits = expected.valueBits

def receiptBindsCheck (expected : ExpectedReceipt) (receipt : ComparisonReceipt) : Bool :=
  receipt.session == expected.session &&
  receipt.rosterDigest == expected.rosterDigest &&
  receipt.nParties == expected.nParties &&
  receipt.valueBits == expected.valueBits

theorem receiptBindsCheck_iff (expected : ExpectedReceipt) (receipt : ComparisonReceipt) :
    receiptBindsCheck expected receipt = true ↔ ReceiptBinds expected receipt := by
  simp [receiptBindsCheck, ReceiptBinds, and_assoc]

/-- Authenticate, bind, and consume one comparison result. The returned list
is the next replay state; the operands and their difference are absent. -/
def consumeReceipt
    (signatureValid : ComparisonReceipt → Bool)
    (expected : ExpectedReceipt)
    (usedReceiptIds : List Nat)
    (receipt : ComparisonReceipt) : Option (Bool × List Nat) :=
  if !receiptBindsCheck expected receipt then none
  else if !signatureValid receipt then none
  else if receipt.receiptId ∈ usedReceiptIds then none
  else some (receipt.lessThan, receipt.receiptId :: usedReceiptIds)

def TrustedReceiptMeaning (left right : Nat) (receipt : ComparisonReceipt) : Prop :=
  receipt.lessThan = strictDecision left right

theorem comparison_replay_refused
    (signatureValid : ComparisonReceipt → Bool) (expected : ExpectedReceipt)
    (used : List Nat) (receipt : ComparisonReceipt)
    (hbind : receiptBindsCheck expected receipt = true)
    (hsig : signatureValid receipt = true)
    (hreplay : receipt.receiptId ∈ used) :
    consumeReceipt signatureValid expected used receipt = none := by
  simp [consumeReceipt, hbind, hsig, hreplay]

theorem fresh_comparison_consumes_exact_bit
    (signatureValid : ComparisonReceipt → Bool) (expected : ExpectedReceipt)
    (used : List Nat) (receipt : ComparisonReceipt)
    (hbind : receiptBindsCheck expected receipt = true)
    (hsig : signatureValid receipt = true)
    (hfresh : receipt.receiptId ∉ used) :
    consumeReceipt signatureValid expected used receipt =
      some (receipt.lessThan, receipt.receiptId :: used) := by
  simp [consumeReceipt, hbind, hsig, hfresh]

theorem authorized_comparison_refines_strict_order
    {left right : Nat} {receipt : ComparisonReceipt}
    (hmeaning : TrustedReceiptMeaning left right receipt) :
    receipt.lessThan = true ↔ left < right := by
  rw [hmeaning]
  exact strictDecision_true_iff left right

#guard strictDecision 3 4
#guard !strictDecision 4 4
#guard windowDecision 10 20 10
#guard !windowDecision 10 20 20
#guard floorInvariantDecision 90000 150 90149
#guard !floorInvariantDecision 90000 150 90150
#guard preferLeft 7 7
#guard !preferLeft 8 7

def fixtureExpectedReceipt : ExpectedReceipt :=
  { session := 71, rosterDigest := 72, nParties := 3, valueBits := 16 }

def fixtureComparisonReceipt : ComparisonReceipt :=
  { receiptId := 73, session := 71, rosterDigest := 72, nParties := 3,
    valueBits := 16, transcriptDigest := 74, lessThan := true }

#guard receiptBindsCheck fixtureExpectedReceipt fixtureComparisonReceipt
#guard consumeReceipt (fun _ => true) fixtureExpectedReceipt [] fixtureComparisonReceipt ==
  some (true, [73])
#guard consumeReceipt (fun _ => true) fixtureExpectedReceipt [73] fixtureComparisonReceipt == none

#assert_all_clean [
  Market.PrivateComparison.strictDecision_true_iff,
  Market.PrivateComparison.strictDecision_false_iff,
  Market.PrivateComparison.windowDecision_true_iff,
  Market.PrivateComparison.floorInvariantDecision_true_iff,
  Market.PrivateComparison.preferLeft_true_iff,
  Market.PrivateComparison.same_decision_same_declared_output,
  Market.PrivateComparison.receiptBindsCheck_iff,
  Market.PrivateComparison.comparison_replay_refused,
  Market.PrivateComparison.fresh_comparison_consumes_exact_bit,
  Market.PrivateComparison.authorized_comparison_refines_strict_order]

end Market.PrivateComparison
