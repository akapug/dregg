/-
# Market.FhEggRustDenotation — the deployed fhEgg crossing, and the exact denotation gaps.

This file is deliberately a correspondence audit, not another ideal clearing model.  It spells out
the observable semantics of `fhegg-fhe/src/lib.rs::{reference_clear,fhe_clear}` and
`fhegg-fhe/src/mpc.rs::mpc_crossing` at the aggregate-curve boundary, then compares those semantics
with `Market.FhEggClearing`.

The comparison exposes three independent residuals at HEAD:

* **`FhEggCrossingConventionResidual`.**  Rust selects the *largest* bucket satisfying `D >= S`;
  `FhEggClearing` selects the *least* bucket satisfying `D <= S`.  Those are adjacent sides of a
  crossing in general, not two presentations of the same function.  The worked book is a concrete
  counterexample: Rust returns `(1, 8)`, Lean returns `(2, 6)`.
* **`FhEggTfheNoCrossResidual`.**  `fhe_clear` reports the no-crossing sentinel when the comparison-bit
  count is zero, but nevertheless decrypts bucket zero and reports its `min(D,S)` as `v_star`.
  `reference_clear` reports volume zero.  This diverges without overflow or cryptographic assumptions.
* **`FhEggTfheWidthResidual`.**  plaintext aggregates are `u32`, while the TFHE aggregates and their
  comparison are `FheUint16`.  No aggregate-bound gate precedes the fold.  Two valid `u16` bids can
  therefore wrap a demand of 65536 to zero and change both the crossing and volume.

The MPC perfect-hiding theorem remains mathematically real, but its `clearsVec` is the opposite
threshold step from deployed `mpc.rs`.  `MpcCrossingDenotationResidual` names and refutes that current
Rust correspondence.  Closing these residuals requires choosing one economic crossing convention,
cutting every implementation/spec to it, adding the aggregate-width bound (or widening ciphertexts),
and proving the real TFHE/MPC program refines this aggregate semantics.  Nothing here models TFHE as
an ideal encryption scheme or assumes that missing refinement.

Pure.  No axioms.
-/
import Market.MpcClearingSecurity
import Dregg2.Tactics

namespace Market.FhEggRustDenotation

open Market

set_option autoImplicit false

/-! ## 1. The plaintext Rust reference semantics. -/

/-- Rust's comparison bit: `fhegg-fhe/src/lib.rs` uses `D[p] >= S[p]`. -/
def rustClears (bk : OrderBook) (p : Nat) : Prop := supply bk p ≤ demand bk p

instance (bk : OrderBook) : DecidablePred (rustClears bk) :=
  fun p => inferInstanceAs (Decidable (supply bk p ≤ demand bk p))

/-- The exact comparison-bit vector opened by `mpc.rs` and homomorphically summed by `fhe_clear`. -/
def rustSignVec (bk : OrderBook) (k : Nat) : List Bool :=
  (List.range k).map (fun p => decide (rustClears bk p))

/-- The number of Rust comparison bits set to one. -/
def rustCount (bk : OrderBook) (k : Nat) : Nat :=
  ((List.range k).filter (fun p => decide (rustClears bk p))).length

/-- Rust's `p_star = count - 1`, with `None` when no `D >= S` bucket exists. -/
def rustPStar (bk : OrderBook) (k : Nat) : Option Nat :=
  if rustCount bk k = 0 then none else some (rustCount bk k - 1)

/-- Observable clearing output shared by the plaintext reference and output-boundary MPC. -/
structure ClearingOutput where
  pStar : Option Nat
  vStar : Int
  deriving DecidableEq, Repr

/-- The output of Rust `reference_clear`, assuming its caller supplies nonzero `k`. -/
def rustReferenceOutput (bk : OrderBook) (k : Nat) : ClearingOutput :=
  match rustPStar bk k with
  | none => ⟨none, 0⟩
  | some p => ⟨some p, min (demand bk p) (supply bk p)⟩

/-- The output proved by the current Lean `FhEggClearing` crossing. -/
def leanClearingOutput (bk : OrderBook) (h : CrossingExists bk) : ClearingOutput :=
  ⟨some (crossing bk h), clearedVolume bk h⟩

/-- **The exact current denotation obligation:** on every valid in-range Lean crossing, Lean's
clearing output equals the deployed Rust plaintext reference output. -/
def FhEggCrossingDenotation : Prop :=
  ∀ (bk : OrderBook) (h : CrossingExists bk) (k : Nat), crossing bk h < k →
    leanClearingOutput bk h = rustReferenceOutput bk k

/-! The repository's own worked book separates the two conventions. -/

#guard rustSignVec workBook 3 == [true, true, false]
#guard rustPStar workBook 3 == some 1
#guard rustReferenceOutput workBook 3 == (⟨some 1, 8⟩ : ClearingOutput)
#guard leanClearingOutput workBook workBook_crosses == (⟨some 2, 6⟩ : ClearingOutput)

/-- **Concrete denotation failure:** deployed Rust returns `(p*,V*) = (1,8)`, while the Lean theorem
tower returns `(2,6)`, on the same valid worked book and the same three buckets. -/
theorem workBook_crossing_conventions_diverge :
    leanClearingOutput workBook workBook_crosses ≠ rustReferenceOutput workBook 3 := by
  rw [show leanClearingOutput workBook workBook_crosses = ⟨some 2, 6⟩ by
    simp [leanClearingOutput, workBook_crossing, workBook_clearedVolume]]
  decide

/-- **`FhEggCrossingConventionResidual` is OPEN, formally:** the current Lean clearing does not denote
the deployed Rust reference clearing. -/
theorem FhEggCrossingConventionResidual : ¬ FhEggCrossingDenotation := by
  intro h
  have hlt : crossing workBook workBook_crosses < 3 := by
    rw [workBook_crossing]
    decide
  exact workBook_crossing_conventions_diverge (h workBook workBook_crosses 3 hlt)

#assert_axioms workBook_crossing_conventions_diverge
#assert_axioms FhEggCrossingConventionResidual

/-! ## 2. The observable `FheUint16` semantics and its two independent gaps. -/

/-- The value domain of `FheUint16`: homomorphic integer operations wrap modulo `2^16`. -/
def u16Residue (x : Int) : Int := x % 65536

/-- The encrypted demand aggregate after the `FheUint16::sum` in `fhe_clear`. -/
def fheDemand (bk : OrderBook) (p : Nat) : Int := u16Residue (demand bk p)

/-- The encrypted supply aggregate after the `FheUint16::sum` in `fhe_clear`. -/
def fheSupply (bk : OrderBook) (p : Nat) : Int := u16Residue (supply bk p)

/-- The TFHE comparison bit, evaluated on the wrapped 16-bit aggregates. -/
def fheClears (bk : OrderBook) (p : Nat) : Prop := fheSupply bk p ≤ fheDemand bk p

instance (bk : OrderBook) : DecidablePred (fheClears bk) :=
  fun p => inferInstanceAs (Decidable (fheSupply bk p ≤ fheDemand bk p))

/-- The encrypted comparison-bit sum is itself a `FheUint16`. -/
def fheCount (bk : OrderBook) (k : Nat) : Nat :=
  ((List.range k).filter (fun p => decide (fheClears bk p))).length % 65536

/-- The sentinel-level interpretation of `FheTiming.p_star`: `usize::MAX` is represented as `none`. -/
def fhePStar (bk : OrderBook) (k : Nat) : Option Nat :=
  if fheCount bk k = 0 then none else some (fheCount bk k - 1)

/-- The bucket `fhe_clear` actually indexes.  Even on a no-cross result it indexes bucket zero; on a
positive count it clamps `count-1` to `k-1`.  This definition is total, while the Rust function itself
panics for `k = 0`; all denotation obligations below require `0 < k`. -/
def fheSelectedIndex (bk : OrderBook) (k : Nat) : Nat :=
  min (if fheCount bk k = 0 then 0 else fheCount bk k - 1) (k - 1)

/-- The observable output of `fhe_clear` after decrypting its result.  This intentionally preserves
the deployed no-cross behavior: `pStar = none`, but `vStar` is still the clear minimum at bucket zero. -/
def fheOutput (bk : OrderBook) (k : Nat) : ClearingOutput :=
  ⟨fhePStar bk k,
    min (fheDemand bk (fheSelectedIndex bk k)) (fheSupply bk (fheSelectedIndex bk k))⟩

/-- Every order is representable by Rust's public `Qty = u16`. -/
def OrdersFitU16 (bk : OrderBook) : Prop :=
  ∀ o ∈ bk, 0 ≤ o.qty ∧ o.qty < 65536

/-- The missing program-refinement statement users would need before claiming
`reference_clear = fhe_clear`.  It is intentionally only an observable functional equality; a
cryptographic TFHE theorem would additionally quantify keys, encryption randomness, and evaluation. -/
def FheComputesReference : Prop :=
  ∀ (bk : OrderBook) (k : Nat), 0 < k → k < 65536 → OrdersFitU16 bk →
    fheOutput bk k = rustReferenceOutput bk k

/-- A one-bucket book with no Rust crossing: `D=5`, `S=10`.  All quantities fit in `u16`; no aggregate
wrap occurs. -/
def noCrossTfheBook : OrderBook :=
  [⟨Side.bid, 5, 0⟩, ⟨Side.ask, 10, 0⟩]

#guard rustReferenceOutput noCrossTfheBook 1 == (⟨none, 0⟩ : ClearingOutput)
#guard fheOutput noCrossTfheBook 1 == (⟨none, 5⟩ : ClearingOutput)

/-- **`FhEggTfheNoCrossResidual`:** even with no wrap, `fhe_clear` reports `min(D[0],S[0])` when its
crossing sentinel says no crossing, unlike `reference_clear`'s zero volume. -/
theorem FhEggTfheNoCrossResidual :
    fheOutput noCrossTfheBook 1 ≠ rustReferenceOutput noCrossTfheBook 1 := by decide

/-- Two maximum-half bids overflow the 16-bit encrypted demand aggregate while remaining individually
valid Rust `u16` orders. -/
def wrapTfheBook : OrderBook :=
  [⟨Side.bid, 32768, 0⟩, ⟨Side.bid, 32768, 0⟩, ⟨Side.ask, 1, 0⟩]

#guard demand wrapTfheBook 0 == 65536
#guard fheDemand wrapTfheBook 0 == 0
#guard rustReferenceOutput wrapTfheBook 1 == (⟨some 0, 1⟩ : ClearingOutput)
#guard fheOutput wrapTfheBook 1 == (⟨none, 0⟩ : ClearingOutput)

/-- **`FhEggTfheWidthResidual`:** individually valid `u16` orders can wrap the encrypted aggregate and
change the reported clearing.  A per-order type alone is not the missing aggregate bound. -/
theorem FhEggTfheWidthResidual :
    fheOutput wrapTfheBook 1 ≠ rustReferenceOutput wrapTfheBook 1 := by decide

/-- The advertised universal plaintext/FHE correctness obligation is false at HEAD.  Both premises
that are already enforced by Rust's input types (`k>0`, `k<2^16`, per-order `u16`) hold in the witness;
what is absent is an aggregate-width check, and the no-cross branch is independently inconsistent. -/
theorem FhEggTfheProgramDenotationResidual : ¬ FheComputesReference := by
  intro h
  have hfit : OrdersFitU16 noCrossTfheBook := by
    intro o ho
    simp [noCrossTfheBook] at ho
    rcases ho with rfl | rfl <;> decide
  exact FhEggTfheNoCrossResidual (h noCrossTfheBook 1 (by decide) (by decide) hfit)

#assert_axioms FhEggTfheNoCrossResidual
#assert_axioms FhEggTfheWidthResidual
#assert_axioms FhEggTfheProgramDenotationResidual

/-! ## 3. The deployed TFHE view leaks more than the advertised output. -/

/-- What the holder of `ClientKey` actually decrypts in `fhe_clear`: the comparison count (reported as
`pStar`) and both aggregate heights `D[p*]`, `S[p*]`.  Rust computes `min` only after those two values
are in the clear. -/
structure TfheDecryptView where
  pStar : Option Nat
  dStar : Int
  sStar : Int
  deriving DecidableEq, Repr

/-- The deployed TFHE decryption view at the selected bucket. -/
def fheDecryptView (bk : OrderBook) (k : Nat) : TfheDecryptView :=
  ⟨fhePStar bk k, fheDemand bk (fheSelectedIndex bk k), fheSupply bk (fheSelectedIndex bk k)⟩

/-- The claimed public leakage is only `(p*, min(D[p*],S[p*]))`. -/
def tfheOutputLeakage (v : TfheDecryptView) : ClearingOutput :=
  ⟨v.pStar, min v.dStar v.sStar⟩

/-- Two honest one-bucket books with the same advertised `(p*,V*)=(0,8)` but different aggregate
heights. -/
def sameOutputBookA : OrderBook := [⟨Side.bid, 10, 0⟩, ⟨Side.ask, 8, 0⟩]
def sameOutputBookB : OrderBook := [⟨Side.bid, 8, 0⟩, ⟨Side.ask, 8, 0⟩]

#guard fheOutput sameOutputBookA 1 == fheOutput sameOutputBookB 1
#guard fheDecryptView sameOutputBookA 1 != fheDecryptView sameOutputBookB 1
#guard fheDecryptView sameOutputBookA 1 == (⟨some 0, 10, 8⟩ : TfheDecryptView)
#guard fheDecryptView sameOutputBookB 1 == (⟨some 0, 8, 8⟩ : TfheDecryptView)

/-- The exact “decrypts only the output” simulator obligation.  A simulator given only `(p*,V*)`
would have to reproduce the holder's deterministic decrypted view for every book. -/
def TfheDecryptViewFactorsThroughOutput : Prop :=
  ∃ sim : ClearingOutput → TfheDecryptView,
    ∀ (bk : OrderBook) (k : Nat), sim (fheOutput bk k) = fheDecryptView bk k

/-- **`FhEggTfheLeakageResidual`:** no such simulator exists, because two real books have equal public
output but the deployed `ClientKey` path decrypts different `D[p*]` values.  Production threshold
decryption of a ciphertext-level `min` would close this particular leak; the current function does not
perform it. -/
theorem FhEggTfheLeakageResidual : ¬ TfheDecryptViewFactorsThroughOutput := by
  rintro ⟨sim, hsim⟩
  have hA := hsim sameOutputBookA 1
  have hB := hsim sameOutputBookB 1
  have hout : fheOutput sameOutputBookA 1 = fheOutput sameOutputBookB 1 := by decide
  have hviews : fheDecryptView sameOutputBookA 1 = fheDecryptView sameOutputBookB 1 := by
    rw [← hA, ← hB, hout]
  exact (by decide : fheDecryptView sameOutputBookA 1 ≠ fheDecryptView sameOutputBookB 1) hviews

#assert_axioms FhEggTfheLeakageResidual

/-! ## 4. The MPC correspondence gap (the perfect-hiding algebra itself is not refuted). -/

/-- The exact current correspondence obligation for the deterministic, publicly opened sign vector. -/
def MpcCrossingDenotation : Prop :=
  ∀ (bk : OrderBook) (_hb : OrdersValid bk) (h : CrossingExists bk) (k : Nat),
    Market.MpcClearingSecurity.clearsVec bk h k = rustSignVec bk k

#guard Market.MpcClearingSecurity.clearsVec workBook workBook_crosses 3 == [false, false, true]
#guard rustSignVec workBook 3 == [true, true, false]

/-- The proved Lean simulator exposes the up-step `[D <= S]`; deployed `mpc.rs` opens the down-step
`[D >= S]`.  Thus its real perfect-hiding lemma is presently joined to the wrong clearing function. -/
theorem MpcCrossingDenotationResidual : ¬ MpcCrossingDenotation := by
  intro h
  have hw := h workBook workBook_valid workBook_crosses 3
  have hlean : Market.MpcClearingSecurity.clearsVec workBook workBook_crosses 3 =
      [false, false, true] := by decide
  have hrust : rustSignVec workBook 3 = [true, true, false] := by decide
  rw [hlean, hrust] at hw
  simp at hw

#assert_axioms MpcCrossingDenotationResidual

end Market.FhEggRustDenotation
