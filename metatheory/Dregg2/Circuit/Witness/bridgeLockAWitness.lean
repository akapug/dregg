/-
# Dregg2.Circuit.Witness.bridgeLockAWitness — `execute → satisfying assignment` for `bridgeLockA` (the
bridge-OUTBOUND LOCK; v2-DUAL family, touched components = `bal` (debit originator) AND `escrows` (park
a bridge record)).

The DUAL bal+escrows analog: `bridgeLockWitnessVec` RUNS the REAL executor `bridgeLockChainA` and lays
the satisfying 74-wire `encodeE2Dual` assignment out as a flat `List Int` over a concrete surface (a
`bal` probe digest for component 1, an injective `escrows` list digest for component 2). The dual circuit
has FIVE gates: guard (`var 0 = 1`), rest (`66=67`), `bal` (`68=69`), `escrows` (`70=71`), log (`72=73`).
The honest witness satisfies `effectCircuit2Dual`; a forged post-state that ALSO mints a bystander cell's
`bal` (component-1 tamper) is REJECTED by the `bal` bind gate `68 ≠ 69`.
`Inst.bridgeLockA.bridgeLockA_full_sound` proved the crown jewel (`⇒ BridgeOutboundLockSpec`).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.Inst.bridgeLockA

namespace Dregg2.Circuit.Witness.BridgeLockAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Inst.BridgeLockA
open Dregg2.Circuit.Spec.BridgeOutboundLock
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (bal probe digest + escrows list digest). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := fun l => (l.length : ℤ)

/-- `bal` probe digest (asset-`asset` column at originator + destination + a bystander cell 2). -/
def balProbes (orig dest : CellId) (asset : AssetId) : List (CellId × AssetId) :=
  [(orig, asset), (dest, asset), (2, asset)]
def balDigestC (orig dest : CellId) (asset : AssetId) (bal : CellId → AssetId → ℤ) : ℤ :=
  (balProbes orig dest asset).foldl (fun acc p => acc * 1000000 + bal p.1 p.2) 0

/-- Escrows list digest (injective, small bases so the fold stays within `i64`). -/
def leConcrete : EscrowRecord → ℤ :=
  fun r => (r.id : ℤ) * 100000 + r.amount * 1000 + (if r.resolved then 1 else 0) * 100 + (r.asset : ℤ)
def cnConcrete : List ℤ → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000000 + x) (xs.length : ℤ)
def escrowsDigestC (escrows : List EscrowRecord) : ℤ := cnConcrete (escrows.map leConcrete)

def bridgeLockSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete dual `ActiveComponent`s + the concrete `bridgeLockEC`. -/

def balComponentC (orig dest : CellId) (asset : AssetId) :
    ActiveComponent RecChainedState BridgeLockArgs where
  digest    := fun k => balDigestC orig dest asset k.bal
  expected  := fun s args =>
    balDigestC orig dest asset (recBalCreditCell s.kernel.bal args.originator args.asset (-args.amount))
  postClause := fun s args post =>
    balDigestC orig dest asset post.bal
      = balDigestC orig dest asset (recBalCreditCell s.kernel.bal args.originator args.asset (-args.amount))
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def escrowsComponentC : ActiveComponent RecChainedState BridgeLockArgs where
  digest    := fun k => escrowsDigestC k.escrows
  expected  := fun s args =>
    escrowsDigestC (parkedBridgeRecord args.id args.originator args.destination args.asset args.amount
      :: s.kernel.escrows)
  postClause := fun s args post =>
    escrowsDigestC post.escrows
      = escrowsDigestC (parkedBridgeRecord args.id args.originator args.destination args.asset args.amount
          :: s.kernel.escrows)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def bridgeLockEC (orig dest : CellId) (asset : AssetId) :
    EffectSpec2Dual RecChainedState BridgeLockArgs where
  view         := chainView
  active1      := balComponentC orig dest asset
  active2      := escrowsComponentC
  logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  restFrame    := fun k k' => True
  guardGates   := bridgeLockGuardGates
  guardProp    := bridgeLockGuardProp
  guardWidth   := 1
  guardEncode  := bridgeLockGuardEncode
  guardLocal   := bridgeLockGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (orig dest : CellId) (asset : AssetId) (s : RecChainedState) (args : BridgeLockArgs)
    (s' : RecChainedState) : List Int :=
  (List.range (bridgeLockEC orig dest asset).traceWidth).map
    (fun v => encodeE2Dual bridgeLockSurfaceC (bridgeLockEC orig dest asset) s args s' v)

def bridgeLockWitnessVec (s : RecChainedState) (args : BridgeLockArgs) : List Int :=
  match bridgeLockChainA s args.id args.actor args.originator args.destination args.asset args.amount with
  | some s' => witnessOf args.originator args.destination args.asset s args s'
  | none    => witnessOf args.originator args.destination args.asset s args s

theorem bridgeLockWitnessVec_commit {s s' : RecChainedState} {args : BridgeLockArgs}
    (h : bridgeLockChainA s args.id args.actor args.originator args.destination args.asset args.amount
        = some s') :
    bridgeLockWitnessVec s args = witnessOf args.originator args.destination args.asset s args s' := by
  unfold bridgeLockWitnessVec; rw [h]

theorem witnessOf_get (orig dest : CellId) (asset : AssetId) (s : RecChainedState)
    (args : BridgeLockArgs) (s' : RecChainedState) (v : Nat)
    (hv : v < (bridgeLockEC orig dest asset).traceWidth) :
    (witnessOf orig dest asset s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2Dual bridgeLockSurfaceC (bridgeLockEC orig dest asset) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

Cells {0,1,2} all live; actor 0 = originator (`authorizedB` true via `actor = src`); `bal` asset-1
column 100/5/50; empty escrows. Lock id 7 moves 5 of asset 1 out of originator 0 (debit), parking a
bridge record. Destination cell 1; bystander cell 2. -/

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => default
        caps := fun _ => []
        bal := fun c a => if a = 1 then (if c = 0 then 100 else if c = 1 then 5 else if c = 2 then 50 else 0) else 0 }
    log := [] }

def goodArgsC : BridgeLockArgs :=
  { id := 7, actor := 0, originator := 0, destination := 1, asset := 1, amount := 5 }

def goodPostC : RecChainedState := (bridgeLockChainA sC0 7 0 0 1 1 5).getD sC0

/-- THE FORGERY: originator 0 honestly debited (95), BUT bystander cell 2's asset-1 balance is ALSO
minted 50 → 999 — value forged into a third cell during the lock. The escrows/frame/log stay honest, so
a projection circuit would have passed it; the `bal` component digest differs (component-1 gate `68=69`). -/
def forgedBalC : CellId → AssetId → ℤ :=
  fun c a => if a = 1 then (if c = 0 then 95 else if c = 1 then 5 else if c = 2 then 999 else 0) else 0

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalC }, log := goodPostC.log }

def honestWitness : List Int := bridgeLockWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 1 1 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 74
#guard forgedWitness.length == 74

#guard decide (satisfied (effectCircuit2Dual (bridgeLockEC 0 1 1))
  (encodeE2Dual bridgeLockSurfaceC (bridgeLockEC 0 1 1) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- comp1 bal
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- comp2 escrows
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log

#guard decide (satisfied (effectCircuit2Dual (bridgeLockEC 0 1 1))
  (encodeE2Dual bridgeLockSurfaceC (bridgeLockEC 0 1 1) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- bal component REJECTED

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def bridgeLockHonestWitnessJson : String := witnessJson honestWitness
def bridgeLockForgedWitnessJson : String := witnessJson forgedWitness

-- The EXACT bytes the Rust `lean_executor_derived_bridge_lock_a` test pastes (goldens).
#guard bridgeLockHonestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100000005000053,95001005705055,3,3,95000005000050,95000005000050,1000705001,1000705001,1,1]"
#guard bridgeLockForgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100000005000053,95001005706004,3,3,95000005000999,95000005000050,1000705001,1000705001,1,1]"

#assert_axioms bridgeLockWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.BridgeLockAWitness
