/-
# Dregg2.Circuit.Witness.CreateSealPairWitness — the v2 WITNESS GENERATOR for `createSealPairA`.

The `execute → prove → verify → anti-ghost` beachhead for `createSealPairA` (the gated double c-list
grant installing a sealer/unsealer keypair), over the v2 framework (`EffectCommit2`). Touched component
= `kernel.caps` (a `funcComponent`), the log grows by one `createSealPairReceipt`, the 16 other kernel
fields are frozen. Mirrors `DelegateWitness` (the v2 template) — the same `caps` funcComponent shape.

Reused (not re-proved): `execFullA … (.createSealPairA …)` (the chained executor),
`Inst.CreateSealPairA.createSealPairA_full_sound`, and `effect2_circuit_full_complete`.

Poseidon-CR portals carried on the abstract keystones.
-/
import Dregg2.Circuit.Inst.createSealPairA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.CreateSealPairWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.CreateSealPairA
open Dregg2.Circuit.Spec.SealPairCreation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest turnLogDigest)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — ABSTRACT execute→prove / prove→state (CR portals carried). -/

variable (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness`** — a `CreateSealPairSpec`-satisfying step makes the v2
witness SATISFY the v2 circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState)
    (hspec : CreateSealPairSpec s args.pid args.actor args.sealerHolder args.unsealerHolder s') :
    satisfiedE2 S (createSealPairE D hD) (encodeE2 S (createSealPairE D hD) s args s') :=
  effect2_circuit_full_complete S (createSealPairE D hD)
    (fun k k' h => (hRest k k').mpr h) (createSealPairGuardEncodes D hD) s args s'
    ((apex_iff_createSealPairSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state`** — a satisfying v2 witness proves the complete
`CreateSealPairSpec` (all 17 kernel fields + log). Reuses `createSealPairA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (createSealPairE D hD) (encodeE2 S (createSealPairE D hD) s args s')) :
    CreateSealPairSpec s args.pid args.actor args.sealerHolder args.unsealerHolder s' :=
  createSealPairA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Field-binding `Auth` index (so endpoint `rights` are bound, not dropped). -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6
/-- **Field-binding** `Cap` encoder: tag + target + the WHOLE rights list (the OLD `capCode` dropped
`endpoint`'s rights via `500 + t`). -/
def encCap : Cap → List ℤ
  | .null         => [0]
  | .node t       => [1, (t : ℤ)]
  | .endpoint t r => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode
/-- One cell's cap-list digest: the REAL `refP2` sponge over the field-binding `encCap`. -/
def capListCode (cs : List Cap) : ℤ := recListDigest encCap cs
/-- Concrete caps digest over carrier `[0,1,2]`: the REAL `refP2` sponge of each cell's cap-list digest. -/
def capsDigConcrete : Caps → ℤ :=
  fun caps => refP2 ([0, 1, 2].map (fun c => capListCode (caps c)))

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
/-- The log hash: the REAL `turnLogDigest` (binds `dst`/`amt` the OLD `actor*1000 + src` fold dropped). -/
def lhConcrete : List Turn → ℤ := turnLogDigest
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `caps` component (computable digest; `postClause` = the digest equality). -/
def capsCompC : ActiveComponent RecChainedState CreateSealPairArgs :=
  { digest    := fun k => capsDigConcrete k.caps
  , expected  := fun s args =>
      capsDigConcrete (createSealPairCaps s.kernel.caps args.pid args.sealerHolder args.unsealerHolder)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (createSealPairCaps s.kernel.caps args.pid args.sealerHolder args.unsealerHolder)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def createSealPairEC : EffectSpec2 RecChainedState CreateSealPairArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => createSealPairReceipt args.actor args.sealerHolder :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := createSealPairGuardGates
  , guardProp    := createSealPairGuardProp
  , guardWidth   := 1
  , guardEncode  := createSealPairGuardEncode
  , guardLocal   := createSealPairGuardLocal
  , guardWidth_le := by decide }

/-- Concrete pre-state: actor 0 has self-authority over sealerHolder 0; cells 0,1,2 hold no caps. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}, cell := fun _ => default, caps := fun _ => [] }
def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : CreateSealPairArgs := { pid := 7, actor := 0, sealerHolder := 0, unsealerHolder := 1 }
def sPost : RecChainedState := (execFullA sPre (.createSealPairA 7 0 0 1)).getD sPre

/-- THE FORGERY: the honest double grant, but a THIRD holder (cell 2) ALSO gains a stolen `node 9` cap. -/
def sForged : RecChainedState :=
  { kernel := { kPre with
      caps := fun c =>
        if c = 0 then [sealerCap 7] else if c = 1 then [unsealerCap 7]
        else if c = 2 then [Cap.node 9] else [] }
  , log := createSealPairReceipt 0 0 :: sPre.log }

def witnessOf (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState) : List Int :=
  (List.range createSealPairEC.traceWidth).map (fun w => encodeE2 SC createSealPairEC s args s' w)

/-- **`createSealPairWitnessVec` — the executor-driven witness generator.** -/
def createSealPairWitnessVec (s : RecChainedState) (args : CreateSealPairArgs) : List Int :=
  match execFullA s (.createSealPairA args.pid args.actor args.sealerHolder args.unsealerHolder) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

def honestWitness : List Int := createSealPairWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard decide (satisfied (effectCircuit2 createSealPairEC) (encodeE2 SC createSealPairEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 createSealPairEC) (encodeE2 SC createSealPairEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 0 0 == 1

-- RIGHTS-CONFUSION anti-ghost tooth (the class the OLD `capCode endpoint t _ => 500+t` MISSED — it made
-- `sealerCap 7 = endpoint 7 [grant]` and `unsealerCap 7 = endpoint 7 [reply]` COLLIDE on the SAME `507`).
-- Here cell 0 is forged to hold the UNSEALER cap (wrong rights) instead of the SEALER cap. `encCap`
-- binds the rights, so the component-bind gate `68 ≠ 69` REJECTS.
def sForgedRights : RecChainedState :=
  { kernel := { kPre with
      caps := fun c => if c = 0 then [unsealerCap 7] else if c = 1 then [unsealerCap 7] else [] }
  , log := createSealPairReceipt 0 0 :: sPre.log }
#guard decide (satisfied (effectCircuit2 createSealPairEC) (encodeE2 SC createSealPairEC sPre argsRef sForgedRights)) == false

/-! ## §5 — JSON export. -/

def emittedCSP : EmittedDescriptor := emittedEffect2 "dregg-createSealPairA-v2" createSealPairEC
def descriptorJson : String := emitDescriptorJson emittedCSP
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedCSP.constraints.length == 4
#guard emittedCSP.traceWidth == 72

-- Structural component-bind goldens (the field-binding `refP2`/`encCap` digests are arbitrary-precision;
-- non-vacuity is at the bind gates; the Rust paste is regenerated from the JSON accessors).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged component differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.CreateSealPairWitness
