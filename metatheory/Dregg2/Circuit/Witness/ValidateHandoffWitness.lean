/-
# Dregg2.Circuit.Witness.ValidateHandoffWitness — the v2 WITNESS GENERATOR for `validateHandoffA`.

Closes the verifiable-execution beachhead for `validateHandoffA` (the 3-vat handoff = the Granovetter
unattenuated held-cap copy, executor `recCDelegate`), over the v2 framework (`EffectCommit2`), touched
component `kernel.caps` (a `funcComponent`). Reused: `Exec.recCDelegate`,
`Inst.ValidateHandoffA.validateHandoffA_full_sound` (⇒ `DelegateSpec`),
`effect2_circuit_full_complete`, `emittedEffect2`/`emitDescriptorJson`.

§3 abstract execute→prove + verify→accept; §4 the concrete `validateHandoffWitnessVec`; §5 the
descriptor + witness JSON. The anti-ghost forgery: recipient steals an extra `node 9` cap on top of
the honest grant — the component-bind gate 68≠69 = a real UNSAT.

CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.validateHandoffA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.ValidateHandoffWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.ValidateHandoffA
open Dregg2.Circuit.Spec.AuthorityUnattenuated
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

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (hspec : DelegateSpec s args.intro args.recip args.tgt s') :
    satisfiedE2 S (validateHandoffE D hD) (encodeE2 S (validateHandoffE D hD) s args s') :=
  effect2_circuit_full_complete S (validateHandoffE D hD)
    (fun k k' h => (hRest k k').mpr h) (handoffGuardEncodes D hD) s args s'
    ((apex_iff_delegateSpec D hD s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (validateHandoffE D hD) (encodeE2 S (validateHandoffE D hD) s args s')) :
    DelegateSpec s args.intro args.recip args.tgt s' :=
  validateHandoffA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Field-binding `Auth` index (so endpoint `rights` are bound, not collapsed to `.length`). -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6
/-- **Field-binding** `Cap` encoder: tag + target + the WHOLE rights list. -/
def encCap : Cap → List ℤ
  | .null         => [0]
  | .node t       => [1, (t : ℤ)]
  | .endpoint t r => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode

/-- One cell's cap-list digest: the REAL `refP2` sponge over the field-binding `encCap` (the OLD
`% 2000003` Horner was a NON-injective field hash). -/
def capListCode (cs : List Cap) : ℤ := recListDigest encCap cs

def capsDigConcrete : Caps → ℤ :=
  fun caps => refP2 ((List.range 4).map (fun l => capListCode (caps l)))

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- The log hash: the REAL `turnLogDigest` (binds `src`/`dst`/`amt` the OLD `actor % 2000003` fold
DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def capsCompC : ActiveComponent RecChainedState HandoffArgs :=
  { digest    := fun k => capsDigConcrete k.caps
  , expected  := fun s args => capsDigConcrete (recDelegateCaps s.kernel.caps args.intro args.recip args.tgt)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (recDelegateCaps s.kernel.caps args.intro args.recip args.tgt)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def validateHandoffEC : EffectSpec2 RecChainedState HandoffArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => authReceipt args.intro :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := handoffGuardGates
  , guardProp    := handoffGuardProp
  , guardWidth   := 1
  , guardEncode  := handoffGuardEncode
  , guardLocal   := handoffGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference triple: intro 0 holds `node 5`, hands off to recip 1. -/

def kPre : RecordKernelState :=
  { accounts := {0, 1}
  , cell := fun _ => default
  , caps := fun l => if l = 0 then [Cap.node 5] else [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : HandoffArgs := { intro := 0, recip := 1, tgt := 5 }
def sPost : RecChainedState := (recCDelegate sPre argsRef.intro argsRef.recip argsRef.tgt).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but recipient 1's slot gains an EXTRA stolen `node 9`
cap on top of the honest handoff grant. The component-bind gate must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      caps := fun l => if l = 1 then Cap.node 9 :: sPost.kernel.caps 1 else sPost.kernel.caps l } }

def witnessOf (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) : List Int :=
  (List.range (validateHandoffEC.traceWidth)).map (fun w => encodeE2 SC validateHandoffEC s args s' w)

def validateHandoffWitnessVec (s : RecChainedState) (args : HandoffArgs) : List Int :=
  match recCDelegate s args.intro args.recip args.tgt with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem validateHandoffWitnessVec_commit {s s' : RecChainedState} {args : HandoffArgs}
    (h : recCDelegate s args.intro args.recip args.tgt = some s') :
    validateHandoffWitnessVec s args = witnessOf s args s' := by
  unfold validateHandoffWitnessVec; rw [h]

def honestWitness : List Int := validateHandoffWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72
#guard decide (satisfied (effectCircuit2 validateHandoffEC) (encodeE2 SC validateHandoffEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 validateHandoffEC) (encodeE2 SC validateHandoffEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

-- RIGHTS-ATTENUATION anti-ghost tooth: recipient 1's handoff grant is forged to an `endpoint 5 [grant]`
-- (amplified authority) instead of the honest `node 5`. The OLD rights-LENGTH `capCode % 2000003` could
-- alias such tampers; `encCap` binds the full rights, so the component-bind gate `68 ≠ 69` REJECTS.
def sForgedRights : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      caps := fun l => if l = 1 then [Cap.endpoint 5 [Auth.grant]] else sPost.kernel.caps l } }
#guard decide (satisfied (effectCircuit2 validateHandoffEC) (encodeE2 SC validateHandoffEC sPre argsRef sForgedRights)) == false

/-! ## §5 — JSON export. -/

def validateHandoffAirName : String := "dregg-validateHandoffA-v2"
def emittedValidateHandoff : EmittedDescriptor := emittedEffect2 validateHandoffAirName validateHandoffEC
def descriptorJson : String := emitDescriptorJson emittedValidateHandoff
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedValidateHandoff.constraints.length == 4
#guard emittedValidateHandoff.traceWidth == 72
#guard descriptorJson ==
  "{\"name\":\"dregg-validateHandoffA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
-- Structural component-bind goldens (the field-binding `refP2`/`encCap` digests replace the non-injective
-- `% 2000003` field hash; non-vacuity is at the bind gates; the Rust paste is regenerated from JSON).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged component differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms validateHandoffWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.ValidateHandoffWitness
