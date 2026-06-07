/-
# Dregg2.Circuit.Witness.DropRefWitness — execute→prove→verify→anti-ghost for `dropRefA`.

Amplifies the `Transfer` beachhead to the CapTP GC effect `dropRefA` (an UNCONDITIONAL cap-graph
`removeEdge`) through the v2 framework (`EffectCommit2`). REUSED (not re-proved):

  * `Exec.recCRevoke` — the REAL chained authority executor (runs `recKRevokeTarget`, prepends an
    authority receipt). `execFullA s (.dropRefA holder t) = some (recCRevoke s holder t)`.
  * `Spec.AuthorityRevocation.execFullA_dropRef_iff_spec` — executor ⟺ `RevokeSpec`.
  * `Inst.DropRefA.{dropRefE, apex_iff_revokeSpec, dropRefA_full_sound}`.
  * `EffectCommit2.{encodeE2, satisfiedE2, effect2_circuit_full_complete}`.

SUPPLIED: §3 the abstract execute→prove / prove→state halves; §4 the executor-driven witness generator
`dropRefWitnessVec` (runs `recCRevoke`, lays the v2 width-72 witness over a concrete caps surface) with
the concrete `#guard`s; §5 the JSON the Rust `lean_executor_derived_drop_ref` prover proves+verifies /
rejects. ANTI-GHOST: a forged post-state where the post `caps` FAIL to revoke (the holder keeps the
edge to the dropped target) — the component-bind gate (68/69) rejects (a real UNSAT), while the rest
frame + guard + log stay honest (a projection circuit would have passed it).
-/
import Dregg2.Circuit.Inst.dropRefA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.DropRefWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.DropRefA
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest turnLogDigest)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness` — execute→prove.** A `RevokeSpec`-satisfying step makes the
v2 full-state witness SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via
`apex_iff_revokeSpec`. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : DropRefArgs) (s' : RecChainedState)
    (hspec : RevokeSpec s args.holder args.t s') :
    satisfiedE2 S (dropRefE D hD) (encodeE2 S (dropRefE D hD) s args s') :=
  effect2_circuit_full_complete S (dropRefE D hD)
    (fun k k' h => (hRest k k').mpr h) (dropRefGuardEncodes D hD) s args s'
    ((apex_iff_revokeSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state` — prove→accept.** ANY witness satisfying the v2 circuit
proves the complete declarative `RevokeSpec` (all 17 kernel fields + log). Reuses `dropRefA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DropRefArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (dropRefE D hD) (encodeE2 S (dropRefE D hD) s args s')) :
    RevokeSpec s args.holder args.t s' :=
  dropRefA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A concrete, computable caps surface over a toy domain (small modular folds, so the digests fit i64 —
the v2 gate only checks EQUALITY). -/

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

/-- Concrete rest hash: reads only the NON-`caps` frame fields (so a pure cap forgery leaves it fixed —
the component-bind gate bites, not the rest gate). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- The log hash: the REAL `turnLogDigest` (binds `src`/`dst`/`amt` the OLD `actor % 2000003` fold
DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `caps` component (computable digest), spec-expected being `removeEdgeCaps`. -/
def capsCompC : ActiveComponent RecChainedState DropRefArgs :=
  { digest     := fun k => capsDigConcrete k.caps
  , expected   := fun s args => capsDigConcrete (removeEdgeCaps s.kernel.caps args.holder args.t)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (removeEdgeCaps s.kernel.caps args.holder args.t)
  , binds      := fun _ _ _ h => h
  , encodes    := fun _ _ _ h => h }

/-- The concrete `dropRefA` effect spec (computable surface), for the witness `#guard`s. -/
def dropRefEC : EffectSpec2 RecChainedState DropRefArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => authReceipt args.holder :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := dropRefGuardGates
  , guardProp    := dropRefGuardProp
  , guardWidth   := 1
  , guardEncode  := dropRefGuardEncode
  , guardLocal   := dropRefGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference triple: holder 0 holds `[node 5, node 7]`, drops the ref to 5. -/

def kPre : RecordKernelState :=
  { accounts := {0, 1}
  , cell := fun _ => default
  , caps := fun l => if l = 0 then [Cap.node 5, Cap.node 7]
                     else if l = 1 then [Cap.node 9]
                     else [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : DropRefArgs := { holder := 0, t := 5 }
def sPost : RecChainedState := recCRevoke sPre argsRef.holder argsRef.t

/-- **THE FORGERY:** the SAME guard/log/frame, but the post `caps` FAIL to drop — holder 0 keeps
`[node 5, node 7]` (the `node 5` edge to target 5 is NOT removed). A bearer of the supposedly-dropped
cap stays authorized: an authority-forgery the component-bind gate must catch. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with caps := kPre.caps } }

def witnessOf (s : RecChainedState) (args : DropRefArgs) (s' : RecChainedState) : List Int :=
  (List.range dropRefEC.traceWidth).map (fun w => encodeE2 SC dropRefEC s args s' w)

/-- **`dropRefWitnessVec`** — runs the REAL executor `recCRevoke` (unconditional) and lays out the
satisfying full-state witness for the executor's post-state. -/
def dropRefWitnessVec (s : RecChainedState) (args : DropRefArgs) : List Int :=
  witnessOf s args (recCRevoke s args.holder args.t)

theorem dropRefWitnessVec_eq (s : RecChainedState) (args : DropRefArgs) :
    dropRefWitnessVec s args = witnessOf s args (recCRevoke s args.holder args.t) := rfl

def honestWitness : List Int := dropRefWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- THE EXECUTE→PROVE GUARANTEE.
#guard decide (satisfied (effectCircuit2 dropRefEC) (encodeE2 SC dropRefEC sPre argsRef sPost))
-- THE ANTI-GHOST TOOTH (real UNSAT): the un-revoked post-caps fail the component-bind gate.
#guard decide (satisfied (effectCircuit2 dropRefEC) (encodeE2 SC dropRefEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected: REJECTED
-- ...the forgery keeps the rest frame + guard honest (a projection circuit would pass it):
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export. -/

def dropRefAirName : String := "dregg-dropRefA-v2"
def emittedDropRef : EmittedDescriptor := emittedEffect2 dropRefAirName dropRefEC
def descriptorJson : String := emitDescriptorJson emittedDropRef
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedDropRef.constraints.length == 4
#guard emittedDropRef.traceWidth == 72
#guard descriptorJson == "{\"name\":\"dregg-dropRefA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
-- the honest component digest binds; the forged (un-revoked) one differs.
#guard !(honestWitness.getD 68 0 == forgedWitness.getD 68 0)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0

-- RIGHTS-ATTENUATION anti-ghost tooth: instead of un-revoking, holder 0's slot is forged to keep an
-- `endpoint 5 [grant]` (the dropped target 5 re-appears as an AMPLIFIED endpoint). The OLD rights-LENGTH
-- `capCode % 2000003` could alias such tampers; `encCap` binds the full rights, so the component-bind
-- gate `68 ≠ 69` REJECTS.
def sForgedRights : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      caps := fun l => if l = 0 then [Cap.node 7, Cap.endpoint 5 [Auth.grant]] else sPost.kernel.caps l } }
#guard decide (satisfied (effectCircuit2 dropRefEC) (encodeE2 SC dropRefEC sPre argsRef sForgedRights)) == false

#assert_axioms dropRefWitnessVec_eq
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.DropRefWitness
