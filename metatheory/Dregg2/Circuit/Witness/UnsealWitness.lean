/-
# Dregg2.Circuit.Witness.UnsealWitness — the v2 WITNESS GENERATOR for `unsealA`.

Closes the verifiable-execution beachhead for `unsealA` (the seal-box UNSEAL: recover the sealed
`payload` cap and grant it to `recipient`), over the GENERIC v2 framework (`EffectCommit2`), since
`unsealA` touches a single non-`cell` component (`kernel.caps`, a `funcComponent`). Reused:

  * `Exec.unsealChainA` — the REAL chained executor (gated on `unsealAdmitGuard`: actor holds the
    unsealer cap for `pid` ∧ the box exists; on commit grants the box payload to `recipient`).
  * `Inst.UnsealA.unsealA_full_sound` — a satisfying v2 witness PROVES `UnsealSpec` (all 16 frame
    fields + caps + log), carrying the realizable Poseidon-CR portals.
  * `EffectCommit2.effect2_circuit_full_complete` / `emittedEffect2` / `emitDescriptorJson`.

§3 the abstract execute→prove + verify→accept theorems; §4 the concrete `unsealWitnessVec` running the
real executor; §5 the descriptor + witness JSON the Rust prover consumes. The anti-ghost forgery is a
post `caps` table where `recipient` does NOT receive the recovered payload (the unseal grant is
dropped) — the component-bind gate 68≠69 = a real UNSAT.

CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.unsealA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.UnsealWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.UnsealA
open Dregg2.Circuit.Spec.SealBoxOperations
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

/-- **`execute_produces_satisfying_witness`** — a `UnsealSpec`-satisfying step makes the v2 witness
SATISFY the v2 circuit (via `apex_iff_unsealSpec` + `effect2_circuit_full_complete`). -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState)
    (hspec : UnsealSpec s args.pid args.actor args.recipient args.box s') :
    satisfiedE2 S (unsealE D hD) (encodeE2 S (unsealE D hD) s args s') :=
  effect2_circuit_full_complete S (unsealE D hD)
    (fun k k' h => (hRest k k').mpr h) (unsealGuardEncodes D hD) s args s'
    ((apex_iff_unsealSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state`** — ANY witness satisfying the v2 circuit proves
`UnsealSpec` (all 16 frame fields + caps + log). Reuses `unsealA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (unsealE D hD) (encodeE2 S (unsealE D hD) s args s')) :
    UnsealSpec s args.pid args.actor args.recipient args.box s' :=
  unsealA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves). -/

/-- Field-binding `Auth` index (so endpoint `rights` are bound, not collapsed to `.length`). -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6
/-- **Field-binding** `Cap` encoder: tag + target + the WHOLE rights list (the OLD `capCode` reduced
`endpoint t r => 11 + t*3 + r.length`, dropping WHICH rights for the LENGTH). -/
def encCap : Cap → List ℤ
  | .null         => [0]
  | .node t       => [1, (t : ℤ)]
  | .endpoint t r => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode
/-- One cell's cap-list digest: the REAL `refP2` sponge over the field-binding `encCap` (the OLD
`% 2000003` Horner was a NON-injective field hash). -/
def capListCode (cs : List Cap) : ℤ := recListDigest encCap cs
/-- Concrete caps digest over carrier `[0,4)`: the REAL `refP2` sponge of each cell's cap-list digest. -/
def capsDigConcrete : Caps → ℤ :=
  fun caps => refP2 ((List.range 4).map (fun l => capListCode (caps l)))

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.sealedBoxes.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- The log hash: the REAL `turnLogDigest` (binds `src`/`dst`/`amt` the OLD `actor % 2000003` fold
DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `caps` component (computable digest), spec-expected being the unseal `grantedCaps`. -/
def capsCompC : ActiveComponent RecChainedState UnsealArgs :=
  { digest    := fun k => capsDigConcrete k.caps
  , expected  := fun s args => capsDigConcrete (grantedCaps s.kernel.caps args.recipient args.box.payload)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (grantedCaps s.kernel.caps args.recipient args.box.payload)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

/-- The concrete `unsealA` effect spec (computable surface), for the witness `#guard`s. -/
def unsealEC : EffectSpec2 RecChainedState UnsealArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => unsealReceipt args.actor args.recipient :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := unsealGuardGates
  , guardProp    := unsealGuardProp
  , guardWidth   := 1
  , guardEncode  := unsealGuardEncode
  , guardLocal   := unsealGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference triple. -/

/-- The sealed box in the store: pair 7, sealer 0, payload `node 5`. -/
def refBox : SealedBoxRecord := { pairId := 7, sealer := 0, payload := Cap.node 5 }

/-- Concrete pre-state: actor 0 holds the unsealer cap `endpoint 7 [reply]` (so `holdsSealCapFor 7`
fires); the store holds `refBox`. Recipient 1 holds no caps. Accounts {0,1}. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1}
  , cell := fun _ => default
  , caps := fun l => if l = 0 then [Cap.endpoint 7 [Auth.reply]] else []
  , sealedBoxes := [refBox] }

def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The unseal args: actor 0 unseals pair 7 and grants the payload to recipient 1. -/
def argsRef : UnsealArgs := { pid := 7, actor := 0, recipient := 1, box := refBox }

/-- The honest post-state (run the REAL executor `unsealChainA`: recipient 1's caps gain `node 5`). -/
def sPost : RecChainedState := (unsealChainA sPre argsRef.pid argsRef.actor argsRef.recipient).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but recipient 1 does NOT receive the recovered payload
(the unseal grant is DROPPED — recipient 1's caps stay empty). The component-bind gate must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with caps := kPre.caps } }

/-! ### The witness vectors. -/

def witnessOf (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState) : List Int :=
  (List.range (unsealEC.traceWidth)).map (fun w => encodeE2 SC unsealEC s args s' w)

/-- **`unsealWitnessVec`** — runs `unsealChainA`; on commit produces the satisfying full-state v2
witness for the executor's post-state. -/
def unsealWitnessVec (s : RecChainedState) (args : UnsealArgs) : List Int :=
  match unsealChainA s args.pid args.actor args.recipient with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem unsealWitnessVec_commit {s s' : RecChainedState} {args : UnsealArgs}
    (h : unsealChainA s args.pid args.actor args.recipient = some s') :
    unsealWitnessVec s args = witnessOf s args s' := by
  unfold unsealWitnessVec; rw [h]

def honestWitness : List Int := unsealWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the v2 circuit.
#guard decide (satisfied (effectCircuit2 unsealEC) (encodeE2 SC unsealEC sPre argsRef sPost))

-- THE ANTI-GHOST TOOTH (real UNSAT): the dropped-grant forgery breaks the component-bind gate (68 ≠ 69).
#guard decide (satisfied (effectCircuit2 unsealEC) (encodeE2 SC unsealEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

-- RIGHTS-CONFUSION anti-ghost tooth: the recipient is granted an `endpoint 5 [grant]` (an
-- amplified-authority cap) instead of the honest `node 5` payload. The OLD `% 2000003` field hash over a
-- rights-LENGTH-reducing `capCode` could alias such tampers; `encCap` binds the full rights, so the
-- component-bind gate `68 ≠ 69` REJECTS.
def sForgedRights : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      caps := fun l => if l = 1 then [Cap.endpoint 5 [Auth.grant]] else sPost.kernel.caps l } }
#guard decide (satisfied (effectCircuit2 unsealEC) (encodeE2 SC unsealEC sPre argsRef sForgedRights)) == false

/-! ## §5 — JSON export. -/

def unsealAirName : String := "dregg-unsealA-v2"
def emittedUnseal : EmittedDescriptor := emittedEffect2 unsealAirName unsealEC
def descriptorJson : String := emitDescriptorJson emittedUnseal
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedUnseal.constraints.length == 4
#guard emittedUnseal.traceWidth == 72
#guard descriptorJson ==
  "{\"name\":\"dregg-unsealA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
-- Structural component-bind goldens (the field-binding `refP2`/`encCap` digests replace the non-injective
-- `% 2000003` field hashes; non-vacuity is at the bind gates; the Rust paste is regenerated from JSON).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged component differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms unsealWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.UnsealWitness
