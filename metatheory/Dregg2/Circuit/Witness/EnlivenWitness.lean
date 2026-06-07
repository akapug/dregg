/-
# Dregg2.Circuit.Witness.EnlivenWitness — execute→prove→verify→anti-ghost for `enlivenRefA`.

Amplifies the `Transfer` beachhead to the CapTP sturdy-ref ENLIVEN effect `enlivenRefA` (a `swiss`
side-table refcount bump) through the v2 framework (`EffectCommit2`), the SAME `execute → prove →
verify → anti-ghost` path — but over a `listComponent` (the touched thing is the `swiss : List
SwissRecord` side-table, not a function-field). REUSED (not re-proved):

  * `Exec.execFullA` — the real chained executor (`.enlivenRefA sw actor exporter claimed` arm = the
    swiss-enliven chain). `execFullA s (.enlivenRefA …) = some s'` IS the executor computing the post.
  * `Spec.SwissEnliven.execFullA_enliven_iff_spec` — executor ⟺ `EnlivenSpec`.
  * `Inst.EnlivenRefA.{enlivenE, apex_iff_enlivenSpec, enlivenRefA_full_sound}`.
  * `EffectCommit2.{encodeE2, satisfiedE2, effect2_circuit_full_complete}`.

SUPPLIED: §3 the abstract execute→prove / prove→state halves (carrying `RestIffNoSwiss`,
`logHashInjective`, and the `listLeafInjective LE`/`compressNInjective cN` swiss-list CR portals); §4
the executor-driven witness generator `enlivenWitnessVec` (runs `execFullA`, lays the v2 width-72
witness over a concrete swiss-list digest surface) with the concrete `#guard`s; §5 the JSON the Rust
`lean_executor_derived_enliven` prover proves+verifies / rejects. ANTI-GHOST: a forged post-state where
the `swiss` list is NOT updated (the refcount stays at 1 instead of the enlivened 2) — the
component-bind gate (68/69) rejects (a real UNSAT), while the rest frame + guard + log stay honest.
-/
import Dregg2.Circuit.Inst.enlivenRefA

namespace Dregg2.Circuit.Witness.EnlivenWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.Inst.EnlivenRefA
open Dregg2.Circuit.Spec.SwissEnliven
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Auth)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

/-- **`execute_produces_satisfying_witness` — execute→prove.** An `EnlivenSpec`-satisfying step makes
the v2 full-state witness SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via
`apex_iff_enlivenSpec`. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoSwiss S.RH)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState)
    (hspec : EnlivenSpec s args.sw args.actor args.exporter args.claimed s') :
    satisfiedE2 S (enlivenE LE cN hN hLE) (encodeE2 S (enlivenE LE cN hN hLE) s args s') :=
  effect2_circuit_full_complete S (enlivenE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (enlivenGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_enlivenSpec LE cN hN hLE s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state` — prove→accept.** ANY witness satisfying the v2 circuit
proves the complete declarative `EnlivenSpec`. Reuses `enlivenRefA_full_sound`; carries
`RestIffNoSwiss`, `logHashInjective`, and the swiss-list CR portals (`listLeafInjective LE`,
`compressNInjective cN`). -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (enlivenE LE cN hN hLE) (encodeE2 S (enlivenE LE cN hN hLE) s args s')) :
    EnlivenSpec s args.sw args.actor args.exporter args.claimed s' :=
  enlivenRefA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A concrete, computable swiss-list digest surface over a toy domain. The leaf encodes ALL of a
`SwissRecord`'s fields (crucially `refcount`, which enliven bumps), so the component digest moves when
the list is enlivened — and a forged post-state that fails to bump shows up. -/

/-- Concrete swiss-record leaf: a positional fold over the record's fields (including `refcount`). -/
def swissLeafC : SwissRecord → ℤ :=
  fun e => (e.swiss : ℤ) * 1000000 + (e.exporter : ℤ) * 10000 + (e.target : ℤ) * 100
           + (e.rights.length : ℤ) * 10 + (e.refcount : ℤ)

/-- Concrete swiss-list sponge: a positional Horner fold (length-tagged). -/
def swissListC : List ℤ → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 100000000 + x) (xs.length : ℤ)

/-- Concrete swiss side-table digest: the sponge of the per-record leaves. -/
def swissDigC (ss : List SwissRecord) : ℤ := swissListC (ss.map swissLeafC)

/-- Concrete rest hash (reads only the non-`swiss` frame fields). -/
def rhC : RecordKernelState → ℤ := fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)

/-- Concrete log hash. -/
def lhC : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => acc * 1000000 + (t.actor : ℤ) + 1) ((xs.length : ℤ) + 1)

def SC : Surface2 := { RH := rhC, LH := lhC }

/-- The concrete `swiss` component (computable list digest), spec-expected being the enlivened list. -/
def swissCompC : ActiveComponent RecChainedState EnlivenArgs :=
  { digest     := fun k => swissDigC k.swiss
  , expected   := fun s args => swissDigC (enlivenSwissPostClause s args)
  , postClause := fun s args post => swissDigC post.swiss = swissDigC (enlivenSwissPostClause s args)
  , binds      := fun _ _ _ h => h
  , encodes    := fun _ _ _ h => h }

/-- The concrete `enlivenRefA` effect spec (computable surface), for the witness `#guard`s. -/
def enlivenEC : EffectSpec2 RecChainedState EnlivenArgs :=
  { view         := chainView
  , active       := swissCompC
  , logUpdate    := some (fun s args => enlivenReceipt args.actor args.exporter :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := enlivenGuardGates
  , guardProp    := enlivenGuardProp
  , guardWidth   := 1
  , guardEncode  := enlivenGuardEncode
  , guardLocal   := enlivenGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: one sturdy ref at index 0 (refcount 1), actor 0 enlivens it. -/

def rec0 : SwissRecord :=
  { swiss := 0, exporter := 0, target := 1, rights := [Auth.read], refcount := 1 }

def kPre : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => default, caps := fun _ => [], swiss := [rec0] }

def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : EnlivenArgs := { sw := 0, actor := 0, exporter := 0, claimed := [Auth.read] }
def sPost : RecChainedState := (execFullA sPre (.enlivenRefA 0 0 0 [Auth.read])).getD sPre

/-- **THE FORGERY:** the SAME guard/log, but the `swiss` list is NOT enlivened — the refcount stays at
1 instead of the bumped 2. The component-bind gate (68/69) must reject the un-bumped list. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with swiss := kPre.swiss } }

def witnessOf (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState) : List Int :=
  (List.range enlivenEC.traceWidth).map (fun w => encodeE2 SC enlivenEC s args s' w)

/-- **`enlivenWitnessVec`** — runs `execFullA`; on commit lays out the satisfying v2 witness. -/
def enlivenWitnessVec (s : RecChainedState) (args : EnlivenArgs) : List Int :=
  match execFullA s (.enlivenRefA args.sw args.actor args.exporter args.claimed) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem enlivenWitnessVec_commit {s s' : RecChainedState} {args : EnlivenArgs}
    (h : execFullA s (.enlivenRefA args.sw args.actor args.exporter args.claimed) = some s') :
    enlivenWitnessVec s args = witnessOf s args s' := by
  unfold enlivenWitnessVec; rw [h]

def honestWitness : List Int := enlivenWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfied (effectCircuit2 enlivenEC) (encodeE2 SC enlivenEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 enlivenEC) (encodeE2 SC enlivenEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- swiss not enlivened: REJECTED
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export. -/

def enlivenAirName : String := "dregg-enlivenRefA-v2"
def emittedEnliven : EmittedDescriptor := emittedEffect2 enlivenAirName enlivenEC
def descriptorJson : String := emitDescriptorJson emittedEnliven
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedEnliven.constraints.length == 4
#guard emittedEnliven.traceWidth == 72
#guard descriptorJson == "{\"name\":\"dregg-enlivenRefA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitness.getD 68 0 == 100000112   -- enlivened (refcount 2) component digest
#guard forgedWitness.getD 68 0 == 100000111   -- un-bumped (refcount 1) — differs
#guard forgedWitness.getD 69 0 == 100000112   -- expected stays the enlivened list

#assert_axioms enlivenWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.EnlivenWitness
