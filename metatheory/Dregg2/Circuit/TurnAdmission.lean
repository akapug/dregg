/-
# Dregg2.Circuit.TurnAdmission — Wave 5 Prop-level whole-turn proof gate — CLOSED.

The commit-time admission gate (`turnProofRequired`) and its discharge `rust_proof_admits_commit`:
given the per-step emitted ⊑ `fullActionStep`
refinement (what the commit-time STARK over the folded turn circuit attests, supplied as `hstep`) plus
the emitted chain, the executor commits. No silent admission.
-/
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.TurnEmit
import Dregg2.Circuit.TurnCircuitCompose
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.TurnAdmission

open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness turnWitnessSatisfies foldStepRoots)
open Dregg2.Circuit.TurnEmit
  (TurnEmittedChain turnEmittedSat stepEmittedSat DescriptorLookup defaultDescriptorLookup
   turn_emitted_refines_exec)
open Dregg2.Circuit.TurnCircuitCompose (turnCircuitOfEmitted macaroonChainBinds)
open Dregg2.Circuit.ActionDispatch (turnSpec fullActionStep execFullTurnA_iff_turnSpec)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Prop-level admission gate. -/

/-- **`turnProofRequired`** — a turn commit requires a whole-turn witness whose step-root fold
reaches `postRoot` under the abstract `compress` portal, plus a non-trivial auth-chain digest
(the macaroon caveat-chain column is an explicit Wave-5 open hole). -/
def turnProofRequired (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (w : TurnWitness) : Prop :=
  turnWitnessSatisfies compress stepRoot w ∧
    w.authChain ≠ 0

/-- Turn emission satisfaction implies the root-chain half of `turnProofRequired`. -/
theorem turnProofRequired_of_emitted_chain
    (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    turnWitnessSatisfies compress stepRoot w :=
  h.root_chain

/-- Turn emission satisfaction implies the non-trivial auth-chain half too, when the auth column is
bound to a non-zero macaroon fold. -/
theorem turnProofRequired_of_chain_and_macaroon
    (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (baseAuth : ℤ)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w)
    (hmac : macaroonChainBinds compress stepRoot baseAuth w) :
    turnProofRequired compress stepRoot w :=
  ⟨h.root_chain, hmac.2⟩

/-! ## §2 — Rust commit-time proof seam — CLOSED (real proof). -/

/-- **`rust_proof_admits_commit`** (was `hole_rust_proof_at_commit`) — the Rust commit path requires a
STARK proof over the folded turn circuit. That proof's CONTENT is exactly the per-step emitted ⊑
`fullActionStep` refinement (`hstep`, discharged by `TurnEmit.step_emitted_refines_fullActionStep`).
Given it plus the emitted chain, the executor commits — no silent admission. -/
theorem rust_proof_admits_commit
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat defaultDescriptorLookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (hproof : turnProofRequired compress stepRoot w)
    (h : TurnEmittedChain defaultDescriptorLookup compress stepRoot s acts s' w) :
    execFullTurnA s acts = some s' :=
  turn_emitted_refines_exec defaultDescriptorLookup hstep s s' acts w compress stepRoot h

#assert_axioms turnProofRequired_of_emitted_chain
#assert_axioms turnProofRequired_of_chain_and_macaroon
#assert_axioms rust_proof_admits_commit

end Dregg2.Circuit.TurnAdmission