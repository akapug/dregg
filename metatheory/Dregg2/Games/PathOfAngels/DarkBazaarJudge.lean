/-
# Path of Angels — Dark Bazaar v1 network judge

The exported evaluator is one fail-closed composition: strict canonical decode,
proof-carrying public-state reconstruction, concrete N=4/K=4 private descriptor
authorization, PoA admission/accounting, exact public successor reconstruction,
and labelled Lean-computed receipt digests.  The private opening is consumed by
the judge and absent from output.
-/
import Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire

namespace Dregg2.Games.PathOfAngels.DarkBazaarJudge

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire

set_option autoImplicit false

structure Settlement where
  inputBytes : String
  input : SemanticInput
  evidence : VerifiedSettlementEvidence input.claim
  successor : BazaarState
  applied : applySettlement input.claim evidence input.state = some successor
  successorWire : StateWire
  successorSemantic : BazaarState
  successorWireDecodes : successorWire.toSemantic? = some successorSemantic
  successorExact : observeState successorSemantic = observeState successor

def settle (inputBytes : String) (input : SemanticInput) : Option Settlement := do
  let evidence ← verifyV1? input.claim input.root input.witness
  match applied : applySettlement input.claim evidence input.state with
  | none => none
  | some successor =>
      let successorWire := input.wire.state.successorCandidate input.wire.claim
      match decoded : successorWire.toSemantic? with
      | none => none
      | some successorSemantic =>
          if exact : observeState successorSemantic = observeState successor then
            some {
              inputBytes
              input
              evidence
              successor
              applied
              successorWire
              successorSemantic
              successorWireDecodes := decoded
              successorExact := exact
            }
          else none

def Settlement.output (settlement : Settlement) : OutputWire :=
  OutputWire.ofTransition settlement.inputBytes settlement.input.wire settlement.successorWire

def canonicalOutput? (output : OutputWire) : Option OutputWire :=
  if decodeOutput output.toJson = some output then some output else none

def process (bytes : String) : Option OutputWire := do
  let wire ← decodeInput bytes
  let input ← wire.toSemantic?
  let settlement ← settle bytes input
  canonicalOutput? settlement.output

def processWire (bytes : String) : Option String :=
  (process bytes).map OutputWire.toJson

/-- Empty is the sole semantic-refusal sentinel.  No Rust semantic twin or
caller-supplied authorization bit exists behind this export. -/
@[export dregg_poa_dark_bazaar_judge]
def darkBazaarJudgeFFI (bytes : String) : String :=
  (processWire bytes).getD ""

theorem darkBazaarJudgeFFI_success_iff {inputBytes outputBytes : String}
    (output_nonempty : outputBytes ≠ "") :
    darkBazaarJudgeFFI inputBytes = outputBytes ↔
      processWire inputBytes = some outputBytes := by
  cases processed : processWire inputBytes with
  | none =>
      constructor
      · intro accepted
        have empty : "" = outputBytes := by
          simpa [darkBazaarJudgeFFI, processed] using accepted
        exact (output_nonempty empty.symm).elim
      · intro accepted
        contradiction
  | some output => simp [darkBazaarJudgeFFI, processed]

theorem process_output_decodes {inputBytes : String} {output : OutputWire}
    (accepted : process inputBytes = some output) :
    decodeOutput output.toJson = some output := by
  cases hwire : decodeInput inputBytes with
  | none => simp [process, hwire] at accepted
  | some wire =>
      cases hsemantic : wire.toSemantic? with
      | none => simp [process, hwire, hsemantic] at accepted
      | some input =>
          cases hsettle : settle inputBytes input with
          | none => simp [process, hwire, hsemantic, hsettle] at accepted
          | some settlement =>
              by_cases hdecode :
                  decodeOutput settlement.output.toJson = some settlement.output
              · simp [process, hwire, hsemantic, hsettle, canonicalOutput?, hdecode] at accepted
                cases accepted
                exact hdecode
              · simp [process, hwire, hsemantic, hsettle, canonicalOutput?, hdecode] at accepted

/-! ## Complete executable fixture

⚑ **THE FIXTURE NO LONGER EVALUATES IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build root — and the ten `native_decide` pins below
ran at elaboration, so any fixture regression here was a hard failure of every Rust proving
target in the workspace (the compilation-unit coupling the stale-fixture outage measured). The
fixture's STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition (a `def`
body elaborates without running), beside the descriptor root, commitment and order nullifiers
they are built from. The EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `DarkBazaarJudgeFixtures.lean`, rooted in the `PathOfAngelsGuards`
library: a plain `lake build` still runs every pin, and a stale fixture reds the guard library
instead of the archive.

Named residue: NONE — every fixture value here is a plain `def`, so no proof is demanded as
data at construction and all ten pins moved. -/

#assert_axioms darkBazaarJudgeFFI_success_iff
#assert_axioms process_output_decodes

-- The ten fixture pins (`native_decide` + `#assert_compiled`) live in
-- `DarkBazaarJudgeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the fixture header above.

end Dregg2.Games.PathOfAngels.DarkBazaarJudge
