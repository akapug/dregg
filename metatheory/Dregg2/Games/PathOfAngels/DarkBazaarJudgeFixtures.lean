/-
# Dark Bazaar v1 judge — the fixture EVALUATION, out of the crypto archive's build

`DarkBazaarJudge.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its complete executable fixture ran ten `native_decide` pins at elaboration —
each one through the concrete N=4/K=4 private descriptor hash and the exported judge — so any
fixture regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The fixture's STATEMENTS remain in
`DarkBazaarJudge.lean` as evaluation-free `check_* : Bool` definitions, beside the descriptor
root, commitment and order nullifiers they are built from; THIS module is where they are RUN. It
is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ Named residue: NONE. Every fixture value in the parent is a plain `def`, so no proof is
demanded as data at construction and all ten pins moved.
-/
import Dregg2.Games.PathOfAngels.DarkBazaarJudge

namespace Dregg2.Games.PathOfAngels.DarkBazaarJudge

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def repeatedDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

def fixtureFederation : Digest32 := repeatedDigest 1
def fixtureContentRoot : Digest32 := repeatedDigest 2
def fixtureActivation : Digest32 := repeatedDigest 3
def fixtureSession : Digest32 := repeatedDigest 4
def fixtureSeller : Digest32 := repeatedDigest 17
def fixtureBuyer : Digest32 := repeatedDigest 34
def fixtureSourceRoot : Digest32 := repeatedDigest 51
def fixtureBaseNullifier : Digest32 := repeatedDigest 113
def fixtureQuoteNullifier : Digest32 := repeatedDigest 114

def fixtureIdentity : IdentityWire where
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  contentEpoch := 1
  seller := fixtureSeller
  buyer := fixtureBuyer
  baseAsset := { kind := "supplies", relicId := 0 }
  quoteAsset := { kind := "intel", relicId := 0 }

def fixtureOutput : ClearingOutputWire := ⟨1, 13⟩

def fixturePolicy : PolicyWire where
  buckets := 4
  quoteTick := 2
  maxOrders := 4
  maxOrderQuantity := 15
  maxPublicAssetInputs := 8
  allowedOutputs := [fixtureOutput]

def fixtureDescriptorRoot : Fin 8 → Int :=
  V1.hash8
    (Market.DarkBazaarPrivateDescriptor.rootPreimage V1.DESCRIPTOR_SESSION
      Market.DarkBazaarPrivateDescriptor.fixtureWitness)

def fixtureCommitment : Digest32 := V1.digestOfRoot fixtureDescriptorRoot

def fixtureOrderNullifiers : List Digest32 :=
  ((List.ofFn fun slot : Fin 4 =>
      (V1.orderId fixtureDescriptorRoot slot).nullifier.value).eraseDups).insertionSort
    (fun left right => Emit.bytes32Hex left < Emit.bytes32Hex right)

def fixtureBaseInput : AssetInputWire where
  nullifier := fixtureBaseNullifier
  owner := fixtureSeller
  asset := { kind := "supplies", relicId := 0 }
  amount := 13

def fixtureQuoteInput : AssetInputWire where
  nullifier := fixtureQuoteNullifier
  owner := fixtureBuyer
  asset := { kind := "intel", relicId := 0 }
  amount := 52

def fixtureClaim : ClaimWire where
  spec := {
    identity := fixtureIdentity
    batchId := 7
    sourceRoot := fixtureSourceRoot
    policy := fixturePolicy
  }
  privateBookCommitment := fixtureCommitment
  output := fixtureOutput
  baseInputs := [fixtureBaseInput]
  quoteInputs := [fixtureQuoteInput]
  orderNullifiers := fixtureOrderNullifiers

def fixtureState : StateWire where
  identity := fixtureIdentity
  policy := fixturePolicy
  baseNotes := [fixtureBaseInput]
  quoteNotes := [fixtureQuoteInput]
  buyerBaseCustody := 0
  sellerQuoteCustody := 0
  consumedAssetNullifiers := []
  consumedOrderNullifiers := []
  consumedBatches := []

def fixtureOpening : OpeningWire where
  format := AUTHORIZATION_FORMAT
  orders := [⟨2, 10⟩, ⟨1, 6⟩, ⟨4, 5⟩, ⟨5, 8⟩]
  blinding := [777, 778, 779, 780, 781, 782, 783, 784]

def fixtureInput : InputWire where
  state := fixtureState
  claim := fixtureClaim
  opening := fixtureOpening

def fixtureInputBytes : String := fixtureInput.toJson
def fixtureExpectedOutput : OutputWire :=
  OutputWire.ofTransition fixtureInputBytes fixtureInput
    (fixtureState.successorCandidate fixtureClaim)
def fixtureOutputBytes : String := fixtureExpectedOutput.toJson

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_input_roundtrip : Bool :=
  decide (decodeInput fixtureInputBytes = some fixtureInput)

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_semantic_inhabited : Bool := fixtureInput.toSemantic?.isSome

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_process_success : Bool :=
  processWire fixtureInputBytes == some fixtureOutputBytes

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_trailing_byte_refused : Bool :=
  (processWire (fixtureInputBytes ++ "\n")).isNone

def fixtureUnknownFieldBytes : String :=
  fixtureInputBytes.replace "\"opening\":" "\"unknown\":0,\"opening\":"

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_unknown_field_refused : Bool := (processWire fixtureUnknownFieldBytes).isNone

def fixtureUppercaseDigestBytes : String :=
  fixtureInputBytes.replace
    "e0a5c50385fa3b60e5ed0433b4c7075201b0b473b6afc4591d98ed7182d5102e"
    "E0a5c50385fa3b60e5ed0433b4c7075201b0b473b6afc4591d98ed7182d5102e"

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_uppercase_digest_refused : Bool :=
  (processWire fixtureUppercaseDigestBytes).isNone

def fixtureReorderedNullifiers : InputWire :=
  { fixtureInput with claim := {
      fixtureInput.claim with orderNullifiers := fixtureInput.claim.orderNullifiers.reverse
    } }

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_reordered_nullifiers_refused : Bool :=
  (processWire fixtureReorderedNullifiers.toJson).isNone

def fixtureOverboundOutput : InputWire :=
  { fixtureInput with claim := { fixtureInput.claim with output :=
      ⟨fixtureInput.claim.output.bucket, DarkBazaar.Wire.maxOutputVolume + 1⟩ } }

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_overbound_output_refused : Bool :=
  (processWire fixtureOverboundOutput.toJson).isNone

def fixtureWrongOutput : InputWire :=
  { fixtureInput with claim := { fixtureInput.claim with output := ⟨2, 13⟩ } }

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_wrong_clearing_refused : Bool := (processWire fixtureWrongOutput.toJson).isNone

def fixtureWrongNullifiers : InputWire :=
  { fixtureInput with claim := {
      fixtureInput.claim with orderNullifiers := [repeatedDigest 200, repeatedDigest 201,
        repeatedDigest 202, repeatedDigest 203]
    } }

/-- (Pinned `= true` in `DarkBazaarJudgeFixtures`.) -/
def check_fixture_wrong_nullifiers_refused : Bool :=
  (processWire fixtureWrongNullifiers.toJson).isNone

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_semantic_inhabited :
    check_fixture_semantic_inhabited = true := by native_decide

theorem fixture_process_success :
    check_fixture_process_success = true := by native_decide

theorem fixture_trailing_byte_refused :
    check_fixture_trailing_byte_refused = true := by native_decide

theorem fixture_unknown_field_refused :
    check_fixture_unknown_field_refused = true := by native_decide

theorem fixture_uppercase_digest_refused :
    check_fixture_uppercase_digest_refused = true := by native_decide

theorem fixture_reordered_nullifiers_refused :
    check_fixture_reordered_nullifiers_refused = true := by native_decide

theorem fixture_overbound_output_refused :
    check_fixture_overbound_output_refused = true := by native_decide

theorem fixture_wrong_clearing_refused :
    check_fixture_wrong_clearing_refused = true := by native_decide

theorem fixture_wrong_nullifiers_refused :
    check_fixture_wrong_nullifiers_refused = true := by native_decide

#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_semantic_inhabited
#assert_compiled fixture_process_success
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_reordered_nullifiers_refused
#assert_compiled fixture_overbound_output_refused
#assert_compiled fixture_wrong_clearing_refused
#assert_compiled fixture_wrong_nullifiers_refused

end Dregg2.Games.PathOfAngels.DarkBazaarJudge
