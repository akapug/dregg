/-
# FinalizedRunEventAggregate — the fixture EVALUATION, out of the crypto archive's build

`FinalizedRunEventAggregate.lean` sits in the `Dregg2.FFI` closure (the crypto archive's
build root), and until 2026-08-08 its fixture ran seven `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving
target in the workspace. The fixture's STATEMENTS remain in
`FinalizedRunEventAggregate.lean` as evaluation-free `check_* : Bool` definitions, beside
the private fixture material they must see; THIS module is where they are RUN. It is
rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
prerequisite probe refuses answers `false`, so a broken prerequisite reds THIS module.
Named residue: none.
-/
import Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

namespace Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.EventSourcing

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The aggregate identity is deployment/session scoped.  Kind `2` is the
candidate second durable PoA aggregate; it is not a display name. -/
def aggregateId (canon : CanonState) : AggregateId where
  namespaceId := canon.federationId
  kind := 2
  key := canon.contentSession

def streamSpec (canon : CanonState) (genesisHead : Digest32) : StreamSpec where
  aggregate := aggregateId canon
  version := ⟨1⟩
  genesisHead

/-- Deterministically construct the next semantic event envelope.  This is not
a durable append or finality claim; `applyEvent` rechecks it, and
the store must CAS the exact predecessor head atomically with the commit row. -/
def nextEnvelope (spec : StreamSpec)
    (digests : DigestBoundary Payload)
    (cursor : Cursor) (payload : Payload) :
    EventEnvelope Payload :=
  let statement : EventStatement := {
    aggregate := spec.aggregate
    version := spec.version
    sequence := cursor.sequence + 1
    predecessor := cursor.head
    payloadDigest := digests.payloadDigest payload
  }
  { statement, payload, eventDigest := digests.eventDigest statement }

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureCoordinate : FinalizedTurnCoordinate where
  federationId := fixtureCarrier.federationId
  commitOrdinal := 7
  turnHash := digestByte 201
  receiptHash := digestByte 202
  eventIndex := 0
  actorRoot := fixtureCarrier.actorRoot
  signer := fixtureCarrier.playerKey

private def fixturePayload : Payload where
  finalized := fixtureCoordinate
  judgeInput := fixtureInputBytes
  judgeOutput := fixtureOutputBytes

private def fixtureDigests : DigestBoundary Payload where
  payloadDigest payload := digestByte
    (20 + payload.finalized.commitOrdinal + payload.judgeInput.length + payload.judgeOutput.length)
  eventDigest statement := digestByte
    (40 + statement.sequence + statement.version.value + statement.aggregate.kind)

private def fixtureSpec : StreamSpec :=
  streamSpec fixtureCanon (digestByte 10)

private def fixtureEventOne : EventEnvelope Payload :=
  nextEnvelope fixtureSpec fixtureDigests fixtureSpec.genesisCursor fixturePayload

private def fixtureProjection? : Option Projection :=
  match rebuildProjection fixtureSpec fixtureDigests reduce
      (Projection.initial fixtureCanon) [fixtureEventOne] with
  | .ok projection => some projection
  | .error _ => none

private def populatedProjectionsProbe : Option Bool := do
  let checked ← checkPayload? fixturePayload
  let projection ← fixtureProjection?
  let run := checked.settlement.judgedRun
  some (
    decide (projection.world? = some checked.settlement.successorWorld) &&
    decide (FieldArchive.ArchiveEntry.ofJudged run ∈ projection.archive.entries) &&
    decide (LockerEntry.ofJudged run ∈ projection.locker.entries) &&
    decide (AttendantCreditNotice.ofJudged run ∈ projection.attendantNotices) &&
    decide (EditorialInboxEntry.ofJudged run ∈ projection.editorialInbox) &&
    decide (ArtifactRefWire.ofSemantic run.receipt.mission.artifact ∈
      projection.canon.known) &&
    decide (projection.lastFinalized = some fixtureCoordinate))

/-- (Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_fixture_native_judge_event_populates_every_projection : Bool :=
  decide (populatedProjectionsProbe = some true)

def wrongOutputPayload : Payload := { fixturePayload with judgeOutput := "{}" }

/-- (Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_hostile_non_lean_output_refused : Bool :=
  (checkPayload? wrongOutputPayload).isNone

def wrongSignerPayload : Payload := {
  fixturePayload with finalized := { fixtureCoordinate with signer := digestByte 250 } }

/-- (Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_hostile_finalized_signer_substitution_refused : Bool :=
  (checkPayload? wrongSignerPayload).isNone

def wrongEventIndexPayload : Payload := {
  fixturePayload with finalized := { fixtureCoordinate with eventIndex := 1 } }

/-- The initial carrier contract is one reserved game command per finalized
turn.  A future multi-event carrier must version this rule rather than silently
reusing the v1 aggregate. (Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_hostile_unversioned_second_carrier_event_refused : Bool :=
  (checkPayload? wrongEventIndexPayload).isNone

private def wrongPredecessorStatement : EventStatement :=
  { fixtureEventOne.statement with predecessor := digestByte 99 }

private def wrongPredecessorEnvelope : EventEnvelope Payload :=
  { fixtureEventOne with
    statement := wrongPredecessorStatement
    eventDigest := fixtureDigests.eventDigest wrongPredecessorStatement }

/-- (Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_hostile_wrong_stream_predecessor_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests reduce (Projection.initial fixtureCanon)
    [wrongPredecessorEnvelope] = .error .wrongPredecessor)

private def wrongPayloadDigestStatement : EventStatement :=
  { fixtureEventOne.statement with payloadDigest := digestByte 77 }

private def wrongPayloadDigestEnvelope : EventEnvelope Payload :=
  { fixtureEventOne with
    statement := wrongPayloadDigestStatement
    eventDigest := fixtureDigests.eventDigest wrongPayloadDigestStatement }

/-- (Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_hostile_wrong_payload_digest_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests reduce (Projection.initial fixtureCanon)
    [wrongPayloadDigestEnvelope] = .error .wrongPayloadDigest)

private def fixtureReplayEvent : EventEnvelope Payload :=
  nextEnvelope fixtureSpec fixtureDigests {
    aggregate := fixtureSpec.aggregate
    version := fixtureSpec.version
    sequence := 1
    head := fixtureEventOne.eventDigest
  } fixturePayload

/-- A fresh stream sequence cannot launder an already consumed judged receipt:
the projection reducer re-runs Canon's receipt-key/counter admission.
(Pinned `= true` in `FinalizedRunEventAggregateFixtures`.) -/
def check_hostile_same_finalized_run_at_fresh_sequence_refused : Bool :=
  decide (rebuild fixtureSpec fixtureDigests reduce
    (Projection.initial fixtureCanon) [fixtureEventOne, fixtureReplayEvent] =
    .error .reducerRejected)

theorem fixture_native_judge_event_populates_every_projection :
    check_fixture_native_judge_event_populates_every_projection = true := by native_decide

theorem hostile_non_lean_output_refused :
    check_hostile_non_lean_output_refused = true := by native_decide

theorem hostile_finalized_signer_substitution_refused :
    check_hostile_finalized_signer_substitution_refused = true := by native_decide

theorem hostile_unversioned_second_carrier_event_refused :
    check_hostile_unversioned_second_carrier_event_refused = true := by native_decide

theorem hostile_wrong_stream_predecessor_refused :
    check_hostile_wrong_stream_predecessor_refused = true := by native_decide

theorem hostile_wrong_payload_digest_refused :
    check_hostile_wrong_payload_digest_refused = true := by native_decide

theorem hostile_same_finalized_run_at_fresh_sequence_refused :
    check_hostile_same_finalized_run_at_fresh_sequence_refused = true := by native_decide

#assert_compiled fixture_native_judge_event_populates_every_projection
#assert_compiled hostile_non_lean_output_refused
#assert_compiled hostile_finalized_signer_substitution_refused
#assert_compiled hostile_unversioned_second_carrier_event_refused
#assert_compiled hostile_wrong_stream_predecessor_refused
#assert_compiled hostile_wrong_payload_digest_refused
#assert_compiled hostile_same_finalized_run_at_fresh_sequence_refused

end Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
