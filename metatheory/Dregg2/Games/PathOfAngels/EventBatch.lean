/-
# EventBatch — one finalized turn, many replayable PoA aggregates

`EventSourcing` gives every aggregate an exact local history.  A local history
is not, by itself, an atomic world transaction: one finalized game turn may
advance Canon, a daily, an attendant, custody, and a market projection together.

This module supplies the missing Lean-authored transaction statement.  One
batch binds an exact PoA deployment, finalized Dregg carrier, actor, ordered
event indices, every per-stream predecessor/successor, and one batch digest.
The fold below is the semantic planning phase for a durable all-or-none append.
Rust may persist the returned plan, but it may not select another ordering or
invent another stream successor.

The digest functions remain named deployment boundaries.  This file proves
structural replay properties; it does not claim collision resistance, durable
atomicity, or that a host supplied the real finalized `CommitRecord`.
-/
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.EventBatch

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

/-! ## One deployment and one finalized carrier -/

/-- Identity of the PoA world whose aggregates may participate in a batch.
This is the common intersection already carried by `CanonState`, game receipts,
attendants, and Galley provisioning. -/
structure WorldIdentity where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
deriving DecidableEq

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

def WorldIdentity.validB (world : WorldIdentity) : Bool :=
  world.federationId != zeroDigest && world.contentRoot != zeroDigest &&
    world.activationDigest != zeroDigest && world.contentSession != zeroDigest &&
    world.contentEpoch.value != 0

/-- Exact finalized carrier shared by every event in one batch.  `blockId`,
`turnHash`, `receiptHash`, and `commitOrdinal` must be welded to the generic
`CommitRecord`; `actorRoot` and `signer` must be welded to the native judge. -/
structure FinalizedTurnCoordinate where
  world : WorldIdentity
  commitOrdinal : Nat
  blockId : Digest32
  turnHash : Digest32
  receiptHash : Digest32
  actorRoot : Digest32
  signer : Digest32
deriving DecidableEq

def FinalizedTurnCoordinate.validB (coordinate : FinalizedTurnCoordinate) : Bool :=
  coordinate.world.validB && coordinate.blockId != zeroDigest &&
    coordinate.turnHash != zeroDigest && coordinate.receiptHash != zeroDigest &&
    coordinate.actorRoot != zeroDigest && coordinate.signer != zeroDigest

/-- A stream is an aggregate together with the schema version under which its
event bytes are interpreted.  Schema version is part of stream identity. -/
structure StreamId where
  world : WorldIdentity
  aggregate : AggregateId
  version : SchemaVersion
deriving DecidableEq

def StreamId.validB (stream : StreamId) : Bool :=
  stream.world.validB && stream.aggregate.namespaceId = stream.world.federationId &&
    stream.aggregate.kind != 0 && stream.aggregate.key != zeroDigest && stream.version.value != 0

def streamOfStatement (world : WorldIdentity) (statement : EventStatement) : StreamId where
  world
  aggregate := statement.aggregate
  version := statement.version

/-- Authoritative pre/post cursor material for one stream.  `head` is the
semantic event digest, not a host's storage-frame digest. -/
structure StreamHead where
  stream : StreamId
  sequence : Nat
  head : Digest32
deriving DecidableEq

def streamIds (heads : List StreamHead) : List StreamId :=
  heads.map StreamHead.stream

def headFor? : List StreamHead → StreamId → Option StreamHead
  | [], _ => none
  | head :: heads, stream =>
      if head.stream = stream then some head else headFor? heads stream

def replaceHead (heads : List StreamHead) (successor : StreamHead) : List StreamHead :=
  heads.map fun head => if head.stream = successor.stream then successor else head

/-! ## Ordered batch statement -/

/-- One payload-erased, fully ordered event.  Payload bytes are committed by
`statement.payloadDigest`; `eventDigest` is the exact successor head. -/
structure IndexedEvent where
  eventIndex : Nat
  statement : EventStatement
  eventDigest : Digest32
deriving DecidableEq

/-- The digest preimage for the complete cross-aggregate transaction. -/
structure Statement where
  coordinate : FinalizedTurnCoordinate
  events : List IndexedEvent
deriving DecidableEq

structure Envelope where
  statement : Statement
  batchDigest : Digest32
deriving DecidableEq

/-- Cryptographic and canonical-codec boundary selected at deployment. -/
structure DigestBoundary where
  eventDigest : EventStatement → Digest32
  batchDigest : Statement → Digest32

abbrev MAX_BATCH_EVENTS : Nat := 4096
abbrev WIRE_U32_MODULUS : Nat := 2 ^ 32
abbrev WIRE_U64_MODULUS : Nat := 2 ^ 64

inductive Error where
  | emptyBatch
  | batchTooLarge
  | duplicateInitialStream
  | invalidCoordinateIdentity
  | invalidInitialHead
  | commitOrdinalOutOfRange
  | eventIndexOutOfRange
  | sequenceOutOfRange
  | wrongBatchDigest
  | wrongEventIndex
  | wrongFederationNamespace
  | unknownStream
  | wrongSequence
  | wrongPredecessor
  | wrongEventDigest
deriving DecidableEq, Repr

/-- The only successor state exposed by successful batch admission. -/
structure AppliedBatch where
  coordinate : FinalizedTurnCoordinate
  batchDigest : Digest32
  events : List IndexedEvent
  successorHeads : List StreamHead
deriving DecidableEq

private def applyOne (boundary : DigestBoundary)
    (coordinate : FinalizedTurnCoordinate) (expectedIndex : Nat)
    (heads : List StreamHead) (event : IndexedEvent) : Except Error (List StreamHead) := do
  if event.eventIndex != expectedIndex then throw .wrongEventIndex
  if WIRE_U32_MODULUS ≤ event.eventIndex then throw .eventIndexOutOfRange
  if WIRE_U64_MODULUS ≤ event.statement.sequence then throw .sequenceOutOfRange
  if event.statement.aggregate.namespaceId != coordinate.world.federationId then
    throw .wrongFederationNamespace
  let stream := streamOfStatement coordinate.world event.statement
  if !stream.validB then throw .invalidInitialHead
  let before ← match headFor? heads stream with
    | none => throw .unknownStream
    | some before => pure before
  if event.statement.sequence != before.sequence + 1 then throw .wrongSequence
  if event.statement.predecessor != before.head then throw .wrongPredecessor
  if event.eventDigest != boundary.eventDigest event.statement then throw .wrongEventDigest
  pure (replaceHead heads {
    stream
    sequence := event.statement.sequence
    head := event.eventDigest
  })

/-- Ordered planning fold.  Repeating a stream is permitted only by explicitly
placing another indexed event whose sequence and predecessor continue the
successor produced by its earlier event. -/
def applyEvents (boundary : DigestBoundary) (coordinate : FinalizedTurnCoordinate) :
    Nat → List StreamHead → List IndexedEvent → Except Error (List StreamHead)
  | _, heads, [] => .ok heads
  | expectedIndex, heads, event :: events => do
      let next ← applyOne boundary coordinate expectedIndex heads event
      applyEvents boundary coordinate (expectedIndex + 1) next events

/-- Admit one all-or-none semantic batch against exact initial stream heads. -/
def applyBatch (boundary : DigestBoundary) (initialHeads : List StreamHead)
    (envelope : Envelope) : Except Error AppliedBatch := do
  if envelope.statement.events.isEmpty then throw .emptyBatch
  if MAX_BATCH_EVENTS < envelope.statement.events.length then throw .batchTooLarge
  if !envelope.statement.coordinate.validB then throw .invalidCoordinateIdentity
  if !initialHeads.all (fun head => head.stream.validB &&
      head.stream.world = envelope.statement.coordinate.world && head.head != zeroDigest &&
      head.sequence < WIRE_U64_MODULUS) then throw .invalidInitialHead
  if !(streamIds initialHeads).Nodup then throw .duplicateInitialStream
  if WIRE_U64_MODULUS ≤ envelope.statement.coordinate.commitOrdinal then
    throw .commitOrdinalOutOfRange
  if envelope.batchDigest != boundary.batchDigest envelope.statement then
    throw .wrongBatchDigest
  let successorHeads ← applyEvents boundary envelope.statement.coordinate 0
    initialHeads envelope.statement.events
  pure {
    coordinate := envelope.statement.coordinate
    batchDigest := envelope.batchDigest
    events := envelope.statement.events
    successorHeads
  }

/-- Planning is a function, not an alternate-choice relation. -/
theorem applyBatch_deterministic (boundary : DigestBoundary)
    (initialHeads : List StreamHead) (envelope : Envelope) (left right : AppliedBatch)
    (hl : applyBatch boundary initialHeads envelope = .ok left)
    (hr : applyBatch boundary initialHeads envelope = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

/-! ## Executable cross-aggregate and hostile fixtures

⚑ **THE FIXTURES NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target. The fixtures'
STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition beside the
private fixture material; the EVALUATION — each `check_* = true`, pinned by
`native_decide` + `#assert_compiled` — lives in `EventBatchFixtures.lean`, rooted in the
`PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale
fixture reds the guard library instead of the archive. The hostile checks pin the EXACT
refusal error, which refutes acceptance by construction. Named residue: none. -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureWorld : WorldIdentity where
  federationId := digestByte 1
  contentRoot := digestByte 2
  activationDigest := digestByte 3
  contentSession := digestByte 4
  contentEpoch := ⟨5⟩

private def stream (kind : Nat) (key : Nat) : StreamId where
  world := fixtureWorld
  aggregate := { namespaceId := fixtureWorld.federationId, kind, key := digestByte key }
  version := ⟨1⟩

private def fixtureBoundary : DigestBoundary where
  eventDigest statement := digestByte
    (100 + statement.aggregate.kind + statement.sequence)
  batchDigest statement := digestByte
    (200 + statement.coordinate.commitOrdinal + statement.events.length)

private def event (eventIndex : Nat) (stream : StreamId) (sequence predecessor payload : Nat) :
    IndexedEvent :=
  let statement : EventStatement := {
    aggregate := stream.aggregate
    version := stream.version
    sequence
    predecessor := digestByte predecessor
    payloadDigest := digestByte payload
  }
  { eventIndex, statement, eventDigest := fixtureBoundary.eventDigest statement }

#assert_axioms applyBatch_deterministic

-- The thirteen fixture pins (`#assert_compiled` + `native_decide`) live in
-- `EventBatchFixtures.lean`, rooted in `PathOfAngelsGuards` — see the fixtures header above.

end Dregg2.Games.PathOfAngels.EventBatch
