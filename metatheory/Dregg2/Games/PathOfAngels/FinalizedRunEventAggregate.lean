/-
# FinalizedRunEventAggregate — the second durable PoA aggregate

Signal finality already demonstrates the first special-purpose durable aggregate:
one finalized Dregg turn is judged by native Lean and its exact input/output and
Canon successor are welded into the generic commit transaction.  This module
extracts the smallest reusable *second aggregate* semantics from that path.

The canonical source is a dense event stream of exact judge input/output
bytes plus finalized-turn coordinates.  Every projection is rebuilt from the
same re-judged `JudgedRun`:

* Canon owns the world successor and replay key;
* Field Archive receives `ArchiveEntry.ofJudged`;
* the personal locker receives the same origin, scoped to the receipt player;
* Attendant receives a non-spendable `ReceiptIdentity` notice (never a forged
  `Credit`; its separate canonical-settlement capability is still required);
* Editorial receives an inbox notice only (never a curator capability or an
  automatic alpha promotion).

`FinalizedTurnCoordinate.turnHash` and `.receiptHash` are storage coordinates.
Lean checks the federation/signer/actor root it can reconstruct from the native
judge input.  The generic durable-store weld must compare the remaining fields
to the actual finalized `CommitRecord`, exactly as `poa_signal_state.rs` does
today.  `DigestBoundary` and atomic CAS remain named deployment
boundaries; this module does not relabel either as a proof.
-/
import Dregg2.Games.PathOfAngels.NetworkJudge
import Dregg2.Games.PathOfAngels.FieldArchive
import Dregg2.Games.PathOfAngels.AttendantKernel
import Dregg2.Games.PathOfAngels.EditorialRegistry
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

/-! ## One shared replay kernel

Finalized runs instantiate the generic `EventSourcing` kernel directly.  The
aggregate therefore shares exact sequence, predecessor, schema-version,
payload-digest, event-digest, snapshot, and rebuild semantics with every other
PoA aggregate.  Only the payload reducer below is game-specific. -/

/-! ## Exact finalized carrier and durable payload -/

/-- Coordinates supplied by the finalized-turn adapter and welded to the
generic commit row.  `eventIndex = 0` is the current exact Signal carrier shape:
one reserved event and no piggyback effects. -/
structure FinalizedTurnCoordinate where
  federationId : Digest32
  commitOrdinal : Nat
  turnHash : Digest32
  receiptHash : Digest32
  eventIndex : Nat
  actorRoot : Digest32
  signer : Digest32
deriving DecidableEq

/-- Durable, codec-ready event payload.  No semantic state or projection is
trusted from storage: reopening runs the native Lean judge over these exact
bytes again. -/
structure Payload where
  finalized : FinalizedTurnCoordinate
  judgeInput : String
  judgeOutput : String
deriving DecidableEq

/-- Checked in-memory view.  Its private constructor prevents a projection from
substituting a different settlement after `checkPayload?` has accepted the exact
native judge output. -/
structure CheckedPayload where
  private mk ::
  raw : Payload
  input : SemanticInput
  settlement : NetworkJudge.Settlement
  output : SignalOutputWire
  outputExact : output.toJson = raw.judgeOutput
  federationExact : raw.finalized.federationId = settlement.carrier.federationId
  actorRootExact : raw.finalized.actorRoot = settlement.carrier.actorRoot
  signerExact : raw.finalized.signer = settlement.carrier.playerKey
  eventIndexExact : raw.finalized.eventIndex = 0

/-- Decode and re-run the actual Signal judge.  Exact byte equality—not merely a
semantic output decode—binds the durable event to Lean's canonical result. -/
def checkPayload? (raw : Payload) : Option CheckedPayload := do
  let wire ← decodeSignalInput raw.judgeInput
  let input ← wire.toSemantic?
  let settlement ← NetworkJudge.settle input
  let output ← settlement.toWire?
  if houtput : output.toJson = raw.judgeOutput then
    if hfederation : raw.finalized.federationId = settlement.carrier.federationId then
      if hroot : raw.finalized.actorRoot = settlement.carrier.actorRoot then
        if hsigner : raw.finalized.signer = settlement.carrier.playerKey then
          if hindex : raw.finalized.eventIndex = 0 then
            some ⟨raw, input, settlement, output, houtput, hfederation,
              hroot, hsigner, hindex⟩
          else none
        else none
      else none
    else none
  else none

/-! ## Receipt-derived read models -/

/-- Personal display placement is a projection, not custody.  The exact Archive
origin and receipt player are retained; moving this card in a UI cannot transfer
or mint the underlying artifact. -/
structure LockerEntry where
  owner : Digest32
  origin : FieldArchive.ArchiveEntry
deriving DecidableEq

def LockerEntry.ofJudged (run : JudgedRun) : LockerEntry where
  owner := run.receipt.playerKey
  origin := FieldArchive.ArchiveEntry.ofJudged run

structure LockerState where
  entries : Finset LockerEntry
deriving DecidableEq

def LockerState.empty : LockerState := ⟨∅⟩

def LockerState.acquire (run : JudgedRun) (state : LockerState) : LockerState where
  entries := insert (LockerEntry.ofJudged run) state.entries

/-- This is deliberately weaker than `AttendantKernel.Credit`: it is a durable
notification that an exact settled receipt exists, but supplies neither the
Attendant canonical-settlement capability nor owner-command authority. -/
structure AttendantCreditNotice where
  owner : Digest32
  receipt : Attendant.ReceiptIdentity
deriving DecidableEq

def AttendantCreditNotice.ofJudged (run : JudgedRun) : AttendantCreditNotice where
  owner := run.receipt.playerKey
  receipt := Attendant.receiptIdentity run.receipt

/-- Likewise, an inbox item is not an `EditorialRegistry.CuratorCapability` and
does not call `prepareStep`.  It only makes the exact beta origin available for
later human editorial selection. -/
structure EditorialInboxEntry where
  origin : FieldArchive.ArchiveEntry
deriving DecidableEq

def EditorialInboxEntry.ofJudged (run : JudgedRun) : EditorialInboxEntry :=
  ⟨FieldArchive.ArchiveEntry.ofJudged run⟩

/-- All read models rebuilt from the event stream.  Canon remains in its exact
bounded wire representation so stream admission has decidable byte-level state
identity; proof fields inside semantic `CanonState` are deliberately not treated
as persistence identity.  World is not stored twice. -/
structure Projection where
  canon : CanonStateWire
  archive : FieldArchive.ArchiveState
  locker : LockerState
  attendantNotices : Finset AttendantCreditNotice
  editorialInbox : Finset EditorialInboxEntry
  lastFinalized : Option FinalizedTurnCoordinate
deriving DecidableEq

def Projection.initial (canon : CanonState) : Projection where
  canon := CanonStateWire.ofSemantic canon
  archive := FieldArchive.ArchiveState.empty
  locker := LockerState.empty
  attendantNotices := ∅
  editorialInbox := ∅
  lastFinalized := none

def Projection.world? (projection : Projection) : Option WorldState :=
  projection.canon.world.toSemantic?

/-- One reducer, one judged run, all projections.  The event's pre-Canon must be
the current projection and recomputing `applyGameEffect` must yield the exact
successor retained by the native Signal settlement. -/
def reduce : Reducer Projection Payload := fun before raw =>
  match checkPayload? raw with
  | none => none
  | some checked =>
      if _hbefore : CanonStateWire.ofSemantic checked.settlement.beforeCanon = before.canon then
        let run := checked.settlement.judgedRun
        some {
          canon := checked.output.successorCanon
          archive := FieldArchive.acquire run before.archive
          locker := before.locker.acquire run
          attendantNotices := insert (AttendantCreditNotice.ofJudged run) before.attendantNotices
          editorialInbox := insert (EditorialInboxEntry.ofJudged run) before.editorialInbox
          lastFinalized := some raw.finalized
        }
      else none

theorem reduce_projects_one_exact_judged_run {before after : Projection} {raw : Payload}
    (h : reduce before raw = some after) :
    ∃ checked : CheckedPayload,
      checkPayload? raw = some checked ∧
      CanonStateWire.ofSemantic checked.settlement.beforeCanon = before.canon ∧
      after.canon = checked.output.successorCanon ∧
      FieldArchive.ArchiveEntry.ofJudged checked.settlement.judgedRun ∈
        after.archive.entries ∧
      LockerEntry.ofJudged checked.settlement.judgedRun ∈ after.locker.entries ∧
      AttendantCreditNotice.ofJudged checked.settlement.judgedRun ∈
        after.attendantNotices ∧
      EditorialInboxEntry.ofJudged checked.settlement.judgedRun ∈
        after.editorialInbox := by
  unfold reduce at h
  cases hc : checkPayload? raw with
  | none => simp [hc] at h
  | some checked =>
      simp only [hc] at h
      split at h
      · rename_i hbefore
        injection h with heq
        subst after
        exact ⟨checked, rfl, hbefore, rfl,
          by simp [FieldArchive.acquire], by simp [LockerState.acquire],
          by simp, by simp⟩
      · simp at h

theorem reduce_world_is_native_judge_successor {before after : Projection} {raw : Payload}
    (h : reduce before raw = some after) :
    ∃ checked : CheckedPayload,
      checkPayload? raw = some checked ∧
      after.world? = checked.output.successorCanon.world.toSemantic? := by
  obtain ⟨checked, checkedRaw, _, canonExact, _⟩ := reduce_projects_one_exact_judged_run h
  exact ⟨checked, checkedRaw, by simp [Projection.world?, canonExact]⟩

/-! ## Stream construction -/

/-! ## Executable fixture and hostile paths

⚑ **THE FIXTURE NO LONGER EVALUATES IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target. The fixture's
STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition; the
EVALUATION — each `check_* = true`, pinned by `native_decide` + `#assert_compiled` — lives
in `FinalizedRunEventAggregateFixtures.lean`, rooted in the `PathOfAngelsGuards` library:
a plain `lake build` still runs every pin, and a stale fixture reds the guard library
instead of the archive. Fail-closed convention: the populated-projections probe matches on
its `Option` prerequisites and answers `false` when any refuses. Named residue: none. -/

#assert_axioms reduce_projects_one_exact_judged_run
#assert_axioms reduce_world_is_native_judge_successor

-- The seven fixture pins (`#assert_compiled` + `native_decide`) live in
-- `FinalizedRunEventAggregateFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- fixture header above.

end Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate
