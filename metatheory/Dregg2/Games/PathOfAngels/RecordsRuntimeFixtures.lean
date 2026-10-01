/-
# Records runtime — the fixture-pin EVALUATION, out of the crypto archive's build

`RecordsRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its seventeen fixture pins ran `native_decide` at elaboration — each
accepted fixture row costing two native judge invocations — so any Records-fixture
regression was a hard failure of every Rust proving target in the workspace (the
compilation-unit coupling the stale-fixture outage measured). The fixtures' STATEMENTS
remain in `RecordsRuntime.lean` as evaluation-free `check_* : Bool` definitions, beside
the private fixture rows and views they must see; THIS module is where they are RUN. It
is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING,
so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The fail-closed convention transfers: a check whose
projected view refuses answers `false`, so a broken projection reds THIS module.

Named residue in the parent: NONE — no construction there demands a proof as data.
-/
import Dregg2.Games.PathOfAngels.RecordsRuntime

namespace Dregg2.Games.PathOfAngels.RecordsRuntime

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.FinalizedRunEventAggregate

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

private def digestByte (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureGenesisWire : CanonStateWire := CanonStateWire.ofSemantic fixtureCanon

/-- ⚠ The TEMPLATE config — which is what a node actually retains and hands this
surface.  `poa_signal_genesis.rs` writes `run_seed: UNBOUND_RUN_SEED` because
genesis describes a mission with no instance; the live seed is drawn per run and
substituted into a COPY at judge time (`poa_signal_adapter.rs`).

The previous fixture handed this surface `fixtureConfig` — the LIVE config, whose
mission carries the derived `fixtureRunSeed` — so the fixture did not model what
production sends, and the emitted document therefore contained the live seed.
That exact previous fixture is retained below as
`hostile_live_run_seed_config_refused`. -/
private def fixtureTemplateConfig : SignalTriangulation.Config :=
  Emit.signalTemplateConfig fixtureFederationId fixtureSourceDigest
    fixtureContentDigest fixtureContentRoot fixtureActivationDigest

private def fixtureSignalConfigWire : SignalConfigWire :=
  SignalConfigWire.ofSemantic fixtureTemplateConfig

private def fixtureConfigWire : GameConfigWire := .signal fixtureSignalConfigWire

/-- The plaintext "transcript digest" of the fixture's single submitted action.
It exists here only to be searched for and not found. -/
private def fixtureTranscript : Digest32 :=
  SignalTriangulation.transcriptDigest [.submit fixtureConfig.target]

private def fixtureRow : RowWire where
  commitOrdinal := 7
  turnHash := digestByte 201
  receiptHash := digestByte 202
  actorRoot := fixtureCarrier.actorRoot
  signer := fixtureCarrier.playerKey
  judgeInput := ⟨fixtureInputBytes⟩
  judgeOutput := ⟨fixtureOutputBytes⟩

private def fixtureRequest (rows : List RowWire) : RequestWire where
  federationId := fixtureCarrier.federationId
  genesisCanon := ⟨fixtureGenesisWire.toJson⟩
  config := ⟨fixtureConfigWire.toJson⟩
  rows := rows

private def genesisOnlyView? : Option ViewWire := project? (fixtureRequest []).toJson

private def oneRunView? : Option ViewWire := project? (fixtureRequest [fixtureRow]).toJson

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_request_round_trips : Bool :=
  decide (decodeRequest (fixtureRequest [fixtureRow]).toJson =
    some (fixtureRequest [fixtureRow]))

/-- The point of the surface: with no finalized run at all, the view still
carries the exact world identity, world meters, Canon revision and playable
mission a run would land in — and says, in one word, that it is waiting for its
first run.  Height zero is not an empty page, and it is not a page pretending to
be full either.  Matches on the projected view; `none` answers `false`
(fail-closed). (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_genesis_only_view_is_a_real_world : Bool :=
  match genesisOnlyView? with
  | some view =>
      decide (view.federationId = fixtureCarrier.federationId) &&
      decide (view.contentSession = fixtureCanon.contentSession) &&
      decide (view.curatorKey = fixtureCanon.curatorKey) &&
      decide (view.stage = WorldStage.awaitingFirstRun) &&
      decide (view.mission.artifact =
        ArtifactRefWire.ofSemantic fixtureTemplateConfig.mission.artifact) &&
      decide (view.world = WorldStateWire.ofSemantic WorldState.empty) &&
      decide (view.canonRevision = 0) &&
      decide (view.runs = []) &&
      decide (view.archiveEntries = 0) &&
      decide (view.consumedRuns = 0)
  | none => false

/-- And one finalized run lands in every projection at once, with the artifact
carrying a Canon-derived beta status recomputed at read time.  The record's rung
is `finalized` and it carries the chain coordinate the host committed to.
Matches on the projected view; `none` answers `false` (fail-closed).
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_one_finalized_run_lands_in_every_projection : Bool :=
  match oneRunView? with
  | some view =>
      decide (view.stage = WorldStage.active) &&
      decide (view.runs.map RunWire.status = [RunStatus.finalized]) &&
      decide (view.runs.map RunWire.coordinate =
        [some { commitOrdinal := 7, turnHash := digestByte 201,
                receiptHash := digestByte 202, signer := fixtureCarrier.playerKey,
                actorRoot := fixtureCarrier.actorRoot }]) &&
      decide (view.runs.all RunWire.coherentB) &&
      decide (view.runs.map RunWire.artifact =
        [ArtifactRefWire.ofSemantic fixtureTemplateConfig.mission.artifact]) &&
      decide (view.catalog.map ArtifactStatusWire.status = ["beta"]) &&
      decide (view.archiveEntries = 1) &&
      decide (view.lockerEntries = 1) &&
      decide (view.attendantNotices = 1) &&
      decide (view.editorialInbox = 1) &&
      decide (view.canonRevision = 1) &&
      decide (view.consumedRuns = 1) &&
      decide (view.world.sequence = 1)
  | none => false

/-- The live seed of this fixture's run is a genuine 64-character spelling and is
NOT the all-zero template sentinel.  Without this, the absence below would be
satisfiable by the needle simply being something the document never had.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_live_seed_is_a_real_needle : Bool :=
  decide ((Emit.bytes32Hex fixtureRunSeed).length = 64) &&
    decide (fixtureRunSeed ≠ Emit.UNBOUND_RUN_SEED)

/-- ⚑ **`transcriptDigest` is not a digest.**  Bytes 1..3 of the fixture's
"digest" are exactly the three submitted bands, and the submitted code of a
solved run is the target.  This is the reviewer's second defect, stated as a
check about the actual encoding rather than asserted in prose — and it is why
no transcript-derived field exists on this surface.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_transcript_is_plaintext_of_the_submitted_code : Bool :=
  decide ((fixtureTranscript.bytes.getD 1 0).val = fixtureConfig.target.low.val) &&
    decide ((fixtureTranscript.bytes.getD 2 0).val = fixtureConfig.target.mid.val) &&
    decide ((fixtureTranscript.bytes.getD 3 0).val = fixtureConfig.target.high.val) &&
    decide (some fixtureConfig.target = SignalTriangulation.targetFromSeed? fixtureRunSeed)

/-- ⚑ The emitted document does not contain the live run seed anywhere — not in
the mission, not in a record, not in any field.  `targetFromSeed?` of that seed is
the answer, so this is the load-bearing absence.  Matches on the projected view;
`none` answers `false` (fail-closed). (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_view_never_publishes_the_live_run_seed : Bool :=
  match oneRunView? with
  | some view =>
      decide ((view.toJson.splitOn (Emit.bytes32Hex fixtureRunSeed)).length = 1)
  | none => false

/-- And it does not contain the plaintext transcript either.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_view_never_publishes_the_transcript : Bool :=
  match oneRunView? with
  | some view =>
      decide ((view.toJson.splitOn (Emit.bytes32Hex fixtureTranscript)).length = 1)
  | none => false

/-- ⚑ **The previous fixture, kept as the falsifier.**  Handing this surface the
LIVE config — the one whose mission carries the derived seed, which is what the
old fixture did — is refused outright rather than rendered.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_live_run_seed_config_refused : Bool :=
  (project? { fixtureRequest [fixtureRow] with
    config := ⟨(GameConfigWire.signal (SignalConfigWire.ofSemantic fixtureConfig)).toJson⟩ }.toJson).isNone

/-- ⚠ The falsifier above really does substitute something: the live config's
bytes differ from the template's, and they differ in the run seed specifically.
Without this the refusal could be refusing an unchanged input.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_live_config_is_a_real_substitution : Bool :=
  decide ((GameConfigWire.signal (SignalConfigWire.ofSemantic fixtureConfig)).toJson ≠ fixtureConfigWire.toJson) &&
    decide ((SignalConfigWire.ofSemantic fixtureConfig).mission.runSeed ≠
      fixtureConfigWire.mission.runSeed)

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_substituted_signer_refused : Bool :=
  (project? (fixtureRequest [{ fixtureRow with signer := digestByte 250 }]).toJson).isNone

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_substituted_actor_root_refused : Bool :=
  (project? (fixtureRequest [{ fixtureRow with actorRoot := digestByte 251 }]).toJson).isNone

/-- A row cannot start from a Canon the projection has not reached: the fold
rebuilds the chain rather than trusting a stored successor.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_row_against_a_foreign_genesis_refused : Bool :=
  (project? { fixtureRequest [fixtureRow] with
    genesisCanon := ⟨fixtureSuccessorCanonWire.toJson⟩ }.toJson).isNone

/-- The same finalized run cannot land twice: Canon's consumed-receipt admission
is re-run inside the fold. (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_replayed_row_refused : Bool :=
  (project? (fixtureRequest
    [fixtureRow, { fixtureRow with commitOrdinal := 8 }]).toJson).isNone

/-- Rows must arrive in strict commit order; a reordered history refuses.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_out_of_order_rows_refused : Bool :=
  (project? (fixtureRequest
    [{ fixtureRow with commitOrdinal := 8 }, fixtureRow]).toJson).isNone

/-- A foreign authority cannot read this world's records under its own id.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_foreign_authority_refused : Bool :=
  (project? { fixtureRequest [] with federationId := digestByte 252 }.toJson).isNone

/-- A mission bound to another world cannot be published beside this Canon.
(Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_hostile_mission_from_another_world_refused : Bool :=
  (project? { fixtureRequest [] with
    config := ⟨(GameConfigWire.signal { fixtureSignalConfigWire with
      mission := { fixtureSignalConfigWire.mission with
        contentRoot := digestByte 253 } }).toJson⟩ }.toJson).isNone

/-- (Pinned `= true` in `RecordsRuntimeFixtures`.) -/
def check_fixture_export_refuses_malformed : Bool :=
  decide (recordsProjectFFI ((fixtureRequest []).toJson ++ "\n") = "")

theorem fixture_request_round_trips :
    check_fixture_request_round_trips = true := by native_decide

theorem fixture_genesis_only_view_is_a_real_world :
    check_fixture_genesis_only_view_is_a_real_world = true := by native_decide

theorem fixture_one_finalized_run_lands_in_every_projection :
    check_fixture_one_finalized_run_lands_in_every_projection = true := by native_decide

theorem fixture_live_seed_is_a_real_needle :
    check_fixture_live_seed_is_a_real_needle = true := by native_decide

theorem fixture_transcript_is_plaintext_of_the_submitted_code :
    check_fixture_transcript_is_plaintext_of_the_submitted_code = true := by native_decide

theorem view_never_publishes_the_live_run_seed :
    check_view_never_publishes_the_live_run_seed = true := by native_decide

theorem view_never_publishes_the_transcript :
    check_view_never_publishes_the_transcript = true := by native_decide

theorem hostile_live_run_seed_config_refused :
    check_hostile_live_run_seed_config_refused = true := by native_decide

theorem hostile_live_config_is_a_real_substitution :
    check_hostile_live_config_is_a_real_substitution = true := by native_decide

theorem hostile_substituted_signer_refused :
    check_hostile_substituted_signer_refused = true := by native_decide

theorem hostile_substituted_actor_root_refused :
    check_hostile_substituted_actor_root_refused = true := by native_decide

theorem hostile_row_against_a_foreign_genesis_refused :
    check_hostile_row_against_a_foreign_genesis_refused = true := by native_decide

theorem hostile_replayed_row_refused :
    check_hostile_replayed_row_refused = true := by native_decide

theorem hostile_out_of_order_rows_refused :
    check_hostile_out_of_order_rows_refused = true := by native_decide

theorem hostile_foreign_authority_refused :
    check_hostile_foreign_authority_refused = true := by native_decide

theorem hostile_mission_from_another_world_refused :
    check_hostile_mission_from_another_world_refused = true := by native_decide

theorem fixture_export_refuses_malformed :
    check_fixture_export_refuses_malformed = true := by native_decide

#assert_compiled fixture_request_round_trips
#assert_compiled fixture_genesis_only_view_is_a_real_world
#assert_compiled fixture_one_finalized_run_lands_in_every_projection
#assert_compiled fixture_live_seed_is_a_real_needle
#assert_compiled fixture_transcript_is_plaintext_of_the_submitted_code
#assert_compiled view_never_publishes_the_live_run_seed
#assert_compiled view_never_publishes_the_transcript
#assert_compiled hostile_live_run_seed_config_refused
#assert_compiled hostile_live_config_is_a_real_substitution
#assert_compiled hostile_substituted_signer_refused
#assert_compiled hostile_substituted_actor_root_refused
#assert_compiled hostile_row_against_a_foreign_genesis_refused
#assert_compiled hostile_replayed_row_refused
#assert_compiled hostile_out_of_order_rows_refused
#assert_compiled hostile_foreign_authority_refused
#assert_compiled hostile_mission_from_another_world_refused
#assert_compiled fixture_export_refuses_malformed

end Dregg2.Games.PathOfAngels.RecordsRuntime
