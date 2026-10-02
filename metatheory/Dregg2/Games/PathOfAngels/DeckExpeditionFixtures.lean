/-
# DeckExpedition — the fixture EVALUATION, out of the crypto archive's build

`DeckExpedition.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its fixtures ran eleven `native_decide` pins at elaboration — whole
expedition replays — so a game-fixture regression was a hard failure of every Rust proving
target in the workspace (the compilation-unit coupling the stale-fixture outage measured).
The STATEMENTS remain in `DeckExpedition.lean` as evaluation-free `check_* : Bool`
definitions, beside the pack, party and transcripts they replay; THIS module is where they
are RUN.  It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI`
by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
prerequisite replay refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Two construction proofs did NOT move (`fixture_raw_config_valid`,
`fixture_tight_raw_config_valid`) — `Config` carries its validity proof as data, so they
must elaborate where `fixtureConfig` and `fixtureTightConfig` are built.  They are the
named residue; the fixtures header in `DeckExpedition.lean` records it.
-/
import Dregg2.Games.PathOfAngels.DeckExpedition

namespace Dregg2.Games.PathOfAngels.DeckExpedition

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DeckGraph

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def fixturePlayer : Digest32 := DeckGraph.zeroDigest

def fixtureKey : ExpeditionKey where
  pack := fixtureConfig.packKey
  playerKey := fixturePlayer
  day := fixtureConfig.raw.day
  counter := 1

def fixtureKeyTwo : ExpeditionKey := { fixtureKey with counter := 2 }
def fixtureKeyThree : ExpeditionKey := { fixtureKey with counter := 3 }

def fixtureInitial : State := initialState fixtureConfig fixturePlayer

/-- The hand-built fixture initial state satisfies the complete state invariant.
(Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_initial_state_valid : Bool := validStateB fixtureConfig fixtureInitial

def fixtureActions : List Action :=
  [ .begin fixtureKey fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront fixtureHazard.id fixtureContainment.id
  , .traverse DeckGraph.fixtureWrap.id
  , .recover fixtureSalvage.id fixtureEngineer.id
  , .traverse DeckGraph.fixtureMirror.id
  , .survey fixtureArtifact fixturePathfinder.id
  , .traverse DeckGraph.fixturePhase.id
  , .extract
  ]

def fixtureAcceptedB : Bool :=
  match replay fixtureConfig fixtureActions.length fixtureInitial fixtureActions with
  | some (state, [receipt]) =>
      decide (state.active = none) &&
      decide (receipt.key = fixtureKey) &&
      decide (receipt.finalPosition = DeckGraph.fixtureFinalPosition) &&
      decide (fixtureSalvage.id ∈ receipt.recovered) &&
      decide (fixtureRelic ∈ receipt.outcome.contribution.relics) &&
      decide (fixtureArtifact ∈ receipt.outcome.betaCandidates) &&
      decide (salvageRecordById? state.salvage fixtureSalvage.id =
        some { id := fixtureSalvage.id, custody := .secured }) &&
      validStateB fixtureConfig state
  | _ => false

/-- The complete authored transcript extracts, with the exact receipt.
(Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_full_expedition_accepts : Bool := fixtureAcceptedB

/-- An unfinished run can withdraw, but carried salvage returns to its exact
authored deck room and produces no extraction receipt.  Charted rooms persist. -/
def fixtureWithdrawActions : List Action :=
  [ .begin fixtureKey fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront fixtureHazard.id fixtureContainment.id
  , .traverse DeckGraph.fixtureWrap.id
  , .recover fixtureSalvage.id fixtureEngineer.id
  , .withdraw
  ]

def fixtureWithdrawalRestoresB : Bool :=
  match replay fixtureConfig fixtureWithdrawActions.length fixtureInitial fixtureWithdrawActions with
  | some (state, []) =>
      decide (salvageRecordById? state.salvage fixtureSalvage.id =
        some { id := fixtureSalvage.id, custody := .onDeck fixtureSalvage.room }) &&
      decide (DeckGraph.fixtureRoomC.id ∈ state.visited) &&
      validStateB fixtureConfig state
  | _ => false

/-- (Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_withdrawal_restores_custody : Bool := fixtureWithdrawalRestoresB

def fixtureSameKeyReplayRefusedB : Bool :=
  match replay fixtureConfig 2 fixtureInitial
      [.begin fixtureKey fixtureParty, .withdraw] with
  | some (state, []) => decide (step fixtureConfig state (.begin fixtureKey fixtureParty) = none)
  | _ => false

/-- (Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_same_key_replay_refused : Bool := fixtureSameKeyReplayRefusedB

def fixtureDailyExhaustionB : Bool :=
  match replay fixtureConfig 4 fixtureInitial
      [ .begin fixtureKey fixtureParty, .withdraw
      , .begin fixtureKeyTwo fixtureParty, .withdraw ] with
  | some (state, []) =>
      decide (step fixtureConfig state (.begin fixtureKeyThree fixtureParty) = none)
  | _ => false

/-- (Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_daily_budget_is_hard : Bool := fixtureDailyExhaustionB

def fixtureUnknownArtifact : ArtifactRef :=
  { fixtureArtifact with artifactId := ⟨999999⟩ }

def fixtureUndeclaredDiscoveryRefusedB : Bool :=
  match step fixtureConfig fixtureInitial (.begin fixtureKey fixtureParty) with
  | some begun =>
      decide (step fixtureConfig begun.state
        (.survey fixtureUnknownArtifact fixturePathfinder.id) = none)
  | none => false

/-- (Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_undeclared_discovery_refused : Bool := fixtureUndeclaredDiscoveryRefusedB

def fixtureEarlyExtractionRefusedB : Bool :=
  match step fixtureConfig fixtureInitial (.begin fixtureKey fixtureParty) with
  | some begun => decide (step fixtureConfig begun.state .extract = none)
  | none => false

/-- (Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_early_extraction_refused : Bool := fixtureEarlyExtractionRefusedB

def fixtureTightRawConfig : RawConfig := { fixtureRawConfig with turnBudget := 1 }

/-- ⚠ NAMED RESIDUE, the second one.  `fixtureTightConfig` cannot be built without it;
see the fixtures header. -/
theorem fixture_tight_raw_config_valid : configValidB fixtureTightRawConfig = true := by
  native_decide

def fixtureTightConfig : Config :=
  { raw := fixtureTightRawConfig, valid := fixture_tight_raw_config_valid }

def fixtureTightInitial : State := initialState fixtureTightConfig fixturePlayer
def fixtureTightKey : ExpeditionKey :=
  { fixtureKey with pack := fixtureTightConfig.packKey }

/-- A one-turn budget refuses the second in-run action.
(Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_turn_budget_refuses_second_run_action : Bool :=
  (replay fixtureTightConfig 3 fixtureTightInitial
    [ .begin fixtureTightKey fixtureParty
    , .traverse DeckGraph.fixtureOneWay.id
    , .confront fixtureHazard.id fixtureContainment.id ]).isNone

def fixtureTreatmentActions : List Action :=
  [ .begin fixtureKey fixtureParty
  , .traverse DeckGraph.fixtureOneWay.id
  , .confront fixtureHazard.id fixtureContainment.id
  , .treat fixtureMedic.id fixtureContainment.id
  ]

def fixtureTreatmentB : Bool :=
  match replay fixtureConfig fixtureTreatmentActions.length fixtureInitial fixtureTreatmentActions with
  | some (state, []) =>
      match officerById? state.officers fixtureContainment.id with
      | some officer => decide (officer.injury.val = 0)
      | none => false
  | _ => false

/-- (Pinned `= true` in `DeckExpeditionFixtures`.) -/
def check_fixture_declared_treatment_repairs_injury : Bool := fixtureTreatmentB

#assert_compiled fixture_tight_raw_config_valid

theorem fixture_initial_state_valid :
    check_fixture_initial_state_valid = true := by native_decide

theorem fixture_full_expedition_accepts :
    check_fixture_full_expedition_accepts = true := by native_decide

theorem fixture_withdrawal_restores_custody :
    check_fixture_withdrawal_restores_custody = true := by native_decide

theorem fixture_same_key_replay_refused :
    check_fixture_same_key_replay_refused = true := by native_decide

theorem fixture_daily_budget_is_hard :
    check_fixture_daily_budget_is_hard = true := by native_decide

theorem fixture_undeclared_discovery_refused :
    check_fixture_undeclared_discovery_refused = true := by native_decide

theorem fixture_early_extraction_refused :
    check_fixture_early_extraction_refused = true := by native_decide

theorem fixture_turn_budget_refuses_second_run_action :
    check_fixture_turn_budget_refuses_second_run_action = true := by native_decide

theorem fixture_declared_treatment_repairs_injury :
    check_fixture_declared_treatment_repairs_injury = true := by native_decide

#assert_compiled fixture_initial_state_valid
#assert_compiled fixture_full_expedition_accepts
#assert_compiled fixture_withdrawal_restores_custody
#assert_compiled fixture_same_key_replay_refused
#assert_compiled fixture_daily_budget_is_hard
#assert_compiled fixture_undeclared_discovery_refused
#assert_compiled fixture_early_extraction_refused
#assert_compiled fixture_turn_budget_refuses_second_run_action
#assert_compiled fixture_declared_treatment_repairs_injury

end Dregg2.Games.PathOfAngels.DeckExpedition
