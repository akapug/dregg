/-
# ContentContract — the specimen EVALUATION, out of the crypto archive's build

`ContentContract.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its spoiler-free specimen and named hostile packs ran eight `native_decide` pins
at elaboration — so any specimen regression was a hard failure of every Rust proving target in
the workspace (the compilation-unit coupling the stale-fixture outage measured). The pins'
STATEMENTS remain in `ContentContract.lean` as evaluation-free `check_* : Bool` definitions,
beside the packs they read; THIS module is where they are RUN. It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged. The hostile checks compare the EXACT error-code lists, so
a pack that refuses for a different reason still fails its pin.

⚠ Named residue: NONE. Every pack in the parent is a plain `def`, so no proof is demanded as
data at construction and all eight pins moved.
-/
import Dregg2.Games.PathOfAngels.ContentContract

namespace Dregg2.Games.PathOfAngels.ContentContract

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The spoiler-free specimen validates.
(Pinned `= true` in `ContentContractFixtures`.) -/
def check_fixture_content_is_valid : Bool := contentValidB fixtureContent

def hostileRoleRelabel : RawContent :=
  { fixtureContent with officers :=
      [ { officer := ⟨0⟩, credential := ⟨100⟩, role := .quartermaster }
      , { officer := ⟨1⟩, credential := ⟨101⟩, role := .engineer }
      , { officer := ⟨2⟩, credential := ⟨102⟩, role := .containment }
      , { officer := ⟨3⟩, credential := ⟨103⟩, role := .quartermaster } ] }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_role_relabel_refused : Bool :=
  decide ((validateWire hostileRoleRelabel).errorCodes = [2])

def hostileUnreachableExtraction : RawContent :=
  { fixtureContent with deck := DeckGraph.boundedSearchFailurePack }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_unreachable_extraction_refused : Bool :=
  decide ((validateWire hostileUnreachableExtraction).errorCodes = [3, 4])

def hostileAsymmetricEncounter : RawContent :=
  { fixtureContent with routes :=
      [ { id := ⟨0⟩, encounters := [⟨11⟩], path := DeckGraph.fixturePath }
      , { id := ⟨1⟩, encounters := [⟨10⟩, ⟨12⟩], path := DeckGraph.fixturePath }
      , { id := ⟨2⟩, encounters := [⟨10⟩, ⟨13⟩], path := DeckGraph.fixturePath } ] }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_route_encounter_asymmetry_refused : Bool :=
  decide ((validateWire hostileAsymmetricEncounter).errorCodes = [4])

def hostileUnwinnableOutcome : RawContent :=
  { fixtureContent with outcomes :=
      { route := ⟨0⟩, extraction := .returnNow, operationalCost := 99,
        agreement := .twoSpecialistSupport, featuredArtifact := ⟨20⟩,
        contribution := fixtureContribution 10 [], recovery := ⟨40⟩ } ::
      fixtureOutcomes.drop 1 }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_unwinnable_budget_refused : Bool :=
  decide ((validateWire hostileUnwinnableOutcome).errorCodes = [5])

def hostileAutomaticRecovery : RawContent :=
  { fixtureContent with recoveries :=
      [ { id := ⟨40⟩, grade := .clean, duration := .none,
          implementation := .betaRecordOnly, globalMeterDebit := 0 }
      , { id := ⟨41⟩, grade := .containmentDebt,
          duration := .untilCuratorSuccessor,
          implementation := .automaticWorldMutation, globalMeterDebit := 1 } ] }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_automatic_recovery_refused : Bool :=
  decide ((validateWire hostileAutomaticRecovery).errorCodes = [6])

def hostileMarketRelic : RawContent :=
  { fixtureContent with relics :=
      [ { id := ⟨30⟩, sourceEncounter := ⟨11⟩, portable := true,
          marketEligible := true, alphaInterpretation := none }
      , { id := ⟨31⟩, sourceEncounter := ⟨12⟩, portable := true,
          marketEligible := false, alphaInterpretation := none }
      , { id := ⟨32⟩, sourceEncounter := ⟨13⟩, portable := false,
          marketEligible := false, alphaInterpretation := none } ] }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_market_relic_refused : Bool :=
  decide ((validateWire hostileMarketRelic).errorCodes = [7])

def hostileSelfPromotion : RawContent :=
  { fixtureContent with promotionHooks :=
      [{ candidate := .place ⟨50⟩, alphaValue := some ⟨99⟩ }] }

/-- (Pinned `= true` in `ContentContractFixtures`.) -/
def check_hostile_direct_alpha_promotion_refused : Bool :=
  decide ((validateWire hostileSelfPromotion).errorCodes = [8])

theorem fixture_content_is_valid :
    check_fixture_content_is_valid = true := by native_decide

theorem hostile_role_relabel_refused :
    check_hostile_role_relabel_refused = true := by native_decide

theorem hostile_unreachable_extraction_refused :
    check_hostile_unreachable_extraction_refused = true := by native_decide

theorem hostile_route_encounter_asymmetry_refused :
    check_hostile_route_encounter_asymmetry_refused = true := by native_decide

theorem hostile_unwinnable_budget_refused :
    check_hostile_unwinnable_budget_refused = true := by native_decide

theorem hostile_automatic_recovery_refused :
    check_hostile_automatic_recovery_refused = true := by native_decide

theorem hostile_market_relic_refused :
    check_hostile_market_relic_refused = true := by native_decide

theorem hostile_direct_alpha_promotion_refused :
    check_hostile_direct_alpha_promotion_refused = true := by native_decide

#assert_compiled fixture_content_is_valid
#assert_compiled hostile_role_relabel_refused
#assert_compiled hostile_unreachable_extraction_refused
#assert_compiled hostile_route_encounter_asymmetry_refused
#assert_compiled hostile_unwinnable_budget_refused
#assert_compiled hostile_automatic_recovery_refused
#assert_compiled hostile_market_relic_refused
#assert_compiled hostile_direct_alpha_promotion_refused

end Dregg2.Games.PathOfAngels.ContentContract
