/-
# NightWatch campaign admission — the teeth's EVALUATION, out of the crypto archive's build

`NightWatchCampaignAdmission.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its teeth ran eleven `native_decide` pins at elaboration — each one
a Poseidon2 slot commitment and a real SHA-256 over manifest bytes — so any fixture regression
was a hard failure of every Rust proving target in the workspace (the compilation-unit coupling
the stale-fixture outage measured). The teeth's STATEMENTS remain in
`NightWatchCampaignAdmission.lean` as evaluation-free `check_* : Bool` definitions, beside the
fixture world/manifest/member they bite on; THIS module is where they are RUN. It is rooted in
the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ Budget: these pins run Poseidon2 sponges and SHA-256 over the manifest bytes — minutes, not
seconds.

⚠ Named residue: NONE. Every fixture value in the parent is a plain `def`, so no proof is
demanded as data at construction and all eleven pins moved.
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- Well-formed on the wire, but every seat shares one player key, so `Nodup` fails
and `activate?` refuses. -/
def fixtureForgedRoster : NightWatchCampaign.RawConfig :=
  { fixtureRaw with
    roster := fixtureRoster.map fun seat => { seat with playerKey := markDigest 16 } }

def fixtureMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← fixtureValidatedManifest?
  authorizeCampaignConfigForWorld? fixtureWorld manifest

/-- The fixture config round-trips through the exact wire codec the manifest carries.
(Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_fixture_config_round_trips_through_the_wire : Bool :=
  decide (decodeConfig (configJson fixtureRaw) = some fixtureRaw)

/-- The fixture manifest decodes canonically.
(Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_fixture_manifest_decodes_canonically : Bool :=
  fixtureValidatedManifest?.isSome

/-- ⚑ The one that closes the hole: a config the CURATOR published, located inside the
active world's own content root, is admitted.
(Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_the_activated_world_admits_its_own_campaign_config : Bool :=
  fixtureMember?.isSome

def forgedMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest forgedManifest.toJson
  authorizeCampaignConfigForWorld? fixtureWorld manifest

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it : Bool :=
  (NightWatchCampaign.activate? forgedRaw).isSome &&
  (ActivatedContent.decodeManifest forgedManifest.toJson).isSome &&
  !(forgedManifest.matchesWorldB fixtureWorld) &&
  forgedMember?.isNone

/-- The component name is exact.  ⚠ The world here is the one whose `contentRoot` IS
the misnamed manifest's root, so `matchesWorldB` PASSES — first conjunct — and the
refusal is isolated to the name lookup rather than riding on a changed root. -/
def misnamedManifest : ActivatedContent.Manifest :=
  { fixtureManifest with
    components := [{ fixtureComponent with name := "poa.night-watch-campaign.config.v2" }] }

def misnamedWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with
    contentRoot := (ActivatedContent.manifestRoot? misnamedManifest).getD (markDigest 0) }

def misnamedMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest misnamedManifest.toJson
  authorizeCampaignConfigForWorld? misnamedWorld manifest

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_a_component_under_another_name_is_not_this_organs_config : Bool :=
  misnamedManifest.matchesWorldB misnamedWorld &&
  (ActivatedContent.componentByName? misnamedManifest.components CONFIG_COMPONENT).isNone &&
  misnamedMember?.isNone

/-- A world that is structurally fine and names a different content session cannot
consume this manifest, even though the manifest root is unchanged. -/
def crossSessionWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with contentSession := markDigest 77 }

def crossSessionMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← fixtureValidatedManifest?
  authorizeCampaignConfigForWorld? crossSessionWorld manifest

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_a_config_cannot_be_carried_into_another_content_session : Bool :=
  crossSessionMember?.isNone

/-- A config that decodes perfectly can still fail `activate?`, and then there is no
member — the witness never manufactures a `Config`. -/
def forgedRosterComponent : ActivatedContent.Component where
  name := CONFIG_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (configJson fixtureForgedRoster)).getD (markDigest 0)
  bytesUtf8 := configJson fixtureForgedRoster

def forgedRosterManifest : ActivatedContent.Manifest :=
  { fixtureManifest with components := [forgedRosterComponent] }

def forgedRosterWorld : WorldActivation.WorldIdentity :=
  { fixtureWorld with
    contentRoot := (ActivatedContent.manifestRoot? forgedRosterManifest).getD (markDigest 0) }

def forgedRosterMember? : Option WorldScopedCampaignConfigMember := do
  let manifest ← ActivatedContent.decodeManifest forgedRosterManifest.toJson
  authorizeCampaignConfigForWorld? forgedRosterWorld manifest

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_an_invalid_config_in_an_exactly_matching_world_still_yields_no_member : Bool :=
  (ActivatedContent.decodeManifest forgedRosterManifest.toJson).isSome &&
  forgedRosterManifest.matchesWorldB forgedRosterWorld &&
  (NightWatchCampaign.activate? fixtureForgedRoster).isNone &&
  forgedRosterMember?.isNone

def oversizedRulesBytes : String :=
  configJson { fixtureRaw with
    rules := List.replicate (NightWatchCampaign.MAX_RULES + 1) fixtureRule }

def riskAboveTheFaceCountBytes : String :=
  configJson { fixtureRaw with
    rules := [{ fixtureRule with riskThreshold := NightWatchCampaign.HAZARD_FACES + 1 }] }

def resourceAboveBoundBytes : String :=
  configJson { fixtureRaw with
    initialResources := ⟨NightWatchCampaign.MAX_RESOURCE + 1, 10, 10, 10⟩ }

/-- The flag day, made findable: an otherwise byte-canonical current document with the
RETIRED `hazard_cycle` spliced back in refuses, rather than being read with the field
ignored.  `exactKeys` is exact in both directions. -/
def legacyHazardCycleBytes : String :=
  ((configJson fixtureRaw).dropEnd 1).toString ++ ",\"hazard_cycle\":[70,10,55]}"

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_oversized_rule_list_refuses : Bool := (decodeConfig oversizedRulesBytes).isNone

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_a_risk_threshold_above_the_face_count_refuses : Bool :=
  (decodeConfig riskAboveTheFaceCountBytes).isNone

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_initial_resource_above_the_bound_refuses : Bool :=
  (decodeConfig resourceAboveBoundBytes).isNone

/-- (Pinned `= true` in `NightWatchCampaignAdmissionFixtures`.) -/
def check_a_config_carrying_the_retired_hazard_cycle_refuses : Bool :=
  (decodeConfig legacyHazardCycleBytes).isNone

theorem fixture_config_round_trips_through_the_wire :
    check_fixture_config_round_trips_through_the_wire = true := by native_decide

theorem fixture_manifest_decodes_canonically :
    check_fixture_manifest_decodes_canonically = true := by native_decide

theorem the_activated_world_admits_its_own_campaign_config :
    check_the_activated_world_admits_its_own_campaign_config = true := by native_decide

theorem a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it :
    check_a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it = true := by
  native_decide

theorem a_component_under_another_name_is_not_this_organs_config :
    check_a_component_under_another_name_is_not_this_organs_config = true := by native_decide

theorem a_config_cannot_be_carried_into_another_content_session :
    check_a_config_cannot_be_carried_into_another_content_session = true := by native_decide

theorem an_invalid_config_in_an_exactly_matching_world_still_yields_no_member :
    check_an_invalid_config_in_an_exactly_matching_world_still_yields_no_member = true := by
  native_decide

theorem oversized_rule_list_refuses :
    check_oversized_rule_list_refuses = true := by native_decide

theorem a_risk_threshold_above_the_face_count_refuses :
    check_a_risk_threshold_above_the_face_count_refuses = true := by native_decide

theorem initial_resource_above_the_bound_refuses :
    check_initial_resource_above_the_bound_refuses = true := by native_decide

theorem a_config_carrying_the_retired_hazard_cycle_refuses :
    check_a_config_carrying_the_retired_hazard_cycle_refuses = true := by native_decide

#assert_compiled fixture_config_round_trips_through_the_wire
#assert_compiled fixture_manifest_decodes_canonically
#assert_compiled the_activated_world_admits_its_own_campaign_config
#assert_compiled a_free_risk_table_rehashes_the_manifest_and_the_world_refuses_it
#assert_compiled a_component_under_another_name_is_not_this_organs_config
#assert_compiled a_config_cannot_be_carried_into_another_content_session
#assert_compiled an_invalid_config_in_an_exactly_matching_world_still_yields_no_member
#assert_compiled oversized_rule_list_refuses
#assert_compiled a_risk_threshold_above_the_face_count_refuses
#assert_compiled initial_resource_above_the_bound_refuses
#assert_compiled a_config_carrying_the_retired_hazard_cycle_refuses

end Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
