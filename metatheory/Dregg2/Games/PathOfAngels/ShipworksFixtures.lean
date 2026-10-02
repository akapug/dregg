/-
# Shipworks — the strategy/hostile-fixture EVALUATION, out of the crypto archive's build

`Shipworks.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its strategy and hostile examples ran twenty-two `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving
target in the workspace (the compilation-unit coupling the stale-fixture outage measured).
The STATEMENTS remain in `Shipworks.lean` as evaluation-free `check_* : Bool` definitions;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  `Shipworks` keeps no `native_decide` residue of its
own — every fixture value is constructed with kernel-checked (`decide`/`norm_num`) proofs.
-/
import Dregg2.Games.PathOfAngels.Shipworks

namespace Dregg2.Games.PathOfAngels.Shipworks

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def atmosphereDispatch : Dispatch := dispatchForFinalizedEpoch ⟨1⟩
def coolantDispatch : Dispatch := dispatchForFinalizedEpoch ⟨2⟩
def rationDispatch : Dispatch := dispatchForFinalizedEpoch ⟨3⟩

def reservePowerLoadout : Loadout := ⟨.busCoupler, .spareCartridge⟩
def atmosphereLoadout : Loadout := ⟨.diagnosticArray, .scrubberMesh⟩
def coolantLoadout : Loadout := ⟨.diagnosticArray, .cryoPatch⟩
def rationLoadout : Loadout := ⟨.diagnosticArray, .cultureCatalyst⟩

def reservePowerPlan : List Action :=
  [.scan, .usePrimary, .useSecondary, .advance, .improvise, .certify]

def atmospherePlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .certify]

def coolantPlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .certify]

def rationPlan : List Action :=
  [.usePrimary, .advance, .useSecondary, .advance, .improvise, .certify]

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_careful_power_completes : Bool :=
  decide ((replay powerDispatch carefulPowerLoadout carefulPowerPlan).map State.status =
    some .complete)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_reserve_power_completes : Bool :=
  decide ((replay powerDispatch reservePowerLoadout reservePowerPlan).map State.status =
    some .complete)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_careful_power_preserves_more_quality : Bool :=
  decide ((replay powerDispatch carefulPowerLoadout carefulPowerPlan).map quality = some 6)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_reserve_power_trades_quality_for_cohesion : Bool :=
  decide ((replay powerDispatch reservePowerLoadout reservePowerPlan).map quality = some 4)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_power_strategies_have_distinct_exact_contributions : Bool :=
  decide ((replay powerDispatch carefulPowerLoadout carefulPowerPlan >>= contributionFor).map
      (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
    some (2, 16, 2, 160)) &&
  decide ((replay powerDispatch reservePowerLoadout reservePowerPlan >>= contributionFor).map
      (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
    some (0, 14, 4, 140))

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_authored_epoch_variant_changes_pressure_exactly : Bool :=
  decide ((replay powerDispatch carefulPowerLoadout carefulPowerPlan).map
      (fun state => (state.fault, quality state)) = some (3, 6)) &&
  decide ((replay (dispatchForFinalizedEpoch ⟨4⟩) carefulPowerLoadout carefulPowerPlan).map
      (fun state => (state.fault, quality state)) = some (4, 5))

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_atmosphere_scrub_completes : Bool :=
  decide ((replay atmosphereDispatch atmosphereLoadout atmospherePlan).map State.status =
    some .complete)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_coolant_repair_completes : Bool :=
  decide ((replay coolantDispatch coolantLoadout coolantPlan).map State.status =
    some .complete)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_ration_synthesis_completes : Bool :=
  decide ((replay rationDispatch rationLoadout rationPlan).map State.status =
    some .complete)

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_three_other_jobs_have_distinct_exact_contributions : Bool :=
  decide ((replay atmosphereDispatch atmosphereLoadout atmospherePlan >>= contributionFor).map
      (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
    some (1, 3, 13, 150)) &&
  decide ((replay coolantDispatch coolantLoadout coolantPlan >>= contributionFor).map
      (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
    some (1, 13, 5, 170)) &&
  decide ((replay rationDispatch rationLoadout rationPlan >>= contributionFor).map
      (fun c => (c.intel.val, c.supplies.val, c.cohesion.val, c.score.val)) =
    some (0, 15, 4, 160))

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_duplicate_tools_refuse : Bool :=
  (initialState powerDispatch ⟨.busCoupler, .busCoupler⟩).isNone

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_early_certification_refuses : Bool :=
  (initialState powerDispatch carefulPowerLoadout >>= fun state => step state .certify).isNone

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_duplicate_scan_refuses : Bool :=
  (replay powerDispatch carefulPowerLoadout [.scan, .scan]).isNone

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_duplicate_tool_use_refuses : Bool :=
  (replay powerDispatch carefulPowerLoadout [.usePrimary, .usePrimary]).isNone

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_reserve_exhaustion_refuses : Bool :=
  (replay powerDispatch carefulPowerLoadout [.stabilize, .stabilize, .stabilize]).isNone

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_second_spare_cartridge_use_refuses : Bool :=
  (replay powerDispatch reservePowerLoadout [.useSecondary, .useSecondary]).isNone

def nearFullSpareState : State := {
  dispatch := powerDispatch
  loadout := ⟨.spareCartridge, .busCoupler⟩
  status := .active
  turn := 0
  output := 0
  fault := 2
  reserves := 3
  scanned := false
  primaryUsed := false
  secondaryUsed := false
}

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_near_full_spare_state_is_valid : Bool := nearFullSpareState.Valid

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_over_capacity_spare_cartridge_refuses : Bool :=
  (step nearFullSpareState .usePrimary).isNone

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_first_power_claim_succeeds : Bool :=
  (settle CareRecord.empty (powerSubmission 20_000)).isSome

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_power_claim_ignores_browser_calendar : Bool :=
  decide (settle CareRecord.empty (powerSubmission 0) =
    settle CareRecord.empty (powerSubmission 4_294_967_295))

def replayedPowerSubmission : Submission := {
  powerSubmission 20_001 with
  claimCounter := ⟨2, by decide⟩
}

/-- (Pinned `= true` in `ShipworksFixtures`.) -/
def check_same_epoch_second_claim_refuses : Bool :=
  ((settle CareRecord.empty (powerSubmission 20_000)).bind
    (fun first => settle first.nextRecord replayedPowerSubmission)).isNone

def gapRecord : CareRecord := {
  lastClaimedEpoch := some ⟨0⟩
  lastCounter := ⟨1, by decide⟩
}

def noHistoryAtCounterOne : CareRecord := {
  lastClaimedEpoch := none
  lastCounter := ⟨1, by decide⟩
}

def epochFourSubmission : Submission := {
  dispatch := dispatchForFinalizedEpoch ⟨4⟩
  presentedMissionEpoch := ⟨4⟩
  browserUtcDay := 20_004
  claimCounter := ⟨2, by decide⟩
  loadout := carefulPowerLoadout
  actions := carefulPowerPlan
}

/-- Four missed rotations do not lower the reward.  Both records have the same
counter; one records an old visit and one records no earlier visit at all.
(Pinned `= true` in `ShipworksFixtures`.) -/
def check_missed_epochs_do_not_change_reward : Bool :=
  decide ((settle gapRecord epochFourSubmission).map Settlement.contribution =
    (settle noHistoryAtCounterOne epochFourSubmission).map Settlement.contribution)

theorem careful_power_completes :
    check_careful_power_completes = true := by native_decide

theorem reserve_power_completes :
    check_reserve_power_completes = true := by native_decide

theorem careful_power_preserves_more_quality :
    check_careful_power_preserves_more_quality = true := by native_decide

theorem reserve_power_trades_quality_for_cohesion :
    check_reserve_power_trades_quality_for_cohesion = true := by native_decide

theorem power_strategies_have_distinct_exact_contributions :
    check_power_strategies_have_distinct_exact_contributions = true := by native_decide

theorem authored_epoch_variant_changes_pressure_exactly :
    check_authored_epoch_variant_changes_pressure_exactly = true := by native_decide

theorem atmosphere_scrub_completes :
    check_atmosphere_scrub_completes = true := by native_decide

theorem coolant_repair_completes :
    check_coolant_repair_completes = true := by native_decide

theorem ration_synthesis_completes :
    check_ration_synthesis_completes = true := by native_decide

theorem three_other_jobs_have_distinct_exact_contributions :
    check_three_other_jobs_have_distinct_exact_contributions = true := by native_decide

theorem duplicate_tools_refuse :
    check_duplicate_tools_refuse = true := by native_decide

theorem early_certification_refuses :
    check_early_certification_refuses = true := by native_decide

theorem duplicate_scan_refuses :
    check_duplicate_scan_refuses = true := by native_decide

theorem duplicate_tool_use_refuses :
    check_duplicate_tool_use_refuses = true := by native_decide

theorem reserve_exhaustion_refuses :
    check_reserve_exhaustion_refuses = true := by native_decide

theorem second_spare_cartridge_use_refuses :
    check_second_spare_cartridge_use_refuses = true := by native_decide

theorem near_full_spare_state_is_valid :
    check_near_full_spare_state_is_valid = true := by native_decide

theorem over_capacity_spare_cartridge_refuses :
    check_over_capacity_spare_cartridge_refuses = true := by native_decide

theorem first_power_claim_succeeds :
    check_first_power_claim_succeeds = true := by native_decide

theorem power_claim_ignores_browser_calendar :
    check_power_claim_ignores_browser_calendar = true := by native_decide

theorem same_epoch_second_claim_refuses :
    check_same_epoch_second_claim_refuses = true := by native_decide

theorem missed_epochs_do_not_change_reward :
    check_missed_epochs_do_not_change_reward = true := by native_decide

#assert_compiled careful_power_completes
#assert_compiled reserve_power_completes
#assert_compiled careful_power_preserves_more_quality
#assert_compiled reserve_power_trades_quality_for_cohesion
#assert_compiled power_strategies_have_distinct_exact_contributions
#assert_compiled authored_epoch_variant_changes_pressure_exactly
#assert_compiled atmosphere_scrub_completes
#assert_compiled coolant_repair_completes
#assert_compiled ration_synthesis_completes
#assert_compiled three_other_jobs_have_distinct_exact_contributions
#assert_compiled duplicate_tools_refuse
#assert_compiled early_certification_refuses
#assert_compiled duplicate_scan_refuses
#assert_compiled duplicate_tool_use_refuses
#assert_compiled reserve_exhaustion_refuses
#assert_compiled second_spare_cartridge_use_refuses
#assert_compiled near_full_spare_state_is_valid
#assert_compiled over_capacity_spare_cartridge_refuses
#assert_compiled first_power_claim_succeeds
#assert_compiled power_claim_ignores_browser_calendar
#assert_compiled same_epoch_second_claim_refuses
#assert_compiled missed_epochs_do_not_change_reward

end Dregg2.Games.PathOfAngels.Shipworks
