/-
# Station Crate Open — the two-pole EVALUATION, out of the crypto archive's build

`StationCrateOpen.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its poles and hostile openings ran seven `native_decide` pins at
elaboration — so any game-fixture regression was a hard failure of every Rust proving target
in the workspace.  The STATEMENTS remain in `StationCrateOpen.lean` as evaluation-free
`check_* : Bool` definitions, beside the private accepted-open prerequisite (`firstOpen?`)
they must see; THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards`
library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
prerequisite open refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ One construction proof did NOT move (`panel_valid`) — `Panel` carries its validity proof
as data, so it must elaborate where `panel` is built.  It is the named residue; the poles
header in `StationCrateOpen.lean` records it.
-/
import Dregg2.Games.PathOfAngels.StationCrateOpen

namespace Dregg2.Games.PathOfAngels.StationCrateOpen

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The panel-only projection of `rollDay`, which is what the two poles below
read.  Refusal is preserved exactly: `none` in, `none` out. -/
def observeDay (state : SalvageCrate.State crate)
    (capability : SalvageCrate.CurrentStateCapability state)
    (panelState : ShipInstrumentPanel.State)
    (envelopes : List SalvageCrate.OpenEnvelope) : Option ShipInstrumentPanel.State :=
  (rollDay crate panel ⟨state, capability, panelState⟩ envelopes).map Rolled.panel

/-- One open from the installed ship, the common shape below. -/
def observeOne (envelope : SalvageCrate.OpenEnvelope) : Option ShipInstrumentPanel.State :=
  observeDay (SalvageCrate.genesis crate) (SalvageCrate.genesisCapability crate)
    (ShipInstrumentPanel.initial panel) [envelope]

abbrev envForCrate : Digest32 → EpochId → Nat → Nat → Nat → SalvageCrate.OpenEnvelope :=
  envFor crate

/-- Crew 41, opening the genesis period from the installed ship: draws the
communal salvage. -/
def env41 : SalvageCrate.OpenEnvelope := envForCrate crew41 ⟨31⟩ 0 1 0

/-- Crew 40, opening the genesis period: draws a bound record (zero contribution). -/
def env40 : SalvageCrate.OpenEnvelope := envForCrate crew40 ⟨31⟩ 0 1 0

/-- ⭐ THE RITUAL MOVES THE SHIP.  The supplies gauge advances by exactly the drawn
contribution (1), the recovered set gains one kind, and the open is counted —
observed and admitted both 1.  A refusal is `none`, so this cannot be met by
declining. (Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_an_honest_salvage_open_moves_the_supplies_gauge : Bool :=
  decide ((observeOne env41).map (fun s =>
      (s.face panel, s.recovered.card, s.observed.card, s.admitted)) =
    some ([{ gauge := ⟨1⟩, meter := .supplies, exactTotal := 1, fullAt := 64,
             shown := 1, atFull := false }], 1, 1, 1))

/-- ⭐ AN ORDINARY DAY MOVES NO GAUGE, on real crate output.  Crew 40 opened — it
is observed and admitted — and the ship is bit-identical to the installed one:
supplies zero, no salvage recovered.  Missing a day is uninteresting.
(Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_an_ordinary_open_moves_no_gauge : Bool :=
  decide ((observeOne env40).map (fun s =>
      (s.face panel, s.recovered.card, s.observed.card, s.admitted)) =
    some ([{ gauge := ⟨1⟩, meter := .supplies, exactTotal := 0, fullAt := 64,
             shown := 0, atFull := false }], 0, 1, 1))

private def firstOpen? : Option (SalvageCrate.OpenResult crate env41) :=
  SalvageCrate.openCrate crate (SalvageCrate.genesis crate)
    (SalvageCrate.genesisCapability crate) env41

/-- The mutation: the SAME crew member opening the SAME period again, on the
successor state, with the correctly advanced counter — so the only check left to
refuse it is the append-only consumed-period guard. -/
def replayEnv41 : SalvageCrate.OpenEnvelope := envForCrate crew41 ⟨31⟩ 1 2 1

/-- The mutation is present: crew 41 already consumed the genesis period.  Matches on the
accepted first open; `none` answers `false` (fail-closed).  This used to cite the accepted
result's own `consumes_exact_period` proof; the pin now evaluates the same membership on the
same accepted successor state. (Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_the_first_period_is_consumed_by_crew_41 : Bool :=
  match firstOpen? with
  | some result =>
      decide (SalvageCrate.openKey crate ⟨31⟩ crew41 ∈ result.after.consumed)
  | none => false

/-- ⭐ REPLAY REFUSED, and it never reaches the panel.  Holding a perfectly valid
successor capability does not let crew 41 open the genesis period twice.  Matches on the
accepted first open; `none` answers `false` (fail-closed).
(Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_the_replay_open_is_refused_and_never_reaches_the_panel : Bool :=
  match firstOpen? with
  | some result =>
      (observeDay result.after result.nextCapability
        (ShipInstrumentPanel.initial panel) [replayEnv41]).isNone
  | none => false

/-- The mutation: crew 41 asking for period 32 while the ship is still at the
genesis period 31. -/
def wrongPeriodEnv41 : SalvageCrate.OpenEnvelope := envForCrate crew41 ⟨32⟩ 0 1 0

/-- ⭐ WRONG-PERIOD REFUSED, and it never reaches the panel.  A capability for the
installed state authorizes opening the CURRENT finalized period, not a future one.
The honest pole above shows this same crew, same genesis, DOES open period 31.
(Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_a_wrong_period_open_is_refused_and_never_reaches_the_panel : Bool :=
  (observeOne wrongPeriodEnv41).isNone

def env40Seq1 : SalvageCrate.OpenEnvelope := envForCrate crew40 ⟨31⟩ 0 1 1
def env42Seq2 : SalvageCrate.OpenEnvelope := envForCrate crew42 ⟨31⟩ 0 1 2

/-- The whole eligible crew opening the genesis period, in arrival order 41,40,42. -/
def theWholeCrewOpens : Option ShipInstrumentPanel.State :=
  observeDay (SalvageCrate.genesis crate) (SalvageCrate.genesisCapability crate)
    (ShipInstrumentPanel.initial panel) [env41, env40Seq1, env42Seq2]

/-- ⭐ The communal gauge carries only the one salvage draw though THREE crew
opened: supplies 1, one recovered kind, three observed, three admitted.  The panel
counts arrivals well enough to keep them apart (observed = 3) and never well enough
to rank them (the face is one supplies number).
(Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_the_communal_gauge_accumulates_only_the_salvage_draw : Bool :=
  decide (theWholeCrewOpens.map (fun s =>
      (s.face panel, s.recovered.card, s.observed.card, s.admitted)) =
    some ([{ gauge := ⟨1⟩, meter := .supplies, exactTotal := 1, fullAt := 64,
             shown := 1, atFull := false }], 1, 3, 3))

def env42Seq0 : SalvageCrate.OpenEnvelope := envForCrate crew42 ⟨31⟩ 0 1 0
def env41Seq2 : SalvageCrate.OpenEnvelope := envForCrate crew41 ⟨31⟩ 0 1 2

/-- The same crew, arriving in a different order 42,40,41. -/
def theWholeCrewOpensReordered : Option ShipInstrumentPanel.State :=
  observeDay (SalvageCrate.genesis crate) (SalvageCrate.genesisCapability crate)
    (ShipInstrumentPanel.initial panel) [env42Seq0, env40Seq1, env41Seq2]

/-- ⭐ Whoever reached the reclamation desk first, the ship reads the same — the
communal face does not depend on arrival order, on the composed write path.
(Pinned `= true` in `StationCrateOpenFixtures`.) -/
def check_the_face_is_the_same_whatever_order_the_crew_arrives : Bool :=
  decide (theWholeCrewOpens.map (fun s => s.face panel) =
    theWholeCrewOpensReordered.map (fun s => s.face panel))

theorem an_honest_salvage_open_moves_the_supplies_gauge :
    check_an_honest_salvage_open_moves_the_supplies_gauge = true := by native_decide

theorem an_ordinary_open_moves_no_gauge :
    check_an_ordinary_open_moves_no_gauge = true := by native_decide

theorem the_first_period_is_consumed_by_crew_41 :
    check_the_first_period_is_consumed_by_crew_41 = true := by native_decide

theorem the_replay_open_is_refused_and_never_reaches_the_panel :
    check_the_replay_open_is_refused_and_never_reaches_the_panel = true := by native_decide

theorem a_wrong_period_open_is_refused_and_never_reaches_the_panel :
    check_a_wrong_period_open_is_refused_and_never_reaches_the_panel = true := by native_decide

theorem the_communal_gauge_accumulates_only_the_salvage_draw :
    check_the_communal_gauge_accumulates_only_the_salvage_draw = true := by native_decide

theorem the_face_is_the_same_whatever_order_the_crew_arrives :
    check_the_face_is_the_same_whatever_order_the_crew_arrives = true := by native_decide

#assert_compiled an_honest_salvage_open_moves_the_supplies_gauge
#assert_compiled an_ordinary_open_moves_no_gauge
#assert_compiled the_first_period_is_consumed_by_crew_41
#assert_compiled the_replay_open_is_refused_and_never_reaches_the_panel
#assert_compiled a_wrong_period_open_is_refused_and_never_reaches_the_panel
#assert_compiled the_communal_gauge_accumulates_only_the_salvage_draw
#assert_compiled the_face_is_the_same_whatever_order_the_crew_arrives

end Dregg2.Games.PathOfAngels.StationCrateOpen
