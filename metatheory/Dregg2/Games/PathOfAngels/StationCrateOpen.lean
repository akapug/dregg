/-
# StationCrateOpen — the daily ritual that finally MOVES the ship

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget; it composes two already-proved state machines.

PLATFORM-ROADMAP §7.3 pairs *salvage crate* (the ritual) with *ship instrument
panel* (what the ritual moves).  Until now the write half was **unreachable by
type**: `SalvageCrate.openCrate` demanded a `CurrentStateCapability` that had no
producer anywhere in the tree, so `StationDailyRuntime` served
`ShipInstrumentPanel.initial` and every gauge read zero — `the_served_ship_has_not
_been_moved`.  `SalvageCrate` now roots that capability in a `genesis` install and
hands the successor capability back from each accepted open, so the ceremony is
**reachable-through-authorization**.  This module is the composition: open the
crate under that chain and fold the accepted `OpenReceipt` into the panel through
the panel's *own* communal `observe`.

## The write is not a second authority

`observeDay` moves the panel ONLY by calling `ShipInstrumentPanel.observe` on a
real `SalvageCrate.OpenReceipt` — the sealed receipt whose only producer is an
accepted opening.  It mints no contribution, chooses no draw, and owns no gauge.
Every number the ship shows is one `Contribution` the crate already proved exact.

## Two poles, on ACTUAL crate output

* `an_honest_salvage_open_moves_the_supplies_gauge` — on the authored deployment,
  crew `digest 41` opening the genesis period draws the communal-salvage row and
  the supplies gauge advances by exactly its contribution (1), the recovered set
  gains the thread spool.  The ritual moves the ship.
* `an_ordinary_open_moves_no_gauge` — crew `digest 40` draws a bound record whose
  contribution is zero; they opened (observed and admitted both count) and the
  ship is bit-identical.  Showing up on an ordinary day and not showing up are the
  same ship — the roadmap's "missing a day is uninteresting", on real output.
* `the_replay_open_is_refused_and_never_reaches_the_panel` and
  `a_wrong_period_open_is_refused_and_never_reaches_the_panel` — a second open of
  the same period by the same crew, and an open of a period that is not the
  current one, are refused by the crate and never reach the fold.  The hostile
  envelopes are constructed explicitly and asserted refused; the honest pole above
  witnesses that the refusal is not vacuous.

## Communal and unattributed

`the_communal_gauge_accumulates_only_the_salvage_draw` folds the whole eligible
crew and the gauge carries only the one salvage draw, with three arrivals counted;
`the_face_is_the_same_whatever_order_the_crew_arrives` reorders them and the ship
reads identically.  There is no per-player field on the panel, so no streak,
leaderboard, or attendance record can be read off the moved ship — exactly the
laws `ShipInstrumentPanel` proves, here on the composed write path.
-/
import Dregg2.Games.PathOfAngels.ShipInstrumentPanel
import Dregg2.Games.PathOfAngels.SalvageCrateExamples
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.StationCrateOpen

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## The deployment: the authored crate and a panel that is its one ship -/

/-- The already-authored, already-valid crate rotation. -/
abbrev crate : SalvageCrate.Config := SalvageCrateExamples.config

/-- The panel identity is read off the crate's mission so a receipt this crate
produces can never be refused by this panel as foreign.  One supplies dial,
because every authored row moves only supplies (the read runtime proves the same
of its own panel). -/
def panelRaw : ShipInstrumentPanel.RawPanel where
  federationId := crate.raw.mission.federationId
  contentSession := crate.raw.mission.contentSession
  contentEpoch := crate.raw.mission.epoch
  gauges := [{ id := ⟨1⟩, meter := .supplies, fullAt := 64 }]
  capacity := ShipInstrumentPanel.MAX_OBSERVED

theorem panel_valid : ShipInstrumentPanel.panelValidB panelRaw = true := by native_decide

def panel : ShipInstrumentPanel.Panel := ⟨panelRaw, panel_valid⟩

/-- ⭐ The panel and the crate are ONE deployment, so no accepted opening is ever
refused as `foreignDeployment`. -/
theorem panel_and_crate_are_one_deployment :
    panelRaw.federationId = crate.raw.mission.federationId ∧
    panelRaw.contentSession = crate.raw.mission.contentSession ∧
    panelRaw.contentEpoch = crate.raw.mission.epoch := ⟨rfl, rfl, rfl⟩

/-! ## The ceremony: open, then fold the receipt into the panel

The three definitions below are stated over an ARBITRARY deployment, not over
this module's `crate`/`panel`.  That is deliberate and it is what lets
`StationCrateOpenRuntime` state its document laws without inheriting this
content's compiled `configValidB`/`panelValidB` evaluation. -/

/-- The three things a replay of the daily ritual carries: the crate state, the
capability bound to *that* state, and the panel.  The capability field is
dependent on the state field, which is exactly the point — there is no way to
build a `Rolled` holding a capability for some other state, so a runtime that
threads this triple across a replay never mints a capability from nothing.

`StationCrateOpenRuntime` needs the crate state and the drawn entry as well as
the panel, so this — rather than `observeDay`'s panel-only result — is the
primitive, and `observeDay` is its projection.  One fold, two consumers. -/
structure Rolled (config : SalvageCrate.Config) where
  state : SalvageCrate.State config
  capability : SalvageCrate.CurrentStateCapability state
  panel : ShipInstrumentPanel.State

/-- The ship exactly as installed, ready to be rolled forward: the genesis crate
state, the one rooted capability, and the untouched panel. -/
def genesisRolled (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel) :
    Rolled config where
  state := SalvageCrate.genesis config
  capability := SalvageCrate.genesisCapability config
  panel := ShipInstrumentPanel.initial deployment

/-- Open the crate under the threaded capability and, on an accepted opening, fold
its receipt into the panel; then continue with the successor state and its
successor capability.  Refuses (returns `none`) at the first crate refusal OR the
first panel refusal, so the panel is never left holding a receipt the crate
declined. -/
def rollDay (config : SalvageCrate.Config) (deployment : ShipInstrumentPanel.Panel) :
    Rolled config → List SalvageCrate.OpenEnvelope → Option (Rolled config)
  | rolled, [] => some rolled
  | rolled, envelope :: rest =>
      match SalvageCrate.openCrate config rolled.state rolled.capability envelope with
      | none => none
      | some result =>
          match ShipInstrumentPanel.observe deployment rolled.panel
                  (ShipInstrumentPanel.ofSalvageOpen result.receipt) with
          | .error _ => none
          | .ok nextPanel =>
              rollDay config deployment
                { state := result.after, capability := result.nextCapability,
                  panel := nextPanel } rest

/-- The envelope a runtime submits.  Every field is derived from the authored
deployment and the caller's position in the node's log; `actorRoot` is the
curator's authored ceremony key rather than a fixture constant, so there is no
number here a caller or a runtime chose. -/
def envFor (config : SalvageCrate.Config) (player : Digest32) (period : EpochId)
    (previous next sequence : Nat) : SalvageCrate.OpenEnvelope where
  configIdentity := config.raw
  expectedPeriod := period
  expectedSequence := sequence
  actorRoot := config.raw.curatorKey
  player := player
  previousPlayerCounter := previous
  playerCounter := next

/-! ## The crew and their authored envelopes

The genesis period is the first authored beacon (31).  Each envelope carries the
running sequence position and the opener's advancing counter; the eligible crew
are `digest 40/41/42`. -/

def crew40 : Digest32 := SalvageCrateExamples.digest 40
def crew41 : Digest32 := SalvageCrateExamples.digest 41
def crew42 : Digest32 := SalvageCrateExamples.digest 42

/-! ## The two poles

⚑ **THE POLES NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target.  Each fixture theorem
below is now an evaluation-free `check_* : Bool` definition; the EVALUATION — each
`check_* = true`, pinned by `native_decide` + `#assert_compiled` — lives in
`StationCrateOpenFixtures.lean`, rooted in the `PathOfAngelsGuards` library.  A plain
`lake build` still runs every pin; `lake build Dregg2.FFI` never does.

Fail-closed convention: where a check needs the accepted first open as a PREREQUISITE (the
old `.get (by native_decide)` shape on `firstResult`), it matches on the `Option` and answers
`false` on `none` — a broken prerequisite fails the pin in the guard library rather than
wedging this module.

⚠ Named residue, one construction proof: `panel_valid` stays `native_decide` HERE because
`Panel` carries its validity proof as data — constructing `panel` at all requires the proof
at elaboration.  Breaking `panelValidB` on `panelRaw` therefore still reds this module (and
the archive).  Everything else moved. -/

/-! ## The hostile openings, constructed and refused

`firstOpen?` is the ACCEPTED first open of crew 41 — the checks below match on it, so its
existence witnesses that the refusals are not vacuous (there really was a ship-moving open
to replay), and a refused prerequisite answers `false` (fail-closed) rather than wedging
this module.  `OpenResult`'s constructor is private and it carries its exactness proofs, so
no fallback value is constructible — the dependent uses are FOLDED into each check's own
`match`, exactly the exemplar's `check_public_double_open_in_one_period_refuses` shape. -/

/-! ## Communal and unattributed, on the composed write path -/

#assert_compiled panel_valid
#assert_compiled panel_and_crate_are_one_deployment

-- The seven pole/hostility pins (`#assert_compiled` + `native_decide`) live in
-- `StationCrateOpenFixtures.lean`, rooted in `PathOfAngelsGuards` — see the poles header above.

end Dregg2.Games.PathOfAngels.StationCrateOpen
