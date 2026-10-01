/-
# Station Crate Open Runtime — the wire-fixture EVALUATION, out of the crypto archive's build

`StationCrateOpenRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root; `dregg_poa_crate_open` is exported from it), and until 2026-08-08 its poles, loop and
hostile-wire fixtures ran twenty-two `native_decide` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace.
The STATEMENTS remain in `StationCrateOpenRuntime.lean` as evaluation-free `check_* : Bool`
definitions; THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards`
library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  `StationCrateOpenRuntime` keeps no `native_decide`
residue of its own — its deployment is `StationCrateOpen`'s `crate`/`panel`, cited by name.
-/
import Dregg2.Games.PathOfAngels.StationCrateOpenRuntime

namespace Dregg2.Games.PathOfAngels.StationCrateOpenRuntime

set_option autoImplicit false
open Lean (Json)
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def crew40 : Digest32 := StationCrateOpen.crew40
def crew42 : Digest32 := StationCrateOpen.crew42

/-- Not on the curator's roster: `SalvageCrateExamples.raw.eligiblePlayers` is
`{digest 40, digest 41, digest 42}`. -/
def stowaway : Digest32 := SalvageCrateExamples.digest 77

/-- The replay of that one-row log really did reach an accepted state that
consumed period 31 for crew 41 — so the refusal below is a replay guard firing,
not a log that failed to parse. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_logged_open_really_consumed_the_installed_period : Bool :=
  decide (((replayOver crate panel (secondOpen crew41).history).map
    (fun rolled =>
      decide (SalvageCrate.openKey crate ⟨INSTALLED_PERIOD⟩ crew41 ∈ rolled.state.consumed)))
    = some true)

/-- ⭐ THE RITUAL MOVES THE SHIP, THROUGH THE WIRE.  Crew 41 opens the installed
period from an empty log: the document is `opened`, the drawn row is the communal
salvage (loot id 13, one supply), and the published panel reads supplies 1 with
one recovered kind, one observed receipt and one admitted open.  A refusal is a
`.refused` verdict, so this cannot be met by declining.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_an_honest_crate_open_publishes_the_moved_ship : Bool :=
  decide ((openFor (firstOpen crew41)).period = some INSTALLED_PERIOD) &&
  decide ((openFor (firstOpen crew41)).verdict =
    .opened { id := 13, prize := "communal-salvage:55", supplies := 1 }
      { gauges := [{ gauge := 1, meter := "supplies", exactTotal := 1, fullAt := 64,
                     shown := 1, atFull := false }],
        recoveredKinds := 1, observed := 1, admitted := 1 })

/-- ⭐ AND THE SECOND OPEN OF THE SAME PERIOD IS REFUSED, with no gauge.  The
only difference from the pole above is the one log row, and the refusal names the
append-only guard that fired.  Together these two are
`the_replay_guard_is_exactly_as_strong_as_the_node_log`: the node's log is the
whole replay authority, and a node that does not append re-opens the crate.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_a_second_open_of_the_installed_period_is_refused : Bool :=
  decide ((openFor (secondOpen crew41)).period = some INSTALLED_PERIOD) &&
  decide ((openFor (secondOpen crew41)).verdict = .refused .alreadyOpenedThisPeriod)

/-- ⭐ The pair, as one statement, because the pair is the claim.  Same crew key,
same period, same deployment: ACCEPTED against an empty log and REFUSED against a
log that records the earlier open. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_replay_guard_is_exactly_as_strong_as_the_node_log : Bool :=
  (openFor (firstOpen crew41)).verdict.openedB &&
  !(openFor (secondOpen crew41)).verdict.openedB

/-- ⭐ THE READ SERVES THE SHIP THE WRITE PUBLISHED, as one equation between two
whole panels.  Left: the communal fields of the document `/panel` serves for the
log the node now holds.  Right: the panel the accepted open published.  Bit for
bit, one value.

This is red if either half stops folding, if the two folds diverge, or if the
read starts inventing a reading — and it is `Option`-valued on both sides, so it
cannot be satisfied by both of them refusing.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_station_read_serves_the_ship_this_write_published : Bool :=
  decide ((StationDailyRuntime.readFor
      { crew := none, history := (secondOpen crew41).history }).map
    (fun reply =>
      ({ gauges := reply.gauges, recoveredKinds := reply.recoveredKinds,
         observed := reply.observed, admitted := reply.admitted } : PanelWire)) =
    (openFor (firstOpen crew41)).verdict.panelWire?)

/-- ⚠ And it is not vacuous on either side: the write really published a panel
and the read really served a document.  Without this, two `none`s would satisfy
the equation above and the loop would be "closed" by both ends going dark.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_neither_side_of_the_loop_is_a_refusal : Bool :=
  ((openFor (firstOpen crew41)).verdict.panelWire?).isSome &&
  (StationDailyRuntime.readFor
    { crew := none, history := (secondOpen crew41).history }).isSome

/-- An ordinary day through the wire: crew 40 draws a bound record, is `opened`
and admitted, and every gauge reads zero.  Showing up on an ordinary day and not
showing up are the same ship — the roadmap's "missing a day is uninteresting", on
the transport. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_an_ordinary_open_publishes_an_unmoved_ship : Bool :=
  decide ((openFor (firstOpen crew40)).verdict =
    .opened { id := 12, prize := "record:8", supplies := 0 }
      { gauges := [{ gauge := 1, meter := "supplies", exactTotal := 0, fullAt := 64,
                     shown := 0, atFull := false }],
        recoveredKinds := 0, observed := 1, admitted := 1 })

/-- A crew member who is not on the curator's roster is refused by name.  The
honest pole above shows the same empty log DOES admit an eligible crew member, so
this is the roster refusing and not the transport failing.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_an_ineligible_crew_key_is_refused : Bool :=
  decide ((openFor (firstOpen stowaway)).verdict = .refused .ineligibleCrew)

/-- A log row that names a period the crate is not at is refused, and the whole
request with it: the reply carries `period: null` because there is no crate state
to read one off.  A row is never silently re-dated to the current period. -/
def logFromAnotherPeriod : Request :=
  { opener := crew42, history := [{ player := crew41, period := 32 }] }

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_a_log_row_from_another_period_refuses : Bool :=
  decide ((openFor logFromAnotherPeriod).period = none) &&
  decide ((openFor logFromAnotherPeriod).verdict = .refused .historyRefused)

/-- A log row naming a crew key the curator never enrolled is refused the same
way: the log is not one this crate could have produced. -/
def logWithAStowaway : Request :=
  { opener := crew41, history := [{ player := stowaway, period := INSTALLED_PERIOD }] }

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_a_log_row_naming_a_stowaway_refuses : Bool :=
  decide ((openFor logWithAStowaway).verdict = .refused .historyRefused)

/-- ⭐ The communal ship accumulates across the whole crew, and the panel counts
arrivals well enough to keep them apart and never well enough to rank them: after
crew 41 and crew 40 are in the log, crew 42 opening publishes supplies 1 (only
the one salvage draw), one recovered kind, and THREE observed receipts. -/
def theThirdCrewMember : Request :=
  { opener := crew42,
    history := [{ player := crew41, period := INSTALLED_PERIOD },
                { player := crew40, period := INSTALLED_PERIOD }] }

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_published_ship_accumulates_the_whole_crew : Bool :=
  decide ((openFor theThirdCrewMember).verdict =
    .opened { id := 10, prize := "warm-air", supplies := 0 }
      { gauges := [{ gauge := 1, meter := "supplies", exactTotal := 1, fullAt := 64,
                     shown := 1, atFull := false }],
        recoveredKinds := 1, observed := 3, admitted := 3 })

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_first_open_request_round_trips : Bool :=
  decide (decodeRequest (firstOpen crew41).toJson = some (firstOpen crew41))

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_second_open_request_round_trips : Bool :=
  decide (decodeRequest (secondOpen crew41).toJson = some (secondOpen crew41))

/-- ⭐ The export really emits both documents, and they are DIFFERENT bytes: the
move and the refusal are distinguishable on the wire.  A refusal is `""`, so
neither half can be satisfied by declining.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_export_emits_a_move_and_a_refusal : Bool :=
  decide (crateOpenFFI (firstOpen crew41).toJson ≠ "") &&
  decide (crateOpenFFI (secondOpen crew41).toJson ≠ "") &&
  decide (crateOpenFFI (firstOpen crew41).toJson ≠ crateOpenFFI (secondOpen crew41).toJson)

/-- An extra field — the shape an attempt to smuggle a period, a counter or a
contribution would take. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_unknown_field_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[],\"period\":31}") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_transposed_keys_refuse : Bool :=
  decide (crateOpenFFI
    ("{\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"format\":\"POA-CRATE-OPEN-1\",\"history\":[]}") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_wrong_format_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-OUT-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[]}") = "")

/-- A log row carrying its own counter — the field this module DERIVES — is not a
row this wire has a spelling for. (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_row_with_a_counter_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[{\"player\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"period\":31,\"counter\":0}]}") = "")

/-- `digest 41` spells as `29…`, which has no letters to case, so the mutation
would be a no-op on it.  `digest 77` spells as `4d…` and really does change.
(Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_the_uppercase_mutation_is_not_a_no_op : Bool :=
  decide ((Emit.bytes32Hex stowaway).toUpper ≠ Emit.bytes32Hex stowaway)

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_uppercase_digest_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++
      (Emit.bytes32Hex stowaway).toUpper ++ "\",\"history\":[]}") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_trailing_byte_refuses : Bool :=
  decide (crateOpenFFI
    ("{\"format\":\"POA-CRATE-OPEN-1\",\"opener\":\"" ++ Emit.bytes32Hex crew41 ++
      "\",\"history\":[]} ") = "")

/-- (Pinned `= true` in `StationCrateOpenRuntimeFixtures`.) -/
def check_hostile_empty_wire_refuses : Bool :=
  decide (crateOpenFFI "" = "")

theorem the_logged_open_really_consumed_the_installed_period :
    check_the_logged_open_really_consumed_the_installed_period = true := by native_decide

theorem an_honest_crate_open_publishes_the_moved_ship :
    check_an_honest_crate_open_publishes_the_moved_ship = true := by native_decide

theorem a_second_open_of_the_installed_period_is_refused :
    check_a_second_open_of_the_installed_period_is_refused = true := by native_decide

theorem the_replay_guard_is_exactly_as_strong_as_the_node_log :
    check_the_replay_guard_is_exactly_as_strong_as_the_node_log = true := by native_decide

theorem the_station_read_serves_the_ship_this_write_published :
    check_the_station_read_serves_the_ship_this_write_published = true := by native_decide

theorem neither_side_of_the_loop_is_a_refusal :
    check_neither_side_of_the_loop_is_a_refusal = true := by native_decide

theorem an_ordinary_open_publishes_an_unmoved_ship :
    check_an_ordinary_open_publishes_an_unmoved_ship = true := by native_decide

theorem an_ineligible_crew_key_is_refused :
    check_an_ineligible_crew_key_is_refused = true := by native_decide

theorem a_log_row_from_another_period_refuses :
    check_a_log_row_from_another_period_refuses = true := by native_decide

theorem a_log_row_naming_a_stowaway_refuses :
    check_a_log_row_naming_a_stowaway_refuses = true := by native_decide

theorem the_published_ship_accumulates_the_whole_crew :
    check_the_published_ship_accumulates_the_whole_crew = true := by native_decide

theorem first_open_request_round_trips :
    check_first_open_request_round_trips = true := by native_decide

theorem second_open_request_round_trips :
    check_second_open_request_round_trips = true := by native_decide

theorem the_export_emits_a_move_and_a_refusal :
    check_the_export_emits_a_move_and_a_refusal = true := by native_decide

theorem hostile_unknown_field_refuses :
    check_hostile_unknown_field_refuses = true := by native_decide

theorem hostile_transposed_keys_refuse :
    check_hostile_transposed_keys_refuse = true := by native_decide

theorem hostile_wrong_format_refuses :
    check_hostile_wrong_format_refuses = true := by native_decide

theorem hostile_row_with_a_counter_refuses :
    check_hostile_row_with_a_counter_refuses = true := by native_decide

theorem the_uppercase_mutation_is_not_a_no_op :
    check_the_uppercase_mutation_is_not_a_no_op = true := by native_decide

theorem hostile_uppercase_digest_refuses :
    check_hostile_uppercase_digest_refuses = true := by native_decide

theorem hostile_trailing_byte_refuses :
    check_hostile_trailing_byte_refuses = true := by native_decide

theorem hostile_empty_wire_refuses :
    check_hostile_empty_wire_refuses = true := by native_decide

#assert_compiled the_logged_open_really_consumed_the_installed_period
#assert_compiled an_honest_crate_open_publishes_the_moved_ship
#assert_compiled a_second_open_of_the_installed_period_is_refused
#assert_compiled the_replay_guard_is_exactly_as_strong_as_the_node_log
#assert_compiled the_station_read_serves_the_ship_this_write_published
#assert_compiled neither_side_of_the_loop_is_a_refusal
#assert_compiled an_ordinary_open_publishes_an_unmoved_ship
#assert_compiled an_ineligible_crew_key_is_refused
#assert_compiled a_log_row_from_another_period_refuses
#assert_compiled a_log_row_naming_a_stowaway_refuses
#assert_compiled the_published_ship_accumulates_the_whole_crew
#assert_compiled first_open_request_round_trips
#assert_compiled second_open_request_round_trips
#assert_compiled the_export_emits_a_move_and_a_refusal
#assert_compiled hostile_unknown_field_refuses
#assert_compiled hostile_transposed_keys_refuse
#assert_compiled hostile_wrong_format_refuses
#assert_compiled hostile_row_with_a_counter_refuses
#assert_compiled the_uppercase_mutation_is_not_a_no_op
#assert_compiled hostile_uppercase_digest_refuses
#assert_compiled hostile_trailing_byte_refuses
#assert_compiled hostile_empty_wire_refuses

end Dregg2.Games.PathOfAngels.StationCrateOpenRuntime
