/-
# Station Daily Runtime — the wire-fixture EVALUATION, out of the crypto archive's build

`StationDailyRuntime.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root; `dregg_poa_station_daily_read` is exported from it), and until 2026-08-08 its gate,
round-trip and hostile-wire fixtures ran sixteen `native_decide` pins at elaboration — so
any game-fixture regression was a hard failure of every Rust proving target in the
workspace.  The STATEMENTS remain in `StationDailyRuntime.lean` as evaluation-free
`check_* : Bool` definitions; THIS module is where they are RUN.  It is rooted in the
`PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  `StationDailyRuntime` keeps no `native_decide`
residue of its own — its panel proof is `StationCrateOpen.panel_valid`, cited by name.
-/
import Dregg2.Games.PathOfAngels.StationDailyRuntime

namespace Dregg2.Games.PathOfAngels.StationDailyRuntime

set_option autoImplicit false
open Lean (Json)
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- ⭐ Every authored row leaves four of the five meters at zero, so the panel
below authors exactly one dial.  A second dial would be one that provably cannot
move — this fact is the reason there is not one.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_authored_table_moves_only_supplies : Bool :=
  stationCrate.raw.table.all (fun entry =>
    decide (entry.contribution.intel = 0) &&
    decide (entry.contribution.cohesion = 0) &&
    decide (entry.contribution.influence = 0) &&
    decide (entry.contribution.score = 0))

abbrev crewWireOf : Digest32 → CrewWire := crewWireOver stationCrate

/-- The communal fields a reader takes off the served document for a given log —
hoisted so the gate check below has no `let` inside its `decide`. -/
private def servedSummaryFor (history : List HistoryRow) :
    Option (List GaugeWire × Nat × Nat × Nat) :=
  (readFor { crew := none, history }).map
    (fun reply => (reply.gauges, reply.recoveredKinds, reply.observed, reply.admitted))

/-- ⭐ THE SERVED SHIP MOVES WHEN THE LOG RECORDS AN OPENING.  Same deployment,
same anonymous request, one row of difference in the node's durable log: the
empty log serves one dial at zero with nothing observed or admitted, and the
one-row log serves supplies 1, one recovered kind, one observation and one
admission.

This is the assertion the retired one claimed to be.  Delete the fold — make
`servedStateOver` ignore its history and answer `ShipInstrumentPanel.initial` —
and the second half goes red immediately, because the two halves would then be
the same document. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_served_ship_moves_when_the_log_records_an_opening : Bool :=
  decide (servedSummaryFor [] =
    some ([{ gauge := 1, meter := "supplies", exactTotal := 0, fullAt := 64,
             shown := 0, atFull := false }], 0, 0, 0)) &&
  decide (servedSummaryFor theLogAfterOneOpen =
    some ([{ gauge := 1, meter := "supplies", exactTotal := 1, fullAt := 64,
             shown := 1, atFull := false }], 1, 1, 1))

/-- ⭐ And the two really are DIFFERENT DOCUMENTS on the wire, byte for byte, so
the move is visible to a reader who parses nothing.  A refusal is `""`, so this
cannot be satisfied by declining either one.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_two_logs_serve_different_documents : Bool :=
  decide (stationDailyReadFFI { crew := none, history := [] : Request }.toJson ≠ "") &&
  decide (stationDailyReadFFI
    { crew := none, history := theLogAfterOneOpen : Request }.toJson ≠ "") &&
  decide (stationDailyReadFFI { crew := none, history := [] : Request }.toJson ≠
    stationDailyReadFFI { crew := none, history := theLogAfterOneOpen : Request }.toJson)

/-- ⭐ A log that is not one this crate could have produced is REFUSED, and the
honest pole above shows the same wire shape does serve a document — so this is
the replay guard firing rather than the transport failing.  `period 32` is not
the period the crate is at, and a row is never silently re-dated.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_a_log_row_from_another_period_is_refused : Bool :=
  decide (stationDailyReadFFI
    { crew := none,
      history := [{ player := StationCrateOpen.crew41, period := 32 }] : Request }.toJson = "") &&
  decide (stationDailyReadFFI
    { crew := none,
      history := [{ player := SalvageCrateExamples.digest 77,
                    period := 31 }] : Request }.toJson = "")

def anonymousRequest : Request := { crew := none, history := [] }

def officerRequest : Request := { crew := some SalvageCrateExamples.officer, history := [] }

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_anonymous_request_round_trips : Bool :=
  decide (decodeRequest anonymousRequest.toJson = some anonymousRequest)

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_officer_request_round_trips : Bool :=
  decide (decodeRequest officerRequest.toJson = some officerRequest)

/-- The export really emits a document for both spellings; a refusal is `""`, so
this cannot be satisfied by declining. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_both_requests_are_served : Bool :=
  decide (stationDailyReadFFI anonymousRequest.toJson ≠ "") &&
  decide (stationDailyReadFFI officerRequest.toJson ≠ "")

/-- The authored officer is on the curator's roster and their whole rotation is
served: three authored periods, every one of them with a drawn row.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_officer_is_eligible_and_draws_every_authored_period : Bool :=
  (crewWireOf SalvageCrateExamples.officer).eligible &&
  decide ((crewWireOf SalvageCrateExamples.officer).rotation.length =
    stationCrate.raw.beacons.length) &&
  (crewWireOf SalvageCrateExamples.officer).rotation.all
    (fun period => period.entry.isSome)

/-- An extra field — the shape an attempt to smuggle a streak or an attendance
count would take. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_unknown_field_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"history\":[],\"streak\":3}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_transposed_keys_refuse : Bool :=
  decide (stationDailyReadFFI
    "{\"crew\":null,\"format\":\"POA-STATION-DAILY-1\",\"history\":[]}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_wrong_format_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-OUT-1\",\"crew\":null,\"history\":[]}" = "")

/-- `false` is not a spelling of "absent". (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_boolean_crew_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":false,\"history\":[]}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_short_digest_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":\"00\",\"history\":[]}" = "")

/-- (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_trailing_byte_refuses : Bool :=
  decide (stationDailyReadFFI
    "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"history\":[]} " = "")

/-- ⚠ THE OLD REQUEST SHAPE REFUSES TO LOAD.  `{"format":…,"crew":null}` was the
whole request until this module grew the log, and it is now a MISSING FIELD
rather than a request with an implicitly empty history.  A wire that defaulted it
would serve the installed ship to every caller of the old shape — which is
precisely the silent zero this change exists to remove.
(Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_the_pre_history_request_shape_refuses : Bool :=
  decide (stationDailyReadFFI "{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null}" = "")

/-- A log row carrying its own counter — the field the fold DERIVES — is not a
row this wire has a spelling for. (Pinned `= true` in `StationDailyRuntimeFixtures`.) -/
def check_hostile_row_with_a_counter_refuses : Bool :=
  decide (stationDailyReadFFI
    ("{\"format\":\"POA-STATION-DAILY-1\",\"crew\":null,\"history\":[{\"player\":\"" ++
      Emit.bytes32Hex StationCrateOpen.crew41 ++
      "\",\"period\":31,\"counter\":0}]}") = "")

theorem the_authored_table_moves_only_supplies :
    check_the_authored_table_moves_only_supplies = true := by native_decide

theorem the_served_ship_moves_when_the_log_records_an_opening :
    check_the_served_ship_moves_when_the_log_records_an_opening = true := by native_decide

theorem the_two_logs_serve_different_documents :
    check_the_two_logs_serve_different_documents = true := by native_decide

theorem a_log_row_from_another_period_is_refused :
    check_a_log_row_from_another_period_is_refused = true := by native_decide

theorem anonymous_request_round_trips :
    check_anonymous_request_round_trips = true := by native_decide

theorem officer_request_round_trips :
    check_officer_request_round_trips = true := by native_decide

theorem both_requests_are_served :
    check_both_requests_are_served = true := by native_decide

theorem the_officer_is_eligible_and_draws_every_authored_period :
    check_the_officer_is_eligible_and_draws_every_authored_period = true := by native_decide

theorem hostile_unknown_field_refuses :
    check_hostile_unknown_field_refuses = true := by native_decide

theorem hostile_transposed_keys_refuse :
    check_hostile_transposed_keys_refuse = true := by native_decide

theorem hostile_wrong_format_refuses :
    check_hostile_wrong_format_refuses = true := by native_decide

theorem hostile_boolean_crew_refuses :
    check_hostile_boolean_crew_refuses = true := by native_decide

theorem hostile_short_digest_refuses :
    check_hostile_short_digest_refuses = true := by native_decide

theorem hostile_trailing_byte_refuses :
    check_hostile_trailing_byte_refuses = true := by native_decide

theorem the_pre_history_request_shape_refuses :
    check_the_pre_history_request_shape_refuses = true := by native_decide

theorem hostile_row_with_a_counter_refuses :
    check_hostile_row_with_a_counter_refuses = true := by native_decide

#assert_compiled the_authored_table_moves_only_supplies
#assert_compiled the_served_ship_moves_when_the_log_records_an_opening
#assert_compiled the_two_logs_serve_different_documents
#assert_compiled a_log_row_from_another_period_is_refused
#assert_compiled anonymous_request_round_trips
#assert_compiled officer_request_round_trips
#assert_compiled both_requests_are_served
#assert_compiled the_officer_is_eligible_and_draws_every_authored_period
#assert_compiled hostile_unknown_field_refuses
#assert_compiled hostile_transposed_keys_refuse
#assert_compiled hostile_wrong_format_refuses
#assert_compiled hostile_boolean_crew_refuses
#assert_compiled hostile_short_digest_refuses
#assert_compiled hostile_trailing_byte_refuses
#assert_compiled the_pre_history_request_shape_refuses
#assert_compiled hostile_row_with_a_counter_refuses

end Dregg2.Games.PathOfAngels.StationDailyRuntime
