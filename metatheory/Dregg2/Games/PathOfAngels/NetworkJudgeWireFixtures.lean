/-
# Signal network wire — the fixture-pin EVALUATION, out of the crypto archive's build

`NetworkJudgeWire.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its thirteen fixture pins ran `native_decide` at elaboration — so any
Signal-wire fixture regression was a hard failure of every Rust proving target in the
workspace (the compilation-unit coupling the stale-fixture outage measured). The pins'
STATEMENTS remain in `NetworkJudgeWire.lean` as evaluation-free `check_* : Bool`
definitions, beside the fixture values they exercise; THIS module is where they are RUN.
It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by
NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ One construction proof did NOT move (`fixtureTarget_is_the_drawn_instance`) —
`fixtureConfig` consumes it as data (it discharges `Config.target_eq` inside
`Emit.signalConfigWith`), so it must elaborate where the config is built.  It is the named
residue; the fixture header in `NetworkJudgeWire.lean` records it.
-/
import Dregg2.Games.PathOfAngels.NetworkJudgeWire

namespace Dregg2.Games.PathOfAngels.NetworkJudgeWire

set_option autoImplicit false
open Lean
open Dregg2.Games.PathOfAngels
open scoped Prod.Lex
open scoped Prod.Lex

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The fixture input decodes back to itself under the canonical seal.
(Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_roundtrip : Bool :=
  decide (decodeSignalInput fixtureInputBytes = some fixtureInputWire)

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_refuses_tight_byte_cap : Bool :=
  (decodeSignalInputWithLimit (fixtureInputBytes.length - 1) fixtureInputBytes).isNone

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_semantic_inhabited : Bool :=
  fixtureInputWire.toSemantic?.isSome

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_refuses_trailing_bytes : Bool :=
  (decodeSignalInput (fixtureInputBytes ++ "\n")).isNone

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_refuses_uppercase_digest : Bool :=
  (decodeSignalInput
    (fixtureInputBytes.replace FIXTURE_FEDERATION_HEX
      (String.toUpper FIXTURE_FEDERATION_HEX))).isNone

def oversizedActionsInput : SignalInputWire :=
  { fixtureInputWire with request := {
      fixtureInputWire.request with
        actions := .signal (List.replicate (GameTag.signal.actionLimit + 1) { low := 0, mid := 0, high := 0 })
    } }

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_refuses_oversized_actions : Bool :=
  (decodeSignalInput oversizedActionsInput.toJson).isNone

def duplicateKnownInput : SignalInputWire :=
  { fixtureInputWire with canon := {
      fixtureInputWire.canon with
      known := [fixtureInputWire.config.mission.artifact, fixtureInputWire.config.mission.artifact]
    } }

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_refuses_duplicate_canon_rows : Bool :=
  (decodeSignalInput duplicateKnownInput.toJson).isNone

def mismatchedWorldInput : SignalInputWire :=
  { fixtureInputWire with world := { fixtureInputWire.world with sequence := 1 } }

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_semantics_refuses_world_canon_mismatch : Bool :=
  !mismatchedWorldInput.toSemantic?.isSome

def oversizedCarrierInput : SignalInputWire :=
  { fixtureInputWire with carrier := {
      fixtureInputWire.carrier with currentPlayerCounter := WIRE_NAT_LIMIT + 1
    } }

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_input_refuses_oversized_carrier_counter : Bool :=
  (decodeSignalInput oversizedCarrierInput.toJson).isNone

/-- The fixture output decodes back to itself under the canonical seal.
(Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_output_roundtrip : Bool :=
  decide (decodeSignalOutput fixtureOutputBytes = some fixtureOutputWire)

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_output_refuses_tight_byte_cap : Bool :=
  (decodeSignalOutputWithLimit (fixtureOutputBytes.length - 1) fixtureOutputBytes).isNone

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_output_semantic_inhabited : Bool :=
  fixtureOutputWire.toSemantic?.isSome

/-- (Pinned `= true` in `NetworkJudgeWireFixtures`.) -/
def check_fixture_output_refuses_trailing_bytes : Bool :=
  (decodeSignalOutput (fixtureOutputBytes ++ "\n")).isNone

theorem fixture_input_roundtrip :
    check_fixture_input_roundtrip = true := by native_decide

theorem fixture_input_refuses_tight_byte_cap :
    check_fixture_input_refuses_tight_byte_cap = true := by native_decide

theorem fixture_input_semantic_inhabited :
    check_fixture_input_semantic_inhabited = true := by native_decide

theorem fixture_input_refuses_trailing_bytes :
    check_fixture_input_refuses_trailing_bytes = true := by native_decide

theorem fixture_input_refuses_uppercase_digest :
    check_fixture_input_refuses_uppercase_digest = true := by native_decide

theorem fixture_input_refuses_oversized_actions :
    check_fixture_input_refuses_oversized_actions = true := by native_decide

theorem fixture_input_refuses_duplicate_canon_rows :
    check_fixture_input_refuses_duplicate_canon_rows = true := by native_decide

theorem fixture_semantics_refuses_world_canon_mismatch :
    check_fixture_semantics_refuses_world_canon_mismatch = true := by native_decide

theorem fixture_input_refuses_oversized_carrier_counter :
    check_fixture_input_refuses_oversized_carrier_counter = true := by native_decide

theorem fixture_output_roundtrip :
    check_fixture_output_roundtrip = true := by native_decide

theorem fixture_output_refuses_tight_byte_cap :
    check_fixture_output_refuses_tight_byte_cap = true := by native_decide

theorem fixture_output_semantic_inhabited :
    check_fixture_output_semantic_inhabited = true := by native_decide

theorem fixture_output_refuses_trailing_bytes :
    check_fixture_output_refuses_trailing_bytes = true := by native_decide

#assert_compiled fixture_input_roundtrip
#assert_compiled fixture_input_refuses_tight_byte_cap
#assert_compiled fixture_input_semantic_inhabited
#assert_compiled fixture_input_refuses_trailing_bytes
#assert_compiled fixture_input_refuses_uppercase_digest
#assert_compiled fixture_input_refuses_oversized_actions
#assert_compiled fixture_input_refuses_duplicate_canon_rows
#assert_compiled fixture_semantics_refuses_world_canon_mismatch
#assert_compiled fixture_input_refuses_oversized_carrier_counter
#assert_compiled fixture_output_roundtrip
#assert_compiled fixture_output_refuses_tight_byte_cap
#assert_compiled fixture_output_semantic_inhabited
#assert_compiled fixture_output_refuses_trailing_bytes

end Dregg2.Games.PathOfAngels.NetworkJudgeWire
