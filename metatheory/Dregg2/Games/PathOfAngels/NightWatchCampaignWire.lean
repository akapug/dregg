/-
# NightWatchCampaignWire — the canonical JSON boundary that makes one watch playable

`NightWatchCampaign` is a complete judged kernel with no way in.  It has zero
`@[export]` and no wire codec, so no browser, node, or curator can reach it.  This
module is that boundary and nothing else: it is a JSON **codec**, not a constraint
system — no AIR, no gadget, no `air_accepts` lives here.

## ⚑ WHAT CHANGED 2026-08-05 — the config no longer arrives in the caller's bytes

`InputWire` used to carry `config`, so `dregg_poa_night_watch_campaign_judge` was a
pure function of the bytes it was handed: `activate?` checked that a config was
*structurally* valid and nothing checked that it was *authentic*.  A caller supplying
all-zero `riskThreshold`s and maximal `successContribution`s got a judged, internally
consistent, entirely fraudulent watch — and every theorem in this file still held,
because each one was conditional on the config supplied.

`InputWire` now carries a **world identity and an activated manifest**, and the config
is whatever `NightWatchCampaignAdmission.authorizeCampaignConfigForWorld?` finds under
`poa.night-watch-campaign.config.v1` inside a manifest whose SHA-256 root IS that
world's `contentRoot`.  There is no other route: `resolve?` cannot reach a `Config`
except through the witness, and the config codec itself lives in the admission module,
which this file imports rather than mirrors.

It also carries the node's **run activation** (slot, secret, published commitment,
player key, mission context, run seed) and the kernel re-derives the commitment and
the seed from the secret before anything is judged.  That is
`Judged.admissionChecks`'s discipline for this organ.

⚠ **The secret crosses this wire**, exactly as it does on `POA-SLOT-DERIVE-1`
(`SlotDeriveRuntime.lean:63`).  These bytes are node-held state, never a client claim,
and they must not leave the node.  The reply does not echo them — the published view
carries no activation field at all.

The native export is bound by `dregg-lean-ffi/src/poa_night_watch_ffi.rs` through
the C shim and the required-export gate. This binding alone does not establish a
public deployment. A host supplies an audited world, not a caller-selected rulebook.

## The asymmetry, stated plainly

`NightWatchCampaign.State` is `private mk ::`.  Canonical JSON therefore **cannot
construct a state**, and this file deliberately does not try: there is no state
parser, and `StateViewWire` is encode-only.  A state is reached the one legitimate way
— `initialState` on an admitted `Activation`, then `replay` over the player's own
command log.  The host persists the COMMAND LIST, not the state.

`no_state_view_decoder_can_be_sound` proves that absence is not merely a convention:
the published view is provably NOT injective on states, so no function `StateViewWire
→ Option State` can round-trip.  The witness is two states differing only in which
nullifier they consumed.

## Fail-closed

Every decoder runs through `canonicalDecode`: parse, re-encode, and refuse unless the
bytes are byte-identical.  One JSON value therefore has exactly one accepted spelling
— key order, whitespace, decimal spelling, digest case, and unknown fields are all
fixed, not normalised.  `exactKeys` refuses missing and unknown fields; every natural
carries the kernel's own bound at the parser; unknown station, task, role and action
tags refuse.

## Two things about the kernel a reader should know

* `configValidB` does **not** require `raw.logStream.validB`.  It constrains only
  `logStream.aggregate.namespaceId = progression.federationId`; the stream's `world` is
  otherwise unchecked, so an activated `Config` may name a zero world identity.  This
  wire does not add that check — semantic validity is `activate?`'s job and a wire that
  refuses more than the kernel is a second disagreeing shape.  It is named here so it
  is findable.  (The world an admitted config is BOUND to is the activation world in
  `InputWire.world`, checked against `progression`, not `logStream.world`.)
* Replay cost is quadratic, by derivation not measurement: `judge` tests
  `command.nullifier ∈ state.consumedActions` and then inserts into that `Finset
  Digest32`, both linear, so replaying `n` commands costs Θ(n²) digest comparisons.
  `MAX_COMMAND_LOG` is the structural maximum (four commands per shift × `MAX_SHIFTS`),
  not a recommended one.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignWire

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## Wire constants -/

abbrev COMMAND_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-COMMAND-1"
abbrev INPUT_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-NIGHT-WATCH-CAMPAIGN-OUT-1"

/-- Four commands (claim, choose, resolve, debrief) complete one shift, so a full
campaign log is four times the shift ceiling. -/
abbrev MAX_COMMAND_LOG : Nat := 4 * NightWatchCampaign.MAX_SHIFTS

/-- The player view carries the tail of the logbook, not all of it. -/
abbrev MAX_HISTORY_VIEW : Nat := 32

/-! ## Refusal labels — encode-only

`errorName` never appears on an input wire; it labels a refusal in the output bytes.
The two theorems below say together that the label distinguishes every refusal the
kernel can raise. -/

def errorName : NightWatchCampaign.Error → String
  | .wrongSequence => "wrong_sequence"
  | .replayedAction => "replayed_action"
  | .shiftLimit => "shift_limit"
  | .wrongPhase => "wrong_phase"
  | .unknownOfficer => "unknown_officer"
  | .officerActorMismatch => "officer_actor_mismatch"
  | .unknownTask => "unknown_task"
  | .roleMismatch => "role_mismatch"
  | .insufficientResources => "insufficient_resources"
  | .evidenceBound => "evidence_bound"
  | .missingHealth => "missing_health"
  | .historyLimit => "history_limit"
  | .callerAuthoredOutcome => "caller_authored_outcome"

def allErrors : List NightWatchCampaign.Error :=
  [ .wrongSequence, .replayedAction, .shiftLimit, .wrongPhase, .unknownOfficer
  , .officerActorMismatch, .unknownTask, .roleMismatch, .insufficientResources
  , .evidenceBound, .missingHealth, .historyLimit
  , .callerAuthoredOutcome ]

theorem allErrors_is_exhaustive (error : NightWatchCampaign.Error) : error ∈ allErrors := by
  cases error <;> simp [allErrors]

/-- The refusal labels distinguish every error the kernel can raise.
(Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_error_names_are_pairwise_distinct : Bool := decide (allErrors.map errorName).Nodup

#assert_axioms allErrors_is_exhaustive

/-! ## The player's submission -/

def actionJson : NightWatchCampaign.Action → String
  | .claimOfficer actor seat =>
      "{\"kind\":\"claim_officer\",\"actor\":" ++ jsonString (Emit.bytes32Hex actor) ++
      ",\"seat\":" ++ toString seat.value ++ "}"
  | .chooseTask station task =>
      "{\"kind\":\"choose_task\",\"station\":" ++ toString station.tag ++
      ",\"task\":" ++ toString task.tag ++ "}"
  | .resolve => "{\"kind\":\"resolve\"}"
  | .debrief => "{\"kind\":\"debrief\"}"

def commandJson (command : NightWatchCampaign.Command) : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++
  ",\"sequence\":" ++ toString command.sequence ++
  ",\"nullifier\":" ++ jsonString (Emit.bytes32Hex command.nullifier) ++
  ",\"action\":" ++ actionJson command.action ++ "}"

private def parseAction (j : Json) : Except String NightWatchCampaign.Action := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "claim_officer" => do
      exactKeys j ["kind", "actor", "seat"]
      pure (.claimOfficer (← objectDigest j "actor") ⟨← objectNat j "seat" 3⟩)
  | "choose_task" => do
      exactKeys j ["kind", "station", "task"]
      let station ← match stationOfTag? (← objectNat j "station" 6) with
        | some value => pure value
        | none => throw "unknown station tag"
      let task ← match taskOfTag? (← objectNat j "task" 6) with
        | some value => pure value
        | none => throw "unknown task tag"
      pure (.chooseTask station task)
  | "resolve" => do
      exactKeys j ["kind"]
      pure .resolve
  | "debrief" => do
      exactKeys j ["kind"]
      pure .debrief
  | _ => throw "unknown action kind"

private def parseCommand (j : Json) : Except String NightWatchCampaign.Command := do
  exactKeys j ["format", "sequence", "nullifier", "action"]
  if (← j.getObjValAs? String "format") != COMMAND_FORMAT then throw "wrong command format"
  pure {
    sequence := ← objectNat j "sequence"
    nullifier := ← objectDigest j "nullifier"
    action := ← parseAction (← j.getObjVal? "action")
  }

def decodeCommandWithLimit (limit : Nat) (bytes : String) : Option NightWatchCampaign.Command :=
  canonicalDecode parseCommand commandJson limit bytes

def decodeCommand (bytes : String) : Option NightWatchCampaign.Command :=
  decodeCommandWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The node's run activation

⚠ EVERY field here is node state.  The key order is `SlotDeriveRuntime.Request`'s for
the mission context (`mission_id`, `epoch`, `federation_id`, `content_session`), so the
same four values are spelled the same way on both wires. -/

def missionContextJson (mission : HiddenInstance.MissionContext) : String :=
  "{\"mission_id\":" ++ toString mission.missionId.value ++
  ",\"epoch\":" ++ toString mission.epoch.value ++
  ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex mission.federationId) ++
  ",\"content_session\":" ++ jsonString (Emit.bytes32Hex mission.contentSession) ++ "}"

def activationJson (draw : NightWatchCampaign.RawActivation) : String :=
  "{\"slot\":" ++ toString draw.slot.value ++
  ",\"slot_secret\":" ++ jsonString (Emit.bytes32Hex draw.slotSecret.value) ++
  ",\"slot_commitment\":" ++ jsonString (Emit.bytes32Hex draw.slotCommitment) ++
  ",\"player_key\":" ++ jsonString (Emit.bytes32Hex draw.playerKey) ++
  ",\"mission\":" ++ missionContextJson draw.mission ++
  ",\"run_seed\":" ++ jsonString (Emit.bytes32Hex draw.runSeed) ++ "}"

private def parseMissionContext (j : Json) : Except String HiddenInstance.MissionContext := do
  exactKeys j ["mission_id", "epoch", "federation_id", "content_session"]
  pure {
    missionId := ⟨← objectNat j "mission_id"⟩
    epoch := ⟨← objectNat j "epoch"⟩
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
  }

private def parseActivation (j : Json) : Except String NightWatchCampaign.RawActivation := do
  exactKeys j ["slot", "slot_secret", "slot_commitment", "player_key", "mission", "run_seed"]
  pure {
    slot := ⟨← objectNat j "slot"⟩
    slotSecret := ⟨← objectDigest j "slot_secret"⟩
    slotCommitment := ← objectDigest j "slot_commitment"
    playerKey := ← objectDigest j "player_key"
    mission := ← parseMissionContext (← j.getObjVal? "mission")
    runSeed := ← objectDigest j "run_seed"
  }

/-! ## The judge envelope

The host holds an audited world, the activated manifest that world's `contentRoot`
commits to, its own run activation, and the player's own command log.  It never holds
a serialized state, because there is no way to serialize one back. -/

structure InputWire where
  world : EventBatch.WorldIdentity
  manifest : String
  activation : NightWatchCampaign.RawActivation
  history : List NightWatchCampaign.Command
  command : NightWatchCampaign.Command
deriving DecidableEq

def inputJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
  ",\"world\":" ++ worldIdentityJson input.world ++
  ",\"manifest\":" ++ jsonString input.manifest ++
  ",\"activation\":" ++ activationJson input.activation ++
  ",\"history\":" ++ jsonArray (input.history.map commandJson) ++
  ",\"command\":" ++ commandJson input.command ++ "}"

private def parseInput (j : Json) : Except String InputWire := do
  exactKeys j ["format", "world", "manifest", "activation", "history", "command"]
  if (← j.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  pure {
    world := ← parseWorldIdentity (← j.getObjVal? "world")
    manifest := ← j.getObjValAs? String "manifest"
    activation := ← parseActivation (← j.getObjVal? "activation")
    history := ← parseBoundedList (← j.getObjVal? "history") MAX_COMMAND_LOG parseCommand
    command := ← parseCommand (← j.getObjVal? "command")
  }

def decodeInputWithLimit (limit : Nat) (bytes : String) : Option InputWire :=
  canonicalDecode parseInput inputJson limit bytes

def decodeInput (bytes : String) : Option InputWire :=
  decodeInputWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The proof-erased player view — ENCODE ONLY

There is deliberately no `parseStateView`.  `no_state_view_decoder_can_be_sound` below
shows that adding one could not be faithful even in principle. -/

structure HealthViewWire where
  seat : Nat
  wounds : Nat
  strain : Nat
  recoveryObserved : Nat
deriving DecidableEq

structure MasteryViewWire where
  seat : Nat
  station : Nat
  xp : Nat
  level : Nat
deriving DecidableEq

inductive PhaseViewWire where
  | idle
  | claimed (seat : Nat)
  | assigned (seat : Nat) (station : Nat) (task : Nat)
  | awaitingDebrief (shift : Nat) (seat : Nat) (station : Nat) (task : Nat)
      (hazardRoll : Nat) (success : Bool)
deriving DecidableEq

structure HistoryRowWire where
  shift : Nat
  seat : Nat
  station : Nat
  task : Nat
  success : Bool
  hazardRoll : Nat
  riskThreshold : Nat
  evidenceAfter : Nat
  terminalContentId : Digest32
deriving DecidableEq

structure StateViewWire where
  sequence : Nat
  shift : Nat
  resources : NightWatchCampaign.ShipResources
  evidence : Nat
  health : List HealthViewWire
  mastery : List MasteryViewWire
  phase : PhaseViewWire
  historyLength : Nat
  recentHistory : List HistoryRowWire
  intentCount : Nat
  consumedActionCount : Nat
deriving DecidableEq

def HistoryRowWire.ofEntry (entry : NightWatchCampaign.LogbookEntry) : HistoryRowWire where
  shift := entry.shift
  seat := entry.seat.value
  station := entry.station.tag
  task := entry.task.tag
  success := entry.success
  hazardRoll := entry.hazardRoll
  riskThreshold := entry.riskThreshold
  evidenceAfter := entry.evidenceAfter
  terminalContentId := entry.terminalContentId

/-- ⚠ A resolved watch's roll is published only AFTER it is resolved, and no future
roll appears anywhere in this view: the schedule lives on the `Activation`, which is
node state and is never encoded. -/
def StateViewWire.ofState (state : NightWatchCampaign.State) : StateViewWire where
  sequence := state.sequence
  shift := state.shift
  resources := state.resources
  evidence := state.evidence
  health := state.health.map fun row =>
    ⟨row.seat.value, row.wounds, row.strain, row.recoveryObserved⟩
  mastery := state.mastery.map fun row =>
    ⟨row.seat.value, row.station.tag, row.xp, row.level⟩
  phase := match state.phase with
    | .idle => .idle
    | .claimed officer => .claimed officer.id.value
    | .assigned officer rule => .assigned officer.id.value rule.station.tag rule.task.tag
    | .awaitingDebrief resolved =>
        .awaitingDebrief resolved.shift resolved.officer.id.value resolved.rule.station.tag
          resolved.rule.task.tag resolved.hazardRoll resolved.success
  historyLength := state.history.length
  recentHistory :=
    (state.history.drop (state.history.length - MAX_HISTORY_VIEW)).map HistoryRowWire.ofEntry
  intentCount := state.intents.length
  consumedActionCount := state.consumedActions.card

def healthViewJson (row : HealthViewWire) : String :=
  "{\"seat\":" ++ toString row.seat ++
  ",\"wounds\":" ++ toString row.wounds ++
  ",\"strain\":" ++ toString row.strain ++
  ",\"recovery_observed\":" ++ toString row.recoveryObserved ++ "}"

def masteryViewJson (row : MasteryViewWire) : String :=
  "{\"seat\":" ++ toString row.seat ++
  ",\"station\":" ++ toString row.station ++
  ",\"xp\":" ++ toString row.xp ++
  ",\"level\":" ++ toString row.level ++ "}"

def phaseViewJson : PhaseViewWire → String
  | .idle => "{\"kind\":\"idle\"}"
  | .claimed seat => "{\"kind\":\"claimed\",\"seat\":" ++ toString seat ++ "}"
  | .assigned seat station task =>
      "{\"kind\":\"assigned\",\"seat\":" ++ toString seat ++
      ",\"station\":" ++ toString station ++ ",\"task\":" ++ toString task ++ "}"
  | .awaitingDebrief shift seat station task hazardRoll success =>
      "{\"kind\":\"awaiting_debrief\",\"shift\":" ++ toString shift ++
      ",\"seat\":" ++ toString seat ++ ",\"station\":" ++ toString station ++
      ",\"task\":" ++ toString task ++ ",\"hazard_roll\":" ++ toString hazardRoll ++
      ",\"success\":" ++ boolJson success ++ "}"

def historyRowJson (row : HistoryRowWire) : String :=
  "{\"shift\":" ++ toString row.shift ++
  ",\"seat\":" ++ toString row.seat ++
  ",\"station\":" ++ toString row.station ++
  ",\"task\":" ++ toString row.task ++
  ",\"success\":" ++ boolJson row.success ++
  ",\"hazard_roll\":" ++ toString row.hazardRoll ++
  ",\"risk_threshold\":" ++ toString row.riskThreshold ++
  ",\"evidence_after\":" ++ toString row.evidenceAfter ++
  ",\"terminal_content_id\":" ++ jsonString (Emit.bytes32Hex row.terminalContentId) ++ "}"

def stateViewJson (view : StateViewWire) : String :=
  "{\"sequence\":" ++ toString view.sequence ++
  ",\"shift\":" ++ toString view.shift ++
  ",\"resources\":" ++ resourcesJson view.resources ++
  ",\"evidence\":" ++ toString view.evidence ++
  ",\"health\":" ++ jsonArray (view.health.map healthViewJson) ++
  ",\"mastery\":" ++ jsonArray (view.mastery.map masteryViewJson) ++
  ",\"phase\":" ++ phaseViewJson view.phase ++
  ",\"history_length\":" ++ toString view.historyLength ++
  ",\"recent_history\":" ++ jsonArray (view.recentHistory.map historyRowJson) ++
  ",\"intent_count\":" ++ toString view.intentCount ++
  ",\"consumed_action_count\":" ++ toString view.consumedActionCount ++ "}"

inductive OutputWire where
  | accepted (view : StateViewWire)
  | refused (error : NightWatchCampaign.Error)
deriving DecidableEq

def outputJson : OutputWire → String
  | .accepted view =>
      "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
      ",\"status\":\"accepted\",\"error\":null,\"state\":" ++ stateViewJson view ++ "}"
  | .refused error =>
      "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
      ",\"status\":\"refused\",\"error\":" ++ jsonString (errorName error) ++
      ",\"state\":null}"

/-! ## The entry point -/

/-- Authenticate the config against the world, admit the node's activation against
that config, and rebuild the state the only legitimate way: `initialState`, then
`replay` over the player's own command log.

Four separate ways to get nothing at all rather than a partial judgement: a manifest
that is not canonical, a manifest that is not this world's content root (or carries no
config component, or one that does not activate), an activation whose commitment or
run seed does not re-derive, and a command log the kernel refuses. -/
def resolve? (input : InputWire) :
    Option (NightWatchCampaign.Activation × NightWatchCampaign.State) :=
  match ActivatedContent.decodeManifest input.manifest with
  | none => none
  | some manifest =>
      match authorizeCampaignConfigForWorld? input.world manifest with
      | none => none
      | some member =>
          match NightWatchCampaign.admitActivation? member.config input.activation with
          | none => none
          | some activation =>
              match NightWatchCampaign.replay activation
                  (NightWatchCampaign.initialState activation) input.history with
              | .error _ => none
              | .ok before => some (activation, before)

def outcome? (input : InputWire) : Option OutputWire :=
  match resolve? input with
  | none => none
  | some (activation, before) =>
      match NightWatchCampaign.judge activation before input.command with
      | .ok after => some (.accepted (StateViewWire.ofState after))
      | .error error => some (.refused error)

def judgeJson (bytes : String) : Option String :=
  match decodeInput bytes with
  | none => none
  | some input =>
      match outcome? input with
      | none => none
      | some output => some (outputJson output)

/-- The public boundary.  It takes no authority argument, so there is no sponsor,
operator, or override a caller could supply; and it returns the empty string rather
than a partial answer when anything refuses.

⚑ MOUNTED NOWHERE: no route, no C shim, no `build.rs` gate, no Rust binding. -/
@[export dregg_poa_night_watch_campaign_judge]
def judgeFFI (bytes : String) : String := (judgeJson bytes).getD ""

/-- ⚑ THE WELD.  An accepted output is the campaign judge's own successor, not a
projection this module chose.  Replace `StateViewWire.ofState after` in `outcome?`
with any doctored view — say a state with one more evidence point — and this goes
red. -/
theorem accepted_output_is_the_campaign_judges_successor
    (input : InputWire) (view : StateViewWire)
    (published : outcome? input = some (.accepted view)) :
    ∃ activation before after,
      resolve? input = some (activation, before) ∧
      NightWatchCampaign.judge activation before input.command = Except.ok after ∧
      view = StateViewWire.ofState after := by
  unfold outcome? at published
  split at published
  · simp at published
  · next activation before resolved =>
      split at published
      · next after judged =>
          have step := Option.some.inj published
          injection step with viewEq
          exact ⟨activation, before, after, resolved, judged, viewEq.symm⟩
      · next error _ => simp at published

#assert_axioms accepted_output_is_the_campaign_judges_successor

/-! ## Canonicality certificates -/

theorem decodeCommandWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : NightWatchCampaign.Command}
    (accepted : decodeCommandWithLimit limit bytes = some value) :
    commandJson value = bytes :=
  canonicalDecode_reencodes parseCommand commandJson limit bytes value accepted

theorem decodeInputWithLimit_reencodes {limit : Nat} {bytes : String} {value : InputWire}
    (accepted : decodeInputWithLimit limit bytes = some value) :
    inputJson value = bytes :=
  canonicalDecode_reencodes parseInput inputJson limit bytes value accepted

#assert_axioms decodeCommandWithLimit_reencodes
#assert_axioms decodeInputWithLimit_reencodes

/-! Closed admission/judge examples and all their compiled proof pins live in
`NightWatchCampaignWireFixtures`. Their values, not only their theorem commands,
are outside the native runtime import closure. Codec laws above remain here. -/

end Dregg2.Games.PathOfAngels.NightWatchCampaignWire
