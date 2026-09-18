/-
# NightWatch campaign wire assurance

Closed examples, their three successful-construction proofs, and the wire/judge
checks live together here. Moving only `native_decide` commands left generated
module initialization eagerly evaluating closed `def` values. The September18
baseline measured 116.696s in the inclusive wire initializer. Runtime savings
from this source move require freshly rebuilt C and a linked measurement.

`Activation.mk` and `State.mk` remain private. Fixtures still consume the actual
successful admission/judgement through the same checked `Option.get` proofs.
`CanonicalCodecHealthWire` imports this module for its shipped-row examples.
The runtime wire and FFI closure do not import this module. PathOfAngelsGuards
retains every assurance check and its compiled-evaluator accounting.
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaignWire

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignWire

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## Source-owned reachable watch fixtures -/

def fixtureActor : Digest32 := fixtureRunOwner

def fixtureClaim (nullifier : Digest32) : NightWatchCampaign.Command where
  sequence := 0
  nullifier := nullifier
  action := .claimOfficer fixtureActor ⟨0⟩

def fixtureActivation? : Option NightWatchCampaign.Activation := do
  let manifest ← fixtureValidatedManifest?
  let member ← authorizeCampaignConfigForWorld? fixtureWorld manifest
  NightWatchCampaign.admitActivation? member.config fixtureDraw

/-- The whole authenticated path, end to end: canonical manifest → world-scoped config
member → re-derived commitment and run seed → a judged activation.

`Activation.mk` is private: the fixture consumes this checked successful admission
through `Option.get`. The construction and its proof belong together in assurance. -/
theorem the_authenticated_path_reaches_an_activation :
    fixtureActivation?.isSome = true := by
  native_decide

def fixtureActivation : NightWatchCampaign.Activation :=
  fixtureActivation?.get the_authenticated_path_reaches_an_activation

def fixtureAfter? (nullifier : Digest32) : Option NightWatchCampaign.State :=
  (NightWatchCampaign.judge fixtureActivation
    (NightWatchCampaign.initialState fixtureActivation) (fixtureClaim nullifier)).toOption

def fixtureNullifierA : Digest32 := markDigest 200
def fixtureNullifierB : Digest32 := markDigest 201

/-- The fixture consumes this checked judged state through `Option.get`.
`CanonicalCodecHealthWire` imports this assurance module for its examples. -/
theorem fixture_claim_with_nullifier_A_reaches_a_state :
    (fixtureAfter? fixtureNullifierA).isSome = true := by
  native_decide

/-- The second fixture also consumes its checked judgement through `Option.get`. -/
theorem fixture_claim_with_nullifier_B_reaches_a_state :
    (fixtureAfter? fixtureNullifierB).isSome = true := by
  native_decide

def fixtureStateA : NightWatchCampaign.State :=
  (fixtureAfter? fixtureNullifierA).get fixture_claim_with_nullifier_A_reaches_a_state

def fixtureStateB : NightWatchCampaign.State :=
  (fixtureAfter? fixtureNullifierB).get fixture_claim_with_nullifier_B_reaches_a_state

def fixtureInput : InputWire where
  world := fixtureWorld
  manifest := fixtureManifestBytes
  activation := fixtureDraw
  history := []
  command := fixtureClaim fixtureNullifierA

def fixtureWrongSequenceInput : InputWire :=
  { fixtureInput with
    command := { sequence := 7, nullifier := fixtureNullifierB, action := .resolve } }

def fixtureReplayInput : InputWire :=
  { fixtureInput with
    history := [fixtureClaim fixtureNullifierA]
    command :=
      { sequence := 1, nullifier := fixtureNullifierA
        action := .chooseTask .bridge .plotDrift } }

-- Successful fixture construction retains its compiled-evaluator accounting.
#assert_compiled the_authenticated_path_reaches_an_activation
#assert_compiled fixture_claim_with_nullifier_A_reaches_a_state
#assert_compiled fixture_claim_with_nullifier_B_reaches_a_state

/-! ## The teeth

Every one of these bites on the ACTUAL exported path (`decodeCommand`, `decodeInput`,
`judgeJson`), not on a scratch model of it. -/

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_fixture_command_round_trips_through_the_wire : Bool :=
  decide (decodeCommand (commandJson (fixtureClaim fixtureNullifierA)) =
    some (fixtureClaim fixtureNullifierA))

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_fixture_input_round_trips_through_the_wire : Bool :=
  decide (decodeInput (inputJson fixtureInput) = some fixtureInput)

def unknownActionKindBytes : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"sequence\":0,\"nullifier\":" ++
  jsonString (Emit.bytes32Hex (markDigest 200)) ++ ",\"action\":{\"kind\":\"seize_ship\"}}"

def unknownFieldBytes : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"sequence\":0,\"nullifier\":" ++
  jsonString (Emit.bytes32Hex (markDigest 200)) ++
  ",\"action\":{\"kind\":\"resolve\"},\"score\":9000}"

def reorderedKeyBytes : String :=
  "{\"sequence\":0,\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"nullifier\":" ++
  jsonString (Emit.bytes32Hex (markDigest 200)) ++ ",\"action\":{\"kind\":\"resolve\"}}"

def uppercaseDigestBytes : String :=
  "{\"format\":" ++ jsonString COMMAND_FORMAT ++ ",\"sequence\":0,\"nullifier\":" ++
  jsonString (String.ofList (List.replicate 62 '0') ++ "C8") ++
  ",\"action\":{\"kind\":\"resolve\"}}"

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_command_with_unknown_action_kind_refuses : Bool :=
  (decodeCommand unknownActionKindBytes).isNone

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_command_with_unknown_field_refuses : Bool := (decodeCommand unknownFieldBytes).isNone

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_command_with_reordered_keys_refuses : Bool := (decodeCommand reorderedKeyBytes).isNone

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_command_with_uppercase_digest_refuses : Bool :=
  (decodeCommand uppercaseDigestBytes).isNone

/-! ## End to end, over the exported bytes -/

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_judge_publishes_the_accepted_state_view : Bool :=
  decide (judgeJson (inputJson fixtureInput) =
    some (outputJson (.accepted (StateViewWire.ofState fixtureStateA))))

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_judge_publishes_the_wrong_sequence_refusal : Bool :=
  decide (judgeJson (inputJson fixtureWrongSequenceInput) =
    some (outputJson (.refused .wrongSequence)))

/-- The history really is replayed: the nullifier spent by the logged command is
already in `consumedActions` when the next command arrives.
(Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_judge_replays_the_history_and_refuses_a_spent_nullifier : Bool :=
  decide (judgeJson (inputJson fixtureReplayInput) =
    some (outputJson (.refused .replayedAction)))

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_judgeFFI_returns_empty_on_undecodable_bytes : Bool := judgeFFI "{}" == ""

/-! ## ⚑ The two authority holes, refuted on the exported path

The first pair is the config: a fraudulent rulebook cannot be handed to the judge any
more, because the judge does not take one.  The second pair is the hazard: a caller
who does not hold the slot secret cannot produce an activation at all. -/

/-- A rules table with every threshold at zero — every watch a guaranteed success —
decodes, activates, and is a perfectly good `Config`.  It still yields NO JUDGEMENT,
because the world's content root does not commit to it.  Before this change the same
bytes in `InputWire.config` would have been judged. -/
def forgedRulesInput : InputWire :=
  { fixtureInput with manifest := forgedManifest.toJson }

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_a_fraudulent_rulebook_is_no_longer_judged : Bool :=
  (NightWatchCampaign.activate? forgedRaw).isSome &&
  decide (forgedRaw.rules.map NightWatchCampaign.TaskRule.riskThreshold = [0]) &&
  (judgeJson (inputJson forgedRulesInput)).isNone

/-- The player's own world, freshly activated around the forged manifest, does not
help either — unless persistence audited that world, and this module is handed the one
it audited.  What IS proved here is the narrower fact: the manifest and the world must
agree, so a forged manifest needs a forged ACTIVATION, which lives behind
`WorldActivation`'s signature seam.
(Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_a_forged_manifest_needs_a_forged_world : Bool :=
  !(forgedManifest.matchesWorldB fixtureWorld)

/-- ⚑ The hazard hole.  A caller who knows everything the descriptor publishes — the
slot, the commitment, the mission context, the player — and holds the WRONG secret
cannot produce an activation: the commitment does not open, and the run seed it
derives is not the one the node served.  The identical draw with the right secret IS
admitted, so the refusal is the secret and nothing else. -/
def forgedSecret : HiddenInstance.SlotSecret := ⟨markDigest 91⟩

def forgedDraw : NightWatchCampaign.RawActivation :=
  { fixtureDraw with
    slotSecret := forgedSecret
    runSeed := HiddenInstance.runSeedFor
      { secret := forgedSecret, slot := fixtureSlot, playerKey := fixtureRunOwner }
      fixtureMissionContext }

def forgedSecretInput : InputWire := { fixtureInput with activation := forgedDraw }

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_a_run_drawn_under_the_wrong_secret_is_not_judged : Bool :=
  decide (forgedDraw.slotCommitment = fixtureDraw.slotCommitment) &&
  decide (forgedDraw.runSeed ≠ fixtureDraw.runSeed) &&
  (judgeJson (inputJson forgedSecretInput)).isNone &&
  (judgeJson (inputJson fixtureInput)).isSome

/-- And the caller cannot escape by naming a different slot: the config publishes the
slot its commitment belongs to. -/
def wrongSlotDraw : NightWatchCampaign.RawActivation :=
  { fixtureDraw with slot := ⟨8⟩ }

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_a_run_claiming_another_slot_is_not_judged : Bool :=
  (judgeJson (inputJson { fixtureInput with activation := wrongSlotDraw })).isNone

/-- A run whose owner is not a seated officer is refused, so a node cannot draw a
schedule against an arbitrary key of its choosing. -/
def unseatedDraw : NightWatchCampaign.RawActivation :=
  { fixtureDraw with
    playerKey := markDigest 99
    runSeed := HiddenInstance.runSeedFor
      { secret := fixtureSecret, slot := fixtureSlot, playerKey := markDigest 99 }
      fixtureMissionContext }

/-- (Pinned `= true` in `NightWatchCampaignWireFixtures`.) -/
def check_a_run_owned_by_an_unseated_key_is_not_judged : Bool :=
  !(NightWatchCampaign.rosterHolds fixtureRaw (markDigest 99)) &&
  (judgeJson (inputJson { fixtureInput with activation := unseatedDraw })).isNone

/-! ## ⚑ The view carries no authority

Two states reached by the same command with different nullifiers are DISTINCT — their
`consumedActions` differ — and publish the SAME view.  So `ofState` is not injective,
and the corollary is unconditional: no decoder from the published view back to a
`State` can be sound.  This is why there is no `parseStateView`, and it is refutable —
put the nullifier set in the view and the first conjunct stays true while the second
goes red.

⚠ Both `state_view_erases_the_consumed_nullifier_ledger` and its corollary
`no_state_view_decoder_can_be_sound` live in `NightWatchCampaignWireFixtures.lean`, VERBATIM —
same names, same statements, same namespace, so the fully-qualified names are unchanged. The
corollary went with the pin because its ONLY proof is that pin; leaving it here would have kept
a `native_decide` in the archive's build for no gain. -/


theorem error_names_are_pairwise_distinct :
    check_error_names_are_pairwise_distinct = true := by native_decide

theorem fixture_command_round_trips_through_the_wire :
    check_fixture_command_round_trips_through_the_wire = true := by native_decide

theorem fixture_input_round_trips_through_the_wire :
    check_fixture_input_round_trips_through_the_wire = true := by native_decide

theorem command_with_unknown_action_kind_refuses :
    check_command_with_unknown_action_kind_refuses = true := by native_decide

theorem command_with_unknown_field_refuses :
    check_command_with_unknown_field_refuses = true := by native_decide

theorem command_with_reordered_keys_refuses :
    check_command_with_reordered_keys_refuses = true := by native_decide

theorem command_with_uppercase_digest_refuses :
    check_command_with_uppercase_digest_refuses = true := by native_decide

theorem judge_publishes_the_accepted_state_view :
    check_judge_publishes_the_accepted_state_view = true := by native_decide

theorem judge_publishes_the_wrong_sequence_refusal :
    check_judge_publishes_the_wrong_sequence_refusal = true := by native_decide

theorem judge_replays_the_history_and_refuses_a_spent_nullifier :
    check_judge_replays_the_history_and_refuses_a_spent_nullifier = true := by native_decide

theorem judgeFFI_returns_empty_on_undecodable_bytes :
    check_judgeFFI_returns_empty_on_undecodable_bytes = true := by native_decide

theorem a_fraudulent_rulebook_is_no_longer_judged :
    check_a_fraudulent_rulebook_is_no_longer_judged = true := by native_decide

theorem a_forged_manifest_needs_a_forged_world :
    check_a_forged_manifest_needs_a_forged_world = true := by native_decide

theorem a_run_drawn_under_the_wrong_secret_is_not_judged :
    check_a_run_drawn_under_the_wrong_secret_is_not_judged = true := by native_decide

theorem a_run_claiming_another_slot_is_not_judged :
    check_a_run_claiming_another_slot_is_not_judged = true := by native_decide

theorem a_run_owned_by_an_unseated_key_is_not_judged :
    check_a_run_owned_by_an_unseated_key_is_not_judged = true := by native_decide

/-- Two states reached by the same command with different nullifiers are DISTINCT — their
`consumedActions` differ — and publish the SAME view. -/
theorem state_view_erases_the_consumed_nullifier_ledger :
    fixtureStateA ≠ fixtureStateB ∧
      StateViewWire.ofState fixtureStateA = StateViewWire.ofState fixtureStateB := by
  native_decide

/-- `ofState` is not injective, so the corollary is unconditional: no decoder from the
published view back to a `State` can be sound.  This is why there is no `parseStateView`, and
it is refutable — put the nullifier set in the view and the first conjunct of the pin above
stays true while the second goes red. -/
theorem no_state_view_decoder_can_be_sound
    (decode : StateViewWire → Option NightWatchCampaign.State)
    (sound : ∀ state : NightWatchCampaign.State,
      decode (StateViewWire.ofState state) = some state) : False := by
  obtain ⟨distinct, sameView⟩ := state_view_erases_the_consumed_nullifier_ledger
  refine distinct (Option.some.inj ?_)
  rw [← sound fixtureStateA, ← sound fixtureStateB, sameView]

#assert_compiled error_names_are_pairwise_distinct
#assert_compiled fixture_command_round_trips_through_the_wire
#assert_compiled fixture_input_round_trips_through_the_wire
#assert_compiled command_with_unknown_action_kind_refuses
#assert_compiled command_with_unknown_field_refuses
#assert_compiled command_with_reordered_keys_refuses
#assert_compiled command_with_uppercase_digest_refuses
#assert_compiled judge_publishes_the_accepted_state_view
#assert_compiled judge_publishes_the_wrong_sequence_refusal
#assert_compiled judge_replays_the_history_and_refuses_a_spent_nullifier
#assert_compiled judgeFFI_returns_empty_on_undecodable_bytes
#assert_compiled a_fraudulent_rulebook_is_no_longer_judged
#assert_compiled a_forged_manifest_needs_a_forged_world
#assert_compiled a_run_drawn_under_the_wrong_secret_is_not_judged
#assert_compiled a_run_claiming_another_slot_is_not_judged
#assert_compiled a_run_owned_by_an_unseated_key_is_not_judged
#assert_compiled state_view_erases_the_consumed_nullifier_ledger
#assert_compiled no_state_view_decoder_can_be_sound

end Dregg2.Games.PathOfAngels.NightWatchCampaignWire
