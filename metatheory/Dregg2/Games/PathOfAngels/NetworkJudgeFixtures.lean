/-
# Signal network judge — fixture data, checks and compiled assurance

The success/refusal fixtures, their 26 `check_* : Bool` definitions and all 26
`native_decide` / `#assert_compiled` pins live together in this module, rooted in
`PathOfAngelsGuards` and absent from the `Dregg2.FFI` import closure. A plain
`lake build` still evaluates every pin against the real runtime judge.

Moving only the proof evaluations here on 2026-08-08 left the closed Bool
computations in `NetworkJudge.lean`: they do not run during def elaboration, but
its generated native initializer eagerly computed them. The 2026-09-18 move
removes those fixture computations from the runtime module while retaining every
declaration body, name and compiled assertion. The wire module's own fixtures
and imported game/emitter computations are separate remaining startup work.

The runtime judge, its exported entry point and its general soundness theorems
remain in `NetworkJudge.lean`; no production policy is duplicated here.
-/
import Dregg2.Games.PathOfAngels.NetworkJudge

namespace Dregg2.Games.PathOfAngels.NetworkJudge

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire

set_option autoImplicit false

/-- This is the actual emitted Signal puzzle, not an independently assembled
receipt-shaped value.  It traverses strict input decode, semantic reconstruction,
the abstract `JudgedRun` constructor boundary, Canon's world chain, and strict
successor encoding. (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_processSignalWire_success : Bool :=
  decide (processSignalWire fixtureInputBytes = some fixtureOutputBytes)

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_signalJudgeFFI_success : Bool :=
  decide (signalJudgeFFI fixtureInputBytes = fixtureOutputBytes)

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_signalJudgeFFI_malformed_refused : Bool :=
  decide (signalJudgeFFI (fixtureInputBytes ++ "\n") = "")

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_verifySignalTransition_success : Bool :=
  (verifySignalTransition fixtureInputBytes fixtureOutputBytes).isSome

def incompleteCanonOutputWire : SignalOutputWire := {
  fixtureOutputWire with
  successorCanon := { fixtureSuccessorCanonWire with
    known := []
    consumedRuns := []
    playerCounters := []
    revision := 0 }
}

/-- A well-shaped standalone output is not enough: exact transition verification
rejects the same world paired with a Canon state that omitted settlement effects.
(Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_incomplete_canon_output_refused : Bool :=
  (verifySignalTransition fixtureInputBytes incompleteCanonOutputWire.toJson).isNone

def wrongPlayerInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with playerKey := fixtureActorRoot }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_wrong_player_refused : Bool :=
  (processSignalWire wrongPlayerInputWire.toJson).isNone

def wrongConfigInputWire : SignalInputWire := {
  fixtureInputWire with
  config := .signal { SignalConfigWire.ofSemantic fixtureConfig with
    reward := { ContributionWire.ofSemantic Emit.signalReward with score := 499 } }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_wrong_config_refused : Bool :=
  (processSignalWire wrongConfigInputWire.toJson).isNone

def wrongCurrentCounterInputWire : SignalInputWire := {
  fixtureInputWire with
  carrier := { fixtureInputWire.carrier with currentPlayerCounter := 1 }
  request := { fixtureInputWire.request with previousPlayerCounter := 1 }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_wrong_current_counter_refused : Bool :=
  (processSignalWire wrongCurrentCounterInputWire.toJson).isNone

def staleCounterInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with previousPlayerCounter := 1 }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_stale_counter_refused : Bool :=
  (processSignalWire staleCounterInputWire.toJson).isNone

def wrongActionInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with
    actions := .signal [{ low := 0, mid := 0, high := 0 }] }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_wrong_action_refused : Bool :=
  (processSignalWire wrongActionInputWire.toJson).isNone

def multipleActionsInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with
    actions := .signal
      [CodeWire.ofSemantic fixtureConfig.target, CodeWire.ofSemantic fixtureConfig.target] }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_multiple_actions_refused : Bool :=
  (processSignalWire multipleActionsInputWire.toJson).isNone

def staleRevisionInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with expectedCanonRevision := 1 }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_stale_revision_refused : Bool :=
  (processSignalWire staleRevisionInputWire.toJson).isNone

/-- Replaying the original counter-zero request against the genuine successor
state fails because Canon now records counter one (and the original receipt key). -/
def replayAgainstSuccessorInputWire : SignalInputWire := {
  fixtureInputWire with
  world := fixturePostWorldWire
  canon := fixtureSuccessorCanonWire
  request := { fixtureInputWire.request with
    expectedWorldSequence := 1
    expectedCanonRevision := 1 }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_replay_against_successor_refused : Bool :=
  (processSignalWire replayAgainstSuccessorInputWire.toJson).isNone

/-! ### The hidden-instance teeth

Each input below is the ACCEPTED one with exactly one value moved, so nothing but that
value is doing the refusing.  The general reason each is refused for is a theorem in
`Judged` (`judgeActive_uncommitted_secret_refused`, `judgeActive_wrong_commitment_refused`,
`judgeActive_wrong_slot_refused`, `judgeActive_underived_seed_refused`); what these add is
that the refusals are REACHABLE through the whole decode → reconstruct → settle path, not
merely stateable about an `ActiveRunState` nothing constructs. -/

/-- A node that published one commitment and then judged against a different slot
secret.  This is the "choose the instance after seeing the transcript" move. -/
def swappedSlotSecretInputWire : SignalInputWire := {
  fixtureInputWire with
  slotState := { fixtureInputWire.slotState with secret := fixtureActorRoot }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_swapped_slot_secret_refused : Bool :=
  (processSignalWire swappedSlotSecretInputWire.toJson).isNone

/-- A client claiming a commitment the node did not publish for this slot. -/
def wrongSlotCommitmentInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with slotCommitment := fixtureActorRoot }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_wrong_slot_commitment_refused : Bool :=
  (processSignalWire wrongSlotCommitmentInputWire.toJson).isNone

/-- A client claiming a different slot from the one the node opened. -/
def wrongSlotInputWire : SignalInputWire := {
  fixtureInputWire with
  request := { fixtureInputWire.request with slot := fixtureInputWire.request.slot + 1 }
}

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_wrong_claimed_slot_refused : Bool :=
  (processSignalWire wrongSlotInputWire.toJson).isNone

/-- ⚑ **The seed nobody gets to choose.**  This input is internally CONSISTENT — the
config is exactly what `Emit.signalConfig` renders for `Emit.UNBOUND_RUN_SEED`, its target
is `targetFromSeed?` of that seed, `exactEmittedSignalConfig` accepts it, and the submitted
action solves it — and it is REFUSED, because that seed is not `HiddenInstance.runSeedFor`
of the committed slot secret for this player.  This is the falsifier for the claim that
`UNBOUND_RUN_SEED` cannot be played. -/
def unboundSeedConfig : SignalTriangulation.Config :=
  Emit.signalTemplateConfig fixtureFederationId fixtureSourceDigest
    fixtureContentDigest fixtureContentRoot fixtureActivationDigest

def unboundSeedInputWire : SignalInputWire := {
  fixtureInputWire with
  config := .signal (SignalConfigWire.ofSemantic unboundSeedConfig)
  request := { fixtureInputWire.request with
    actions := .signal [CodeWire.ofSemantic unboundSeedConfig.target] }
}

/-! ### ⚑ THE SECOND GAME, THROUGH THIS EXACT EXPORT

`processSignalWire` is the body of `@[export dregg_poa_signal_judge]`.  These checks run
a Vent Crawl transcript through IT — not through `VentCrawl.judge` directly, not through
a test harness — so what they pin is that the deployed boundary settles a second game.

⚠ Each hostile check asserts its MUTATION IS PRESENT before it reads the verdict.  A
`.isNone` alone would stay green if the mutation stopped applying, which is the shape
that killed a falsifier in this repo already. -/

/-- POLE ONE — a legitimate Vent Crawl run SETTLES. -/
def check_vent_fixture_settles : Bool :=
  (processSignalWire ventFixtureInputWire.toJson).isSome

/-- ⚑ And it settles into the SAME canonical output wire the Signal arm produces —
so the successor a node persists is one shape for every game. -/
def check_vent_output_is_canonical : Bool :=
  match processSignal ventFixtureInputWire.toJson with
  | none => false
  | some output => (decodeSignalOutput output.toJson == some output)

/-- ⚑ The two games are NOT settling the same run: their inputs differ and so do their
receipts.  Without this, a vent fixture that silently fell through to the Signal arm
would look exactly like a success. -/
def check_vent_and_signal_are_different_runs : Bool :=
  decide (ventFixtureInputWire.toJson ≠ fixtureInputWire.toJson) &&
  (match processSignal ventFixtureInputWire.toJson, processSignal fixtureInputWire.toJson with
   | some vent, some signal => decide (vent.receipt ≠ signal.receipt)
   | _, _ => false)

/-- POLE TWO(a) — a FORGED transcript: banking twice, which the kernel's own
`openB` refuses from a terminal state. -/
def check_vent_forged_continuation_refused : Bool :=
  decide (ventForgedContinuationInputWire.toJson ≠ ventFixtureInputWire.toJson) &&
  (processSignalWire ventForgedContinuationInputWire.toJson).isNone

/-- POLE TWO(b) — a WRONG-INSTANCE claim: a slot commitment no curator published. -/
def check_vent_wrong_instance_refused : Bool :=
  decide (ventWrongInstanceInputWire.toJson ≠ ventFixtureInputWire.toJson) &&
  (processSignalWire ventWrongInstanceInputWire.toJson).isNone

/-- POLE TWO(c) — a REPLAY: the same run against an already-advanced counter. -/
def check_vent_replayed_counter_refused : Bool :=
  decide (ventReplayedCounterInputWire.toJson ≠ ventFixtureInputWire.toJson) &&
  (processSignalWire ventReplayedCounterInputWire.toJson).isNone

/-- POLE TWO(d) — a request naming a mission its own config does not carry. -/
def check_vent_wrong_mission_refused : Bool :=
  decide (ventWrongMissionInputWire.toJson ≠ ventFixtureInputWire.toJson) &&
  (processSignalWire ventWrongMissionInputWire.toJson).isNone

/-- ⚑ The tag is LOAD-BEARING, not decorative: retagging the accepted vent bytes as
`signal-triangulation` — changing nothing else — must refuse, or the tag is a comment.
⚠ The mutation is asserted present first; `replacen` of a string that has left the
fixture is exactly how an adversary stops adversing. -/
def ventRetaggedBytes : String :=
  ventFixtureInputWire.toJson.replace
    "{\"game\":\"vent-crawl\"" "{\"game\":\"signal-triangulation\""

def check_vent_retagged_as_signal_refused : Bool :=
  decide (ventRetaggedBytes ≠ ventFixtureInputWire.toJson) &&
  (processSignalWire ventRetaggedBytes).isNone

/-- And the converse: the Signal fixture retagged as Vent Crawl refuses too. -/
def signalRetaggedBytes : String :=
  fixtureInputWire.toJson.replace
    "{\"game\":\"signal-triangulation\"" "{\"game\":\"vent-crawl\""

def check_signal_retagged_as_vent_refused : Bool :=
  decide (signalRetaggedBytes ≠ fixtureInputWire.toJson) &&
  (processSignalWire signalRetaggedBytes).isNone

/-- (Pinned `= true` in `NetworkJudgeFixtures`.) -/
def check_fixture_unbound_run_seed_refused : Bool :=
  (processSignalWire unboundSeedInputWire.toJson).isNone

theorem fixture_processSignalWire_success :
    check_fixture_processSignalWire_success = true := by native_decide

theorem fixture_signalJudgeFFI_success :
    check_fixture_signalJudgeFFI_success = true := by native_decide

theorem fixture_signalJudgeFFI_malformed_refused :
    check_fixture_signalJudgeFFI_malformed_refused = true := by native_decide

theorem fixture_verifySignalTransition_success :
    check_fixture_verifySignalTransition_success = true := by native_decide

theorem fixture_incomplete_canon_output_refused :
    check_fixture_incomplete_canon_output_refused = true := by native_decide

theorem fixture_wrong_player_refused :
    check_fixture_wrong_player_refused = true := by native_decide

theorem fixture_wrong_config_refused :
    check_fixture_wrong_config_refused = true := by native_decide

theorem fixture_wrong_current_counter_refused :
    check_fixture_wrong_current_counter_refused = true := by native_decide

theorem fixture_stale_counter_refused :
    check_fixture_stale_counter_refused = true := by native_decide

theorem fixture_wrong_action_refused :
    check_fixture_wrong_action_refused = true := by native_decide

theorem fixture_multiple_actions_refused :
    check_fixture_multiple_actions_refused = true := by native_decide

theorem fixture_stale_revision_refused :
    check_fixture_stale_revision_refused = true := by native_decide

theorem fixture_replay_against_successor_refused :
    check_fixture_replay_against_successor_refused = true := by native_decide

theorem fixture_swapped_slot_secret_refused :
    check_fixture_swapped_slot_secret_refused = true := by native_decide

theorem fixture_wrong_slot_commitment_refused :
    check_fixture_wrong_slot_commitment_refused = true := by native_decide

theorem fixture_wrong_claimed_slot_refused :
    check_fixture_wrong_claimed_slot_refused = true := by native_decide

theorem fixture_unbound_run_seed_refused :
    check_fixture_unbound_run_seed_refused = true := by native_decide

/-! ## ⚑ THE SECOND GAME — measured 2026-08-09, all nine `true`

These run a real Vent Crawl transcript through `processSignalWire`, the body of
`@[export dregg_poa_signal_judge]`.  They are the evidence that this boundary settles
more than one game; every one of them was EVALUATED before it was written down.

⚠ They are `native_decide` for the same reason the Signal pins are: `admissionChecks`
re-derives the run seed with `HiddenInstance.runSeedFor`, a Poseidon2 sponge the kernel
cannot reduce (47.6 GB / 68 min, measured).  `#assert_compiled` records that as a
confession, not a certificate. -/

theorem vent_fixture_settles : check_vent_fixture_settles = true := by native_decide

theorem vent_output_is_canonical : check_vent_output_is_canonical = true := by native_decide

theorem vent_and_signal_are_different_runs :
    check_vent_and_signal_are_different_runs = true := by native_decide

theorem vent_forged_continuation_refused :
    check_vent_forged_continuation_refused = true := by native_decide

theorem vent_wrong_instance_refused :
    check_vent_wrong_instance_refused = true := by native_decide

theorem vent_replayed_counter_refused :
    check_vent_replayed_counter_refused = true := by native_decide

theorem vent_wrong_mission_refused :
    check_vent_wrong_mission_refused = true := by native_decide

theorem vent_retagged_as_signal_refused :
    check_vent_retagged_as_signal_refused = true := by native_decide

theorem signal_retagged_as_vent_refused :
    check_signal_retagged_as_vent_refused = true := by native_decide

#assert_compiled fixture_processSignalWire_success
#assert_compiled fixture_signalJudgeFFI_success
#assert_compiled fixture_signalJudgeFFI_malformed_refused
#assert_compiled fixture_verifySignalTransition_success
#assert_compiled fixture_incomplete_canon_output_refused
#assert_compiled fixture_wrong_player_refused
#assert_compiled fixture_wrong_config_refused
#assert_compiled fixture_wrong_current_counter_refused
#assert_compiled fixture_stale_counter_refused
#assert_compiled fixture_wrong_action_refused
#assert_compiled fixture_multiple_actions_refused
#assert_compiled fixture_stale_revision_refused
#assert_compiled fixture_replay_against_successor_refused
#assert_compiled fixture_swapped_slot_secret_refused
#assert_compiled fixture_wrong_slot_commitment_refused
#assert_compiled fixture_wrong_claimed_slot_refused
#assert_compiled fixture_unbound_run_seed_refused
#assert_compiled vent_fixture_settles
#assert_compiled vent_output_is_canonical
#assert_compiled vent_and_signal_are_different_runs
#assert_compiled vent_forged_continuation_refused
#assert_compiled vent_wrong_instance_refused
#assert_compiled vent_replayed_counter_refused
#assert_compiled vent_wrong_mission_refused
#assert_compiled vent_retagged_as_signal_refused
#assert_compiled signal_retagged_as_vent_refused

end Dregg2.Games.PathOfAngels.NetworkJudge
