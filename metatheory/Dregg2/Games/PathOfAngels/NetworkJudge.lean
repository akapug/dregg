/-
# Path of Angels — Signal network judge

This is the first complete internal settlement evaluator for a PoA minigame.  The
node supplies one canonical `NetworkJudgeWire` value.  Lean reconstructs the complete
world, canon, active configuration, finalized carrier, and request; checks that
the configuration is the Signal program emitted by `Emit`; replays the submitted
Signal TRANSCRIPT — one to `SignalTriangulation.MAX_TURNS` actions, in the order
they were played — through `judgeActive`; applies its closed `GameEffect`; and emits
a canonical successor plus the semantic receipt.

⚑ It replayed "exactly one Signal action" until 2026-08-07, and that sentence was
true of the code (`signalActions?`, formerly `oneSignalAction?`, matched a singleton
and refused everything else).  See that definition for what it cost.

There is intentionally no Rust-shaped alternate judge in this module.  This
function becomes authoritative only when the node adapter replaces caller data
with the persisted active Canon/config and derives `FinalizedCarrier` from the
finalized SignedTurn signer and AIR-bound pre-state root.  It must never be exposed
as a public HTTP oracle accepting caller-authored authority fields.
-/
import Dregg2.Games.PathOfAngels.NetworkJudgeWire

namespace Dregg2.Games.PathOfAngels.NetworkJudge

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire

set_option autoImplicit false

/-! ## Exact active Signal projection -/

/-- Rebuild the only Signal configuration this boundary accepts.  The five
authenticated identities remain variable, and so — ⚠ NOW — does the run seed: it
is drawn per run from the committed slot secret, so the emitter cannot supply it
and this boundary carries the candidate's own.  Every other game-semantic field
still comes from the Lean emitter: mission/artifact ids, epoch, session, budget,
privacy, ballot, reward, allowed relics.  The TARGET is no longer among them,
because it is no longer a constant: it is `targetFromSeed?` of whatever live seed
`Judged.admissionChecks` proved was the derived one. -/
def emittedSignalConfig (config : SignalTriangulation.Config) :
    SignalTriangulation.Config :=
  Emit.signalConfigWith config.mission.runSeed config.target config.target_eq
    config.mission.federationId
    config.mission.artifact.sourceDigest config.mission.artifact.contentDigest
    config.mission.contentRoot config.mission.activationDigest

/-- ⚠ **The rebuild carries the candidate's OWN target, and that is not a relaxation.**
The draw is partial now, so a rebuild that re-drew would have to handle a refusal it
can never see: `Config.target_eq` already forces every configuration's target to be
the draw of its own mission's run seed, so the target component of the comparison
below was NEVER able to fail — before this change it compared `targetFromSeed s`
against a field the type defined to be `targetFromSeed s`.  This `rfl` is that
statement, and it is why nothing here needs an `Option`.

Where a CLAIMED target is actually checked against the derivation is
`SignalConfigWire.toSemantic?`, at the point the target enters from the wire — and
that check is now `some target = targetFromSeed? …`, so a wire naming a target for a
seed that draws nothing is refused rather than reinterpreted. -/
theorem emittedSignalConfig_target_was_already_forced (config : SignalTriangulation.Config) :
    (emittedSignalConfig config).target = config.target := rfl

def exactEmittedSignalConfig (config : SignalTriangulation.Config) : Bool :=
  decide (ActiveGame.configClaim (.signal config) =
    ActiveGame.configClaim (.signal (emittedSignalConfig config)))

/-- Rebuild the only Vent Crawl configuration this boundary accepts.

⚠ **TOTAL, unlike Signal's, and the difference is which hidden thing the config
holds.**  Signal's rebuild has to carry the candidate's own target because
`targetFromSeed?` is partial; Vent Crawl's per-player hidden thing is the FLOOD TAPE,
`floodTapeFromRunSeed` is total, and `Config.floods_eq` already forces it — so
`Emit.ventConfigWith` takes the live run seed and nothing else that could be chosen.

⚠ And the VEIN is absent from both sides of this comparison, which is the point: it
is not in a `Config` at all.  What the comparison does check is everything a host
could otherwise drift — mission id, artifact digests, epoch, session, budget, privacy,
ballot, the allowlist, and the deep relic. -/
def emittedVentConfig (config : VentCrawl.Config) : VentCrawl.Config :=
  Emit.ventConfigWith config.mission.runSeed
    config.mission.federationId
    config.mission.artifact.sourceDigest config.mission.artifact.contentDigest
    config.mission.contentRoot config.mission.activationDigest

def exactEmittedVentConfig (config : VentCrawl.Config) : Bool :=
  decide (ActiveGame.configClaim (.ventCrawl config) =
    ActiveGame.configClaim (.ventCrawl (emittedVentConfig config)))

/-- The one config gate, over whatever game the wire decoded to.

⚠ **The four games with no transport arm return `false`, not `true`.**  A default that
admitted them would be a config gate that stops checking the moment a fifth game is
enrolled in `Judged` and forgotten here — the failure would be that a Deck Descent run
settles against an unchecked configuration, which is the opposite of quiet.  They
cannot reach this function today (`GameConfigWire.toSemantic?` cannot produce them),
and if that changes this refuses until someone writes the arm. -/
def exactEmittedConfig : ActiveGame → Bool
  | .signal config => exactEmittedSignalConfig config
  | .ventCrawl config => exactEmittedVentConfig config
  | _ => false

theorem an_untransported_game_is_refused_by_the_config_gate
    (config : DeckDescent.Config) : exactEmittedConfig (.deckDescent config) = false := rfl

#assert_axioms an_untransported_game_is_refused_by_the_config_gate

/-- Cross-object state checks that are not game-judge concerns.  In particular,
the request must pin the state it saw, and world/canon must name the same complete
artifact population.  Strict `<` leaves room for the successor sequence/revision
inside the bounded network format. -/
def preStateChecks (input : SemanticInput) : Bool :=
  exactEmittedConfig input.game &&
  decide (input.request.missionId = input.game.mission.missionId.value) &&
  decide (input.request.expectedWorldSequence = input.world.sequence) &&
  decide (input.request.expectedCanonRevision = input.canon.revision) &&
  decide (input.world = input.canon.world) &&
  decide (input.canon.world.betaArtifacts = input.canon.known) &&
  decide (input.world.sequence < WIRE_NAT_LIMIT) &&
  decide (input.canon.revision < WIRE_NAT_LIMIT)

/-- ⚠ The three slot fields come from `input.slotState`, which is NODE state — not
from `input.request`, which is the client's.  `admissionChecks` then requires the
commitment to be the commitment OF that secret and the run seed to be the derivation
FROM it, so neither the node nor the client can name the instance after the fact. -/
def activeOf (input : SemanticInput) : ActiveRunState := {
  game := input.game
  federationId := input.canon.federationId
  contentRoot := input.canon.contentRoot
  activationDigest := input.canon.activationDigest
  contentSession := input.canon.contentSession
  contentEpoch := input.canon.contentEpoch
  slot := input.slot
  slotSecret := input.slotSecret
  slotCommitment := input.slotCommitment
  runSeed := input.game.mission.runSeed
  world := input.canon.world
  playerCounters := input.canon.playerCounters
}

/-- ⚠ `runSeed` is gone from the claim and `target` is gone from the config claim.
What a client asserts about its instance is now exactly two values it legitimately
holds — the slot it played in, and the commitment its opening showed it. -/
def claimOf (input : SemanticInput) : RunClaim := {
  config := input.game.configClaim
  federationId := input.request.federationId
  contentRoot := input.request.contentRoot
  activationDigest := input.request.activationDigest
  contentSession := input.request.contentSession
  contentEpoch := ⟨input.request.contentEpoch⟩
  slot := ⟨input.request.slot⟩
  slotCommitment := input.request.slotCommitment
  actorRoot := input.request.actorRoot
  playerKey := input.request.playerKey
  claimedPreviousPlayerCounter := input.request.previousPlayerCounter
}

/-- The submitted transcript, in the order it was played, for whatever game the
config named.

⚑ **THIS WAS `signalActions?`, AND BEFORE THAT `oneSignalAction?`.**  The one-action
version made judged Signal a single blind guess; this version's predecessor fixed that
and was still `List CodeWire → List SignalTriangulation.Action`, which is why five of
the six games `judgeActive` can score had no way in.  The decode now lives in
`NetworkJudgeWire.ActionsWire.toSemantic?` and lands directly on `Judged.SubmittedRun`,
so this boundary chooses no game: it forwards the one the config already fixed.

The empty-transcript refusal moved with it, and moved UP: it is stated once at the
wire for every game rather than once here for Signal. -/
def submittedRun? (request : SignalRequestWire) : Option SubmittedRun :=
  request.actions.toSemantic?

/-- ⚠ And the run it forwards is the game the config named — so the
`judgeAdmitted` catch-all, which returns `none` for a config/actions mismatch and is
therefore indistinguishable from a losing run, is unreachable from this boundary. -/
theorem submitted_run_is_the_configs_game {request : SignalRequestWire} {run : SubmittedRun}
    (h : submittedRun? request = some run) :
    NetworkJudgeWire.submittedRunTag? run = some request.actions.game :=
  NetworkJudgeWire.ActionsWire.toSemantic_preserves_tag h

#assert_axioms submitted_run_is_the_configs_game

/-! ## Proof-carrying settlement -/

/-- A successful settlement retains both executable evidence edges: the closed
game registry accepted the run, and Canon accepted the resulting one-shot effect.
The printable receipt is a projection of this evidence, not caller data. -/
structure Settlement where
  active : ActiveRunState
  carrier : FinalizedCarrier
  claim : RunClaim
  submitted : SubmittedRun
  judgedRun : JudgedRun
  judgeAccepted : judgeActive active carrier claim submitted = some judgedRun
  beforeCanon : CanonState
  successorCanon : CanonState
  canonApplied : applyGameEffect (.recordRun judgedRun) beforeCanon = some successorCanon

def Settlement.receipt (settlement : Settlement) : RunReceipt :=
  settlement.judgedRun.receipt

def Settlement.successorWorld (settlement : Settlement) : WorldState :=
  settlement.receipt.postWorld

/-- The complete semantic transition.  Refusal at any stage is `none`; there is
no accepted no-op and no partial Canon write. -/
def settle (input : SemanticInput) : Option Settlement :=
  if preStateChecks input then
    match submittedRun? input.request with
    | none => none
    | some submitted =>
        let active := activeOf input
        let claim := claimOf input
        match hj : judgeActive active input.carrier claim submitted with
        | none => none
        | some judgedRun =>
            match hc : applyGameEffect (.recordRun judgedRun) input.canon with
            | none => none
            | some successorCanon =>
                some {
                  active
                  carrier := input.carrier
                  claim
                  submitted
                  judgedRun
                  judgeAccepted := hj
                  beforeCanon := input.canon
                  successorCanon
                  canonApplied := hc
                }
  else none

theorem Settlement.receipt_applied (settlement : Settlement) :
    applyContribution settlement.receipt.mission settlement.receipt.contribution
      settlement.receipt.preWorld = some settlement.receipt.postWorld :=
  settlement.judgedRun.applied

theorem Settlement.canon_records_receipt (settlement : Settlement) :
    settlement.receipt.mission.artifact ∈ settlement.successorCanon.known :=
  applyGameEffect_records_beta_candidate settlement.canonApplied

theorem Settlement.canon_consumes_receipt (settlement : Settlement) :
    settlement.receipt.key ∈ settlement.successorCanon.consumedRuns :=
  applyGameEffect_consumes_counter settlement.canonApplied

theorem Settlement.counter_advances (settlement : Settlement) :
    (settlement.beforeCanon.playerCounters.lookup settlement.receipt.counterKey).val =
        settlement.receipt.previousPlayerCounter ∧
      (settlement.successorCanon.playerCounters.lookup settlement.receipt.counterKey).val =
        settlement.receipt.playerCounter :=
  applyGameEffect_advances_player_counter settlement.canonApplied

theorem Settlement.successor_world_chained (settlement : Settlement) :
    settlement.successorCanon.world = settlement.successorWorld :=
  (applyGameEffect_chains_world settlement.canonApplied).2

theorem Settlement.replay_refused (settlement : Settlement) :
    applyGameEffect (.recordRun settlement.judgedRun) settlement.successorCanon = none :=
  applyGameEffect_same_counter_replay_refused settlement.canonApplied

/-! ## Canonical network entry point -/

def canonicalOutput? (output : SignalOutputWire) : Option SignalOutputWire :=
  if decodeSignalOutput output.toJson = some output then some output else none

theorem canonicalOutput_sound {output accepted : SignalOutputWire}
    (h : canonicalOutput? output = some accepted) :
    accepted = output ∧ decodeSignalOutput accepted.toJson = some accepted := by
  simp only [canonicalOutput?] at h
  split at h
  · rename_i decoded
    cases h
    exact ⟨rfl, decoded⟩
  · contradiction

def Settlement.toWire? (settlement : Settlement) : Option SignalOutputWire := do
  let successorCanon ← CanonStateWire.ofSemantic? settlement.successorCanon
  canonicalOutput? {
    receipt := SignalReceiptWire.ofSemantic settlement.receipt
    successorWorld := WorldStateWire.ofSemantic settlement.successorWorld
    successorCanon
  }

theorem Settlement.toWire_decodes {settlement : Settlement} {output : SignalOutputWire}
    (h : settlement.toWire? = some output) :
    decodeSignalOutput output.toJson = some output := by
  cases hc : CanonStateWire.ofSemantic? settlement.successorCanon with
  | none => simp [Settlement.toWire?, hc] at h
  | some successorCanon =>
      have accepted : canonicalOutput? {
          receipt := SignalReceiptWire.ofSemantic settlement.receipt
          successorWorld := WorldStateWire.ofSemantic settlement.successorWorld
          successorCanon
        } = some output := by
        simpa [Settlement.toWire?, hc] using h
      exact (canonicalOutput_sound accepted).2

/-- Typed-output form of the gate, useful to state semantic properties without
parsing its own freshly encoded result. -/
def processSignal (bytes : String) : Option SignalOutputWire := do
  let wire ← decodeSignalInput bytes
  let input ← wire.toSemantic?
  let settlement ← settle input
  settlement.toWire?

/-- Internal Signal evaluator.  Decode, semantic reconstruction, exact replay,
Canon transition, and output encoding are one fail-closed composition.  The
authority-origin precondition is described in the module header. -/
def processSignalWire (bytes : String) : Option String :=
  (processSignal bytes).map SignalOutputWire.toJson

/-- **`@[export dregg_poa_signal_judge]`** — the internal evaluator boundary.
`""` is the fail-closed refusal sentinel; every accepted result is the nonempty,
canonical `POA-SIGNAL-OUT-1` JSON emitted by `processSignalWire` itself.

This export authenticates nothing outside the supplied semantic carrier.  A host
must derive that carrier from finalized authority before calling it; in
particular this is not a public oracle for caller-authored state. -/
@[export dregg_poa_signal_judge]
def signalJudgeFFI (bytes : String) : String :=
  (processSignalWire bytes).getD ""

theorem signalJudgeFFI_success_iff {inputBytes outputBytes : String}
    (output_nonempty : outputBytes ≠ "") :
    signalJudgeFFI inputBytes = outputBytes ↔
      processSignalWire inputBytes = some outputBytes := by
  cases processed : processSignalWire inputBytes with
  | none =>
      constructor
      · intro accepted
        have empty : "" = outputBytes := by
          simpa [signalJudgeFFI, processed] using accepted
        exact (output_nonempty empty.symm).elim
      · intro accepted
        contradiction
  | some output =>
      simp [signalJudgeFFI, processed]

theorem processSignal_output_decodes {inputBytes : String} {output : SignalOutputWire}
    (h : processSignal inputBytes = some output) :
    decodeSignalOutput output.toJson = some output := by
  cases hdecode : decodeSignalInput inputBytes with
  | none => simp [processSignal, hdecode] at h
  | some wire =>
      cases hsemantic : wire.toSemantic? with
      | none => simp [processSignal, hdecode, hsemantic] at h
      | some input =>
          cases hsettle : settle input with
          | none => simp [processSignal, hdecode, hsemantic, hsettle] at h
          | some settlement =>
              have hwire : settlement.toWire? = some output := by
                simpa [processSignal, hdecode, hsemantic, hsettle] using h
              exact Settlement.toWire_decodes hwire

theorem processSignalWire_output_is_lean_encoded {inputBytes outputBytes : String}
    (h : processSignalWire inputBytes = some outputBytes) :
    ∃ output, processSignal inputBytes = some output ∧ output.toJson = outputBytes := by
  unfold processSignalWire at h
  cases hp : processSignal inputBytes with
  | none => simp [hp] at h
  | some output =>
      simp [hp] at h
      exact ⟨output, rfl, h⟩

theorem processSignalWire_output_decodes {inputBytes outputBytes : String}
    (h : processSignalWire inputBytes = some outputBytes) :
    ∃ output, decodeSignalOutput outputBytes = some output := by
  obtain ⟨output, processed, encoded⟩ :=
    processSignalWire_output_is_lean_encoded h
  refine ⟨output, ?_⟩
  rw [← encoded]
  exact processSignal_output_decodes processed

/-- Authoritative output verification requires the original input: recompute the
entire strict decode → Signal judge → Canon transition, require byte equality,
then reconstruct the already-matched output for inspection.  Standalone
`decodeSignalOutputSemantic` is intentionally not a substitute for this check. -/
def verifySignalTransition (inputBytes outputBytes : String) : Option SemanticOutput := do
  let expectedBytes ← processSignalWire inputBytes
  if expectedBytes = outputBytes then
    decodeSignalOutputSemantic outputBytes
  else none

/-! The concrete success/refusal fixtures and all 26 compiled pins live in
`NetworkJudgeFixtures.lean`, rooted in `PathOfAngelsGuards`. Their closed `Bool`
definitions must live there too: although elaboration does not evaluate a `def`
body, native module initialization eagerly computes these closed values.
The runtime judge and its general soundness theorems remain in this module. -/

#assert_axioms Settlement.receipt_applied
#assert_axioms Settlement.canon_records_receipt
#assert_axioms Settlement.canon_consumes_receipt
#assert_axioms Settlement.counter_advances
#assert_axioms Settlement.successor_world_chained
#assert_axioms Settlement.replay_refused
#assert_axioms canonicalOutput_sound
#assert_axioms Settlement.toWire_decodes
#assert_axioms processSignal_output_decodes
#assert_axioms processSignalWire_output_is_lean_encoded
#assert_axioms processSignalWire_output_decodes
#assert_axioms signalJudgeFFI_success_iff

end Dregg2.Games.PathOfAngels.NetworkJudge
