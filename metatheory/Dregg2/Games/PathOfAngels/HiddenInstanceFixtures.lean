/-
# HiddenInstance — the fixture EVALUATION, out of the crypto archive's build

`HiddenInstance.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root),
and until 2026-08-08 its seven fixtures ran `native_decide` at elaboration — every one of
them a Poseidon2 sponge draw — so a game-fixture regression was a hard failure of every
Rust proving target in the workspace (the compilation-unit coupling the stale-fixture
outage measured).  The STATEMENTS remain in `HiddenInstance.lean` as evaluation-free
`check_* : Bool` definitions, beside the private secrets and mission they are stated over;
THIS module is where they are RUN.  It is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

⚠ The sponge cost is real and it is now paid HERE.  `commit`, `runSeedFor` and
`practiceRunSeed` are `@[irreducible]` because a live draw through Lean's ELABORATOR cost
47.6 GB and 68 minutes on one file; `native_decide` runs the COMPILED function, which
ignores irreducibility and is cheap.  Do not replace any pin below with `decide` — that
would hand the kernel the reduction bomb.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  There is no residue: `HiddenInstance` builds no
proof-carrying structure that needs a drawn seed at elaboration.
-/
import Dregg2.Games.PathOfAngels.HiddenInstance

namespace Dregg2.Games.PathOfAngels.HiddenInstance

set_option autoImplicit false
open Dregg2.Games.PathOfAngels
open Dregg2.Circuit.Poseidon2BabyBearW16

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- The rehearsal seed a browser draws for ITSELF.  There is no secret and no
slot: a client picks `clientSeed`, the `practice` tag separates the stream, and
the resulting instance is a real instance of the same family that no judge will
ever score. -/
@[irreducible] def practiceRunSeed (clientSeed : Digest32) (ctx : MissionContext) : Digest32 :=
  digestOfStream (streamFor .practice clientSeed ⟨0⟩ ctx clientSeed)

private def taggedDigest (tag : List Nat) : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match tag[i.val]? with
    | some n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
    | none => 0
  length_eq := by simp

private def fixtureFederation : Digest32 := taggedDigest [70, 69, 68, 45, 49]
private def fixtureSession : Digest32 := taggedDigest [83, 69, 83, 83, 45, 49]
private def fixtureContentRoot : Digest32 := taggedDigest [82, 79, 79, 84]
private def fixtureActivation : Digest32 := taggedDigest [65, 67, 84]
private def fixtureSourceDigest : Digest32 := taggedDigest [83, 82, 67]

private def secretA : SlotSecret := ⟨taggedDigest [83, 69, 67, 45, 65]⟩
private def secretB : SlotSecret := ⟨taggedDigest [83, 69, 67, 45, 66]⟩
private def alice : Digest32 := taggedDigest [65, 76, 73, 67, 69]
private def bob : Digest32 := taggedDigest [66, 79, 66]

private def fixtureBudget : ContributionBudget where
  intel := ⟨1, by decide⟩
  supplies := ⟨1, by decide⟩
  cohesion := ⟨1, by decide⟩
  influence := ⟨1, by decide⟩
  score := ⟨1, by decide⟩
  relics := ⟨1, by decide⟩

private def fixtureMission : MissionSpec where
  missionId := ⟨1⟩
  artifact :=
    { missionId := ⟨1⟩, artifactId := ⟨1⟩
      sourceDigest := fixtureSourceDigest, contentDigest := fixtureContentRoot }
  epoch := ⟨1⟩
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  runSeed := taggedDigest []
  budget := fixtureBudget
  allowedRelics := {⟨1⟩}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT]

private def slotSeven : EpochId := ⟨7⟩
private def slotEight : EpochId := ⟨8⟩

/-- **Binding.**  Two secrets, one slot, two commitments.  A curator cannot
publish one commitment and open it to a different secret without finding a sponge
collision. (Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_commit_separates_secrets : Bool :=
  decide (commit secretA slotSeven ≠ commit secretB slotSeven)

/-- The commitment is slot-scoped: reusing a secret across slots does not reuse
its commitment. (Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_commit_separates_slots : Bool :=
  decide (commit secretA slotSeven ≠ commit secretA slotEight)

/-- **The descriptor does not determine the instance.**  Everything an artifact
carries is fixed here — mission, federation, content session, slot, player — and
the run seed still moves when the secret does.  This is the statement the old
`signalTarget_literal` could not make, because there the seed WAS the artifact.
(Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_published_context_does_not_determine_the_run_seed : Bool :=
  decide (runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) ≠
    runSeedFor ⟨secretB, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission))

/-- **Per player.**  Two players in the same slot, under the same secret, draw
different instances, so a solved run tells its neighbour nothing.  The cost of
this choice is that two scores are draws from one distribution rather than
attempts at one puzzle; the benefit is that the first finisher cannot hand the
answer to the rest of the slot. (Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_two_players_draw_different_instances : Bool :=
  decide (runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) ≠
    runSeedFor ⟨secretA, slotSeven, bob⟩ (MissionContext.ofMission fixtureMission))

/-- **Per slot.**  The same player in two slots draws two instances, so yesterday
does not answer today. (Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_two_slots_draw_different_instances : Bool :=
  decide (runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) ≠
    runSeedFor ⟨secretA, slotEight, alice⟩ (MissionContext.ofMission fixtureMission))

/-- **Practice is not the live game.**  Handing the practice draw the slot secret
itself — the most favourable possible confusion — still does not reproduce a
judged seed, because the purpose tag is in the preimage.
(Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_practice_is_not_judged : Bool :=
  decide (practiceRunSeed secretA.value (MissionContext.ofMission fixtureMission) ≠
    runSeedFor ⟨secretA, ⟨0⟩, secretA.value⟩ (MissionContext.ofMission fixtureMission))

/-- The commitment does not repeat the run seed: publishing it is not publishing
a value one draw away from the instance.
(Pinned `= true` in `HiddenInstanceFixtures`.) -/
def check_commitment_is_not_the_seed : Bool :=
  decide (commit secretA slotSeven ≠
    runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission))

theorem commit_separates_secrets : check_commit_separates_secrets = true := by native_decide

theorem commit_separates_slots : check_commit_separates_slots = true := by native_decide

theorem published_context_does_not_determine_the_run_seed :
    check_published_context_does_not_determine_the_run_seed = true := by native_decide

theorem two_players_draw_different_instances :
    check_two_players_draw_different_instances = true := by native_decide

theorem two_slots_draw_different_instances :
    check_two_slots_draw_different_instances = true := by native_decide

theorem practice_is_not_judged : check_practice_is_not_judged = true := by native_decide

theorem commitment_is_not_the_seed : check_commitment_is_not_the_seed = true := by native_decide

#assert_compiled commit_separates_secrets
#assert_compiled commit_separates_slots
#assert_compiled published_context_does_not_determine_the_run_seed
#assert_compiled two_players_draw_different_instances
#assert_compiled two_slots_draw_different_instances
#assert_compiled practice_is_not_judged
#assert_compiled commitment_is_not_the_seed

end Dregg2.Games.PathOfAngels.HiddenInstance
