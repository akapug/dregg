/-
# Vent Crawl — the measured-design EVALUATION, out of the crypto archive's build

`VentCrawl.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its measured design properties ran twenty `native_decide` evaluations at
elaboration — the 51-state parametric closure, the per-vein family census, the played-out
lines, and the two Poseidon2 sentinel fixtures — so any game-fixture regression was a hard
failure of every Rust proving target in the workspace (the compilation-unit coupling the
stale-fixture outage measured). The properties' STATEMENTS remain in `VentCrawl.lean` as
evaluation-free `check_* : Bool` definitions over `stepB`/`replayB`/`rowFor`; THIS module is
where they are RUN. It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

⚠ The two sentinel pins at the bottom evaluate Poseidon2 sponges.  That is exactly why they
are HERE and why they are `native_decide`: `Poseidon2BabyBearW16.perm` reduces exponentially
under the elaborator, and the compiled evaluator is the only thing ever asked to run it.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

Named residue in the parent: NONE — no construction in `VentCrawl.lean` consumes a
`native_decide` proof as data, so every pin moved.
-/
import Dregg2.Games.PathOfAngels.VentCrawl

namespace Dregg2.Games.PathOfAngels.VentCrawl

set_option autoImplicit false
open Dregg2.Games.PathOfAngels

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

def parametricRowCount : Nat := parametricStates.length * allActions.length

/-- ⚑ **The table is closed.**  Every successor any row names is a state the
descriptor declares, so a client can never be handed an id it does not have.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_parametric_closure_is_closed : Bool :=
  parametricStates.all (fun s =>
    allActions.all (fun a =>
      (rowSuccessors s a).all (fun n => parametricStates.contains n)))

/-- (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_parametric_states_nodup : Bool :=
  decide (parametricStates.eraseDups = parametricStates)

/-- (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_initial_state_is_declared : Bool := parametricStates.contains initialState

/-- The emitted shape, so the descriptor's size is a number a reader has before
they open the file.  ⚠ 51 states is SMALL and it is meant to be — see the
parameter table in the docblock for what each axis buys.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_parametric_shape_is_measured : Bool :=
  decide (parametricStates.length = 51) && decide (allActions.length = 2) &&
  decide (parametricRowCount = 102)

/-- ⚑ **The table really consults the day.**  Some rows are wagers with more than
one haul, so the gate's "every transition is deterministic and the instance
cannot affect play" failure cannot fire. -/
def branchingWagerCount : Nat :=
  (parametricStates.filter (fun s =>
    match rowFor s Action.crawl with
    | .wager _ _ hauls => 1 < (hauls.map Prod.snd).eraseDups.length
    | _ => false)).length

/-- (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_the_table_consults_the_day : Bool := decide (0 < branchingWagerCount)

/-- ⚑ **Every declared refusal reason fires somewhere reachable.**  A sibling game
declared four reasons and reached two; this is the check that says all three of
these are real. (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_every_declared_reason_fires : Bool :=
  declaredReasons.all (fun r =>
    parametricStates.any (fun s =>
      allActions.any (fun a =>
        match rowFor s a with
        | .refuse r' => r' == r
        | _ => false)))

/-- And nothing else fires: the reasons the table actually carries are exactly
the three declared.  Without this, `every_declared_reason_fires` would be one
half of a vocabulary check. (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_no_undeclared_reason_fires : Bool :=
  parametricStates.all (fun s =>
    allActions.all (fun a =>
      match rowFor s a with
      | .refuse r => declaredReasons.contains r
      | _ => true))

def veinSuccessors (v : Vein) (s : State) : List State :=
  allActions.flatMap (fun a =>
    if openB s a then
      match a with
      | .bank => [bankSuccessor s]
      | .crawl => [floodSuccessor s, haulSuccessor v s]
    else [])

def veinReachableWithin (v : Vein) : Nat → List State
  | 0 => [initialState]
  | fuel + 1 =>
      let prior := veinReachableWithin v fuel
      (prior ++ prior.flatMap (veinSuccessors v)).eraseDups

def veinReachable (v : Vein) : List State := veinReachableWithin v (ACTION_LIMIT + 1)

/-- States on this vein where both verbs are open — the real decision points. -/
def veinDecisionCount (v : Vein) : Nat :=
  ((veinReachable v).filter (fun s =>
    openB s Action.crawl && openB s Action.bank)).length

def veinDrownCount (v : Vein) : Nat :=
  ((veinReachable v).filter (fun s => decide (s.outcome = Outcome.drowned))).length

def familyTotal (f : Vein → Nat) : Nat :=
  allVeins.foldl (fun acc v => acc + f v) 0

/-- ⚑ **The measured shape of the family.**  These are the numbers
`scripts/poa-design-gate.py` must independently arrive at by simulating the
emitted descriptor; they are stated here so a disagreement is loud.  A pin
against its own definition is decoration — this is one of two sources.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_family_shape_is_measured : Bool :=
  decide (familyTotal (fun v => (veinReachable v).length) = 136) &&
  decide (familyTotal veinDecisionCount = 40) &&
  decide (familyTotal veinDrownCount = 40)

/-- ⚑ **Every vein can be crawled to the bottom and every vein can drown you.**
No draw is a dead day and no draw is a safe one.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_every_vein_forks : Bool :=
  allVeins.all (fun v => decide (0 < veinDecisionCount v)) &&
  allVeins.all (fun v => decide (0 < veinDrownCount v))

def playOut (v : Vein) (t : FloodTape) (acts : List Action) : Option State :=
  replayB v t initialState acts

/-- Bank immediately: the mouth cache and nothing else.  It is legal, it is
always safe, and it is what the game has to make look foolish. -/
def timidLine : List Action := [.bank]

/-- Down to rung 3 and out — the line that buys the answer and then leaves. -/
def scoutLine : List Action := [.crawl, .crawl, .bank]

/-- ⚑ **On a calm tape every line banks, and the deepest one banks the most.**
The tape is what decides; the vein is what it is worth.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_a_calm_tape_rewards_the_deep_line : Bool :=
  allVeins.all (fun v =>
    match playOut v calmTape greedLine, playOut v calmTape timidLine with
    | some deep, some shallow =>
        decide (deep.outcome = Outcome.banked) &&
        decide (shallow.outcome = Outcome.banked) &&
        decide (shallow.carried < deep.carried)
    | _, _ => false)

/-- ⚑ **A tape that runs against you takes the very first crawl.**  Rung 2 is
1-in-8 and this is that one: on every vein, because the vein is what a rung is
WORTH and the tape is what it COSTS. -/
def foulTape : FloodTape :=
  { r1 := ⟨0, by decide⟩, r2 := ⟨0, by decide⟩, r3 := ⟨0, by decide⟩
    r4 := ⟨0, by decide⟩, r5 := ⟨0, by decide⟩, r6 := ⟨0, by decide⟩ }

/-- (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_a_foul_tape_drowns_the_first_crawl : Bool :=
  allVeins.all (fun v =>
    match playOut v foulTape [Action.crawl] with
    | some s =>
        decide (s.outcome = Outcome.drowned) && decide (s.carried = 0) &&
        decide (s.depth = 2)
    | none => false)

/-- ⚑ **And a drowned run cannot keep going.**  Every continuation past the water
is refused, so a drowning is always the last thing in a transcript and a receipt
cannot report a crawler who kept crawling.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_a_drowned_run_cannot_keep_going : Bool :=
  allVeins.all (fun v =>
    (playOut v foulTape [Action.crawl, Action.crawl]).isNone &&
    (playOut v foulTape [Action.crawl, Action.bank]).isNone)

/-- Three crawls and no bank: the line that goes looking for the water. -/
def riskyLine : List Action := [.crawl, .crawl, .crawl]

/-- ⚑ **Same tape, same first two rungs, opposite endings.**  The crawler who
banked out of rung 3 has a full sling; the one who took the fourth rung has
nothing.  ONE ACTION apart, on identical information — this is the whole game in
one theorem, and it holds on all four veins because the water does not care what
the shaft is paying. -/
def middlingTape : FloodTape :=
  { r1 := ⟨7, by decide⟩, r2 := ⟨7, by decide⟩, r3 := ⟨7, by decide⟩
    r4 := ⟨2, by decide⟩, r5 := ⟨0, by decide⟩, r6 := ⟨0, by decide⟩ }

/-- (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_the_scout_comes_home_where_the_third_crawl_drowns : Bool :=
  allVeins.all (fun v =>
    match playOut v middlingTape scoutLine, playOut v middlingTape riskyLine with
    | some scout, some risky =>
        decide (scout.outcome = Outcome.banked) && decide (0 < scout.carried) &&
        decide (scout.depth = 3) &&
        decide (risky.outcome = Outcome.drowned) && decide (risky.carried = 0) &&
        decide (risky.depth = 4)
    | _, _ => false)

/-- ⚑ **Ids separate states.** (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_state_ids_are_distinct : Bool :=
  decide ((parametricStates.map stateId).eraseDups.length = parametricStates.length)

/-- ⚑ **A drowned run is always worth submitting.**  Every drowning a run can
actually reach — the shallowest is rung 2 — pays at least one `intel`, so the
carrying turn is never spent for nothing.  This is the residual the consolation
exists for and it survives the discount; a pricing that took it to zero would
have bought the tradeoff by making the public record blind to drownings.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_a_drowned_run_is_always_worth_submitting : Bool :=
  parametricStates.all (fun s =>
    !decide (s.outcome = Outcome.drowned) ||
      decide (0 < mapDrowned s.depth))

private def taggedDigest (tag : List Nat) : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match tag[i.val]? with
    | some n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
    | none => ⟨0, by decide⟩
  length_eq := by simp

private def fixtureSecret : HiddenInstance.SlotSecret := ⟨taggedDigest [83, 69, 67, 45, 86]⟩
private def fixtureCrawler : Digest32 := taggedDigest [67, 82, 65, 87, 76]
private def fixtureOtherCrawler : Digest32 := taggedDigest [77, 65, 84, 69]
private def fixtureSlot : EpochId := ⟨11⟩

private def fixtureContext : HiddenInstance.MissionContext where
  missionId := ⟨9⟩
  epoch := ⟨11⟩
  federationId := taggedDigest [70, 69, 68]
  contentSession := taggedDigest [83, 69, 83, 83]

/-- The SAME night, asked by a different mission.  Everything the ship draw reads
— slot, federation, content session — is identical; only the mission id and epoch
differ, and those are exactly the two lanes `DayWater.shipHeaderBlock` drops. -/
private def fixtureOtherMission : HiddenInstance.MissionContext :=
  { fixtureContext with missionId := ⟨5⟩, epoch := ⟨11⟩ }

/-- ⚑ **The day's table is not any crawler's stream.**  Two crawlers in the slot
draw two different tapes, and neither of them is the seed the vein came off.
(Pinned `= true` in `VentCrawlFixtures`.) -/
def check_the_day_table_is_not_a_player_stream : Bool :=
  decide (DayWater.shipSeedFor fixtureSecret fixtureSlot
      fixtureContext.federationId fixtureContext.contentSession ≠
    HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureCrawler⟩
      fixtureContext) &&
  decide (DayWater.shipSeedFor fixtureSecret fixtureSlot
      fixtureContext.federationId fixtureContext.contentSession ≠
    HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureOtherCrawler⟩
      fixtureContext) &&
  decide (HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureCrawler⟩
      fixtureContext ≠
    HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureOtherCrawler⟩
      fixtureContext)

/-- ⚑ **A mission-scoped day WOULD have differed, and that is the whole reason
the seam moved.**

⚠ Read what this does NOT check, because the obvious version is a tautology and
was written first.  "Two missions share one night" is a fact about
`DayWater.shipDayFor`'s SIGNATURE — it takes no mission, so there is no mission
to vary — and a fixture that fed it `fixtureContext.federationId` beside
`fixtureOtherMission.federationId` would be comparing one closed expression with
itself, exactly the `x = x` that
`check_two_crawlers_share_a_vein_and_not_a_tape` was corrected for on
2026-08-09.

What IS contingent is the counterfactual: the derivation the ship draw REPLACED
separates two missions that differ in nothing but their id.  `fixtureContext` and
`fixtureOtherMission` share a secret, a slot, a federation and a content session;
the deleted `daySeedFor` routed all of that through
`HiddenInstance.headerBlock`, whose lane 3 is the mission id, and this is that
difference on a real sponge.  (Pinned `= true` in `VentCrawlFixtures`.) -/
def check_a_mission_scoped_day_would_have_differed : Bool :=
  decide (HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureCrawler⟩
      fixtureContext ≠
    HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureCrawler⟩
      fixtureOtherMission) &&
  decide (fixtureContext.federationId = fixtureOtherMission.federationId) &&
  decide (fixtureContext.contentSession = fixtureOtherMission.contentSession)

/-- ⚑ **Two crawlers on one day draw two tapes.**  The vein they share; the water
they do not.  This is what makes a neighbour's drowning news about the day and
not news about the crawler.

⚠ The first conjunct was a TAUTOLOGY until 2026-08-09: it read
`veinFromDaySeed (daySeedFor …) = veinFromDaySeed (daySeedFor …)`, the same
closed expression on both sides, so it was `x = x` and would have stayed `true`
if the day draw had been replaced by a constant.  "Two crawlers share a vein" was
never checkable here anyway — `daySeedFor` takes no player, so it is a fact about
the SIGNATURE.  The conjunct now carries the fact that IS contingent and IS new:
the day's water moves the vein, on the same seam.  (Pinned `= true` in
`VentCrawlFixtures`.) -/
def check_two_crawlers_share_a_vein_and_not_a_tape : Bool :=
  decide (veinFromShipDay
      { bilge := true, seam := (DayWater.shipDayFor fixtureSecret fixtureSlot
          fixtureContext.federationId fixtureContext.contentSession).seam } ≠
    veinFromShipDay
      { bilge := false, seam := (DayWater.shipDayFor fixtureSecret fixtureSlot
          fixtureContext.federationId fixtureContext.contentSession).seam }) &&
  decide (floodTapeFromRunSeed
      (HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureCrawler⟩
        fixtureContext) ≠
    floodTapeFromRunSeed
      (HiddenInstance.runSeedFor ⟨fixtureSecret, fixtureSlot, fixtureOtherCrawler⟩
        fixtureContext))

#assert_axioms allVeins_length

theorem parametric_closure_is_closed :
    check_parametric_closure_is_closed = true := by native_decide

theorem parametric_states_nodup :
    check_parametric_states_nodup = true := by native_decide

theorem initial_state_is_declared :
    check_initial_state_is_declared = true := by native_decide

theorem parametric_shape_is_measured :
    check_parametric_shape_is_measured = true := by native_decide

theorem the_table_consults_the_day :
    check_the_table_consults_the_day = true := by native_decide

theorem every_declared_reason_fires :
    check_every_declared_reason_fires = true := by native_decide

theorem no_undeclared_reason_fires :
    check_no_undeclared_reason_fires = true := by native_decide

theorem family_shape_is_measured :
    check_family_shape_is_measured = true := by native_decide

theorem a_drowned_run_is_always_worth_submitting :
    check_a_drowned_run_is_always_worth_submitting = true := by native_decide

theorem every_vein_forks :
    check_every_vein_forks = true := by native_decide

theorem state_ids_are_distinct :
    check_state_ids_are_distinct = true := by native_decide

theorem a_calm_tape_rewards_the_deep_line :
    check_a_calm_tape_rewards_the_deep_line = true := by native_decide

theorem a_foul_tape_drowns_the_first_crawl :
    check_a_foul_tape_drowns_the_first_crawl = true := by native_decide

theorem a_drowned_run_cannot_keep_going :
    check_a_drowned_run_cannot_keep_going = true := by native_decide

theorem the_scout_comes_home_where_the_third_crawl_drowns :
    check_the_scout_comes_home_where_the_third_crawl_drowns = true := by native_decide

theorem the_day_table_is_not_a_player_stream :
    check_the_day_table_is_not_a_player_stream = true := by native_decide

theorem two_crawlers_share_a_vein_and_not_a_tape :
    check_two_crawlers_share_a_vein_and_not_a_tape = true := by native_decide

/-- ⚑ The counterfactual the seam moved for: two missions in one slot, alike in
secret, slot, federation and content session, got DIFFERENT day seeds under the
deleted `daySeedFor`, because `HiddenInstance.headerBlock` carries the mission id
in lane 3.  See the ⚠ on the check for the tautology this deliberately is not. -/
theorem a_mission_scoped_day_would_have_differed :
    check_a_mission_scoped_day_would_have_differed = true := by native_decide

#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled parametric_shape_is_measured
#assert_compiled the_table_consults_the_day
#assert_compiled every_declared_reason_fires
#assert_compiled no_undeclared_reason_fires
#assert_compiled family_shape_is_measured
#assert_compiled a_drowned_run_is_always_worth_submitting
#assert_compiled every_vein_forks
#assert_compiled state_ids_are_distinct
#assert_compiled a_calm_tape_rewards_the_deep_line
#assert_compiled a_foul_tape_drowns_the_first_crawl
#assert_compiled a_drowned_run_cannot_keep_going
#assert_compiled the_scout_comes_home_where_the_third_crawl_drowns
#assert_compiled the_day_table_is_not_a_player_stream
#assert_compiled two_crawlers_share_a_vein_and_not_a_tape
#assert_compiled a_mission_scoped_day_would_have_differed

end Dregg2.Games.PathOfAngels.VentCrawl
