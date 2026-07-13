/-
# Dregg2.Circuit.ChainStepNonTautology — the E-guarantee, de-tautologized.

**Survey finding #2 (the E-guarantee tautology), addressed head-on.**

`Distributed.HistoryAggregation.ChainStep` (line 172) bundles the executor witness
`commits : recCexec pre turn = some post` as a STRUCTURE FIELD. Consequently:

  * `HistoryAggregation.every_turn_executed_correctly` (line 347) is `fun s _ => s.commits` —
    provable for ANY `List ChainStep` whatsoever, with no verification hypothesis in sight;
  * the `every_turn` field of `RecursiveAggregation.AggregateAttests` (line 187) therefore adds
    NOTHING an adversary must fear: "every turn executed correctly" is baked into the TYPE of the
    steps list, not extracted from `verify agg.root`. We EXHIBIT this below
    (`every_turn_is_free`, `every_turn_says_nothing`): the conjunct is logically `True`.

  (To be fair to the original design: `ChainStep` is the SPEC-side interpretation the soundness
  hypotheses pair proofs against — the real content of `AggregateAttests` was always in the OTHER
  three fields, the two public root pins and `ChainBound`. But the E-guarantee prose headlines
  "every turn executed correctly", and THAT conjunct is the free one.)

Meanwhile the REAL adversarial statement — `Crypto.LightClientUC.unfoolable_of_floor` (line 159)
/ `fooling_breaks_floor` (line 170): a no-secret light client can only be made to ACCEPT a
non-produced state by BREAKING the named crypto floor (STARK/Fiat-Shamir extractability + the
CR binding) — is pinned in `AssuranceCase` (§E, `#assert_axioms` at :704–:705) but NEVER CONJOINED
into the deployed E-statement (`unfoolability_guarantee`, AssuranceCase:666, which conjoins only
`AggregateAttests` + conservation).

**The deliverable (`light_client_E_genuine`).** ONE statement conjoining exactly the genuine,
non-free content:

  (1) the public GENESIS root pin      (`AggregateAttests.genesis_pinned`),
  (2) the public FINAL root pin        (`AggregateAttests.final_is_genuine_fold`),
  (3) the `ChainBound` ordering tooth  (`AggregateAttests.ordered` — no reorder/drop/insert),
  (4) the ADVERSARIAL dichotomy, in `CollisionReduce.OrBreak` form: the light client is
      `Unfoolable` UNLESS the extractability floor is broken (`OrBreak (¬ExtractsTo) Unfoolable`),
  (5) the contrapositive with teeth: any successful fooling attack CONSTRUCTS a floor break
      (`Foolable → ¬ExtractsTo` — exactly `fooling_breaks_floor`).

**Where the adversarial content comes from (and where it does NOT).** Conjuncts (4)–(5) are proved
by `fooling_hardness_from_floor` below, whose statement and proof mention NO `ChainStep`, NO
`Aggregate`, NO `steps` — only the light-client game (`Foolable`/`Unfoolable`) and the floor
carriers (`ExtractsTo`/`SatBindsProduced`). The fooling-hardness comes from the FLOOR (threaded
honestly: the binding carrier `hBind` is a hypothesis; extractability stays INSIDE the statement as
the `OrBreak` break event / the implication's antecedent, so nothing is vacuous by assumption).
`ChainStep.commits` is never consulted for it — it CANNOT be, since no `ChainStep` occurs in
(4)–(5). Conjuncts (1)–(3) come from `light_client_verifies_whole_history` under `EngineSound` +
`verify agg.root = true`; we deliberately DROP its `every_turn` field from the conjunction, because
`every_turn_says_nothing` shows it is free.

**FIRE (both polarities), on the honest chain.** The hypotheses are satisfiable on the REAL 1-step
honest executor chain (`RecursiveAggregation.realSteps` over `teethGenesis`, engine soundness
`real_engine_sound`) with the LightClientUC reference instance: the honest twin resolves the
`OrBreak` to the GOOD branch (`fire_unfoolable`, via `refExtractsTo`) and yields a concrete
rejection fact (`fire_rejects_unproduced`: no proof makes the sound client accept the non-produced
state `3`); the broken twin (`badVerify`, accepts everything) is FORCED into the real break branch
(`fire_twin_forced_broke`) and conjunct (5) extracts the concrete floor break
(`fire_twin_breaks_floor`). So the dichotomy is a real discriminator, not a formal husk.

Does NOT edit `AssuranceCase`/`HistoryAggregation`/`RecursiveAggregation` — pure strengthening on top.
`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Circuit.RecursiveAggregation
import Dregg2.Circuit.CollisionReduce
import Dregg2.Crypto.LightClientUC

namespace Dregg2.Circuit.ChainStepNonTautology

open Dregg2.Exec (RecChainedState recCexec)
open Dregg2.Distributed.HistoryAggregation
open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Circuit.CollisionReduce
open Dregg2.Crypto.LightClientUC

/-! ## §1 — THE TAUTOLOGY, exhibited (which part of the E-guarantee was free).

`ChainStep.commits` is a structure field, so "every turn executed correctly" holds for EVERY
`List ChainStep` — no aggregate, no verifier, no soundness hypothesis. These two theorems are the
INDICTMENT, not the deliverable: they prove the `every_turn` conjunct of `AggregateAttests` (and
hence that conjunct of `AssuranceCase.unfoolability_guarantee`) carries zero adversarial content.
The `↔ True` shape is deliberate — it is the finding itself, machine-checked. -/

/-- **The free conjunct.** For ANY list of `ChainStep`s — no `verify`, no `EngineSound`, no
aggregate anywhere — "every turn executed correctly per the verified executor" holds, because the
executor witness is a FIELD of `ChainStep`. This is verbatim the content of
`HistoryAggregation.every_turn_executed_correctly` and of `AggregateAttests.every_turn`; restated
here hypothesis-free to make the freeness impossible to miss. -/
theorem every_turn_is_free (steps : List ChainStep) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post :=
  fun s _ => s.commits

/-- **The conjunct says nothing.** The `every_turn` proposition is logically `True` for every
steps list: as a conjunct of an attestation it adds no constraint an adversary must satisfy.
(The REAL constraints of `AggregateAttests` are the other three fields — the two public root pins
and `ChainBound` — which `light_client_E_genuine` keeps.) -/
theorem every_turn_says_nothing (steps : List ChainStep) :
    (∀ s ∈ steps, recCexec s.pre s.turn = some s.post) ↔ True :=
  iff_true_intro (every_turn_is_free steps)

/-! ## §2 — The adversarial core, PROVED WITHOUT `ChainStep`.

The genuine "unfoolability" content of guarantee E is the LightClientUC reduction: a no-secret
client can only be fooled by breaking the floor. We package it as the two conjuncts
`light_client_E_genuine` will carry, and prove them in a statement in which NO `ChainStep`,
`Aggregate`, or steps list occurs — so the fooling-hardness demonstrably does NOT ride
`ChainStep.commits`. The binding carrier (`SatBindsProduced`, the sponge-CR/StateCommit
injectivity shape) is threaded honestly as a hypothesis; the extractability carrier
(`ExtractsTo`, the STARK/Fiat-Shamir floor) is NOT assumed — it is the `OrBreak` break event in
(a) and the antecedent target in (b), so neither conjunct is vacuous-by-assumption. -/

section AdversarialCore

universe u

variable {LCState LCProof LCWitness : Type u}

/-- **`fooling_hardness_from_floor` — the E-guarantee's adversarial content, `ChainStep`-free.**
Under the binding carrier alone:
  (a) `OrBreak (¬ExtractsTo) Unfoolable` — the client is unfoolable, UNLESS the extractability
      floor is broken (the collision-reduce dichotomy; good branch = the real security verdict);
  (b) `Foolable → ¬ExtractsTo` — a successful fooling attack CONSTRUCTS a concrete break of the
      STARK/Fiat-Shamir floor (`fooling_breaks_floor` verbatim).
(a) rides `unfoolable_of_floor` on the `ExtractsTo` case split; (b) is the contrapositive with
teeth. No `ChainStep` occurs in this statement or proof. -/
theorem fooling_hardness_from_floor
    (lcVerify : LCState → LCProof → Bool)
    (Sat : LCState → LCWitness → Prop) (Produced : LCState → Prop)
    (hBind : SatBindsProduced Sat Produced) :
    OrBreak (¬ ExtractsTo lcVerify Sat) (Unfoolable lcVerify Produced)
      ∧ (Foolable lcVerify Produced → ¬ ExtractsTo lcVerify Sat) := by
  constructor
  · by_cases hExt : ExtractsTo lcVerify Sat
    · exact OrBreak.ok (unfoolable_of_floor lcVerify Sat Produced hExt hBind)
    · exact OrBreak.broke hExt
  · exact fun hFool => fooling_breaks_floor lcVerify Sat Produced hBind hFool

end AdversarialCore

/-! ## §3 — THE DELIVERABLE: `light_client_E_genuine`.

The non-tautological E-statement: the two public root pins + the `ChainBound` ordering tooth
(the genuine content of `AggregateAttests`, its free `every_turn` field DROPPED) conjoined with
the adversarial fooling-hardness (§2). Hypotheses are exactly the existing keystones':
`EngineSound` + `verify agg.root = true` for the pins/ordering (as in
`light_client_verifies_whole_history`), and the binding floor carrier `hBind` for the adversarial
part (as in `fooling_breaks_floor`) — extractability is never assumed, only concluded about. -/

section Genuine

universe u

variable {LCState LCProof LCWitness : Type u}
variable (Proof : Type) (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`light_client_E_genuine` — guarantee E with the tautological conjunct removed and the
adversarial reduction conjoined.** A light client that checks ONLY `verify agg.root = true` learns
  (1) the public genesis root is pinned to the chain's start,
  (2) the public final root IS the genuine fold of the whole history,
  (3) the chain is correctly ordered (`ChainBound` — no reorder/drop/insert),
and, from the floor (NOT from any `ChainStep` field),
  (4) the no-secret light client is `Unfoolable` UNLESS the STARK/Fiat-Shamir extractability floor
      is broken (`OrBreak` dichotomy), and
  (5) any successful fooling attack constructs a concrete floor break (`Foolable → ¬ExtractsTo`).

What is deliberately ABSENT: the `every_turn` conjunct — `every_turn_says_nothing` proves it is
`True` for every steps list (it rides the `ChainStep.commits` field), so conjoining it would
launder a type-level triviality as a verification result. Conjuncts (4)–(5) are produced by
`fooling_hardness_from_floor`, whose statement contains no `ChainStep` at all: the
fooling-hardness comes from the floor carriers, threaded honestly (`hBind` assumed; `ExtractsTo`
concluded-about, never assumed). -/
theorem light_client_E_genuine
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (lcVerify : LCState → LCProof → Bool)
    (Sat : LCState → LCWitness → Prop) (Produced : LCState → Prop)
    (hBind : SatBindsProduced Sat Produced) :
    -- (1) the public genesis root pin
    agg.genesisRoot = (match steps.head? with
        | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
        | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
    -- (2) the public final root pin
    ∧ agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps
    -- (3) the ordering tooth
    ∧ ChainBound CH RH cmb compress compressN steps
    -- (4) unfoolable UNLESS the floor is broken
    ∧ OrBreak (¬ ExtractsTo lcVerify Sat) (Unfoolable lcVerify Produced)
    -- (5) fooling REQUIRES breaking the floor
    ∧ (Foolable lcVerify Produced → ¬ ExtractsTo lcVerify Sat) := by
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  obtain ⟨hdich, hcontra⟩ := fooling_hardness_from_floor lcVerify Sat Produced hBind
  exact ⟨hatt.genesis_pinned, hatt.final_is_genuine_fold, hatt.ordered, hdich, hcontra⟩

end Genuine

/-! ## §4 — FIRE, both polarities, on the honest chain.

Hypothesis satisfiability is witnessed on the REAL instances the codebase already carries:
  * aggregate side — `RecursiveAggregation.realSteps` (the honest 1-step executor chain over
    `teethGenesis`, `recCexec teethGenesis honestTurn = some _` discharged by `decide`), with
    `real_engine_sound : EngineSound …` and the accepting root (`hroot := rfl`);
  * game side — the LightClientUC `Reference` instance (`refVerify`/`refSat`/`refProduced`,
    binding `refSatBinds` PROVED), and its broken twin `badVerify` (accepts everything).
The honest twin lands in the GOOD branch with a concrete rejection consequence; the broken twin is
FORCED into the real break branch and conjunct (5) extracts the floor break. -/

section Fire

open Dregg2.Exec.ConsensusExec (teethGenesis)

/-- The full `light_client_E_genuine` conclusion, INSTANTIATED: honest aggregate instance
(`realAggregate`/`realSteps`/`real_engine_sound`, accepting root) × honest game instance
(`Reference`). All hypotheses discharged concretely — the theorem FIRES. -/
theorem fire_E_genuine :
    realAggregate.genesisRoot = (match realSteps.head? with
        | none   => stateRoot zCH zRH zcmb zcompress zcompressN teethGenesis.kernel zeroTurn
        | some s => ChainStep.oldRoot zCH zRH zcmb zcompress zcompressN s)
    ∧ realAggregate.finalRoot
        = foldedFinalRoot zCH zRH zcmb zcompress zcompressN teethGenesis realSteps
    ∧ ChainBound zCH zRH zcmb zcompress zcompressN realSteps
    ∧ OrBreak (¬ ExtractsTo Reference.refVerify Reference.refSat)
        (Unfoolable Reference.refVerify Reference.refProduced)
    ∧ (Foolable Reference.refVerify Reference.refProduced
        → ¬ ExtractsTo Reference.refVerify Reference.refSat) :=
  light_client_E_genuine RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps real_engine_sound rfl
    Reference.refVerify Reference.refSat Reference.refProduced Reference.refSatBinds

/-- **FIRE (good branch).** On the honest instance the extractability floor HOLDS
(`Reference.refExtractsTo` is PROVED), so the §3 `OrBreak` conjunct RESOLVES to its good branch:
the reference light client is genuinely `Unfoolable`. The security verdict is extracted from
`light_client_E_genuine`'s conclusion, not re-proved from scratch. -/
theorem fire_unfoolable : Unfoolable Reference.refVerify Reference.refProduced :=
  OrBreak.resolve (not_not_intro Reference.refExtractsTo) fire_E_genuine.2.2.2.1

/-- **FIRE (good branch, read concretely).** The resolved verdict is a TRUE arithmetic fact: NO
proof `π` makes the sound reference client accept the non-produced (odd) state `3`. The twin
`refVerify 3 3 = false` is `#guard`ed in `LightClientUC`; here the SAME rejection follows for
EVERY `π` from the §3 conclusion — the good branch is a real universal, not a husk. -/
theorem fire_rejects_unproduced (π : Nat) : Reference.refVerify 3 π ≠ true := by
  intro hacc
  have h3 : Reference.refProduced 3 := fire_unfoolable 3 π hacc
  simp [Reference.refProduced] at h3

/-- **FIRE (break branch, forced).** The broken twin (`badVerify`, accepts everything) CANNOT
occupy the good branch — `Reference.badNotUnfoolable` refutes it — so the §3 `OrBreak` conjunct
(instantiated at `badVerify`) is FORCED into the REAL break branch: extractability is broken.
The dichotomy genuinely discriminates the two twins on concrete instances. -/
theorem fire_twin_forced_broke : ¬ ExtractsTo Reference.badVerify Reference.refSat := by
  have h := (light_client_E_genuine RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps real_engine_sound rfl
    Reference.badVerify Reference.refSat Reference.refProduced Reference.refSatBinds).2.2.2.1
  rcases h with hgood | hbroke
  · exact absurd hgood Reference.badNotUnfoolable
  · exact hbroke

/-- **FIRE (conjunct (5) bites).** The broken twin admits a concrete fooling attack
(`Reference.badFoolable`: the environment shows the odd state `3`), and conjunct (5) of
`light_client_E_genuine` converts it into the concrete floor break `¬ExtractsTo` — the
`fooling_breaks_floor` reduction firing end-to-end THROUGH the conjoined E-statement. -/
theorem fire_twin_breaks_floor : ¬ ExtractsTo Reference.badVerify Reference.refSat :=
  (light_client_E_genuine RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps real_engine_sound rfl
    Reference.badVerify Reference.refSat Reference.refProduced Reference.refSatBinds).2.2.2.2
    Reference.badFoolable

end Fire

/-! ## §5 — Axiom hygiene. -/

#assert_axioms every_turn_is_free
#assert_axioms every_turn_says_nothing
#assert_axioms fooling_hardness_from_floor
#assert_axioms light_client_E_genuine
#assert_axioms fire_E_genuine
#assert_axioms fire_unfoolable
#assert_axioms fire_rejects_unproduced
#assert_axioms fire_twin_forced_broke
#assert_axioms fire_twin_breaks_floor

end Dregg2.Circuit.ChainStepNonTautology
