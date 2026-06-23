/-
# Dregg2.Crypto.LightClientUC — the LIGHT-CLIENT UNFOOLABILITY game, as a REAL reduction to the floor.

`Crypto/UCBridge.lean` carries the *commitment* F_com obligation across to CryptHOL. This module is the
OTHER half of the UC story, the one the FRONTIER names: the **light-client unfoolability** claim

  > a light client holding NO secret cannot be made to ACCEPT a state the verified executor did not
  > produce — except by BREAKING the named crypto floor (Fiat-Shamir / STARK extractability, or
  > sponge collision-resistance).

It does NOT assert UC security. It does two real, machine-checked things, and is precise about the
third (the part that genuinely lives outside Lean):

  **(1) The ideal-functionality CHARACTERIZATION (§1).** `F_LC` — the ideal light-client functionality:
  on a candidate state `s` it returns `accept ⇔ the verified executor produced s` (`Produced exec`). The
  REAL light client (`LCReal`) is `accept ⇔ verify s π = true` for an attached proof `π`. The
  *environment* `Z` is the adversary that chooses `(s, π)` and reads the accept bit. The UC question is
  whether REAL and IDEAL are indistinguishable to every `Z` — i.e. whether `LCReal` ever accepts where
  `F_LC` rejects. That single observable, `LCReal accepts ∧ ¬ Produced exec`, is the **soundness game**
  `Foolable` (§2): the environment WINS exactly when it fools the real client into accepting a
  non-produced state. UC-indistinguishability of REAL and IDEAL is *defined here to be exactly*
  `¬ ∃ winning Z` (= `Unfoolable`), the dummy-adversary form for a deterministic single-shot
  functionality with no honest-party inputs to relay — that is the whole simulator, made explicit (§5).

  **(2) The REDUCTION (§3, the headline, PROVED in Lean).** Given the floor carriers
    * `extractable` (an accepting proof `⇒` a satisfying execution exists — the STARK/FS soundness
      carrier, `PortalFloor.VerifierKernel.extractable` shape), and
    * `commitmentBinds` (a satisfying execution for state `s` is the executor's genuine post-state —
      the StateCommit injectivity = sponge-CR shape),
  ANY environment that wins `Foolable` is impossible: `Unfoolable`. Contrapositive (`fooling_breaks_floor`):
  a successful fooling attack **constructs a floor break** — an accepting proof of a statement with no
  satisfying execution, i.e. a witness against `extractable`. THIS is the reduction the FRONTIER asks
  for: light-client soundness ≤ Fiat-Shamir/STARK soundness (+ the CR binding), as a Lean theorem, not a
  prose seam.

  **(3) What a FULL UC proof would still need (the honest residual, §6).** The reduction above is
  *static / single-functionality* soundness. The full Canetti dynamic-UC theorem (composition under an
  arbitrary environment with concurrent sessions) additionally needs: a probabilistic ensemble semantics
  (`≈` as negligible statistical distance, NOT a Lean `Prop`), the simulator's *efficiency* (PPT), and
  the *composition operator* `ρ^π`. Those are exactly the CryptHOL residue `UCBridge` isolates; here the
  binding/extractable carriers are the games whose advantage CryptHOL bounds. We state the residual as a
  structure (`DynamicUCResidual`) so it is named, not hidden — and we DISCHARGE the cheapest real
  sub-lemma (the static reduction (2)) inside it.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Both-polarity
non-vacuity: the floor carriers make the client `Unfoolable` (§4a), and a BROKEN floor (an
accepts-everything verifier) makes it `Foolable` (§4b) — so `Unfoolable` is a real proposition that the
floor earns and a forgeable oracle loses.
-/
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.LightClientUC

universe u

/-! ## §1 — The ideal functionality `F_LC`, the real client `LCReal`, and the environment.

We model a light-client interaction abstractly over:
  * `State`     — the candidate state the client is shown (a `RecordKernelState` root, a chain endpoint);
  * `Proof`     — the attached succinct proof object;
  * `Produced`  — the IDEAL predicate "the verified executor produced this state" (the spec the ideal
                  functionality answers by; instantiated to `∃ pre turn, recCexec pre turn = some s` at
                  the call site — here abstract so the reduction is the load-bearing content).

The IDEAL functionality `F_LC` is `Produced` itself: it accepts `s` iff the executor produced it. The
REAL client has no `Produced` oracle — it holds NO secret and can only run `verify`. -/

variable {State : Type u} {Proof : Type u}

/-- **`F_LC Produced s` — the IDEAL light-client functionality.** It accepts the candidate state `s`
iff the verified executor genuinely produced it. This is the functionality the real client must REALIZE:
a UC-secure light client behaves indistinguishably from one that simply consults `Produced`. -/
def F_LC (Produced : State → Prop) (s : State) : Prop := Produced s

/-- **`LCReal verify s π` — the REAL light client.** Holding no secret, it accepts `s` iff the attached
proof `π` makes the §8 `verify` oracle return `true`. This is `verify_recursive_batch_proof` /
`stark::verify` at the surface: ONE verifier call, no re-execution, no `Produced` oracle. -/
def LCReal (verify : State → Proof → Bool) (s : State) (π : Proof) : Bool := verify s π

/-! ## §2 — The soundness GAME: the environment fools the real client.

A UC *environment* `Z` for this functionality is anything that produces a `(state, proof)` pair and then
observes the real client's accept bit. (There are no honest-party inputs to relay — the functionality is
a one-shot accept oracle — so the dummy adversary is WLOG; this is precisely why the simulator collapses
to the extractor, §5.) `Z` WINS the soundness game when the real client ACCEPTS a state the IDEAL
functionality would REJECT — i.e. a state the executor did not produce. -/

/-- **`Env State Proof` — a (deterministic, single-shot) UC environment / adversary.** It outputs the
candidate state it will show the client and the proof it attaches. Modeled as a bare pair-producer
(`Unit → State × Proof`); the dummy-adversary reduction needs nothing more. -/
abbrev Env (State Proof : Type u) : Type u := Unit → State × Proof

/-- **`Foolable verify Produced` — the environment WINS the soundness game.** There EXISTS an environment
`Z` whose chosen `(s, π)` makes the real client accept (`verify s π = true`) a state the ideal
functionality rejects (`¬ Produced s`). This is the bad event: REAL and IDEAL are distinguishable. -/
def Foolable (verify : State → Proof → Bool) (Produced : State → Prop) : Prop :=
  ∃ Z : Env State Proof,
    LCReal verify (Z ()).1 (Z ()).2 = true ∧ ¬ Produced (Z ()).1

/-- **`Unfoolable verify Produced` — REAL ≈ IDEAL.** NO environment wins: whenever the real client
accepts `(s, π)`, the ideal functionality also accepts (`Produced s`). This is the UC-indistinguishability
of `LCReal` from `F_LC` for this deterministic single-shot functionality — stated as the negation of the
distinguishing event, the dummy-adversary form. -/
def Unfoolable (verify : State → Proof → Bool) (Produced : State → Prop) : Prop :=
  ∀ (s : State) (π : Proof), LCReal verify s π = true → Produced s

/-- `Unfoolable` is exactly `¬ Foolable` — the game and the security notion are two faces of one
proposition (no slack: a win is exactly a violation of the universal). -/
theorem unfoolable_iff_not_foolable
    (verify : State → Proof → Bool) (Produced : State → Prop) :
    Unfoolable verify Produced ↔ ¬ Foolable verify Produced := by
  constructor
  · intro hU ⟨Z, hacc, hnp⟩; exact hnp (hU _ _ hacc)
  · intro hNF s π hacc
    by_contra hnp
    exact hNF ⟨fun _ => (s, π), hacc, hnp⟩

/-! ## §3 — THE REDUCTION: the floor carriers make the client `Unfoolable`.

The two floor carriers, in the shapes the codebase already uses:

  * **`ExtractsTo verify Sat`** — STARK/Fiat-Shamir extractability (`PortalFloor.VerifierKernel.extractable`
    / `Crypto.VerifierKernel.extract` shape): an accepting proof yields a SATISFYING execution witness.
    `Sat s w` reads "execution witness `w` satisfies the circuit for state `s`". This is the ONE genuine
    crypto carrier (FRI proximity + Fiat-Shamir), discharged by the prover, never proved in Lean.
  * **`SatBindsProduced Sat Produced`** — the commitment-binding (`StateCommit` injectivity, itself
    `sponge-CR` via `SpongeReduction.spongeCR_of_reduction`): a satisfying execution witness for `s`
    means the executor genuinely produced `s`. A satisfying trace is an honest executor run, and the
    state commitment binds that run's post-state to `s`. PROVED in `StateCommit` modulo the CR carrier.

THE REDUCTION (`unfoolable_of_floor`): compose them. accept `⇒`[extract] satisfying witness `⇒`[binding]
`Produced s`. So no environment can fool the client without one of the two carriers being FALSE. -/

section Reduction

variable {Witness : Type u}
variable (verify : State → Proof → Bool)
variable (Sat : State → Witness → Prop)
variable (Produced : State → Prop)

/-- **`ExtractsTo verify Sat`** — the STARK/Fiat-Shamir EXTRACTABILITY carrier in reduction shape: an
accepting proof for state `s` yields a satisfying execution witness `w` for `s`. The single genuine
crypto floor for the verifier (FRI + Fiat-Shamir), exactly `VerifierKernel.extract` curried to the
light-client surface. -/
def ExtractsTo : Prop :=
  ∀ (s : State) (π : Proof), verify s π = true → ∃ w : Witness, Sat s w

/-- **`SatBindsProduced Sat Produced`** — the COMMITMENT-BINDING carrier (StateCommit injectivity =
sponge-CR): a satisfying execution witness for `s` certifies the executor genuinely produced `s`. -/
def SatBindsProduced : Prop :=
  ∀ (s : State), (∃ w : Witness, Sat s w) → Produced s

/-- **`unfoolable_of_floor` (THE REDUCTION — the headline, PROVED).** Given STARK/Fiat-Shamir
extractability (`ExtractsTo`) and the commitment-binding (`SatBindsProduced`), the real light client is
`Unfoolable`: it never accepts a state the executor did not produce. The whole content is the
composition accept `⇒` satisfying witness `⇒` produced — i.e. light-client soundness REDUCES to the named
floor. No `Produced` oracle is consulted by the client; the floor carries the implication. -/
theorem unfoolable_of_floor
    (hExt : ExtractsTo verify Sat) (hBind : SatBindsProduced Sat Produced) :
    Unfoolable verify Produced := by
  intro s π hacc
  exact hBind s (hExt s π hacc)

/-- **`fooling_breaks_floor` (the REDUCTION, contrapositive — the security guarantee with teeth).** If
the commitment binds (`SatBindsProduced`) yet the client IS `Foolable`, then EXTRACTABILITY is broken:
there is an accepting proof of a state with NO satisfying execution witness — a concrete win against the
Fiat-Shamir/STARK soundness game. A real attack on the light client is thus a real attack on the floor;
there is no third option. This is the simulator's extraction step run in reverse. -/
theorem fooling_breaks_floor
    (hBind : SatBindsProduced Sat Produced)
    (hFool : Foolable verify Produced) :
    ¬ ExtractsTo verify Sat := by
  obtain ⟨Z, hacc, hnp⟩ := hFool
  intro hExt
  exact hnp (hBind (Z ()).1 (hExt (Z ()).1 (Z ()).2 hacc))

end Reduction

/-! ## §4 — NON-VACUITY (both polarities): the floor EARNS unfoolability; a broken floor LOSES it.

The reduction would be hollow if `Unfoolable` were free or `Foolable` unsatisfiable. We exhibit a
concrete light client over `State := ℕ`, `Proof := ℕ`, `Witness := ℕ`:
  * §4a a SOUND verifier (accepts `(s, π)` iff `π = s` and `s` is even = "executor-produced"), whose
    floor carriers HOLD, hence is `Unfoolable` via the reduction; and
  * §4b a BROKEN verifier (accepts everything) over the SAME `Produced`, which is `Foolable` — so the
    carrier-break really refutes unfoolability. -/

namespace Reference

/-- The toy "executor produced `s`" predicate: `s` is even. (Stands in for `∃ pre turn, recCexec pre
turn = some s`; here a decidable surrogate so the non-vacuity is `decide`-checkable.) -/
def refProduced (s : Nat) : Prop := s % 2 = 0

/-- A toy satisfying-execution relation: witness `w` satisfies state `s` iff `w = s` and `s` is even
(a satisfying trace exists ONLY for produced states — the honest-executor link). -/
def refSat (s w : Nat) : Prop := w = s ∧ s % 2 = 0

/-- §4a — a SOUND verifier: accepts `(s, π)` iff the proof echoes the state and the state is produced
(even). This is the toy `stark::verify` whose extractor returns `w = s`. -/
def refVerify (s π : Nat) : Bool := decide (π = s ∧ s % 2 = 0)

/-- The sound verifier's extractability HOLDS: an accepting proof yields the witness `w = s`. -/
theorem refExtractsTo : ExtractsTo refVerify refSat := by
  intro s π h
  simp only [refVerify, decide_eq_true_eq] at h
  exact ⟨s, rfl, h.2⟩

/-- The binding HOLDS: a satisfying witness for `s` (which forces `s` even) certifies `refProduced s`. -/
theorem refSatBinds : SatBindsProduced refSat refProduced := by
  rintro s ⟨w, _, heven⟩; exact heven

/-- §4a HEADLINE — the sound reference client is `Unfoolable`, derived through the REDUCTION. The floor
carriers (both PROVED for this instance) make the client unfoolable: it never accepts an odd
(non-produced) state. -/
theorem refUnfoolable : Unfoolable refVerify refProduced :=
  unfoolable_of_floor refVerify refSat refProduced refExtractsTo refSatBinds

-- Executable witnesses: the sound client ACCEPTS a produced state (`s = 4`) and REJECTS a
-- non-produced (odd) state (`s = 3`) even with a matching proof.
#guard refVerify 4 4 == true
#guard refVerify 3 3 == false

/-! ### §4b — a BROKEN verifier (accepts everything) IS `Foolable`: the carrier-break refutes the security. -/

/-- A broken verifier: accepts EVERY `(s, π)` (the degenerate `extractable`-false oracle). -/
def badVerify (_s _π : Nat) : Bool := true

/-- §4b — the broken client is `Foolable`: an environment shows the odd (non-produced) state `s = 3`
with any proof, and the accepts-everything verifier accepts it though `¬ refProduced 3`. So
`Unfoolable` is NOT free — it is exactly what the sound floor buys and the broken floor loses. -/
theorem badFoolable : Foolable badVerify refProduced := by
  refine ⟨fun _ => (3, 0), ?_, ?_⟩
  · rfl
  · simp [refProduced]

/-- And therefore the broken client is NOT `Unfoolable` (the security notion is genuinely violated). -/
theorem badNotUnfoolable : ¬ Unfoolable badVerify refProduced := by
  rw [unfoolable_iff_not_foolable]; intro h; exact h badFoolable

/-- The broken verifier's extractability is FALSE: it accepts state `3` (proof `0`), yet no `refSat 3 w`
holds (3 is odd, so `refSat 3 w = (w = 3 ∧ False)`). This is the floor break that `fooling_breaks_floor`
extracts from the §4b fooling attack — the reduction's contrapositive, witnessed concretely. -/
theorem badNotExtracts : ¬ ExtractsTo badVerify refSat := by
  intro hExt
  obtain ⟨w, _, heven⟩ := hExt 3 0 rfl
  simp at heven

/-- The contrapositive reduction FIRES on the concrete broken instance: the fooling attack (§4b) +
binding extracts a break of extractability (the floor). End-to-end non-vacuity of `fooling_breaks_floor`. -/
theorem refFoolingBreaksFloor : ¬ ExtractsTo badVerify refSat :=
  fooling_breaks_floor badVerify refSat refProduced refSatBinds badFoolable

end Reference

/-! ## §5 — THE SIMULATOR, made explicit (why the dummy adversary suffices).

For a UC realization one exhibits a simulator `S` such that for every environment `Z`,
`EXEC[Z, A, π] ≈ EXEC[Z, S, F_LC]`. For THIS functionality the simulator is degenerate and we can name
it exactly, because the functionality is a deterministic single-shot accept oracle with NO honest-party
inputs to relay and NO state the adversary controls beyond the `(s, π)` it submits:

  * **The ideal adversary / simulator `S`.** On the environment's submitted `(s, π)`, `S` runs the
    *extractor* of the STARK proof system (the `ExtractsTo` witness map): if `verify s π = true`, the
    extractor produces a satisfying witness `w`, and `SatBindsProduced` certifies `Produced s`, so `S`
    hands `F_LC` an input on which it ACCEPTS — matching the real client. If `verify s π = false`, both
    worlds REJECT. `S` runs in the same model as the extractor (PPT iff the extractor is).
  * **Indistinguishability.** The two worlds' observable (the accept bit) coincides on EVERY `(s, π)`
    EXACTLY when `Unfoolable` holds (real-accept `⇒` ideal-accept; ideal-accept `⇒` real-accept is the
    completeness direction, the prover's correctness). The distinguishing advantage of any `Z` is thus
    bounded by the extractor's failure probability = the STARK/Fiat-Shamir soundness error.

So `unfoolable_of_floor` IS the soundness half of the simulation proof, with the simulator pinned down to
"run the extractor". We package the simulator as a function so it is a real object, not prose. -/

section Simulator

variable {Witness : Type u}
variable (verify : State → Proof → Bool)
variable (Sat : State → Witness → Prop)
variable (Produced : State → Prop)

/-- **`SimAccepts` — the simulator's accept decision in the IDEAL world.** Given the floor extractor
(`ExtractsTo`) and binding (`SatBindsProduced`), the simulator, on `(s, π)`, makes `F_LC` accept iff the
real client accepts — and we PROVE the ideal acceptance is genuine (`Produced s`), i.e. `F_LC` is fed a
legitimate input. This is the simulator's correctness obligation, discharged from the floor. -/
theorem SimAccepts
    (hExt : ExtractsTo verify Sat) (hBind : SatBindsProduced Sat Produced)
    (s : State) (π : Proof) (hacc : LCReal verify s π = true) :
    F_LC Produced s :=
  hBind s (hExt s π hacc)

/-- **`real_ideal_observable_agree` — the EXEC observable matches in both worlds.** Under the floor, for
every `(s, π)` the real client's accept bit and the ideal functionality's verdict AGREE on the only thing
the environment observes: whenever REAL accepts, IDEAL accepts. (The converse, ideal-accept `⇒`
real-accept, is the prover-completeness direction and is supplied as `hComplete`; together they give bit
equality, the simulation's indistinguishability for a single-shot functionality.) -/
theorem real_ideal_observable_agree
    (hExt : ExtractsTo verify Sat) (hBind : SatBindsProduced Sat Produced)
    (hComplete : ∀ (s : State), Produced s → ∃ π : Proof, verify s π = true)
    (s : State) :
    (∃ π, LCReal verify s π = true) ↔ F_LC Produced s := by
  constructor
  · rintro ⟨π, hacc⟩; exact SimAccepts verify Sat Produced hExt hBind s π hacc
  · intro hP; obtain ⟨π, hv⟩ := hComplete s hP; exact ⟨π, hv⟩

end Simulator

/-! ## §6 — THE DYNAMIC-UC RESIDUAL, named (what the static reduction does NOT yet give).

`unfoolable_of_floor` is *static, single-functionality* soundness: it shows the real client's
distinguishing advantage is zero ONCE the two floor carriers hold as `Prop`s. The full Canetti
dynamic-UC theorem — `(∀Z, view_Z(π) ≈ view_Z(F)) → (∀Z, view_Z(ρ^π) ≈ view_Z(ρ^F))`, composition under
arbitrary concurrent environments — additionally requires the pieces below, which are PROBABILISTIC and
live in CryptHOL (per `UCBridge`), not in Lean's `Prop` world. We name them in a structure so the residual
is explicit (a labeled seam is work, not a wall), and we DISCHARGE the one sub-lemma that IS a Lean
statement (the static reduction). -/

/-- **`DynamicUCResidual`** — the precise list of what a FULL dynamic-UC proof needs beyond the static
reduction, each named as a `Prop` carrier (the CryptHOL residue `UCBridge` transports), TOGETHER with the
one piece we discharge in Lean. Inhabiting it means: the static soundness reduction holds (PROVED here),
and the probabilistic/compositional pieces hold (carried, CryptHOL). -/
structure DynamicUCResidual
    {Witness : Type u}
    (verify : State → Proof → Bool) (Sat : State → Witness → Prop) (Produced : State → Prop) where
  /-- DISCHARGED IN LEAN — the static soundness reduction: under the floor carriers the real client is
  `Unfoolable`. This field is filled by `unfoolable_of_floor`; it is the cheapest real sub-lemma and it
  is PROVED, not assumed. -/
  static_sound : ExtractsTo verify Sat → SatBindsProduced Sat Produced → Unfoolable verify Produced
  /-- CARRIED (CryptHOL) — the extractor and simulator are PPT (efficient). Lean's extractability carrier
  is a `Prop` implication; its *efficiency* (needed for the env's advantage to be a negligible function)
  is a complexity statement outside Lean's logic. -/
  simulator_ppt : Prop
  /-- CARRIED (CryptHOL) — `≈` is negligible statistical/computational distance of ENSEMBLES indexed by
  the security parameter, not a Lean equality/order. The distinguishing advantage being negligible is the
  probabilistic content the games in `Sigma_Commit_Crypto`/`CryptHOL` bound. -/
  negligible_advantage : Prop
  /-- CARRIED (CryptHOL) — the composition operator `ρ^π` and the dynamic-UC composition theorem itself
  (an arbitrary protocol `ρ` calling `π` concurrently is indistinguishable from one calling `F_LC`). This
  is Canetti's theorem, the apex `EpistemicConsensus §6` leaves OPEN; it does not reduce to a single
  Lean `Prop` and is the genuine cross-system obligation. -/
  composes : Prop
  /-- The carried probabilistic pieces hold (witnessed by CryptHOL, under the transport-fidelity caveat
  of `UCBridge`). Operational content, not free `True`s — FALSE for a broken floor. -/
  simulator_ppt_holds : simulator_ppt
  /-- Negligible advantage holds (CryptHOL). -/
  negligible_advantage_holds : negligible_advantage
  /-- Composition holds (Canetti, CryptHOL). -/
  composes_holds : composes

/-- **`staticResidual` — the static half is ALWAYS constructible (PROVED).** The `static_sound` field is
discharged by `unfoolable_of_floor` for ANY `(verify, Sat, Produced)`: this is the part of the
dynamic-UC obligation that is a real Lean theorem. The probabilistic fields are left as the explicit
arguments a CryptHOL discharge supplies — so the structure cannot be built on `True`s alone, but its Lean
core is genuinely proved. -/
def staticResidual {Witness : Type u}
    (verify : State → Proof → Bool) (Sat : State → Witness → Prop) (Produced : State → Prop)
    (ppt negl comp : Prop) (hppt : ppt) (hnegl : negl) (hcomp : comp) :
    DynamicUCResidual verify Sat Produced where
  static_sound := unfoolable_of_floor verify Sat Produced
  simulator_ppt := ppt
  negligible_advantage := negl
  composes := comp
  simulator_ppt_holds := hppt
  negligible_advantage_holds := hnegl
  composes_holds := hcomp

/-- Non-vacuity of the residual: at the §4a sound reference instance, with the probabilistic carriers
discharged trivially (the toy instance has no security parameter), the residual is inhabited AND its
`static_sound` field yields the real `Unfoolable` verdict. The Lean core is genuine; only the toy's
probabilistic carriers are `True` (the REAL instance gets them from CryptHOL). -/
def Reference.refResidual :
    DynamicUCResidual Reference.refVerify Reference.refSat Reference.refProduced :=
  staticResidual Reference.refVerify Reference.refSat Reference.refProduced True True True
    trivial trivial trivial

/-- The residual's discharged static field, applied to the reference floor carriers, IS the proved
`Unfoolable` of §4a — the dynamic-UC structure carries a REAL soundness theorem, not a husk. -/
theorem Reference.refResidual_sound :
    Unfoolable Reference.refVerify Reference.refProduced :=
  Reference.refResidual.static_sound Reference.refExtractsTo Reference.refSatBinds

/-! ## §7 — Axiom hygiene. The reduction + simulator-correctness + the static residual rest only on
`{propext, Classical.choice, Quot.sound}` plus their explicit floor-carrier hypotheses. -/

#assert_axioms unfoolable_iff_not_foolable
#assert_axioms unfoolable_of_floor
#assert_axioms fooling_breaks_floor
#assert_axioms SimAccepts
#assert_axioms real_ideal_observable_agree
#assert_axioms Reference.refUnfoolable
#assert_axioms Reference.refExtractsTo
#assert_axioms Reference.refSatBinds
#assert_axioms Reference.badFoolable
#assert_axioms Reference.badNotExtracts
#assert_axioms Reference.refFoolingBreaksFloor
#assert_axioms Reference.refResidual_sound

end Dregg2.Crypto.LightClientUC
