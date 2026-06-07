# `Metatheory/` Glue Audit — how much glue are we huffing?

**Date:** 2026-06-06
**Scope:** `Metatheory/*.lean` (5 files) + `Metatheory/Open/*.lean` (7 files), 4536 LOC.
**Method:** read the actual theorem bodies, not docstrings. Verified `sorry`/`axiom`/`:= True`
counts, checked whether each "keystone" is real or scaffolding, and — crucially — traced the
**direction and reality** of every claimed connection to `Dregg2/`.

---

## TL;DR verdict

**This is NOT vacuous glue.** The discipline is real: **zero `sorry`, zero `axiom`, zero
`admit`, zero `:= True`/`:= Unit`-as-success** across all 12 files (every "sorry" string is in
a comment; every `Unit`/`Bool` is either an honest degenerate model or an explicit anti-vacuity
witness). Every keystone is `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`,
and several modules carry deliberate **"teeth"** lemmas that *prove the constraint is falsifiable*
(`leaky_no_simulator`, `confluence_fails_when_coupled`, `realizes_fails`) — the opposite of
laundering.

**BUT the framing in the intent is partly inverted.** The pitch was: *"`Metatheory/` is the
abstract general theory; `Dregg2/` is an INSTANCE that inherits the theorems."* In reality the
dependency runs **mostly the other way**: 10 of 12 metatheory files `import Dregg2.*` and most of
their headline keystones are **verbatim re-wrappers / re-narrations of already-proved Dregg2
theorems into a new vocabulary** (categorical, epistemic, ZK). That is downstream re-naming, not
an upstream generalization the concrete system derives from.

There are **three genuine exceptions** where the hoped-for direction is real and load-bearing
(`EpistemicDial` → 8 Crypto modules; `EpistemicConsensus.Frame` → `Lawvere`; the
`Confluence`/`Finality` lattice bridges in `Categorical`), and **one** genuinely-new closed-OPEN
theorem (`FinalCoalgebra`).

**Honest split: ~55% real substance / ~45% glue** — where "glue" = mathematically-valid but
either (a) a renaming of a Dregg2 theorem the system already had, or (b) an abstract structure
whose only instances are toys defined in the same file, never touched by real `Dregg2`.

---

## The connection taxonomy (the load-bearing question)

Three distinct relationships hide under the word "connects":

| Kind | Meaning | Verdict |
|---|---|---|
| **(I) Instantiated** | A real `Dregg2` def builds an instance of a `Metatheory` structure and *invokes* its inherited keystone. **This is the hoped-for direction.** | RARE but REAL — see EpistemicDial, EpistemicConsensus/Lawvere |
| **(II) Reuse-wrapper** | `Metatheory` theorem body is `:= Dregg2.Foo.bar ...` verbatim, or `:= by exact Dregg2.…`. Re-narration, not generalization. The system does **not** inherit anything; the metatheory inherits from *it*. | COMMON |
| **(III) Disconnected lookalike** | `Metatheory` proves an abstract theorem; a docstring says it "recovers"/"mirrors" a Dregg2 result, but no def is shared and the abstract structure is never instantiated by `Dregg2`. | COMMON in §1/§2 of Categorical, all of Perfect{ZK,UC} |

---

## Per-module verdict

### `Metatheory/Categorical.lean` (742 LOC) — **PARTIAL** (mixed I/II/III)

- **§1 Conservation** (`measure_unit`/`measure_tensor`/`no_free_copy`, `Categorical.lean:63–144`):
  REAL but **Kind III / honestly thin**. Derives monoid-hom + invariance from "Σ is a lax
  monoidal functor to `Discrete M`." The docstring (`:18–21`, `:148–152`) *itself admits* the
  coherence diagrams are vacuous in a discrete target — "we derive monoid-hom + invariance, and
  only that." **Critically: never instantiated.** `Dregg2.Core.withholding_no_free_copy`
  (`Dregg2/Core.lean:203`) is proved **independently** from `Conservation`'s fields — it does NOT
  call `Categorical.no_free_copy`. The two are structurally-isomorphic parallel proofs in
  different namespaces. So §1 is an abstract lookalike, not a theory Dregg2 derives from.
- **§2 Seam** (`Seam`/`seam_*`, `:170–211`): REAL but **Kind III**. `Seam` is a bare
  `GaloisConnection` wrapper; `seam_*` lemmas are one-line `S.adj.*` calls. **The `Seam` structure
  is never instantiated anywhere** (the `*Seam` defs in `Dregg2/Crypto/` are unrelated
  `Verifiable` instances, not `Metatheory.Seam`). Decorative.
- **§4 Finality** (`:225–288`): **REAL, Kind I.** `tier_commit_eq_crossTierJoin`
  (`:283`) is `commitAtMax a b = Dregg2.Finality.crossTierJoin a b := rfl` — a *definitional*
  match on the **real** `Dregg2.Finality.Tier`, plus genuine `OrderTop`/`OrderBot`/`BoundedOrder`
  instances on it (`:267–279`). Load-bearing.
- **§5 Confluence** (`:339–345`): **REAL, Kind II→borderline-I.** `tier1Eligible_closedUnderJoin`
  is `:= fun x y hx hy => Dregg2.Confluence.admits_sound …` — reuses the **real** module's tier-1
  soundness. Honest reuse.
- **§3 Coalgebra/pullback** (`:351–620`): states the cell as an `F`-coalgebra and JointTurn as a
  wide pullback; **leaves final-coalgebra existence explicitly OPEN** (`:597–607`, closed in
  `FinalCoalgebra`). Honest about being conditional.

### `Metatheory/ConstructiveKnowledge.lean` (444 LOC) — **PARTIAL** (mostly Kind II)

- **§1 realizability** (`Holds`, `holds_iff_discharged_witness`, `holds_mono`, `find_realizes`,
  `:72–139`): **REAL and genuinely built on real Dregg2 primitives** (`Dregg2.Laws.Verifiable`/
  `Discharged`/`Searchable`/`search_sound`). `holds_iff_discharged_witness` is `Iff.rfl` (the
  content is the *definition* `Holds := ∃ w, Discharged …`), but the encoding is faithful. This is
  the substantive core of the file.
- **§4 no-drift** (`knowledge_does_not_drift`, `:369–382`): **Kind II, verbatim wrapper.** Body is
  `:= stepComplete_preserves Impl … hsc hpres hlife hx` — the proved Dregg2 keystone re-named.
- **`knower_sound_to_itself`** (`:390–393`): `:= sound_refl Impl x` — verbatim Dregg2 wrapper.
- **`knowledge_no_free_copy`** (`:426–432`): `:= Dregg2.Core.withholding_no_free_copy …` —
  **verbatim Dregg2 wrapper**, and honestly NOT `#assert_axioms`-pinned because it rests on the
  `sorry`'d conservation primitive (`:420–425`).
- **Net:** §1 is real reuse; §4–§5 are re-narration of theorems Dregg2 already had. The coda
  (`:434–442`) is honest: "the verification of dregg2 discharges these obligations … a distinct,
  larger body of Lean." I.e. the module knows it is downstream.

### `Metatheory/EpistemicConsensus.lean` (407 LOC) — **PARTIAL → REAL-ish** (Kind I target)

- Builds an Aumann/Kripke `Frame` (indistinguishability `Indist`, `Knows`, `DistKnows`) and proves
  `honest_dist_knowledge_iff_holds`, `distKnows_mono_group`, `no_dist_knowledge_of_unrealizable`
  (`:148–241`). Real epistemic-logic content, but the keystones bottom out in
  `holds_iff_discharged_witness` (= `Iff.rfl`), so the "distributed knowledge" mostly reduces to
  realizability.
- **Anti-vacuity is taken seriously**: §6 (`:245+`) flags that `∀`-quantified frame theorems can be
  vacuous and supplies a *discriminating* witness (`verifiable_discriminates`, `:316`, proving the
  check is not constantly-true; the `Unit`/`Bool` here are anti-glue, not glue).
- **Connection is REAL (Kind I):** this `Frame` is consumed by `Dregg2/Metatheory/Lawvere.lean`
  (`import Metatheory.EpistemicConsensus`) to build the `∀_a = Knows` triple. So it is an upstream
  abstraction the Dregg2-side actually uses.

### `Metatheory/Disputation.lean` (86 LOC) — **REAL but slim** (Kind II)

- `upheld := Holds`; `verdict_is_honest_distributed_knowledge`/`byzantine_majority_cannot_uphold`
  (`:31–46`) are real proofs but reduce to `holds_iff_discharged_witness` + `Frame.*` lemmas.
  Genuinely states the "constructive adjudication escapes Arrow on the certifiable domain" thesis,
  but it is a thin corollary of EpistemicConsensus. Worth keeping as the named endpoint.

### `Metatheory/EpistemicDial.lean` (505 LOC) — **REAL, the BEST connection (Kind I)** ✅

- **This is the one module that fully delivers the intended architecture.** It defines `Dial`,
  `DiscloseAt`, the disclosure-lattice laws (`leak_mono`, `accepts_invariant_under_dial`,
  `accepts_bot_iff_discharged`, `:213–226`), and — crucially — **all 8 `Dregg2/Crypto/*` verifier
  kinds instantiate `DiscloseAt` and invoke the inherited keystone**:
  `Dregg2/Crypto/NonMembership.lean:327` builds `nonMembershipDisclose : @DiscloseAt …` and
  `:343` proves `nonmembership_dial_wired` by calling `DiscloseAt.accepts_bot_iff_discharged`
  (`Dregg2/Crypto/NonMembership.lean:352`). Same pattern in Pedersen, Custom, Dfa, Temporal,
  Bridge, PredicateKernel, BlindedSet. **This is real "Dregg2 is an instance that inherits the
  theorem."**
- **The "unify single ⊕ multi-party" keystone has a caveat** (`:341–375`): `Dregg2Mode`
  (`:258`) is a **local 3-element toy enum defined in this file**, NOT the real `Dregg2.Exec.AuthMode`.
  So `dial_unifies_single_and_multi_party` unifies two toy enums; several conjuncts are `rfl`
  (`embeddings_agree_at_extremes := ⟨rfl, rfl⟩`, `:370`). The `PartySchedule` party-count
  agnosticism (`:414`) is genuine abstraction (`Fintype ι`) but its conjunct (1) is `fun _ => rfl`.
  **Verdict:** the `DiscloseAt`-instantiation half is load-bearing and real; the
  single⊕multi-party "unification" half is a same-file toy dressed up.

### `Metatheory/Open/FinalCoalgebra.lean` (157 LOC) — **REAL, the strongest pure theorem** ✅

- Constructively builds the Moore-behaviour final coalgebra (carrier `List Adm → Obs`) and proves
  `nuF_isFinal : IsFinalCell (nuF Obs Adm)` and `nuF_exists` (`:139–147`) for **arbitrary** types,
  closing Categorical §3's real OPEN, `#assert_axioms`-clean. Honest mathematics, the
  "co-Yoneda/final-coalgebra existence" hard centerpiece dispatched via the classical Moore route.
- **Caveat (Kind III):** `nuF` is **never connected to a real Dregg2 cell** — grep of `Dregg2/`
  for `nuF`/`FinalCoalgebra` is empty. It closes an abstract OPEN that lives entirely inside the
  abstract layer. Real theorem, but the concrete system doesn't consume it.

### `Metatheory/Open/PerfectZK.lean` (333 LOC) — **PARTIAL** (toy-only, but with teeth)

- `view_indep_of_witness`/`view_factors_through_statement` (`:101–111`) are near-definitional
  unfolds of the `hperf` field (`rw [Z.hperf …]`, `⟨Z.sim, Z.hperf⟩`). All the content is in the
  assumption `hperf : view s w = sim s`. **Only instances are toy `Unit`/`Bool` OTP** (`:259`).
- **Good discipline (teeth):** `leaky_view_indep_FAILS`/`leaky_no_simulator` (`:300–307`) prove the
  constraint is falsifiable — not vacuous. And there's a **real** bridge to Dregg2:
  `floor_bit_iff_discharged` (`:230`) ties the dial bottom to `Dregg2.Laws.Discharged`.
- **Verdict:** the perfect-ZK "theorem" is the trivial information-theoretic fragment; never
  instantiated by a real ZK system. Honest about it (the computational case is the explicit
  residual). Keep the teeth + dial bridge; the abstract structure is thin.

### `Metatheory/Open/PerfectUC.lean` (423 LOC) — **PARTIAL** (degenerate fragment, honest)

- `perfectUC_composition` (`:200–208`) is the **perfect** (= equality, not ≈) UC composition: the
  proof is literally `rw [hb]` / `congrArg ρ.compose` (`:214–217`). The docstring (`:198–199`)
  *explicitly* flags the real computational theorem (PPT, negligible advantage) as "the explicit
  residual" — i.e. unproven. Teeth present (`realizes_fails`, `composition_needs_hypothesis`).
- **Verdict:** UC-security transport is proved only in the trivial perfect-equality case; the hard
  part is honestly marked OPEN. Candidate-independent but never instantiated by a Dregg2 protocol.

### `Metatheory/Open/ConservationMultiEdge.lean` (431 LOC) — **REAL** ✅ (Kind I/II)

- Substantive: `round_cg5_conserves` (`:154–169`) is a genuine **induction over `Round`** using the
  **real** `Dregg2.Exec.JointCell.jointApplyRound`/`joint_cg5_conserves`, lifting the single-edge
  conservation bridge to multi-edge rounds, and ties to the **real** `WhoYields.ConjGraph` WL cut.
  This is an actual generalization of a real Dregg2 result built on real Dregg2 defs.
- Honest scaffolding-marking: `Placement` (`:184`) is "supplied as DATA … the narrowed residual."

### `Metatheory/Open/CrossCellBisim.lean` (373 LOC) — **REAL** ✅ (Kind I/II)

- Lifts the **real** `Dregg2.Proof.ContendedCrossCell.applyHalfOut_comm_disjoint` (a 2-point
  commutation) to whole-history confluence `xcell_whole_history_confluent` (`:204`) over the
  coinductive adversary stream, with real obs-bisimulation. Teeth: `confluence_fails_when_coupled`
  (`:338`). Genuine, connected, load-bearing.

### `Metatheory/Open/CurvatureScreen.lean` (335 LOC) — **REAL** ✅ (Kind I/II)

- `curv_screen_sound` (`:183`) is a real ℚ-arithmetic proof (convexity/chord bound) in the exact
  shape of the **real** `Dregg2.Apps.OrbitalScreen.screen`, with teeth
  (`teeth_curv_rejects`/`teeth_conjunction_in_step`). Genuine.

### `Metatheory/Open/AuthorityClosure.lean` (300 LOC) — **REAL but self-contained** (Kind III-ish)

- `noforge_closure`/`amp_noforge_closure` (`:128–283`) are real induction-over-traces
  non-amplification proofs. Self-contained (`TracesTo`/`AmpClosed` defined locally); the docstring
  (`:295`) honestly says the operational `withholding_no_free_copy` line lives elsewhere. Real
  theorem, candidate-independent, but not instantiated by a concrete Dregg2 authority object.

---

## The known-hard centerpieces (verdict each)

| Centerpiece | Status |
|---|---|
| **Co-Yoneda collapse / final coalgebra existence** | **PROVED** via Moore construction (`FinalCoalgebra.nuF_exists`). Real. Not co-Yoneda per se, but a legitimate route. Not consumed by Dregg2. |
| **Faithful `∀_a = Knows` epistemic triple** | **PROVED + connected.** `Dregg2/Metatheory/Lawvere.lean:113 lawvere_triple` (`∃_f ⊣ f* ⊣ ∀_f` as GaloisConnections), built on `Metatheory.EpistemicConsensus.Frame`, with honest **negative teeth** (`§B.4`: the clean triple does NOT lift to the Byzantine fibre). The best single result in the whole stack. |
| **Rigidity isos** | Not found as a proved iso in `Metatheory/`; the closest is `embeddings_agree_at_extremes` (toy `rfl`). Treat as not delivered here. |
| **UC-security transport (PerfectUC)** | **Perfect/equality fragment only** — `congrArg`. Computational UC explicitly OPEN. Honest. |
| **PerfectZK** | **Information-theoretic fragment only**, toy `Unit`/`Bool` instances. Computational ZK is the abstract `Disclosure` residual. Honest, with teeth. |

---

## Genuinely load-bearing pieces worth keeping

1. **`EpistemicDial.DiscloseAt`** — the real abstraction the 8 Dregg2 Crypto kinds instantiate and
   inherit (`accepts_bot_iff_discharged`). This is the architecture working as intended. **Keep,
   and extend this pattern.**
2. **`EpistemicConsensus.Frame` → `Lawvere.lawvere_triple`** — real upstream epistemic abstraction
   the Dregg2-side consumes; the `∀_a = Knows` triple with honest teeth.
3. **`FinalCoalgebra.nuF_exists`** — genuine closed-OPEN theorem.
4. **`Categorical` §4/§5 bridges** — `tier_commit_eq_crossTierJoin` (`rfl` on real `Tier`),
   `tier1Eligible_closedUnderJoin` (reuses real `admits_sound`).
5. **The three "Open" lifts** — `ConservationMultiEdge.round_cg5_conserves`,
   `CrossCellBisim.xcell_whole_history_confluent`, `CurvatureScreen.curv_screen_sound`: real
   generalizations built on real Dregg2 app theorems, each with anti-vacuity teeth.
6. **The teeth discipline globally** — every `*_FAILS`/`fails`/`cannot` lemma is genuine
   anti-laundering and should be a required pattern.

## What is glue (mathematically valid, but not the advertised generalization)

- **`Categorical` §1 Conservation + §2 Seam** — abstract lookalikes never instantiated; the real
  Dregg2 conservation is proved independently. Decorative re-derivation.
- **`ConstructiveKnowledge` §4–§5** — verbatim re-wrappers of `stepComplete_preserves`,
  `sound_refl`, `withholding_no_free_copy` under new names.
- **`EpistemicDial`'s single⊕multi-party "unification"** — unifies two **same-file toy enums**;
  `Dregg2Mode ≠` the real `AuthMode`.
- **`PerfectZK`/`PerfectUC`** — only toy instances; the non-degenerate (computational) theorems are
  honestly OPEN. Valuable as *specifications with teeth*, not as connected generalizations.

---

## What it would take to make this an actual generalized metatheory Dregg2 derives from

The fix is to **invert the remaining dependencies** so `Dregg2` instantiates abstractions and
inherits, instead of `Metatheory` re-naming Dregg2 theorems:

1. **Make the conservation functor real.** Define one `Σ : DreggCellCat ⥤ Discrete ℕ` from the
   actual `Dregg2.Core.Conservation`, then *derive* `withholding_no_free_copy` by applying
   `Categorical.no_free_copy` to it — deleting the independent proof in `Core.lean`. Until then §1
   is decorative.
2. **Instantiate `Metatheory.Seam`** with the real `Predicate ⊣ Witness` of `Dregg2.Laws` (a single
   `Seam` value), so `seam_*` become theorems *about the system*. Today it is never built.
3. **Replace `EpistemicDial.Dregg2Mode` (toy) with the real `Dregg2.Exec.AuthMode`** and re-prove
   the embedding, so "single⊕multi-party unification" touches the real disclosure type.
4. **Connect `FinalCoalgebra.nuF` to the real cell** (`Dregg2.Boundary.TurnCoalg`): exhibit the
   anamorphism of a real cell into `nuF` and state no-drift as agreement-with-νF, so the final
   coalgebra is *used*, not just proven to exist.
5. **Reframe `ConstructiveKnowledge` §4–§5 as `instance`/`abbrev` aliases**, not `theorem`
   re-statements, to make the "this IS the Dregg2 theorem, renamed" honesty structural rather than
   prose.
6. **Land the non-degenerate ZK/UC** (computational indistinguishability) or relabel
   `PerfectZK`/`PerfectUC` as *information-theoretic-fragment specs* in their public names, not just
   docstrings, so the OPEN is visible at the type level.

Do (1)–(4) and the "% real generalized metatheory the concrete system derives from" moves from
~55% to genuinely high, because the abstraction becomes load-bearing rather than narrating.

---

## Bottom line for the maintainer

You are **not** huffing glue in the dishonest sense — there are no `sorry`s, no `:= True`, the
teeth are real, and the axiom-pinning is rigorous. But you are partly **huffing your own
re-narration**: a large fraction of the "categorical/epistemic keystones" are Dregg2 theorems
wearing a fancier hat (Kind II), or abstract structures whose only instances are toys in the same
file (Kind III). The architecture you *intended* — Dregg2 instantiates the abstraction and inherits
— is genuinely realized in exactly one-and-a-half places (`EpistemicDial`→Crypto, and
`EpistemicConsensus`→`Lawvere`), plus the lattice bridges. Those are the templates; the rest needs
the dependency inverted to earn the word "metatheory."
