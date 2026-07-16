# Sound-Fix Verdict: which repair of ArkLib's vacuous t-SDH / KZG binding to ship

**Scope.** Five candidate sound fixes for ArkLib's `Classical.choice`-vacuous `tSdhAssumption`
(and the `binding` / `function_binding` it powers) were elaborated under
`candidates/`. This note is the integrator's verdict: each candidate re-verified against real
ArkLib @ `d72f8392` (Lean `v4.31.0`), the comparison, the per-goal winner, and the honest
recommendation. **Re-verification was done by rebuilding each artifact against the genuine tree
and reading the theorem *statements*, not trusting the lane's summary.**

Nothing here is filed, pushed, or PR'd.

---

## 0. Re-verification results (rebuilt by the integrator, not inherited)

Every artifact below was recompiled with `lake env lean` against the genuine ArkLib checkout
(`/private/tmp/arklib-review` or `/private/tmp/arklib-ggm`, both at `d72f8392`), and its axiom
closure printed. All are `sorry`-free with axioms exactly `[propext, Classical.choice, Quot.sound]`
— **no `sorryAx`**.

| Artifact | Headline theorem(s) | Build | Axioms |
|---|---|---|---|
| `GgmCandidate.lean` | `ggm_tSdh_sound`, `card_winningPoints_le`, `ggm_bound_lt_one` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmAdaptive.lean` (ADAPTIVE) | `adaptive_ggm_sound`, `runAux_congr_of_agree`, `realWinSet_subset`, `card_rootUnion_le`, `adaptive_generalizes_static` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmRandomEncoding.lean` (QUADRATIC) | `rand_encoding_bound`, `card_pairRootUnion_le_two_mul`, `card_handlePolys_le`, `badSet_subset_pairRootUnion`, `rand_encoding_bound_srs` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmDegreeInvariant.lean` (DEGREE, peer) | `degree_invariant_paired`, `degree_invariant_paired_uniform`, `flat_2D_bound_false`, `degree_invariant`, `degree_invariant_linComb` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `GgmArkLibTransport.lean` (TRANSPORT) | `groupWinSet_eq_realWinSet`, `tSdhCondition_iff_field`, `gpow_val_injective`, `fraction_bound_transports_to_group` | exit 0 | `[propext, Classical.choice, Quot.sound]` |
| `AlgebraicTSdh.lean` (novel) | `algExperiment_le`, `alg_survives_attack`, `algExperiment_zeroPoly` (canary) | exit 0 | clean |
| `RepairSurvives.lean` (extraction) | `binding_reduces_to_tSdh`, `repair_survives_attack`, `t_sdh_cond_of_two_valid_openings` | exit 0 | clean |
| `KzgQDlogVacuity.lean` (qdlog) | `not_qDlogAssumption`, `qDlogExperiment_trapdoorAdversary`, `experiment_discriminates` (canary) | exit 0 | clean |
| `AgmSound.lean` (agm) | `repr_valid_of_extraction`, `tau_mem_roots` | exit 0 | clean |

---

## 1. The comparison table

| Candidate | Survives-attack | Numeric bound (rests-on) | Mechanized today | Verdict |
|---|---|---|---|---|
| **extraction** | **PROVEN** (`repair_survives_attack`, sorry-free) | **NO** — reduction only, honestly | **sorry-free** (`+41/−14` patch to `Binding.lean`; whole tree 2994 jobs, exit 0) | **STRONG** (mergeable now) |
| **GGM (static)** | **PROVEN** (`ggm_tSdh_sound`, over the *full* `GenericAdversary` type) | **YES: `(D+1)/(p-1)`** — rests on the static-generic idealization (output committed as deg-≤D poly, `τ` absent from scope) | **sorry-free**, static fragment only | **STRONG** for the static class; **FRONTIER** for adaptive |
| **novel / AlgebraicTSdh** | **PROVEN** (`alg_survives_attack`, sorry-free) | **YES: `(D+1)/(p-1)`** — same static Schwartz–Zippel core, algebraic-model framing | **sorry-free** | **STRONG** — this *is* the GGM-static number in the AGM idiom; a sibling, not a rival |
| **AGM (FKL)** | bounded form **provably still BROKEN** (representation is free data); reduction transports t-SDH(alg) → q-DLOG | **NO** — relocates the number onto q-DLOG (FKL's own `O((t²q+q³)/p)` is *argued*, not mechanized) | reduction sorry-free; the bound is **not** mechanized | **VIABLE relocation / WEAK standalone** |
| **qdlog-direct** | naive form **mechanized BROKEN** (`not_qDlogAssumption`, sorry-free); sound form ARGUED, rests on GGM | **NO** — the number still comes from GGM | vacuity mechanized; sound bound is **frontier** | **DEAD as an escape** (collapses to "fix the base assumption first") — but a **valuable finding** (§4) |

Axes read as: **survives-attack** = does the exact `tauExtractingAdversary` trapdoor attack fail
to beat the bound? — `proven` (mechanized), `argued` (paper), `broken` (still refuted).
**numeric** = does it deliver a real `ε < 1`, and on what does that `ε` rest? **mechanized-today**
= sorry-free against the genuine tree now, partial, or frontier.

---

## 2. The crown jewel, re-checked by a skeptic — is GGM-static a real bound or a dodge?

`ggm_tSdh_sound` states: **for every** `A : GenericAdversary D p` (offset `c`, representation
polynomial `f` with `deg f ≤ D`), with `2 ≤ p`,

```
ggmExperiment A = (winningPoints A).card / (p - 1)  ≤  (D + 1) / (p - 1)
```

A survives-attack result is worthless if it survives by *excluding everything* — a bound that
holds because no adversary is expressible, or because it merely restates `≤ 1`. Applying that
sufficient test to **our own winner**:

1. **The adversary type is richly inhabited, not empty.** `GenericAdversary D p` ranges over
   *every* offset in `ZMod p` and *every* degree-≤D polynomial. The theorem quantifies over that
   whole type — including every `Classical.choice`-definable inhabitant. It does **not** survive
   by having no adversaries to bound. (Contrast a dodge that restricts the type to the empty set.)

2. **The bound is a genuine `< 1`, not a restated `≤ 1`.** `ggm_bound_lt_one` proves
   `(D+1)/(p-1) < 1` for `p > D+2`; at cryptographic parameters (`p ≈ 2²⁵⁴`, `D ≈ 2²⁰`) it is
   `≈ 2⁻²³⁴`. A real, tiny number.

3. **The measured quantity is genuinely nonzero and the cap is tight.** An adversary that
   interpolates `f` through `D+1` targets `1/(τᵢ+c)` wins on exactly `D+1` trapdoors — the
   Boneh–Boyen worst case — so `winningPoints` is not trivially empty and `(D+1)` is not slack.
   The sibling canaries confirm the experiment discriminates (`algExperiment_zeroPoly`,
   `experiment_discriminates`: distinct adversaries get distinct success values).

4. **The generic model is faithful for the static class.** In a prime-order group the reachable
   exponents from the SRS handles `g₁^{τ⁰}, …, g₁^{τ^D}` are exactly `span{1, τ, …, τ^D}` =
   degree-≤D polynomials, so "committed degree-≤D `f`, chosen with `τ` absent" is the *exact*
   static-generic output space, not a convenient sub-space. The exact `tauExtractingAdversary`
   that killed the original **cannot even be typed** here — `GenericAdversary` receives no group
   element, hence no `∃ a, · = g^a` for `Exists.choose` to invert.

**Semantic verdict: GGM-static is a REAL numeric survives-attack bound, not a definitional
dodge.** It survives by *removing the leak input* (`τ`/`g^τ`), not by emptying the adversary set,
and it delivers a real `ε`.

### Two honest scope limits (must travel with every citation)

- **(a) STATIC, now EXTENDED to ADAPTIVE (explicit-oracle model) — `GgmAdaptive.lean`.** The
  `GgmCandidate.lean` bound is the `q = 0` fragment: the adversary commits to one output and makes
  **zero** queries. This limit is now **closed for the explicit-equality-oracle (Maurer) GGM**:
  `adaptive_ggm_sound` admits an adversary making up to `fuel` adaptive queries — linear combinations,
  pairings, and equality tests — and bounds its success by `(fuel·Δ + (D+1))/(p−1)`, sorry-free,
  axioms `[propext, Classical.choice, Quot.sound]`. **The identical-until-bad hybrid is PROVEN by
  induction** (`runAux_congr_of_agree`), not assumed; `fuel = 0` recovers the static number exactly.
  Two residuals remain (see PAPER §9.2), named not faked, and **both narrowed** by the three new lemma
  files: (i) the *classical quadratic* `~(q_G+D)²(D+1)/(p−1)` — Shoup's *random-encoding* model (free
  equality comparison → bad event over all table pairs) — is now MECHANIZED at the counting level as
  `GgmRandomEncoding.rand_encoding_bound : ε ≤ (C(n,2)·2D + (D+1))/(p−1)` with `n = fuel+D+4`, the
  all-table-pairs bad event and the table-size bound both THEOREMS (`badSet_subset_pairRootUnion`,
  `card_handlePolys_le`), **modulo** the whole-table degree hypothesis `hdeg_handles`; our tighter
  linear-in-queries number remains the honest bound for the model where equality costs a query; (ii)
  the degree facts still enter as hypotheses, but the SRS degree invariant is now proved
  **structurally** — `GgmDegreeInvariant.degree_invariant_paired : 2D` under the two-sorted pairing
  discipline, with the naive flat `2D` claim REFUTED (`flat_2D_bound_false`, `X⁴` at `D=1`). Crucially
  that proof is a **PEER model** (`PairedOp`/`buildPaired`) that `GgmAdaptive.runAux` does not import, so
  it does **not yet discharge** `hdeg_out`/`hdeg_pairs`/`hdeg_handles` — see the interlock verdict below.
  The generic-group oracle + simulation lemma that **neither Mathlib nor VCVio had** are built from
  scratch in `GgmAdaptive.lean`.

- **(b) FIELD-LEVEL win predicate — condition-level transport now MECHANIZED against real ArkLib;
  `ProbComp` plumbing remains.** The win condition is stated at the field level (`f.eval τ = 1/(τ+c)`).
  Its equivalence to ArkLib's group-level win is **no longer merely argued**:
  `GgmArkLibTransport.groupWinSet_eq_realWinSet` / `tSdhCondition_iff_field` import ArkLib's **real**
  `Groups.tSdhCondition` (restating nothing) and prove — via injectivity of `a ↦ g^{a.val}` in a
  prime-order group, from ArkLib's own `gpow_div_eq` / `exists_zmod_power_of_generator` — that the
  generic run's group-level winning-trapdoor set IS `GgmAdaptive.realWinSet`, so the bound transports
  verbatim to the group side. What remains is the `OptionT ProbComp` / `StateT QueryCache` monad
  threading (the `Strat → tSdhAdversary` embedding + `sampleNonzeroZMod` sampler `Pr = card/(p−1)`
  semantics) and the separate re-typing of `bindingReduction`'s adversary as a `Strat` — probability
  bookkeeping and reduction-plumbing, with the **condition provably identical**.

**Interlock verdict (verified by reading, not taken on trust).** The three files are *designed* to
interlock — `GgmRandomEncoding`'s `hdeg_handles` ↔ `GgmDegreeInvariant`'s structural `2D` ↔ the pairing
discipline — but the interlock is **architectural, not mechanized**: `GgmDegreeInvariant` imports only
`Mathlib`, references no adaptive-experiment object, and nothing imports it; there is no bridge lemma
`runTable ↔ buildPaired`. So the degree bound is proved in a **peer model**, and the adaptive /
random-encoding theorems **still carry their degree facts as undischarged hypotheses**. Honest tag: the
degree invariant is proved *structurally as a peer* and refutes the naive flat claim — but it is **not**
a discharge of the hypothesis in the experiment. Wiring the discipline into `runAux` (two-sorted handle
table, or a `runTable ↔ buildPaired` bridge) is the one remaining item on that axis; and because
`runAux`'s flat `Move.pair` admits nesting, `flat_2D_bound_false` shows `2D` is a genuine restriction the
oracle must adopt, not a property it already has.

Neither limit makes the bound a dodge — they scope *what class* and *at what level* the real
number holds.

---

## 3. Winners, by goal

- **Mergeable now → `extraction`.** The only candidate that is both sorry-free against the genuine
  tree *and* a low-invasiveness (`+41/−14`) patch with the whole tree green. It removes the
  vacuous premise and provably survives the exact attack — but hands **no number** (its RHS is
  still `tSdhExperiment` of the constructed reduction adversary). This is the safe first commit.

- **Numeric survives-attack (static) → `GGM-static`** (equivalently `AlgebraicTSdh`). The only
  mechanized candidate that delivers a real `ε = (D+1)/(p-1) < 1` proven for the whole generic
  adversary type. Scope it as **static** every time.

- **Adaptive numeric bound (explicit-oracle GGM) → `GgmAdaptive.lean` (MECHANIZED).** The
  generic-group oracle that was absent from Mathlib/VCVio is now built, and the adaptive `q`-query
  bound `(fuel·Δ + (D+1))/(p−1)` is proven sorry-free with the identical-until-bad hybrid mechanized
  by induction. Three follow-on lemma files (PAPER §9.1) narrow the residuals: `GgmRandomEncoding.lean`
  mechanizes the classical **quadratic** Shoup random-encoding number `(C(n,2)·2D + (D+1))/(p−1)` at the
  counting level (all-table-pairs bad event + table size, both THEOREMS; degree still a hypothesis);
  `GgmDegreeInvariant.lean` proves the `2D` degree invariant **structurally under the pairing discipline**
  and REFUTES the naive flat claim — but as a **peer model** not yet wired into the oracle, so the degree
  hypotheses remain undischarged (see the interlock verdict, §2); `GgmArkLibTransport.lean` mechanizes the
  **condition-level** field→group transport against ArkLib's real `tSdhCondition`, leaving only the
  `ProbComp` monad threading. `AGM` and `qdlog-direct` correctly route their numbers back through exactly
  this generic-group hardness.

---

## 4. The finding that strengthens the whole result: the vacuity is the *pattern*, not the theorem

Re-verified, sorry-free, against real ArkLib:

- **`not_qDlogAssumption` (`KzgQDlogVacuity.lean`).** State the natural "reduce KZG binding to
  q-strong-DLOG" base assumption in ArkLib's *own* idiom — recover the trapdoor `τ` from the
  power-SRS, with the same unrestricted `… → StateT unifSpec.QueryCache ProbComp (Option _)`
  adversary type — and it is **equally vacuous**: false for every error `< 1`, by the *identical*
  `Classical.choice` trapdoor extraction. So switching the named assumption (t-SDH → q-DLOG) does
  **not** escape the hole.

- **ArkLib's own `AGM/Basic.lean` is unsound as written** (source-read, `d72f8392`):
  `Adversary.run` is literally `sorry` (`AGM/Basic.lean:164–165`), the type proves zero theorems
  and is orphaned, and — decisively — `Adversary` is a `ReaderT (GroupValTable ι G) …`
  (`AGM/Basic.lean:149–153`) that hands the adversary the **concrete** group table over the
  concrete group `G`, so its outputs can still depend on discrete logs. The author's own comments
  flag exactly this: *"TODO: need to be sure this definition is correct"* (line 147) and *"How to
  make the adversary truly independent of the group description? It could have had `G` hardwired"*
  (lines 169–173).

**Consequence:** the vacuity is not a t-SDH typo; it is the whole *unrestricted-adversary pattern*
in this idiom. Any concrete-group hardness assumption stated as `∀ (unrestricted adversary),
Pr[win] ≤ ε < 1` is `Classical.choice`-false, and the ecosystem lacks a sound generic/algebraic
adversary class to state it against. That is what makes the mechanized static-GGM bound above
worth having: it is the first sound, restricted-class numeric hardness statement in the tree.

---

## 5. Honest recommendation

1. **Ship `extraction` first** as the immediate, backward-compatible de-vacuation
   (`binding_reduces_to_tSdh` primary, `binding` a corollary). It is mergeable today and costs
   nothing in soundness.
2. **Adopt `GGM-static` as the mechanized numeric floor**, stated *precisely as the static
   fragment*, to discharge the single reduction obligation `extraction` isolates — for the static
   adversary class. Do not let it be read as the full adaptive number.
3. **Name the narrowed frontier precisely.** The generic-group oracle (once absent from Mathlib/VCVio),
   the adaptive linear bound, the quadratic random-encoding counting bound, and the condition-level
   field→group transport are all now MECHANIZED (PAPER §9.1). What remains, scoped: (a) **wire the
   structural `2D` degree invariant into `runAux`** — it is proved only for a peer model
   (`GgmDegreeInvariant`, not imported), so the Shoup adaptive/random-encoding theorems still carry the
   degree facts as hypotheses (interlock verdict, §2); (b) **thread the `ProbComp` monad** to reach the
   literal `tSdhExperiment` inequality (condition already provably identical); (c) re-type
   `bindingReduction`'s adversary as a `Strat` so the binding reduction inherits the bound.
4. **Present the q-DLOG-idiom vacuity and the AGM stub as evidence that the pattern is systemic** —
   the reason a sound restricted adversary class (not a renamed assumption) is the real fix.
