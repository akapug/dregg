// Two-panel research summary of PAPER.md (this directory).
// One A3-landscape page = two A4-sized panels side by side, screenshot-ready as a spread.
// Compile: typst compile twopager.typ twopager.pdf

#let accent = rgb("#1e5f74")
#let inkdim = luma(90)
#let sans = "Helvetica Neue"

#set page(paper: "a3", flipped: true, margin: (top: 10.5mm, bottom: 9.5mm, x: 14mm))
#set text(font: "Libertinus Serif", size: 9.3pt, fill: luma(25))
#set par(justify: true, leading: 0.545em, spacing: 0.88em)

#show raw: set text(font: "DejaVu Sans Mono")
#show raw.where(block: false): set text(size: 8.1pt, fill: accent.darken(35%))
#show raw.where(block: true): it => block(
  fill: luma(249),
  stroke: (left: 1.4pt + accent.lighten(45%), rest: 0.4pt + luma(228)),
  inset: (x: 3.0mm, y: 2.1mm),
  width: 100%,
  radius: 1.5pt,
  text(size: 7.7pt, it),
)

#show heading.where(level: 1): it => block(above: 0mm, below: 3.0mm, {
  text(font: sans, size: 14pt, weight: "bold", fill: accent, it.body)
  v(1.4mm)
  line(length: 100%, stroke: 0.9pt + accent.lighten(35%))
})
#show heading.where(level: 2): it => block(
  above: 3.3mm, below: 1.6mm,
  text(font: sans, size: 10.2pt, weight: "bold", fill: accent.darken(15%), it.body),
)

#set list(marker: text(fill: accent, "▸"), indent: 1.2mm, body-indent: 1.8mm, spacing: 0.62em)

// ── Title banner ────────────────────────────────────────────────────────────
#block(width: 100%)[
  #grid(columns: (1fr, auto), column-gutter: 8mm, align: (left + bottom, right + bottom),
    [
      #text(font: sans, size: 21pt, weight: "bold", fill: luma(15))[Vacuity and Repair]
      #h(3.5mm)
      #text(font: sans, size: 12.5pt, fill: inkdim)[the generic-group security of KZG evaluation binding, from a mechanized formalization-soundness finding]
    ],
    [
      #text(font: sans, size: 8pt, fill: inkdim, align(right)[
        ArkLib #raw("d72f8392") · Lean v4.31.0 \
        two independent checkers · summary of #raw("PAPER.md")
      ])
    ],
  )
  #v(1.8mm)
  #line(length: 100%, stroke: 1.4pt + accent)
  #v(1.6mm)
  #text(size: 9.9pt)[
    ArkLib's KZG evaluation-binding theorem is axiom-clean *and* carries no information at any parameter: its `t`-SDH assumption quantifies over an unrestricted adversary type, which a `Classical.choice` trapdoor extractor inhabits with success probability exactly 1. We mechanize the refutation, the extraction-shaped repair that provably survives the exact attack, and the generic-group security bound — now mechanized *end to end* on ArkLib's real `tSdhExperiment`, over the generic-restricted class, with the side-conditions named.
  ]
  #v(1mm)
  #text(font: sans, size: 8pt, fill: inkdim)[
    Research note — internal, not filed, not a security advisory: a *formalization-soundness* issue in a public, in-development library, not a vulnerability in any deployed system. KZG, `t`-SDH, and the reduction are sound as normally stated — the issue is a Lean quantifier. The central generic-group argument is complete and mechanized end to end.
  ]
]
#v(3mm)

// ── Two panels ──────────────────────────────────────────────────────────────
#grid(columns: (1fr, 1fr), column-gutter: 10mm,

// ═══ LEFT PANEL — the finding ═══
[
= I · The finding: axiom-clean, and empty

== The mechanism
KZG evaluation binding is proved in ArkLib by a correct, constructive reduction to the `t`-SDH assumption — whose adversary is a *plain, unrestricted function type*:

```lean
abbrev tSdhAdversary (D : ℕ) :=
  Vector G₁ (D+1) × Vector G₂ 2 → StateT unifSpec.QueryCache ProbComp (Option (ZMod p × G₁))

def tSdhAssumption (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : tSdhAdversary D), tSdhExperiment D adversary ≤ error
```

`ProbComp` is a free monad over oracle queries: only `query` nodes cost anything; pure computation is free and no resource bound is imposed anywhere. The SRS includes the verifier leg $(g_2, g_2^tau)$, which determines $tau$ whenever $g_2 eq.not 1$, and ArkLib's own `exists_zmod_power_of_generator` (`Algebra.lean:105`) makes the discrete log `Classical.choice`-definable. The adversary reads $g_2^tau$, recovers $tau$, and returns the `t`-SDH solution #box($(c = 0, g_1^(1\/tau))$) — zero oracle queries, success probability exactly 1.

```lean
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) : tSdhAdversary D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf hg₂ srs.2[1]).val))

theorem tSdhExperiment_tauExtractingAdversary : tSdhExperiment D (…) = 1
theorem not_tSdhAssumption      (herr : error < 1) : ¬ tSdhAssumption D error
theorem tSdhAssumption_trivial_of_one_le (1 ≤ error) : tSdhAssumption D error
```

== No content at any parameter
Below 1 the assumption is refuted; at $gt.eq 1$ its conclusion is the triviality "a probability is $lt.eq 1$." `binding` consumes the assumption in the last step of its `calc`, and its hypothesis `hpair : pairing g₁ g₂ ≠ 0` *forces* $g_2 eq.not 1$ (a bilinear map kills the identity) — exactly what the extractor needs. So `binding`'s hypotheses are jointly unsatisfiable for any error below 1 (`binding_hypotheses_unsatisfiable`), and its conclusion is free at $gt.eq 1$. The sibling ARSDH assumption falls identically, taking `function_binding` with it. A canary — the giving-up adversary scores exactly 0 — confirms the experiment discriminates. The reduction itself is fully constructive and algebraically correct; the vacuity lives entirely in the assumption's quantifier.

== The pattern, not a typo
Reducing to a *different* base assumption does not escape. The natural `q`-DLOG assumption, stated in ArkLib's own unrestricted-adversary idiom, is equally false below 1 (`not_qDlogAssumption`, same extraction, own canary). And ArkLib's algebraic-group-model scaffolding confirms the disease from the other side: `AGM/Basic.lean` is a stub (its adversary's `run` is literally `sorry`; zero theorems; orphaned) and is *unsound as written* — the adversary is a `ReaderT` over the concrete group table, so its outputs can still depend on discrete logs. Its author flags the open problem verbatim: #quote[TODO: need to be sure this definition is correct]; #quote[How to make the adversary truly independent of the group description? It could have had `G` hardwired.] Any concrete-group assumption of the shape $forall "unrestricted adversary", "Pr"["win"] lt.eq epsilon < 1$ is `Classical.choice`-false in this idiom.

== The methodological point: axiom checks are blind to vacuity
`binding`, the refutation, and the winning adversary all print the *same* clean axiom closure:

```lean
#print axioms not_tSdhAssumption   -- [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, nothing any `#print axioms` / `#assert_axioms` gate would flag. *Axiom-clean and vacuous coexist.* The blindness is structural: an axiom check reports a proof term's closure; it never asks whether the theorem's *hypotheses* are jointly satisfiable, and any `def FooHard : Prop` used as a hypothesis is an assumption no axiom check inspects. Query-based bounds (`IsQueryBoundP`) do not help either — the winning adversary makes zero queries. The only reliable test is adversarial: try to *inhabit the assumption's negation* — prove the floor false at its deployed parameters. We found the identical pattern in our own hardness floors first, in several places, before ever looking at ArkLib; we present this as a field lesson, not a dunk.
],

// ═══ RIGHT PANEL — the repair + the end-to-end theorem ═══
[
= II · The repair, the number, and the end-to-end theorem

== The mergeable de-vacuation (mechanized)
ArkLib's reduction is already constructive, and the assumption is consumed at exactly one `calc` step — so split there. The unconditional prefix becomes the primary theorem; the original `binding` becomes a one-line corollary.

```lean
theorem binding_reduces_to_tSdh … (adversary : KzgBindingAdversary …) :
    bindingExperiment … adversary
      ≤ tSdhExperiment g₁ g₂ n (bindingReduction … adversary)
```

No assumption `Prop`: both sides are concrete probabilities, true at every parameter — nothing for `Classical.choice` to inhabit (+41/−14 in one file; whole tree builds, 2994 jobs; axiom-clean). It *provably survives the exact attack* (`repair_survives_attack`): in one `sorry`-free closure, the trapdoor adversary still refutes `tSdhAssumption` below 1 *and* the repaired bound holds regardless — the unsatisfiable premise removed, every step of the reduction kept, the one obligation a sound assumption class must discharge isolated.

== The number: the generic bilinear group bound
Group elements become opaque handles carrying *ordinary* polynomials in $ZZ_p [X]$ — *not Laurent*: group inversion negates the exponent, it never introduces $X^(-1)$. A winning $1\/(X+c)$ is therefore unrepresentable, and a "win" forces the nonzero, degree-$lt.eq D+1$ polynomial $F_ell dot (X+c) - 1$ to vanish at the random $tau$. Simulation (identical-until-bad) plus Schwartz–Zippel yield Boneh–Boyen's Theorem 12, verified line by line against the source:
$ epsilon space lt.eq space (q_G + D + 3)^2 (D+1) / (p-1) space = space O((q_G + D)^2 dot D \/ p) $
*Not* a clean $q^2\/p$: the bound is cubic in the SRS degree $D$, and at production parameters the $D^3\/p$ term is the one to watch (Corollary 13's $q < O(p^(1\/3))$ side condition). Naive AGM is not a shortcut — a `Classical.choice` adversary returns a *valid* representation too; validity is not independence — it relocates the same content onto `q`-DLog's generic hardness.

== The end-to-end theorem #text(size: 8.4pt, fill: inkdim, font: sans)[(mechanized, `sorry`-free, no `sorryAx`)]
The generic-group bound is now a *complete* mechanized theorem about ArkLib's *own* `Groups.tSdhExperiment`, restated nowhere. For every generic strategy `strat` and query budget `fuel`:

```lean
tSdh_ggm_sound : tSdhExperiment D (embed strat) ≤ (C(fuel+D+4, 2)·D + (D+1)) / (p − 1)
```

the Shoup random-encoding number at $delta = D$, a genuine $< 1$ in the standard regime (`tSdh_ggm_sound_lt_one`). *Why it escapes the vacuity:* it does *not* quantify over the full `tSdhAdversary` type — over which the statement is provably *false* (Panel I) — but over the *image of the generic embedding* `embed`: a strategy receives only equality booleans, never a group element, so it realizes only $g_1^(f(tau))$ with $deg f lt.eq D$ — exactly what the counting bound bounds. `#print axioms` on the capstone and its full spine: `[propext, Classical.choice, Quot.sound]`. *Honest side-conditions, named* — "sound" means sound under these: $1 lt.eq D$ (genuinely *false* at $D = 0$: with no pairing, a $G_1$ adversary cannot form $g_1^tau$); $2 lt.eq p$; $"orderOf" g_1 = p$ (with $g_1, g_2 eq.not 1$); ArkLib's own `SampleableType` instance; the $< 1$ regime $binom("fuel"+D+4, 2) dot D + (D+1) < p-1$.

== The mechanized spine #text(size: 8.4pt, fill: inkdim, font: sans)[(all `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`)]
- *Vacuity refutations* — `t`-SDH, ARSDH, `q`-DLOG, each with a discriminating canary, against genuine ArkLib. *The repair and its survival* — `binding_reduces_to_tSdh`, `repair_survives_attack`.
- *The counting bounds* — static core `ggm_tSdh_sound`: $epsilon lt.eq (D+1)\/(p-1)$ over the *entire* committed-generic type (the trapdoor extractor is untypable here; as far as our census found, the first generic-group security theorem in Lean); Maurer explicit-equality `adaptive_ggm_sound` (identical-until-bad *proven by induction*, not assumed); Shoup random-encoding `rand_encoding_bound` (all-pairs bad event and table size are theorems; its $delta = D$ specialization feeds the capstone).
- *Degree discharge on the ACTUAL oracle* — ArkLib's `tSdhAdversary` is granted *no pairing map*, so the oracle is purely linear; `hdeg_out_of_run` / `hdeg_handles_of_run` prove $"natDegree" lt.eq D$ by induction on the *real* `runAux`/`runTable` recursion — the degree hypotheses are theorems, the $delta = D$ bound hypothesis-free.
- *The wiring* — `embed` / `embed_run_correspondence` (the group run steps in lockstep with the symbolic run); `experiment_eq_count` (ArkLib's game collapses to $("winSet.card")\/(p-1)$ — no monad plumbing left); `groupWinSet_eq_realWinSet` (the win predicate *is* ArkLib's real `tSdhCondition`, by prime-order injectivity).

== Off the critical path #text(size: 8.4pt, fill: inkdim, font: sans)[(optional — gates nothing)]
The pairing-aware $delta = 2D$ variant (`degree_invariant_paired`; the naive flat-table $2D$ claim *refuted*, $X^4$ at $D=1$) is for a *pairing-endowed* oracle the ArkLib adversary does not have — the honest ceiling for a stronger, off-interface adversary. And re-typing `bindingReduction`'s adversary as a `Strat` — a convenience, not a gap: the result already holds for the whole `embed` image.
],
)

// ── Footer ──────────────────────────────────────────────────────────────────
#v(1fr)
#line(length: 100%, stroke: 0.6pt + luma(200))
#v(1.2mm)
#text(size: 7.5pt, fill: inkdim, font: sans)[
  *Artifacts* (this directory, all `sorry`-free against ArkLib `d72f8392`): #raw("KzgVacuity.lean") · #raw("binding-repair.patch") · #raw("RepairSurvives.lean") · #raw("candidates/{GgmCandidate, GgmAdaptive, GgmRandomEncoding, GgmDegreeInvariant, GgmDegreeDischarge, GgmArkLibTransport, GgmProbThreading, GgmEmbed, GgmEndToEnd, KzgQDlogVacuity}.lean") — capstone: #raw("GgmEndToEnd.tSdh_ggm_sound").
  *Reproduce:* drop #raw("KzgVacuity.lean") into #raw("ArkLib/Scratch/"), #raw("lake build"); #raw("#print axioms") → #raw("[propext, Classical.choice, Quot.sound]").
  *References:* [KZG10] Kate–Zaverucha–Goldberg · [BB04/BB08] Boneh–Boyen (Thm 12, Cor 13) · [Sho97] Shoup · [Mau05] Maurer · [FKL18] Fuchsbauer–Kiltz–Loss · [CGKY25] Chiesa–Guan–Knabenhans–Yu.
]
