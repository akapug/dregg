# Novel candidate — algebraic/generic-group t-SDH with a proven Schwartz–Zippel (Boneh–Boyen) number

**Status:** local, mechanized `sorry`-free against a scratch ArkLib @ `d72f8392` (Lean
`v4.31.0`). Nothing filed, pushed, or PR'd. Artifact: `candidates/AlgebraicTSdh.lean`
(byte-copy of the compiled `/private/tmp/arklib-review/AlgebraicTSdh.lean`).

This is the fix the two enumerated options (REPAIR.md's **(A) naïve AGM**, **(B) extraction
shape**) leave on the table: a **number**. (A) was flagged as not even closing the vacuity;
(B) closes it but yields a reduction with nothing to falsify. This candidate supplies the
*restricted-adversary bound* that (B)'s own docstring says is missing — "`binding` only becomes
informative once the assumption is stated over a restricted (e.g. algebraic-group-model)
adversary class" — and it supplies it as a **proven real number**, `(D+1)/(p-1)`, not another
assumption.

It is best read as **option C, the numeric floor under B**, not a competitor to B.

---

## 1. Why every naïve fix fails, stated once and precisely

In classical Lean, over any concrete finite `Group`, **every** function is inhabited by
`Classical.choice`; dlog is choice-definable via ArkLib's own `exists_zmod_power_of_generator`.
Therefore **any** hardness statement of the shape

```
∀ (adversary : ‹concrete-group inputs› → ProbComp ‹output›), Pr[win] ≤ error < 1
```

is false whenever a winner exists in principle — which for t-SDH / q-DLOG / DLOG it always does
(finite group). This is the whole disease, and it is why the prompt's "no free lunch" is real:

- **Naïve AGM (A) does not survive.** Make the adversary also return a representation. The SRS
  basis is `{g₁^(τ^i)}_{i≤D}`, and a *constant* polynomial `P = 1/(τ+c)` (degree 0) already
  represents the winning element `g₁^(1/(τ+c))`. `Classical.choice` extracts `τ`, returns the
  element **and** the genuinely-valid representation `(1/(τ+c), 0, …, 0)`. The representation is
  free data, exactly as the prompt warns.
- **"Return only the coefficients" does not survive either.** If the adversary still *takes the
  SRS as input*, `Classical.choice` computes `τ` from it and bakes `1/(τ+c)` into the constant
  coefficient. The representation restriction is empty as long as `τ` is reachable from the
  input.
- **Reducing to q-DLOG buys nothing by itself.** q-DLOG stated with the same unrestricted,
  concrete-group adversary is *also* false below 1 (the choice adversary reads `g₂^τ` and
  outputs `τ`). A reduction from vacuous-t-SDH to vacuous-q-DLOG transports the vacuity; it does
  not remove it. A number cannot rest on q-DLOG-as-a-∀-Prop.

**The only two escapes are:** (a) drop the ∀-Prop and state a per-adversary reduction bound —
this is option B, and it has no number; or (b) **change the adversary type so the winner is no
longer choice-definable** — which forces a boundary where `τ` is *not in the adversary's scope*.
This candidate is (b), taken in its lightest sound form.

## 2. The model — the algebraic adversary as a τ-independent committed polynomial

The AGM/GGM insight, encoded so it is *genuinely restrictive*:

> An algebraic (generic) adversary can only produce a G₁ element by taking `ZMod p`-linear
> combinations of the G₁ SRS elements `{g₁^(τ^i)}_{i≤D}` it was handed. Every element it outputs
> is therefore `g₁^(P τ)` for an **exponent polynomial `P` of degree ≤ D whose coefficients it
> chose from the abstract handles — with no access to the value τ**, which is sampled only
> afterwards.

Concretely (`AlgebraicTSdh.lean`):

```lean
structure AlgAdversary (D : ℕ) where       -- no `srs` input: the boundary that defeats choice
  offset : ZMod p
  poly   : (ZMod p)[X]
  hdeg   : poly.natDegree ≤ D

noncomputable def algExperiment (D) (A : AlgAdversary D) : ℝ≥0∞ :=
  Pr[fun τ => (τ + A.offset) * A.poly.eval τ = 1 | Groups.sampleNonzeroZMod (p := p)]
```

`(τ + c) * P.eval τ = 1` is exactly `g₁^(P τ) = g₁^(1/(τ+c))` in a prime-order group — the
identical t-SDH winning condition, over the *identical* `sampleNonzeroZMod` trapdoor
distribution the vacuity attack used. The two modelling moves that close the hole, both essential:

1. **The output is the polynomial, not a group element** — nothing to hand `Classical.choice` a
   free winning element for.
2. **`τ` is not in the adversary's scope.** `AlgAdversary` has no `srs` argument. `τ` is sampled
   *inside* `algExperiment`, after `A` is fixed. There is no expression of type `ZMod p` equal to
   `τ` anywhere in the adversary's construction, so `Classical.choice` has nothing to invert.

This is Maurer's generic-group adversary specialised to the non-interactive case, and it is the
same "algebraic representation" object as Fuchsbauer–Kiltz–Loss 2018 — but with the boundary the
naïve encoding lacked: the coefficients are committed *before* the trapdoor exists.

## 3. Survives the exact attack — **PROVEN**, `sorry`-free

The disclosure proved the original false with `not_tSdhAssumption` (experiment `= 1`). This
candidate proves the exact positive mirror. The load-bearing fact is Schwartz–Zippel on the
witness polynomial `Q c P := (X + C c) * P - 1`:

```lean
-- Q is never the zero polynomial (a degree count: (X+C c)*P = 1 is impossible), degree ≤ D+1.
theorem alg_winning_set_card_le (D c P) (hP : P.natDegree ≤ D) :
    (witnessPoly c P).roots.toFinset.card ≤ D + 1

-- Hence the number of winning trapdoors is ≤ D+1 (out of ≥ p-1 nonzero samples):
theorem alg_num_winning_trapdoors_le (D c P) (hP : P.natDegree ≤ D) :
    {τ : ZMod p | (τ + c) * P.eval τ = 1}.ncard ≤ D + 1

-- The probability form, over the real sampleNonzeroZMod distribution:
theorem algExperiment_le (D) (A : AlgAdversary D) :
    algExperiment D A ≤ (D + 1 : ℝ≥0∞) / ((p - 1 : ℕ) : ℝ≥0∞)

-- THE GATE — the exact contrast with the prob-1 unrestricted attack:
theorem alg_survives_attack (D) (hp : D + 2 < p) (A : AlgAdversary D) :
    algExperiment D A < 1
```

`alg_survives_attack` is the survival, mechanized: in the regime `p > D + 2` (the same shape as
the sibling ARSDH statement's `p ≥ n + 2`), **every** algebraic adversary — including any built
by `Classical.choice` — wins with probability *strictly below 1*, whereas
`KzgVacuity.tauExtractingAdversary` won with probability *exactly 1*. The trapdoor-extracting
attack cannot be replayed: to win at `c = 0` it would need `P` with `P(τ) = 1/τ`, but `P` is a
committed `(ZMod p)[X]` value with no τ in scope; the closest any inhabitant gets is some fixed
polynomial, which the Schwartz–Zippel bound pins below 1. A canary
(`algExperiment_zeroPoly = 0`) shows the experiment discriminates, so the `< 1` bound is not a
`probEvent`-machinery artifact.

All four theorems: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Verified by
`#print axioms`.

## 4. The number, and what it rests on — **no free lunch, named**

- **Number:** `algExperiment A ≤ (D+1)/(p-1)`. For BabyBear/BN254-scale `p` and practical `D`
  this is ~`D/p`, i.e. `2^{-240}`-ish — a real, falsifiable-in-principle bound, not `≤ 1`.
- **Rests on:** the **generic/algebraic group model**. The bound is *unconditional and proven*
  for the algebraic adversary class. What is assumed — and this is the honest boundary — is that
  a real adversary against concrete-group t-SDH is captured by an algebraic one of comparable
  advantage. That is the Boneh–Boyen 2004 GGM theorem for q-SDH (and the FKL18 algebraic-model
  meta-theorem); it is an *idealization*, not a Lean theorem here. **The number rests on GGM.**
  It does **not** rest on q-DLOG: the direct Schwartz–Zippel bound on the committed
  representation *is* the core of Boneh–Boyen's GGM proof, so this candidate skips the q-DLOG
  reduction entirely (and thereby skips having to soundly re-state q-DLOG, which suffers the
  identical vacuity).
- **Recognized formulation?** Yes — Maurer's GGM adversary / the Boneh–Boyen SDH generic-group
  analysis / the FKL18 algebraic representation. This is the textbook object.
- **Honest gap in the constant.** The mechanized bound `(D+1)/(p-1)` is the single-winning-event
  Schwartz–Zippel term. The full *interactive* GGM accounting (equality/collision events across
  `q` group-operation queries, Shoup-style) contributes the familiar lower-order `O((q+D)²/p)`.
  This candidate mechanizes the core event; the query-collision terms are not modelled (the
  adversary here is non-interactive). Group operations do not raise the degree past `D` — they
  are linear combinations of the G₁ SRS exponents — so the *degree* bound is exact; only the
  adaptive collision accounting is deferred.

## 5. How it completes option B (the elegant composition)

Option B proved, unconditionally, `binding_advantage(adv) ≤ tSdhExperiment(bindingReduction adv)`
and isolated the exact obligation: *bound the success of the one reduction adversary.*
`bindingReduction` constructs its t-SDH output as `g₁^(explicit polynomial in the SRS)` — it is,
by construction, an **algebraic** adversary. So:

```
binding_advantage(adv)  ≤  tSdhExperiment(bindingReduction adv)   -- option B, unconditional
                        ≤  (D+1)/(p-1)                            -- this candidate, once the
                                                                   -- reduction adversary is
                                                                   -- typed algebraic
```

B supplies the reduction; C supplies the number B's docstring asks for. Together they give a
numeric, non-vacuous binding bound.

## 6. Invasiveness — honest

**More invasive than B, less than a full interactive GGM.** What ships today
(`AlgebraicTSdh.lean`, ~216 lines, self-contained, imports only `ArkLib…KZG.Sampling` + Mathlib
polynomials) is the *proven algebraic-side bound*. To land it in ArkLib as a deployed guarantee
you additionally need, in rough order of effort:

1. **Type the reduction adversary as algebraic.** Give `bindingReduction`'s output the
   `AlgAdversary` shape (it already builds `g₁^poly`; thread the `poly` + degree proof). Small–
   medium; this is the honest core of what REPAIR.md's option (A) called "rework
   `bindingReduction` so its output comes with a representation".
2. **State `tSdhAssumption` (or a new `tSdhAssumptionAlg`) over `AlgAdversary`** and replace its
   `∀`-over-unrestricted-functions. `algExperiment_le` discharges it with a number.
3. **(The hard, deferred piece — months away.)** The *faithfulness* lemma: every concrete
   `tSdhAdversary` induces an `AlgAdversary` of comparable advantage. This is the GGM/AGM
   meta-theorem. It is genuinely new metatheory (an extraction/generic-group boundary ArkLib and
   VCVio do not have), and it is the price of the number. Without it, the number is a statement
   *about algebraic adversaries*; with it, a statement about all adversaries.

So: the **survival + the number are mechanized now**; the **deployment into ArkLib's live
reduction is partial** (steps 1–2 are ordinary work, step 3 is the standing metatheoretic gap
that any numeric t-SDH bound must pay).

## 7. Verdict

| axis | this candidate |
|---|---|
| survives the exact attack | **PROVEN** (`alg_survives_attack`, `sorry`-free) |
| standard formulation | yes — Maurer GGM / Boneh–Boyen SDH / FKL18 algebraic adversary |
| gives a real number | **yes** — `(D+1)/(p-1)` |
| what the number rests on | **GGM ideal model** (not q-DLOG, not a bare reduction) |
| minimal diff to ArkLib | core proven standalone; ArkLib deployment partial (faithfulness deferred) |
| mechanizable today | **the bound + survival ARE mechanized**; faithfulness reduction is months away |

The one thing a judge cannot do is inhabit a winner: `alg_survives_attack` is a `sorry`-free
theorem that *every* algebraic adversary, `Classical.choice`-built or not, wins with probability
`< 1`. That is the gate, passed and checked.

**Artifact:** `candidates/AlgebraicTSdh.lean`. Rebuild:
`cd <arklib@d72f8392> && cp candidates/AlgebraicTSdh.lean . && lake env lean AlgebraicTSdh.lean`
(green, no `sorry`; append the `#print axioms` lines for the closure above).
