# PR description — draft (not filed; ember opens the PR)

Base: `Verified-zkEVM/ArkLib` @ `d72f8392ff03047dc5386f4f4bb513743e7ada65`.
Branch: `emberian/ArkLib:kzg-vacuity-pr`.

---

## Title

**`feat(KZG): de-vacuate evaluation binding and prove the t-SDH GGM soundness bound`**

(If a single `<type>` must be chosen, this leads with the soundness formalization it adds;
the one-line fix to `Binding.lean` is the `fix(KZG):` commit inside it. Happy to retitle
`fix(KZG): …` if you would rather foreground the de-vacuation.)

---

## Body

**This is not a security advisory.** There is no vulnerability, nothing exploitable, and no
embargo. KZG, the `t`-SDH assumption as normally stated, and the reduction in `Binding.lean`
are all sound. The issue is the *quantifier* in one Lean assumption. We ran an adversarial
"try to prove each hardness floor false at its deployed parameters" audit on our own Lean tree,
found the identical unrestricted-quantifier pattern in several of our own floors first, and
bring it here as a shared field lesson. Everything below reproduces against `d72f8392`, is
`sorry`-free, and has axiom closure exactly `[propext, Classical.choice, Quot.sound]`.

### Motivation: `tSdhAssumption` is `Classical.choice`-false, so `binding` is vacuous

`Groups.tSdhAssumption` quantifies over an *unrestricted* adversary type. `tSdhAdversary` lands
in `StateT unifSpec.QueryCache ProbComp`, and because `ProbComp` is a free monad over oracle
queries, **pure computation is free** — an adversary may `pure` an arbitrary noncomputable
function of the SRS at zero cost. The SRS includes the verifier leg `(g₂, g₂^τ)`, which
determines `τ` whenever `g₂ ≠ 1`, and ArkLib's own `Algebra.lean:105
exists_zmod_power_of_generator` makes that discrete log `Classical.choice`-definable. A one-line
adversary recovers `τ`, returns the `t`-SDH solution `(c = 0, g₁^{1/τ})`, and wins with
probability *exactly* `1` (zero oracle queries). Consequently:

- `tSdhAssumption D error` is **false for every `error < 1`** (`not_tSdhAssumption`), and
  trivially true for `error ≥ 1` since a probability is `≤ 1` (`tSdhAssumption_trivial_of_one_le`).
- `KZG.CommitmentScheme.binding` takes `tSdhAssumption` as a hypothesis and concludes a bound at
  the *same* `error`, so it carries no information at any parameter. Its own
  `hpair : pairing g₁ g₂ ≠ 0` even forces `g₂ ≠ 1`, discharging the killing adversary's one
  hypothesis from `binding`'s own premises (`binding_hypotheses_unsatisfiable`).
- The sibling `Groups.arsdhAssumption` — hypothesis of `KZG.function_binding` — has the identical
  unrestricted quantifier and falls the identical way (`not_arsdhAssumption` /
  `arsdhAssumption_trivial_of_one_le`); the ARSDH branch's `D + 2 ≤ p` is exactly the `p ≥ n + 2`
  that `function_binding` already carries.

`#print axioms` does not catch this: `binding` is axiom-clean *and* vacuous at the same time. A
clean axiom closure certifies "no `sorry`, no `native_decide`"; it says nothing about whether a
hypothesis is satisfiable. Canaries (`tSdhExperiment_givingUpAdversary = 0`,
`arsdhExperiment_givingUpAdversary = 0`) confirm the `= 1` is a fact about *this* adversary, not
an artifact of the probability machinery.

### What this PR changes

**1. The fix — an unconditional reduction (`+42 / −14`, `Binding.lean` only).** `t`-SDH is an
*algebraic* assumption whose killing adversary makes zero queries, so query-bounding (the right
tool for random-oracle/hash floors) constrains something it never does. Instead we observe that
ArkLib's reduction is **already fully constructive**: `binding`'s proof is a five-step `calc`, and
`tSdhAssumption` is consumed in exactly one place — the last `≤`. Splitting the calc there yields
`binding_reduces_to_tSdh`, which carries the full constructive content *without* the
universally-quantified assumption — it relates two concrete probabilities (*this* adversary's
binding advantage and *its* reduction's `t`-SDH success), so there is no assumption `Prop` for a
`Classical.choice` adversary to inhabit, and it has content at every parameter. `binding` keeps
its exact signature as a one-line corollary (backward compatible). `RepairSurvives.lean` proves
the de-vacuation *survives the exact attack* (`repair_survives_attack`): the trapdoor-extracting
adversary still refutes `tSdhAssumption` below `1`, and `binding_reduces_to_tSdh` holds
unconditionally — nothing left to empty.

**2. The sound number — `t`-SDH in the generic group model, both standard models, both wired.**
The fix removes the vacuity but hands no number; the number a KZG binding bound rests on is the
generic-group hardness of `t`-SDH. We mechanize it in **both** standard GGM formulations and wire
**both** to ArkLib's real `tSdhExperiment`, each yielding the Boneh–Boyen numerator
`C(fuel+D+4, 2)·D + (D+1)` over `p − 1`:

- **Maurer explicit-equality** (`GgmEndToEnd.tSdh_ggm_sound`, + `_lt_one`), wired via `embed`.
- **Shoup random-encoding / free-comparison** (`GgmShoup.shoup_ggm_sound` model-internal, then
  `GgmShoupEmbed.shoup_tSdh_ggm_sound` + `_lt_one` wired via `embedShoup`). Free comparison is
  *realized, not assumed*: in a prime-order group the exponent encoding `a ↦ g₁^{a.val}` is
  injective, so the adversary's real pairwise `DecidableEq G₁` equality matrix equals the
  symbolic pattern the strategy branches on (`groupEqPattern_eq`).

Each capstone quantifies over the **image of its embedding** into `tSdhAdversary` — the
generic-restricted class that escapes §1's refutation (over the full type the statement is false).
Group elements carry *ordinary* polynomials in `X` (not Laurent: inversion negates the exponent),
which is exactly why a winning `1/(X+c)` output is unrepresentable and forces a bounded-degree
root event. The `< 1` companions give genuine content in the standard regime
`C(fuel+D+4,2)·D + (D+1) < p − 1` (`≈ 2⁻²³⁴` at cryptographic parameters).

To our knowledge — a census of ArkLib, VCVio, and Mathlib — no generic-group-model security
*theorem* previously existed in Lean, so this is a candidate first of its kind. (ArkLib's
`AGM/Basic.lean` is a WIP stub — `Adversary.run` is `sorry`, and its adversary is a `ReaderT` over
the concrete group table, so outputs can still depend on discrete logs. The extraction-shaped fix
is the right first step regardless of whether you later complete that module to opacity: it
isolates the single obligation any restricted assumption must discharge.)

### Contrast with previous behavior

- Before: `binding` / `function_binding` are provable but vacuous — their `tSdhAssumption` /
  `arsdhAssumption` premises are unsatisfiable below error `1` and their conclusions free at or
  above it. No parameter carries information.
- After: `binding_reduces_to_tSdh` is an unconditional, content-bearing reduction at every
  parameter; `binding` remains as its corollary with an unchanged signature; and the number the
  reduction points at is proved sound in two independent GGM models against the real experiment,
  with every side-condition named.

### Honest scope / side-conditions

`1 ≤ D` (the meaningful KZG regime); `2 ≤ p`; `orderOf g₁ = p` for both tracks' transport into
`tSdhExperiment` (generator, for encoding injectivity); Maurer additionally carries ArkLib's own
`[∀ i, SampleableType (unifSpec.Range i)]` verbatim. The bound is the classical Boneh–Boyen shape
`O((q_G + D)²·D / p)` — degree-dependent, not a clean `q²/p`. `GgmRandomEncoding` additionally
carries, clearly labelled **off-path**, a conservative pairing-capable `δ = 2D` variant not
consumed by either capstone. The `Classical.choice` in the vacuity theorems is the *content* (the
unbounded extractor exhibited as a legal inhabitant of the unrestricted type), not a smell.

### Structure and review

The branch is 16 argument-ordered commits, each `git checkout`-able and `lake build`-green: the
finding, the `fix(KZG):` de-vacuation, its survival proof, the GGM dependency spine in import
order, the two capstones, the BibTeX, and the README. Every headline theorem is `sorry`-free with
axiom closure exactly `[propext, Classical.choice, Quot.sound]`. All new Lean lives under
`ArkLib/Scratch/KzgVacuity/`; the only edit to an existing file is `Binding.lean` (the fix) and
the six added references in `blueprint/src/references.bib`.

**This is a large contribution, and we are happy to split it** — the one-file `Binding.lean`
de-vacuation (with `KzgVacuity.lean` + `RepairSurvives.lean` as the finding-and-survival evidence)
stands on its own as a small, self-contained PR, and the GGM soundness formalization can follow as
a second. Tell us which shape you prefer and we will restructure.

A two-pager (`twopager.pdf`) is available as a visual blueprint-style companion to this branch.

### References

`[BB04]` Boneh–Boyen, *Short Signatures Without Random Oracles* · `[KZG10]` Kate–Zaverucha–Goldberg
· `[Sho97]` Shoup, *Lower Bounds for Discrete Logarithms* · `[Mau05]` Maurer, *Abstract Models of
Computation in Cryptography* · `[FKL18]` Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model* ·
`[Sch80]` Schwartz · `[Zip79]` Zippel. (Added to `blueprint/src/references.bib`.)
