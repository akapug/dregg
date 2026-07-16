# The honest repair — turning "your `KZG.binding` is vacuous" into "here is a fix"

**Status:** local, reviewable. NOTHING filed, pushed, or PR'd. This is a *proposal* to the
ArkLib maintainers, mechanized against a scratch copy of ArkLib @ `d72f8392`
(`/private/tmp/arklib-review`, Lean `v4.31.0`), not a correction from on high. The EF's
reduction in `Binding.lean` is careful, correct work; the fix keeps all of it.

Companion files in this directory:
- `binding-repair.patch` — the real diff against ArkLib's `Binding.lean` (+41 / −14).
- `RepairSurvives.lean` — the `sorry`-free mechanized non-vacuity proof (the fix survives
  the exact attack that killed the original).
- The vacuity itself: `KzgVacuity.lean`, `DISCLOSURE-DRAFT.md`, `FACTCHECK-FABLE.md`.

---

## 1. The problem, in one paragraph

`Groups.tSdhAssumption D error := ∀ (adversary : tSdhAdversary D), tSdhExperiment … ≤ error`
places **no resource bound on the adversary type**. `tSdhAdversary` is a plain function into
`StateT unifSpec.QueryCache ProbComp`; `ProbComp` is a free monad, so pure computation is
free, and `Classical.choice` (via `Exists.choose` on ArkLib's own
`Algebra.lean:105 exists_zmod_power_of_generator`) inhabits an adversary that reads `g₂^τ`
out of the verifier SRS leg, recovers the trapdoor `τ`, and wins with probability `1`. Hence
`tSdhAssumption … error` is **false for every `error < 1`**, and `KZG.CommitmentScheme.binding`
— which takes it as a hypothesis — carries no information (premise false below `1`, conclusion
trivial at `≥ 1`). Mechanized, `sorry`-free, in `KzgVacuity.lean` (`not_tSdhAssumption`).

**Query-bounding is the wrong tool.** t-SDH is an *algebraic* assumption: the winning
adversary makes **zero** oracle queries — all its work is under `pure`. A query/ROM bound
(`IsQueryBoundP`, the right fix for hash/random-oracle floors) constrains something this
adversary never does, so it leaves the vacuity untouched. The honest menu is the algebraic
group model, or an extraction-shaped restatement. We take the latter.

---

## 2. The two options

**(A) AGM-restrict the adversary type.** In the Algebraic Group Model an adversary that
outputs a group element must also output its representation as a known linear combination of
its SRS inputs; `Classical.choice`'s extraction is then blocked because the choice-adversary
cannot *produce* the representation. This is the textbook way t-SDH is modeled. But ArkLib
has **no AGM scaffolding** (no `Algebraic`/`AGM`/`representation` anywhere in the tree).
Adopting (A) means: define an algebraic-adversary type carrying representations, rewrite
`tSdhGame`/`tSdhExperiment` to thread them, **and rework `bindingReduction`** so its output
element `g₁^(1/(τ+c))` comes with a representation over the SRS. That is new infrastructure
plus a reduction rewrite — genuinely invasive, not a one-liner.

And, subtly, **the naïve version of (A) does not even close the vacuity.** If the adversary
stays an arbitrary function that now *also* returns a representation, `Classical.choice` still
wins: it extracts `τ`, returns `h = g₁^(1/τ)`, **and** returns the genuinely valid
representation (coefficient `1/τ` on the `g₁` SRS basis element). A dependent pair (element,
representation-proof) is extra data the choice-adversary happily supplies, not a restriction.
A sound AGM repair therefore needs a real computational / generic-group boundary — the
representation must be *extracted by the reduction to solve a separate hard problem* (e.g.
q-DLOG), which is precisely the metatheoretic content ArkLib does not yet have. This makes (A)
strictly heavier than "add a field," and makes (B) the clearly correct minimal step.

**(B) Extraction-shaped restatement** (the pattern VCVio uses for its Merkle `Binding`, zero
sorries, no vacuity — the sound dodge worth stealing). State binding as the per-adversary
**reduction bound** it already proves: a binding adversary *yields, as data* — the explicit
`bindingReduction … adversary` — a t-SDH adversary whose success probability upper-bounds the
binding advantage. There is no `∀ efficient adversary` and no assumption `Prop`, so there is
**nothing for `Classical.choice` to inhabit**.

---

## 3. Why (B), and why it is nearly free

The decisive observation is structural: **ArkLib's reduction is already fully constructive.**
`binding`'s proof is a five-step calc; the first four steps are unconditional transition
lemmas, and `tSdhAssumption` is consumed in *exactly one place* — the last step
`t_sdh_error_bound`, which is literally `htSdh (bindingReduction … adversary)`, applying the
universally-quantified assumption to the *one* explicitly-built reduction adversary:

```
Pr[bindingCondition | game]
  = Pr[bindingCondExt | game_ext]                        -- binding_game_ext_eq_binding_game
  ≤ Pr[tSdhCondition ∘ mapBindingToTsdh | game_ext]      -- binding_cond_le_t_sdh_cond  (uses hg₁, hpair)
  = Pr[tSdhCondition | mapBindingToTsdh <$> game_ext]    -- map_binding_instance_drag
  = tSdhExperiment n (bindingReduction … adversary)      -- t_sdh_game_eq
  ≤ tSdhError                                            -- t_sdh_error_bound := htSdh (bindingReduction …)
```

So option (B) is: **split the calc at the last `≤`.** The unconditional prefix becomes a new
theorem; the original `binding` becomes its one-line corollary.

```lean
/-- Extraction-shaped evaluation binding: every binding adversary yields (as the explicit
    reduction `bindingReduction … adversary`) a t-SDH adversary upper-bounding its advantage. -/
theorem binding_reduces_to_tSdh {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (AuxState : Type)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Commitment.bindingExperiment (init := pure ∅) (impl := randomOracle)
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) AuxState adversary
    ≤ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) AuxState adversary) := by
  … -- the first four calc steps, verbatim, nothing new

/-- Original assumption-form binding, now a corollary. -/
theorem binding … (htSdh : Groups.tSdhAssumption … n tSdhError) :
    Commitment.binding … (kzg …) tSdhError := by
  simp only [Commitment.binding]; intro AuxState adversary
  exact (binding_reduces_to_tSdh (pairing := pairing) hg₁ hpair AuxState adversary).trans
    (t_sdh_error_bound … tSdhError htSdh adversary)
```

**The four transition lemmas are untouched.** `binding_reduces_to_tSdh`'s proof is the
existing calc prefix copied verbatim; `binding`'s proof shrinks to two lines. The full diff
is **+41 / −14** in one file (`binding-repair.patch`). The whole ArkLib tree still builds
(`lake build …KZG.Binding` → 2994 jobs, exit 0), and both theorems are axiom-clean:

```
KZG.CommitmentScheme.binding_reduces_to_tSdh   [propext, Classical.choice, Quot.sound]
KZG.CommitmentScheme.binding                   [propext, Classical.choice, Quot.sound]
```

---

## 4. Non-vacuity — the fix survives the *exact* attack (mechanized, `sorry`-free)

The original `binding` was vacuous because the attack (`tauExtractingAdversary` +
`not_tSdhAssumption`) made its premise false. The repair must survive that same attack, not
merely avoid mentioning it. `RepairSurvives.lean` proves it does. It re-proves the exact
refutation against the *repaired* tree, then states both facts as one theorem:

```lean
theorem repair_survives_attack
    (pairing …) (hg₁ : g₁ ≠ 1) (hpair : pairing (.ofMul g₁) (.ofMul g₂) ≠ 0) [SampleableType G₁]
    (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1)
    (AuxState : Type) (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    -- (1) the EXACT attack still refutes the assumption below error 1 …
    (¬ Groups.tSdhAssumption (g₁ := g₁) (g₂ := g₂) n tSdhError)
    -- … (2) yet the repaired reduction bound holds UNCONDITIONALLY.
    ∧ (Commitment.bindingExperiment … (kzg …) AuxState adversary
        ≤ Groups.tSdhExperiment n (bindingReduction … AuxState adversary)) := by
  refine ⟨not_tSdhAssumption (g₂_ne_one_of_pairing_ne_zero pairing hpair) n tSdhError herr,
          binding_reduces_to_tSdh (pairing := pairing) hg₁ hpair AuxState adversary⟩
```

Both conjuncts hold **at the same time, in the same groups, `sorry`-free**
(`[propext, Classical.choice, Quot.sound]`). Leg (1) is the identical trapdoor-extracting
adversary that killed the original — we did **not** weaken the assumption, so `not_tSdhAssumption`
still refutes it verbatim (`hpair` even *forces* the `g₂ ≠ 1` the attack needs). Leg (2) is the
repaired bound, and it takes no `tSdhAssumption` hypothesis, so leg (1) cannot empty it. That is
the precise sense in which the vacuity is closed: the disease was "the premise is unsatisfiable";
the cure removes the premise while keeping every ounce of the reduction's content.

The bound is genuine content, not a dressed-up `≤ 1`: its RHS is `tSdhExperiment` of a
*specific* constructed adversary, and the vacuity artifact's canary
(`tSdhExperiment_givingUpAdversary = 0`) shows the experiment discriminates, so the RHS is not
constantly `1`.

---

## 5. Invasiveness verdict

**(B) is a mergeable, small, local change** — split one calc, add one theorem, shrink
`binding` to a corollary; +41 / −14; four transition lemmas and the whole reduction untouched;
tree green; axiom-clean. This is a PR that *gives* the maintainers the sound statement rather
than asking them to redesign anything.

**(A) is the heavier, "more standard textbook" direction** and is worth flagging as future
work, but it is genuinely invasive (AGM adversary type + game/experiment rewrite + reduction
rework to emit representations) and should be the maintainers' call, not a drive-by patch. If
they prefer (A), (B) is still the right first step: it isolates the exact obligation (bound the
success of the *one* reduction adversary) that any restricted assumption — algebraic or
otherwise — must discharge.

**Recommendation for the PR.** Ship (B): keep `binding` (unchanged signature, now a corollary)
for backward compatibility, add `binding_reduces_to_tSdh` as the honest primary statement, and
note in the docstring that the assumption-form corollary is only informative once
`tSdhAssumption` is restricted to an algebraic adversary class. Offer (A) as a follow-up the
maintainers may prefer to own.
