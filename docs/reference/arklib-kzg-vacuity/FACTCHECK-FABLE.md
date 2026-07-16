# Independent factcheck (Fable lane) — ArkLib `KZG.binding` vacuity claim

**Checker:** Fable 5, independent second factchecker. Instructed to REFUTE; did not read the
sibling Opus lane's analysis. All checks re-derived from source and re-run from scratch.

**Verdict: CONFIRMED.**

The claim survives every attack I ran. Point-by-point, most dangerous first:

## (a) Real upstream ArkLib, or a restatement? — REAL UPSTREAM. Verified by my own build.

- Checkout: `/private/tmp/arklib-review` (also `/private/tmp/arklib-hostile`), remote
  `https://github.com/Verified-zkEVM/ArkLib.git`, HEAD = `d72f8392ff03047dc5386f4f4bb513743e7ada65`
  ("Fix/blueprint latex (#649)") — exactly the pinned commit in the writeup. Toolchain
  `leanprover/lean4:v4.31.0`, matching.
- `KzgVacuity.lean` has exactly one import: `import ArkLib.Commitments.Functional.KZG.Binding`
  (line 5). It re-`def`s **nothing** from ArkLib. Every upstream symbol it consumes exists at the
  pinned commit with the exact signature the writeup quotes — I read each one:
  - `Groups.tSdhAdversary` / `tSdhCondition` / `tSdhGame` / `tSdhExperiment` / `tSdhAssumption` —
    `ArkLib/Commitments/Functional/KZG/HardnessAssumptions.lean:53/58/70/82/88`, verbatim match.
  - `Groups.exists_zmod_power_of_generator` — `Algebra.lean:105`, verbatim match.
  - `Groups.orderOf_eq_prime_of_ne_one` (:61), `zmod_eq_zero_of_gpow_eq_one` (:70),
    `gpow_div_eq` (:93), `PowerSrs.tower` (:40), `PowerSrs.generate` (:45) — all present; in
    particular `generate n τ = (tower g₁ τ n, tower g₂ τ 1)`, so `srs.2[1] = g₂ ^ (τ.val)` — the
    adversary's extraction site is exactly what upstream puts there, at every degree `D`.
  - `Groups.sampleNonzeroZMod` — `Sampling.lean:33`; support is `{1, …, p−1}` by construction
    (`Fin (p−1)` shifted by one), so the `τ ≠ 0` step is sound.
  - `KZG.CommitmentScheme.binding` — `Binding.lean:743`, verbatim match including
    `hg₁ : g₁ ≠ 1`, `hpair : pairing g₁ g₂ ≠ 0`, and
    `htSdh : Groups.tSdhAssumption … n tSdhError`.
- **Build result (mine, from scratch on the warm cache):**
  `lake build ArkLib.Commitments.Functional.KZG.Binding` → `Build completed successfully
  (2994 jobs)`, exit 0. Then the artifact **verbatim** (byte-copied from
  `docs/reference/arklib-kzg-vacuity/KzgVacuity.lean`, with only `#print axioms` lines appended)
  via `lake env lean` → **exit 0, no errors, no sorry**; only `unusedSectionVars` linter warnings.
- Axiom prints (my run):
  ```
  'ArkLibVacuity.not_tSdhAssumption'               [propext, Classical.choice, Quot.sound]
  'ArkLibVacuity.tSdhExperiment_tauExtractingAdversary' [propext, Classical.choice, Quot.sound]
  'ArkLibVacuity.binding_hypotheses_unsatisfiable' [propext, Classical.choice, Quot.sound]
  'ArkLibVacuity.experiment_discriminates'         [propext, Classical.choice, Quot.sound]
  'ArkLibVacuity.g₂_ne_one_of_pairing_ne_zero'     [propext, Classical.choice, Quot.sound]
  'KZG.CommitmentScheme.binding'                   [propext, Classical.choice, Quot.sound]
  ```
  No `sorryAx` anywhere in the closure — the target theorem itself is genuinely green, and so is
  the refutation. (ArkLib's build does emit `sorry` warnings, but all in unrelated modules:
  `Data/Fin/{Basic,Sigma}`, `ToMathlib/…/RenyiDivergence`, `OracleReduction/{Basic,Execution,
  Security/Basic,OracleInterface}`, plus VCVio's `GPVHashAndSign`/`FujisakiOkamoto`/
  `FiatShamir.WithAbort` — none under `binding` or the refutation, confirming the writeup.)

## (b) `g₂ ≠ 1` — FORCED by `binding`'s own `hpair`, not assumed.

`pairing` is a section variable of `Binding.lean` (line 44):
`(pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))` — a genuine
`ZMod p`-bilinear map. So `pairing g₁ (Additive.ofMul 1) = pairing g₁ 0 = 0` by `map_zero`, and
`hpair : pairing g₁ g₂ ≠ 0` forces `g₂ ≠ 1`. The artifact's `g₂_ne_one_of_pairing_ne_zero`
proves exactly this and compiles against real ArkLib (axiom print above). The refutation carries
`hg₂` as an explicit hypothesis in `not_tSdhAssumption`, but `binding_hypotheses_unsatisfiable`
discharges it from `hpair` — so for the "binding is vacuous" conclusion, nothing is assumed
beyond `binding`'s own hypotheses. Joint-unsatisfiability at `error < 1`: confirmed.

## (c) Is `tSdhAssumption` genuinely what `binding` assumes? — YES, and it is the only one.

`Binding.lean:745` consumes `Groups.tSdhAssumption` directly. I grepped the whole tree: the only
`tSdh*` definitions are in `HardnessAssumptions.lean`; the only other assumption there is
`arsdhAssumption` (:125, same unrestricted shape; unmechanized by the artifact, and the writeup
says so). There is **no** query-bounded, cost-bounded, or AGM variant of t-SDH anywhere in
ArkLib. `IsQueryBound` appears in ArkLib exactly once — commented out, in the unrelated
`OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemma.lean:111` — precisely as the writeup
states. The adversary type (`HardnessAssumptions.lean:53`) is a plain function into
`StateT unifSpec.QueryCache ProbComp`; `pure` is a legal, zero-query inhabitant; the `∀` in
`tSdhAssumption` (:88) has no side condition. Confirmed.

## (d) Is `binding` WIP-labelled? — NO.

No `sorry`/`WIP`/`TODO`/`placeholder`/`experimental`/`scaffold` marker anywhere in `Binding.lean`
or `HardnessAssumptions.lean`. The module docstring says "This file **proves** evaluation binding
for the KZG commitment scheme by reducing … to the `t`-SDH experiment", with authorship and
references (KZG10 extended version). It is presented as a finished result. This is a real finding,
not a shot at scaffolding.

## (e) Weakest link (since not refuted)

The argument itself has no soft spot I could find; the caveats are presentational:

1. **The `error ≥ 1` branch is argued, not mechanized, in the shipped artifact.** "No content at
   any parameter" = (hypotheses unsatisfiable for `error < 1`) + (conclusion free for
   `error ≥ 1`). The second leg is elementary — I read `Commitment.binding`
   (`Functional/Basic.lean:167`): it is `∀ AuxState adversary, Pr[…] ≤ bindingError`, and a
   `probEvent` is always `≤ 1`, so `probEvent_le_one.trans` closes it in one line — but
   `KzgVacuity.lean` does not contain that lemma. Worth adding for completeness before any
   disclosure; it is a one-liner, and its absence does not weaken the mechanized core
   (`tSdhAssumption` false below 1 is the entire finding).
2. **The claim text's "pairing is `ZMod p`-bilinear ⇒ `pairing g₁ 1 = 0`"** mixes multiplicative
   and additive notation (the `0` lives in `Additive Gₜ`, i.e. `1` in `Gₜ`; the `1` fed to the
   pairing is `0` in `Additive G₂`). The Lean artifact states it correctly via `Additive.ofMul`;
   the prose is fine for a cryptographer but a pedant could quibble. Cosmetic.
3. The `hg₁`-redundancy aside and the `arsdhAssumption`-likely-refutable aside are unmechanized;
   both are explicitly flagged as such in the writeup. Honest as stated.

## Bottom line

The one load-bearing error pattern this chain kept producing (checking a restatement instead of
the target) is **not** present here: the artifact imports the genuine
`ArkLib.Commitments.Functional.KZG.Binding` at the pinned upstream commit, redefines nothing,
builds green under my own hands, and its axiom closure is clean including upstream `binding`
itself. `tSdhAssumption` quantifies over an adversary type with no query bound; ArkLib's own
`exists_zmod_power_of_generator` makes `Exists.choose` a trapdoor; the SRS's verifier leg carries
`g₂^τ` at every degree; `hpair` forces `g₂ ≠ 1`; the exhibited adversary wins with probability 1;
the canary shows the experiment discriminates. **CONFIRMED** — a formalization gap in ArkLib's
t-SDH statement, exactly as claimed: the quantifier is broken, not the cryptography, and not the
reduction in `Binding.lean`. Nothing filed; disclosure remains ember's call.
