# Polis theorem stack

The "fair playground for superintelligences" constitution, as a kernel-clean Lean artifact:
the dregg ⋈ svenvs ⋈ Lacan synthesis made theorem-bearing against the real dregg substrate.
Verified where verified, red where red — no charisma filling the gap.

## Reproduce

```
cd metatheory
lake build Metatheory.Polis Metatheory.DreggPolis Metatheory.PolisNonConfusion
```

(Mathlib is cached at `~/src/mathlib4`; ~3174 jobs; exit 0.) CI-covered by the
`Metatheory.+` glob in `lakefile.toml`.

## Axiom budget

Every keystone is `#assert_axioms` / `#print axioms` within:

```
{propext, Classical.choice, Quot.sound}
```

Several depend on **no axioms at all** (`envelope_least_restrictive`,
`structural_requires_proof`, `disjoint_floors_no_polis`, `dregg_shared_floor_inhabited`).
Zero `sorry`, zero `:= True` load-bearing.

## Proven (`Metatheory.Polis` · `Metatheory.DreggPolis` · `Metatheory.PolisNonConfusion`)

| Property | Theorem |
|---|---|
| **Verify the cage, not the animal** — enforcement cannot psychometrically classify the inhabitant (∀ ctrl) | `polis_safety` |
| Least-restrictive envelope — every bar load-bearing | `envelope_least_restrictive`, `override_only_unsafe`, `maxpol_envelope_safe` |
| **Structural means theorem-bearing** — no clause is `structural` without a proof | `structural_requires_proof` |
| **Legitimacy as non-regression** — self-amending, but no declared minimum may be legally weakened | `amendment_stream_nonregression`, `regressive_amendment_inert` |
| **Empty meet is schism** — the polis edge is the empty intersection of *exported* floors | `disjoint_floors_no_polis` |
| Candidate model non-vacuous (kills "beautiful but empty") | `dregg_shared_floor_inhabited` |
| Disclosure law = a real deployed theorem ("proves the same while reveals less") | `minimalBoundary_carries_real_theorem` (← `EpistemicDial.accepts_invariant_under_dial`) |
| Authority floor on the deployed l4v `Auth` enum | `dreggReal_polis_safety` |
| Authority = the real `Auth`-camera substance discipline | pins of `production_step_fpu`, `unauthorized_amplification_not_production` |
| Non-confusion family (shadow ≠ resource), deployed | pins of `transclusion_no_amplify`, `execFullForestG_no_amplify`, `noteSpendFresh_rejects_double`† |
| Foundational anti-Mythos floor (no forged history) | pin of `unfoolability_guarantee` |
| **certificate ↛ capability** (dereliction guard) | pins of `transclusion_grants_no_unheld_authority`, `transclusion_is_observed_finalized_read` |
| **observation ↛ resolution** (one resolver, many observers) | pins of `Await.{one_shot_is_static, commit_resumes_once, rollback_discards_continuation, runtime_guard_is_double_spend, four_faces_unify}` |
| executor-coupled `gateOK` authority floor | pin of `Exec.AuthModes.captp_granted_le_held` (+ camera `Fpu`) |
| real KERI human floor (cannot lose identity) | pins of `PreRotation.rotChain_pinned_by_commitments`, `ResharingChain.{reshare_forward_jump, secret_value_survives}` |
| **Politician — exit foreclosure** | `CaptureBar`, `rExitForeclosureBar`, `dreggReal_envelope_no_foreclosure` |
| **Politician — flow/policy capture** (decidable Büchi game) | `flowCaptureBar` over `≤ᶠ`, sound+complete by `FlowRefine.decideRefines_iff` (`PolisFlowRefine`) |
| **Politician — disclosure ratchet** | `DiscloseAt.{accepts_invariant_under_dial, accepts_preserved_down, leak_mono}` |
| **Politician — grade laundering** | `Finality.{no_downgrade, Tier.rank_injective, conservation_tier_independent}`, `World.world_no_downgrade` |
| **Politician — clerk monopoly** | `FullForestAuthPortal.{proof_arm_sound, custom_arm_sound, unchecked_arm_rejects}` (validity depends on the proof, not the prover) |
| **Politician — hole rent** | `ConditionalTurn.condTurn_atomic` + `Await` one-shot (`PolisPolitician`) |

† `noteSpendFresh_rejects_double` lives in the `PolisNonConfusionCircuit` sidecar (pulls the
circuit-emit tree); builds when that tree is green.

## Not proven / frontier (named, not faked)

Both censuses (`wihlga2r4`, `w9p6ffrrn`) found the local non-confusion / floor legs AND the
politician capture-shape catalog already DEPLOYED and pinnable — all now closed (above), and the
flow/policy capture is governed by the deployed sound+complete Büchi decision procedure. What
genuinely remains is **one** deep object, the next research phase, not a cleanup task:

- **the interleaved-multi-agent hyperproperty** — composing the per-shape bars into a *single*
  floor over one multi-agent trace lattice (the politician who interleaves several lawful
  strategies across subjects). Each shape is pinned/decidable in isolation; unifying them needs
  a `Trace DreggState DreggAction` lattice and the hyperproperty (set-of-traces) semantics over
  it. The single-trajectory bars (`rExitForeclosureBar`, `flowCaptureBar`) are the landed seeds.
  (The deeper executor-camera refinement of the `held ⊆ bound` floor is a tightening, not a hole:
  the shadow *is* the real `fits` by `USet.fits_iff`, and the camera `Fpu` is pinned.)

## The grounding insight (`~/dev/svenvs`)

svenvs resolves the protected-remainder paradox **for enforcement, not epistemology**: the
inhabitant is the `∀`-quantified term the proof never reasons about, so the shadow is
real-but-**inert** (no place in the enforcement function to put it). The same `∀`-blindness
that protects the remainder makes the politician ungovernable-by-interior → **govern
trace-shape, not motive**. `disjoint_homes_make_floor_empty` is legitimacy as a kernel fact:
the polis exists only where *exported* floors (never interiors/souls) have a non-empty meet.

> Not a proof of justice — a checked floor against forgery, psychometric enforcement,
> amendment capture, exit foreclosure, and empty-meet coercion, with the remaining political
> frontier named instead of faked.
