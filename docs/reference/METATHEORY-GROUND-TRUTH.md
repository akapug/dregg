# METATHEORY GROUND TRUTH — read this BEFORE modeling anything in Lean

> **STOP.** If you are about to model the effect-VM, the circuit/STARK, the kernel state, capabilities, or
> turn soundness in Lean — **they already exist.** This file says where. Modeling them fresh produces a
> *mirror*: a real theorem about a fake object, which then gets described as a theorem about the real system.
> That has happened (2026-07-09; see the HORIZONLOG **RETRACTION** entry and
> `memory/feedback-integrator-must-not-compress-scope`).

## The rule
Before writing `inductive Effect` / `def applyEff` / `def verifyCore` / any `KernelCap`, grep this tree first.
Then paste the **real signatures and absolute paths** into any subagent prompt. Prose invites reconstruction.

---

## Where the real models live

### The effect algebra + the real state
- **`Dregg2/Exec/RecordKernel.lean:309` — `structure RecordKernelState`** (the real state: `cell`, `bal`, …).
- **`Dregg2/Circuit/Argus/Stmt.lean:102` — `def interp : RecStmt → RecordKernelState → Option RecordKernelState`**
  — the real interpreter.
- **`Dregg2/Circuit/Argus/Effects/` — 45 files**, one per real effect: `CreateCell`, `Mint`, `Burn`,
  `NoteSpend`, `NoteCreate`, `Delegate`, `DelegateAtten`, `Attenuate`, `ExerciseViaCapability`, `CellSeal`,
  `CellUnseal`, `CellDestroy`, `MakeSovereign`, `BridgeMint`, `Introduce`, `EmitEvent`, `IncrementNonce`, …
- Per-effect soundness against the kernel, e.g. `Stmt.lean:174 interp_transferStmt_eq_recKExec`,
  `:258 interp_mintStmt_eq_recKMint`, `:272 interp_burnStmt_eq_recKBurn`,
  `Effects/MakeSovereign.lean:193 interp_makeSovereignStmt_eq_kernel`.
- The deployed Rust `Effect` enum has **33 variants** (`turn/src/action.rs`), applied by
  `apply_effect_to_cell` (`turn/src/rotation_witness.rs:1126`). Any Lean `Effect` with six constructors over a
  scalar is **not** it.

### The circuit / turn-soundness apex
- **`Dregg2/Circuit/CircuitSoundness.lean:633` — `turnDecodeChain_refines_turnSpec`**
  `(hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry) (c : TurnDecodeChain hash S start fin)`
  `(href : StepsRefine hash S R c) : ∃ acts : List FullActionA, turnSpec start acts fin`
  — the decoded turn chain **refines the turn spec**. Also `:696 turnDecodeChain_refines_turnSpec_gen`.
- Closure: `Dregg2/Circuit/CircuitSoundnessAssembled.lean:677 hrefinesAll`,
  `Dregg2/Circuit/ClosureAll.lean:1596 hrefinesAllClosed`, `Dregg2/Circuit/ClosureForest.lean:101`.
- Effects↔circuit: 20 files under `Dregg2/Circuit/Argus/` reference `Surface2` (e.g. `createCellCircuit`).

### THE THREE OPEN CARRIERS (this is the actual remaining work)
`CircuitSoundness.lean`'s header names exactly what the apex leaves open:
1. **`[StarkSound]`** — soundness of the deployed STARK verifier. *This* is the real "CircuitSound".
   Discharging it = AIR soundness at the real `Surface2` constraint set **plus** FRI soundness at the
   **deployed field, rate, and round count** — not a toy field.
2. **`[Poseidon2SpongeCR hash]`** — Poseidon2-sponge collision resistance (`Dregg2/Circuit/Poseidon2Binding.lean`).
   De-laundering this to a standard CR assumption is real, tractable work.
3. Per-effect carried facts: `cellLeafInjective CH`, `RestHashIffFrame RH`.
- Also `Dregg2/Circuit.lean` carries a `-- PRIMITIVE:` digest-binding obligation (now reduced to `HashCR`).

### The crypto floor (the good part of the 07-09 work)
- `Dregg2/Crypto/HybridCombiner.lean` — `SigScheme`, `EufCma`, and the **projection** argument (a hybrid
  forgery projects to component forgeries). This one *is* about the real construction.
- `Dregg2/Crypto/IdentityCommitment.lean` — `verify_committed_ml_dsa` binding → `HashCR`. Corresponds to the
  deployed `dregg-types` function of the same name.
- `Dregg2/Crypto/HermineSelfTargetMSIS.lean`, `SchnorrEufCma.lean` — the DL/MSIS extractions.
- `Dregg2/Crypto/OneWayToHiding.lean`, `DoubleSidedO2H.lean` — a q-query QROM adversary built from
  `EuclideanSpace ℂ`; `norm_sq_sum_orthogonal` (orthogonal errors combine in quadrature) is real.
- `Dregg2/Circuit/FriSoundness.lean` — `fold_close_of_two_alpha`, the BBHR18 two-challenge reconstruction.
  Real lemma; **instantiated only on a toy field so far**.

### Capabilities
- `Dregg2/Crypto/CapabilityChain.lean` — the cryptographic attenuation chain (real).
- `Dregg2/Firmament/SeL4Kernel.lean` — a Lean seL4 model. **Caution:** its `Slot.rights : AuthReq` is *defined*
  to be the protocol's own authority type, so any "the two lattices coincide" claim is definitional until the
  kernel model is given an independent rights type and a mapping is *proved*.

---

## Known-bogus artifacts (deleted 2026-07-09, listed so they are not resurrected)
`Crypto/EffectVmSemantics.lean` (an additive counter over `ZMod 5` called "the deployed effect-VM"),
`Circuit/CircuitSoundCompose.lean` (`circuit_sound` instantiated at `ZMod 5`, `|L|=4`, error `1/5`),
`Crypto/CapWeld.lean` (`capMap c := c.rights`, definitional), `Crypto/ParameterSecurity.lean` +
`Crypto/LatticeEstimate.lean` (λ = `by decide` on ℕ, **no `∀ adversary`**, unsourced constants — `192` is the
NIST Category-3 *label*, not quantum core-SVP).

Also: `Crypto/Fips204Verify.lean`'s `verifyCore : ℤ → ℤ → (ℤ×ℤ×ℤ) → Bool` is **not** ML-DSA (no `R_q`, no NTT,
no SHAKE, no packing), and `dregg-pq::ml_dsa_verify` still calls the `fips204` crate — the extracted core is an
opt-in shadow nothing invokes. Same for `Fips203Kem`. Do not cite these as "the primitive is verified".

## Checklist before claiming a theorem is about the deployed system
1. Read the **type** of every object in the statement. A type signature refutes a headline faster than an audit.
2. For a security bound: **where is the `∀ adversary`?** `:= by decide` on a ℕ is arithmetic, not security.
3. For "X *is* Y": was `X` **defined** to be `Y`?
4. Any "engineering, not open" caveat (NTT, hash, field size) is **load-bearing** until proven otherwise.
5. A result that would be publishable if true gets audited **before** it is celebrated.
