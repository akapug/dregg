# CARRIER CENSUS — every assumed Prop/class in the metatheory, classified (2026-07-09)

> Companion to `METATHEORY-GROUND-TRUTH.md`. Prompted by ember's "naming IS faking": a `def C : Prop` or
> `class C` used as a hypothesis `[C]` is an ASSUMPTION `#assert_axioms` cannot see. This census sorts every
> such carrier into: **FLOOR** (legitimately irreducible) / **realized** (actually proved somewhere) /
> **PROVE?** (a real obligation, dischargeable) / **REFINE?** (unrealizable *as stated* — needs a data
> refinement to become provable). Method: mechanical grep pass + targeted reads; **every verdict has a grep
> line, but the buckets are heuristic — spot-verify before trusting a single row.**

## The headline: it is NOT "all fake." Three clusters, very different leverage.
Counts (carrier-shaped Props/classes that appear in ≥1 hypothesis position): **FLOOR 9 · realized ~37 ·
PROVE? ~38 · REFINE? ~17.**

### 1. FLOOR (9) — legitimate, keep them
`Poseidon2SpongeCR` (423 uses), `HashCR` (47), `SchnorrDLHard` (27), `Poseidon2WideCR` (8), `MSISHard` (6),
`DecisionMLWEHard` (3), `MLWESearchHard` (3), `SchnorrDLHardF` (3), `HintMLWEHard` (2). Assuming a concrete
hash is CR and a lattice/DL problem is hard IS the floor. **These are the honest TCB** (plus leanc/FFI for the
extracted native code, and — separately — seL4's cited kernel proofs).

### 2. HASH-INJECTIVITY — NOT a debt, a PLUMBING alias (~1200 uses, ~5 carriers)
`compressNInjective` (464), `logHashInjective` (363), `cellLeafInjective` (195), `compressInjective` (155),
`compress4Injective` (3). Their definitions are literally collision-resistance, e.g.
`compressNInjective h := ∀ xs ys, h xs = h ys → xs = ys`. **The reduction to the floor already exists** —
`Poseidon2Binding.compressNInjective_of_poseidon2CR`, `cellLeafInjective_of_realization`,
`HistoryAggregation.lean:92` states `compressNInjective compressN = Poseidon2SpongeCR compressN`. They show as
"PROVE?" only because callers assume the *alias* `[compressNInjective]` in 464 places instead of threading the
existing reduction. **Debt: mechanical — route everything through the single `Poseidon2SpongeCR` floor** so the
crypto residual of the whole commitment machinery is ONE assumption, not a scattered injectivity set. (Modulo
the finite-encodability caveat in cluster 4: injectivity-from-CR needs the hashed value to be finitely
serializable — which is exactly what the data refinement guarantees.)

### 3. realized (~37) — genuinely proved (spot-verified: trustworthy)
`ChipTableSound`/`ChipTableSoundN` (`FloorsNonVacuous.genuineChipTbl_sound … := by`, `arTf_sound`, `honTf_sound`
over real poseidon2 chips), `GuardDecodes` (12 realizations), `RangeTableSound`, `FriExtract`, the `*CR` app
carriers, `Poseidon2RealizedSponge`, `QROMInjective`, `HintTranscriptSimulatable` (proved via `hint_mlwe`), the
UC residuals, etc. Grounded; individual rows still merit a look but the bucket is real.

## THE TWO REAL DEBTS

### DEBT A — STARK/FRI verifier soundness (~5 carriers, ~50 uses)
`StarkSound` (38, `class`, 0 instances — the p3 batch-STARK "accept ⟹ ∃ satisfying trace"), `AlgoStarkSound`,
`FriLowDegreeSound`, `FriProximity` (3 — PARTIALLY discharged: `FriSoundness.friProximity_discharge` proves it,
but only instantiated over a `ZMod 5` toy; the folding lemma `fold_close_of_two_alpha` is field-generic and
REAL), `EngineSound` (32), `FriExtract`. **The grind:** model the Plonky3/FRI-over-**BabyBear** verifier
(AIR quotient check + FRI low-degree test + Poseidon2 Merkle openings), instantiate the field-generic FRI
soundness at BabyBear/rate/rounds, prove `accept ⟹ ∃ t, Satisfied2`, produce an actual `instance : StarkSound`.
Not a research open (BBHR18 + the p3 design); large, multi-session.

### DEBT B — DATA REFINEMENT of function-valued state (~15 carriers, ~250 uses)  ← highest leverage
`RestHashIffFrame` (199), `RestFrameDecodes2` + `…Dual/Triple/Quad/Quint` (~44), `DeployedFaithfulEff` /
`…Eff8` / `DeployedFaithful` / `FaithfulCapTree` (~33), `Satisfied2Faithful` (34), `LeafRealization` /
`LogRealization` (11). **Root cause (the tree admits it — `KeystoneAuditArgusReceipt.lean:34`: "the ONLY
carrier with no realization into ℤ is `RestHashIffFrame`"):** the kernel models `caps : CellId → List Auth`,
`delegations`, `heaps` as TOTAL FUNCTIONS over an infinite `CellId` domain. A commitment `RH : … → ℤ` cannot
injectively bind an infinite-domain function, so `RestHashIffFrame` (which asserts exactly that binding) is
**unsatisfiable**, and every whole-kernel binding downstream is vacuous-in-application.

**THE FIX (ember's data-refinement idea — the unlock):** remodel the function-valued kernel fields as **finite
maps** (`Finsupp` / sorted association lists over the finitely-many touched cells). Then:
- the state is finitely serializable ⇒ the hash-injectivity reductions (cluster 2) actually apply;
- `RestHashIffFrame` becomes a PROVABLE lemma (finite encode is injective under CR), not an assumption;
- `RestFrameDecodes2*` and the `DeployedFaithful*` faithfulness carriers follow.
Keep the deployed Rust impl efficient (it already uses finite maps — `caps` is a sparse map at runtime, not a
total function); connect the efficient impl to the finite-map proof model by a **refinement relation**
(`impl_refines_model`), so the proof gets a finitely-committable object and the impl pays nothing. This is the
classic proof-vs-performance data refinement, and it discharges the single largest carrier cluster in the tree.

### misc PROVE? (~25) — assorted per-effect obligations
`GuardDecodes2` (25) + `…Dual/Triple/Quint/Quad`, `SoundPolicy`, `VouchSound`, `EffectDecodeBridge`,
`ClosedWitness`, `SoundSubstitution`, `JointBinding`, `RedBinding`, `BridgeRowBinds`, `CellBridgeMintSpec`, …
Each is a real, individually-dischargeable soundness obligation (many are per-effect variants of the same
argument). Lower leverage than A/B; do them as the effects they gate get grounded.

## Recommended grind order
1. **DEBT B first (data refinement)** — highest leverage (~250 direct carrier-uses + it *enables* cluster 2's
   injectivity reductions to actually apply). Finite-map the state, prove `RestHashIffFrame`, thread the
   refinement relation to the impl.
2. **Cluster 2 plumbing** — once the state is finite, collapse the ~1200 injectivity hypotheses to the single
   `Poseidon2SpongeCR` floor.
3. **DEBT A (StarkSound)** — the p3/FRI verifier soundness, in parallel (independent of B).
4. **misc PROVE?** — per effect, as grounded.

## Honesty notes
- The buckets are a HEURISTIC (regex for "hypothesis position" vs "goal position"). Known false-"PROVE?":
  `FriProximity`, `HintTranscriptSimulatable` are discharged under hypotheses my grep didn't credit. Spot-verify
  any row before acting on it.
- "realized" ≠ "realized for the DEPLOYED object" — verify the realization isn't a toy (the `ZMod 5` lesson).
- This census counts CIRCUIT/soundness carriers. The crypto-floor reductions (DL/MSIS/MLWE) are separately
  audited in `METATHEORY-GROUND-TRUTH.md`.
