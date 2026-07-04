# RESEARCH — the registry-driven proof-carrying handler executor

> Scope: read-only scoping report. Verifies the ACTUAL source state (not docs/memory/harvest).
> The campaign as framed — "replace the closed inductive executor with proof-carrying handlers
> carrying `conserves`/`auth_gated`/`admission_gated` as proof fields, so a missing gate is
> unrepresentable" — is **LARGELY ALREADY BUILT**. This report maps what IS vs ISN'T there, names
> the precise remaining gap, and gives a phased plan to close it.

---

## 1. WHAT EXISTS IN SOURCE NOW (verified, file:line)

The proof-carrying handler executor is **not an idea — it is a landed, axiom-clean subsystem**.
All of the following are committed at HEAD (none in the working-tree modified set).

### 1a. The `EffectHandler` record — DATA + 3 PROOF FIELDS (the core of the design)

`Dregg2/Exec/Handler.lean:70-87`:

```
structure EffectHandler (Args : Type) where
  step       : RecordKernelState → Args → Option RecordKernelState
  delta      : Args → AssetId → Int
  auth       : RecordKernelState → Args → Bool
  admission  : RecordKernelState → Args → Bool
  trace      : Args → Turn
  auth_gated      : ∀ s a s', step s a = some s' → auth s a = true
  admission_gated : ∀ s a s', step s a = some s' → admission s a = true
  conserves       : ∀ s a s', step s a = some s' →
                       ∀ b, recTotalAsset s' b = recTotalAsset s b + delta a b
```

The three obligation fields **are proofs** — a handler literal is ill-typed until they are
discharged against `step`. This is exactly the campaign's keystone: soundness is a typing condition
on registration, not a separate audit.

### 1b. The registry coproduct + lookup dispatch

- `PackedHandler` (`Handler.lean:98-102`) — existentially packs `Σ Args, EffectHandler Args`.
- `abbrev Registry := List PackedHandler` (`Handler.lean:105`).
- `ClosedEffect` (`Handler.lean:111-119`), `execEffect = lookup + step` (`Handler.lean:124`),
  `execTurn = es.foldlM ...` (`Handler.lean:133`).

### 1c. THE PROOF-MATRIX KILLER — proven, generic, axiom-clean

`Handler.lean:172` `turn_conserves`: for ANY `List ClosedEffect`, the combined per-asset measure
moves by the SUM of the per-effect deltas — ONE `List.foldlM` induction consuming each handler's
`conserves` field, NO per-arm matrix. Companions `turn_head_authorized` (`:202`),
`turn_head_admitted` (`:212`). All `#assert_axioms`-pinned to the kernel triple (`:391-397`).

### 1d. The FULL handler registry — every domain handler, obligations discharged

`Dregg2/Exec/Handlers/*.lean` (2254 lines), each handler an `EffectHandler` whose three obligations
are discharged by composing the proved `RecordKernel` palette lemmas:

| File | Handlers (proof-carrying) |
|---|---|
| `StateSupply.lean` (665) | `mintH`, `burnH`, `bridgeMintH`, `createCellH`, `spawnH`, `createCellFromFactoryH`, `stateWriteH`, `heapWriteH`, `makeSovereignH` |
| `Authority.lean` (497) | `delegateH`, `introduceH`, `delegateAttenH`, `attenuateH`, `revokeH`, `revokeDelegationH` |
| `Lifecycle.lean` (345) | `cellSealH`, `cellUnsealH`, `cellDestroyH`, `refreshDelegationH`, `emitEventH`, `cellArchiveH` |
| `Escrow.lean` (168) | `noteSpendA`, `noteCreateA` (F1b: escrow handlers dissolved into factories) |
| `Bridge.lean` (115) | `pipelinedSendA` |
| `Exercise.lean` (464) | `exerciseH` (the recursive sub-effect forest + R4 facet mask) |

The slice-3 originals (`transferH`, `stateH`) live in `Handler.lean:249,311`.

### 1e. THE ASSEMBLED EXECUTOR — `Dregg2/Exec/HandlerExecutor.lean` (1236 lines)

- `masterRegistry` (`:95`) — the coproduct of all proved handlers (23 entries; `masterRegistry_length`
  `:124`).
- `toClosedEffect : FullActionA → ClosedEffect` (`:146`) — TOTAL, all 56 `FullActionA` constructors
  mapped, aliases collapsed (introduce↔delegateAtten, bridgeMint↔mint, spawn↔createCell, …).
- `execHandlerTurn` (`:208`) — the registry executor over the chained state.
- **Derived global laws (lifted, not re-proved):** `execHandlerTurn_conserves` (`:243`),
  `_head_authorized` (`:257`), `_head_admitted` (`:273`).
- **THE STRENGTHENING — `handler_refines_execFullA_*`:** proved for ~30 constructors (transfer, mint,
  burn, bridgeMint, revoke, createCell, spawn, createCellFromFactory, noteSpend/Create, pipelinedSend,
  revokeDelegation, stateWrite/incrementNonce/setPermissions/setVK/setProgram/refusal/setField,
  makeSovereign, receiptArchive, cellSeal/Unseal/Destroy, refreshDelegation, emitEvent, delegate/
  delegateAtten/introduce/attenuate, exercise). Each: "every commit the handler executor makes,
  `execFullA` ALSO makes, and they AGREE on the kernel." `:1160-1193` pin all to the kernel triple.
- **THE TEETH (`#guard`-verified):** `:1123-1148` — concrete attacks rejected; conservation evaluated.

### 1f. The verb registry (the campaign's "registry" sibling)

`Dregg2/Substrate/VerbRegistry.lean` reifies the 8-verb / 27-live-`EffectTag` census with a total
`classify` cover (compiler-checked exhaustive), `minimality`, and factory-provenance. This is the
**signature-level** registry (what the verbs ARE); the `HandlerExecutor` `masterRegistry` is the
**executable** registry (what each handler DOES). They are reconciled by name, not yet by a proof.

### 1g. `Dregg2/HandlerTransformer.lean`

A SEPARATE, more abstract frontier (safe-step preorder / camera `Fpu` / sheaf-of-verifiers gluing).
Relevant only as the future "handler-transformer" algebra; not part of the executor cutover. Carries
named OPENs (the `Fpu`=gluing weld, higher-order tier).

### 1h. THE LIVE PRODUCTION PATH — and the three-executor reality (CRITICAL)

There are **three** executors, and the handler one is NOT yet the live one:

1. `execFullA` (`TurnExecutorFull.lean`) — the flat-list 56-arm `match`. **The handler executor
   refines THIS.**
2. `execFullForestA` / `execFullForestG` (`Dregg2/Exec/FullForest.lean`) — the TREE-shaped, per-node
   credential+caveat-gated executor. **This is the live production path**: the sole `@[export]`
   `dregg_exec_full_forest_auth` (`FFI.lean:971`) runs `execFullForestG` under the `Admission`
   prologue (`TurnAdmission.runGatedForestTurn`).
3. `execHandlerTurn` (`HandlerExecutor.lean`) — the registry handler executor. Wired into
   `TurnAdmission.runHandlerTurn` (`TurnAdmission.lean:44`) as the "soundness-strengthening path",
   but **NOT exported** and **NOT the production entry**.

So the cutover is *staged-additive and de-risked* (the algebra + global laws + refinement-to-`execFullA`
are proved), but **the live switch has not happened**, and crucially the live executor is the
**forest** one, not the flat `execFullA` the handler executor currently refines. (`execFullForestA`
nodes each run their own `execFullA` — `FullForest.lean:84,193 — so a handler⊑execFullA result lifts
node-wise, but that lift is not yet proved.)

**Verdict on (1):** the campaign is ~80% built. The Handler record, the registry coproduct, the
matrix-killing `turn_conserves`, the full per-domain handler suite with discharged obligations, the
total dispatch, and the refinement-to-`execFullA` for ~30 constructors all EXIST and are axiom-clean.
What is missing is (a) the floor-predicate completeness of the obligation fields, (b) the cutover to
the live (forest) path.

---

## 2. THE GATE-HOLE CLASS this closes — and the precise remaining gap

The campaign's thesis: the pre-codex review kept finding silent-gate holes one at a time
(setField-resets-nonce, membership-vs-liveness, emitEvent-not-live, attenuate-no-op-on-bad-index).
Make the missing gate UNREPRESENTABLE.

### 2a. Per-arm preconditions an effect can forget (the hole locations)

| Floor | Where checked today | A handler obligation field? |
|---|---|---|
| **authority** (cap confers the edge) | `auth` gate + `auth_gated` | ✅ YES (`auth_gated`) |
| **availability / liveness** (cell is Live, not Sealed/Destroyed) | `admission` gate + `admission_gated` | ✅ YES (`admission_gated`) |
| **conservation** (Σδ per-asset) | `conserves` field | ✅ YES (`conserves`) |
| **reserved-field** (only the dedicated effect writes nonce/perms/vk/program) | `reservedField` inside `stateStepDev` (`EffectsState.lean:313,321`), NOT in `stateWriteStep` | ❌ NO — carried as side-hyp `hnr` in `handler_refines_execFullA_setField` (`HandlerExecutor.lean:799`) |
| **caveat-admission** (predicate caveats discharged) | `caveatsAdmit` inside `stateStepGuarded` (`EffectsState.lean:248`) | ❌ NO — side-hyp `hcav` (`HandlerExecutor.lean:800`) |
| **freshness** (delegationEpochAt re-stamped; no stale snapshot) | inside `execFullA` refresh/spawn arms | ❌ NO — `refreshDelegation` refinement holds only MODULO the epoch re-stamp residual (`HandlerExecutor.lean:897-927`) |
| **non-amplification** (granted ≤ held on a delegation edge) | `execFullForestA_no_amplify` (forest-level), per-edge | ❌ NO — a forest-executor theorem, not a handler field |
| **index-bounds** (attenuate slot in range) | `attenuateStep` fail-closed | ⚠ PARTIAL — handler is fail-closed, but refinement carries `hb : idx < length` side-hyp (`HandlerExecutor.lean:1025`) |
| **monotone-nonce** (strictly advancing) | `incrementNonceStep` monotone gate | ❌ NO — side-hyp `hmono` (`HandlerExecutor.lean:571`) |
| **membership** (cell ∈ accounts) | bare step | ❌ NO — side-hyp `hmem`, pervasive |

### 2b. The honest diagnosis

The `EffectHandler` record captures **exactly three** floors (authority / availability / conservation)
as typed obligations. The **other six** floors the campaign names — reserved-field, caveat,
freshness, non-amplification, index-bounds, monotone-nonce (plus membership) — are **NOT** handler
proof fields. They are enforced ad-hoc inside individual `step` functions, and where the handler's
`step` is *weaker* than `execFullA`'s arm (e.g. `stateWriteStep` skips the reserved/caveat gate that
`stateStepDev` has), the refinement theorem **carries the missing gate as a side-hypothesis**
(`hnr`, `hcav`, `hmono`, `hmem`, `hb`, the epoch-residual).

**This is the residual hole-class.** A side-hypothesis on a refinement theorem is the exact shape of
a "silent gate" the campaign wants to make unrepresentable: the handler CAN be constructed without
the gate (it type-checks), and the gate only re-appears as a hypothesis the *caller* must supply.
The class is not closed by construction until each of these floors is *either* (i) a proof field on
`EffectHandler`, *or* (ii) provably implied by `step`-commits with no side-hypothesis.

---

## 3. THE DESIGN (to finish closing the class)

The structure already exists (`§1a`). The completion is to **widen the obligation surface** so every
floor a handler can forget becomes a typed field, and to make the executor the live one.

### 3a. Widen `EffectHandler` with the missing floor obligations

Add proof fields (each ill-typed until discharged), e.g.:

```
  -- the "guard" floor: every commit had its predicate caveats + reserved-domain discharged
  guard         : RecordKernelState → Args → Bool
  guard_gated   : ∀ s a s', step s a = some s' → guard s a = true
  -- the freshness floor: every commit left no stale delegation snapshot (or re-stamped it)
  fresh_gated   : ∀ s a s', step s a = some s' → freshAfter s' a
  -- the non-amplification floor (for the edge-bearing handlers)
  nonamp_gated  : ∀ s a s', step s a = some s' → grantedLeHeld s a
```

The uniformity question (a real risk — see §5): not every floor is a single Bool. `conserves` is
already a relation, `freshness` and `non-amp` are relations over the post-state and over delegation
edges respectively. The cleanest design generalizes the obligation surface to a **list of
`FloorObligation` records** (a predicate + a `*_gated` proof), or a `FloorSpec` typeclass the handler
must satisfy — so adding a floor is adding one obligation entry, mirroring how adding an effect is
adding one registry entry. The campaign's "floor-obligation typeclass" framing (P0 below) is the
right shape.

### 3b. Make the side-hypotheses unrepresentable

For each floor currently carried as a refinement side-hyp, EITHER:

- **strengthen the handler's `step`** so it fail-closes on that floor (then the side-hyp is
  discharged from the commit, e.g. give `stateWriteStep` the `reservedField`/`caveatsAdmit` gate so
  `handler_refines_execFullA_setField` drops `hnr`/`hcav`); OR
- **add the obligation field** so the floor is a typing condition and the executor's global companion
  theorem (à la `turn_head_admitted`) witnesses it for every committing turn.

The goal state: `handler_refines_execFullA_*` has NO side-hypotheses beyond the commit itself, i.e.
the handler executor is an unconditional sound strengthening, and the missing-gate is a type error.

### 3c. The cutover target is the FOREST executor, not flat `execFullA`

Because production runs `execFullForestG`, the cutover needs a `execHandlerForest` (the handler
registry over the tree shape) OR a proof `execFullForestA`-node ⊑ handler so the existing flat
refinement lifts node-wise. `execFullForestA` already runs each node via `execFullA`
(`FullForest.lean:193`), and the forest carries `_no_amplify` / `_conserves_per_asset` at the
forest level — so the lift is plausible but unproved. This is the largest single piece of remaining
work and was NOT visible in the campaign framing (which assumed the flat `execFullA` was the live
target).

---

## 4. PHASED BUILD PLAN

**P0 — the floor-obligation surface (the typeclass/record).** Generalize the three ad-hoc obligation
fields into a uniform `FloorObligation`/`FloorSpec` so floors are extensible by ONE entry. Re-express
`auth_gated`/`admission_gated`/`conserves` through it (additive; the existing handlers keep
type-checking). **First concrete step (do this first):** in a NEW file `Dregg2/Exec/HandlerFloors.lean`,
define `structure FloorObligation (Args)` = `{ gate : RKState → Args → Bool, gated : ∀ s a s', step
s a = some s' → gate s a = true }` parameterized by a handler's `step`, and prove the two existing
gates (`auth`, `admission`) are instances — WITHOUT editing `Handler.lean` (so nothing downstream
breaks). This de-risks the surface before touching the 23 live handlers.

**P1 — close the reserved-field + caveat floor (the highest-leverage single hole).** Give
`stateWriteStep` the `reservedField`/`caveatsAdmit` gate (or add `guard`/`guard_gated` to the
field-write handlers), then DROP the `hnr`/`hcav` side-hypotheses from
`handler_refines_execFullA_setField`. This is the exact hole the just-banked commit `c4f4f0012`
("reserve protocol fields in setField + incrementNonce-strictly-advances") fixed in the *live*
executor — P1 makes it a HANDLER obligation, so it can never silently regress. Prove an unconditional
strengthening for the whole field-write family.

**P2 — close freshness / non-amp / monotone-nonce / index-bounds.** One floor per sub-phase, each
ending with the corresponding `handler_refines_execFullA_*` shedding its side-hypothesis (`hmono`,
`hb`, the epoch-residual) and the per-floor global companion theorem (the `turn_head_*` analogue).

**P3 — the forest cutover.** Prove `execFullForestA` node-step ⊑ the handler registry (lift the flat
refinement node-wise, reconciling with `execFullForestA_no_amplify`/`_conserves_per_asset`), then
switch `dregg_exec_full_forest_auth`'s body from `execFullForestG` to a handler-registry forest
executor. This is the live switch; it is VK/wire-affecting and the biggest piece.

**P4 — reconcile the two registries.** Prove `masterRegistry` (executable) and
`Substrate.VerbRegistry.classify` (signature) agree: every live `EffectTag` has exactly one handler,
and every handler classifies to its verb. Closes the "by name, not by proof" gap (`§1f`).

---

## 5. RISKS / HARDEST PARTS / DEPENDENCIES

- **Floor non-uniformity (real).** `conserves` is per-asset relational, `freshness` is over the
  post-state, `non-amp` is over delegation edges — they are NOT all `RKState → Args → Bool` gates.
  A naive "add three more Bool fields" under-models freshness/non-amp. P0's `FloorObligation` must be
  general enough (a `Prop`-valued post-condition, not just a Bool gate) or split into Bool-gate
  floors vs relational floors. This is the main design risk.
- **The forest cutover (P3) is the cost center.** Production is the tree executor, not flat
  `execFullA`. All ~30 existing refinement theorems target `execFullA`; lifting them through the
  forest fold (and reconciling with the forest's own `_no_amplify`/`_conserves_per_asset` keystones)
  is substantial. It is also VK/wire-affecting (per `feedback-dont-over-ember-gate`: drive to green +
  commit, do not park as "ember-gated").
- **Interaction with the just-banked fixes.** Commits `c4f4f0012` (reserved-field + no-replay),
  `1d029713e` (emitEvent/makeSovereign liveness), `72d516364` (node-cap attenuation),
  `85063e80a` (spawn/refresh epoch-stamp freshness), `761af9a63` (attenuate index fail-closed),
  `ee9bcfc0e` (revokeDelegation epoch) — these closed each hole in the LIVE executor arm-by-arm. They
  are EXACTLY the floors P1/P2 must promote to handler obligations. Risk: drift — if the live arm and
  the handler diverge again (as makeSovereign/receiptArchive already did, §6.3b), a new side-hyp
  silently re-appears. The cure is precisely making them obligation fields (the campaign's thesis).
- **Circuit / rotated-refinement composition.** ~20 `Circuit/RotatedKernelRefinement*.lean` files
  refine the CIRCUIT against `execFullA` (not the handler executor). The circuit-soundness apex
  (`project-circuit-soundness-apex`) is keyed to `execFullA`/`execFullForestA`. A handler cutover must
  preserve those refinements — either by proving the handler executor equals the circuit's reference
  semantics, or by re-keying the rotated refinements. NOT independent of the live circuit campaign.
- **`exerciseH` recursion + R4 facet mask.** The exercise refinement is only on the inner-turn honest
  path (`hinner` hypothesis, `HandlerExecutor.lean:1061`); the recursive handler is the most delicate
  to give unconditional obligations to.

---

## 6. VERDICT

**Tractable, high-leverage, and ~80% already done — but the campaign's framing overstates how much is
greenfield.** The proof-carrying handler design is not an idea to build; it is a landed, axiom-clean
subsystem (`Handler.lean` + `Handlers/*` + `HandlerExecutor.lean`). The matrix-killer `turn_conserves`
works, every domain handler discharges its three obligations, the total dispatch and ~30 refinement
theorems to `execFullA` exist.

**What is genuinely open is narrower and sharper than "build the handler executor":**

1. The obligation surface captures **3 of ~9 floors**. The other six (reserved-field, caveat,
   freshness, non-amp, monotone-nonce, index-bounds/membership) are carried as **refinement
   side-hypotheses** — which is the silent-gate shape the campaign wants to eliminate. Promoting them
   to typed obligations (P0–P2) is **the highest-leverage work** and is tractable: it is local,
   per-floor, additive, and each sub-phase has a crisp done-condition (the matching
   `handler_refines_execFullA_*` sheds its side-hyp).
2. The live executor is the **forest** path (`execFullForestG`), not the flat `execFullA` the handler
   executor refines. The cutover (P3) is the larger, VK-affecting piece and was not in the campaign's
   line of sight.

**Recommendation:** run P0 → P1 → P2 (the floor-obligation promotion) as the immediate campaign — it
directly delivers "missing gate is unrepresentable" for the whole field-write/authority/lifecycle
family and burns down the side-hypothesis class that is the real residual hole. Treat P3 (forest
cutover) as a separate, coordinated workstream with the circuit-soundness apex (they share the
`execFullA`/`execFullForestA` reference semantics). **First concrete step: the additive
`Dregg2/Exec/HandlerFloors.lean` `FloorObligation` record (P0), proving the two existing gates are
instances, touching no existing file.**
