# DEBT B — the finite-map data refinement (design, oriented 2026-07-09)

> Kills the single largest carrier cluster in the metatheory (CARRIER-CENSUS.md DEBT B, ~250 uses:
> `RestHashIffFrame` 199, `RestFrameDecodes2*`, `DeployedFaithful*`, `Satisfied2Faithful`, `LeafRealization`).
> Root cause: `RecordKernelState` models per-cell state as **total functions over an infinite `CellId`
> domain**, which no `RH : … → ℤ` can injectively bind — so the whole-kernel commitment binding is
> unsatisfiable and every downstream soundness theorem is vacuous-in-application. This is NOT a research
> problem; it is a modeling mismatch. **The deployed Rust already uses finite maps.** We make the Lean model
> faithful to the impl, and the "unrealizable" carriers become proved lemmas.

## The exact targets (from `Dregg2/Exec/RecordKernel.lean:309`)
Function-valued fields, every one `Key → V` with a **canonical default**:

| field | Lean type | default | key domain |
|---|---|---|---|
| `cell` | `CellId → Value` | `.record []` | CellId |
| `caps` | `Caps = Label → List Cap` | `[]` | Label |
| `bal` | `CellId → AssetId → ℤ` | `0` | CellId × AssetId |
| `slotCaveats` | `CellId → List SlotCaveat` | `[]` | CellId |
| `lifecycle` | `CellId → Nat` | `0` | CellId |
| `deathCert` | `CellId → Nat` | `0` | CellId |
| `delegate` | `CellId → Option CellId` | `none` | CellId |
| `delegations` | `CellId → List Cap` | `[]` | CellId |
| `delegationEpoch` | `CellId → Nat` | `0` | CellId |
| `delegationEpochAt` | `CellId → Nat` | `0` | CellId |
| `heaps` | `CellId → List (ℤ × ℤ)` | `[]` | CellId |

Already finite (NO refinement needed): `accounts : Finset CellId`, `nullifiers`/`revoked`/`commitments : List Nat`,
`factories : List (Nat × FactoryEntry)`.

## The impl side (the refinement is FREE — impl unchanged)
The deployed Rust already stores these sparsely: `HashMap<CellId, …>`, `HashMap<(CellId,u32), DerivationNode>`
(`cell/src/derivation.rs:172`), `BTreeMap<[u8;32], Entry>` (`custom_effect.rs:189`),
`HashMap<CellId, CellStateDelta>` (`finalize.rs:511`), `Cell` (`cell/src/cell.rs:249`), and the commitment is
`Poseidon2(nonce, balance, fields, cap_root, …)` over the CONCRETE cell — `circuit/src/effect_vm/cell_state.rs`.
**A `BTreeMap` is exactly a canonical sorted finite map — the serialization the injective hash needs.** So the
refinement changes the LEAN MODEL to match the impl; the impl pays nothing.

## The design
1. **`SortedMap Key V` = a sorted-nodup association list (LOCKED 2026-07-09; NOT Mathlib `Finmap`).** A structure
   `{ entries : List (Key × V) // entries.map Prod.fst |>.Sorted (·<·) ∧ Nodup }`, read as `fun k =>
   (entries.lookup k).getD default`. RATIONALE (stronger than efficiency — FAITHFULNESS): the DEPLOYED commitment
   ALREADY sorts — `cap_root.rs::CanonicalCapTree` folds the **sorted-by-slot_hash** leaf list
   (`DeployedCapTree.lean:20`), the state commit uses **sorted-canonical** leaves (`StateCommit.lean:151`), and
   `ListCommit.lean:34` hashes a **canonical per-entry serialization**. So the sorted list IS what the impl
   commits over — serialization is DEFINITIONAL (no canonicalization step, no quotient), the injective-hash proof
   is DIRECT (sorted+nodup ⇒ `entries = entries' ↔ map = map'`), and `impl_refines` (Rust `BTreeMap`/the sorted
   CanonicalCapTree) is definitional. Mathlib `Finmap` was REJECTED: it is a `Quotient` by permutation, so it
   abstracts away the very sortedness the commitment relies on and forces quotient-section gymnastics at the
   load-bearing hash step. Reuse the existing `sortedInsert` (108 uses in-tree) + `ListCommit` + `DeployedCapTree`
   for the invariant plumbing; the "REALIZABLE — canonical serialization" annotations on `cellLeafInjective` /
   `ListCommit` become ACTUALLY realized once the state provides this finite canonical form.
2. **`FinKernelState`** — the same structure with the 11 fields as `FinMap`s; the already-finite fields
   unchanged.
3. **`denote : FinKernelState → RecordKernelState`** — field-wise lookup-with-default. This is the refinement
   relation `impl ⊑ model`; it is TOTAL and SURJECTIVE onto reachable states (executions start from empty maps
   and each effect touches finitely many keys, so every reachable `RecordKernelState` is `denote` of some
   `FinKernelState`). Prove `reachable k → ∃ f, denote f = k`.
4. **Effect simulation** — for each effect, `denote (finStep e f) = recStep e (denote f)` (map-update denotes to
   function-update). REUSE the existing per-effect interp: `Dregg2/Circuit/Argus/Stmt.lean` (`interp_*_eq_recK*`),
   `RotatedKernelRefinementCapFamily.lean` (`DelegateCapsTreeEncodes`/`AttenuateCapsTreeEncodes` — the cap-tree
   refinement scaffold), `DeployedCapTree.lean` (the finite 7-field cap-tree already modeled).
5. **`frameHashFin : FinKernelState → ℤ`** = `Poseidon2(canonical_serialize(all fields))`, and prove
   `restHashIffFrame_fin : frameHashFin f = frameHashFin f' ↔ f = f'` **as a THEOREM** — under `Poseidon2SpongeCR`,
   a finite canonical encoding is injective. This is the discharge of `RestHashIffFrame` (lift via `denote`).

## What this discharges (the payoff)
- `RestHashIffFrame` (199) → PROVED (`restHashIffFrame_fin` + `denote` surjectivity).
- `RestFrameDecodes2` + `…Dual/Triple/Quad/Quint` (~44) → each is a per-effect frame-decode; follows from the
  simulation + the frame hash.
- `DeployedFaithfulEff*` / `DeployedFaithful*` / `FaithfulCapTree` (~33) → the finite cap-tree IS the canonical
  model now, so "the deployed tree faithfully implements caps" is `denote`-of-the-tree = the Caps function,
  a theorem, not an assumption (build on `DeployedCapTree` + `CapRootBridge`).
- `Satisfied2Faithful` (34) → the AIR is faithful to the finite step, provable from the simulation.
- `LeafRealization` / `LogRealization` (11) → the leaf/log encoders are injective on the finite canonical form
  (they already have `_of_realization` reductions; realize them on `FinKernelState`).
- ENABLES the injectivity plumbing collapse (CARRIER-CENSUS cluster 2, ~1200 uses): with a finite serializable
  state, `cellLeafInjective`/`compressNInjective` route to `Poseidon2SpongeCR` for real.

## Existing scaffolding to build ON (do NOT re-mirror)
- `Dregg2/Exec/Kernel.lean`, `Exec/MultiAsset.lean` — `AList`/`Finmap` precedent in the kernel.
- `Dregg2/Circuit/DeployedCapTree.lean` — the finite 7-field cap-tree (the `caps` finite model).
- `Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean` — cap-tree refinement structures + per-effect refine
  theorems (`delegate_descriptorRefines`, `attenuate_descriptorRefines_exact`).
- `Dregg2/Circuit/CapRootBridge.lean` — `CapsEncodes` (the cap→root encoding).
- `Dregg2/Circuit/StateCommit.lean` — `RestHashIffFrame`, `recStateCommit_binds_kernel`, `cellLeafInjective`,
  `compressNInjective_of_poseidon2CR` (the reductions to reuse).
- `Dregg2/Circuit/Freshness.lean` — its `no_replay` is parametric over a `CommitSurface`; a
  `FinKernelState`-grounded surface is the concrete instance that drops `RestHashIffFrame`.

## STATUS (2026-07-09)
- **R1 DONE** `6458e10d2` — `SortedMap`/`CanonMap` + `SortedMap.ext` (canonical form) + `FinKernelState` +
  `denote` + `denote_injective` (UNCONDITIONAL) + the surjectivity honesty-gate (`hpres` explicit, `finStep`
  abstract). Audited by type.
- **R2 DONE** `e365d1c2d` — `serializeFin` + `serializeFin_injective` + `frameHashFin` + `restHashIffFrame_fin`
  (residual `Poseidon2SpongeCR` ALONE) + `restHashIffFrame_of_fin` (the `StateCommit.RestHashIffFrame`
  biconditional, PROVED on the denote-image / reachable subclass — honestly scoped, vacuous-on-image for the
  accumulator roots because R1 doesn't yet carry them; see convergence item below).
- **R3-core DONE** `e365d1c2d` — `finStep`/`recStep` (REAL `recK*` semantics) + `finStep_canonical` +
  `finStep_denote` (the commuting square) + `reachable_states_are_finite` — for the **5 `FullAction` primitives**
  (balance/delegate/revoke/mint/burn) ONLY. The other ~28 deployed effects are NOT covered (honest scope).

## REMAINING PLAN (in order)
1. **VK-epoch root convergence** — `FinKernelState` must carry `nullifierRoot`/`revokedRoot` (`Fin 8 → ℤ`,
   finite — verbatim) + the pending `commitmentsRoot` dual (`1dce9523c`). Currently DROPPED (denote defaults
   them ⇒ R2's root-clauses vacuous). Fold into R4/R3.
2. **The delta de-risk FIRST** (`DELTA-FUTURE.md`) — the deployed Rust is already delta-based (`ledger.rs`); the
   EffectsAsDataProto NO was against the nested-`if` model. Prototype the delta-refactor on ONE effect before
   committing R3-continuation. If it composes → delta-refactor (dissolves the cluster + more faithful); else →
   the `denote_applyUpdates` bridge + a `refine_commutes` tactic is the ceiling for the current model.
3. **R3-continuation** — the remaining ~28 effects, via the winning model.
4. **R4** — re-seat the apex commitment binding on `FinKernelState`; drop `RestHashIffFrame`/`RestFrameDecodes2*`/
   `DeployedFaithful*`/`Satisfied2Faithful` from the carried set; collapse the injectivity cluster to the floor.

## Original swarm plan (fire ONLY after ember signs off on this design)
- **Lane R1 — representation + denotation:** `FinKernelState`, `FinMap`/canonical-sort, `denote`, `denote`
  surjectivity on reachable states. Foundation; others depend on it.
- **Lane R2 — frame hash + `RestHashIffFrame` theorem:** `frameHashFin`, `restHashIffFrame_fin` ← Poseidon2CR;
  lift to discharge `RestHashIffFrame`.
- **Lane R3 — effect simulation:** `denote (finStep e ·) = recStep e (denote ·)` per effect family, reusing
  Argus/RotatedKernelRefinement/DeployedCapTree.
- **Lane R4 — plumb the apex:** re-seat `recStateCommit_binds_kernel` / the surface on `FinKernelState`, collapse
  the injectivity hypotheses to the single `Poseidon2SpongeCR` floor, and drop `RestHashIffFrame` from the
  downstream carried set.
Each lane grounded with the exact signatures above; each audited by reading the resulting TYPES (no carrier may
be assumed that this refinement was supposed to discharge). Whole-tree `lake build Dregg2` green after each.

## The honesty gate for this refactor
`denote` must be TOTAL and its surjectivity on reachable states PROVED — otherwise a `FinKernelState` binding
theorem is just a new, smaller vacuity. `restHashIffFrame_fin` must reduce to `Poseidon2SpongeCR` with NO new
carrier. If any field's usage does not fit `Key → V`-with-default (spot: `bal` is two-level; `caps` is over
`Label`), flag it precisely — do not force it.
