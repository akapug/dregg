# DELTA-FUTURE — the Lean kernel should be delta-based (a faithfulness fork, not just proof sugar)

> Captured 2026-07-09 so we don't lose it. This is NOT merely "proofs would be cleaner." The measured finding:
> **the deployed Rust already applies effects as validated deltas, so our nested-`if` Lean ops are the *less*
> faithful model** — same category of mismatch as DEBT-B's total-functions-vs-finite-maps. Fixing it is a
> faithfulness correction that *also* dissolves the per-effect proof cluster and aligns the kernel with the
> circuit's per-cell rows. Related: [[CARRIER-CENSUS]], [[DEBT-B-FINITE-MAP-REFINEMENT]].

## The verified evidence (the Rust IS delta-based)
- `cell/src/ledger.rs:35` — `struct CellStateDelta` (the per-cell change).
- `ledger.rs:70` — `updated: Vec<(CellId, CellStateDelta)>` — an effect yields a **LIST of (CellId, delta)**.
  This is exactly the update-list / effects-as-data shape.
- `ledger.rs:785 validate_delta` (the GUARD) → `ledger.rs:700 apply_delta` / `:881 apply_cell_delta`
  ("Apply a CellStateDelta to a cell (assumes validation passed)") — the APPLY, a fold over the list.
- So the deployed pipeline is **`validate → Vec<(CellId, CellStateDelta)> → fold-apply`**. Guard and apply are
  already separated; the "delta" is already the interchange form.

## Why our current Lean model is less faithful
`Dregg2/Exec/RecordKernel.lean`'s `recTransfer`/`recCreditCell`/`recKExec` fuse guard + compute + apply into one
nested-`if` (`fun c => if c = src then … else if c = dst then …`). That is a DIFFERENT structure from the Rust's
validate/delta/apply-list. The EffectsAsDataProto (2026-07-09) measured the cost: reconciling a delta-fold
against the nested-`if` needs a per-effect `by_cases` over touched cells (empirically load-bearing). **That
residue is an artifact of modeling the impl with a nested-`if` instead of the delta-fold the impl actually
uses.** Against a delta-based Lean kernel (`apply_cell_delta`-shaped), both sides are the same fold — the
`by_cases` becomes `rfl`-ish and the effects-as-data architecture FULLY composes.

## The payoff (why this is worth wanting)
1. **More faithful.** The Lean semantics would mirror `validate_delta`/`apply_cell_delta` structurally, not
   just extensionally. Closes a faithfulness gap the same way finite-maps closed the hashability gap.
2. **Dissolves the per-effect proof cluster.** `denote (finStep e f) = recStep e (denote f)` for ALL effects
   follows from one naturality lemma over the delta-list (the prototype's `denote_applyUpdates`), because the
   deployed op IS the fold now. R3-continuation (~28 effects) + `RestFrameDecodes2*` + `DeployedFaithful*` +
   `Satisfied2Faithful` collapse to "effects are deltas, naturality is one theorem." The full dissolution the
   prototype couldn't reach against the nested-`if` model.
3. **Aligns kernel ↔ circuit.** The AIR is already per-cell (`circuit/src/effect_vm/air.rs`); a delta-list
   kernel makes each circuit row = one `CellStateDelta`, likely simplifying `Satisfied2Faithful` / the
   descriptor refinement.
4. **Explicit, auditable effect footprints.** A delta-list IS "what this effect changed" — makes locality /
   confinement / non-interference theorems (this effect touches only these cells) nearly free, and it's exactly
   what a receipt/witness wants to attest.
5. **Guard/apply separation matches the Rust** — the admissibility guard becomes `validateDelta`, the state
   change becomes `applyDelta`, mirroring `validate_delta`/`apply_cell_delta` one-to-one.

## Synergy with DEBT-B (they are the same thesis, on different axes)
- DEBT-B: make the STATE faithful to the impl (finite maps, not total functions) → hashable.
- DELTA: make the STEP faithful to the impl (delta-fold, not nested-`if`) → composable.
- Together = the fully faithful, fully hashable, fully composable kernel. R1 (`FinKernelState`, `denote_injective`)
  and R2 (`frameHashFin`, `RestHashIffFrame`) are about STATE and SURVIVE a delta-refactor unchanged. Only R3
  (the step commuting square) is redone — and it gets *much* cleaner (the reason to consider delta BEFORE
  grinding R3-continuation against the nested-`if` model).

## The cost (why it's a fork, not a now-thing)
- Core refactor of `recKExec`/`recTransfer`/`recKMint`/`recKBurn`/`recKDelegate`/`recKRevokeTarget` and every
  effect's semantics into `validateDelta`/`applyDelta` form. Ripples through Argus (`Stmt.lean`, the 45
  `Effects/*`) and everything that reasons over the kernel step — the apex included.
- The Lean `Delta` type should MATCH the Rust `CellStateDelta`/`LedgerDelta` fields (or refine to them), which
  introduces its own (small, checkable) faithfulness obligation: `Lean.applyDelta` denotes to what
  `apply_cell_delta` does.

## Open questions to resolve BEFORE committing (measure first, per today's discipline)
1. Does EVERY effect fit `validate → delta-list → fold`? (Some — bulk cap rewrites, lifecycle, factory — may
   produce non-cell deltas or multi-field deltas; check `CellStateDelta`'s actual fields cover them.)
2. Does it genuinely simplify the circuit refinement (`Satisfied2Faithful`), or just move work?
3. LOC / ripple cost of the core refactor vs. the bridge+tactic ceiling against the current model.
4. Does matching the Rust `CellStateDelta` structure exactly avoid a NEW mirror, or introduce one?

## ⚖ MEASURED VERDICT (2026-07-10, DeltaProto.lean — audited by type, green 1432 jobs)
The de-risk ran. `EffectsAsDataProto`'s earlier **NO** conflated two costs; separated, the answer is **YES**:
- **RECURRING per-effect square: ZERO per-cell `by_cases`.** `denote_applyDelta : denote (applyDeltaFin ds f) =
  applyDeltaRec ds (denote f)` is EFFECT-FREE (names no effect), proved once by induction on the delta-list.
  Every effect's square is then `cases recKX (guard) → rw [denote_applyDelta] → exact (migration).symm`. Verified:
  `finTransferDelta_denote` has zero `by_cases`; its only split is the none/some **guard** match, which every
  executable op has.
- **ONE-TIME migration lemma: 2 per-cell `by_cases`** (`c=src`, `c=dst`) in `applyDeltaRec_transfer` — disclosed,
  isolated, NOT hidden in a helper. Proportional to the cells an effect writes.
- **Under REDEFINITION** (the deployed op DEFINED as the fold, §6): the per-cell `by_cases` **vanishes** —
  `recKExecDelta_eq_applyDelta` retains only the structural `hg` authorization-guard split.
- **Blast radius of redefinition (re-derived independently): 150 files, 112 proof sites** that `unfold`/`simp`
  `recTransfer`/`recKExec`/`recCreditCell`.
- Faithfulness win: the Lean `CellDelta.balanceChange : ℤ` is a RELATIVE delta mirroring Rust's `i64`, so
  `transferDelta turn = [(src,⟨-amt⟩),(dst,⟨amt⟩)]` is state-INDEPENDENT DATA (the earlier absolute-overwrite
  proto had to read `k`).

## ✅ DECISION (2026-07-10)
**Adopt the delta model for R3-continuation (Option A) — do NOT redefine the deployed ops inside DEBT-B.**
Option A captures the recurring win (shared effect-free naturality; per-effect cost drops from a full
commuting-square proof to a small reconciliation lemma sized by cells-touched) at LOW risk.
**Option B (redefine `recKExec`/`recTransfer` as folds) is DEFERRED as its own scoped campaign**: it makes the
migration lemmas guard-only and is structurally faithful to `apply_cell_delta`, but ripples 112 proof sites across
150 files *including the apex*. That is not a thing to do inside DEBT-B. Its cost is now MEASURED, not guessed —
which is the whole point of having run the de-risk.
⚠ Scope note for R3-continuation: `denote_applyDelta` leverage is per-FIELD. `CellDelta` currently models only
`balanceChange` (the one field transfer touches). Effects mutating `caps`/`lifecycle`/`heaps`/`slotCaveats` need
their field's delta + its own naturality instance. Rust's `CellStateDelta` has six fields — mirror them as needed.

## The trigger
When R3-continuation / the faithfulness cluster is taken on for real, evaluate the delta-refactor FIRST — a
one-effect prototype (transfer as `validateDelta`+`applyDelta` mirroring `ledger.rs`, measure whether
`finTransfer_denote` becomes `rfl`-ish and the circuit row aligns) — before committing to the bridge+tactic
against the nested-`if` model. If it composes, delta-refactor is likely cheaper end-to-end AND more faithful.
The near-term (bridge + `refine_commutes` tactic) remains the honest ceiling for the CURRENT model; this note
is the better model waiting for its de-risk.
