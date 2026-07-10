/-
# Dregg2.Exec.ReactiveRegistry — the reactive subsystem MODELED, so `Promise`/`Notify` stop being an
unmodeled boundary and the React one-shot becomes an end-to-end THEOREM on the combined state.

DEBT-B classified the 33 deployed effects. `Promise`/`Notify` (`turn/src/executor/apply.rs`
`apply_promise :1315`, `apply_notify :1349`) mutate `self.reactive_registry.lock()` — an EXECUTOR-side
structure that is NOT a `RecordKernelState` field. So they have NO finite-map kernel commuting square,
correctly, and were named an honest OFF-KERNEL boundary. This module models the registry itself, so the
boundary becomes a PROVED subsystem:

  * The registry is modeled faithfully after `turn/src/reactive.rs` +
    `turn/src/pending.rs::PendingTurnRegistry` (a map keyed by the hole id, whose entry mirrors
    `PendingEntry { turn, condition, dependents, submitted_at, timeout_height }`; the id IS the wake-turn
    hash, `reactive.rs:217`).
  * `promiseStep`/`notifyStep` mirror `apply_promise`/`apply_notify`: a Pure actor guard, then a registry
    deposit, with the kernel component passed through VERBATIM. `promise_kernel_unchanged` /
    `notify_kernel_unchanged` turn the OFF-KERNEL claim into a THEOREM (the committed `RecordKernelState`
    is literally `= k`).
  * `reactStep` mirrors `apply_react` (`apply.rs:1405`): its kernel leg IS the committed
    `FinReactSquare.reactStmt`/`reactKStep` (a `noteSpend` nullifier advance under the wake-hash binding;
    `reactStep_kernel_is_reactStmt` proves it, so the nullifier gate is RIDDEN, not re-modeled), and its
    registry leg is the `resolve` removal. THE KEYSTONE `react_one_shot`/`no_double_react` proves no two
    `React`s on the same hole id both succeed — the hole is spent into the SAME `note_nullifiers` set that
    gates `NoteSpend`, so a repeat fail-closes (`apply.rs:1502`).

## HONEST SCOPE — deployed behaviour left off-kernel (named, not faked)
  * The proof/temporal gate `resolve_condition` (`apply.rs:1456`: proof validity + timeout via a TRANSIENT
    proof ledger and `self.block_height`) is EXECUTOR-side — NOT `RecordKernelState`. It is abstracted by
    the Pure binding guard `φ` (the wake-hash↔pending_id binding, `apply.rs:1429`), exactly as the
    committed `FinReactSquare` does; the proof-validity/expiry check is not re-modeled here.
  * `expire` (`pending.rs::check_timeouts`) removes past-timeout holes; its `currentHeight` is an OFF-KERNEL
    block-height input, and a timed-out hole is DROPPED from the registry WITHOUT any nullifier spend — so
    it is correctly registry-only (kernel-neutral). Modeled structurally, height named off-kernel.
  * Cascading resolution + broken-promise propagation (`PendingEntry.dependents`, `ResolutionEvent`,
    synthetic receipts) are registry EVENT / receipt-log machinery with no kernel effect; `resolve` models
    only the entry REMOVAL (the one-shot registry tooth). The event/cascade emission is not modeled.

Builds ON committed `FinReactSquare` (hence `RecordKernel` + Argus `noteSpend`) verbatim; edits NOTHING
committed. Sorry-free. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.FinReactSquare

namespace Dregg2.Exec.Reactive

open Dregg2.Exec
open Dregg2.Circuit.Argus (interp)
open Dregg2.Circuit.FinReactSquare (reactStmt reactKStep interp_reactStmt_eq_reactKStep)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — The registry model, mirrored from `turn/src/reactive.rs` + `turn/src/pending.rs`. -/

/-- **`ResolutionCondition`** — faithful mirror of `pending.rs::ResolutionCondition` (`pending.rs:57`),
the three conditions a promise-hole may await. `awaitCondition` carries the `ProofCondition` as an opaque
tag: its crypto/proof discharge is the OFF-KERNEL `resolve_condition` gate (see the module scope note),
not modeled here. -/
inductive ResolutionCondition where
  /-- `AwaitReceipt { turn_hash, federation_id }` — awaiting a (possibly remote) turn receipt. -/
  | awaitReceipt   (turnHash : Nat) (federationId : Option Nat)
  /-- `AwaitCondition(ProofCondition)` — awaiting a proof discharge (the tag; crypto is off-kernel). -/
  | awaitCondition (proofTag : Nat)
  /-- `AwaitHeight(u64)` — awaiting a block height. -/
  | awaitHeight    (height : Nat)
  deriving DecidableEq, Repr

/-- **`HoleEntry`** — one promise-hole, mirroring `pending.rs::PendingEntry` (`pending.rs:43`). The hole
`id` IS the wake-turn hash (`reactive.rs:217`, `notify` returns `wake.hash()`), so we carry `wake` as that
content hash and key the registry by it. `dependents` mirrors the cascade list (defaults empty, exactly as
`submit_pending_at` leaves it). `submittedAt`/`timeoutHeight` are the deposit's block-height bookkeeping. -/
structure HoleEntry where
  /-- The wake turn's content hash — the hole id (`reactive.rs:217`). -/
  wake          : Nat
  /-- The condition the recipient discharges to react (`PendingEntry.condition`). -/
  condition     : ResolutionCondition
  /-- Block height at which the hole times out (`PendingEntry.timeout_height`). -/
  timeoutHeight : Nat
  /-- Block height at which the hole was deposited (`PendingEntry.submitted_at`). -/
  submittedAt   : Nat
  /-- Turns waiting on THIS hole (`PendingEntry.dependents`); cascade is off-kernel event machinery. -/
  dependents    : List Nat := []
  deriving DecidableEq, Repr

/-- **`ReactiveRegistry`** — the reactive registry as an association list keyed by hole id, mirroring
`pending.rs::PendingTurnRegistry`'s `pending : HashMap<[u8;32], PendingEntry>` (`pending.rs:167`).
`lookup` is first-match, so a `deposit` (list-cons) shadows an older entry exactly as a `HashMap::insert`
overwrites. -/
abbrev ReactiveRegistry := List (Nat × HoleEntry)

/-- **`deposit`** — `PendingTurnRegistry::submit_pending_at` (`pending.rs:202`): insert the hole keyed by
its wake hash (its id). The kernel-backed `NotifyEdge` deposit. -/
def ReactiveRegistry.deposit (reg : ReactiveRegistry) (e : HoleEntry) : ReactiveRegistry :=
  (e.wake, e) :: reg

/-- **`lookup`** — `PendingTurnRegistry::get_pending` (`pending.rs:327`): first-match by id. -/
def ReactiveRegistry.lookup (reg : ReactiveRegistry) (id : Nat) : Option HoleEntry :=
  (reg.find? (fun p => p.1 == id)).map (·.2)

/-- **`resolve`** — `PendingTurnRegistry::resolve`'s `pending.remove(&turn_hash)` (`pending.rs:246`): the
hole is CONSUMED (removed). This is `reactive.rs`'s registry-removal one-shot tooth — a redundant second
tooth beside the load-bearing nullifier gate (`apply.rs:1536`). The cascade/event emission is off-kernel
receipt-log machinery, not modeled. -/
def ReactiveRegistry.resolve (reg : ReactiveRegistry) (id : Nat) : ReactiveRegistry :=
  reg.filter (fun p => p.1 != id)

/-- **`expire`** — `PendingTurnRegistry::check_timeouts` (`pending.rs:309`): drop holes past their timeout.
`currentHeight` is an OFF-KERNEL block-height input; a timed-out hole is removed from the registry WITHOUT
any nullifier spend (kernel-neutral) — so expiry cannot spend a hole (it can only forget it). -/
def ReactiveRegistry.expire (reg : ReactiveRegistry) (currentHeight : Nat) : ReactiveRegistry :=
  reg.filter (fun p => decide (currentHeight ≤ p.2.timeoutHeight))

/-! ## §2 — `promiseStep` / `notifyStep`: the OFF-KERNEL fact becomes a THEOREM.

Both mirror the deployed handlers: a Pure actor guard, then a registry `deposit`, with the kernel
component `k` threaded UNCHANGED. `promise_kernel_unchanged`/`notify_kernel_unchanged` prove that
committed step's `RecordKernelState` is literally `= k` — the honest OFF-KERNEL boundary, now a theorem. -/

/-- **`promiseStep`** — `apply_promise` (`apply.rs:1315`): guard `cell == actor` (a cell makes its OWN
standing commitments), then deposit the hole. The kernel `k` is passed through verbatim. -/
def promiseStep (k : RecordKernelState) (reg : ReactiveRegistry)
    (cell actor : CellId) (e : HoleEntry) : Option (RecordKernelState × ReactiveRegistry) :=
  if cell = actor then some (k, reg.deposit e) else none

/-- **`notifyStep`** — `apply_notify` (`apply.rs:1349`): guard `from == actor` (no spoofed provenance)
AND `wake.agent == to` (the deposited wake is the recipient's to discharge), then deposit. Kernel `k`
passed through verbatim. -/
def notifyStep (k : RecordKernelState) (reg : ReactiveRegistry)
    (from_ actor to_ wakeAgent : CellId) (e : HoleEntry) :
    Option (RecordKernelState × ReactiveRegistry) :=
  if from_ = actor ∧ wakeAgent = to_ then some (k, reg.deposit e) else none

/-- **`promise_kernel_unchanged` — the OFF-KERNEL claim, now a THEOREM.** A committed `Promise` step
leaves the kernel component EXACTLY `k`: `Promise` touches only the executor-side registry, never
`RecordKernelState`. (The prompt's `(promiseStep …).1 = k`, in fail-closed committed form.) -/
theorem promise_kernel_unchanged {k k' : RecordKernelState} {reg reg' : ReactiveRegistry}
    {cell actor : CellId} {e : HoleEntry}
    (h : promiseStep k reg cell actor e = some (k', reg')) : k' = k := by
  unfold promiseStep at h
  by_cases hc : cell = actor
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **`notify_kernel_unchanged` — the OFF-KERNEL claim, now a THEOREM.** A committed `Notify` step leaves
the kernel component EXACTLY `k`: `Notify` deposits into the recipient's registry only. -/
theorem notify_kernel_unchanged {k k' : RecordKernelState} {reg reg' : ReactiveRegistry}
    {from_ actor to_ wakeAgent : CellId} {e : HoleEntry}
    (h : notifyStep k reg from_ actor to_ wakeAgent e = some (k', reg')) : k' = k := by
  unfold notifyStep at h
  by_cases hc : from_ = actor ∧ wakeAgent = to_
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-! ## §3 — `reactStep`: the combined React step, whose kernel leg IS the committed `reactStmt`. -/

/-- **`reactStep`** — `apply_react` (`apply.rs:1405`) on the combined `(RecordKernelState ×
ReactiveRegistry)`: the kernel leg is the committed `FinReactSquare.reactKStep` (= `interp (reactStmt
pendingId φ)`, the `noteSpend` nullifier advance under the wake-hash binding `φ`), and — on commit — the
registry `resolve`s (removes) the hole. Fail-closed exactly as the kernel leg (a bad binding OR a
double-spend ⇒ `none`; the registry is then untouched). -/
def reactStep (k : RecordKernelState) (reg : ReactiveRegistry) (pendingId : Nat)
    (φ : RecordKernelState → Bool) : Option (RecordKernelState × ReactiveRegistry) :=
  match reactKStep k pendingId φ with
  | some k' => some (k', reg.resolve pendingId)
  | none    => none

/-- **`reactStep_kernel_is_reactStmt` — the kernel leg is RIDDEN, not re-modeled.** The kernel projection
of `reactStep` IS the committed `interp (reactStmt pendingId φ)` — the SAME `noteSpend` nullifier gate
`NoteSpend` rides, guarded by the wake-hash binding. We do not re-implement the double-spend gate. -/
theorem reactStep_kernel_is_reactStmt (k : RecordKernelState) (reg : ReactiveRegistry) (pendingId : Nat)
    (φ : RecordKernelState → Bool) :
    (reactStep k reg pendingId φ).map Prod.fst = interp (reactStmt pendingId φ) k := by
  rw [interp_reactStmt_eq_reactKStep]
  unfold reactStep
  cases reactKStep k pendingId φ <;> simp

/-- **`reactStep_inserts`.** A committed React SPENDS the hole: `pendingId ∈ k1.nullifiers`. The React's
kernel leg is `noteSpendNullifier` under the binding guard, so a commit inserts the hole id into the SAME
spent-note set that gates `NoteSpend` (`note_spend_inserts`). -/
theorem reactStep_inserts {k k1 : RecordKernelState} {reg reg1 : ReactiveRegistry}
    {id : Nat} {φ : RecordKernelState → Bool}
    (h : reactStep k reg id φ = some (k1, reg1)) : id ∈ k1.nullifiers := by
  unfold reactStep at h
  cases hk : reactKStep k id φ with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k'' =>
      rw [hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hk1, _⟩ := h
      subst hk1
      unfold reactKStep at hk
      by_cases hφ : φ k = true
      · rw [if_pos hφ] at hk; exact note_spend_inserts hk
      · rw [if_neg (by simpa using hφ)] at hk; exact absurd hk (by simp)

/-- **`reactStep_rejects_spent` (the one-shot gate BITES).** A React on a hole id ALREADY in the
nullifier set fail-closes (`= none`) for ANY binding guard `φ`: the `noteSpend` double-spend gate
(`note_no_double_spend`) refuses it. The kernel-side one-shot tooth (`apply.rs:1502`). -/
theorem reactStep_rejects_spent {k : RecordKernelState} {reg : ReactiveRegistry}
    {id : Nat} {φ : RecordKernelState → Bool} (hmem : id ∈ k.nullifiers) :
    reactStep k reg id φ = none := by
  have hnone : reactKStep k id φ = none := by
    unfold reactKStep
    by_cases hφ : φ k = true
    · rw [if_pos hφ]; exact note_no_double_spend k id hmem
    · rw [if_neg (by simpa using hφ)]
  unfold reactStep; rw [hnone]

/-- **THE KEYSTONE — `react_one_shot` (no double-react, end-to-end on the combined state).** Once a
`React` on hole `id` SUCCEEDS (producing `k1`), EVERY subsequent `React` on the SAME `id` — under ANY
binding/proof guard `φ'` — fail-closes (`= none`). The first react spent the hole into the nullifier set
(`reactStep_inserts`); the gate then refuses the repeat (`reactStep_rejects_spent`). This is the
promise-hole-as-nullifier one-shot linearity: a promise deposited by `Promise`/`Notify` is spent by
`React` at most once, riding the deployed `note_nullifiers` double-spend gate. -/
theorem react_one_shot {k k1 : RecordKernelState} {reg reg1 : ReactiveRegistry}
    {id : Nat} {φ φ' : RecordKernelState → Bool}
    (h1 : reactStep k reg id φ = some (k1, reg1)) :
    reactStep k1 reg1 id φ' = none :=
  reactStep_rejects_spent (reactStep_inserts h1)

/-- **`no_double_react` — the keystone as an impossibility.** No two `React`s on the same hole id both
succeed: given a first success on `id`, a second `React` on `id` CANNOT produce `some`. -/
theorem no_double_react {k k1 k2 : RecordKernelState} {reg reg1 reg2 : ReactiveRegistry}
    {id : Nat} {φ φ' : RecordKernelState → Bool}
    (h1 : reactStep k reg id φ = some (k1, reg1)) :
    reactStep k1 reg1 id φ' ≠ some (k2, reg2) := by
  rw [react_one_shot h1]; simp

#assert_axioms promise_kernel_unchanged
#assert_axioms notify_kernel_unchanged
#assert_axioms reactStep_kernel_is_reactStmt
#assert_axioms react_one_shot
#assert_axioms no_double_react

/-! ## §4 — TEETH (both polarities). Concrete fixtures: a first React on a fresh hole FIRES; a second on
the same hole BITES; a promise deposit/lookup/resolve round-trips. -/

section Teeth

/-- A concrete kernel: live account `0`, EMPTY nullifier set. -/
def k0 : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [], caps := fun _ => [], nullifiers := [] }

/-- The same kernel with hole `7` ALREADY reacted (nullifier set `[7]`) — the double-spend fixture. -/
def k7 : RecordKernelState := { k0 with nullifiers := [7] }

/-- The empty registry. -/
def reg0 : ReactiveRegistry := []

/-- A promise-hole for wake `7`, awaiting height `100`. -/
def hole7 : HoleEntry :=
  { wake := 7, condition := ResolutionCondition.awaitHeight 100, timeoutHeight := 100, submittedAt := 10 }

-- Registry round-trip: a deposited hole is LOOKED UP; after resolve it is GONE; expiry drops it past timeout.
#guard ((reg0.deposit hole7).lookup 7).isSome                       -- deposit ⇒ live
#guard (((reg0.deposit hole7).resolve 7).lookup 7).isNone           -- resolve ⇒ consumed (one-shot removal)
#guard (((reg0.deposit hole7).expire 101).lookup 7).isNone          -- expire past timeout ⇒ dropped (no spend)
#guard (((reg0.deposit hole7).expire 50).lookup 7).isSome           -- expire before timeout ⇒ survives

-- React teeth on the combined state:
#guard (reactStep k0 reg0 7 (fun _ => true)).isSome                 -- fresh hole + valid binding ⇒ FIRES
#guard ((reactStep k0 reg0 7 (fun _ => true)).map (fun p => p.1.nullifiers)) == some [7]  -- advances [] → [7]
#guard (reactStep k0 reg0 7 (fun _ => false)).isNone               -- bad binding (wake-hash ≠ id) ⇒ REJECT
#guard (reactStep k7 reg0 7 (fun _ => true)).isNone                -- stale hole (already reacted) ⇒ REJECT

/-- **POSITIVE tooth — a first React on a fresh hole FIRES and spends `id`.** The combined step commits,
and the resulting kernel's nullifier set advances `[] → [7]` (the hole is spent, one-shot armed). -/
theorem react_first_fires :
    (reactStep k0 reg0 7 (fun _ => true)).map (fun p => p.1.nullifiers) = some [7] := by
  rfl

/-- **NEGATIVE tooth (bad binding) — the wake-hash guard BITES.** A React whose binding guard is false
(`wake.hash() ≠ pending_id`) fail-closes; the registry is untouched. -/
theorem react_rejects_bad_binding : reactStep k0 reg0 7 (fun _ => false) = none := by
  rfl

/-- **NEGATIVE tooth (double-react) — the one-shot gate BITES.** A second React on an ALREADY-reacted
hole (`7 ∈ k7.nullifiers`) fail-closes even with a VALID binding: the `note_nullifiers` double-spend
gate refuses it (`apply.rs:1502`). The keystone, exercised on a concrete fixture. -/
theorem react_second_rejected : reactStep k7 reg0 7 (fun _ => true) = none :=
  reactStep_rejects_spent (by decide)

/-- **The keystone FIRES end-to-end on the fixtures.** The first React on `7` succeeds, and THEN a second
React on `7` (any guard) is refused — no two Reacts on the same hole both succeed. -/
theorem react_one_shot_fires :
    ∀ k1 reg1, reactStep k0 reg0 7 (fun _ => true) = some (k1, reg1) →
      reactStep k1 reg1 7 (fun _ => true) = none :=
  fun _ _ h => react_one_shot h

end Teeth

end Dregg2.Exec.Reactive
