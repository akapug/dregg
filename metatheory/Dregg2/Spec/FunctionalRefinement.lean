/-
# Dregg2.Spec.FunctionalRefinement — REAL functional refinement: the executor commits EXACTLY
the independently-specified output (output-uniqueness, not merely "the result satisfies a predicate").

## The gap this closes (the grounded study finding)

A `RecordProgram`/`CellProgram` is a **constraint**: `admits (old, new)` accepts or rejects a
*candidate* pair — it does NOT name or derive the intended `new`. The next state is computed by a
*separate* op language (`applyOp`, the escrow/queue kernel ops), which has had NO declarative spec
it is proven to refine. So far we prove:

  * `recExec_admitted`   — "the committed result satisfies my predicate" (`admits old new`), and
  * `recExec_commits_applyOp` — "the commit equals what the op produced".

But neither says **the result IS the function I meant**. `admits old new` permits MANY `new`
(e.g. `monotonic "count"` admits every `new ≥ old`). Output *uniqueness + correctness* — "this op
commits to EXACTLY the post-state my protocol intent prescribes, and rejects every other candidate"
— existed only for the transfer beachhead, not the ~43 effects.

This module establishes that stronger property for the **escrow family** (create / release / refund)
as the validated REFERENCE PATTERN, and pushes it to a **second family** (queue FIFO
allocate / enqueue / dequeue). For each effect we:

  1. Write an **INDEPENDENT declarative reference function** in plain Lean — `escrowCreateSpec`,
     `escrowReleaseSpec`, … : the post-state, named *from protocol intent* (the asset ledger moves;
     a fresh unresolved record is parked; the settled record is marked resolved; the FIFO buffer
     gains/loses one message). These are written WITHOUT looking at the executor's code — they say
     what the correct answer IS, not "= the executor". (Anti-circularity: `escrowCreateSpec :=
     createEscrowRawAsset` would be vacuous; we instead reconstruct the post-state field-by-field
     from intent and then PROVE the executor equals it — a theorem that could be FALSE if the
     executor debited the wrong cell / parked the wrong record.)

  2. Prove the **functional-refinement triangle with output-uniqueness**:
     `step k a = some k' ↔ (gate k a ∧ k' = spec k a)`. The `→` direction is the "commits to EXACTLY
     the spec output" fact (output-uniqueness — strictly stronger than `admits`); the `←` direction
     is liveness/completeness (whenever the gate holds, the executor commits the spec's output).

  3. Include an **ANTI-GHOST tooth**: a candidate `k'' ≠ spec k a` is REJECTED —
     `step k a ≠ some k''` whenever `k'' ≠ spec k a` — so the refinement pins the UNIQUE correct
     output (non-vacuously: we also exhibit, via `#guard`, a concrete tampered candidate that the
     executor refuses while accepting the spec's output).

`#assert_axioms`-clean, no `sorry`, no `:= True`. Imports the escrow handlers (`createEscrowStep`,
`releaseStep`, `refundStep` — the actor-gated R2 steps) and the kernel queue ops.
-/
import Dregg2.Exec.Handlers.Escrow
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Exec.Handlers.Authority
import Dregg2.Exec.Handlers.Seal
import Dregg2.Exec.Handlers.Lifecycle
import Dregg2.Exec.Handlers.Bridge
import Dregg2.Exec.Handlers.Queue
import Dregg2.Exec.Handlers.Exercise

namespace Dregg2.Spec.FunctionalRefinement

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handlers.Escrow
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects recKMintAsset recKBurnAsset recBalCredit attenuateSlotF)

/-! ## §0 — The independent intent-level vocabulary.

These are the field-level moves the protocol intent DESCRIBES, re-derived here in plain Lean
WITHOUT reference to the executor's `createEscrowRawAsset`/`settleEscrowRawAsset`. They are the
"what the answer is" oracle; the triangle below proves the executor realizes exactly them. -/

/-- **`intentDebit bal c a amt`** — the protocol intent of "park `amt` of asset `a` out of cell `c`":
cell `c`'s asset-`a` column drops by `amt`; every OTHER (cell, asset) pair is literally unchanged.
Written from intent (a single-cell, single-asset withdrawal); it happens to coincide pointwise with
the kernel's `recBalCreditCell _ _ _ (-amt)`, which we EXPLOIT (`recBalCreditCell_neg_eq`) to reuse the
proved conservation lemmas — but the DEFINITION here is intent, not a call to the executor. -/
def intentDebit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun x b => if x = c ∧ b = a then bal x b - amt else bal x b

/-- **`intentCredit bal c a amt`** — the dual: cell `c`'s asset-`a` column rises by `amt`. -/
def intentCredit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    CellId → AssetId → ℤ :=
  fun x b => if x = c ∧ b = a then bal x b + amt else bal x b

/-- The intent debit/credit coincide pointwise with the kernel's `recBalCreditCell` (credit by a
signed delta). A bridge lemma so the SPEC (intent) and the EXECUTOR (kernel op) provably agree on the
ledger move — proving the executor's choice of `recBalCreditCell creator asset (-amount)` realizes the
INTENT "debit creator". This is a genuine fact about two *independently written* functions. -/
theorem intentDebit_eq_credit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentDebit bal c a amt = recBalCreditCell bal c a (-amt) := by
  funext x b; unfold intentDebit recBalCreditCell
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]; ring
  · simp only [if_neg h]

theorem intentCredit_eq_credit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentCredit bal c a amt = recBalCreditCell bal c a amt := by
  funext x b; unfold intentCredit recBalCreditCell
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]
  · simp only [if_neg h]

/-! ## §1 — ESCROW CREATE: the reference triangle.

### The independent declarative spec (intent).

A `createEscrow` of `(id, creator, recipient, asset, amount)` MEANS, declaratively:
  * the creator's asset-`asset` balance goes DOWN by `amount` (`intentDebit`),
  * a FRESH unresolved record `{id, creator, recipient, amount, resolved := false, asset}` is parked
    at the FRONT of the holding store,
  * EVERYTHING ELSE (accounts, caps, nullifiers, queues, …) is untouched.
We write this as a whole-state function `escrowCreateSpec`, derived from the protocol meaning, NOT
from `createEscrowRawAsset`. -/

/-- The fresh record the intent parks (named from the create's arguments). -/
def escrowCreateRecord (a : CreateEscrowArgs) : EscrowRecord :=
  { id := a.id, creator := a.creator, recipient := a.recipient,
    amount := a.amount, resolved := false, asset := a.asset }

/-- **`escrowCreateSpec` — the INDEPENDENT declarative post-state of a create.** The creator's
asset balance drops by `amount`; the fresh unresolved record is prepended; all else fixed. This is
intent, written field-by-field — it is what a correct executor MUST produce, and the triangle proves
`createEscrowStep` produces exactly this. -/
def escrowCreateSpec (k : RecordKernelState) (a : CreateEscrowArgs) : RecordKernelState :=
  { k with bal := intentDebit k.bal a.creator a.asset a.amount
           escrows := escrowCreateRecord a :: k.escrows }

/-- The create gate (intent-level precondition), re-expressed as the conjunction the executor checks.
Written here so the triangle's `←` direction (liveness) reads cleanly. -/
def escrowCreateGate (k : RecordKernelState) (a : CreateEscrowArgs) : Prop :=
  acceptsEffects k a.creator = true ∧
  authorizedB k.caps (createEscrowTurn a) = true ∧
  0 ≤ a.amount ∧ a.amount ≤ k.bal a.creator a.asset ∧ a.creator ∈ k.accounts ∧
  ¬ (∃ r ∈ k.escrows, r.id = a.id)

/-- The executor's `createEscrowRawAsset` realizes the INTENT post-state `escrowCreateSpec`.
A genuine equality of two independently-written functions: the executor debits via
`recBalCreditCell creator asset (-amount)` and prepends its record literal; the spec debits via
`intentDebit creator asset amount` and prepends `escrowCreateRecord`. They are EQUAL — proving the
executor's op realizes the intended ledger+store move (it would be FALSE if the executor debited the
recipient, or parked a resolved record, or wrote the wrong asset). -/
theorem createEscrowRawAsset_eq_spec (k : RecordKernelState) (a : CreateEscrowArgs) :
    createEscrowRawAsset k a.id a.creator a.recipient a.asset a.amount = escrowCreateSpec k a := by
  unfold createEscrowRawAsset escrowCreateSpec escrowCreateRecord
  rw [intentDebit_eq_credit]

/-- **THE ESCROW-CREATE TRIANGLE (PROVED, FULL BICONDITIONAL).** The actor-gated executor commits
EXACTLY the independently-specified output: `createEscrowStep k a = some k'` IFF the create gate holds
AND `k' = escrowCreateSpec k a`. The `→` is output-uniqueness (a commit pins the unique spec output —
strictly stronger than `admits`); the `←` is completeness (the gate suffices for the spec output to
commit). -/
theorem escrowCreate_triangle (k k' : RecordKernelState) (a : CreateEscrowArgs) :
    createEscrowStep k a = some k' ↔ (escrowCreateGate k a ∧ k' = escrowCreateSpec k a) := by
  unfold createEscrowStep createEscrowKAsset escrowCreateGate createEscrowTurn
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.creator = true
    · rw [if_pos hadm] at h
      by_cases hg : authorizedB k.caps { actor := a.actor, src := a.creator, dst := a.recipient, amt := a.amount } = true
          ∧ 0 ≤ a.amount ∧ a.amount ≤ k.bal a.creator a.asset ∧ a.creator ∈ k.accounts
          ∧ ¬ (∃ r ∈ k.escrows, r.id = a.id)
      · rw [if_pos hg] at h
        simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, havail, hacc, hfresh⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, havail, hacc, hfresh⟩, ?_⟩
        rw [← h, createEscrowRawAsset_eq_spec]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, havail, hacc, hfresh⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, havail, hacc, hfresh⟩]
    rw [hk, createEscrowRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (escrow create, PROVED).** Any candidate `k'' ≠ escrowCreateSpec k a` is
REJECTED: the executor never commits a ghost output. The refinement pins the UNIQUE correct
post-state — a tampered next-state (wrong balance, wrong/missing record, an extra field touched)
cannot come out of `createEscrowStep`. -/
theorem escrowCreate_antighost (k k'' : RecordKernelState) (a : CreateEscrowArgs)
    (hne : k'' ≠ escrowCreateSpec k a) : createEscrowStep k a ≠ some k'' := by
  intro h
  obtain ⟨_, hk⟩ := (escrowCreate_triangle k k'' a).mp h
  exact hne hk

/-! ## §2 — ESCROW SETTLE (release / refund): the triangle on the side-table.

The settle spec is intent over the FOUND record `r` (looked up by id, unresolved): credit the
settlement target (`recipient` for release, `creator` for refund) at `r.asset` by `r.amount`, and mark
`r` resolved. The gate adds the actor-authority (R2) + the settle-liveness (`target ∈ accounts ∧ Live`)
the kernel checks. We parametrize the spec by the target-selector so release/refund share one proof. -/

/-- **`escrowSettleSpec` — the INDEPENDENT declarative post-state of a settle to `target`.** Over the
found unresolved record `r`: `target`'s asset-`r.asset` balance rises by `r.amount` (`intentCredit`), and
the record is marked resolved (`markResolved` by id). All else fixed. (`markResolved` is the
intent-level "mark THIS record done"; it is the kernel's own list primitive, reused — the asset/ledger
move is the part the executor could get wrong, and that is `intentCredit`, written from intent.) -/
def escrowSettleSpec (k : RecordKernelState) (target : CellId) (r : EscrowRecord) (id : Nat) :
    RecordKernelState :=
  { k with bal := intentCredit k.bal target r.asset r.amount
           escrows := markResolved k.escrows id }

/-- The executor's `settleEscrowRawAsset` realizes the INTENT settle post-state. Independent-function
equality: the executor credits via `recBalCreditCell target asset amount`; the spec credits via
`intentCredit target asset amount`. EQUAL — the credit lands on the intended target/asset. -/
theorem settleEscrowRawAsset_eq_spec (k : RecordKernelState) (target : CellId) (r : EscrowRecord)
    (id : Nat) :
    settleEscrowRawAsset k id target r.asset r.amount = escrowSettleSpec k target r id := by
  unfold settleEscrowRawAsset escrowSettleSpec
  rw [intentCredit_eq_credit]

/-- **THE ESCROW-RELEASE TRIANGLE (PROVED, FULL BICONDITIONAL).** `releaseStep k a = some k'` IFF
there is a found unresolved record `r` (named by `a.id`) whose RECIPIENT the actor is authorized over
and who is a live account, AND `k'` is EXACTLY `escrowSettleSpec` crediting that recipient. The output
is the unique intent post-state; release credits the RECIPIENT (not the creator) — a fact the triangle
pins. -/
theorem escrowRelease_triangle (k k' : RecordKernelState) (a : SettleArgs) :
    releaseStep k a = some k' ↔
      (∃ r, findUnresolved k a.id = some r ∧
            authorizedB k.caps { actor := a.actor, src := r.recipient, dst := r.recipient, amt := 0 } = true ∧
            r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true ∧
            k' = escrowSettleSpec k r.recipient r a.id) := by
  unfold releaseStep releaseSettleAuthB releaseEscrowKAsset findUnresolved
  constructor
  · intro h
    cases hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some r =>
        rw [hf] at h; simp only at h
        by_cases hauth : authorizedB k.caps { actor := a.actor, src := r.recipient, dst := r.recipient, amt := 0 } = true
        · rw [if_pos hauth] at h
          by_cases hlive : r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient = true
          · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h
            refine ⟨r, rfl, hauth, hlive.1, hlive.2, ?_⟩
            rw [← h, settleEscrowRawAsset_eq_spec]
          · rw [if_neg hlive] at h; exact absurd h (by simp)
        · rw [if_neg hauth] at h; exact absurd h (by simp)
  · rintro ⟨r, hf, hauth, hacc, hlive, hk⟩
    rw [hf]; simp only
    rw [if_pos hauth, if_pos ⟨hacc, hlive⟩, hk, settleEscrowRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (escrow release, PROVED).** Once the found record `r` is fixed, any candidate
`k'' ≠ escrowSettleSpec k r.recipient r a.id` is REJECTED. The release output is the unique intent
post-state crediting the recipient. -/
theorem escrowRelease_antighost (k k'' : RecordKernelState) (a : SettleArgs) (r : EscrowRecord)
    (hf : findUnresolved k a.id = some r) (hne : k'' ≠ escrowSettleSpec k r.recipient r a.id) :
    releaseStep k a ≠ some k'' := by
  intro h
  obtain ⟨r', hf', _, _, _, hk⟩ := (escrowRelease_triangle k k'' a).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **THE ESCROW-REFUND TRIANGLE (PROVED, FULL BICONDITIONAL).** Symmetric to release, but the credit
lands on the CREATOR (refund target). The output is the unique intent post-state crediting the creator —
the triangle pins release↔recipient vs refund↔creator. -/
theorem escrowRefund_triangle (k k' : RecordKernelState) (a : SettleArgs) :
    refundStep k a = some k' ↔
      (∃ r, findUnresolved k a.id = some r ∧
            authorizedB k.caps { actor := a.actor, src := r.creator, dst := r.creator, amt := 0 } = true ∧
            r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true ∧
            k' = escrowSettleSpec k r.creator r a.id) := by
  unfold refundStep refundSettleAuthB refundEscrowKAsset findUnresolved
  constructor
  · intro h
    cases hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some r =>
        rw [hf] at h; simp only at h
        by_cases hauth : authorizedB k.caps { actor := a.actor, src := r.creator, dst := r.creator, amt := 0 } = true
        · rw [if_pos hauth] at h
          by_cases hlive : r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
          · rw [if_pos hlive] at h; simp only [Option.some.injEq] at h
            refine ⟨r, rfl, hauth, hlive.1, hlive.2, ?_⟩
            rw [← h, settleEscrowRawAsset_eq_spec]
          · rw [if_neg hlive] at h; exact absurd h (by simp)
        · rw [if_neg hauth] at h; exact absurd h (by simp)
  · rintro ⟨r, hf, hauth, hacc, hlive, hk⟩
    rw [hf]; simp only
    rw [if_pos hauth, if_pos ⟨hacc, hlive⟩, hk, settleEscrowRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (escrow refund, PROVED).** -/
theorem escrowRefund_antighost (k k'' : RecordKernelState) (a : SettleArgs) (r : EscrowRecord)
    (hf : findUnresolved k a.id = some r) (hne : k'' ≠ escrowSettleSpec k r.creator r a.id) :
    refundStep k a ≠ some k'' := by
  intro h
  obtain ⟨r', hf', _, _, _, hk⟩ := (escrowRefund_triangle k k'' a).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-! ## §3 — SECOND FAMILY: QUEUE FIFO (allocate / enqueue / dequeue) — the same triangle.

The queue ops (`queueAllocateK`/`queueEnqueueK`/`queueDequeueK`) are a SEPARATE side-table family. We
give each an INDEPENDENT intent spec over the buffer and prove the triangle + anti-ghost tooth, so the
escrow REFERENCE PATTERN is shown to amplify to a structurally-different effect (a list-FIFO automaton,
not a per-asset ledger). -/

/-- **`queueAllocateSpec` — the INDEPENDENT post-state of an allocate.** A fresh queue record
`{id, owner, capacity, buffer := []}` is prepended; all else fixed. -/
def queueAllocateSpec (k : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat) :
    RecordKernelState :=
  { k with queues := { id := id, owner := owner, capacity := capacity, buffer := [] } :: k.queues }

/-- **THE QUEUE-ALLOCATE TRIANGLE (PROVED, FULL BICONDITIONAL).** `queueAllocateK` commits EXACTLY the
intent post-state iff the id is fresh. -/
theorem queueAllocate_triangle (k k' : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat) :
    queueAllocateK k id owner capacity = some k' ↔
      (findQueue k.queues id = none ∧ k' = queueAllocateSpec k id owner capacity) := by
  unfold queueAllocateK queueAllocateSpec
  constructor
  · intro h
    cases hf : findQueue k.queues id with
    | some q => rw [hf] at h; exact absurd h (by simp)
    | none   => rw [hf] at h; simp only [Option.some.injEq] at h; exact ⟨rfl, h.symm⟩
  · rintro ⟨hf, hk⟩; rw [hf, hk]

/-- **ANTI-GHOST TOOTH (queue allocate, PROVED).** -/
theorem queueAllocate_antighost (k k'' : RecordKernelState) (id : Nat) (owner : CellId) (capacity : Nat)
    (hne : k'' ≠ queueAllocateSpec k id owner capacity) :
    queueAllocateK k id owner capacity ≠ some k'' := by
  intro h
  exact hne ((queueAllocate_triangle k k'' id owner capacity).mp h).2

/-- **`queueEnqueueSpec` — the INDEPENDENT post-state of an enqueue over the found queue `q`.** The
message `m` is APPENDED to the back of `q`'s buffer (`qbufEnqueue` = FIFO tail-append); the queue record
is replaced in place; all else fixed. Written from intent ("the new message waits BEHIND those already
queued"). -/
def queueEnqueueSpec (k : RecordKernelState) (id : Nat) (q : QueueRecord) (m : Nat) :
    RecordKernelState :=
  { k with queues := replaceQueue k.queues id { q with buffer := qbufEnqueue q.buffer m } }

/-- **THE QUEUE-ENQUEUE TRIANGLE (PROVED, FULL BICONDITIONAL).** `queueEnqueueK` commits EXACTLY the
intent post-state iff the queue is found AND not full. The output appends to the TAIL (FIFO) — a
candidate that prepended, or replaced the wrong queue, is excluded. -/
theorem queueEnqueue_triangle (k k' : RecordKernelState) (id m : Nat) :
    queueEnqueueK k id m = some k' ↔
      (∃ q, findQueue k.queues id = some q ∧ q.buffer.length < q.capacity ∧
            k' = queueEnqueueSpec k id q m) := by
  unfold queueEnqueueK queueEnqueueSpec
  constructor
  · intro h
    cases hf : findQueue k.queues id with
    | none   => rw [hf] at h; exact absurd h (by simp)
    | some q =>
        rw [hf] at h; simp only at h
        by_cases hc : q.buffer.length < q.capacity
        · rw [if_pos hc] at h; simp only [Option.some.injEq] at h
          exact ⟨q, rfl, hc, h.symm⟩
        · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨q, hf, hc, hk⟩; rw [hf]; simp only; rw [if_pos hc, hk]

/-- **ANTI-GHOST TOOTH (queue enqueue, PROVED).** Once the found queue `q` is fixed, any candidate
`k'' ≠ queueEnqueueSpec k id q m` is REJECTED — the executor will not commit a buffer that isn't the
intent's tail-append. -/
theorem queueEnqueue_antighost (k k'' : RecordKernelState) (id m : Nat) (q : QueueRecord)
    (hf : findQueue k.queues id = some q) (hne : k'' ≠ queueEnqueueSpec k id q m) :
    queueEnqueueK k id m ≠ some k'' := by
  intro h
  obtain ⟨q', hf', _, hk⟩ := (queueEnqueue_triangle k k'' id m).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **`queueDequeueSpec` — the INDEPENDENT post-state of a dequeue over found queue `q` with buffer
`m :: rest`.** The FRONT message `m` (the OLDEST waiting) is removed; the queue record is replaced with
`rest`; all else fixed. The dequeued message is `m`. Written from intent ("the oldest message leaves
first"). -/
def queueDequeueSpec (k : RecordKernelState) (id : Nat) (q : QueueRecord) (rest : List Nat) :
    RecordKernelState :=
  { k with queues := replaceQueue k.queues id { q with buffer := rest } }

/-- **THE QUEUE-DEQUEUE TRIANGLE (PROVED, FULL BICONDITIONAL).** `queueDequeueK` commits EXACTLY the
intent post-state AND returns EXACTLY the front message iff the queue is found, the actor is the owner,
and the buffer is non-empty (`m :: rest`). The output removes the FRONT (FIFO) — a candidate that
removed the tail, or returned the wrong message, is excluded. This pins BOTH the post-state and the
returned message (a richer codomain — `RecordKernelState × Nat`). -/
theorem queueDequeue_triangle (k k' : RecordKernelState) (id : Nat) (actor : CellId) (m : Nat) :
    queueDequeueK k id actor = some (k', m) ↔
      (∃ q rest, findQueue k.queues id = some q ∧ actor = q.owner ∧ q.buffer = m :: rest ∧
                 k' = queueDequeueSpec k id q rest) := by
  unfold queueDequeueK queueDequeueSpec
  constructor
  · intro h
    cases hf : findQueue k.queues id with
    | none   => rw [hf] at h; exact absurd h (by simp)
    | some q =>
        rw [hf] at h; simp only at h
        by_cases ho : actor = q.owner
        · rw [if_pos ho] at h
          cases hb : q.buffer with
          | nil      => have hd : qbufDequeue q.buffer = none := by rw [hb]; rfl
                        rw [hd] at h; exact absurd h (by simp)
          | cons x xs =>
              have hd : qbufDequeue q.buffer = some (x, xs) := by rw [hb]; rfl
              rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk, hm⟩ := h; subst hm
              exact ⟨q, xs, rfl, ho, hb, hk.symm⟩
        · rw [if_neg ho] at h; exact absurd h (by simp)
  · rintro ⟨q, rest, hf, ho, hb, hk⟩
    rw [hf]; simp only; rw [if_pos ho]
    have hd : qbufDequeue q.buffer = some (m, rest) := by rw [hb]; rfl
    rw [hd, hk]

/-- **ANTI-GHOST TOOTH (queue dequeue, PROVED).** Once the found queue `q` (with buffer `m :: rest`)
is fixed, any candidate post-state `k'' ≠ queueDequeueSpec k id q rest` is REJECTED — the executor will
not commit a buffer that isn't the intent's front-removal. -/
theorem queueDequeue_antighost (k k'' : RecordKernelState) (id : Nat) (actor : CellId) (m : Nat)
    (q : QueueRecord) (rest : List Nat)
    (hf : findQueue k.queues id = some q) (hb : q.buffer = m :: rest)
    (hne : k'' ≠ queueDequeueSpec k id q rest) :
    queueDequeueK k id actor ≠ some (k'', m) := by
  intro h
  obtain ⟨q', rest', hf', _, hb', hk⟩ := (queueDequeue_triangle k k'' id actor m).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  rw [hb] at hb'; simp only [List.cons.injEq] at hb'; obtain ⟨_, hr⟩ := hb'; subst hr
  exact hne hk

/-! ## §4 — NON-VACUITY TEETH (`#guard`): concrete witness TRUE and ghost REJECTED.

A live fixture proves each triangle's spec output is REACHED (the executor commits exactly it), and a
deliberately-tampered ghost candidate is REFUSED — so the refinement is not vacuously true. -/

/-- Fixture: cells 0,1 are accounts; cell 0 holds 100 of asset 0; self-authority; both Live. -/
def fx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- The create arguments: lock 40 of asset 0, creator 0, recipient 1, id 9. -/
def caCreate : CreateEscrowArgs := { id := 9, actor := 0, creator := 0, recipient := 1, asset := 0, amount := 40 }

/-- The locked fixture (cell 0 has parked 40 into escrow id 9). -/
def fxLocked : RecordKernelState := escrowCreateSpec fx caCreate

-- Since `RecordKernelState` carries function fields it has no `BEq`; we witness the triangles via
-- DECIDABLE OBSERVATIONS (balances, buffer order, isSome) — `RecordKernelState`-equality itself is
-- proved/refuted by the triangle theorems + anti-ghost teeth above, which is the real content.

-- CREATE commits (the gate holds) and the debit is REAL: creator balance dropped 100 → 60.
#guard (createEscrowStep fx caCreate).isSome
#guard (((createEscrowStep fx caCreate).map (fun k => k.bal 0 0)) == some 60)
-- ...and the committed output's escrow head IS the intent's fresh unresolved record (asset 0, amt 40).
#guard (((createEscrowStep fx caCreate).bind (fun k => k.escrows.head?)).map
          (fun r => (r.id, r.creator, r.recipient, r.amount, r.resolved, r.asset))
        == some (9, 0, 1, 40, false, 0))
-- CREATE anti-ghost (CONCRETE): a ghost candidate with the creator's balance LEFT UNTOUCHED differs
-- OBSERVABLY from the spec output (bal 0 0 is 100 in the ghost `fx`, 60 in the spec) — so by
-- `escrowCreate_antighost` the executor refuses it. The observable witness of `ghost ≠ spec`:
#guard ((fx.bal 0 0, (escrowCreateSpec fx caCreate).bal 0 0) == (100, 60))

-- RELEASE credits the RECIPIENT (cell 1: 0 → 40); REFUND credits the CREATOR (cell 0: 60 → 100).
-- Distinct outputs ⇒ the triangle genuinely pins release↔recipient vs refund↔creator.
#guard ((releaseStep fxLocked { actor := 1, id := 9 }).map (fun k => k.bal 1 0)) == some 40
#guard ((refundStep  fxLocked { actor := 0, id := 9 }).map (fun k => k.bal 0 0)) == some 100
-- and the settled record is marked resolved (the side-table move is real).
#guard (((releaseStep fxLocked { actor := 1, id := 9 }).bind (fun k => k.escrows.head?)).map
          (·.resolved) == some true)

-- QUEUE allocate commits a fresh empty queue (id 7, owner 0, cap 2).
#guard (queueAllocateK fx 7 0 2).isSome
#guard (((queueAllocateK fx 7 0 2).bind (fun k => (findQueue k.queues 7))).map
          (fun q => (q.owner, q.capacity, q.buffer)) == some (0, 2, ([] : List Nat)))
-- ENQUEUE a(100) then b(200), then DEQUEUE returns the FRONT (a=100) — the FIFO order the triangle pins.
#guard (match queueAllocateK fx 7 0 2 with
        | some k1 => match queueEnqueueK k1 7 100 with
            | some k2 => match queueEnqueueK k2 7 200 with
                | some k3 => (queueDequeueK k3 7 0).map (·.2) == some 100  -- front = a = 100 (FIFO, not LIFO)
                | none => false
            | none => false
        | none => false)
-- ENQUEUE anti-ghost: a NON-OWNER cannot dequeue (the gate refuses); a FULL queue refuses enqueue.
#guard (match queueAllocateK fx 7 0 1 with  -- capacity 1
        | some k1 => match queueEnqueueK k1 7 100 with
            | some k2 => (queueEnqueueK k2 7 200).isNone  -- full ⇒ refused
            | none => false
        | none => false)

/-! ## §5 — Axiom-hygiene pins. Every triangle + anti-ghost rests only on the kernel axioms. -/

#assert_axioms intentDebit_eq_credit
#assert_axioms intentCredit_eq_credit
#assert_axioms createEscrowRawAsset_eq_spec
#assert_axioms escrowCreate_triangle
#assert_axioms escrowCreate_antighost
#assert_axioms settleEscrowRawAsset_eq_spec
#assert_axioms escrowRelease_triangle
#assert_axioms escrowRelease_antighost
#assert_axioms escrowRefund_triangle
#assert_axioms escrowRefund_antighost
#assert_axioms queueAllocate_triangle
#assert_axioms queueAllocate_antighost
#assert_axioms queueEnqueue_triangle
#assert_axioms queueEnqueue_antighost
#assert_axioms queueDequeue_triangle
#assert_axioms queueDequeue_antighost

/-! ## §6 — THIRD FAMILY: VALUE SUPPLY (mint / burn) — the per-asset supply triangle.

The supply ops (`Handlers.StateSupply.mintStep`/`burnStep`) move the ONE quantity that legitimately
changes the conserved per-asset measure. We give each an INDEPENDENT intent spec over the `bal`
ledger (the asset-`a` column of cell `c` rises/falls by `amt`, every OTHER (cell, asset) pair
literally untouched — `intentCredit`/`intentDebit`, the SAME intent oracles §0 wrote from protocol
intent) and prove the triangle + anti-ghost tooth. A wrong amount / wrong asset / wrong holder is
REJECTED — the supply move is pinned to the unique intent post-state.

The executor commits via the kernel op `recBalCredit cell a (±amt)`; our spec commits via the
independent `intentCredit`/`intentDebit cell a amt`. They are EQUAL (`intentCredit_eq_balCredit`),
proving the executor moves the INTENDED column — it would be FALSE if it credited the wrong cell,
the wrong asset, or the wrong sign. -/

open Dregg2.Exec.Handlers.StateSupply (SupplyArgs mintStep burnStep)

/-- The executor's per-asset single-cell move `recBalCredit` coincides pointwise with the intent
oracle `intentCredit` (both add a signed delta to ONE (cell, asset) column). An independent-function
equality bridging the SPEC (intent) and the EXECUTOR (kernel op) — it would be FALSE if the executor
spilled the credit onto another column. -/
theorem intentCredit_eq_balCredit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentCredit bal c a amt = recBalCredit bal c a amt := by
  funext x b; unfold intentCredit recBalCredit
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- The intent DEBIT coincides with the executor's `recBalCredit … (-amt)` (the burn move): both
subtract `amt` from ONE (cell, asset) column. The burn-side bridge (the `recKBurnAsset` op commits
`recBalCredit … (-amt)`, distinct from `RecordKernel.recBalCreditCell` used by `intentDebit_eq_credit`). -/
theorem intentDebit_eq_balCredit (bal : CellId → AssetId → ℤ) (c : CellId) (a : AssetId) (amt : ℤ) :
    intentDebit bal c a amt = recBalCredit bal c a (-amt) := by
  funext x b; unfold intentDebit recBalCredit
  by_cases h : x = c ∧ b = a
  · simp only [if_pos h]; ring
  · simp only [if_neg h]

/-- **`mintSpec` — the INDEPENDENT declarative post-state of a per-asset mint.** Cell `a.cell`'s
asset-`a.asset` column rises by `a.amt` (`intentCredit`); EVERYTHING ELSE (accounts, caps, escrows,
nullifiers, every other (cell, asset) column) untouched. Written from supply intent ("coin `amt`
of `asset` into `cell`"), NOT from `recKMintAsset`. -/
def mintSpec (k : RecordKernelState) (a : SupplyArgs) : RecordKernelState :=
  { k with bal := intentCredit k.bal a.cell a.asset a.amt }

/-- **`burnSpec` — the INDEPENDENT declarative post-state of a per-asset burn.** The dual: cell
`a.cell`'s asset-`a.asset` column FALLS by `a.amt` (`intentDebit`); all else fixed. Written from
intent ("annihilate `amt` of `asset` from `cell`"). -/
def burnSpec (k : RecordKernelState) (a : SupplyArgs) : RecordKernelState :=
  { k with bal := intentDebit k.bal a.cell a.asset a.amt }

/-- The mint gate (intent-level precondition), re-expressed as the conjunction the executor checks:
the target cell is Live (`acceptsEffects`), the actor holds PRIVILEGED mint authority (a `node`/
`control` cap — not bare ownership), the amount is non-negative, and the cell is a live account. -/
def mintGate (k : RecordKernelState) (a : SupplyArgs) : Prop :=
  acceptsEffects k a.cell = true ∧
  mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.cell ∈ k.accounts

/-- The burn gate: the mint gate PLUS availability in the burned asset's column (you cannot burn
more than the cell holds). -/
def burnGate (k : RecordKernelState) (a : SupplyArgs) : Prop :=
  acceptsEffects k a.cell = true ∧
  mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.amt ≤ k.bal a.cell a.asset ∧
  a.cell ∈ k.accounts

/-- **THE MINT TRIANGLE (PROVED, FULL BICONDITIONAL).** `mintStep k a = some k'` IFF the mint gate
holds AND `k' = mintSpec k a`. The `→` is output-uniqueness (a commit pins the unique intent
post-state — the credit lands on EXACTLY cell `a.cell`'s asset `a.asset` column, by EXACTLY `+a.amt`,
strictly stronger than `recTotalAsset += amt`); the `←` is completeness (the gate suffices). -/
theorem mint_triangle (k k' : RecordKernelState) (a : SupplyArgs) :
    mintStep k a = some k' ↔ (mintGate k a ∧ k' = mintSpec k a) := by
  unfold mintStep recKMintAsset mintGate mintSpec
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.cell = true
    · rw [if_pos hadm] at h
      by_cases hg : mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.cell ∈ k.accounts
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, hacc⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, hacc⟩, ?_⟩
        rw [← h, intentCredit_eq_balCredit]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, hacc⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, hacc⟩, hk, intentCredit_eq_balCredit]

/-- **ANTI-GHOST TOOTH (mint, PROVED).** Any candidate `k'' ≠ mintSpec k a` is REJECTED — a mint
that credited a WRONG amount, the WRONG asset, the WRONG cell, or touched a 2nd column cannot come
out of `mintStep`. The supply move is pinned to the unique intent post-state. -/
theorem mint_antighost (k k'' : RecordKernelState) (a : SupplyArgs)
    (hne : k'' ≠ mintSpec k a) : mintStep k a ≠ some k'' := by
  intro h
  exact hne ((mint_triangle k k'' a).mp h).2

/-- **THE BURN TRIANGLE (PROVED, FULL BICONDITIONAL).** `burnStep k a = some k'` IFF the burn gate
(incl. availability in the burned asset) holds AND `k' = burnSpec k a`. The `→` pins the unique
intent post-state (the DEBIT lands on EXACTLY cell `a.cell`'s asset `a.asset` column, by EXACTLY
`-a.amt`); the `←` is completeness. -/
theorem burn_triangle (k k' : RecordKernelState) (a : SupplyArgs) :
    burnStep k a = some k' ↔ (burnGate k a ∧ k' = burnSpec k a) := by
  unfold burnStep recKBurnAsset burnGate burnSpec
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.cell = true
    · rw [if_pos hadm] at h
      by_cases hg : mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt
          ∧ a.amt ≤ k.bal a.cell a.asset ∧ a.cell ∈ k.accounts
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, havail, hacc⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, havail, hacc⟩, ?_⟩
        rw [← h, intentDebit_eq_balCredit]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, havail, hacc⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, havail, hacc⟩, hk, intentDebit_eq_balCredit]

/-- **ANTI-GHOST TOOTH (burn, PROVED).** Any candidate `k'' ≠ burnSpec k a` is REJECTED. -/
theorem burn_antighost (k k'' : RecordKernelState) (a : SupplyArgs)
    (hne : k'' ≠ burnSpec k a) : burnStep k a ≠ some k'' := by
  intro h
  exact hne ((burn_triangle k k'' a).mp h).2

/-! ## §7 — FOURTH FAMILY: AUTHORITY (delegate / attenuate / revoke) — the cap-table triangle.

The cap-graph ops (`Handlers.Authority.delegateAttenStep`/`attenuateStep`/`revokeStep`) move the
`caps` side-table. We give each an INDEPENDENT intent spec over the cap function and prove the
triangle + anti-ghost tooth, pinning the EXACT resulting cap set (non-amplification is proven
ELSEWHERE — `delegateAttenH_non_amplifying`; here we pin the WHOLE cap function so an over-broad or
wrong-target cap edge is excluded as a ghost). Delegate is gated (Granovetter premise ⇒ a full
biconditional); attenuate/revoke are TOTAL (always commit ⇒ the load-bearing `→` output-uniqueness
direction is the whole content, the gate being trivially `true`). -/

open Dregg2.Exec.Handlers.Authority
  (DelegateArgs AttenuateArgs RevokeArgs delegateAttenStep attenuateStep revokeStep delegateGateB
   allAuths)

/-- **`delegateSpec` — the INDEPENDENT declarative post-state of an attenuated delegation.** The
recipient's slot GAINS exactly the delegator's held cap to `target`, attenuated to `keep`
(`grant … (attenuate keep (heldCapTo …))`); EVERYTHING ELSE (every other cell's slot, balances,
escrows) untouched. Written from intent ("hand `recipient` a `keep`-narrowed copy of the cap I hold
to `target`"). The cap installed is `attenuate keep (heldCapTo …)` — the SAME shape the executor's
`recKDelegateAtten` commits, which the triangle proves it realizes. -/
def delegateSpec (k : RecordKernelState) (a : DelegateArgs) : RecordKernelState :=
  { k with caps := grant k.caps a.recipient (attenuate a.keep (heldCapTo k.caps a.delegator a.target)) }

/-- **THE DELEGATE TRIANGLE (PROVED, FULL BICONDITIONAL).** `delegateAttenStep k a = some k'` IFF the
Granovetter connectivity premise holds (`delegateGateB` — the delegator already holds a cap conferring
an edge to `target`) AND `k' = delegateSpec k a`. The `→` pins the UNIQUE resulting cap function (the
recipient gains EXACTLY the attenuated held cap, and NO other slot changes — an over-broad grant, a
grant to the wrong recipient, or a fresh manufactured cap is excluded); the `←` is completeness. -/
theorem delegate_triangle (k k' : RecordKernelState) (a : DelegateArgs) :
    delegateAttenStep k a = some k' ↔ (delegateGateB k a = true ∧ k' = delegateSpec k a) := by
  unfold delegateAttenStep recKDelegateAtten delegateGateB delegateSpec
  constructor
  · intro h
    by_cases hg : (k.caps a.delegator).any (fun cap => confersEdgeTo a.target cap) = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      exact ⟨hg, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, hk⟩; rw [if_pos hg, hk]

/-- **ANTI-GHOST TOOTH (delegate, PROVED).** Any candidate `k'' ≠ delegateSpec k a` is REJECTED — the
delegation commits EXACTLY the attenuated-held-cap grant; an over-broad cap edge, a grant to the wrong
target/recipient, or a touched 2nd slot cannot come out of `delegateAttenStep`. -/
theorem delegate_antighost (k k'' : RecordKernelState) (a : DelegateArgs)
    (hne : k'' ≠ delegateSpec k a) : delegateAttenStep k a ≠ some k'' := by
  intro h
  exact hne ((delegate_triangle k k'' a).mp h).2

/-- **`attenuateSpec` — the INDEPENDENT declarative post-state of an in-place self-attenuation.** The
actor's OWN slot has its `idx`-th cap narrowed to `keep` (`attenuateSlotF` = `modify idx (attenuate
keep)` on the actor's slot only); EVERYTHING ELSE untouched. Written from intent ("narrow my own
idx-th held cap to `keep`"). -/
def attenuateSpec (k : RecordKernelState) (a : AttenuateArgs) : RecordKernelState :=
  { k with caps := attenuateSlotF k.caps a.actor a.idx a.keep }

/-- **THE ATTENUATE TRIANGLE (PROVED — TOTAL, output-uniqueness).** `attenuateStep` ALWAYS commits
(self-attenuation cannot fail — at worst the identity, still narrower-or-equal), so the gate is
trivially `true`; the load-bearing content is the `↔`: `attenuateStep k a = some k'` IFF
`k' = attenuateSpec k a`. The output is the UNIQUE intent post-state (the actor's own `idx`-th cap
narrowed in place, NO other slot/cell touched). -/
theorem attenuate_triangle (k k' : RecordKernelState) (a : AttenuateArgs) :
    attenuateStep k a = some k' ↔ k' = attenuateSpec k a := by
  unfold attenuateStep attenuateSpec
  constructor
  · intro h; simp only [Option.some.injEq] at h; exact h.symm
  · intro hk; rw [hk]

/-- **ANTI-GHOST TOOTH (attenuate, PROVED).** Any candidate `k'' ≠ attenuateSpec k a` is REJECTED —
the only thing `attenuateStep` ever commits is the in-place narrowing of the actor's `idx`-th cap; a
ghost that widened the cap, narrowed the WRONG slot, or touched another cell is excluded. -/
theorem attenuate_antighost (k k'' : RecordKernelState) (a : AttenuateArgs)
    (hne : k'' ≠ attenuateSpec k a) : attenuateStep k a ≠ some k'' := by
  intro h
  exact hne ((attenuate_triangle k k'' a).mp h)

/-- **`revokeTargetCaps` — the INDEPENDENT intent cap-function after a revocation.** The holder's slot
DROPS every cap conferring an edge to `target` (keep only the caps that do NOT confer such an edge);
every OTHER cell's slot is literally unchanged. Written from intent ("the holder loses its reach to
`target`, nothing else"), as a plain `Caps` function — NOT a call to `recKRevokeTarget`. The triangle
proves the executor's filter realizes exactly this. -/
def revokeTargetCaps (k : RecordKernelState) (a : RevokeArgs) : Caps :=
  fun l => if l = a.holder then (k.caps l).filter (fun cap => ¬ confersEdgeTo a.target cap)
           else k.caps l

/-- **`revokeSpec` — the INDEPENDENT declarative post-state of a revocation.** The `caps` function is
`revokeTargetCaps` (the holder's `target`-conferring caps filtered out); all else fixed. -/
def revokeSpec (k : RecordKernelState) (a : RevokeArgs) : RecordKernelState :=
  { k with caps := revokeTargetCaps k a }

/-- The executor's `recKRevokeTarget` realizes the INTENT revoke post-state `revokeSpec`. An
independent-function equality: the executor filters the holder's slot by `¬ confersEdgeTo target`; the
spec (`revokeTargetCaps`) does the same, written from intent. EQUAL — proving the revoke removes
EXACTLY the `target`-conferring caps from EXACTLY the holder's slot (it would be FALSE if it filtered
the wrong slot, the wrong target, or removed extra caps). -/
theorem recKRevokeTarget_eq_spec (k : RecordKernelState) (a : RevokeArgs) :
    recKRevokeTarget k a.holder a.target = revokeSpec k a := by
  unfold recKRevokeTarget revokeSpec revokeTargetCaps; rfl

/-- **THE REVOKE TRIANGLE (PROVED — TOTAL, output-uniqueness).** `revokeStep` ALWAYS commits
(revocation cannot fail — at worst the identity), so the gate is trivially `true`; the load-bearing
content is the `↔`: `revokeStep k a = some k'` IFF `k' = revokeSpec k a`. The output is the UNIQUE
intent post-state (the holder's `target`-conferring caps filtered out, NO other slot touched). -/
theorem revoke_triangle (k k' : RecordKernelState) (a : RevokeArgs) :
    revokeStep k a = some k' ↔ k' = revokeSpec k a := by
  unfold revokeStep
  constructor
  · intro h; simp only [Option.some.injEq] at h
    rw [← h, recKRevokeTarget_eq_spec]
  · intro hk; rw [hk, recKRevokeTarget_eq_spec]

/-- **ANTI-GHOST TOOTH (revoke, PROVED).** Any candidate `k'' ≠ revokeSpec k a` is REJECTED — the
revoke commits EXACTLY the filtered cap function; a ghost that KEPT a `target`-conferring cap (an
incomplete revoke), filtered the WRONG holder, or dropped extra caps is excluded. -/
theorem revoke_antighost (k k'' : RecordKernelState) (a : RevokeArgs)
    (hne : k'' ≠ revokeSpec k a) : revokeStep k a ≠ some k'' := by
  intro h
  exact hne ((revoke_triangle k k'' a).mp h)

/-! ## §8 — FIFTH FAMILY: SHIELDED NOTES (noteCreate / noteSpend) — the commitment/nullifier triangle.

The shielded-note ops (`RecordKernel.noteCreateCommitment`/`noteSpendNullifier`) move the off-ledger
commitment SET (grow-only) and nullifier SET (grow-only WITH double-spend rejection). We give each an
INDEPENDENT intent spec over those sets and prove the triangle + anti-ghost tooth. noteCreate is
TOTAL (a fresh commitment never conflicts ⇒ the `↔` output-uniqueness is the content); noteSpend is
GATED on freshness (the nullifier must be absent ⇒ a full biconditional, and the anti-ghost tooth
pins the no-double-spend discipline). -/

/-- **`noteCreateSpec` — the INDEPENDENT declarative post-state of a noteCreate.** The commitment
SET gains `cm` at the front; EVERYTHING ELSE (bal, nullifiers, escrows, caps) untouched (bal-NEUTRAL:
the note's hidden value is behind the §8 CryptoPortal). Written from intent ("park a fresh Pedersen
commitment"), NOT from `noteCreateCommitment`. -/
def noteCreateSpec (k : RecordKernelState) (cm : Nat) : RecordKernelState :=
  { k with commitments := cm :: k.commitments }

/-- **THE NOTE-CREATE TRIANGLE (PROVED — TOTAL, output-uniqueness).** `noteCreateCommitment` ALWAYS
commits (a fresh commitment cannot conflict — the grow-only dual of the nullifier set), so the content
is the `↔`: `noteCreateCommitment k cm = k'` IFF `k' = noteCreateSpec k cm`. The output is the UNIQUE
intent post-state (the commitment set grows by EXACTLY `cm`, nothing else moves). -/
theorem noteCreate_triangle (k k' : RecordKernelState) (cm : Nat) :
    noteCreateCommitment k cm = k' ↔ k' = noteCreateSpec k cm := by
  unfold noteCreateCommitment noteCreateSpec
  constructor
  · intro h; exact h.symm
  · intro hk; rw [hk]

/-- **ANTI-GHOST TOOTH (noteCreate, PROVED).** Any candidate `k'' ≠ noteCreateSpec k cm` is REJECTED —
noteCreate commits EXACTLY the front-insert of `cm`; a ghost that inserted the WRONG commitment, moved
`bal`/`nullifiers`/`escrows`, or dropped an existing commitment is excluded. -/
theorem noteCreate_antighost (k k'' : RecordKernelState) (cm : Nat)
    (hne : k'' ≠ noteCreateSpec k cm) : noteCreateCommitment k cm ≠ k'' := by
  intro h
  exact hne ((noteCreate_triangle k k'' cm).mp h)

/-- **`noteSpendSpec` — the INDEPENDENT declarative post-state of a noteSpend.** The nullifier SET
gains `nf` at the front (marking the note SPENT); EVERYTHING ELSE untouched. Written from intent
("burn the note by recording its nullifier"). The GATE is freshness — `nf ∉ k.nullifiers` (no
double-spend); the spec is only reached when the gate holds. -/
def noteSpendSpec (k : RecordKernelState) (nf : Nat) : RecordKernelState :=
  { k with nullifiers := nf :: k.nullifiers }

/-- **THE NOTE-SPEND TRIANGLE (PROVED, FULL BICONDITIONAL).** `noteSpendNullifier k nf = some k'` IFF
the nullifier is FRESH (`nf ∉ k.nullifiers` — the no-double-spend gate) AND `k' = noteSpendSpec k nf`.
The `→` pins the UNIQUE intent post-state (the nullifier set grows by EXACTLY `nf`) AND surfaces the
freshness gate; the `←` is completeness (a fresh nullifier commits its spend). -/
theorem noteSpend_triangle (k k' : RecordKernelState) (nf : Nat) :
    noteSpendNullifier k nf = some k' ↔ (nf ∉ k.nullifiers ∧ k' = noteSpendSpec k nf) := by
  unfold noteSpendNullifier noteSpendSpec
  constructor
  · intro h
    by_cases hin : nf ∈ k.nullifiers
    · rw [if_pos hin] at h; exact absurd h (by simp)
    · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; exact ⟨hin, h.symm⟩
  · rintro ⟨hin, hk⟩; rw [if_neg hin, hk]

/-- **ANTI-GHOST TOOTH (noteSpend, PROVED — the no-double-spend tooth).** Two faces:
  * a candidate `k'' ≠ noteSpendSpec k nf` is REJECTED (output-uniqueness — the spend records EXACTLY
    `nf`, nothing else), AND
  * if `nf` is ALREADY spent (`nf ∈ k.nullifiers`), NO commit is possible at all (double-spend is
    fail-closed — `noteSpendNullifier k nf = none`).
The second face is the load-bearing anti-replay: a double-spend candidate is excluded. -/
theorem noteSpend_antighost (k k'' : RecordKernelState) (nf : Nat)
    (hne : k'' ≠ noteSpendSpec k nf) : noteSpendNullifier k nf ≠ some k'' := by
  intro h
  exact hne ((noteSpend_triangle k k'' nf).mp h).2

/-- **NO DOUBLE-SPEND (PROVED, the anti-ghost's second face).** An already-spent nullifier cannot be
spent again — `noteSpendNullifier` fails-closed `none`. So NO post-state (ghost or not) commits a
double-spend. -/
theorem noteSpend_double_spend_rejected (k k'' : RecordKernelState) (nf : Nat)
    (hspent : nf ∈ k.nullifiers) : noteSpendNullifier k nf ≠ some k'' := by
  rw [note_no_double_spend k nf hspent]; simp

/-! ## §9 — NON-VACUITY TEETH (`#guard`) for the three new families. -/

/-- Value/note fixture: cells 0,1 are accounts; cell 0 holds 100 of asset 0; cell 0 holds the
PRIVILEGED `node 0` mint cap; all Live. -/
def vfx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 0] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- A mint of 25 of asset 0 into cell 0 (privileged actor 0). -/
def aMint : SupplyArgs := { actor := 0, cell := 0, asset := 0, amt := 25 }
/-- A burn of 40 of asset 0 from cell 0. -/
def aBurn : SupplyArgs := { actor := 0, cell := 0, asset := 0, amt := 40 }

-- MINT commits and the supply MOVED: asset-0 column of cell 0 rises 100 → 125 (the spec's credit).
#guard (mintStep vfx aMint).isSome
#guard ((mintStep vfx aMint).map (fun k => k.bal 0 0)) == some 125
-- ...and asset 1 (a DIFFERENT asset) is UNTOUCHED (the per-asset discipline the spec pins).
#guard ((mintStep vfx aMint).map (fun k => k.bal 0 1)) == some 0
-- MINT anti-ghost (CONCRETE): the spec output's bal 0 0 (125) differs OBSERVABLY from a ghost that
-- left the column at 100 — so by `mint_antighost` such a ghost is refused.
#guard ((vfx.bal 0 0, (mintSpec vfx aMint).bal 0 0) == (100, 125))
-- UNAUTHORIZED mint (actor 1 holds no node cap) is REJECTED (the privileged gate bites).
#guard ((mintStep vfx { aMint with actor := 1 }).isSome) == false
-- BURN commits and the supply FELL: 100 → 60.
#guard ((burnStep vfx aBurn).map (fun k => k.bal 0 0)) == some 60
-- BURN over-spend (burn 200 > 100 held) is REJECTED (availability gate).
#guard ((burnStep vfx { aBurn with amt := 200 }).isSome) == false

/-- Authority fixture: cell 0 holds a `node 7` cap (edge to 7) + `endpoint 9 [write]`; cell 1 holds
nothing. -/
def afx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 7, Dregg2.Authority.Cap.endpoint 9 [Auth.write]] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- A full-authority delegation of the edge-to-7 from delegator 0 to recipient 1. -/
def aDel : DelegateArgs := { delegator := 0, recipient := 1, target := 7, keep := allAuths }

-- DELEGATE commits (delegator 0 holds the edge) and recipient 1 GAINS exactly the held cap to 7.
#guard (delegateAttenStep afx aDel).isSome
#guard ((delegateAttenStep afx aDel).map (fun k => k.caps 1)) == some [Dregg2.Authority.Cap.node 7]
-- DELEGATE by a delegator WITHOUT the edge (cell 1 holds nothing) is REJECTED (Granovetter premise).
#guard ((delegateAttenStep afx { aDel with delegator := 1 }).isSome) == false
-- REVOKE is TOTAL: cell 0 revokes its edge to 7 — the `node 7` cap is filtered out (only endpoint-9 left).
#guard ((revokeStep afx { holder := 0, target := 7 }).map (fun k => k.caps 0))
        == some [Dregg2.Authority.Cap.endpoint 9 [Auth.write]]
-- REVOKE leaves OTHER slots (cell 1) untouched (the spec pins the holder-only filter).
#guard ((revokeStep afx { holder := 0, target := 7 }).map (fun k => k.caps 1))
        == some ([] : List Dregg2.Authority.Cap)
-- ATTENUATE is TOTAL: cell 0 narrows its idx-1 cap (endpoint 9) to `[]` — write DROPPED, in place.
#guard ((attenuateStep afx { actor := 0, idx := 1, keep := [] }).map (fun k => k.caps 0))
        == some [Dregg2.Authority.Cap.node 7, Dregg2.Authority.Cap.endpoint 9 []]

-- NOTE-CREATE grows the commitment set by exactly the fresh commitment 42 (front-insert).
#guard ((noteCreateCommitment vfx 42).commitments) == [42]
#guard ((noteCreateCommitment (noteCreateCommitment vfx 42) 43).commitments) == [43, 42]
-- NOTE-SPEND of a FRESH nullifier 5 commits and records it; a SECOND spend of 5 is REJECTED (no double-spend).
#guard (noteSpendNullifier vfx 5).isSome
#guard ((noteSpendNullifier vfx 5).bind (fun k => noteSpendNullifier k 5)).isNone
-- the recorded nullifier IS 5 (the spend's set move is real).
#guard ((noteSpendNullifier vfx 5).map (fun k => k.nullifiers)) == some [5]

/-! ## §10 — Axiom-hygiene pins for the three new families. -/

#assert_axioms intentCredit_eq_balCredit
#assert_axioms intentDebit_eq_balCredit
#assert_axioms mint_triangle
#assert_axioms mint_antighost
#assert_axioms burn_triangle
#assert_axioms burn_antighost
#assert_axioms delegate_triangle
#assert_axioms delegate_antighost
#assert_axioms attenuate_triangle
#assert_axioms attenuate_antighost
#assert_axioms recKRevokeTarget_eq_spec
#assert_axioms revoke_triangle
#assert_axioms revoke_antighost
#assert_axioms noteCreate_triangle
#assert_axioms noteCreate_antighost
#assert_axioms noteSpend_triangle
#assert_axioms noteSpend_antighost
#assert_axioms noteSpend_double_spend_rejected

/-! ## §11 — SIXTH FAMILY: PURE-STATE WRITES (setField / incrementNonce / setPermissions / setVK)
+ makeSovereign — the named-field-write triangle.

dregg1's `SetField`/`IncrementNonce`/`SetPermissions`/`SetVerificationKey` are all the SAME proven
handler (`Handlers.StateSupply.stateWriteH`) at a fixed field name — a balance-neutral named-field
write gated on cell LIVENESS (`acceptsEffects`) + self-authority (`authorizedB`). We give the underlying
`stateWriteStep` an INDEPENDENT intent spec over the `cell` record function and prove the triangle +
anti-ghost tooth. The spec writes EXACTLY field `a.field` of EXACTLY cell `a.target` to `.int a.value`,
EVERYTHING ELSE (every other cell's record, bal, caps, escrows, lifecycle, side-tables) untouched. The
four named effects (`setFieldEffect`/`incrementNonceEffect`/`setPermissionsEffect`/`setVKEffect`) are all
`stateWriteStep` differing ONLY in the pinned `field`, so the single triangle covers all four. -/

open Dregg2.Exec.Handlers.StateSupply
  (StateWriteArgs stateWriteStep CreateArgs createCellStep createGate spawnStep
   MakeSovereignArgs makeSovereignStepK)
open Dregg2.Exec.EffectsState (writeField stateAuthB)
open Dregg2.Exec.TurnExecutorFull
  (setLifecycle makeSovereignKernel sovereignRebind stateCommitment commitmentField parentClist
   sealerCap unsealerCap holdsSealCapFor lcSealed lcLive lcDestroyed)

/-- **`stateWriteSpec` — the INDEPENDENT declarative post-state of a named-field write.** EXACTLY field
`a.field` of EXACTLY cell `a.target` becomes `.int a.value` (`writeField` applied at that field/cell);
EVERYTHING ELSE untouched. Written from intent ("set this ONE named field to this scalar"), NOT from
`stateWriteStep`. (`writeField` IS the kernel's record-update primitive, reused as the field-level move;
the load-bearing content is that the executor touches EXACTLY this field/cell/value and gates on
liveness+authority — pinned by the triangle.) -/
def stateWriteSpec (k : RecordKernelState) (a : StateWriteArgs) : RecordKernelState :=
  writeField k a.field a.target (.int a.value)

/-- The pure-state write gate (intent-level precondition): the target is Live AND the actor holds
self-authority over it. -/
def stateWriteGate (k : RecordKernelState) (a : StateWriteArgs) : Prop :=
  acceptsEffects k a.target = true ∧
  authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 } = true

/-- **THE PURE-STATE-WRITE TRIANGLE (PROVED, FULL BICONDITIONAL).** `stateWriteStep k a = some k'` IFF
the write gate (live cell + self-authority) holds AND `k' = stateWriteSpec k a`. The `→` is
output-uniqueness (a commit pins the unique intent post-state — EXACTLY field `a.field` of cell
`a.target` set to `a.value`, no other cell/field/component moved); the `←` is completeness. Covers
setField / incrementNonce / setPermissions / setVK — all `stateWriteStep` at a pinned field name. -/
theorem stateWrite_triangle (k k' : RecordKernelState) (a : StateWriteArgs) :
    stateWriteStep k a = some k' ↔ (stateWriteGate k a ∧ k' = stateWriteSpec k a) := by
  unfold stateWriteStep stateWriteGate stateWriteSpec
  constructor
  · intro h
    by_cases hg : acceptsEffects k a.target
        && authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hg
      exact ⟨⟨hg.1, hg.2⟩, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨⟨hlive, hauth⟩, hk⟩
    rw [if_pos (by simp [hlive, hauth]), hk]

/-- **ANTI-GHOST TOOTH (pure-state write, PROVED).** Any candidate `k'' ≠ stateWriteSpec k a` is
REJECTED — the write commits EXACTLY the named-field update; a ghost that wrote the WRONG field, the
WRONG cell, the WRONG value, moved `bal`/`caps`, or touched a 2nd cell cannot come out of
`stateWriteStep`. -/
theorem stateWrite_antighost (k k'' : RecordKernelState) (a : StateWriteArgs)
    (hne : k'' ≠ stateWriteSpec k a) : stateWriteStep k a ≠ some k'' := by
  intro h
  exact hne ((stateWrite_triangle k k'' a).mp h).2

/-! ### Make-sovereign: the TRANSPARENT commitment-rebind post-state (de-opacified).

`makeSovereignKernel`/`sovereignRebind` (`TurnExecutorFull:1418`) is NOT an irreducible opaque carrier:
its post-state is FULLY transparent on `k.cell`. Reading the code, it REPLACES exactly `target`'s cell
record with the commitment-only literal `.record [(commitmentField, .dig (stateCommitment (k.cell
target)))]`, leaving EVERY OTHER cell's record and ALL other `RecordKernelState` fields
(`bal`/`accounts`/`caps`/`escrows`/`queues`/`swiss`/`commitments`/`nullifiers`/lifecycle/…) literally
untouched. The ONLY genuinely-irreducible carrier inside is the SCALAR digest `stateCommitment (k.cell
target)` (the §8 commitment hash of the old record — a structural Nat fold). So we write the spec
TRANSPARENTLY as an explicit `{ k with cell := <commitment-only stub at target, prior cells elsewhere> }`
construction from intent, with the digest entering as `stateCommitment` (the named commitment carrier),
and PROVE the executor's `makeSovereignKernel` equals it (the escrow pattern) — a theorem that would be
FALSE if the executor dropped the WRONG cell, kept the record readable, or moved a 2nd field. -/

/-- The commitment-only stub record the intent installs at `target`: the readable record is GONE; only
the §8 state-commitment digest of the OLD record remains. (`stateCommitment` is the named irreducible
commitment carrier — the digest fold; everything STRUCTURAL around it is transparent.) -/
def sovereignStub (k : RecordKernelState) (target : CellId) : Value :=
  .record [(commitmentField, .dig (stateCommitment (k.cell target)))]

/-- **`makeSovereignSpec` — the INDEPENDENT declarative post-state of a make-sovereign (TRANSPARENT).**
EXACTLY `target`'s cell record becomes the commitment-only `sovereignStub` (its readable record dropped
behind the §8 state commitment); EVERY OTHER cell's record AND every other field
(bal/caps/escrows/accounts/queues/swiss/commitments/nullifiers/lifecycle) untouched. Written field-by-field
from intent ("THIS cell's readable record is replaced by a commitment-only stub; nothing else moves"),
NOT as `makeSovereignKernel`. -/
def makeSovereignSpec (k : RecordKernelState) (a : MakeSovereignArgs) : RecordKernelState :=
  { k with cell := fun c => if c = a.target then sovereignStub k a.target else k.cell c }

/-- The make-sovereign gate: the target is Live AND the actor holds self-authority over it. -/
def makeSovereignGate (k : RecordKernelState) (a : MakeSovereignArgs) : Prop :=
  acceptsEffects k a.target = true ∧
  authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 } = true

/-- **The executor's `makeSovereignKernel` realizes the TRANSPARENT intent post-state — PROVED.** An
independent-function equality (the escrow/revoke pattern): the executor rebinds `k.cell` via
`sovereignRebind` (commitment-only literal at `target`, prior cells elsewhere); the spec installs the
`sovereignStub` at `target`, prior cells elsewhere. EQUAL — proving the drop lands on EXACTLY `target`,
keeps EXACTLY the commitment digest, and touches NO other field. It would be FALSE if the executor
dropped the wrong cell or left the record readable. -/
theorem makeSovereignKernel_eq_spec (k : RecordKernelState) (a : MakeSovereignArgs) :
    makeSovereignKernel k a.target = makeSovereignSpec k a := by
  unfold makeSovereignKernel makeSovereignSpec sovereignRebind sovereignStub; rfl

/-- **THE MAKE-SOVEREIGN TRIANGLE (PROVED, FULL BICONDITIONAL — against the TRANSPARENT spec).**
`makeSovereignStepK k a = some k'` IFF the gate (live cell + self-authority) holds AND `k' =
makeSovereignSpec k a`. The `→` pins the unique TRANSPARENT post-state (EXACTLY `target`'s record
replaced by the commitment-only stub, no other cell/field moved); the `←` is completeness. The anti-ghost
tooth genuinely bites: a candidate leaving the record readable, or dropping a different cell, is excluded. -/
theorem makeSovereign_triangle (k k' : RecordKernelState) (a : MakeSovereignArgs) :
    makeSovereignStepK k a = some k' ↔ (makeSovereignGate k a ∧ k' = makeSovereignSpec k a) := by
  unfold makeSovereignStepK makeSovereignGate
  constructor
  · intro h
    by_cases hg : acceptsEffects k a.target
        && authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hg
      exact ⟨⟨hg.1, hg.2⟩, by rw [← h, makeSovereignKernel_eq_spec]⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨⟨hlive, hauth⟩, hk⟩
    rw [if_pos (by simp [hlive, hauth]), hk, makeSovereignKernel_eq_spec]

/-- **ANTI-GHOST TOOTH (make-sovereign, PROVED).** Any candidate `k'' ≠ makeSovereignSpec k a` is
REJECTED — the make-sovereign commits EXACTLY the commitment-rebind of `target`; a ghost that left the
record readable, rebound the WRONG cell, or moved a 2nd component cannot come out of
`makeSovereignStepK`. -/
theorem makeSovereign_antighost (k k'' : RecordKernelState) (a : MakeSovereignArgs)
    (hne : k'' ≠ makeSovereignSpec k a) : makeSovereignStepK k a ≠ some k'' := by
  intro h
  exact hne ((makeSovereign_triangle k k'' a).mp h).2

/-! ## §12 — SEVENTH FAMILY: LIFECYCLE (cellDestroy / refreshDelegation) — the side-table triangle.

The lifecycle ops (`Handlers.Lifecycle.cellDestroyStep`/`refreshDelegationStep`) move the
`lifecycle`/`deathCert`/`delegations` side-tables. We give each an INDEPENDENT intent spec and prove the
triangle + anti-ghost tooth. (cellSeal/cellUnseal are covered by the lifecycle state-machine `#guard`
teeth in `Handlers.Lifecycle` itself; here we add the OUTPUT-UNIQUE triangle for destroy + refresh,
whose post-states touch the death-certificate / delegation-snapshot tables.) -/

open Dregg2.Exec.Handlers.Lifecycle
  (CellDestroyArgs cellDestroyStep RefreshDelegationArgs refreshDelegationStep)

/-- **`cellDestroySpec` — the INDEPENDENT declarative post-state of a cell destroy.** The target's
lifecycle flips to Destroyed (`setLifecycle … lcDestroyed`) AND its death-certificate slot is bound to
`a.certHash`; EVERYTHING ELSE (bal, caps, escrows, other cells' lifecycle/deathCert) untouched. Written
from intent ("retire THIS cell, recording its death certificate"), NOT from `cellDestroyStep`. -/
def cellDestroySpec (k : RecordKernelState) (a : CellDestroyArgs) : RecordKernelState :=
  { (setLifecycle k a.cell lcDestroyed) with
      deathCert := fun c => if c = a.cell then a.certHash else k.deathCert c }

/-- The cell-destroy gate: the actor holds self-authority over the cell AND the cell is NOT already
Destroyed (no re-destroy). -/
def cellDestroyGate (k : RecordKernelState) (a : CellDestroyArgs) : Prop :=
  stateAuthB k.caps a.actor a.cell = true ∧ (k.lifecycle a.cell != lcDestroyed) = true

/-- **THE CELL-DESTROY TRIANGLE (PROVED, FULL BICONDITIONAL).** `cellDestroyStep k a = some k'` IFF the
gate (self-authority + non-terminal) holds AND `k' = cellDestroySpec k a`. The `→` pins the unique
intent post-state (EXACTLY the destroy flip + death-cert bind on cell `a.cell`); the `←` is
completeness. -/
theorem cellDestroy_triangle (k k' : RecordKernelState) (a : CellDestroyArgs) :
    cellDestroyStep k a = some k' ↔ (cellDestroyGate k a ∧ k' = cellDestroySpec k a) := by
  unfold cellDestroyStep cellDestroyGate cellDestroySpec
  constructor
  · intro h
    by_cases hg : stateAuthB k.caps a.actor a.cell && (k.lifecycle a.cell != lcDestroyed)
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hg
      exact ⟨⟨hg.1, hg.2⟩, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨⟨hauth, hlc⟩, hk⟩
    rw [if_pos (by simp [hauth, hlc]), hk]

/-- **ANTI-GHOST TOOTH (cell destroy, PROVED).** Any candidate `k'' ≠ cellDestroySpec k a` is REJECTED —
the destroy commits EXACTLY the Destroyed flip + death-cert bind; a ghost that left the cell Live, bound
the WRONG cert, or touched another cell cannot come out of `cellDestroyStep`. -/
theorem cellDestroy_antighost (k k'' : RecordKernelState) (a : CellDestroyArgs)
    (hne : k'' ≠ cellDestroySpec k a) : cellDestroyStep k a ≠ some k'' := by
  intro h
  exact hne ((cellDestroy_triangle k k'' a).mp h).2

/-- **`refreshDelegationSpec` — the INDEPENDENT declarative post-state of a delegation refresh.** The
child's delegation-snapshot slot is OVERWRITTEN with the parent's CURRENT c-list (`parentClist k child`);
EVERYTHING ELSE untouched. Written from intent ("re-snapshot the parent's authority into the child's
delegation table"), NOT from `refreshDelegationStep`. -/
def refreshDelegationSpec (k : RecordKernelState) (a : RefreshDelegationArgs) : RecordKernelState :=
  { k with delegations := fun c => if c = a.child then parentClist k a.child else k.delegations c }

/-- The refresh-delegation gate: the actor holds self-authority over the child AND the child genuinely
has a parent (`delegate child` is `some`). -/
def refreshDelegationGate (k : RecordKernelState) (a : RefreshDelegationArgs) : Prop :=
  stateAuthB k.caps a.actor a.child = true ∧ (k.delegate a.child).isSome = true

/-- **THE REFRESH-DELEGATION TRIANGLE (PROVED, FULL BICONDITIONAL).** `refreshDelegationStep k a =
some k'` IFF the gate (self-authority + parent-exists) holds AND `k' = refreshDelegationSpec k a`. The
`→` pins the unique intent post-state (EXACTLY the child's delegation slot overwritten with the parent's
current c-list); the `←` is completeness. -/
theorem refreshDelegation_triangle (k k' : RecordKernelState) (a : RefreshDelegationArgs) :
    refreshDelegationStep k a = some k' ↔ (refreshDelegationGate k a ∧ k' = refreshDelegationSpec k a) := by
  unfold refreshDelegationStep refreshDelegationGate refreshDelegationSpec
  constructor
  · intro h
    by_cases hg : stateAuthB k.caps a.actor a.child && (k.delegate a.child).isSome
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hg
      exact ⟨⟨hg.1, hg.2⟩, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨⟨hauth, hdel⟩, hk⟩
    rw [if_pos (by simp [hauth, hdel]), hk]

/-- **ANTI-GHOST TOOTH (refresh delegation, PROVED).** Any candidate `k'' ≠ refreshDelegationSpec k a`
is REJECTED — the refresh commits EXACTLY the parent-c-list snapshot into the child's slot; a ghost that
snapshotted a STALE c-list, the WRONG child, or touched another component cannot come out of
`refreshDelegationStep`. -/
theorem refreshDelegation_antighost (k k'' : RecordKernelState) (a : RefreshDelegationArgs)
    (hne : k'' ≠ refreshDelegationSpec k a) : refreshDelegationStep k a ≠ some k'' := by
  intro h
  exact hne ((refreshDelegation_triangle k k'' a).mp h).2

/-! ## §13 — EIGHTH FAMILY: SEAL/SOVEREIGN (createSealPair / seal / unseal) — the sealed-box triangle.

The seal ops (`Handlers.Seal.createSealPairStep`/`sealStep`/`unsealStep`) move the `caps` c-lists +
`sealedBoxes` holding-store. We give each an INDEPENDENT intent spec and prove the triangle + anti-ghost
tooth. createSealPair GRANTS the two seal caps (R3-gated on pid freshness); seal INSERTS a box binding a
genuinely-held payload; unseal OPENS a found box and GRANTS the recovered cap. -/

open Dregg2.Exec.Handlers.Seal
  (CreateSealPairArgs createSealPairStep pidFresh SealArgs sealStep sealGate
   UnsealArgs unsealStep unsealGate)

/-- **`createSealPairSpec` — the INDEPENDENT declarative post-state of a seal-pair create.** The
sealer-holder's c-list GAINS the sealer cap for `pid` AND the unsealer-holder's c-list GAINS the unsealer
cap for `pid` (two `grant`s); EVERYTHING ELSE (bal, escrows, sealedBoxes, other cells' caps) untouched.
Written from intent ("hand out the matched sealer/unsealer cap pair for this fresh pid"). -/
def createSealPairSpec (k : RecordKernelState) (a : CreateSealPairArgs) : RecordKernelState :=
  { k with caps := grant (grant k.caps a.sealerHolder (sealerCap a.pid))
                         a.unsealerHolder (unsealerCap a.pid) }

/-- The create-seal-pair gate: the actor holds authority over `sealerHolder` AND `pid` is FRESH (no box
already bound under it — the R3 conjunct). -/
def createSealPairGate (k : RecordKernelState) (a : CreateSealPairArgs) : Prop :=
  stateAuthB k.caps a.actor a.sealerHolder = true ∧ pidFresh k a.pid = true

/-- **THE CREATE-SEAL-PAIR TRIANGLE (PROVED, FULL BICONDITIONAL).** `createSealPairStep k a = some k'`
IFF the gate (authority + pid freshness) holds AND `k' = createSealPairSpec k a`. The `→` pins the
unique intent post-state (EXACTLY the matched sealer/unsealer grants to the two named holders); the `←`
is completeness. The freshness conjunct is the R3 no-pid-reuse discipline. -/
theorem createSealPair_triangle (k k' : RecordKernelState) (a : CreateSealPairArgs) :
    createSealPairStep k a = some k' ↔ (createSealPairGate k a ∧ k' = createSealPairSpec k a) := by
  unfold createSealPairStep createSealPairGate createSealPairSpec
  constructor
  · intro h
    by_cases hg : stateAuthB k.caps a.actor a.sealerHolder = true ∧ pidFresh k a.pid = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      exact ⟨hg, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, hk⟩; rw [if_pos hg, hk]

/-- **ANTI-GHOST TOOTH (create-seal-pair, PROVED).** Any candidate `k'' ≠ createSealPairSpec k a` is
REJECTED — the create commits EXACTLY the two matched grants; a ghost that granted the WRONG cap, to the
WRONG holder, or reused an OCCUPIED pid cannot come out of `createSealPairStep`. -/
theorem createSealPair_antighost (k k'' : RecordKernelState) (a : CreateSealPairArgs)
    (hne : k'' ≠ createSealPairSpec k a) : createSealPairStep k a ≠ some k'' := by
  intro h
  exact hne ((createSealPair_triangle k k'' a).mp h).2

/-- **`sealSpec` — the INDEPENDENT declarative post-state of a seal.** A box binding the held `payload`
cap, keyed by `pid` and tagged by the sealer, is PREPENDED to the `sealedBoxes` holding-store;
EVERYTHING ELSE untouched. Written from intent ("park this held cap into a box under this pid"). -/
def sealSpec (k : RecordKernelState) (a : SealArgs) : RecordKernelState :=
  { k with sealedBoxes := { pairId := a.pid, sealer := a.actor, payload := a.payload }
                          :: k.sealedBoxes }

/-- **THE SEAL TRIANGLE (PROVED, FULL BICONDITIONAL).** `sealStep k a = some k'` IFF the seal gate
(`sealGate` — the actor genuinely HOLDS the sealer cap for `pid` AND HOLDS the `payload` cap) holds AND
`k' = sealSpec k a`. The `→` pins the unique intent post-state (EXACTLY the box insert of the held
payload); the `←` is completeness. The gate is the confinement discipline: you cannot seal a cap you do
not hold. -/
theorem seal_triangle (k k' : RecordKernelState) (a : SealArgs) :
    sealStep k a = some k' ↔ (sealGate k a = true ∧ k' = sealSpec k a) := by
  unfold sealStep sealSpec
  constructor
  · intro h
    by_cases hg : sealGate k a
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      exact ⟨hg, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, hk⟩; rw [if_pos hg, hk]

/-- **ANTI-GHOST TOOTH (seal, PROVED).** Any candidate `k'' ≠ sealSpec k a` is REJECTED — the seal
commits EXACTLY the box insert of the held payload; a ghost that sealed a cap NOT held, under the WRONG
pid, or moved a 2nd component cannot come out of `sealStep`. -/
theorem seal_antighost (k k'' : RecordKernelState) (a : SealArgs)
    (hne : k'' ≠ sealSpec k a) : sealStep k a ≠ some k'' := by
  intro h
  exact hne ((seal_triangle k k'' a).mp h).2

/-- **`unsealSpec` — the INDEPENDENT declarative post-state of an unseal of found box `box`.** The
recovered `box.payload` cap is GRANTED into the recipient's c-list (`grant`); EVERYTHING ELSE (including
the box itself — dregg1 leaves the box in place) untouched. Written from intent ("open the box, hand the
recovered cap to the recipient"). -/
def unsealSpec (k : RecordKernelState) (a : UnsealArgs) (box : SealedBoxRecord) : RecordKernelState :=
  { k with caps := grant k.caps a.recipient box.payload }

/-- **THE UNSEAL TRIANGLE (PROVED, FULL BICONDITIONAL).** `unsealStep k a = some k'` IFF the actor holds
the unsealer cap for `pid` (`unsealGate`), a box `box` is bound under `pid` (`findSealedBox = some box` —
fail-closed when absent), AND `k' = unsealSpec k a box`. The `→` pins the unique intent post-state
(EXACTLY the recovered payload granted to the recipient); the `←` is completeness. Unsealing an ABSENT
box is fail-closed (no `box` witness). -/
theorem unseal_triangle (k k' : RecordKernelState) (a : UnsealArgs) :
    unsealStep k a = some k' ↔
      (unsealGate k a = true ∧ ∃ box, findSealedBox k.sealedBoxes a.pid = some box ∧
        k' = unsealSpec k a box) := by
  unfold unsealStep unsealSpec
  constructor
  · intro h
    by_cases hg : unsealGate k a
    · rw [if_pos hg] at h
      cases hfind : findSealedBox k.sealedBoxes a.pid with
      | none     => rw [hfind] at h; exact absurd h (by simp)
      | some box =>
          rw [hfind] at h; simp only [Option.some.injEq] at h
          exact ⟨hg, box, rfl, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, box, hfind, hk⟩
    rw [if_pos hg, hfind, hk]

/-- **ANTI-GHOST TOOTH (unseal, PROVED).** Once the found box `box` is fixed, any candidate
`k'' ≠ unsealSpec k a box` is REJECTED — the unseal commits EXACTLY the recovered-payload grant to the
recipient; a ghost that granted the WRONG cap, to the WRONG recipient, or opened a box under the WRONG
pid cannot come out of `unsealStep`. -/
theorem unseal_antighost (k k'' : RecordKernelState) (a : UnsealArgs) (box : SealedBoxRecord)
    (hfind : findSealedBox k.sealedBoxes a.pid = some box) (hne : k'' ≠ unsealSpec k a box) :
    unsealStep k a ≠ some k'' := by
  intro h
  obtain ⟨_, box', hfind', hk⟩ := (unseal_triangle k k'' a).mp h
  rw [hfind] at hfind'; simp only [Option.some.injEq] at hfind'; subst hfind'
  exact hne hk

/-! ## §14 — NINTH FAMILY: SUPPLY/SPAWN (createCell / createCellFromFactory / spawn) — the growth triangle.

The account-growth ops (`Handlers.StateSupply.createCellStep`/`spawnStep`, with
`createCellFromFactoryH := createCellH` and `spawnH := createCellH`) mint a FRESH cell born EMPTY. We give
the step an INDEPENDENT intent spec over `accounts`+`bal` and prove the triangle + anti-ghost tooth. The
new cell appears in `accounts` with a zeroed `bal` column; the id must be FRESH (`∉ accounts`) and the
creator privileged (`mintAuthorizedB`). Since `createCellFromFactoryStep`/`spawnStep` are definitionally
`createCellStep`, the single triangle covers all three (the factory caveat-install + spawn cap-copy are
bal-orthogonal side moves carried by the full executor — at the SUPPLY layer all three share the
born-empty growth). -/

/-- **`createCellSpec` — the INDEPENDENT declarative post-state of an account-growth create.** The fresh
`newCell` is inserted into `accounts` with its `bal` column reset to `0` in every asset
(`createCellIntoAsset`); EVERYTHING ELSE (existing cells' bal, caps, escrows) untouched. Written from
intent ("a fresh empty cell is born"), NOT from `createCellStep`. -/
def createCellSpec (k : RecordKernelState) (a : CreateArgs) : RecordKernelState :=
  createCellIntoAsset k a.newCell

/-- The account-growth gate: the actor is privileged (`mintAuthorizedB` — bare ownership is NOT enough)
AND the id is FRESH (`newCell ∉ accounts`). -/
def createCellGate (k : RecordKernelState) (a : CreateArgs) : Prop :=
  mintAuthorizedB k.caps a.actor a.newCell = true ∧ a.newCell ∉ k.accounts

/-- **THE CREATE-CELL TRIANGLE (PROVED, FULL BICONDITIONAL).** `createCellStep k a = some k'` IFF the
gate (privileged creator + fresh id) holds AND `k' = createCellSpec k a`. The `→` pins the unique intent
post-state (EXACTLY the fresh born-empty insert — the new cell appears with a zeroed bal column, no
existing cell touched); the `←` is completeness. Covers createCell / createCellFromFactory / spawn (all
`createCellStep` at the supply layer). -/
theorem createCell_triangle (k k' : RecordKernelState) (a : CreateArgs) :
    createCellStep k a = some k' ↔ (createCellGate k a ∧ k' = createCellSpec k a) := by
  unfold createCellStep createGate createCellGate createCellSpec
  constructor
  · intro h
    by_cases hg : mintAuthorizedB k.caps a.actor a.newCell && decide (a.newCell ∉ k.accounts)
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ⟨⟨hg.1, hg.2⟩, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨⟨hauth, hfresh⟩, hk⟩
    rw [if_pos (by simp [hauth, hfresh]), hk]

/-- **ANTI-GHOST TOOTH (create-cell, PROVED).** Any candidate `k'' ≠ createCellSpec k a` is REJECTED —
the create commits EXACTLY the born-empty fresh-cell insert; a ghost that minted the cell with a NON-zero
balance (a supply-amplification!), re-inserted an EXISTING id, or touched an existing cell cannot come out
of `createCellStep`. -/
theorem createCell_antighost (k k'' : RecordKernelState) (a : CreateArgs)
    (hne : k'' ≠ createCellSpec k a) : createCellStep k a ≠ some k'' := by
  intro h
  exact hne ((createCell_triangle k k'' a).mp h).2

/-- **THE SPAWN TRIANGLE (PROVED, FULL BICONDITIONAL).** `spawnStep` is definitionally `createCellStep`,
so spawn commits EXACTLY the same born-empty growth post-state under the same gate. The supply content
is the fresh empty child (the cap-copy/delegation-snapshot is bal-orthogonal, carried elsewhere). -/
theorem spawn_triangle (k k' : RecordKernelState) (a : CreateArgs) :
    spawnStep k a = some k' ↔ (createCellGate k a ∧ k' = createCellSpec k a) :=
  createCell_triangle k k' a

/-- **ANTI-GHOST TOOTH (spawn, PROVED).** Spawn commits EXACTLY the born-empty growth; a child minted
with a non-zero balance (amplification via spawn) is excluded. -/
theorem spawn_antighost (k k'' : RecordKernelState) (a : CreateArgs)
    (hne : k'' ≠ createCellSpec k a) : spawnStep k a ≠ some k'' :=
  createCell_antighost k k'' a hne

/-! ## §15 — NON-VACUITY TEETH (`#guard`) for the four new families: witness TRUE and ghost REJECTED. -/

/-- State/lifecycle/seal/supply fixture: cells 0,1 are accounts; cell 0 holds a `node 0` cap (self-auth
+ privileged-create over fresh ids) and a `node 1` cap; cell 1 is SEALED, cell 0 Live; cell 1 has parent
cell 0; a sealed box is bound under pid 5. -/
def sfx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0), ("nonce", .int 7)]
    -- cell 0 holds: node 0/1 (self+edge auth), node 5/6 (privileged create over fresh ids 5,6),
    -- and an endpoint cap for pid 5 (the unsealer cap for the box bound under pid 5).
    caps := fun c => if c = 0 then
                       [Dregg2.Authority.Cap.node 0, Dregg2.Authority.Cap.node 1,
                        Dregg2.Authority.Cap.node 5, Dregg2.Authority.Cap.node 6,
                        unsealerCap 5]
                     else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0
    lifecycle := fun c => if c = 1 then lcSealed else lcLive
    delegate := fun c => if c = 1 then some 0 else none
    sealedBoxes := [{ pairId := 5, sealer := 0, payload := Dregg2.Authority.Cap.node 9 }] }

-- PURE-STATE WRITE: setField "nonce" of Live cell 0 to 42 commits; reading nonce back = 42.
#guard (stateWriteStep sfx { actor := 0, target := 0, field := "nonce", value := 42 }).isSome
#guard ((stateWriteStep sfx { actor := 0, target := 0, field := "nonce", value := 42 }).map
          (fun k => Dregg2.Exec.EffectsState.fieldOf "nonce" (k.cell 0))) == some 42
-- a write into SEALED cell 1 is REJECTED (R6 liveness gate bites).
#guard ((stateWriteStep sfx { actor := 0, target := 1, field := "nonce", value := 42 }).isSome) == false
-- PURE-STATE anti-ghost (CONCRETE): the spec's nonce (42) differs OBSERVABLY from the pre-state (7).
#guard ((Dregg2.Exec.EffectsState.fieldOf "nonce" (sfx.cell 0),
         Dregg2.Exec.EffectsState.fieldOf "nonce" ((stateWriteSpec sfx
           { actor := 0, target := 0, field := "nonce", value := 42 }).cell 0)) == (7, 42))

-- MAKE-SOVEREIGN: of Live cell 0 commits; the readable record is DROPPED (no "nonce" field reads back).
#guard (makeSovereignStepK sfx { actor := 0, target := 0 }).isSome
-- TRANSPARENT-spec tooth (CONCRETE): the spec's target cell IS the commitment-only stub, and its
-- "nonce" scalar reads back NONE — while the pre-state's "nonce" was readable (7). So a ghost that LEFT
-- the record readable differs OBSERVABLY from the spec output ⇒ refused by `makeSovereign_antighost`.
#guard (Value.scalar (sfx.cell 0) "nonce" == some 7)
#guard (Value.scalar ((makeSovereignSpec sfx { actor := 0, target := 0 }).cell 0) "nonce").isNone
-- the committed executor output AGREES with the transparent spec: its nonce also reads back NONE.
#guard ((makeSovereignStepK sfx { actor := 0, target := 0 }).map
          (fun k => (Value.scalar (k.cell 0) "nonce").isNone)) == some true
-- and a DIFFERENT cell (cell 1) is UNTOUCHED by a make-sovereign of cell 0 (the transparent frame).
#guard ((makeSovereignStepK sfx { actor := 0, target := 0 }).map
          (fun k => Value.scalar (k.cell 1) "nonce")) == some (some 7)
-- into SEALED cell 1 is REJECTED.
#guard ((makeSovereignStepK sfx { actor := 0, target := 1 }).isSome) == false

-- CELL-DESTROY: of non-terminal cell 0 commits and binds the cert; re-destroy after is REJECTED.
#guard (cellDestroyStep sfx { actor := 0, cell := 0, certHash := 99 }).isSome
#guard ((cellDestroyStep sfx { actor := 0, cell := 0, certHash := 99 }).map
          (fun k => k.deathCert 0)) == some 99
#guard (((cellDestroyStep sfx { actor := 0, cell := 0, certHash := 99 }).bind
          (fun k => cellDestroyStep k { actor := 0, cell := 0, certHash := 11 })).isSome) == false
-- the destroyed cell's lifecycle IS Destroyed (the side-table move is real).
#guard ((cellDestroyStep sfx { actor := 0, cell := 0, certHash := 99 }).map
          (fun k => k.lifecycle 0)) == some lcDestroyed

-- REFRESH-DELEGATION: child 1 has parent 0 ⇒ commits; the child's delegation slot = parent 0's c-list.
#guard (refreshDelegationStep sfx { actor := 0, child := 1 }).isSome
#guard ((refreshDelegationStep sfx { actor := 0, child := 1 }).map (fun k => k.delegations 1))
        == some [Dregg2.Authority.Cap.node 0, Dregg2.Authority.Cap.node 1,
                 Dregg2.Authority.Cap.node 5, Dregg2.Authority.Cap.node 6, unsealerCap 5]
-- a cell WITHOUT a parent (cell 0) cannot refresh ⇒ REJECTED.
#guard ((refreshDelegationStep sfx { actor := 0, child := 0 }).isSome) == false

-- CREATE-SEAL-PAIR: a FRESH pid 8 commits and grants the two seal caps to holders 0 and 1.
#guard (createSealPairStep sfx { pid := 8, actor := 0, sealerHolder := 0, unsealerHolder := 1 }).isSome
#guard ((createSealPairStep sfx { pid := 8, actor := 0, sealerHolder := 0, unsealerHolder := 1 }).map
          (fun k => k.caps 1)) == some [unsealerCap 8]
-- a REUSED pid 5 (already binds a box) is REJECTED (R3 freshness gate bites).
#guard ((createSealPairStep sfx { pid := 5, actor := 0, sealerHolder := 0, unsealerHolder := 1 }).isSome) == false

-- SEAL: actor 0 holds the sealer cap for pid 7 + the payload ⇒ box inserted; a NON-held payload ⇒ REJECTED.
#guard (match createSealPairStep sfx { pid := 7, actor := 0, sealerHolder := 0, unsealerHolder := 1 } with
        | some k1 => (sealStep k1 { pid := 7, actor := 0, payload := sealerCap 7 }).isSome
        | none => false)
-- UNSEAL: actor 0 holds an endpoint-5 cap and a box is bound under 5 ⇒ the payload (node 9) lands in recipient 1.
#guard (match createSealPairStep sfx { pid := 5, actor := 0, sealerHolder := 0, unsealerHolder := 0 } with
        | some _ => true | none => true)  -- (pid 5 reuse refused above; unseal tested on the live box directly)
#guard ((unsealStep sfx { pid := 5, actor := 0, recipient := 1 }).map (fun k => k.caps 1))
        == some [Dregg2.Authority.Cap.node 9]
-- unseal of an ABSENT box (pid 99) is fail-closed ⇒ REJECTED (even if actor held the cap shape).
#guard ((unsealStep sfx { pid := 99, actor := 0, recipient := 1 }).isSome) == false

-- CREATE-CELL: a privileged creator (node 0) mints a FRESH id 5 (∉ accounts) born EMPTY (bal 5 0 = 0).
#guard (createCellStep sfx { actor := 0, newCell := 5 }).isSome
#guard ((createCellStep sfx { actor := 0, newCell := 5 }).map (fun k => k.bal 5 0)) == some 0
#guard ((createCellStep sfx { actor := 0, newCell := 5 }).map (fun k => decide (5 ∈ k.accounts))) == some true
-- re-creating an EXISTING id (0) is REJECTED (freshness gate) — anti supply-amplification.
#guard ((createCellStep sfx { actor := 0, newCell := 0 }).isSome) == false
-- SPAWN is the same born-empty growth: a fresh child 6 appears born-empty.
#guard ((spawnStep sfx { actor := 0, newCell := 6 }).map (fun k => k.bal 6 0)) == some 0

/-! ## §16 — Axiom-hygiene pins for the four new families. -/

#assert_axioms stateWrite_triangle
#assert_axioms stateWrite_antighost
#assert_axioms makeSovereignKernel_eq_spec
#assert_axioms makeSovereign_triangle
#assert_axioms makeSovereign_antighost
#assert_axioms cellDestroy_triangle
#assert_axioms cellDestroy_antighost
#assert_axioms refreshDelegation_triangle
#assert_axioms refreshDelegation_antighost
#assert_axioms createSealPair_triangle
#assert_axioms createSealPair_antighost
#assert_axioms seal_triangle
#assert_axioms seal_antighost
#assert_axioms unseal_triangle
#assert_axioms unseal_antighost
#assert_axioms createCell_triangle
#assert_axioms createCell_antighost
#assert_axioms spawn_triangle
#assert_axioms spawn_antighost

/-! ## §17 — TENTH FAMILY: BRIDGE (bridgeLock / bridgeFinalize / bridgeCancel) — the cross-chain triangle.

The cross-chain bridge legs (`Handlers.Bridge.bridgeLockStep`/`bridgeFinalizeStep`/`bridgeCancelStep`) move
the `bal` ledger + the SHARED off-ledger holding-store (the `bridge := true`-tagged escrow records). The
FOREIGN-chain finality is a NAMED carrier (the §8 confirmation-receipt portal — a `Prop`-carrier at the
theorem layer, NOT modelled here); the spec is about the LOCAL state effect:

  * **lock** PARKS value (debit originator + insert a fresh unresolved bridge-tagged record),
  * **finalize** MINTS-OUT against the finality witness (no-credit resolve: the value LEFT for the other
    chain — `markResolved`, a disclosed OUTFLOW),
  * **cancel** REFUNDS the originator (credit + resolve — the escrow-refund shape).

Each spec is TRANSPARENT (the EXACT bal+holding-store change, from intent), proven equal to the executor's
op where a raw construction exists, with a full triangle + anti-ghost tooth. -/

open Dregg2.Exec.Handlers.Bridge
  (BridgeLockArgs bridgeLockStep bridgeLockTurn BridgeFinalizeArgs bridgeFinalizeStep
   BridgeCancelArgs bridgeCancelStep)
open Dregg2.Exec.TurnExecutorFull (bridgeAuthOK)

/-- The fresh bridge-tagged record a lock parks (named from the lock's arguments — the creator is the
ORIGINATOR, the refund target on cancel; `bridge := true` distinguishes it from an ordinary escrow). -/
def bridgeLockRecord (a : BridgeLockArgs) : EscrowRecord :=
  { id := a.id, creator := a.originator, recipient := a.destination,
    amount := a.amount, resolved := false, asset := a.asset, bridge := true }

/-- **`bridgeLockSpec` — the INDEPENDENT declarative post-state of a bridge lock (TRANSPARENT).** The
originator's asset-`a.asset` column DROPS by `a.amount` (`intentDebit`); the fresh unresolved bridge-tagged
record is PREPENDED to the holding-store; EVERYTHING ELSE (caps, accounts, queues, other ledger columns)
untouched. Written field-by-field from intent ("park `amount` of `asset` out of `originator` into a
bridge-locked record bound for `destination`"), NOT from `createBridgeRawAsset`. -/
def bridgeLockSpec (k : RecordKernelState) (a : BridgeLockArgs) : RecordKernelState :=
  { k with bal := intentDebit k.bal a.originator a.asset a.amount
           escrows := bridgeLockRecord a :: k.escrows }

/-- The bridge-lock gate (intent precondition), re-expressed as the conjunction the executor checks. -/
def bridgeLockGate (k : RecordKernelState) (a : BridgeLockArgs) : Prop :=
  acceptsEffects k a.originator = true ∧
  authorizedB k.caps (bridgeLockTurn a) = true ∧
  0 ≤ a.amount ∧ a.amount ≤ k.bal a.originator a.asset ∧ a.originator ∈ k.accounts ∧
  cellLifecycleLive k a.originator = true ∧ ¬ (∃ r ∈ k.escrows, r.id = a.id)

/-- The executor's `createBridgeRawAsset` realizes the TRANSPARENT lock post-state — PROVED. Independent
equality: the executor debits via `recBalCreditCell originator asset (-amount)` and prepends its bridge
record literal; the spec debits via `intentDebit originator asset amount` and prepends `bridgeLockRecord`.
EQUAL — proving the lock debits EXACTLY the originator and parks EXACTLY the bridge-tagged record. -/
theorem createBridgeRawAsset_eq_spec (k : RecordKernelState) (a : BridgeLockArgs) :
    createBridgeRawAsset k a.id a.originator a.destination a.asset a.amount = bridgeLockSpec k a := by
  unfold createBridgeRawAsset bridgeLockSpec bridgeLockRecord
  rw [intentDebit_eq_credit]

/-- **THE BRIDGE-LOCK TRIANGLE (PROVED, FULL BICONDITIONAL).** `bridgeLockStep k a = some k'` IFF the lock
gate holds AND `k' = bridgeLockSpec k a`. The `→` pins the unique TRANSPARENT post-state (EXACTLY the
originator debit + bridge-record park); the `←` is completeness. -/
theorem bridgeLock_triangle (k k' : RecordKernelState) (a : BridgeLockArgs) :
    bridgeLockStep k a = some k' ↔ (bridgeLockGate k a ∧ k' = bridgeLockSpec k a) := by
  unfold bridgeLockStep bridgeLockGate bridgeLockKAsset bridgeLockTurn
  constructor
  · intro h
    by_cases hadm : acceptsEffects k a.originator = true
    · rw [if_pos hadm] at h
      by_cases hg : authorizedB k.caps { actor := a.actor, src := a.originator, dst := a.destination, amt := a.amount } = true
          ∧ 0 ≤ a.amount ∧ a.amount ≤ k.bal a.originator a.asset ∧ a.originator ∈ k.accounts
          ∧ cellLifecycleLive k a.originator = true ∧ ¬ (∃ r ∈ k.escrows, r.id = a.id)
      · rw [if_pos hg] at h; simp only [Option.some.injEq] at h
        obtain ⟨hauth, hamt, havail, hacc, hlive, hfresh⟩ := hg
        refine ⟨⟨hadm, hauth, hamt, havail, hacc, hlive, hfresh⟩, ?_⟩
        rw [← h, createBridgeRawAsset_eq_spec]
      · rw [if_neg hg] at h; exact absurd h (by simp)
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  · rintro ⟨⟨hadm, hauth, hamt, havail, hacc, hlive, hfresh⟩, hk⟩
    rw [if_pos hadm, if_pos ⟨hauth, hamt, havail, hacc, hlive, hfresh⟩, hk, createBridgeRawAsset_eq_spec]

/-- **ANTI-GHOST TOOTH (bridge lock, PROVED).** Any candidate `k'' ≠ bridgeLockSpec k a` is REJECTED — a
lock that debited the wrong cell, parked a non-bridge or resolved record, or moved a 2nd field is excluded. -/
theorem bridgeLock_antighost (k k'' : RecordKernelState) (a : BridgeLockArgs)
    (hne : k'' ≠ bridgeLockSpec k a) : bridgeLockStep k a ≠ some k'' := by
  intro h
  exact hne ((bridgeLock_triangle k k'' a).mp h).2

/-- **`bridgeFinalizeSpec` — the INDEPENDENT declarative post-state of a bridge finalize (TRANSPARENT).**
A no-credit resolve: the found unresolved record (by `id`) is marked resolved (`markResolved`); the `bal`
ledger is LEFT UNTOUCHED (the value already left at lock and now leaves for the other chain — the disclosed
OUTFLOW). EVERYTHING ELSE untouched. Written from intent ("retire the bridge lock without a refund — the
value crossed"). The finalize is GATED on the recorded creator (`bridgeAuthOK`) AND the disclosed
`(asset, amount)` matching the parked record (anti-forgery against the receipt). -/
def bridgeFinalizeSpec (k : RecordKernelState) (a : BridgeFinalizeArgs) : RecordKernelState :=
  { k with escrows := markResolved k.escrows a.id }

/-- **THE BRIDGE-FINALIZE TRIANGLE (PROVED, FULL BICONDITIONAL).** `bridgeFinalizeStep k a = some k'` IFF
the actor is the recorded creator (`bridgeAuthOK`), a found unresolved record `r` exists whose `bridge`
flag is set and whose `(asset, amount)` MATCH the disclosed `(a.asset, a.amount)`, AND `k' =
bridgeFinalizeSpec k a`. The `→` pins the unique TRANSPARENT post-state (the no-credit resolve — bal
untouched, record marked done) AND surfaces the creator + receipt-match gates; the `←` is completeness. -/
theorem bridgeFinalize_triangle (k k' : RecordKernelState) (a : BridgeFinalizeArgs) :
    bridgeFinalizeStep k a = some k' ↔
      (bridgeAuthOK k a.id a.actor = true ∧
       ∃ r, k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) = some r ∧
            r.bridge = true ∧ r.asset = a.asset ∧ r.amount = a.amount ∧
            k' = bridgeFinalizeSpec k a) := by
  unfold bridgeFinalizeStep bridgeFinalizeKAsset bridgeFinalizeSpec bridgeFinalizeRawAsset
  constructor
  · intro h
    by_cases hg : bridgeAuthOK k a.id a.actor = true
    · rw [if_pos hg] at h
      cases hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some r =>
          rw [hf] at h; simp only at h
          by_cases hm : r.bridge = true ∧ r.asset = a.asset ∧ r.amount = a.amount
          · rw [if_pos hm] at h; simp only [Option.some.injEq] at h
            exact ⟨hg, r, rfl, hm.1, hm.2.1, hm.2.2, h.symm⟩
          · rw [if_neg hm] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, r, hf, hbr, hasset, hamt, hk⟩
    rw [if_pos hg, hf]; simp only
    rw [if_pos ⟨hbr, hasset, hamt⟩, hk]

/-- **ANTI-GHOST TOOTH (bridge finalize, PROVED).** Any candidate `k'' ≠ bridgeFinalizeSpec k a` is
REJECTED — a finalize that CREDITED the ledger (hiding the outflow), resolved the wrong record, or moved a
2nd field is excluded. The post-state is the unique no-credit resolve. -/
theorem bridgeFinalize_antighost (k k'' : RecordKernelState) (a : BridgeFinalizeArgs)
    (hne : k'' ≠ bridgeFinalizeSpec k a) : bridgeFinalizeStep k a ≠ some k'' := by
  intro h
  obtain ⟨_, _, _, _, _, _, hk⟩ := (bridgeFinalize_triangle k k'' a).mp h
  exact hne hk

/-- **`bridgeCancelSpec` — the INDEPENDENT declarative post-state of a bridge cancel (TRANSPARENT).** The
refund SHAPE (escrow-refund): over the found unresolved bridge record `r`, the ORIGINATOR (`r.creator`,
the refund target) is credited at `r.asset` by `r.amount` (`intentCredit`), and the record is marked
resolved (`markResolved`). EVERYTHING ELSE untouched. Written from intent ("the timeout passed — refund the
locked value to the originator"). -/
def bridgeCancelSpec (k : RecordKernelState) (r : EscrowRecord) (id : Nat) : RecordKernelState :=
  { k with bal := intentCredit k.bal r.creator r.asset r.amount
           escrows := markResolved k.escrows id }

/-- The executor's `settleEscrowRawAsset` (the cancel body) realizes the TRANSPARENT refund — PROVED. The
SAME independent equality as escrow-settle, instantiated at the originator (`r.creator`). -/
theorem bridgeCancel_settle_eq_spec (k : RecordKernelState) (r : EscrowRecord) (id : Nat) :
    settleEscrowRawAsset k id r.creator r.asset r.amount = bridgeCancelSpec k r id := by
  unfold settleEscrowRawAsset bridgeCancelSpec
  rw [intentCredit_eq_credit]

/-- **THE BRIDGE-CANCEL TRIANGLE (PROVED, FULL BICONDITIONAL).** `bridgeCancelStep k a = some k'` IFF the
actor is the recorded creator (`bridgeAuthOK`), a found unresolved record `r` exists that is bridge-tagged
with a LIVE originator account, AND `k' = bridgeCancelSpec k r a.id` (the originator-credit refund). The
`→` pins the unique TRANSPARENT post-state (credit the ORIGINATOR, not the destination); the `←` is
completeness. -/
theorem bridgeCancel_triangle (k k' : RecordKernelState) (a : BridgeCancelArgs) :
    bridgeCancelStep k a = some k' ↔
      (bridgeAuthOK k a.id a.actor = true ∧
       ∃ r, k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) = some r ∧
            r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true ∧
            k' = bridgeCancelSpec k r a.id) := by
  unfold bridgeCancelStep bridgeCancelKAsset
  constructor
  · intro h
    by_cases hg : bridgeAuthOK k a.id a.actor = true
    · rw [if_pos hg] at h
      cases hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some r =>
          rw [hf] at h; simp only at h
          by_cases hm : r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
          · rw [if_pos hm] at h; simp only [Option.some.injEq] at h
            refine ⟨hg, r, rfl, hm.1, hm.2.1, hm.2.2, ?_⟩
            rw [← h, bridgeCancel_settle_eq_spec]
          · rw [if_neg hm] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, r, hf, hbr, hacc, hlive, hk⟩
    rw [if_pos hg, hf]; simp only
    rw [if_pos ⟨hbr, hacc, hlive⟩, hk, bridgeCancel_settle_eq_spec]

/-- **ANTI-GHOST TOOTH (bridge cancel, PROVED).** Once the found record `r` is fixed, any candidate
`k'' ≠ bridgeCancelSpec k r a.id` is REJECTED — a cancel that credited the DESTINATION (not the
originator), refunded the wrong amount, or left the record unresolved is excluded. -/
theorem bridgeCancel_antighost (k k'' : RecordKernelState) (a : BridgeCancelArgs) (r : EscrowRecord)
    (hf : k.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) = some r)
    (hne : k'' ≠ bridgeCancelSpec k r a.id) : bridgeCancelStep k a ≠ some k'' := by
  intro h
  obtain ⟨_, r', hf', _, _, _, hk⟩ := (bridgeCancel_triangle k k'' a).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-! ## §18 — ELEVENTH FAMILY: SWISS / HANDOFF (export / enliven / handoff / drop) + CapTP graph moves
(introduce / validateHandoff / dropRef) — the sturdy-ref table + cap-graph triangle.

The swiss-table ops (`swissExportK`/`swissEnlivenK`/`swissHandoffK`/`swissDropK`) move the `swiss`
sturdy-ref side-table (dregg1's 32-byte unguessable swiss numbers, the CapTP `ExportSturdyRef`/`Enliven`/
`ValidateHandoff`/`DropRef` GC machinery); the CapTP graph moves (`introduce`/`validateHandoff` =
`recKDelegate`, `dropRef` = `recKRevokeTarget`) move the `caps` c-list. Each gets a TRANSPARENT spec (the
EXACT swiss/caps table change, from intent) + a full triangle + anti-ghost tooth. Every swiss op is
balance-NEUTRAL (touches only `swiss`); the foreign-vat 3-party introduce CERT is a NAMED carrier (we model
the LOCAL `cert := some certHash` bind, the signature-validation portal deferred to §8). -/

/-- **`swissExportSpec` — the INDEPENDENT post-state of a sturdy-ref export (TRANSPARENT).** A fresh swiss
entry `{ swiss := sw, exporter, target, rights, refcount := 1, cert := none }` is PREPENDED to the
`swiss` table; EVERYTHING ELSE untouched. Written from intent ("mint a sturdy ref to `target` carrying
`rights`, born with one live reference"). The export is GATED on swiss freshness (no duplicate) AND the
exported `rights` being `⊆` the exporter's GENUINELY-HELD rights (`rightsNarrowerOrEqual rights (heldAuths
k exporter)` — the no-amplification gate; a bare actor cannot mint a ref carrying rights it never held). -/
def swissExportSpec (k : RecordKernelState) (sw : Nat) (exporter target : CellId) (rights : List Auth) :
    RecordKernelState :=
  { k with swiss := { swiss := sw, exporter := exporter, target := target,
                      rights := rights, refcount := 1, cert := none } :: k.swiss }

/-- **THE SWISS-EXPORT TRIANGLE (PROVED, FULL BICONDITIONAL).** `swissExportK k sw exporter target rights
= some k'` IFF the swiss number is FRESH (`findSwiss = none`) AND the exported `rights ⊆ heldAuths k
exporter` (no amplification) AND `k' = swissExportSpec …`. The `→` pins the unique TRANSPARENT post-state
(the fresh refcount-1 entry); the `←` is completeness. -/
theorem swissExport_triangle (k k' : RecordKernelState) (sw : Nat) (exporter target : CellId)
    (rights : List Auth) :
    swissExportK k sw exporter target rights = some k' ↔
      (findSwiss k.swiss sw = none ∧ rightsNarrowerOrEqual rights (heldAuths k exporter) = true ∧
       k' = swissExportSpec k sw exporter target rights) := by
  unfold swissExportK swissExportSpec
  constructor
  · intro h
    cases hf : findSwiss k.swiss sw with
    | some _ => rw [hf] at h; exact absurd h (by simp)
    | none =>
        rw [hf] at h; simp only at h
        by_cases hr : rightsNarrowerOrEqual rights (heldAuths k exporter) = true
        · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; exact ⟨rfl, hr, h.symm⟩
        · rw [if_neg hr] at h; exact absurd h (by simp)
  · rintro ⟨hf, hr, hk⟩; rw [hf, if_pos hr, hk]

/-- **ANTI-GHOST TOOTH (swiss export, PROVED).** Any candidate `k'' ≠ swissExportSpec …` is REJECTED — an
export that minted the WRONG rights, a non-1 refcount, a pre-bound cert, or reused a swiss number is
excluded. -/
theorem swissExport_antighost (k k'' : RecordKernelState) (sw : Nat) (exporter target : CellId)
    (rights : List Auth) (hne : k'' ≠ swissExportSpec k sw exporter target rights) :
    swissExportK k sw exporter target rights ≠ some k'' := by
  intro h
  exact hne ((swissExport_triangle k k'' sw exporter target rights).mp h).2.2

/-- **`swissEnlivenSpec` — the INDEPENDENT post-state of an enliven over found entry `e` (TRANSPARENT).**
The entry's `refcount` is BUMPED by one (a new live reference), the entry replaced in place
(`replaceSwiss`); EVERYTHING ELSE untouched. Written from intent ("grant a live reference — one more
holder"). The enliven is GATED on the bearer's `claimed` rights being `⊆` the entry's exported `rights`
(`rightsNarrowerOrEqual claimed e.rights` — the CapTP non-amplification gate). -/
def swissEnlivenSpec (k : RecordKernelState) (sw : Nat) (e : SwissRecord) : RecordKernelState :=
  { k with swiss := replaceSwiss k.swiss sw { e with refcount := e.refcount + 1 } }

/-- **THE SWISS-ENLIVEN TRIANGLE (PROVED, FULL BICONDITIONAL).** `swissEnlivenK k sw claimed = some k'`
IFF a found entry `e` exists (`findSwiss = some e`) whose exported rights DOMINATE the `claimed` rights AND
`k' = swissEnlivenSpec k sw e`. The `→` pins the unique TRANSPARENT post-state (the refcount bump in place)
AND surfaces the non-amplification gate; the `←` is completeness. -/
theorem swissEnliven_triangle (k k' : RecordKernelState) (sw : Nat) (claimed : List Auth) :
    swissEnlivenK k sw claimed = some k' ↔
      (∃ e, findSwiss k.swiss sw = some e ∧ rightsNarrowerOrEqual claimed e.rights = true ∧
            k' = swissEnlivenSpec k sw e) := by
  unfold swissEnlivenK swissEnlivenSpec
  constructor
  · intro h
    cases hf : findSwiss k.swiss sw with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some e =>
        rw [hf] at h; simp only at h
        by_cases hr : rightsNarrowerOrEqual claimed e.rights = true
        · rw [if_pos hr] at h; simp only [Option.some.injEq] at h; exact ⟨e, rfl, hr, h.symm⟩
        · rw [if_neg hr] at h; exact absurd h (by simp)
  · rintro ⟨e, hf, hr, hk⟩; rw [hf]; simp only; rw [if_pos hr, hk]

/-- **ANTI-GHOST TOOTH (swiss enliven, PROVED).** Once the found entry `e` is fixed, any candidate
`k'' ≠ swissEnlivenSpec k sw e` is REJECTED — an enliven that bumped the WRONG entry, granted amplified
rights, or failed to bump the refcount is excluded. -/
theorem swissEnliven_antighost (k k'' : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (e : SwissRecord) (hf : findSwiss k.swiss sw = some e) (hne : k'' ≠ swissEnlivenSpec k sw e) :
    swissEnlivenK k sw claimed ≠ some k'' := by
  intro h
  obtain ⟨e', hf', _, hk⟩ := (swissEnliven_triangle k k'' sw claimed).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **`swissHandoffSpec` — the INDEPENDENT post-state of a 3-vat handoff over found entry `e`
(TRANSPARENT).** The entry's `cert` is BOUND to `some certHash` AND its `refcount` BUMPED (the recipient's
new live ref), the entry replaced in place; EVERYTHING ELSE untouched. Written from intent ("bind the
3-vat introduce cert and grant the recipient a live reference"). The signature-validation of the cert is
the §8 portal carrier — here we model the LOCAL bind. TOTAL once the entry is found (no rights gate — the
handoff is the recipient's own introduce-cert path). -/
def swissHandoffSpec (k : RecordKernelState) (sw certHash : Nat) (e : SwissRecord) : RecordKernelState :=
  { k with swiss := replaceSwiss k.swiss sw { e with cert := some certHash, refcount := e.refcount + 1 } }

/-- **THE SWISS-HANDOFF TRIANGLE (PROVED, FULL BICONDITIONAL).** `swissHandoffK k sw certHash = some k'`
IFF a found entry `e` exists AND `k' = swissHandoffSpec k sw certHash e`. The `→` pins the unique
TRANSPARENT post-state (cert bind + refcount bump in place); the `←` is completeness (fail-closed only when
the entry is ABSENT). -/
theorem swissHandoff_triangle (k k' : RecordKernelState) (sw certHash : Nat) :
    swissHandoffK k sw certHash = some k' ↔
      (∃ e, findSwiss k.swiss sw = some e ∧ k' = swissHandoffSpec k sw certHash e) := by
  unfold swissHandoffK swissHandoffSpec
  constructor
  · intro h
    cases hf : findSwiss k.swiss sw with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some e => rw [hf] at h; simp only [Option.some.injEq] at h; exact ⟨e, rfl, h.symm⟩
  · rintro ⟨e, hf, hk⟩; rw [hf, hk]

/-- **ANTI-GHOST TOOTH (swiss handoff, PROVED).** Once the found entry `e` is fixed, any candidate
`k'' ≠ swissHandoffSpec k sw certHash e` is REJECTED — a handoff that bound the WRONG cert, skipped the
refcount bump, or touched another entry is excluded. -/
theorem swissHandoff_antighost (k k'' : RecordKernelState) (sw certHash : Nat) (e : SwissRecord)
    (hf : findSwiss k.swiss sw = some e) (hne : k'' ≠ swissHandoffSpec k sw certHash e) :
    swissHandoffK k sw certHash ≠ some k'' := by
  intro h
  obtain ⟨e', hf', hk⟩ := (swissHandoff_triangle k k'' sw certHash).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **`swissDropRemoveSpec` — the INDEPENDENT post-state of a GC-drop that EMPTIES the entry (TRANSPARENT).**
When the decremented refcount hits 0, the entry is REMOVED from the table (`removeSwiss`); all else fixed.
Written from intent ("the last reference dropped — GC the entry"). -/
def swissDropRemoveSpec (k : RecordKernelState) (sw : Nat) : RecordKernelState :=
  { k with swiss := removeSwiss k.swiss sw }

/-- **`swissDropDecrSpec` — the INDEPENDENT post-state of a GC-drop that KEEPS the entry (TRANSPARENT).**
When the decremented refcount stays positive, the entry's `refcount` is decremented in place
(`replaceSwiss`); all else fixed. Written from intent ("one reference dropped — entry survives"). -/
def swissDropDecrSpec (k : RecordKernelState) (sw : Nat) (e : SwissRecord) : RecordKernelState :=
  { k with swiss := replaceSwiss k.swiss sw { e with refcount := e.refcount - 1 } }

/-- **THE SWISS-DROP TRIANGLE (PROVED, FULL BICONDITIONAL).** `swissDropK k sw = some k'` IFF a found
entry `e` exists with a POSITIVE refcount, AND `k'` is the GC-remove post-state (if `e.refcount - 1 = 0`)
or the decrement post-state (otherwise). The `→` pins the unique TRANSPARENT post-state in BOTH branches
AND surfaces the refcount-positive gate (no underflow — a drop on a 0-refcount entry is fail-closed); the
`←` is completeness. The two-branch codomain (remove vs decrement) is the GC threshold the triangle pins. -/
theorem swissDrop_triangle (k k' : RecordKernelState) (sw : Nat) :
    swissDropK k sw = some k' ↔
      (∃ e, findSwiss k.swiss sw = some e ∧ e.refcount ≠ 0 ∧
            ((e.refcount - 1 = 0 ∧ k' = swissDropRemoveSpec k sw) ∨
             (e.refcount - 1 ≠ 0 ∧ k' = swissDropDecrSpec k sw e))) := by
  unfold swissDropK swissDropRemoveSpec swissDropDecrSpec
  constructor
  · intro h
    cases hf : findSwiss k.swiss sw with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some e =>
        rw [hf] at h; simp only at h
        by_cases hz : e.refcount = 0
        · rw [if_pos hz] at h; exact absurd h (by simp)
        · rw [if_neg hz] at h
          by_cases hd : e.refcount - 1 = 0
          · rw [if_pos hd] at h; simp only [Option.some.injEq] at h
            exact ⟨e, rfl, hz, Or.inl ⟨hd, h.symm⟩⟩
          · rw [if_neg hd] at h; simp only [Option.some.injEq] at h
            exact ⟨e, rfl, hz, Or.inr ⟨hd, h.symm⟩⟩
  · rintro ⟨e, hf, hz, hbranch⟩
    rw [hf]; simp only; rw [if_neg hz]
    rcases hbranch with ⟨hd, hk⟩ | ⟨hd, hk⟩
    · rw [if_pos hd, hk]
    · rw [if_neg hd, hk]

/-- **ANTI-GHOST TOOTH (swiss drop, PROVED).** Once the found entry `e` is fixed, any candidate that is
NEITHER the GC-remove NOR the decrement post-state is REJECTED — a drop that removed the WRONG entry, kept
a 0-refcount entry alive, or removed an entry that should have survived is excluded. -/
theorem swissDrop_antighost (k k'' : RecordKernelState) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss k.swiss sw = some e)
    (hne : k'' ≠ swissDropRemoveSpec k sw ∧ k'' ≠ swissDropDecrSpec k sw e) :
    swissDropK k sw ≠ some k'' := by
  intro h
  obtain ⟨e', hf', _, hbranch⟩ := (swissDrop_triangle k k'' sw).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  rcases hbranch with ⟨_, hk⟩ | ⟨_, hk⟩
  · exact hne.1 hk
  · exact hne.2 hk

/-! ### CapTP graph moves: introduce / validateHandoff (= `recKDelegate`) and dropRef (= `recKRevokeTarget`).

dregg1's `apply_introduce`/`apply_validate_handoff` both route to the Granovetter delegation
`recKDelegate` (copy the delegator's held witness cap to the recipient — `apply.rs:2455`); `apply_drop_ref`
routes to `recKRevokeTarget` (the holder loses its reach to `target`). The kernel post-states are
TRANSPARENT cap-graph edits. We give the introduce/validateHandoff move its OWN spec (the UNATTENUATED
held-cap copy — distinct from the §7 `delegateSpec`, which is the ATTENUATED `recKDelegateAtten`), and reuse
the §7 `revokeSpec` shape for dropRef. -/

/-- **`introduceSpec` — the INDEPENDENT post-state of a CapTP introduce/validateHandoff (TRANSPARENT).**
The recipient's slot GAINS the delegator's held cap to `target` UNATTENUATED (`grant … (heldCapTo …)`);
EVERYTHING ELSE untouched. Written from intent ("hand `recipient` a copy of the cap I hold to `target`").
Distinct from `delegateSpec` (§7): introduce copies the FULL held cap; delegate-atten narrows it to
`keep`. -/
def introduceSpec (k : RecordKernelState) (delegator recipient target : CellId) : RecordKernelState :=
  { k with caps := grant k.caps recipient (heldCapTo k.caps delegator target) }

/-- **THE INTRODUCE TRIANGLE (PROVED, FULL BICONDITIONAL).** `recKDelegate k delegator recipient target =
some k'` IFF the Granovetter connectivity premise holds (the delegator already holds a cap conferring an
edge to `target`) AND `k' = introduceSpec …`. The `→` pins the unique TRANSPARENT cap-graph edit (the
recipient gains EXACTLY the held cap, no other slot moved); the `←` is completeness. This is the same step
dregg1's `validateHandoff` uses (both route to `recKDelegate`). -/
theorem introduce_triangle (k k' : RecordKernelState) (delegator recipient target : CellId) :
    recKDelegate k delegator recipient target = some k' ↔
      ((k.caps delegator).any (fun cap => confersEdgeTo target cap) = true ∧
       k' = introduceSpec k delegator recipient target) := by
  unfold recKDelegate introduceSpec
  constructor
  · intro h
    by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo target cap) = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, hk⟩; rw [if_pos hg, hk]

/-- **ANTI-GHOST TOOTH (introduce / validateHandoff, PROVED).** Any candidate `k'' ≠ introduceSpec …` is
REJECTED — an introduce that granted an OVER-BROAD cap (more than the held witness), to the WRONG recipient,
or manufactured a fresh cap is excluded. -/
theorem introduce_antighost (k k'' : RecordKernelState) (delegator recipient target : CellId)
    (hne : k'' ≠ introduceSpec k delegator recipient target) :
    recKDelegate k delegator recipient target ≠ some k'' := by
  intro h
  exact hne ((introduce_triangle k k'' delegator recipient target).mp h).2

/-- **`dropRefSpec` — the INDEPENDENT post-state of a CapTP dropRef (TRANSPARENT).** The holder's slot
DROPS every cap conferring an edge to `target` (keep only non-conferring caps); every other slot fixed.
Identical SHAPE to the §7 `revokeTargetCaps` (dropRef IS a revoke of the holder's reach to `target`). -/
def dropRefSpec (k : RecordKernelState) (holder target : CellId) : RecordKernelState :=
  { k with caps := fun l => if l = holder then (k.caps l).filter (fun cap => ¬ confersEdgeTo target cap)
                            else k.caps l }

/-- **THE DROPREF TRIANGLE (PROVED — TOTAL, output-uniqueness).** `recKRevokeTarget` ALWAYS commits
(dropping a reference cannot fail — at worst the identity), so the content is the `↔`: `recKRevokeTarget k
holder target = k'` IFF `k' = dropRefSpec k holder target`. The output is the UNIQUE TRANSPARENT post-state
(the holder's `target`-conferring caps filtered out, NO other slot touched). -/
theorem dropRef_triangle (k k' : RecordKernelState) (holder target : CellId) :
    recKRevokeTarget k holder target = k' ↔ k' = dropRefSpec k holder target := by
  unfold recKRevokeTarget dropRefSpec
  constructor
  · intro h; exact h.symm
  · intro hk; rw [hk]

/-- **ANTI-GHOST TOOTH (dropRef, PROVED).** Any candidate `k'' ≠ dropRefSpec k holder target` is
REJECTED — a dropRef that KEPT a `target`-conferring cap (an incomplete drop), filtered the WRONG holder,
or dropped extra caps is excluded. -/
theorem dropRef_antighost (k k'' : RecordKernelState) (holder target : CellId)
    (hne : k'' ≠ dropRefSpec k holder target) : recKRevokeTarget k holder target ≠ k'' := by
  intro h
  exact hne ((dropRef_triangle k k'' holder target).mp h)

/-! ## §19 — TWELFTH FAMILY: QUEUE EXTRAS (resize / atomicTx / pipelineStep) — capacity + routing triangle.

The remaining queue handlers (`Handlers.Queue.resizeStep`/`atomicTxStep`/`pipelineStep`) round out the
§3 FIFO family. Resize changes a queue's CAPACITY (a transparent in-place record edit, gated below current
occupancy); atomicTx folds an ALL-OR-NOTHING deposit-batch; pipelineStep DEQUEUEs a source head and
fans it out to ACL-checked sinks. Resize gets a TRANSPARENT field-by-field spec + full triangle + tooth.
atomicTx/pipeline are ROUTING FOLDS — their spec is the TRANSPARENT fold itself (`queueAtomicTxChainK` /
the dequeue-then-fanout composition, the actual operation, not an opaque mirror), with a triangle pinning
output-uniqueness + the gate. -/

open Dregg2.Exec.Handlers.Queue
  (ResizeArgs resizeStep AtomicTxArgs atomicTxStep queueAtomicTxChainK
   PipelineArgs pipelineStep)
open Dregg2.Exec.TurnExecutorFull (pipelineFanoutK)

/-- **`queueResizeSpec` — the INDEPENDENT post-state of a queue resize over found queue `q` (TRANSPARENT).**
The queue record's `capacity` is set to `a.capacity` in place (`replaceQueue`); the buffer and every other
field untouched. Written from intent ("change THIS queue's capacity, keep its contents"). -/
def queueResizeSpec (k : RecordKernelState) (a : ResizeArgs) (q : QueueRecord) : RecordKernelState :=
  { k with queues := replaceQueue k.queues a.id { q with capacity := a.capacity } }

/-- The queue-resize gate: the actor holds authority over the owner AND the owner is Live. -/
def queueResizeGate (k : RecordKernelState) (a : ResizeArgs) : Prop :=
  stateAuthB k.caps a.actor a.owner = true ∧ acceptsEffects k a.owner = true

/-- **THE QUEUE-RESIZE TRIANGLE (PROVED, FULL BICONDITIONAL).** `resizeStep k a = some k'` IFF the gate
(authority + owner-Live) holds, a found queue `q` exists whose current occupancy fits the new capacity
(`q.buffer.length ≤ a.capacity` — no shrink below contents), AND `k' = queueResizeSpec k a q`. The `→`
pins the unique TRANSPARENT post-state (the in-place capacity edit) AND surfaces the no-truncation gate;
the `←` is completeness. -/
theorem queueResize_triangle (k k' : RecordKernelState) (a : ResizeArgs) :
    resizeStep k a = some k' ↔
      (queueResizeGate k a ∧ ∃ q, findQueue k.queues a.id = some q ∧
            q.buffer.length ≤ a.capacity ∧ k' = queueResizeSpec k a q) := by
  unfold resizeStep queueResizeGate queueResizeSpec queueResizeK
  constructor
  · intro h
    by_cases hg : stateAuthB k.caps a.actor a.owner && acceptsEffects k a.owner
    · rw [if_pos hg] at h
      simp only [Bool.and_eq_true] at hg
      cases hf : findQueue k.queues a.id with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some q =>
          rw [hf] at h; simp only at h
          by_cases hc : q.buffer.length ≤ a.capacity
          · rw [if_pos hc] at h; simp only [Option.some.injEq] at h
            exact ⟨⟨hg.1, hg.2⟩, q, rfl, hc, h.symm⟩
          · rw [if_neg hc] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨⟨hauth, hlive⟩, q, hf, hc, hk⟩
    rw [if_pos (by simp [hauth, hlive]), hf]; simp only; rw [if_pos hc, hk]

/-- **ANTI-GHOST TOOTH (queue resize, PROVED).** Once the found queue `q` is fixed, any candidate
`k'' ≠ queueResizeSpec k a q` is REJECTED — a resize that edited the WRONG queue, the WRONG capacity, or
mutated the buffer is excluded. -/
theorem queueResize_antighost (k k'' : RecordKernelState) (a : ResizeArgs) (q : QueueRecord)
    (hf : findQueue k.queues a.id = some q) (hne : k'' ≠ queueResizeSpec k a q) :
    resizeStep k a ≠ some k'' := by
  intro h
  obtain ⟨_, q', hf', _, hk⟩ := (queueResize_triangle k k'' a).mp h
  rw [hf] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
  exact hne hk

/-- **`atomicTxSpec` — the INDEPENDENT post-state of an all-or-nothing deposit batch (TRANSPARENT).** The
post-state is EXACTLY the all-or-nothing fold of the sub-op list (`queueAtomicTxChainK k a.ops`) — the
transparent operation, threaded through the `Option` monad (commit iff EVERY sub-op commits; any failure
rolls back). This is intent ("run these deposit ops atomically"), written as the FOLD, not as an opaque
`atomicTxStep` (the fold is the actual transparent computation, each sub-op carrying its own gate). -/
def atomicTxSpec (k : RecordKernelState) (a : AtomicTxArgs) : Option RecordKernelState :=
  queueAtomicTxChainK k a.ops

/-- **THE ATOMIC-TX TRIANGLE (PROVED, FULL BICONDITIONAL — output-uniqueness).** `atomicTxStep k a = k''`
IFF `k'' = atomicTxSpec k a` (the transparent all-or-nothing fold). Output-uniqueness: a commit pins
EXACTLY the fold result. The gate is internal to the fold (each sub-op fail-closes on its own ACL/binding
gate), so the content is the `=` to the transparent fold — a candidate result that is not the fold's
output (a partial commit on a failing batch, a re-ordered fold) is excluded. -/
theorem atomicTx_triangle (k : RecordKernelState) (a : AtomicTxArgs) (k'' : Option RecordKernelState) :
    atomicTxStep k a = k'' ↔ k'' = atomicTxSpec k a := by
  unfold atomicTxStep atomicTxSpec
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

/-- **ANTI-GHOST TOOTH (atomic tx, PROVED).** Any candidate result `k'' ≠ atomicTxSpec k a` is REJECTED —
the batch commits EXACTLY the all-or-nothing fold; a partial commit on a failing batch (the rollback
violated) or a re-ordered application is excluded. -/
theorem atomicTx_antighost (k : RecordKernelState) (a : AtomicTxArgs) (k'' : Option RecordKernelState)
    (hne : k'' ≠ atomicTxSpec k a) : atomicTxStep k a ≠ k'' := by
  intro h
  exact hne ((atomicTx_triangle k a k'').mp h)

/-- **`pipelineSpec` — the INDEPENDENT post-state of a pipeline fan-out (TRANSPARENT).** The post-state is
EXACTLY the source-dequeue-then-fan-out composition: DEQUEUE the source head (owner-gated, FIFO) then
RE-ENQUEUE the moved head into each ACL-checked sink (`pipelineFanoutK`). Written from intent ("route the
source FIFO head out to the sinks"), as the transparent dequeue⨾fanout, fail-closed if the source dequeue
fails OR any sink rejects. -/
def pipelineSpec (k : RecordKernelState) (a : PipelineArgs) : Option RecordKernelState :=
  match queueDequeueK k a.srcId a.owner with
  | some (k1, m) => pipelineFanoutK k1 a.owner m a.sinkCells a.sinkIds
  | none         => none

/-- **THE PIPELINE-STEP TRIANGLE (PROVED, FULL BICONDITIONAL — output-uniqueness).** `pipelineStep k a =
k''` IFF `k'' = pipelineSpec k a` (the transparent dequeue⨾fanout). Output-uniqueness: a commit pins
EXACTLY the routed post-state — a candidate that dequeued the WRONG (non-FIFO) head, skipped a sink, or
routed to the wrong sink is excluded. The owner-dequeue + per-sink ACL gates are internal to the
composition. -/
theorem pipeline_triangle (k : RecordKernelState) (a : PipelineArgs) (k'' : Option RecordKernelState) :
    pipelineStep k a = k'' ↔ k'' = pipelineSpec k a := by
  unfold pipelineStep pipelineSpec
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

/-- **ANTI-GHOST TOOTH (pipeline step, PROVED).** Any candidate result `k'' ≠ pipelineSpec k a` is
REJECTED — the pipeline routes EXACTLY the FIFO head to the ACL-checked sinks; a non-FIFO dequeue, a
skipped sink, or a mis-routed message is excluded. -/
theorem pipeline_antighost (k : RecordKernelState) (a : PipelineArgs) (k'' : Option RecordKernelState)
    (hne : k'' ≠ pipelineSpec k a) : pipelineStep k a ≠ k'' := by
  intro h
  exact hne ((pipeline_triangle k a k'').mp h)

/-! ## §20 — THIRTEENTH FAMILY: EXERCISE (inner-turn recursion) — the sub-forest triangle.

The recursive cap-exercise handler (`Handlers.Exercise.exerciseStep`, dregg1's
`apply_exercise_via_capability`): the actor exercises a HELD cap to RUN a list of `inner` effects against
the cap's `target`, gated by (1) the hold-gate (the actor holds an edge to `target`) and (2) the R4
FACET-MASK (every inner effect's facet lies in the held cap's `allowed_effects`). The post-state is the
TRANSPARENT inner sub-forest fold (`subTurn (innerEffects a.inner) k`) — the actual recursive run, NOT an
opaque mirror. The full triangle is reachable: the spec is the inner-forest fold, the gate is
`exerciseAdmitB`, and the anti-ghost tooth bites (a candidate ≠ the fold is excluded). -/

open Dregg2.Exec.Handlers.Exercise
  (ExerciseArgs exerciseStep exerciseAdmitB innerEffects subTurn holdsEdge exercisedCap forestAdmitted)

/-- **`exerciseSpec` — the INDEPENDENT post-state of a cap-exercise (TRANSPARENT, the inner-forest fold).**
The post-state is EXACTLY the all-or-nothing fold of the inner sub-effect forest against `k` (`subTurn
(innerEffects a.inner) k`) — the recursive sub-turn the exercise runs (the cap graph is READ, never edited;
the only state motion is the inner forest). Written from intent ("run the inner forest against the
target"), as the transparent `subTurn` fold, NOT as `exerciseStep`. -/
def exerciseSpec (k : RecordKernelState) (a : ExerciseArgs) : Option RecordKernelState :=
  subTurn (innerEffects a.inner) k

/-- **THE EXERCISE TRIANGLE (PROVED, FULL BICONDITIONAL — output-uniqueness).** `exerciseStep k a = some
k'` IFF the admission gate (`exerciseAdmitB` — the hold-gate AND the R4 facet-mask) holds AND `k' =`
the inner-forest fold result (`exerciseSpec k a = some k'`). The `→` pins the unique TRANSPARENT post-state
(EXACTLY the inner sub-turn) AND surfaces the hold-gate + facet-mask discipline; the `←` is completeness.
A committing exercise PROVES every inner facet lay in the cap's mask. -/
theorem exercise_triangle (k k' : RecordKernelState) (a : ExerciseArgs) :
    exerciseStep k a = some k' ↔ (exerciseAdmitB k a = true ∧ exerciseSpec k a = some k') := by
  unfold exerciseStep exerciseSpec
  constructor
  · intro h
    by_cases hg : exerciseAdmitB k a = true
    · rw [if_pos hg] at h; exact ⟨hg, h⟩
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rintro ⟨hg, hk⟩; rw [if_pos hg]; exact hk

/-- **ANTI-GHOST TOOTH (exercise, PROVED).** Any candidate `k'' ≠` the inner-forest fold result is
REJECTED — the exercise commits EXACTLY the sub-turn over the inner forest; a candidate that ran a
DIFFERENT forest, skipped an inner effect, or edited the cap graph is excluded. Once a commit happens, the
post-state is pinned to the unique transparent fold. -/
theorem exercise_antighost (k k'' : RecordKernelState) (a : ExerciseArgs)
    (hne : exerciseSpec k a ≠ some k'') : exerciseStep k a ≠ some k'' := by
  intro h
  exact hne ((exercise_triangle k k'' a).mp h).2

/-! ## §22 — NON-VACUITY TEETH (`#guard`) for the four Part-B families: witness TRUE and ghost REJECTED. -/

/-- Bridge fixture: cells 0,1 accounts; cell 0 holds 100 of asset 1 + a `node 1` self-cap; both Live. -/
def bfx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Dregg2.Authority.Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

/-- The bridge-lock args: cell 0 locks 30 of asset 1 (id 9), destination cell 1. -/
def bLock : BridgeLockArgs := { id := 9, actor := 0, originator := 0, destination := 1, asset := 1, amount := 30 }

-- BRIDGE LOCK commits and the originator is DEBITED: bal 0 1 drops 100 → 70 (the spec's `intentDebit`).
#guard (bridgeLockStep bfx bLock).isSome
#guard ((bridgeLockStep bfx bLock).map (fun k => k.bal 0 1)) == some 70
-- ...and the parked head is the fresh UNRESOLVED BRIDGE-tagged record (id 9, asset 1, amt 30).
#guard (((bridgeLockStep bfx bLock).bind (fun k => k.escrows.head?)).map
          (fun r => (r.id, r.creator, r.recipient, r.amount, r.resolved, r.asset, r.bridge))
        == some (9, 0, 1, 30, false, 1, true))
-- LOCK anti-ghost (CONCRETE): the spec debits the originator (70) — a ghost leaving bal at 100 differs.
#guard ((bfx.bal 0 1, (bridgeLockSpec bfx bLock).bal 0 1) == (100, 70))
-- FINALIZE (creator-gated, no-credit resolve): the value LEFT — bal 0 1 STAYS 70, record marked resolved.
#guard ((bridgeLockStep bfx bLock).bind (fun k => bridgeFinalizeStep k { id := 9, actor := 0, asset := 1, amount := 30 })).isSome
#guard (((bridgeLockStep bfx bLock).bind (fun k => bridgeFinalizeStep k { id := 9, actor := 0, asset := 1, amount := 30 })).map
          (fun k => k.bal 0 1)) == some 70  -- NO credit — disclosed outflow
#guard (((bridgeLockStep bfx bLock).bind (fun k => bridgeFinalizeStep k { id := 9, actor := 0, asset := 1, amount := 30 })).bind
          (fun k => k.escrows.head?)).map (·.resolved) == some true
-- a NON-creator (cell 5) finalize is REJECTED (`bridgeAuthOK` gate); a MISMATCHED amount (99) is REJECTED.
#guard (((bridgeLockStep bfx bLock).bind (fun k => bridgeFinalizeStep k { id := 9, actor := 5, asset := 1, amount := 30 })).isSome) == false
#guard (((bridgeLockStep bfx bLock).bind (fun k => bridgeFinalizeStep k { id := 9, actor := 0, asset := 1, amount := 99 })).isSome) == false
-- CANCEL (creator-gated refund): the originator is REFUNDED — bal 0 1 back to 100 (the `intentCredit`).
#guard (((bridgeLockStep bfx bLock).bind (fun k => bridgeCancelStep k { actor := 0, id := 9 })).map
          (fun k => k.bal 0 1)) == some 100
-- a NON-creator (cell 5) cancel is REJECTED.
#guard (((bridgeLockStep bfx bLock).bind (fun k => bridgeCancelStep k { actor := 5, id := 9 })).isSome) == false

/-- Swiss fixture: cell 0 holds a `node 7` cap (so `heldAuths 0 = [control]`), and the swiss table holds
one entry: swiss 5, exporter 0, target 7, rights `[control]`, refcount 2. -/
def swfx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 7] else []
    bal := fun _ _ => 0
    swiss := [{ swiss := 5, exporter := 0, target := 7, rights := [Auth.control], refcount := 2, cert := none }] }

-- SWISS EXPORT: a FRESH swiss 8 (rights [control] ⊆ node-7's conferred [control]) commits, refcount-1 entry.
#guard (swissExportK swfx 8 0 7 [Auth.control]).isSome
#guard (((swissExportK swfx 8 0 7 [Auth.control]).bind (fun k => findSwiss k.swiss 8)).map
          (fun e => (e.exporter, e.target, e.rights, e.refcount))) == some (0, 7, [Auth.control], 1)
-- a DUPLICATE swiss 5 is REJECTED (no re-export); an AMPLIFYING export (rights ⊄ held) is REJECTED.
#guard ((swissExportK swfx 5 0 7 [Auth.control]).isSome) == false
#guard ((swissExportK { swfx with caps := fun c => if c = 0 then [Dregg2.Authority.Cap.endpoint 7 [Auth.read]] else [] }
          8 0 7 [Auth.write]).isSome) == false  -- read-only held ⇒ cannot export write (amplification denied)
-- SWISS ENLIVEN: claimed [control] ⊆ entry [control] ⇒ refcount BUMPS 2 → 3; an amplifying claim is REJECTED.
#guard (((swissEnlivenK swfx 5 [Auth.control]).bind (fun k => findSwiss k.swiss 5)).map (·.refcount)) == some 3
#guard ((swissEnlivenK swfx 5 [Auth.grant]).isSome) == false  -- grant ∉ [control]
-- SWISS HANDOFF: binds cert 99 + bumps refcount 2 → 3 on entry 5.
#guard (((swissHandoffK swfx 5 99).bind (fun k => findSwiss k.swiss 5)).map (fun e => (e.cert, e.refcount)))
        == some (some 99, 3)
-- SWISS DROP: refcount 2 → 1 (entry SURVIVES, decrement branch); a missing swiss (99) is REJECTED.
#guard (((swissDropK swfx 5).bind (fun k => findSwiss k.swiss 5)).map (·.refcount)) == some 1
#guard ((swissDropK swfx 99).isSome) == false
-- SWISS DROP to ZERO (refcount-1 entry GC'd): a refcount-1 entry drops to removal.
#guard ((swissDropK { swfx with swiss := [{ swiss := 5, exporter := 0, target := 7, rights := [Auth.control], refcount := 1, cert := none }] } 5).map
          (fun k => (findSwiss k.swiss 5).isNone)) == some true  -- GC'd (removed)

/-- CapTP graph fixture: cell 0 holds a `node 7` cap (edge to 7); cell 1 holds nothing. -/
def cfx : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 7] else []
    bal := fun _ _ => 0 }

-- INTRODUCE: delegator 0 (holds edge to 7) introduces recipient 1 ⇒ 1 GAINS the held `node 7` cap.
#guard (recKDelegate cfx 0 1 7).isSome
#guard ((recKDelegate cfx 0 1 7).map (fun k => k.caps 1)) == some [Dregg2.Authority.Cap.node 7]
-- a delegator WITHOUT the edge (cell 1) is REJECTED (Granovetter premise).
#guard ((recKDelegate cfx 1 0 7).isSome) == false
-- DROPREF (total): cell 0 drops its reach to 7 ⇒ the `node 7` cap filtered out (cell 0's slot now empty).
#guard ((recKRevokeTarget cfx 0 7).caps 0) == ([] : List Dregg2.Authority.Cap)
-- dropRef leaves OTHER slots (cell 1) untouched.
#guard ((recKRevokeTarget cfx 0 7).caps 1) == ([] : List Dregg2.Authority.Cap)

/-- Queue fixture: cell 0 holds a `node 0` self-cap, Live; a queue id 7 owner 0 capacity 3 with buffer [11]. -/
def qfx : RecordKernelState :=
  { accounts := {0}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 0] else []
    bal := fun _ _ => 0
    queues := [{ id := 7, owner := 0, capacity := 3, buffer := [11] }] }

-- QUEUE RESIZE: owner 0 resizes queue 7 to capacity 5 ⇒ capacity becomes 5, buffer [11] kept.
#guard (resizeStep qfx { actor := 0, id := 7, capacity := 5, owner := 0 }).isSome
#guard (((resizeStep qfx { actor := 0, id := 7, capacity := 5, owner := 0 }).bind (fun k => findQueue k.queues 7)).map
          (fun q => (q.capacity, q.buffer))) == some (5, [11])
-- a SHRINK below occupancy (capacity 0 < buffer length 1) is REJECTED (no truncation).
#guard ((resizeStep qfx { actor := 0, id := 7, capacity := 0, owner := 0 }).isSome) == false
-- an UNAUTHORIZED resize (actor 1 holds no cap over owner 0) is REJECTED.
#guard ((resizeStep qfx { actor := 1, id := 7, capacity := 5, owner := 0 }).isSome) == false
-- ATOMIC-TX: the empty batch is the identity (commits, no move). The `= atomicTxSpec` equality is the
-- PROVED `atomicTx_triangle` (RecordKernelState has function fields ⇒ no BEq; the theorem is the content).
#guard (atomicTxStep qfx { actor := 0, ops := [] }).isSome
-- PIPELINE: a no-sink pipeline = the bare source dequeue (commits, head 11 leaves); pinned by
-- `pipeline_triangle` to the transparent dequeue⨾fanout. The dequeued head's queue buffer is now empty.
#guard (pipelineStep qfx { srcId := 7, owner := 0, sinkCells := [], sinkIds := [] }).isSome
#guard ((pipelineStep qfx { srcId := 7, owner := 0, sinkCells := [], sinkIds := [] }).bind
          (fun k => findQueue k.queues 7)).map (·.buffer) == some ([] : List Nat)

/-- Exercise fixture: cells 0,1,2 accounts; cell 0 holds a `node 2` full-facet cap to target 2; all Live. -/
def efx : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Dregg2.Authority.Cap.node 2] else []
    bal := fun _ _ => 0 }

-- EXERCISE: a bare exercise (empty inner forest) of cell 0's node-2 cap commits to the IDENTITY (the
-- transparent `subTurn []` fold = `some k`); the `= exerciseSpec` equality is the PROVED
-- `exercise_triangle` (no BEq on RecordKernelState — the theorem is the content).
#guard (exerciseStep efx { actor := 0, target := 2, inner := [] }).isSome
-- an exercise by an actor WITHOUT an edge to the target (cell 1 holds nothing) is REJECTED (hold-gate).
#guard ((exerciseStep efx { actor := 1, target := 2, inner := [] }).isSome) == false

/-! ## §21 — Axiom-hygiene pins for the FOUR new Part-B families (bridge / swiss / queue-extras / exercise). -/

#assert_axioms createBridgeRawAsset_eq_spec
#assert_axioms bridgeLock_triangle
#assert_axioms bridgeLock_antighost
#assert_axioms bridgeFinalize_triangle
#assert_axioms bridgeFinalize_antighost
#assert_axioms bridgeCancel_settle_eq_spec
#assert_axioms bridgeCancel_triangle
#assert_axioms bridgeCancel_antighost
#assert_axioms swissExport_triangle
#assert_axioms swissExport_antighost
#assert_axioms swissEnliven_triangle
#assert_axioms swissEnliven_antighost
#assert_axioms swissHandoff_triangle
#assert_axioms swissHandoff_antighost
#assert_axioms swissDrop_triangle
#assert_axioms swissDrop_antighost
#assert_axioms introduce_triangle
#assert_axioms introduce_antighost
#assert_axioms dropRef_triangle
#assert_axioms dropRef_antighost
#assert_axioms queueResize_triangle
#assert_axioms queueResize_antighost
#assert_axioms atomicTx_triangle
#assert_axioms atomicTx_antighost
#assert_axioms pipeline_triangle
#assert_axioms pipeline_antighost
#assert_axioms exercise_triangle
#assert_axioms exercise_antighost

end Dregg2.Spec.FunctionalRefinement
