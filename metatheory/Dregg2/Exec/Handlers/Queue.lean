/-
# Dregg2.Exec.Handlers.Queue — the QUEUE (FIFO + refundable deposit) handler batch.

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler` (read that module first:
the `EffectHandler` record bundling `step`/`delta`/`auth`/`admission`/`trace` WITH the forced obligation
proofs `auth_gated`/`admission_gated`/`conserves`, the registry coproduct, and the generic
`turn_conserves`). We register one handler per effect of the QUEUE cluster — `queueAllocateA`,
`queueEnqueueA`, `queueDequeueA`, `queueResizeA`, `queueAtomicTxA`, `queuePipelineStepA` — each reusing
that effect's ALREADY-PROVED kernel step + conservation lemma + the queue-cell authority gate from
`Dregg2.Exec.RecordKernel`/`TurnExecutorFull`. We do NOT touch `TurnExecutorFull`'s
`execFullA`/`FullActionA` (the cutover is a later step); we only IMPORT and REUSE.

Conservation faces:

  * **bal-NEUTRAL ORDER ops** (`queueAllocateA`/`queueResizeA`). Allocate creates a fresh queue record;
    resize changes capacity. Both touch ONLY `queues`, never `bal`/`escrows` — the combined per-asset
    measure is unchanged (`delta = 0`), discharged by `queueAllocateK_balNeutral`/`queueResizeK_balNeutral`.

  * **COMBINED-conserving DEPOSIT ops** (`queueEnqueueA`/`queueDequeueA`). dregg1's enqueue PARKS a
    refundable anti-spam deposit (the sender's `bal` ledger DROPS, the shared holding-store RISES — the
    bare ledger genuinely MOVES, the COMBINED measure is fixed); dequeue REFUNDS it (ledger rises, store
    drops). The combined per-asset measure is unchanged (`delta = 0`), discharged by the proved
    `queueEnqueueDepositK_conserves_combined` / `queueDequeueRefundK_conserves_combined`. The bare ledger
    debit/credit is REAL (witnessed by `queueEnqueueDepositK_debits`) — only the combined sum is held.

  * **bal-NEUTRAL ROUTING ops** (`queueAtomicTxA`/`queuePipelineStepA`). The atomic batch folds the
    deposit enqueue/dequeue sub-ops all-or-nothing (each combined-conserving, so the fold is — proved by
    induction reusing the per-op `conserves`); the pipeline step dequeues a source head and fans it out
    into each ACL-checked sink (combined-conserving: dequeue + fan-out are both bal-neutral on `queues`).

## CLOSING THE QUEUE↔DEPOSIT BINDING HOLE (codex P0-1).

The kernel `queueDequeueRefundK k id actor depId` credits a CALLER-SUPPLIED deposit-record `depId`,
looked up in the GLOBAL `escrows` table, to the dequeuer `actor` — with NO binding between the named
record and the message being dequeued (or even the queue). So a dequeuer can name an UNRELATED unresolved
deposit (one parked FOR someone else, by someone else) and have its `amount` of its `asset` CREDITED to
itself — draining a deposit that was never destined to them. (`recTotalAsset` stays conserved
because it is a settle, so the conservation keystone does NOT catch it — this is a pure AUTHORITY hole.)

The fix is a WRAP: `dequeueBindStep` resolves the deposit record by `depId` and admits the refund ONLY
when `r.recipient = actor` — the deposit must be DESTINED to the dequeuer. In the honest flow the deposit
is parked with `recipient := owner` (the queue owner) and `queueDequeueK` already gates `actor = owner`,
so the bound deposit's `recipient` IS the dequeuer; an UNRELATED deposit (recipient ≠ actor) is REJECTED.
`auth_gated` makes the binding a TYPING obligation: a handler whose step skipped it would not type-check.
The minimal SOUND conjunct is `r.recipient = actor`; the FULLER per-message binding (the deposit keyed to
the specific dequeued message hash, not just the queue owner) is §DEFER'd — it needs a message→deposit
map the `QueueRecord` buffer does not carry. The conservation lemma is UNCONDITIONAL on the kernel op
committing, so the binding wrap composes for free (it only narrows WHICH deposit may be drained; the
value-conservation math is the kernel's, cited verbatim). `delta = 0`.

`#eval`-verified TEETH: the P0-1 attack (a dequeuer refunding
an UNRELATED deposit, recipient ≠ actor) returns `none`; the actor's own bound deposit returns `some`.
Standalone: `lake build Dregg2.Exec.Handlers.Queue`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Queue

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle pipelineFanoutK pipelineFanoutK_balNeutral)
open Dregg2.Exec.EffectsState (stateAuthB)

/-! ## §1 — `queueAllocateA`: create a fresh queue record. bal-NEUTRAL (`delta = 0`).

`queueAllocateK` inserts a fresh `QueueRecord` (rejecting a duplicate id); it touches ONLY `queues`, so
the combined per-asset measure is unchanged. We WRAP it with the queue-cell authority gate
(`stateAuthB actor owner`, the dregg1 chained-step gate — the actor must hold authority over the owning
cell) and the owner-Live admission gate; `conserves` cites `queueAllocateK_balNeutral`. -/

/-- Queue-allocate arguments. ALIGNED to `execFullA`'s `queueAllocateChainA`: the queue record's
STORED owner is the **actor** (`queueAllocateK k id actor cap`), and the authority/admission gate is on
the **`gateCell`** the queue is created on (`stateAuthB actor gateCell`). Earlier the handler stored
owner = `cell` (a DIVERGENCE from `execFullA`, which stored owner = `actor`); separating the stored
owner (`actor`) from the gate cell (`gateCell`) closes the §6.6 hole. -/
structure AllocateArgs where
  /-- The actor performing the allocate — and the STORED queue owner (only the owner may dequeue). -/
  actor : CellId
  /-- The fresh queue id (rejected if already in use). -/
  id : Nat
  /-- The cell the queue is created on — the authority + admission gate target. -/
  gateCell : CellId
  /-- The buffer capacity. -/
  capacity : Nat

/-- The authority-gated allocate step: the actor must hold authority over `gateCell` AND `gateCell` must
be a Live cell, then run the proved `queueAllocateK` with the STORED owner = `actor` (the `execFullA`
alignment). -/
def allocateStep (k : RecordKernelState) (a : AllocateArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.gateCell && acceptsEffects k a.gateCell then
    queueAllocateK k a.id a.actor a.capacity
  else none

/-- **`queueAllocateA` — the registered queue-allocate handler.** `delta = 0` (touches only `queues`).
`conserves` from `queueAllocateK_balNeutral`. `auth_gated`/`admission_gated` from the wrapping gate.
The stored owner is `actor` (aligned to `execFullA`); the gate is on `gateCell`. -/
def queueAllocateA : EffectHandler AllocateArgs where
  step := allocateStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.gateCell
  admission := fun k a => acceptsEffects k a.gateCell
  trace := fun a => { actor := a.actor, src := a.gateCell, dst := a.gateCell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold allocateStep at h
    by_cases hg : stateAuthB s.caps a.actor a.gateCell && acceptsEffects s a.gateCell
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold allocateStep at h
    by_cases hg : stateAuthB s.caps a.actor a.gateCell && acceptsEffects s a.gateCell
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold allocateStep at h
    by_cases hg : stateAuthB s.caps a.actor a.gateCell && acceptsEffects s a.gateCell
    · rw [if_pos hg] at h
      rw [queueAllocateK_balNeutral h b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §2 — `queueEnqueueA`: the bare FIFO append. bal-NEUTRAL (`delta = 0`).

F1b: the Wave-8 refundable anti-spam deposit-park (`queueEnqueueDepositK`) is GONE with the kernel
escrow holding-store it parked into (anti-spam deposits are a FACTORY concern in the F2 queue
migration). The enqueue is the bare `queueEnqueueK` FIFO append again — it touches ONLY `queues`,
never `bal`. We WRAP it with the writer-ACL authority gate (`stateAuthB actor cell`, the dregg1
chained-step gate) and the cell-Live admission gate; `conserves` cites `queueEnqueueK_balNeutral`. -/

/-- Queue-enqueue arguments (deposit-free, aligned to `execFullA`'s `queueEnqueueChainA`). -/
structure EnqueueArgs where
  /-- The queue id to enqueue into. -/
  id : Nat
  /-- The message hash appended to the FIFO tail. -/
  m : Nat
  /-- The actor performing the enqueue (the writer-ACL subject). -/
  actor : CellId
  /-- The queue's representing cell (the authority + admission gate target). -/
  cell : CellId

/-- The authority-gated enqueue step: writer-ACL + Live cell, then the proved `queueEnqueueK`
(fail-closed if absent OR FULL). -/
def enqueueStep (k : RecordKernelState) (a : EnqueueArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.cell && acceptsEffects k a.cell then
    queueEnqueueK k a.id a.m
  else none

/-- **`queueEnqueueA` — the registered queue-enqueue handler.** `delta = 0` (touches only `queues`).
`conserves` from `queueEnqueueK_balNeutral`. `auth_gated`/`admission_gated` from the wrapping gate. -/
def queueEnqueueA : EffectHandler EnqueueArgs where
  step := enqueueStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold enqueueStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold enqueueStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold enqueueStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · rw [if_pos hg] at h
      rw [queueEnqueueK_balNeutral h b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §3 — `queueDequeueA`: the bare owner-gated FIFO pop. bal-NEUTRAL (`delta = 0`).

F1b: the deposit refund (`queueDequeueRefundK`) and the P0-1 binding gate are GONE with the deposit
park — the dequeue is the bare `queueDequeueK` REMOVE-FROM-FRONT again (owner-only, fail-closed on
absent/EMPTY). It touches ONLY `queues`. We WRAP it with the c-list authority gate + Live cell;
`conserves` cites `queueDequeueK_balNeutral`. -/

/-- Queue-dequeue arguments (deposit-free, aligned to `execFullA`'s `queueDequeueChainA`). -/
structure DequeueArgs where
  /-- The queue id to dequeue from. -/
  id : Nat
  /-- The dequeuer (must be the queue owner — the kernel gate). -/
  actor : CellId
  /-- The queue's representing cell (the authority + admission gate target). -/
  cell : CellId

/-- The authority-gated dequeue step: c-list gate + Live cell, then the proved `queueDequeueK`
(owner-only, FIFO order; the dequeued head surfaces in the kernel transition's `Nat`). -/
def dequeueBindStep (k : RecordKernelState) (a : DequeueArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.cell && acceptsEffects k a.cell then
    (queueDequeueK k a.id a.actor).map Prod.fst
  else none

/-- **`queueDequeueA` — the registered queue-dequeue handler.** `delta = 0` (touches only `queues`).
`conserves` from `queueDequeueK_balNeutral`. `auth_gated`/`admission_gated` from the wrapping gate;
the OWNER gate lives in `queueDequeueK` itself. -/
def queueDequeueA : EffectHandler DequeueArgs where
  step := dequeueBindStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold dequeueBindStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold dequeueBindStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold dequeueBindStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · rw [if_pos hg] at h
      cases hk : queueDequeueK s a.id a.actor with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some pr =>
          obtain ⟨k1, mh⟩ := pr
          rw [hk] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          rw [queueDequeueK_balNeutral hk b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §4 — `queueResizeA`: change the queue capacity. bal-NEUTRAL (`delta = 0`).

`queueResizeK` changes a queue's capacity (rejecting a shrink below current occupancy); it touches ONLY
`queues`, so the combined measure is unchanged. We WRAP it with the queue-cell authority gate
(`stateAuthB actor owner`) and the owner-Live admission gate; `conserves` cites `queueResizeK_balNeutral`. -/

/-- Queue-resize arguments: the actor, the queue `id`, the new `capacity`, and the queue `owner`
(authority subject). -/
structure ResizeArgs where
  /-- The actor performing the resize (must hold authority over `owner`). -/
  actor : CellId
  /-- The queue id to resize. -/
  id : Nat
  /-- The new capacity (rejected if below current occupancy). -/
  capacity : Nat
  /-- The queue owner (authority subject). -/
  owner : CellId

/-- The authority-gated resize step: the actor must hold authority over `owner` AND `owner` must be Live,
then run the proved `queueResizeK`. -/
def resizeStep (k : RecordKernelState) (a : ResizeArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.owner && acceptsEffects k a.owner then
    queueResizeK k a.id a.capacity
  else none

/-- **`queueResizeA` — the registered queue-resize handler.** `delta = 0` (touches only `queues`).
`conserves` from `queueResizeK_balNeutral`. `auth_gated`/`admission_gated` from the wrapping gate. -/
def queueResizeA : EffectHandler ResizeArgs where
  step := resizeStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.owner
  admission := fun k a => acceptsEffects k a.owner
  trace := fun a => { actor := a.actor, src := a.owner, dst := a.owner, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold resizeStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold resizeStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold resizeStep at h
    by_cases hg : stateAuthB s.caps a.actor a.owner && acceptsEffects s a.owner
    · rw [if_pos hg] at h
      rw [queueResizeK_balNeutral h b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §5 — `queueAtomicTxA`: the ALL-OR-NOTHING queue-op batch. bal-NEUTRAL (`delta = 0`).

dregg1's `apply_queue_atomic_tx` folds a list of queue sub-ops (enqueue / dequeue) all-or-nothing: the
batch COMMITS iff EVERY sub-op commits (each against the prior's result); ANY failure rolls back the
whole batch (`Option`-monad fold). F1b: the deposit/refund legs are GONE with the kernel escrow
holding-store — each sub-op is the bare bal-NEUTRAL FIFO op, so the fold is bal-NEUTRAL by induction. -/

/-- One atomic-batch sub-op at the bare kernel layer (F1b: deposit-free). -/
inductive QueueTxOpK where
  /-- `Enqueue { queue, message }` — append `m` to queue `id` (fail-closed if absent/FULL). -/
  | enqueue (id m : Nat)
  /-- `Dequeue { queue }` — remove the FIFO head of queue `id` (owner-gated, fail-closed on EMPTY). -/
  | dequeue (id : Nat) (actor : CellId)
  deriving Repr

/-- Run one atomic sub-op at the bare kernel layer (the proved kernel FIFO ops). -/
def queueTxOpStepK (k : RecordKernelState) : QueueTxOpK → Option RecordKernelState
  | .enqueue id m => queueEnqueueK k id m
  | .dequeue id actor => (queueDequeueK k id actor).map Prod.fst

/-- **`queueTxOpStepK_conserves` — PROVED.** Each atomic sub-op is bal-NEUTRAL per asset — read off
the kernel FIFO ops' proved bal-neutrality. -/
theorem queueTxOpStepK_conserves {k k' : RecordKernelState} {op : QueueTxOpK}
    (h : queueTxOpStepK k op = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  cases op with
  | enqueue id m =>
      exact queueEnqueueK_balNeutral (k := k) (k' := k') h b
  | dequeue id actor =>
      simp only [queueTxOpStepK] at h
      cases hk : queueDequeueK k id actor with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some pr =>
          obtain ⟨k1, mh⟩ := pr
          rw [hk] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
          exact queueDequeueK_balNeutral hk b

/-- **The all-or-nothing atomic batch fold** (dregg1 `apply_queue_atomic_tx`). Thread the sub-ops
left-to-right through the `Option` monad: COMMIT iff EVERY sub-op commits; ANY failure ⇒ `none` (the
whole batch rolls back). -/
def queueAtomicTxChainK (k : RecordKernelState) : List QueueTxOpK → Option RecordKernelState
  | []        => some k
  | op :: ops =>
      match queueTxOpStepK k op with
      | some k' => queueAtomicTxChainK k' ops
      | none    => none

/-- **`queueAtomicTxChainK_conserves` — PROVED (the atomic batch is bal-NEUTRAL per asset).** A
committed batch preserves `recTotalAsset` at EVERY asset: each sub-op is bal-neutral,
and the fold composes them. By induction on the op list. -/
theorem queueAtomicTxChainK_conserves {k k' : RecordKernelState} {ops : List QueueTxOpK}
    (h : queueAtomicTxChainK k ops = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  induction ops generalizing k with
  | nil => simp only [queueAtomicTxChainK, Option.some.injEq] at h; subst h; rfl
  | cons op rest ih =>
      simp only [queueAtomicTxChainK] at h
      cases hop : queueTxOpStepK k op with
      | none    => rw [hop] at h; exact absurd h (by simp)
      | some k1 =>
          rw [hop] at h
          rw [ih h, queueTxOpStepK_conserves hop b]

/-- Atomic-tx arguments: the actor (the batch-commit subject) and the sub-op list. -/
structure AtomicTxArgs where
  /-- The actor performing the atomic batch (the metadata/receipt subject). -/
  actor : CellId
  /-- The all-or-nothing list of queue sub-ops. -/
  ops : List QueueTxOpK

/-- The atomic-tx step: run the all-or-nothing batch fold over the bare kernel (the receipt-chain
metadata row lives in the chained executor; here the conservation content is the fold). -/
def atomicTxStep (k : RecordKernelState) (a : AtomicTxArgs) : Option RecordKernelState :=
  queueAtomicTxChainK k a.ops

/-- **`queueAtomicTxA` — the registered atomic-tx handler (`delta = 0`, bal-NEUTRAL).**
`conserves` from `queueAtomicTxChainK_conserves` (the per-op neutrality summed over the fold).
`auth`/`admission` default-true here (each sub-op carries its OWN fail-closed gate IN the fold). -/
def queueAtomicTxA : EffectHandler AtomicTxArgs where
  step := atomicTxStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold atomicTxStep at h
    have := queueAtomicTxChainK_conserves (k := s) (k' := s') h b
    rw [this]; ring

/-! ## §6 — `queuePipelineStepA`: the FAN-OUT routing step. bal-NEUTRAL (`delta = 0`).

dregg1's `apply_queue_pipeline_step` DEQUEUEs the FIFO head from a source queue (owner-only) and
RE-ENQUEUEs that moved head into EACH sink (ACL-checked per sink, `pipelineFanoutK`). It moves MESSAGES,
never balance — every step is bal-NEUTRAL on `queues`, so the combined per-asset measure is unchanged
(`delta = 0`). We model the step at the bare kernel layer (the chained version adds a routing receipt
row); `conserves` composes `queueDequeueK_balNeutral` (the source dequeue) with the proved
`pipelineFanoutK_balNeutral` (the sink fan-out). -/

/-- Pipeline-step arguments: the source queue `srcId`, the `owner` (source dequeuer), and the
position-paired sink cells / sink queue ids. -/
structure PipelineArgs where
  /-- The source queue id (the FIFO head is dequeued from here). -/
  srcId : Nat
  /-- The source dequeuer (must be the source queue owner). -/
  owner : CellId
  /-- The representing cells of each sink (writer-ACL gated per sink). -/
  sinkCells : List CellId
  /-- The queue ids of each sink (position-paired with `sinkCells`). -/
  sinkIds : List Nat

/-- The pipeline step at the bare kernel layer: dequeue the source head (owner-gated, FIFO order) then
fan it out into each ACL-checked sink (all-or-nothing). Fail-closed if the source dequeue fails OR any
sink rejects. -/
def pipelineStep (k : RecordKernelState) (a : PipelineArgs) : Option RecordKernelState :=
  match queueDequeueK k a.srcId a.owner with
  | some (k1, m) => pipelineFanoutK k1 a.owner m a.sinkCells a.sinkIds
  | none         => none

/-- **`queuePipelineStepA` — the registered pipeline-routing handler (`delta = 0`, bal-NEUTRAL).**
`conserves` composes the source dequeue's bal-neutrality (`queueDequeueK_balNeutral`) with the sink
fan-out's (`pipelineFanoutK_balNeutral`). `auth`/`admission` default-true here (the OWNER gate lives in
`queueDequeueK` IN the step, the per-sink writer-ACL in `pipelineFanoutK` IN the step — the load-bearing
gates are the kernel ops the step composes; the `#eval` TEETH verify them). -/
def queuePipelineStepA : EffectHandler PipelineArgs where
  step := pipelineStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.owner, src := a.owner, dst := a.owner, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold pipelineStep at h
    cases hd : queueDequeueK s a.srcId a.owner with
    | none => rw [hd] at h; exact absurd h (by simp)
    | some pr =>
        obtain ⟨k1, m⟩ := pr
        rw [hd] at h
        rw [pipelineFanoutK_balNeutral h b, queueDequeueK_balNeutral hd b]; ring

/-! ## §7 — The batch registry: the queue cluster as coproduct entries.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler`. -/

/-- The queue batch registry (the coproduct menu for this cluster). -/
def queueBatchRegistry : Registry :=
  [ ⟨AllocateArgs, queueAllocateA⟩,
    ⟨EnqueueArgs, queueEnqueueA⟩,
    ⟨DequeueArgs, queueDequeueA⟩,
    ⟨ResizeArgs, queueResizeA⟩,
    ⟨AtomicTxArgs, queueAtomicTxA⟩,
    ⟨PipelineArgs, queuePipelineStepA⟩ ]

/-- Build a closed queue-allocate effect (tag `0`). The STORED queue owner is `actor` (aligned to
`execFullA`'s `queueAllocateChainA`); `gateCell` is the cell the queue is created on (the gate target). -/
def allocateEffect (actor : CellId) (id : Nat) (gateCell : CellId) (capacity : Nat) : ClosedEffect :=
  { tag := 0, Args := AllocateArgs,
    args := { actor := actor, id := id, gateCell := gateCell, capacity := capacity }, handler := queueAllocateA }

/-- Build a closed queue-enqueue effect (tag `1`; F1b deposit-free). -/
def enqueueEffect (id m : Nat) (actor cell : CellId) : ClosedEffect :=
  { tag := 1, Args := EnqueueArgs,
    args := { id := id, m := m, actor := actor, cell := cell }, handler := queueEnqueueA }

/-- Build a closed queue-dequeue effect (tag `2`; F1b deposit-free). -/
def dequeueEffect (id : Nat) (actor cell : CellId) : ClosedEffect :=
  { tag := 2, Args := DequeueArgs, args := { id := id, actor := actor, cell := cell },
    handler := queueDequeueA }

/-- Build a closed queue-resize effect (tag `3`). -/
def resizeEffect (actor : CellId) (id capacity : Nat) (owner : CellId) : ClosedEffect :=
  { tag := 3, Args := ResizeArgs,
    args := { actor := actor, id := id, capacity := capacity, owner := owner }, handler := queueResizeA }

/-- Build a closed atomic-tx effect (tag `4`). -/
def atomicTxEffect (actor : CellId) (ops : List QueueTxOpK) : ClosedEffect :=
  { tag := 4, Args := AtomicTxArgs, args := { actor := actor, ops := ops }, handler := queueAtomicTxA }

/-- Build a closed pipeline-step effect (tag `5`). -/
def pipelineEffect (srcId : Nat) (owner : CellId) (sinkCells : List CellId) (sinkIds : List Nat) :
    ClosedEffect :=
  { tag := 5, Args := PipelineArgs,
    args := { srcId := srcId, owner := owner, sinkCells := sinkCells, sinkIds := sinkIds },
    handler := queuePipelineStepA }

/-! ## §8 — TEETH: the FIFO order/allocate/resize/atomic/pipeline behaviour, evaluated.

(F1b: the P0-1 deposit-binding attack fixtures left with the kernel deposit park — anti-spam deposits
are a factory concern in the F2 queue migration.) -/

/-- A fixture: cells 0 (queue owner), 5 (sender), 8 are live accounts; cell 5 holds 100
of asset 0; one queue (id 7, owner 0, cap 3, empty). Self-authority (every cell authorizes its own
ledger). All cells Live. -/
def qh0 : RecordKernelState :=
  { accounts := {0, 5, 8}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 5 ∧ a = 0 then 100 else 0
    queues := [{ id := 7, owner := 0, capacity := 3, buffer := [] }] }

/-- The fixture after actor 0 enqueues message 111 into queue 7 (writer-ACL self-gate). -/
def qhEnq : Option RecordKernelState :=
  enqueueStep qh0 { id := 7, m := 111, actor := 0, cell := 0 }

-- §TEETH-1 (HONEST dequeue): the owner (0) dequeues the head ⇒ SUCCEEDS, bal-NEUTRAL.
#guard ((qhEnq.bind (fun k => execEffect (dequeueEffect 7 0 0) k)).isSome)  --  true
-- §TEETH-2 (NON-OWNER dequeue REJECTED): actor 5 (not the owner) ⇒ none (the kernel owner gate).
#guard ((qhEnq.bind (fun k => execEffect (dequeueEffect 7 5 5) k)).isSome) == false  --  false
-- §TEETH-3 (CONSERVATION): the dequeue conserves the per-asset measure.
#guard ((qhEnq.bind (fun k => execEffect (dequeueEffect 7 0 0) k)).map
        (fun k => recTotalAsset k 0)) == some 100  --  some 100
-- §TEETH-4 (ENQUEUE bal-NEUTRAL): enqueue moves NO value (the deposit is F1b-GONE).
#guard (qhEnq.map (fun k => recTotalAsset k 0)) == some 100  --  some 100
-- §TEETH-5 (FIFO order): after enqueue the message is in the buffer.
#guard (qhEnq.bind (fun k => (findQueue k.queues 7).map (·.buffer))) == some [111]  --  some [111]
-- §TEETH-6 (ALLOCATE): actor 0 allocates a fresh queue id 12 (owner 0) ⇒ SUCCEEDS, measure unchanged.
#guard ((execEffect (allocateEffect 0 12 0 4) qh0).map
        (fun k => (recTotalAsset k 0, ((findQueue k.queues 12).map (·.capacity))))) == some (100, some 4)  --  some (100, some 4)
-- §TEETH-7 (ALLOCATE duplicate id REJECTED): re-allocating the existing queue 7 ⇒ none.
#guard ((execEffect (allocateEffect 0 7 0 4) qh0).isSome) == false  --  false
-- §TEETH-8 (RESIZE): grow queue 7's capacity to 5 ⇒ SUCCEEDS; shrink below occupancy is rejected (see kernel).
#guard ((execEffect (resizeEffect 0 7 5 0) qh0).map
        (fun k => (findQueue k.queues 7).map (·.capacity))) == some (some 5)  --  some (some 5)
-- §TEETH-9 (ENQUEUE FULL gate): filling the queue past capacity 3 is REJECTED.
#guard ((execEffect (atomicTxEffect 0
        [ QueueTxOpK.enqueue 7 1, QueueTxOpK.enqueue 7 2, QueueTxOpK.enqueue 7 3,
          QueueTxOpK.enqueue 7 4 ]) qh0).isSome) == false  --  false (the 4th overflows ⇒ batch rolls back)
-- §TEETH-10 (ATOMIC-TX all-or-nothing + neutral): a batch [enqueue; dequeue-by-owner] runs the fold
-- and conserves the measure.
#guard ((execEffect (atomicTxEffect 0
        [ QueueTxOpK.enqueue 7 111, QueueTxOpK.dequeue 7 0 ]) qh0).map
        (fun k => recTotalAsset k 0)) == some 100  --  some 100
-- §TEETH-11 (ATOMIC-TX rollback): a batch whose dequeue is by a NON-owner ROLLS BACK the whole batch.
#guard ((execEffect (atomicTxEffect 0
        [ QueueTxOpK.enqueue 7 111, QueueTxOpK.dequeue 7 5 ]) qh0).isSome) == false  --  false
-- §TEETH-12 (PIPELINE fan-out): allocate a sink queue (id 13, owner 0), enqueue a message into source 7,
-- then pipeline the head from 7 into sink 13 ⇒ SUCCEEDS; the message LANDED in the sink and the
-- measure is UNCHANGED (messages move, not value).
#guard (((queueAllocateK qh0 13 0 3).bind (fun k => queueEnqueueK k 7 111)).bind
        (fun k => execEffect (pipelineEffect 7 0 [0] [13]) k) |>.map
        (fun k => ((findQueue k.queues 13).map (·.buffer), recTotalAsset k 0))) == some (some [111], 100)  --  some (some [111], 100)
-- §TEETH-13 (PIPELINE source-empty REJECTED): pipelining an EMPTY source queue ⇒ none.
#guard ((execEffect (pipelineEffect 7 0 [0] [13]) qh0).isSome) == false  --  false

/-! ## §9 — turn_conserves cross-check: a registry turn of queue effects conserves the measure. -/
#guard (turnDelta [allocateEffect 0 12 0 4, enqueueEffect 7 111 0 0, dequeueEffect 7 0 0] 0) == 0  --  0
#guard ((execTurn [enqueueEffect 7 111 0 0, dequeueEffect 7 0 0] qh0).map
        (fun k => recTotalAsset k 0)) == some 100  --  some 100

/-! ## §10 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler def pins its obligation fields transitively (the literal CARRIES the proofs); each
fold/conservation helper is pinned directly. A `sorryAx` anywhere fails the pin AND the build. -/

#assert_axioms queueAllocateA
#assert_axioms queueEnqueueA
#assert_axioms queueDequeueA
#assert_axioms queueResizeA
#assert_axioms queueAtomicTxA
#assert_axioms queuePipelineStepA
#assert_axioms queueTxOpStepK_conserves
#assert_axioms queueAtomicTxChainK_conserves

/-! ## §DEFER — honest scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **Anti-spam deposits (F1b).** The Wave-8 refundable deposit-park/refund + the P0-1 binding gates
    are GONE with the kernel escrow holding-store; they re-land as a FACTORY concern in the F2 queue
    migration (a deposit is then an ordinary `bal` move into a factory-born deposit cell).

  * **The receipt-chain metadata rows.** `queueAtomicTxA`/`queuePipelineStepA` register the bare-kernel
    CONSERVATION content (the all-or-nothing fold / the source-dequeue-then-fan-out). The chained
    executor's batch-commit / routing receipt rows (`escrowReceiptA` / the routing log row) live in
    `TurnExecutorFull`'s `RecChainedState` layer — the EffectHandler algebra is over the bare kernel
    state; the receipt-chain face folds on at the cutover.

  * **`queueAtomicTxA`/`queuePipelineStepA` batch-level `auth`/`admission`.** These default-true because
    the load-bearing gates live IN the step (each sub-op's writer-ACL / owner / P0-1 binding inside the
    fold; the source-owner + per-sink ACL inside the pipeline). The §8 `#eval` TEETH verify the gates
    bite. A batch-level authority object (the conjunction of the sub-op gates as a single witness) is the
    Guard-valued upgrade noted in `Dregg2.Exec.Handler`'s §DEFER. -/

end Dregg2.Exec.Handlers.Queue
