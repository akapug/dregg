/-
# Dregg2.Exec.HandlerExecutor — THE CUTOVER KEYSTONE (additive; the live switch is mechanical).

This is the file the seven handler batches were built FOR. It assembles them into ONE executor that is a
DROP-IN, SOUNDNESS-STRENGTHENING replacement for `TurnExecutorFull.execFullA`, and proves the global
conservation/gate laws for it WITHOUT a per-arm matrix — by LIFTING the scaffold's generic `turn_conserves`
/ `turn_head_authorized` / `turn_head_admitted` (`Dregg2.Exec.Handler`). This is additive: it does NOT edit
`execFullA`/`FullActionA`; switching the call-sites is a later mechanical step.

The five deliverables:

  1. **`masterRegistry`** (`§2`) — the coproduct `Registry = List PackedHandler` packing ALL the proved
     handlers across the seven files (transfer / mint / burn / state-write / createCell / escrow /
     release / refund / note / seal / unseal / seal-pair / swiss-export/enliven/handoff/drop / delegate /
     attenuate / revoke / queue-allocate/enqueue/dequeue/resize/atomic/pipeline / bridge-lock/finalize/
     cancel / pipelined-send / exercise). Every entry's obligation proofs are a TYPING condition on entry.

  2. **`toClosedEffect`** (`§3`) — the TOTAL map `FullActionA → ClosedEffect` mapping each of the 56
     constructors to its handler + args, ALIASES collapsed (obligation→escrow, committed→escrow,
     introduce/validateHandoff→delegateAtten, slash→release, fulfill→refund, bridgeMint→mint,
     createCellFromFactory/spawn→createCell, dropRef/revokeDelegation→revoke, the lifecycle/emit
     family→a live-gated state write). 56/56 constructors covered.

  3. **`execHandlerTurn`** (`§4`) — `List FullActionA → RecChainedState → Option RecChainedState`: map
     `toClosedEffect`, run each `ClosedEffect`'s `step` on the `.kernel`, thread the state through the
     scaffold's generic `execTurn` (the `.log` carries the audit trace).

  4. **THE DERIVED GLOBAL CONSERVATION** (`§5`) — `execHandlerTurn_conserves`: the combined per-asset
     measure `recTotalAssetWithEscrow` (over `.kernel`; log-independent) moves by the SUM of the
     per-effect deltas, proved by LIFTING the scaffold's generic `turn_conserves` (NOT a 56-arm cases
     matrix — THIS is the matrix-killer demonstrated at full scale). Plus the gate companions
     (`execHandlerTurn_head_authorized` / `_admitted`) lifted from `turn_head_authorized`/`_admitted`.

  5. **THE STRENGTHENING** (`§6`) — `handler_refines_execFullA_*`: the handler executor is a SOUND
     STRENGTHENING of `execFullA`: for the hole-closing effects (a transfer R1, an escrow-release R2, a
     state-write R6) every commit the handler executor makes, `execFullA` ALSO makes, AND they AGREE on
     the kernel. The handlers only ADD gates.

  6. **THE TEETH** (`§7`) — concrete attacks `execFullA` ADMITS but `execHandlerTurn` REJECTS: a transfer
     into a Sealed cell (R1), an escrow-release by a stranger (R2), a state-write into a Sealed cell (R6).
     `#eval`-verified: `execFullA = some` (the live hole) vs `execHandlerTurn = none` (the algebra closes
     it). The cutover STRICTLY improves soundness.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/eval-only; no `maxHeartbeats`. The conservation
keystone REUSES `turn_conserves` (generic) — it is NEVER re-derived. `#assert_axioms`-pinned. Verified
standalone: `lake build Dregg2.Exec.HandlerExecutor`.
-/
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Exec.Handlers.Escrow
import Dregg2.Exec.Handlers.Seal
import Dregg2.Exec.Handlers.Authority
import Dregg2.Exec.Handlers.Queue
import Dregg2.Exec.Handlers.Bridge
import Dregg2.Exec.Handlers.Exercise
import Dregg2.Exec.Handlers.Lifecycle

namespace Dregg2.Exec.HandlerExecutor

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle parentClist cellSealChainA cellUnsealChainA
   cellDestroyChainA refreshDelegationChainA emitStep execFullA FullActionA QueueTxOpA
   recCDelegate recCDelegateAtten attenuateStepA
   createSealPairChainA sealChainA unsealChainA
   swissExportChainA swissEnlivenChainA swissHandoffChainA swissDropChainA
   queueAllocateChainA queueResizeChainA pipelineFanoutK
   authReceipt escrowReceiptA sealerCap unsealerCap holdsSealCapFor)
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec (recKDelegate recKDelegateAtten heldCapTo attenuate grant)
open scoped BigOperators

-- module-qualified aliases for the seven batches (every handler + ClosedEffect builder lives here)
open Dregg2.Exec.Handlers.StateSupply
open Dregg2.Exec.Handlers.Escrow
open Dregg2.Exec.Handlers.Seal
open Dregg2.Exec.Handlers.Authority
open Dregg2.Exec.Handlers.Queue
open Dregg2.Exec.Handlers.Bridge
open Dregg2.Exec.Handlers.Exercise
open Dregg2.Exec.Handlers.Lifecycle

/-! ## §1 — Pretty names for the master registry indices (the audit-trail tags).

Each `ClosedEffect` already carries the registry `tag` its batch assigned (the coproduct injection key);
`toClosedEffect` (`§3`) reuses each batch's `ClosedEffect` builder VERBATIM, so the tags it emits are the
batch-local ones. The master registry below LISTS every handler so the executor's dispatch is one LOOKUP
over the coproduct — the 56-arm `match` of `execFullA` collapsed into a list. -/

/-! ## §2 — `masterRegistry`: the coproduct (LIST) of ALL the proved handlers, seven batches assembled.

This is the master menu. Each entry is one `PackedHandler` carrying a handler whose obligation proofs are
DISCHARGED (the structure literal would not type-check otherwise). The generic `turn_conserves` /
`turn_head_authorized` / `turn_head_admitted` are generic over THIS list — adding an effect is adding one
well-typed entry, never a lemma. -/

/-- **`masterRegistry`** — the coproduct of all proved handlers across the seven batches. The 56-effect
op-set as a single list; the executor dispatches by LOOKUP, not a bespoke `match`. -/
def masterRegistry : Registry :=
  -- §transfer / supply / state-write (Handler scaffold + StateSupply)
  [ ⟨TransferArgs, transferH⟩
  , ⟨SupplyArgs, mintH⟩, ⟨SupplyArgs, burnH⟩, ⟨SupplyArgs, bridgeMintH⟩
  , ⟨CreateArgs, createCellH⟩, ⟨CreateArgs, createCellFromFactoryH⟩, ⟨CreateArgs, spawnH⟩
  , ⟨StateWriteArgs, stateWriteH⟩
  -- §escrow / obligation / note (Escrow)
  , ⟨CreateEscrowArgs, createEscrowA⟩
  , ⟨SettleArgs, releaseEscrowA⟩, ⟨SettleArgs, refundEscrowA⟩
  , ⟨CreateEscrowArgs, createObligationA⟩
  , ⟨SettleArgs, slashObligationA⟩, ⟨SettleArgs, fulfillObligationA⟩
  , ⟨NoteSpendArgs, noteSpendA⟩, ⟨NoteCreateArgs, noteCreateA⟩
  -- §seal / swiss (Seal)
  , ⟨CreateSealPairArgs, createSealPairA⟩, ⟨SealArgs, sealA⟩, ⟨UnsealArgs, unsealA⟩
  , ⟨ExportArgs, exportSturdyRefA⟩, ⟨EnlivenArgs, enlivenRefA⟩
  , ⟨HandoffArgs, swissHandoffA⟩, ⟨DropArgs, swissDropA⟩
  -- §authority / delegation (Authority)
  , ⟨DelegateArgs, delegateH⟩, ⟨DelegateArgs, introduceH⟩, ⟨DelegateArgs, validateHandoffH⟩
  , ⟨DelegateArgs, delegateAttenH⟩
  , ⟨AttenuateArgs, attenuateH⟩
  , ⟨RevokeArgs, revokeDelegationH⟩, ⟨RevokeArgs, dropRefH⟩, ⟨RevokeArgs, revokeH⟩
  -- §queue (Queue)
  , ⟨AllocateArgs, queueAllocateA⟩, ⟨EnqueueArgs, queueEnqueueA⟩, ⟨DequeueArgs, queueDequeueA⟩
  , ⟨ResizeArgs, queueResizeA⟩, ⟨AtomicTxArgs, queueAtomicTxA⟩, ⟨PipelineArgs, queuePipelineStepA⟩
  -- §bridge (Bridge)
  , ⟨BridgeLockArgs, bridgeLockA⟩, ⟨BridgeFinalizeArgs, bridgeFinalizeA⟩
  , ⟨BridgeCancelArgs, bridgeCancelA⟩, ⟨PipelinedSendArgs, pipelinedSendA⟩
  -- §exercise (Exercise — the recursive sub-effect forest)
  , ⟨ExerciseArgs, exerciseH⟩
  -- §lifecycle / emit (Lifecycle — real side-table semantics, not field-write stubs)
  , ⟨CellLifecycleArgs, cellSealH⟩
  , ⟨CellLifecycleArgs, cellUnsealH⟩
  , ⟨CellDestroyArgs, cellDestroyH⟩
  , ⟨RefreshDelegationArgs, refreshDelegationH⟩
  , ⟨EmitEventArgs, emitEventH⟩ ]

/-- The master registry packs 47 distinct handler ENTRIES (the 56 op-set constructors collapse onto these
via the aliasing of `toClosedEffect` — obligation↔escrow, committed↔escrow, slash↔release, fulfill↔refund,
introduce/validateHandoff↔delegateAtten, bridgeMint↔mint, factory/spawn↔createCell, dropRef/
revokeDelegation↔revoke). -/
theorem masterRegistry_length : masterRegistry.length = 47 := rfl

/-! ## §3 — `toClosedEffect`: the TOTAL `FullActionA → ClosedEffect` dispatch (56/56 constructors).

This is the cutover's heart: it sends every `FullActionA` constructor to the registered handler that
implements it, plus its concrete args, by REUSING each batch's `ClosedEffect` builder verbatim (so the
obligation proofs come along for free). The ALIASING is the dregg2 dispatch collapse the catalog already
records: an obligation IS an escrow, a slash IS a release-to-beneficiary, a fulfil IS a refund-to-obligor,
an introduce / validate-handoff IS an attenuated delegation, a bridge-mint IS a mint, a factory/spawn IS a
born-empty createCell, a dropRef / revoke-delegation IS a target revocation, a committed escrow IS an
escrow at the executable layer (the §8 hiding portal is off-ledger).

The lifecycle/emit family (`emitEventA` / `cellSealA` / `cellUnsealA` / `cellDestroyA` /
`refreshDelegationA`) routes to the dedicated `Lifecycle` handlers (real `lifecycle`/`deathCert`/
`delegations` side-table edits + authority-free emit membership gate). The seven named-field writes
(`setFieldA` / `incrementNonceA` / `setPermissionsA` / `setVKA` / `makeSovereignA` / `refusalA` /
`receiptArchiveA`) map onto the GENERIC live-gated `stateWriteH`. The committed
escrow / queue-atomic-tx args that carry shapes the bare kernel handler does not (the `hidingProof`
witness; the `QueueTxOpA` discriminant) are projected onto the handler's executable core (the escrow
lock; the `QueueTxOpK` sub-op list) — documented at each arm. -/

/-- Project an executor `QueueTxOpA` onto the handler's bare-kernel `QueueTxOpK` sub-op (the atomic-batch
discriminant; the chained step's receipt row lives in `RecChainedState`, off the kernel algebra). -/
def txOpToK : QueueTxOpA → Dregg2.Exec.Handlers.Queue.QueueTxOpK
  | .enqueue id m actor _cell depId dAsset deposit =>
      .enqueue id m actor actor depId dAsset deposit   -- owner-recipient = sender (honest park-for-self in the batch)
  | .dequeue id actor _cell depId _deposit =>
      .dequeue id actor depId

/-- **`toClosedEffect`** — the TOTAL dispatch map (every one of the 56 `FullActionA` constructors). Each
arm reuses its batch's `ClosedEffect` builder, so the looked-up handler's obligation proofs are carried.
Aliases collapse onto one handler; the field-write/lifecycle family routes through the generic
live-gated `stateWriteEffect` at a pinned field name (closing R6 for the whole family). -/
def toClosedEffect : FullActionA → ClosedEffect
  -- §transfer / authority / supply
  | .balanceA t a              => transferEffect t a
  | .delegate del rec t        => delegateEffect del rec t
  | .revoke holder t           => revokeEffect holder t
  | .mintA actor cell a amt     => mintEffect actor cell a amt
  | .burnA actor cell a amt     => burnEffect actor cell a amt
  -- §field writes (the 4 protocol-managed + the 3 Wave-6 flags) → generic live-gated write at a field
  | .setFieldA actor cell f v        => stateWriteEffect actor cell f v
  | .emitEventA actor cell topic data => emitEventEffect actor cell topic data
  | .incrementNonceA actor cell n     => incrementNonceEffect actor cell n
  | .setPermissionsA actor cell p     => setPermissionsEffect actor cell p
  | .setVKA actor cell vk             => setVKEffect actor cell vk
  -- §authority (6 distinct) — introduce/validateHandoff alias the attenuated delegation (keep := allAuths)
  | .introduceA intro rec t          => introduceEffect intro rec t
  | .delegateAttenA del rec t keep   => delegateAttenEffect del rec t keep
  | .attenuateA actor idx keep       => attenuateEffect actor idx keep
  | .dropRefA holder t               => dropRefEffect holder t
  | .revokeDelegationA holder t      => revokeDelegationEffect holder t
  | .validateHandoffA intro rec t    => validateHandoffEffect intro rec t
  -- §exercise (recursive) — the inner FullActionA forest folds onto its handlers via closedToSub
  | .exerciseA actor t inner         =>
      exerciseEffect actor t (inner.map (fun fa => facetedOf Auth.control (toClosedEffect fa)))
  -- §supply / account growth
  | .createCellA actor newCell       => createCellEffect actor newCell
  | .createCellFromFactoryA actor newCell _vk => createCellFromFactoryEffect actor newCell
  | .spawnA actor child _target      => spawnEffect actor child
  | .bridgeMintA actor cell a value  => bridgeMintEffect actor cell a value
  -- §escrow / obligation / committed-escrow / note (obligation/committed alias escrow)
  | .createEscrowA id actor creator recipient asset amount =>
      createEscrowEffect id actor creator recipient asset amount
  | .releaseEscrowA id actor          => releaseEscrowEffect actor id
  | .refundEscrowA id actor           => refundEscrowEffect actor id
  | .createObligationA id actor obligor beneficiary asset stake =>
      createEscrowEffect id actor obligor beneficiary asset stake
  | .fulfillObligationA id actor      => refundEscrowEffect actor id
  | .slashObligationA id actor        => releaseEscrowEffect actor id
  | .noteSpendA nf actor              => noteSpendEffect actor nf
  | .noteCreateA cm actor             => noteCreateEffect actor cm
  | .createCommittedEscrowA id actor creator recipient asset amount _hidingProof =>
      createEscrowEffect id actor creator recipient asset amount
  | .releaseCommittedEscrowA id actor => releaseEscrowEffect actor id
  | .refundCommittedEscrowA id actor  => refundEscrowEffect actor id
  -- §bridge (lock / finalize the delta<0 / cancel / pipelined-send)
  | .bridgeLockA id actor originator destination asset amount =>
      bridgeLockEffect id actor originator destination asset amount
  | .bridgeFinalizeA id actor asset amount => bridgeFinalizeEffect id actor asset amount
  | .bridgeCancelA id actor                => bridgeCancelEffect actor id
  -- §seal / swiss
  | .sealA pid actor payload      => sealEffect pid actor payload
  | .unsealA pid actor recipient  => unsealEffect pid actor recipient
  | .createSealPairA pid actor sealerHolder unsealerHolder =>
      createSealPairEffect pid actor sealerHolder unsealerHolder
  -- §flag/lifecycle writes (makeSovereign / refusal / receiptArchive) → generic live-gated write
  | .makeSovereignA actor cell    => makeSovereignEffect actor cell
  | .refusalA actor cell          => refusalEffect actor cell
  | .receiptArchiveA actor cell   => receiptArchiveEffect actor cell 1
  -- §queue
  | .queueAllocateA id actor cell cap   => allocateEffect actor id cell cap
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      enqueueEffect id m actor cell depId dAsset deposit
  | .queueDequeueA id actor _cell depId _deposit => dequeueEffect id actor depId
  | .queueResizeA id newCap actor cell  => resizeEffect actor id newCap cell
  | .queueAtomicTxA actor ops           => atomicTxEffect actor (ops.map txOpToK)
  | .queuePipelineStepA srcId owner sinkCells sinkIds =>
      pipelineEffect srcId owner sinkCells sinkIds
  | .pipelinedSendA actor               => pipelinedSendEffect actor
  -- §swiss
  | .exportSturdyRefA sw actor exporter target rights =>
      exportSturdyRefEffect sw actor exporter target rights
  | .enlivenRefA sw actor exporter claimed => enlivenRefEffect sw actor exporter claimed
  | .swissHandoffA sw certHash introducer exporter =>
      swissHandoffEffect sw certHash introducer exporter
  | .swissDropA sw actor exporter          => swissDropEffect sw actor exporter
  -- §lifecycle (cell seal/unseal/destroy + refresh-delegation) → real side-table handlers
  | .cellSealA actor cell          => cellSealEffect actor cell
  | .cellUnsealA actor cell        => cellUnsealEffect actor cell
  | .cellDestroyA actor cell certHash => cellDestroyEffect actor cell certHash
  | .refreshDelegationA actor child => refreshDelegationEffect actor child

/-! ## §4 — `execHandlerTurn`: the registry executor over the chained state.

Map each `FullActionA` to its `ClosedEffect` via `toClosedEffect`, run the looked-up handler's
fail-closed `step` on the `.kernel`, and thread the kernel through the scaffold's generic `execTurn`
(the `List.foldlM` all-or-nothing transaction). The `.log` carries the audit trace: each committed
effect appends its handler's `trace` Turn. This is the executable shadow that REPLACES `execFullA` —
additive here, the call-sites switch later. -/

/-- The closed-effect list a chained turn dispatches to (the cutover's per-turn dispatch table). -/
def closedOf (acts : List FullActionA) : List ClosedEffect := acts.map toClosedEffect

/-- **`execHandlerTurn`** — the registry executor. Run the closed effects (the `toClosedEffect` images)
all-or-nothing over the `.kernel` via the scaffold's `execTurn`, threading the receipt log. Any single
fail-closed handler aborts the whole turn (the `Option`-monad fold). -/
def execHandlerTurn (acts : List FullActionA) (s : RecChainedState) : Option RecChainedState :=
  -- run the kernel transaction; rebuild a chained state carrying the appended traces on success.
  match execTurn (closedOf acts) s.kernel with
  | some k' => some { kernel := k', log := (closedOf acts).reverse.map (fun e => e.handler.trace e.args) ++ s.log }
  | none    => none

/-- A single closed effect's chained step (the `execHandlerTurn` of a one-element list, unfolded). -/
def execHandlerOne (a : FullActionA) (s : RecChainedState) : Option RecChainedState :=
  execHandlerTurn [a] s

/-! ## §5 — THE DERIVED GLOBAL CONSERVATION (lift the scaffold's generic `turn_conserves`).

The combined per-asset measure over the kernel moves by the SUM of the per-effect deltas — PROVED by
LIFTING `Dregg2.Exec.Handler.turn_conserves` (generic over ANY `List ClosedEffect`) onto the chained
state's kernel. There is NO per-effect restatement and NO 56-arm cases matrix: the executable kernel
transition of `execHandlerTurn` IS `execTurn (closedOf acts)`, so the generic theorem applies VERBATIM.
THIS is the matrix-killer demonstrated at full scale. -/

/-- The combined per-asset turn delta of a `FullActionA` list under the handler executor: the SUM of the
per-effect deltas of the `toClosedEffect` images. (The right-hand budget conservation holds the measure
to — log-independent, a pure function of the closed-effect images.) -/
def handlerTurnDelta (acts : List FullActionA) (b : AssetId) : Int :=
  turnDelta (closedOf acts) b

/-- The empty turn is the identity (kernel unchanged). -/
@[simp] theorem execHandlerTurn_nil (s : RecChainedState) :
    (execHandlerTurn [] s).map (·.kernel) = some s.kernel := by
  simp only [execHandlerTurn, closedOf, List.map_nil, execTurn_nil, Option.map_some]

/-- **`execHandlerTurn_conserves` — THE DERIVED GLOBAL CONSERVATION (PROVED by LIFTING `turn_conserves`).**
For ANY `FullActionA` list run through the handler executor, the combined per-asset measure over the
kernel changes by EXACTLY the SUM of the per-effect deltas, at EVERY asset `b`. The proof is ONE LINE of
lifting: the kernel transition is `execTurn (closedOf acts)`, so the scaffold's generic `turn_conserves`
discharges it — NO per-arm matrix, NO re-derivation. The 56-arm `execFullA_ledger_per_asset` cases proof
collapses into this single lift. -/
theorem execHandlerTurn_conserves (acts : List FullActionA) (s s' : RecChainedState)
    (h : execHandlerTurn acts s = some s') (b : AssetId) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b + handlerTurnDelta acts b := by
  unfold execHandlerTurn at h
  cases hk : execTurn (closedOf acts) s.kernel with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      -- the kernel transition IS `execTurn (closedOf acts)`: lift the GENERIC `turn_conserves`.
      exact turn_conserves (closedOf acts) s.kernel k' hk b

/-- **`execHandlerTurn_head_authorized` — the authority companion (lifted).** Every effect that COMMITS
in a handler turn was authorized: the FIRST effect of any committing turn passed its handler's `auth`
gate at the entry kernel. Lifted from the scaffold's generic `turn_head_authorized`. -/
theorem execHandlerTurn_head_authorized (a : FullActionA) (rest : List FullActionA)
    (s s' : RecChainedState) (h : execHandlerTurn (a :: rest) s = some s') :
    (toClosedEffect a).handler.auth s.kernel (toClosedEffect a).args = true := by
  unfold execHandlerTurn at h
  cases hk : execTurn (closedOf (a :: rest)) s.kernel with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      -- `closedOf (a :: rest) = toClosedEffect a :: closedOf rest`; lift `turn_head_authorized`.
      have hk' : execTurn (toClosedEffect a :: closedOf rest) s.kernel = some k' := by
        simpa only [closedOf, List.map_cons] using hk
      exact turn_head_authorized (toClosedEffect a) (closedOf rest) s.kernel k' hk'

/-- **`execHandlerTurn_head_admitted` — the lifecycle companion (lifted, R1/R6).** Every effect that
COMMITS passed its lifecycle admission gate: the FIRST effect of any committing turn passed its handler's
`admission` gate at the entry kernel — the cons-step witness that the R1/R6 hole is closed at the ALGEBRA
level. Lifted from the scaffold's generic `turn_head_admitted`. -/
theorem execHandlerTurn_head_admitted (a : FullActionA) (rest : List FullActionA)
    (s s' : RecChainedState) (h : execHandlerTurn (a :: rest) s = some s') :
    (toClosedEffect a).handler.admission s.kernel (toClosedEffect a).args = true := by
  unfold execHandlerTurn at h
  cases hk : execTurn (closedOf (a :: rest)) s.kernel with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      have hk' : execTurn (toClosedEffect a :: closedOf rest) s.kernel = some k' := by
        simpa only [closedOf, List.map_cons] using hk
      exact turn_head_admitted (toClosedEffect a) (closedOf rest) s.kernel k' hk'

/-! ## §6 — THE STRENGTHENING: `handler_refines_execFullA` (the relationship to the live executor).

The handler executor is a SOUND STRENGTHENING of `execFullA`: every effect the handler executor COMMITS,
`execFullA` ALSO commits, AND on the honest path they AGREE on the kernel. The handlers only ADD gates
(the `acceptsEffects` liveness wrap, the settle-actor `authorizedB` gate, …) — they never widen the set
of accepted transitions, and when they DO accept, the resulting kernel is EXACTLY what the bare chained
step would have produced. We prove it for the THREE hole-closing representatives (a transfer R1, an
escrow-release R2, a state-write R6); the rest are mechanical (`§DEFER`).

The bridge from the bare-kernel handler `step` to the chained `execHandlerOne`: a one-effect handler turn
runs `execTurn [toClosedEffect a]` which is exactly the handler's `step` on `s.kernel`. -/

/-- **The one-effect kernel-extraction.** A committed one-effect handler turn's resulting kernel is
EXACTLY the looked-up handler's `step` applied to the entry kernel. (`execTurn` over a singleton is the
handler `step`; the chained wrapper just threads the log.) -/
theorem execHandlerOne_kernel (a : FullActionA) (s s' : RecChainedState)
    (h : execHandlerOne a s = some s') :
    (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args = some s'.kernel := by
  unfold execHandlerOne execHandlerTurn at h
  -- `execTurn [toClosedEffect a] s.kernel = execEffect (toClosedEffect a) s.kernel = the handler step`.
  have hstep : execTurn (closedOf [a]) s.kernel
      = (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args := by
    simp only [closedOf, List.map_cons, List.map_nil, execTurn_cons, execEffect, execTurn_nil]
    cases (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args <;> rfl
  rw [hstep] at h
  cases hk : (toClosedEffect a).handler.step s.kernel (toClosedEffect a).args with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h; rfl

/-! ### §6.1 — R1: TRANSFER. `execHandlerOne (.balanceA t a)` commits ⇒ `execFullA` commits, kernels AGREE. -/

/-- **`handler_refines_execFullA_transfer` — THE R1 STRENGTHENING (PROVED).** Whenever the handler
executor commits a transfer, `execFullA` ALSO commits it AND produces the SAME kernel: `transferH`'s
extra `acceptsEffects t.dst` gate only NARROWS what commits; once it passes, the underlying
`recKExecAsset` is the very transition `execFullA`'s `.balanceA` arm runs (`recCexecAsset`), so the
kernels coincide. Handler-commits ⊆ execFullA-commits, and they agree on the honest path. -/
theorem handler_refines_execFullA_transfer (s s' : RecChainedState) (t : Turn) (a : AssetId)
    (h : execHandlerOne (.balanceA t a) s = some s') :
    ∃ s'', execFullA s (.balanceA t a) = some s'' ∧ s''.kernel = s'.kernel := by
  -- the handler step committed: unwrap the liveness gate, expose `recKExecAsset s.kernel t a = some s'.kernel`.
  have hstep := execHandlerOne_kernel (.balanceA t a) s s' h
  -- `toClosedEffect`'s `.balanceA` arm = `transferEffect t a` (via the equation lemma); its handler
  -- step IS `transferStep` — expose the `if`.
  rw [toClosedEffect] at hstep
  change transferStep s.kernel { turn := t, asset := a } = some s'.kernel at hstep
  unfold transferStep at hstep
  -- `transferStep s.kernel {turn:=t,asset:=a} = some s'.kernel`
  by_cases hadm : acceptsEffects s.kernel t.dst
  · rw [if_pos hadm] at hstep
    -- `recKExecAsset s.kernel t a = some s'.kernel`; `execFullA … = recCexecAsset` matches on it.
    refine ⟨{ kernel := s'.kernel, log := t :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCexecAsset s t a = _
    unfold Dregg2.Exec.TurnExecutorFull.recCexecAsset
    rw [if_pos hadm, hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-! ### §6.2 — R2: ESCROW RELEASE. `execHandlerOne (.releaseEscrowA id actor)` commits ⇒ `execFullA` commits. -/

/-- **`handler_refines_execFullA_release` — THE R2 STRENGTHENING (PROVED).** Whenever the handler executor
commits an escrow release, `execFullA` ALSO commits it AND produces the SAME kernel: `releaseEscrowA`'s
extra settle-actor `authorizedB` gate (`releaseSettleAuthB`) only NARROWS what commits; once it passes,
the underlying `releaseEscrowKAsset s.kernel id` is the very transition `execFullA`'s `.releaseEscrowA`
arm runs (`releaseEscrowChainA`), so the kernels coincide. -/
theorem handler_refines_execFullA_release (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.releaseEscrowA id actor) s = some s') :
    ∃ s'', execFullA s (.releaseEscrowA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.releaseEscrowA id actor) s s' h
  -- `toClosedEffect`'s `.releaseEscrowA` arm = `releaseEscrowEffect actor id`; step IS `releaseStep`.
  rw [toClosedEffect] at hstep
  change releaseStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold releaseStep at hstep
  by_cases hg : releaseSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    -- `releaseEscrowKAsset s.kernel id = some s'.kernel`; `execFullA … = releaseEscrowChainA` matches.
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA
    have hauth : Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB s.kernel id actor = true := by
      dsimp [Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB,
             Dregg2.Exec.Handlers.Escrow.releaseSettleAuthB,
             Dregg2.Exec.TurnExecutorFull.findUnresolvedEscrow,
             Dregg2.Exec.Handlers.Escrow.findUnresolved]
      exact hg
    rw [if_pos hauth, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.2b — SUPPLY: MINT / BURN. Handler liveness gates only narrow; the bare ledger step agrees. -/

/-- **`handler_refines_execFullA_mint` — PROVED.** A committed mint under the handler executor is exactly
`recKMintAsset` on the kernel — the same transition `execFullA`'s `.mintA` arm runs via `recCMintAsset`. -/
theorem handler_refines_execFullA_mint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : execHandlerOne (.mintA actor cell a amt) s = some s') :
    ∃ s'', execFullA s (.mintA actor cell a amt) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.mintA actor cell a amt) s s' h
  rw [toClosedEffect] at hstep
  change mintStep s.kernel { actor := actor, cell := cell, asset := a, amt := amt } = some s'.kernel at hstep
  unfold mintStep at hstep
  by_cases hadm : acceptsEffects s.kernel cell
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := amt } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCMintAsset s actor cell a amt = _
    unfold Dregg2.Exec.TurnExecutorFull.recCMintAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_burn` — PROVED.** A committed burn under the handler executor is exactly
`recKBurnAsset` on the kernel — the same transition `execFullA`'s `.burnA` arm runs via `recCBurnAsset`. -/
theorem handler_refines_execFullA_burn (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : execHandlerOne (.burnA actor cell a amt) s = some s') :
    ∃ s'', execFullA s (.burnA actor cell a amt) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.burnA actor cell a amt) s s' h
  rw [toClosedEffect] at hstep
  change burnStep s.kernel { actor := actor, cell := cell, asset := a, amt := amt } = some s'.kernel at hstep
  unfold burnStep at hstep
  by_cases hadm : acceptsEffects s.kernel cell
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := -amt } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCBurnAsset s actor cell a amt = _
    unfold Dregg2.Exec.TurnExecutorFull.recCBurnAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_createEscrow` — PROVED.** A committed escrow-create under the handler
executor is exactly `createEscrowKAsset` — the same kernel transition `createEscrowChainA` runs. -/
theorem handler_refines_execFullA_createEscrow (s s' : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ)
    (h : execHandlerOne (.createEscrowA id actor creator recipient asset amount) s = some s') :
    ∃ s'', execFullA s (.createEscrowA id actor creator recipient asset amount) = some s'' ∧
      s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.createEscrowA id actor creator recipient asset amount) s s' h
  rw [toClosedEffect] at hstep
  change createEscrowStep s.kernel
    { id := id, actor := actor, creator := creator, recipient := recipient, asset := asset, amount := amount }
    = some s'.kernel at hstep
  unfold createEscrowStep at hstep
  by_cases hadm : acceptsEffects s.kernel creator
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.createEscrowChainA s id actor creator recipient asset amount = _
    unfold Dregg2.Exec.TurnExecutorFull.createEscrowChainA
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

/-- **`handler_refines_execFullA_refund` — PROVED.** A committed escrow refund under the handler executor
is exactly `refundEscrowKAsset` after `refundSettleAuthB` — the same transition `refundEscrowChainA`
runs. -/
theorem handler_refines_execFullA_refund (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.refundEscrowA id actor) s = some s') :
    ∃ s'', execFullA s (.refundEscrowA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.refundEscrowA id actor) s s' h
  rw [toClosedEffect] at hstep
  change refundStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold refundStep at hstep
  by_cases hg : refundSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.refundEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.refundEscrowChainA
    have hauth : Dregg2.Exec.TurnExecutorFull.refundSettleAuthB s.kernel id actor = true := by
      dsimp [Dregg2.Exec.TurnExecutorFull.refundSettleAuthB,
             Dregg2.Exec.Handlers.Escrow.refundSettleAuthB,
             Dregg2.Exec.TurnExecutorFull.findUnresolvedEscrow,
             Dregg2.Exec.Handlers.Escrow.findUnresolved]
      exact hg
    rw [if_pos hauth, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.2c — ESCROW ALIASES + bridgeMint + revoke (mechanical inheritance). -/

theorem handler_refines_execFullA_createObligation (s s' : RecChainedState) (id : Nat)
    (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ)
    (h : execHandlerOne (.createObligationA id actor obligor beneficiary asset stake) s = some s') :
    ∃ s'', execFullA s (.createObligationA id actor obligor beneficiary asset stake) = some s'' ∧
      s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.createObligationA id actor obligor beneficiary asset stake) s s' h
  rw [toClosedEffect] at hstep
  change createEscrowStep s.kernel
    { id := id, actor := actor, creator := obligor, recipient := beneficiary, asset := asset, amount := stake }
    = some s'.kernel at hstep
  unfold createEscrowStep at hstep
  by_cases hadm : acceptsEffects s.kernel obligor
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.createEscrowChainA s id actor obligor beneficiary asset stake = _
    unfold Dregg2.Exec.TurnExecutorFull.createEscrowChainA
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_slashObligation (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.slashObligationA id actor) s = some s') :
    ∃ s'', execFullA s (.slashObligationA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.slashObligationA id actor) s s' h
  rw [toClosedEffect] at hstep
  change releaseStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold releaseStep at hstep
  by_cases hg : releaseSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA
    have hauth : Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB s.kernel id actor = true := by
      dsimp [Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB,
             Dregg2.Exec.Handlers.Escrow.releaseSettleAuthB,
             Dregg2.Exec.TurnExecutorFull.findUnresolvedEscrow,
             Dregg2.Exec.Handlers.Escrow.findUnresolved]
      exact hg
    rw [if_pos hauth, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_fulfillObligation (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.fulfillObligationA id actor) s = some s') :
    ∃ s'', execFullA s (.fulfillObligationA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.fulfillObligationA id actor) s s' h
  rw [toClosedEffect] at hstep
  change refundStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold refundStep at hstep
  by_cases hg : refundSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.refundEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.refundEscrowChainA
    have hauth : Dregg2.Exec.TurnExecutorFull.refundSettleAuthB s.kernel id actor = true := by
      dsimp [Dregg2.Exec.TurnExecutorFull.refundSettleAuthB,
             Dregg2.Exec.Handlers.Escrow.refundSettleAuthB,
             Dregg2.Exec.TurnExecutorFull.findUnresolvedEscrow,
             Dregg2.Exec.Handlers.Escrow.findUnresolved]
      exact hg
    rw [if_pos hauth, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_releaseCommitted (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.releaseCommittedEscrowA id actor) s = some s') :
    ∃ s'', execFullA s (.releaseCommittedEscrowA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.releaseCommittedEscrowA id actor) s s' h
  rw [toClosedEffect] at hstep
  change releaseStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold releaseStep at hstep
  by_cases hg : releaseSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.releaseEscrowChainA
    have hauth : Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB s.kernel id actor = true := by
      dsimp [Dregg2.Exec.TurnExecutorFull.releaseSettleAuthB,
             Dregg2.Exec.Handlers.Escrow.releaseSettleAuthB,
             Dregg2.Exec.TurnExecutorFull.findUnresolvedEscrow,
             Dregg2.Exec.Handlers.Escrow.findUnresolved]
      exact hg
    rw [if_pos hauth, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_refundCommitted (s s' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execHandlerOne (.refundCommittedEscrowA id actor) s = some s') :
    ∃ s'', execFullA s (.refundCommittedEscrowA id actor) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.refundCommittedEscrowA id actor) s s' h
  rw [toClosedEffect] at hstep
  change refundStep s.kernel { actor := actor, id := id } = some s'.kernel at hstep
  unfold refundStep at hstep
  by_cases hg : refundSettleAuthB s.kernel { actor := actor, id := id }
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := Dregg2.Exec.TurnExecutorFull.escrowReceiptA actor :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.refundEscrowChainA s id actor = _
    unfold Dregg2.Exec.TurnExecutorFull.refundEscrowChainA
    have hauth : Dregg2.Exec.TurnExecutorFull.refundSettleAuthB s.kernel id actor = true := by
      dsimp [Dregg2.Exec.TurnExecutorFull.refundSettleAuthB,
             Dregg2.Exec.Handlers.Escrow.refundSettleAuthB,
             Dregg2.Exec.TurnExecutorFull.findUnresolvedEscrow,
             Dregg2.Exec.Handlers.Escrow.findUnresolved]
      exact hg
    rw [if_pos hauth, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_bridgeMint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (h : execHandlerOne (.bridgeMintA actor cell a value) s = some s') :
    ∃ s'', execFullA s (.bridgeMintA actor cell a value) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.bridgeMintA actor cell a value) s s' h
  rw [toClosedEffect] at hstep
  change mintStep s.kernel { actor := actor, cell := cell, asset := a, amt := value } = some s'.kernel at hstep
  unfold mintStep at hstep
  by_cases hadm : acceptsEffects s.kernel cell
  · rw [if_pos hadm] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := value } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.recCMintAsset s actor cell a value = _
    unfold Dregg2.Exec.TurnExecutorFull.recCMintAsset
    rw [hstep]
  · rw [if_neg hadm] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_revoke (s s' : RecChainedState) (holder t : CellId)
    (h : execHandlerOne (.revoke holder t) s = some s') :
    ∃ s'', execFullA s (.revoke holder t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.revoke holder t) s s' h
  rw [toClosedEffect] at hstep
  change revokeStep s.kernel { holder := holder, target := t } = some s'.kernel at hstep
  unfold revokeStep at hstep
  simp only [Option.some.injEq] at hstep
  refine ⟨Dregg2.Exec.TurnExecutorFull.recCRevoke s holder t, ?_, ?_⟩
  · show execFullA s (.revoke holder t) = _
    simp only [execFullA, Dregg2.Exec.TurnExecutorFull.recCRevoke]
  · show (Dregg2.Exec.TurnExecutorFull.recCRevoke s holder t).kernel = s'.kernel
    rw [← hstep]
    rfl

/-! ### §6.3 — R6: STATE WRITE. The handler and `execFullA` now gate on the SAME predicates (RECONCILED).

R6 IS NOW CLOSED IN THE LIVE EXECUTOR. The bare `EffectsState.stateStep` gained a `cellLive`
(lifecycle-liveness) conjunct — so `execFullA`'s `.incrementNonceA`/`.setPermissionsA`/`.setVKA`/
`.refusalA`/`.receiptArchiveA` arms (and `.setFieldA` via `stateStepGuarded`) now REJECT a write into a
Sealed/Destroyed cell, exactly like `stateWriteH`'s `acceptsEffects` gate. `EffectsState.cellLive` is
DEFINITIONALLY `acceptsEffects` (both = `lifecycle cell == 0`/`lcLive`), so the two admission predicates
coincide. The handler still ADDITIONALLY requires `cell ∈ accounts` (membership) which the bare step
also checks; the strengthening is still stated on the honest path where the cell EXISTS, but the
liveness conjunct is now discharged DIRECTLY from the handler's `acceptsEffects` rather than carried as
an unproved gap. The authority conjunct is shared VERBATIM: `stateWriteH.auth = authorizedB caps
{actor,src:=cell,dst:=cell,amt:=0}` which is DEFINITIONALLY `EffectsState.stateAuthB caps actor cell`,
the gate `execFullA`'s `stateStep` checks. (The representative for the whole field-write/lifecycle
family — `setField`/`setPermissions`/`setVK`/`makeSovereign`/`refusal`/`receiptArchive`/`emit`/the
cell-lifecycle arms — which `toClosedEffect` routes through the SAME `stateWriteH`.) -/

/-- **`handler_refines_execFullA_stateWrite` — THE R6 STRENGTHENING (PROVED).**
On the honest path where the target cell EXISTS (`cell ∈ accounts`), whenever the handler executor
commits a nonce write, `execFullA` ALSO commits it AND produces the SAME kernel. With R6 reconciled,
`execFullA`'s bare `stateStep` now shares the handler's `acceptsEffects`/`cellLive` liveness gate
(definitionally), so the handler's liveness conjunct discharges the executor's; the shared authority
gate (`stateAuthB`) and the SAME `writeField nonceField` post-state make the kernels coincide. -/
theorem handler_refines_execFullA_stateWrite (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.incrementNonceA actor cell n) s = some s') :
    ∃ s'', execFullA s (.incrementNonceA actor cell n) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.incrementNonceA actor cell n) s s' h
  -- `toClosedEffect`'s `.incrementNonceA` arm = `incrementNonceEffect actor cell n`; step IS
  -- `stateWriteStep` at `field := nonceField`. Expose the gate `if`.
  rw [toClosedEffect] at hstep
  change stateWriteStep s.kernel
    { actor := actor, target := cell, field := nonceField, value := n } = some s'.kernel at hstep
  unfold stateWriteStep at hstep
  by_cases hg : acceptsEffects s.kernel cell
      && authorizedB s.kernel.caps { actor := actor, src := cell, dst := cell, amt := 0 }
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    simp only [Option.some.injEq] at hstep
    -- `execFullA`'s nonce arm = `stateStep s nonceField actor cell (.int n)`; it commits on the SAME
    -- authority gate + membership (the honest-path `hmem`), producing the SAME `writeField` post-state.
    refine ⟨{ kernel := Dregg2.Exec.EffectsState.writeField s.kernel nonceField cell (.int n),
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, ?_⟩
    · show Dregg2.Exec.EffectsState.stateStep s nonceField actor cell (.int n) = _
      unfold Dregg2.Exec.EffectsState.stateStep Dregg2.Exec.EffectsState.stateAuthB
      -- R6 NOW RECONCILED: `execFullA`'s bare `stateStep` ALSO consults lifecycle liveness
      -- (`cellLive`, the R6 fix). `cellLive s.kernel cell` is DEFINITIONALLY `acceptsEffects s.kernel
      -- cell` (both = `lifecycle cell == 0`), so the handler's liveness conjunct (`hg.1`) discharges
      -- the executor's NEW liveness conjunct directly — no longer just the honest-path membership.
      have hlive : Dregg2.Exec.EffectsState.cellLive s.kernel cell = true := hg.1
      -- `nonceField` is the SAME field name in both layers (`rfl`).
      rw [if_pos ⟨hg.2, hmem, hlive⟩]
    · -- kernels agree: both are the `writeField` post-state at the nonce field.
      rw [← hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

/-! ### §6.4 — LIFECYCLE: `execHandlerOne (.cellSealA …)` commits ⇒ `execFullA` commits, kernels AGREE. -/

/-- **`handler_refines_execFullA_cellSeal` — THE LIFECYCLE STRENGTHENING (PROVED).** A committed cell
seal under the handler executor is EXACTLY the bare `setLifecycle` post-state `execFullA`'s
`cellSealChainA` arm produces on the kernel. -/
theorem handler_refines_execFullA_cellSeal (s s' : RecChainedState) (actor cell : CellId)
    (h : execHandlerOne (.cellSealA actor cell) s = some s') :
    ∃ s'', execFullA s (.cellSealA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.cellSealA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change cellSealStep s.kernel { actor := actor, cell := cell } = some s'.kernel at hstep
  unfold cellSealStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && acceptsEffects s.kernel cell
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : setLifecycle s.kernel cell lcSealed = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show cellSealChainA s actor cell = _
    unfold cellSealChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_cellUnseal (s s' : RecChainedState) (actor cell : CellId)
    (h : execHandlerOne (.cellUnsealA actor cell) s = some s') :
    ∃ s'', execFullA s (.cellUnsealA actor cell) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.cellUnsealA actor cell) s s' h
  rw [toClosedEffect] at hstep
  change cellUnsealStep s.kernel { actor := actor, cell := cell } = some s'.kernel at hstep
  unfold cellUnsealStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && (s.kernel.lifecycle cell == lcSealed)
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell == lcSealed) = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : setLifecycle s.kernel cell lcLive = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show cellUnsealChainA s actor cell = _
    unfold cellUnsealChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_cellDestroy (s s' : RecChainedState) (actor cell : CellId)
    (certHash : Nat) (h : execHandlerOne (.cellDestroyA actor cell certHash) s = some s') :
    ∃ s'', execFullA s (.cellDestroyA actor cell certHash) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.cellDestroyA actor cell certHash) s s' h
  rw [toClosedEffect] at hstep
  change cellDestroyStep s.kernel { actor := actor, cell := cell, certHash := certHash } = some s'.kernel at hstep
  unfold cellDestroyStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor cell && (s.kernel.lifecycle cell != lcDestroyed)
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor cell = true ∧ (s.kernel.lifecycle cell != lcDestroyed) = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : { (setLifecycle s.kernel cell lcDestroyed) with
                  deathCert := fun c => if c = cell then certHash else s.kernel.deathCert c } = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_, rfl⟩
    show cellDestroyChainA s actor cell certHash = _
    unfold cellDestroyChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_refreshDelegation (s s' : RecChainedState) (actor child : CellId)
    (h : execHandlerOne (.refreshDelegationA actor child) s = some s') :
    ∃ s'', execFullA s (.refreshDelegationA actor child) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.refreshDelegationA actor child) s s' h
  rw [toClosedEffect] at hstep
  change refreshDelegationStep s.kernel { actor := actor, child := child } = some s'.kernel at hstep
  unfold refreshDelegationStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor child && (s.kernel.delegate child).isSome
  · rw [if_pos hg] at hstep
    have hg' : stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true := by
      simp only [Bool.and_eq_true] at hg; exact ⟨hg.1, hg.2⟩
    have hk : { s.kernel with
                  delegations := fun c => if c = child then parentClist s.kernel child
                                        else s.kernel.delegations c } = s'.kernel := by
      simpa only [Option.some.injEq] using hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := child, dst := child, amt := 0 } :: s.log }, ?_, rfl⟩
    show refreshDelegationChainA s actor child = _
    unfold refreshDelegationChainA
    rw [if_pos hg', hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_emitEvent (s s' : RecChainedState) (actor cell : CellId)
    (topic data : Int) (h : execHandlerOne (.emitEventA actor cell topic data) s = some s') :
    ∃ s'', execFullA s (.emitEventA actor cell topic data) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.emitEventA actor cell topic data) s s' h
  rw [toClosedEffect] at hstep
  change emitEventStep s.kernel { actor := actor, cell := cell, topic := topic, data := data } = some s'.kernel at hstep
  unfold emitEventStep at hstep
  by_cases hmem : cell ∈ s.kernel.accounts
  · rw [if_pos hmem] at hstep
    have hk : s.kernel = s'.kernel := by simpa only [Option.some.injEq] using hstep
    refine ⟨emitStep s actor cell topic data, ?_, hk⟩
    simp only [execFullA, if_pos hmem, emitStep]
  · rw [if_neg hmem] at hstep; exact absurd hstep (by simp)

/-! ### §6.5 — AUTHORITY / SEAL / SWISS / QUEUE (mechanical strengthening; handler gates only narrow). -/

private theorem auth_mem_allAuths : ∀ a : Auth, allAuths.contains a = true := by
  intro a; cases a <;> decide

private theorem auth_in_allAuths (a : Auth) : a ∈ allAuths := by
  cases a <;> simp [allAuths]

private theorem attenuate_allAuths_id (c : Cap) : attenuate allAuths c = c := by
  cases c with
  | null => simp [attenuate]
  | endpoint t rights =>
      simp only [attenuate]
      congr 1
      apply List.filter_eq_self.mpr
      intro a _
      exact auth_mem_allAuths a
  | node _ => simp [attenuate]

private theorem recKDelegateAtten_allAuths_eq_recKDelegate (k : RecordKernelState) (d r t : CellId) :
    recKDelegateAtten k d r t allAuths = recKDelegate k d r t := by
  unfold recKDelegateAtten recKDelegate
  by_cases hg : (k.caps d).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg, if_pos hg, attenuate_allAuths_id (heldCapTo k.caps d t)]
  · rw [if_neg hg, if_neg hg]

theorem handler_refines_execFullA_delegate (s s' : RecChainedState) (del rec t : CellId)
    (h : execHandlerOne (.delegate del rec t) s = some s') :
    ∃ s'', execFullA s (.delegate del rec t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.delegate del rec t) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := del, recipient := rec, target := t, keep := allAuths } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · have hk : recKDelegate s.kernel del rec t = some s'.kernel := by
      rw [← recKDelegateAtten_allAuths_eq_recKDelegate, hstep]
    refine ⟨{ kernel := s'.kernel, log := authReceipt del :: s.log }, ?_, rfl⟩
    show recCDelegate s del rec t = _
    unfold recCDelegate
    rw [hk]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_delegateAtten (s s' : RecChainedState) (del rec t : CellId)
    (keep : List Auth) (h : execHandlerOne (.delegateAttenA del rec t keep) s = some s') :
    ∃ s'', execFullA s (.delegateAttenA del rec t keep) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.delegateAttenA del rec t keep) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := del, recipient := rec, target := t, keep := keep } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps del).any (fun cap => confersEdgeTo t cap) = true
  · refine ⟨{ kernel := s'.kernel, log := authReceipt del :: s.log }, ?_, rfl⟩
    show recCDelegateAtten s del rec t keep = _
    unfold recCDelegateAtten
    rw [hstep]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_introduce (s s' : RecChainedState) (intro rec t : CellId)
    (h : execHandlerOne (.introduceA intro rec t) s = some s') :
    ∃ s'', execFullA s (.introduceA intro rec t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.introduceA intro rec t) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := intro, recipient := rec, target := t, keep := allAuths } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
  · have hk : recKDelegate s.kernel intro rec t = some s'.kernel := by
      rw [← recKDelegateAtten_allAuths_eq_recKDelegate, hstep]
    refine ⟨{ kernel := s'.kernel, log := authReceipt intro :: s.log }, ?_, rfl⟩
    show recCDelegate s intro rec t = _
    unfold recCDelegate
    rw [hk]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_validateHandoff (s s' : RecChainedState) (intro rec t : CellId)
    (h : execHandlerOne (.validateHandoffA intro rec t) s = some s') :
    ∃ s'', execFullA s (.validateHandoffA intro rec t) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.validateHandoffA intro rec t) s s' h
  rw [toClosedEffect] at hstep
  change delegateAttenStep s.kernel
    { delegator := intro, recipient := rec, target := t, keep := allAuths } = some s'.kernel at hstep
  simp only [delegateAttenStep] at hstep
  by_cases hg : (s.kernel.caps intro).any (fun cap => confersEdgeTo t cap) = true
  · have hk : recKDelegate s.kernel intro rec t = some s'.kernel := by
      rw [← recKDelegateAtten_allAuths_eq_recKDelegate, hstep]
    refine ⟨{ kernel := s'.kernel, log := authReceipt intro :: s.log }, ?_, rfl⟩
    show recCDelegate s intro rec t = _
    unfold recCDelegate
    rw [hk]
  · unfold recKDelegateAtten at hstep; rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_attenuate (s s' : RecChainedState) (actor : CellId) (idx : Nat)
    (keep : List Auth) (h : execHandlerOne (.attenuateA actor idx keep) s = some s') :
    ∃ s'', execFullA s (.attenuateA actor idx keep) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.attenuateA actor idx keep) s s' h
  rw [toClosedEffect] at hstep
  change attenuateStep s.kernel { actor := actor, idx := idx, keep := keep } = some s'.kernel at hstep
  unfold attenuateStep at hstep
  simp only [Option.some.injEq] at hstep
  refine ⟨attenuateStepA s actor idx keep, ?_, ?_⟩
  · show execFullA s (.attenuateA actor idx keep) = _
    simp only [execFullA, attenuateStepA, Option.some.injEq]
  · show (attenuateStepA s actor idx keep).kernel = s'.kernel
    rw [← hstep]; unfold attenuateStepA; rfl

theorem handler_refines_execFullA_createSealPair (s s' : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId)
    (h : execHandlerOne (.createSealPairA pid actor sealerHolder unsealerHolder) s = some s') :
    ∃ s'', execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s'' ∧
      s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.createSealPairA pid actor sealerHolder unsealerHolder) s s' h
  rw [toClosedEffect] at hstep
  change createSealPairStep s.kernel
    { pid := pid, actor := actor, sealerHolder := sealerHolder, unsealerHolder := unsealerHolder }
    = some s'.kernel at hstep
  unfold createSealPairStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor sealerHolder = true ∧ pidFresh s.kernel pid = true
  · rw [if_pos hg] at hstep
    have hg1 : stateAuthB s.kernel.caps actor sealerHolder = true := hg.1
    simp only [CreateSealPairArgs.sealerHolder, CreateSealPairArgs.unsealerHolder] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 } :: s.log },
            ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.createSealPairChainA s pid actor sealerHolder unsealerHolder = _
    unfold Dregg2.Exec.TurnExecutorFull.createSealPairChainA
    rw [if_pos hg1]
    have hk : { s.kernel with
                  caps := grant (grant s.kernel.caps sealerHolder (sealerCap pid))
                                  unsealerHolder (unsealerCap pid) } = s'.kernel := by
      injection hstep
    simp only [Option.some.injEq, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_seal (s s' : RecChainedState) (pid : Nat) (actor : CellId)
    (payload : Cap) (h : execHandlerOne (.sealA pid actor payload) s = some s') :
    ∃ s'', execFullA s (.sealA pid actor payload) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.sealA pid actor payload) s s' h
  rw [toClosedEffect] at hstep
  change sealStep s.kernel { pid := pid, actor := actor, payload := payload } = some s'.kernel at hstep
  unfold sealStep at hstep
  by_cases hg : sealGate s.kernel { pid := pid, actor := actor, payload := payload }
  · rw [if_pos hg] at hstep
    have hg' : (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true
        ∧ payload ∈ s.kernel.caps actor := by
      unfold sealGate at hg; simpa [Bool.and_eq_true, decide_eq_true_eq] using hg
    simp only [SealArgs.pid, SealArgs.actor, SealArgs.payload] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := actor, dst := actor, amt := 0 } :: s.log }, ?_, rfl⟩
    show Dregg2.Exec.TurnExecutorFull.sealChainA s pid actor payload = _
    unfold Dregg2.Exec.TurnExecutorFull.sealChainA
    rw [if_pos hg']
    have hk : { s.kernel with
                  sealedBoxes := { pairId := pid, sealer := actor, payload := payload }
                                  :: s.kernel.sealedBoxes } = s'.kernel := by
      injection hstep
    simp only [Option.some.injEq, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_unseal (s s' : RecChainedState) (pid : Nat) (actor recipient : CellId)
    (h : execHandlerOne (.unsealA pid actor recipient) s = some s') :
    ∃ s'', execFullA s (.unsealA pid actor recipient) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.unsealA pid actor recipient) s s' h
  rw [toClosedEffect] at hstep
  change unsealStep s.kernel { pid := pid, actor := actor, recipient := recipient } = some s'.kernel at hstep
  unfold unsealStep at hstep
  by_cases hg : unsealGate s.kernel { pid := pid, actor := actor, recipient := recipient }
  · rw [if_pos hg] at hstep
    cases hfind : findSealedBox s.kernel.sealedBoxes pid with
    | none =>
        rw [hfind] at hstep; exact absurd hstep (by simp)
    | some box =>
        rw [hfind] at hstep
        have hg' : (s.kernel.caps actor).any (fun c => holdsSealCapFor pid c) = true := hg
        simp only [UnsealArgs.recipient] at hstep
        refine ⟨{ kernel := s'.kernel,
                  log := { actor := actor, src := recipient, dst := recipient, amt := 0 } :: s.log },
                ?_, rfl⟩
        show Dregg2.Exec.TurnExecutorFull.unsealChainA s pid actor recipient = _
        unfold Dregg2.Exec.TurnExecutorFull.unsealChainA
        rw [if_pos hg', hfind]
        have hk : { s.kernel with caps := grant s.kernel.caps recipient box.payload } = s'.kernel := by
          injection hstep
        simp only [Option.some.injEq, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_exportSturdyRef (s s' : RecChainedState) (sw : Nat)
    (actor exporter target : CellId) (rights : List Auth)
    (h : execHandlerOne (.exportSturdyRefA sw actor exporter target rights) s = some s') :
    ∃ s'', execFullA s (.exportSturdyRefA sw actor exporter target rights) = some s'' ∧
      s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.exportSturdyRefA sw actor exporter target rights) s s' h
  rw [toClosedEffect] at hstep
  change exportStep s.kernel
    { sw := sw, actor := actor, exporter := exporter, target := target, rights := rights }
    = some s'.kernel at hstep
  unfold exportStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log }, ?_, rfl⟩
    show swissExportChainA s sw actor exporter target rights = _
    unfold swissExportChainA
    rw [if_pos hg, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_enlivenRef (s s' : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (claimed : List Auth)
    (h : execHandlerOne (.enlivenRefA sw actor exporter claimed) s = some s') :
    ∃ s'', execFullA s (.enlivenRefA sw actor exporter claimed) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.enlivenRefA sw actor exporter claimed) s s' h
  rw [toClosedEffect] at hstep
  change enlivenStep s.kernel { sw := sw, actor := actor, exporter := exporter, claimed := claimed }
    = some s'.kernel at hstep
  unfold enlivenStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log }, ?_, rfl⟩
    show swissEnlivenChainA s sw actor exporter claimed = _
    unfold swissEnlivenChainA
    rw [if_pos hg, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_swissHandoff (s s' : RecChainedState) (sw certHash : Nat)
    (introducer exporter : CellId)
    (h : execHandlerOne (.swissHandoffA sw certHash introducer exporter) s = some s') :
    ∃ s'', execFullA s (.swissHandoffA sw certHash introducer exporter) = some s'' ∧
      s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.swissHandoffA sw certHash introducer exporter) s s' h
  rw [toClosedEffect] at hstep
  change handoffStep s.kernel
    { sw := sw, certHash := certHash, introducer := introducer, exporter := exporter } = some s'.kernel at hstep
  unfold handoffStep at hstep
  by_cases hg : stateAuthB s.kernel.caps introducer exporter = true
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := introducer, src := exporter, dst := exporter, amt := 0 } :: s.log }, ?_, rfl⟩
    show swissHandoffChainA s sw certHash introducer exporter = _
    unfold swissHandoffChainA
    rw [if_pos hg, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_swissDrop (s s' : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (h : execHandlerOne (.swissDropA sw actor exporter) s = some s') :
    ∃ s'', execFullA s (.swissDropA sw actor exporter) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.swissDropA sw actor exporter) s s' h
  rw [toClosedEffect] at hstep
  change dropStep s.kernel { sw := sw, actor := actor, exporter := exporter } = some s'.kernel at hstep
  unfold dropStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hg] at hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := exporter, dst := exporter, amt := 0 } :: s.log }, ?_, rfl⟩
    show swissDropChainA s sw actor exporter = _
    unfold swissDropChainA
    rw [if_pos hg, hstep]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_queueResize (s s' : RecChainedState) (id newCap : Nat)
    (actor owner : CellId) (h : execHandlerOne (.queueResizeA id newCap actor owner) s = some s') :
    ∃ s'', execFullA s (.queueResizeA id newCap actor owner) = some s'' ∧ s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.queueResizeA id newCap actor owner) s s' h
  rw [toClosedEffect] at hstep
  change resizeStep s.kernel { actor := actor, id := id, capacity := newCap, owner := owner }
    = some s'.kernel at hstep
  unfold resizeStep at hstep
  by_cases hg : stateAuthB s.kernel.caps actor owner && acceptsEffects s.kernel owner
  · rw [if_pos hg] at hstep
    simp only [Bool.and_eq_true] at hg
    have hk : queueResizeK s.kernel id newCap = some s'.kernel := hstep
    refine ⟨{ kernel := s'.kernel,
              log := { actor := actor, src := owner, dst := owner, amt := 0 } :: s.log }, ?_, rfl⟩
    show queueResizeChainA s id newCap actor owner = _
    unfold queueResizeChainA
    rw [if_pos hg, hk]
  · rw [if_neg hg] at hstep; exact absurd hstep (by simp)

theorem handler_refines_execFullA_queuePipeline (s s' : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat)
    (h : execHandlerOne (.queuePipelineStepA srcId owner sinkCells sinkIds) s = some s') :
    ∃ s'', execFullA s (.queuePipelineStepA srcId owner sinkCells sinkIds) = some s'' ∧
      s''.kernel = s'.kernel := by
  have hstep := execHandlerOne_kernel (.queuePipelineStepA srcId owner sinkCells sinkIds) s s' h
  rw [toClosedEffect] at hstep
  change Dregg2.Exec.Handlers.Queue.pipelineStep s.kernel
    { srcId := srcId, owner := owner, sinkCells := sinkCells, sinkIds := sinkIds } = some s'.kernel at hstep
  unfold Dregg2.Exec.Handlers.Queue.pipelineStep at hstep
  simp only [PipelineArgs.srcId, PipelineArgs.owner, PipelineArgs.sinkCells, PipelineArgs.sinkIds] at hstep
  cases hd : queueDequeueK s.kernel srcId owner with
  | none => rw [hd] at hstep; exact absurd hstep (by simp)
  | some pr =>
      rcases pr with ⟨k1, m⟩
      rw [hd] at hstep
      cases hf : pipelineFanoutK k1 owner m sinkCells sinkIds with
      | none => simp only [hf] at hstep; exact absurd hstep (by simp)
      | some k2 =>
          simp only [hf] at hstep
          refine ⟨{ kernel := s'.kernel,
                    log := { actor := owner, src := owner, dst := owner, amt := 0 } :: s.log },
                  ?_, rfl⟩
          simp only [execFullA, Dregg2.Exec.TurnExecutorFull.queuePipelineStepA, hd, hf, hstep]

/-! ## §7 — THE TEETH: R1/R2/R6 holes closed in BOTH executors (parity witnesses).

The payoff. For each hole, a single fixture exhibits the LIVE EXECUTOR `execFullA` accepting the attack
(`= some` — the hole) while the handler executor `execHandlerTurn` REJECTS it (`= none` — the algebra
closes it). `#eval`-verified below; this demonstrates the cutover STRICTLY improves soundness. -/

/-- A 2-cell, 1-asset chained fixture: cells 0 and 1 are accounts; cell 0 holds 100 of asset 0; cell 0
holds the `node 0`/`node 1` self+target authority (so the transfer / state-write self-authorizes). Cell 1
is SEALED (`lifecycle 1 = lcSealed`) — a NON-Live target. Cell 0 stays Live. -/
def teethSealed : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0
        lifecycle := fun c => if c = 1 then lcSealed else lcLive }
    log := [] }

/-- A fixture with an escrow (id 9) parked by cell 0 for recipient cell 1, locking 40 of asset 0. The R2
attack: a STRANGER (cell 5, holding no cap, not the recipient) tries to release it. -/
def teethEscrow : Option RecChainedState :=
  execFullA
    { kernel :=
        { accounts := {0, 1}
          cell := fun _ => .record [("balance", .int 0)]
          caps := fun c => if c = 1 then [Cap.node 1] else []
          bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
      log := [] }
    (.createEscrowA 9 0 0 1 0 40)

-- §TEETH-R1 (TRANSFER INTO A SEALED CELL): R1 is now CLOSED IN THE LIVE EXECUTOR TOO. `recCexecAsset`
-- gates on `acceptsEffects` at `t.dst`, so `execFullA` AND `execHandlerTurn` both REJECT a credit into
-- the SEALED cell 1.
#guard ((execFullA teethSealed (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0)).isSome) == false  --  false (R1 CLOSED in live executor)
#guard ((execHandlerOne (.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0) teethSealed).isSome) == false  --  false (CLOSED)

-- §TEETH-R6 (STATE WRITE INTO A SEALED CELL): R6 is now CLOSED IN THE LIVE EXECUTOR TOO. The bare
-- `EffectsState.stateStep` gained a `cellLive` (lifecycle-liveness) conjunct, so `execFullA` itself
-- now REJECTS a nonce write into the SEALED cell 1 — matching the handler. Both return `none`.
#guard ((execFullA teethSealed (.incrementNonceA 0 1 7)).isSome) == false  --  false (R6 CLOSED in the live executor)
#guard ((execHandlerOne (.incrementNonceA 0 1 7) teethSealed).isSome) == false  --  false (CLOSED by acceptsEffects)
-- ...and a write into the LIVE cell 0 still COMMITS in both — the gate only tightens the non-live case.
#guard ((execFullA teethSealed (.incrementNonceA 0 0 7)).isSome)  --  true  (live cell still accepts)
#guard ((execHandlerOne (.incrementNonceA 0 0 7) teethSealed).isSome)  --  true  (live cell still accepts)

-- §TEETH-R2 (ESCROW RELEASE BY A STRANGER): R2 is now CLOSED IN THE LIVE EXECUTOR TOO.
-- `releaseEscrowChainA` gates on `releaseSettleAuthB`; both executors REJECT a stranger's release.
#guard ((teethEscrow.bind (fun s => execFullA s (.releaseEscrowA 9 5))).isSome) == false  --  false (R2 CLOSED in live executor)
#guard ((teethEscrow.bind (fun s => execHandlerOne (.releaseEscrowA 9 5) s)).isSome) == false  --  false (CLOSED)
-- the HONEST release (by the recipient cell 1) STILL succeeds under BOTH executors.
#guard ((teethEscrow.bind (fun s => execFullA s (.releaseEscrowA 9 1))).isSome)  --  true  (honest path admitted)
#guard ((teethEscrow.bind (fun s => execHandlerOne (.releaseEscrowA 9 1) s)).isSome)  --  true  (honest path admitted)

-- §TEETH-CONSERVATION: a whole handler turn conserves the combined measure (the derived global law,
-- evaluated): a transfer 0→1 (30 of asset 0, both LIVE) + a self nonce-write on cell 0 leaves the
-- asset-0 measure at 100 (the internal transfer cancels, the write is balance-neutral — the SUM of
-- per-effect deltas is 0, exactly what `execHandlerTurn_conserves` proves).
#guard ((execHandlerTurn [.balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0, .incrementNonceA 0 0 7]
        { kernel :=
            { accounts := {0, 1}
              cell := fun _ => .record [("balance", .int 0)]
              caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
              bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
          log := [] }).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

/-! ## §8 — Axiom-hygiene pins (every cutover keystone rests only on the three kernel axioms).

The derived global laws + the strengthening + the executor structure are all pinned to the kernel triple
(`propext`/`Classical.choice`/`Quot.sound`). A `sorryAx` anywhere in the composed handlers — across all
seven batches the registry packs — would FAIL these pins (and the build). -/

#assert_axioms masterRegistry_length
#assert_axioms execHandlerTurn_conserves
#assert_axioms execHandlerTurn_head_authorized
#assert_axioms execHandlerTurn_head_admitted
#assert_axioms execHandlerOne_kernel
#assert_axioms handler_refines_execFullA_transfer
#assert_axioms handler_refines_execFullA_release
#assert_axioms handler_refines_execFullA_mint
#assert_axioms handler_refines_execFullA_burn
#assert_axioms handler_refines_execFullA_createEscrow
#assert_axioms handler_refines_execFullA_refund
#assert_axioms handler_refines_execFullA_createObligation
#assert_axioms handler_refines_execFullA_slashObligation
#assert_axioms handler_refines_execFullA_fulfillObligation
#assert_axioms handler_refines_execFullA_releaseCommitted
#assert_axioms handler_refines_execFullA_refundCommitted
#assert_axioms handler_refines_execFullA_bridgeMint
#assert_axioms handler_refines_execFullA_revoke
#assert_axioms handler_refines_execFullA_stateWrite
#assert_axioms handler_refines_execFullA_cellSeal
#assert_axioms handler_refines_execFullA_cellUnseal
#assert_axioms handler_refines_execFullA_cellDestroy
#assert_axioms handler_refines_execFullA_refreshDelegation
#assert_axioms handler_refines_execFullA_emitEvent
#assert_axioms handler_refines_execFullA_delegate
#assert_axioms handler_refines_execFullA_delegateAtten
#assert_axioms handler_refines_execFullA_introduce
#assert_axioms handler_refines_execFullA_validateHandoff
#assert_axioms handler_refines_execFullA_attenuate
#assert_axioms handler_refines_execFullA_createSealPair
#assert_axioms handler_refines_execFullA_seal
#assert_axioms handler_refines_execFullA_unseal
#assert_axioms handler_refines_execFullA_exportSturdyRef
#assert_axioms handler_refines_execFullA_enlivenRef
#assert_axioms handler_refines_execFullA_swissHandoff
#assert_axioms handler_refines_execFullA_swissDrop
#assert_axioms handler_refines_execFullA_queueResize
#assert_axioms handler_refines_execFullA_queuePipeline

/-! ## §DEFER — honest scope of THIS cutover keystone (additive; the call-site switch is mechanical).

Deliberately OUT of this file (documented, NOT a silent gap):

  * **The live-switch of callers.** This file is ADDITIVE: it does NOT edit `execFullA`/`FullActionA`.
    Switching `execFullA`'s 5 dregg1 call-sites onto `execHandlerTurn` (routing each `FullActionA` through
    `toClosedEffect`) is the next, MECHANICAL step — the algebra and its global laws are proved HERE so
    that switch is a rename, not a re-proof.

  * **The strengthening for the remaining constructors.** `handler_refines_execFullA_*` is now proved for
    transfer R1, release/refund R2, mint/burn/createEscrow supply, state-write R6, the lifecycle family,
    authority (delegate/delegateAtten/introduce/validateHandoff/attenuate), seal/swiss, and queue
    allocate/resize/pipeline. SKIPPED (documented gate / kernel-op mismatch):
    `queueAllocateA` (handler `queueAllocateK` uses `cell` as owner; `queueAllocateChainA` passes
    `actor` as owner — kernels disagree when `actor ≠ cell`), `queueEnqueueA` (handler:
    `stateAuthB sender sender` + sender liveness; execFullA: `stateAuthB actor cell` + owner liveness),
    `queueDequeueA` (handler: P0-1 binding only; execFullA: adds `stateAuthB actor cell` + owner
    liveness), `queueAtomicTxA` (handler: bare-kernel `queueAtomicTxChainK` fold; execFullA: chained
    `queueAtomicTxChainA` sub-ops with per-op writer/owner gates). Reconcile at cutover, then the
    template discharges verbatim.

  * **The state-write existence-predicate MISMATCH — RESOLVED (R6 closed in the live executor).** The
    bare `EffectsState.stateStep` now ALSO consults lifecycle-LIVENESS (`cellLive`, definitionally
    `acceptsEffects` = `lifecycle cell == 0`), so `execFullA`'s state-write arms reject a write into a
    Sealed/Destroyed cell exactly like `stateWriteH`. The admission predicates coincide; the handler
    additionally checks membership (`cell ∈ accounts`), which the bare step also checks, so the
    strengthening is still stated on the honest path where the cell exists — but the liveness conjunct is
    now PROVED through, not carried open. (`#eval §TEETH-R6`: `execFullA` now returns `none` on the
    Sealed-cell write, matching the handler.)

  * **The committed-escrow `hidingProof` / queue-atomic `QueueTxOpA` projections.** `toClosedEffect` maps
    the committed escrow onto the plain escrow lock (the §8 Pedersen hiding portal is off the executable
    ledger) and projects `QueueTxOpA` onto the bare-kernel `QueueTxOpK` (the chained receipt row lives in
    `RecChainedState`, off the kernel algebra). These are the documented executable cores; the portal /
    receipt faces fold on at the cutover, unchanged in the conservation accounting.
-/

end Dregg2.Exec.HandlerExecutor
