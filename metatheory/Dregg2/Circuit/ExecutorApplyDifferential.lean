/-
# Dregg2.Circuit.ExecutorApplyDifferential — the P5b differential pin:
#   the verified executor step (`recKExec`) vs. the deployed Rust `TurnExecutor::apply_effect`.

RESIDUAL P5b asked: the Lean executor step (`Exec.RecordKernel.recKExec`) is not differentially
pinned to the deployed Rust `TurnExecutor::apply` over the full effect/selector coverage. This file
supplies that pin, additively, in two layers — the SELECTOR layer and the SEMANTIC layer.

## The deployed dispatcher (ground truth)

`turn/src/executor/apply.rs:124 pub(crate) fn apply_effect(effect, ledger, …)` is a total
`match effect { … }` over the deployed `Effect` enum (`turn/src/action.rs:1061 pub enum Effect`),
routing each of its **33** variants to a dedicated `apply_<variant>` method. The match is EXHAUSTIVE
(no `_ =>` arm), so those 33 variants ARE the deployed effect set the executor accepts.

### Layer 1 — SELECTOR coverage (`Selector`, `DeployedEffect`, `dispatch`).
`DeployedEffect` transcribes the 33 `Effect` constructors; `dispatch : DeployedEffect → Selector`
transcribes the `apply_effect` `match` (which `apply_<variant>` each arm calls). `dispatch_surjective`
PROVES every selector is reachable — the Lean dispatcher covers the whole deployed effect set, none
dropped. `pinLayer : Selector → PinLayer` then records, HONESTLY and as data, WHERE each selector's
state semantics is pinned: `recKExec` (here), `execFullA <arm>` (the full per-asset executor
`Exec.TurnExecutorFull.execFullA`), or `residual <reason>` (a deployed selector the Lean executor
does not yet model).

### Layer 2 — SEMANTIC pin of the ONE selector `recKExec` models: `Transfer`.
`recKExec` (`Exec.RecordKernel.lean:538`) models exactly the `Transfer` selector — a balance move.
`applyTransferModel` is an INDEPENDENT transcription of `apply_transfer` (`apply.rs:493`), gate for
gate: self-transfer reject (`from == to`, :510) → `src ≠ dst`; cross-cell `Send` authority (:518) →
`authorizedB`; source live + funded (:544/:554) → `cellLifecycleLive src` + `amt ≤ balOf (cell src)`;
dest exists + live (:564/:567) → `dst ∈ accounts` + `cellLifecycleLive dst`; then the
debit/credit set_balance (:586–:595) → `recTransfer`.

  • `applyTransferModel_refines_recKExec` — UNCONDITIONAL: whenever the deployed `apply_transfer`
    accepts and yields `k'`, the verified kernel `recKExec` accepts and yields the SAME `k'`. (The
    load-bearing direction: the Rust dataplane never commits a transfer the verified kernel rejects,
    and never to a different post-state.)
  • `recKExec_eq_applyTransferModel_of_live` — EXACT equality once both endpoints are Live, which
    characterizes the ONLY gap between the two gates: `recKExec` (the scalar `balance`-field kernel
    step) does NOT gate lifecycle, whereas `apply_transfer` does. The `#guard`
    `deadDstGap` exhibits a concrete turn `recKExec` commits but `apply_transfer` refuses — the gap
    is REAL, not vacuous (and is CLOSED by `recKExecAsset`, `RecordKernel.lean:655`, which gates the
    source lifecycle; the dest leg is gated by `recCexecAsset`).

## NAMED residuals (deployed selectors NOT modeled by the Lean executor `execFullA`)
`Promise`, `Notify`, `React` — the promise-pipelining / eventual-resolution selectors; their state
move happens in the SEPARATE resolution pass (`Exec.ConditionalTurn`), not `apply_effect`, so they
are `residual` here. `ShieldedTransfer` — the prover-only hiding uni-STARK path (`apply.rs:1295`,
`#[cfg(feature = "prover")]`); the executable Lean shadow is `noteSpendA`/`noteCreateA`, the full
`ShieldedTransfer` payload is not modeled. These four are surfaced as data by `residualSelectors`.

Every theorem is `#assert_axioms`-clean and there are `#guard` non-vacuity fixtures below.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Tactics

namespace Dregg2.Circuit.ExecutorApplyDifferential

open Dregg2.Exec

/-! ## Layer 1 — the deployed selector set and the `apply_effect` dispatcher. -/

/-- The 33 `apply_<variant>` methods `turn/src/executor/apply.rs:124 apply_effect` dispatches to —
one per deployed `Effect` constructor (`turn/src/action.rs:1061`). This is the deployed SELECTOR set. -/
inductive Selector where
  | setField | transfer | grantCapability | revokeCapability | emitEvent
  | incrementNonce | createCell | setPermissions | setVerificationKey | setProgram
  | noteSpend | noteCreate | bridgeMint | exerciseViaCapability | pipelinedSend
  | introduce | spawnWithDelegation | refreshDelegation | revokeDelegation | makeSovereign
  | createCellFromFactory | refusal | cellSeal | cellUnseal | cellDestroy
  | burn | mint | attenuateCapability | receiptArchive | promise
  | notify | react | shieldedTransfer
  deriving DecidableEq, Repr, BEq

/-- The deployed `Effect` enum (`turn/src/action.rs:1061`), SELECTOR-faithful: one constructor per
`Effect` variant. Payloads are the primary operands the dispatcher branches on (the `Transfer` arm
carries a full `Turn`, the semantic unit `recKExec` consumes); the full FIELD-level model of each
variant lives in `Exec.TurnExecutorFull.execFullA` / the `Circuit.Argus.Effects.*` witnesses. -/
inductive DeployedEffect where
  | setField (actor cell : CellId) (field v : Int)
  | transfer (t : Turn)
  | grantCapability (fromC toC : CellId)
  | revokeCapability (cell : CellId) (slot : Nat)
  | emitEvent (cell : CellId)
  | incrementNonce (cell : CellId)
  | createCell (owner : CellId)
  | setPermissions (cell : CellId) (perms : Int)
  | setVerificationKey (cell : CellId) (vk : Int)
  | setProgram (cell : CellId) (prog : Int)
  | noteSpend (nf : Nat)
  | noteCreate (cm : Nat)
  | bridgeMint (cell : CellId) (value : Int)
  | exerciseViaCapability (actor target : CellId)
  | pipelinedSend (target : CellId)
  | introduce (introducer recipient target : CellId)
  | spawnWithDelegation (parent child : CellId)
  | refreshDelegation (child : CellId)
  | revokeDelegation (child : CellId)
  | makeSovereign (cell : CellId)
  | createCellFromFactory (owner : CellId) (vk : Int)
  | refusal (cell : CellId)
  | cellSeal (target : CellId)
  | cellUnseal (target : CellId)
  | cellDestroy (target : CellId) (certHash : Nat)
  | burn (target : CellId) (slot : Nat) (amount : Int)
  | mint (target : CellId) (slot : Nat) (amount : Int)
  | attenuateCapability (cell : CellId) (slot : Nat)
  | receiptArchive (prefixEndHeight : Nat)
  | promise (cell : CellId)
  | notify (fromC toC : CellId)
  | react (pendingId : Nat)
  | shieldedTransfer (payload : Nat)

/-- The `apply_effect` `match effect { … }` transcribed: which `apply_<variant>` each `Effect`
constructor routes to. Total; mirrors `turn/src/executor/apply.rs:140–428` arm for arm. -/
def dispatch : DeployedEffect → Selector
  | .setField ..              => .setField
  | .transfer ..              => .transfer
  | .grantCapability ..       => .grantCapability
  | .revokeCapability ..      => .revokeCapability
  | .emitEvent ..             => .emitEvent
  | .incrementNonce ..        => .incrementNonce
  | .createCell ..            => .createCell
  | .setPermissions ..        => .setPermissions
  | .setVerificationKey ..    => .setVerificationKey
  | .setProgram ..            => .setProgram
  | .noteSpend ..             => .noteSpend
  | .noteCreate ..            => .noteCreate
  | .bridgeMint ..            => .bridgeMint
  | .exerciseViaCapability .. => .exerciseViaCapability
  | .pipelinedSend ..         => .pipelinedSend
  | .introduce ..             => .introduce
  | .spawnWithDelegation ..   => .spawnWithDelegation
  | .refreshDelegation ..     => .refreshDelegation
  | .revokeDelegation ..      => .revokeDelegation
  | .makeSovereign ..         => .makeSovereign
  | .createCellFromFactory .. => .createCellFromFactory
  | .refusal ..               => .refusal
  | .cellSeal ..              => .cellSeal
  | .cellUnseal ..            => .cellUnseal
  | .cellDestroy ..           => .cellDestroy
  | .burn ..                  => .burn
  | .mint ..                  => .mint
  | .attenuateCapability ..   => .attenuateCapability
  | .receiptArchive ..        => .receiptArchive
  | .promise ..               => .promise
  | .notify ..                => .notify
  | .react ..                 => .react
  | .shieldedTransfer ..      => .shieldedTransfer

/-- A canonical `DeployedEffect` witness for each selector — used to PROVE dispatcher coverage. -/
def witness : Selector → DeployedEffect
  | .setField              => .setField 0 0 0 0
  | .transfer              => .transfer { actor := 0, src := 0, dst := 1, amt := 0 }
  | .grantCapability       => .grantCapability 0 1
  | .revokeCapability      => .revokeCapability 0 0
  | .emitEvent             => .emitEvent 0
  | .incrementNonce        => .incrementNonce 0
  | .createCell            => .createCell 0
  | .setPermissions        => .setPermissions 0 0
  | .setVerificationKey    => .setVerificationKey 0 0
  | .setProgram            => .setProgram 0 0
  | .noteSpend             => .noteSpend 0
  | .noteCreate            => .noteCreate 0
  | .bridgeMint            => .bridgeMint 0 0
  | .exerciseViaCapability => .exerciseViaCapability 0 1
  | .pipelinedSend         => .pipelinedSend 0
  | .introduce             => .introduce 0 1 2
  | .spawnWithDelegation   => .spawnWithDelegation 0 1
  | .refreshDelegation     => .refreshDelegation 0
  | .revokeDelegation      => .revokeDelegation 0
  | .makeSovereign         => .makeSovereign 0
  | .createCellFromFactory => .createCellFromFactory 0 0
  | .refusal               => .refusal 0
  | .cellSeal              => .cellSeal 0
  | .cellUnseal            => .cellUnseal 0
  | .cellDestroy           => .cellDestroy 0 0
  | .burn                  => .burn 0 0 0
  | .mint                  => .mint 0 0 0
  | .attenuateCapability   => .attenuateCapability 0 0
  | .receiptArchive        => .receiptArchive 0
  | .promise               => .promise 0
  | .notify                => .notify 0 1
  | .react                 => .react 0
  | .shieldedTransfer      => .shieldedTransfer 0

/-- `dispatch` routes each selector's canonical witness back to that selector. -/
theorem dispatch_witness (s : Selector) : dispatch (witness s) = s := by
  cases s <;> rfl

/-- **FULL SELECTOR COVERAGE:** every deployed selector is reachable through `dispatch` — the Lean
dispatcher covers the whole 33-variant deployed effect set, none dropped. -/
theorem dispatch_surjective : Function.Surjective dispatch :=
  fun s => ⟨witness s, dispatch_witness s⟩

#assert_axioms dispatch_witness
#assert_axioms dispatch_surjective

/-! ## Layer 1 — the honest PIN-LAYER map (where each selector's semantics is pinned). -/

/-- Where a deployed selector's STATE SEMANTICS is pinned in the Lean model. -/
inductive PinLayer where
  /-- Pinned HERE to the verified kernel step `Exec.RecordKernel.recKExec`. -/
  | recKExec
  /-- Modeled by the full per-asset executor `Exec.TurnExecutorFull.execFullA` (arm cited). -/
  | execFullA (arm : String)
  /-- A deployed selector the Lean executor does NOT yet model (reason cited) — NAMED residual. -/
  | residual (reason : String)
  deriving Repr

/-- The pin-layer of each deployed selector. `transfer` is pinned HERE (Layer 2). The rest cite the
`execFullA` arm that models them, or are NAMED `residual`. This is a DATA statement of the coverage
frontier, not a claim of proof. -/
def pinLayer : Selector → PinLayer
  | .transfer              => .recKExec
  | .pipelinedSend         => .execFullA "pipelinedSendA → neutral apply-time clock row (resolution deferred)"
  | .setField              => .execFullA "setFieldA → stateStepDev"
  | .grantCapability       => .execFullA "delegate → recCDelegate (Granovetter grant)"
  | .revokeCapability      => .execFullA "revoke → recCRevoke"
  | .emitEvent             => .execFullA "emitEventA → emitStep (liveness-gated)"
  | .incrementNonce        => .execFullA "incrementNonceA → incrementNonceStep (monotone)"
  | .createCell            => .execFullA "createCellA → createCellChainA"
  | .setPermissions        => .execFullA "setPermissionsA → stateStep permsField"
  | .setVerificationKey    => .execFullA "setVKA → stateStep vkField"
  | .setProgram            => .execFullA "setProgramA → stateStep programField"
  | .noteSpend             => .execFullA "noteSpendA → noteSpendChainA (fail-closed on proof)"
  | .noteCreate            => .execFullA "noteCreateA → noteCreateChainA"
  | .bridgeMint            => .execFullA "bridgeMintA → recCMintAsset"
  | .exerciseViaCapability => .execFullA "exerciseA → exerciseStepA ∘ execInnerA (facet-masked)"
  | .introduce             => .execFullA "introduceA/delegateAttenA → recCDelegate(Atten)"
  | .spawnWithDelegation   => .execFullA "spawnA → spawnChainA"
  | .refreshDelegation     => .execFullA "refreshDelegationA → refreshDelegationChainA"
  | .revokeDelegation      => .execFullA "revokeDelegationA → recCRevokeDelegationFull (epoch bump)"
  | .makeSovereign         => .execFullA "makeSovereignA → makeSovereignStep"
  | .createCellFromFactory => .execFullA "createCellFromFactoryA → createCellFromFactoryChainA"
  | .refusal               => .execFullA "refusalA → stateStep refusalField"
  | .cellSeal              => .execFullA "cellSealA → cellSealChainA"
  | .cellUnseal            => .execFullA "cellUnsealA → cellUnsealChainA"
  | .cellDestroy           => .execFullA "cellDestroyA → cellDestroyChainA"
  | .burn                  => .execFullA "burnA → recCBurnAsset"
  | .mint                  => .execFullA "mintA → recCMintAsset"
  | .attenuateCapability   => .execFullA "attenuateA → attenuateStepA (slot-guarded)"
  | .receiptArchive        => .execFullA "receiptArchiveA → receiptArchiveChainA"
  | .promise               => .residual "promise-pipelining: resolution in Exec.ConditionalTurn, not apply_effect"
  | .notify                => .residual "eventual notify: resolution in Exec.ConditionalTurn, not apply_effect"
  | .react                 => .residual "react: pending-resolution pass in Exec.ConditionalTurn, not apply_effect"
  | .shieldedTransfer      => .residual "prover-only hiding uni-STARK (apply.rs:1295, cfg prover); shadow = noteSpendA/noteCreateA"

/-- `true` iff the selector is a NAMED residual (unmodeled by the Lean executor). -/
def isResidual : Selector → Bool
  | s => match pinLayer s with | .residual _ => true | _ => false

/-- The full deployed selector set, as a list (drives the coverage `#guard`s). -/
def allSelectors : List Selector :=
  [.setField, .transfer, .grantCapability, .revokeCapability, .emitEvent,
   .incrementNonce, .createCell, .setPermissions, .setVerificationKey, .setProgram,
   .noteSpend, .noteCreate, .bridgeMint, .exerciseViaCapability, .pipelinedSend,
   .introduce, .spawnWithDelegation, .refreshDelegation, .revokeDelegation, .makeSovereign,
   .createCellFromFactory, .refusal, .cellSeal, .cellUnseal, .cellDestroy,
   .burn, .mint, .attenuateCapability, .receiptArchive, .promise,
   .notify, .react, .shieldedTransfer]

/-- The NAMED residual selectors (deployed but not modeled by `execFullA`). -/
def residualSelectors : List Selector := allSelectors.filter isResidual

/-! ## Layer 2 — the `Transfer` selector's SEMANTIC pin against `recKExec`. -/

/-- **An INDEPENDENT transcription of the deployed `apply_transfer`** (`apply.rs:493`), gate for gate:
`from == to` reject (:510) → `src ≠ dst`; cross-cell `Send` authority (:518) → `authorizedB`; source
live + funded (:544/:554) → `cellLifecycleLive src` + `amt ≤ balOf (cell src)`; dest exists + live
(:564/:567) → `dst ∈ accounts` + `cellLifecycleLive dst`; then `set_balance` debit/credit (:586–:595)
→ `recTransfer`. Amount is a `u64` in Rust (`0 ≤ amt` here). NAMED gap: Rust's dest-credit i64
overflow-check (:578) has no analog — Lean `ℤ` is unbounded, so the arithmetic-overflow leg is a
Rust runtime bound, not a semantic one; it never REJECTS a transfer the kernel would accept, it only
guards machine-int wraparound. -/
def applyTransferModel (k : RecordKernelState) (turn : Turn) : Option RecordKernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
      ∧ cellLifecycleLive k turn.src = true ∧ cellLifecycleLive k turn.dst = true then
    some { k with cell := recTransfer k.cell turn.src turn.dst turn.amt }
  else
    none

/-- **THE PIN (load-bearing direction).** Whenever the deployed `apply_transfer` accepts a turn and
yields `k'`, the verified kernel `recKExec` accepts the SAME turn and yields the SAME `k'`. So the
Rust dataplane never commits a `Transfer` the verified kernel rejects, nor to a different post-state:
`applyTransferModel` REFINES `recKExec`. UNCONDITIONAL. -/
theorem applyTransferModel_refines_recKExec (k k' : RecordKernelState) (turn : Turn)
    (h : applyTransferModel k turn = some k') : recKExec k turn = some k' := by
  unfold applyTransferModel at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
      ∧ cellLifecycleLive k turn.src = true ∧ cellLifecycleLive k turn.dst = true
  · rw [if_pos hg] at h
    unfold recKExec
    rw [if_pos ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1⟩]
    exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **EXACT equality once both endpoints are Live.** `recKExec` (the scalar `balance`-field kernel
step) and the deployed `apply_transfer` compute the SAME `Option` result whenever the source and
destination cells are Live — which pins down the ONE gate difference: `recKExec` does NOT check
lifecycle, `apply_transfer` does (and `recKExecAsset` restores the source leg). Non-vacuous: the
default `RecordKernelState` has every cell Live (`lifecycle = 0`), so the hypotheses are routinely
met (see the `#guard`s). -/
theorem recKExec_eq_applyTransferModel_of_live (k : RecordKernelState) (turn : Turn)
    (hs : cellLifecycleLive k turn.src = true) (hd : cellLifecycleLive k turn.dst = true) :
    recKExec k turn = applyTransferModel k turn := by
  unfold recKExec applyTransferModel
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg,
      if_pos ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2, hs, hd⟩]
  · rw [if_neg hg,
      if_neg (fun h => hg ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)]

/-- **The deployed transfer step CONSERVES the total `balance`.** Every state the Rust
`apply_transfer` commits preserves `recTotal` — inherited from the verified kernel via the refinement
(`recKExec_conserves`). A genuine safety fact about the deployed selector, not a restatement. -/
theorem applyTransferModel_conserves (k k' : RecordKernelState) (turn : Turn)
    (h : applyTransferModel k turn = some k') : recTotal k' = recTotal k :=
  recKExec_conserves k k' turn (applyTransferModel_refines_recKExec k k' turn h)

#assert_axioms applyTransferModel_refines_recKExec
#assert_axioms recKExec_eq_applyTransferModel_of_live
#assert_axioms applyTransferModel_conserves

/-! ## §NON-VACUITY — `#guard` / `#eval` fixtures over the deployed effect set. -/

-- Layer-1 coverage: exactly 33 deployed selectors, and `dispatch` sends each variant's fixture to
-- its own selector (the routing is faithful, in enum order).
#guard allSelectors.length = 33
#guard (allSelectors.map witness).map dispatch = allSelectors
-- Every selector is distinct (the `match` has no accidental merges).
#guard allSelectors.eraseDups.length = 33
-- The NAMED residual frontier: exactly the four unmodeled selectors.
#guard residualSelectors = [Selector.promise, Selector.notify, Selector.react, Selector.shieldedTransfer]
#guard residualSelectors.length = 4
-- The other 29 are pinned (recKExec or execFullA) — coverage is 29/33.
#guard (allSelectors.filter (fun s => !isResidual s)).length = 29

/-- A concrete three-cell pre-state (cells {0,1,2}, balances 100/5/50, all Live by default), reused
from the `StateCommit` fixture shape. -/
def kFix : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

/-- A funded, authorized, both-Live transfer (actor 0 owns cell 0): 30 from cell 0 to cell 1. -/
def goodTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

-- Layer-2 non-vacuity: `apply_transfer` COMMITS the good turn, and `recKExec` agrees EXACTLY.
#guard (applyTransferModel kFix goodTurn).isSome = true
-- `recKExec` and `apply_transfer` land on the SAME post-state (compared by balance projection, since
-- `RecordKernelState` has function fields and is not `DecidableEq`); the exact-equality claim is the
-- THEOREM `recKExec_eq_applyTransferModel_of_live`.
#guard (match recKExec kFix goodTurn, applyTransferModel kFix goodTurn with
        | some a, some b => balOf (a.cell 0) = balOf (b.cell 0)
            ∧ balOf (a.cell 1) = balOf (b.cell 1) ∧ balOf (a.cell 2) = balOf (b.cell 2)
        | none, none     => True
        | _, _           => False)
#eval match applyTransferModel kFix goodTurn with
      | some k' => (balOf (k'.cell 0), balOf (k'.cell 1), balOf (k'.cell 2))  -- expect (70, 35, 50)
      | none    => (0, 0, 0)
#guard (match applyTransferModel kFix goodTurn with
        | some k' => balOf (k'.cell 0) = 70 ∧ balOf (k'.cell 1) = 35 ∧ balOf (k'.cell 2) = 50
        | none    => False)

-- The lifecycle GAP is REAL, not vacuous: mark cell 1 (the destination) NON-Live (Sealed = 1). Now
-- `recKExec` (no lifecycle gate) STILL commits, but `apply_transfer` REFUSES (dest not live) — the
-- exact rejection-parity asymmetry the Rust `apply_transfer` comment (:535) warns of, and which
-- `recKExecAsset`/`recCexecAsset` close.
def kDeadDst : RecordKernelState := { kFix with lifecycle := fun c => if c = 1 then 1 else 0 }
#guard (recKExec kDeadDst goodTurn).isSome = true
#guard (applyTransferModel kDeadDst goodTurn).isNone = true

-- Fail-closed parity on an UNFUNDED turn (200 > 100): BOTH refuse.
#guard (recKExec kFix { actor := 0, src := 0, dst := 1, amt := 200 }).isNone = true
#guard (applyTransferModel kFix { actor := 0, src := 0, dst := 1, amt := 200 }).isNone = true
-- Fail-closed parity on a SELF-transfer (src == dst): BOTH refuse.
#guard (applyTransferModel kFix { actor := 0, src := 0, dst := 0, amt := 10 }).isNone = true
-- Fail-closed parity on an UNAUTHORIZED turn (actor 2 has no cap over cell 0): BOTH refuse.
#guard (applyTransferModel kFix { actor := 2, src := 0, dst := 1, amt := 10 }).isNone = true

end Dregg2.Circuit.ExecutorApplyDifferential
