/-
# Dregg2.Circuit.Inst.queueEnqueueA — the v2 (`EffectCommit2`) VALIDATION for `queueEnqueueA`.

F1b: the refundable deposit-park is GONE with the kernel escrow holding-store — `queueEnqueueA` is
the bare FIFO append again (`queueEnqueueK`): it APPENDS message `m` to queue `id`'s buffer, advances
the log by `enqueueReceipt actor cell ::`, and FREEZES the other kernel fields. So the instance
collapses from the verb-era v2-TRIPLE (`queues`+`bal`+`escrows`) to the SINGLE `queues`
`listComponent` — the same shape as `Inst/queueAllocateA.lean`.

THE VALIDATION: `queueEnqueueA_full_sound ⇒ QueueEnqueueSpec` THROUGH the framework. A satisfying v2
full-state witness for `queueEnqueueE` proves the complete declarative `QueueEnqueueSpec` (the apex
truth in `Dregg2/Circuit/Spec/queuefifocore.lean`, whose executor corner is
`execFullA_queueEnqueueA_iff_spec`).

ADDITIVE: imports `EffectCommit2` + `Spec/queuefifocore`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Inst.QueueEnqueueA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — propBit guard (wire 0, guardWidth = 1). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoQueues` portal (the rest hash binds every non-`queues` component).

Kept under the verb-era name `RestIffNoQueuesBalEscrows` as an abbreviation for downstream callers
(`EffectRefinementBatch2`); F1b: `bal` and the (deleted) `escrows` are no longer touched, so the
frame now BINDS `bal` too. -/

/-- **`RestIffNoQueues RH`** — the rest hash binds the non-`queues` components (BIDIRECTIONAL),
omitting `queues` (the touched field of the deposit-free `queueEnqueueA`). -/
def RestIffNoQueues (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)

/-- Verb-era alias (the deposit triple's portal name) — F1b: same portal, the `queues`-omitting
rest frame. Kept so `EffectRefinementBatch2`'s signatures survive the collapse. -/
abbrev RestIffNoQueuesBalEscrows (RH : RecordKernelState → ℤ) : Prop := RestIffNoQueues RH

/-! ## §2 — the `queueEnqueueE` instance (touched component = `queues`). -/

/-- The enqueue effect arguments (F1b deposit-free). -/
structure EnqueueArgs where
  id    : Nat
  m     : Nat
  actor : CellId
  cell  : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The enqueue guard as a `Prop` (the spec's `enqueueGuard` = authority ∧ liveness ∧ found ∧ not-FULL). -/
def enqueueGuardProp (s : RecChainedState) (args : EnqueueArgs) : Prop :=
  enqueueGuard s.kernel args.id args.m args.actor args.cell

instance (s : RecChainedState) (args : EnqueueArgs) : Decidable (enqueueGuardProp s args) := by
  unfold enqueueGuardProp enqueueGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def enqueueGuardEncode (s : RecChainedState) (args : EnqueueArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (enqueueGuardProp s args) else 0

def enqueueGuardGates : ConstraintSystem := [cBitGuard]

theorem enqueueGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied enqueueGuardGates a ↔ satisfied enqueueGuardGates b := by
  unfold satisfied enqueueGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- Canonical post-`queues`: the witnessed queue with `m` appended (matches the spec's per-found-`q`
clause; the `none` arm is unreachable on the committed path — the guard requires the queue found). -/
def enqueuePostQueues (s : RecChainedState) (args : EnqueueArgs) : List QueueRecord :=
  match findQueue s.kernel.queues args.id with
  | some q => replaceQueue s.kernel.queues args.id { q with buffer := qbufEnqueue q.buffer args.m }
  | none   => s.kernel.queues

/-- The `queues` list component: digest = `listDigest LE cN` over the queue side-table. -/
def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState EnqueueArgs :=
  listComponent (·.queues) LE cN hN hLE enqueuePostQueues

/-- **`queueEnqueueE`** — the `EffectSpec2` for the deposit-free `queueEnqueueA`. -/
def queueEnqueueE (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState EnqueueArgs where
  view         := chainView
  active       := queuesComponent LE cN hN hLE
  logUpdate    := some (fun s args => enqueueReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := enqueueGuardGates
  guardProp    := enqueueGuardProp
  guardWidth   := 1
  guardEncode  := enqueueGuardEncode
  guardLocal   := enqueueGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `queueEnqueueE`. -/

theorem enqueueGuardDecodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (queueEnqueueE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied enqueueGuardGates (enqueueGuardEncode s args s') at hsat
  show enqueueGuardProp s args
  have hg := hsat cBitGuard (by simp [enqueueGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, enqueueGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem enqueueGuardEncodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (queueEnqueueE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied enqueueGuardGates (enqueueGuardEncode s args s')
  intro c hc
  simp only [enqueueGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, enqueueGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem enqueueRestFrameDecodes (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoQueues S.RH) :
    RestFrameDecodes2 S (queueEnqueueE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `QueueEnqueueSpec` bridge. -/

/-- **`apex_iff_queueEnqueueSpec`** — the framework's derived `apex` for `queueEnqueueE` is EXACTLY
`QueueEnqueueSpec`: the guard coincides; the component `postClause` (the canonical
`enqueuePostQueues`) matches the spec's per-found-`q` clause via the guard's found-queue witness; the
log and the frame line up one-to-one. -/
theorem apex_iff_queueEnqueueSpec (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) :
    (queueEnqueueE LE cN hN hLE).apex s args s'
      ↔ QueueEnqueueSpec s args.id args.m args.actor args.cell s' := by
  show (enqueueGuardProp s args
        ∧ s'.kernel.queues = enqueuePostQueues s args
        ∧ s'.log = enqueueReceipt args.actor args.cell :: s.log
        ∧ ((queueEnqueueE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ QueueEnqueueSpec s args.id args.m args.actor args.cell s'
  unfold QueueEnqueueSpec enqueueGuardProp queueEnqueueE
  constructor
  · rintro ⟨hg, hq, hlog, hframe⟩
    obtain ⟨hauth, hacc, q, hfq, hcap⟩ := hg
    refine ⟨⟨hauth, hacc, q, hfq, hcap⟩, ?_, hlog, hframe⟩
    intro q' hq'
    rw [hfq] at hq'
    simp only [Option.some.injEq] at hq'
    subst hq'
    rw [hq]
    unfold enqueuePostQueues
    rw [hfq]
  · rintro ⟨hg, hq, hlog, hframe⟩
    obtain ⟨hauth, hacc, q, hfq, hcap⟩ := hg
    refine ⟨⟨hauth, hacc, q, hfq, hcap⟩, ?_, hlog, hframe⟩
    rw [hq q hfq]
    unfold enqueuePostQueues
    rw [hfq]

/-! ### §2c — THE VALIDATION: `queueEnqueueA_full_sound ⇒ QueueEnqueueSpec` through the framework. -/

/-- **`queueEnqueueA_full_sound` — the VALIDATION (queue-enqueue through the v2 framework).** A
satisfying v2 full-state witness for `queueEnqueueE` proves the complete declarative bespoke
`QueueEnqueueSpec`. Portals: `RestIffNoQueues RH`, `logHashInjective LH`, `compressNInjective cN` +
`listLeafInjective LE` (the `queues` list-component carriers). The circuit⟺spec corner of the
queue-enqueue triangle (whose executor corner is `execFullA_queueEnqueueA_iff_spec`). -/
theorem queueEnqueueA_full_sound
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueEnqueueE LE cN hN hLE)
          (encodeE2 S (queueEnqueueE LE cN hN hLE) s args s')) :
    QueueEnqueueSpec s args.id args.m args.actor args.cell s' := by
  have hapex : (queueEnqueueE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (queueEnqueueE LE cN hN hLE)
      (enqueueRestFrameDecodes S LE cN hN hLE hRest) hLog (enqueueGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_queueEnqueueSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueEnqueueEWire : EffectSpec2 RecChainedState EnqueueArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := enqueueGuardGates
  guardProp    := enqueueGuardProp
  guardWidth   := 1
  guardEncode  := enqueueGuardEncode
  guardLocal   := enqueueGuardLocal
  guardWidth_le := by decide

def queueEnqueueAAirName : String := "dregg-queueEnqueueA-v2"

def queueEnqueueAEmitted : EmittedDescriptor := emittedEffect2 queueEnqueueAAirName queueEnqueueEWire

#guard queueEnqueueAEmitted.name == queueEnqueueAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms enqueueGuardLocal
#assert_axioms enqueueGuardDecodes
#assert_axioms enqueueGuardEncodes
#assert_axioms apex_iff_queueEnqueueSpec
#assert_axioms queueEnqueueA_full_sound

end Dregg2.Circuit.Inst.QueueEnqueueA
