/-
# Dregg2.Circuit.Inst.queueDequeueA — the v2 (`EffectCommit2`) VALIDATION for `queueDequeueA`.

F1b: the deposit refund is GONE with the kernel escrow holding-store — `queueDequeueA` is the bare
owner-gated FIFO pop again (`queueDequeueK`): it REMOVES the FRONT of queue `id`'s buffer, advances
the log by `dequeueReceipt actor cell ::`, and FREEZES the other kernel fields. So the instance
collapses from the verb-era v2-TRIPLE (`queues`+`bal`+`escrows`) to the SINGLE `queues`
`listComponent` — the same shape as `Inst/queueAllocateA.lean`.

THE VALIDATION: `queueDequeueA_full_sound ⇒ QueueDequeueSpec` THROUGH the framework (the apex truth in
`Dregg2/Circuit/Spec/queuefifocore.lean`, whose executor corner is `execFullA_queueDequeueA_iff_spec`).

ADDITIVE: imports `EffectCommit2` + `Spec/queuefifocore`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Inst.QueueDequeueA

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

/-! ## §1 — the `RestIffNoQueues` portal (the rest hash binds every non-`queues` component). -/

/-- **`RestIffNoQueues RH`** — the rest hash binds the non-`queues` components (BIDIRECTIONAL),
omitting `queues` (the touched field of the deposit-free `queueDequeueA`). -/
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

/-! ## §2 — the `queueDequeueE` instance (touched component = `queues`). -/

/-- The dequeue effect arguments (F1b deposit-free). -/
structure DequeueArgs where
  id    : Nat
  actor : CellId
  cell  : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The dequeue guard as a `Prop` (the spec's `dequeueGuard` = authority ∧ liveness ∧ found ∧
owner-only ∧ non-EMPTY). -/
def dequeueGuardProp (s : RecChainedState) (args : DequeueArgs) : Prop :=
  dequeueGuard s.kernel args.id args.actor args.cell

instance (s : RecChainedState) (args : DequeueArgs) : Decidable (dequeueGuardProp s args) := by
  unfold dequeueGuardProp dequeueGuard
  refine @instDecidableAnd _ _ _ ?_
  refine @instDecidableAnd _ _ _ ?_
  cases hf : findQueue s.kernel.queues args.id with
  | none =>
      exact isFalse (by
        rintro ⟨q, m, rest, hq, _, _⟩
        simp at hq)
  | some q =>
      cases hd : qbufDequeue q.buffer with
      | none =>
          exact isFalse (by
            rintro ⟨q', m, rest, hq', _, hd'⟩
            obtain rfl := (Option.some.inj hq').symm
            rw [hd] at hd'; simp at hd')
      | some pr =>
          by_cases ho : args.actor = q.owner
          · exact isTrue ⟨q, pr.1, pr.2, rfl, ho, hd⟩
          · exact isFalse (by
              rintro ⟨q', m, rest, hq', ho', _⟩
              obtain rfl := (Option.some.inj hq').symm
              exact ho ho')

def dequeueGuardEncode (s : RecChainedState) (args : DequeueArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (dequeueGuardProp s args) else 0

def dequeueGuardGates : ConstraintSystem := [cBitGuard]

theorem dequeueGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied dequeueGuardGates a ↔ satisfied dequeueGuardGates b := by
  unfold satisfied dequeueGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- Canonical post-`queues`: the witnessed queue with its FIFO head popped (matches the spec's
per-found-`q` clause; the `none` arms are unreachable on the committed path). -/
def dequeuePostQueues (s : RecChainedState) (args : DequeueArgs) : List QueueRecord :=
  match findQueue s.kernel.queues args.id with
  | some q =>
      match qbufDequeue q.buffer with
      | some (_, rest) => replaceQueue s.kernel.queues args.id { q with buffer := rest }
      | none           => s.kernel.queues
  | none   => s.kernel.queues

/-- The `queues` list component: digest = `listDigest LE cN` over the queue side-table. -/
def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState DequeueArgs :=
  listComponent (·.queues) LE cN hN hLE dequeuePostQueues

/-- **`queueDequeueE`** — the `EffectSpec2` for the deposit-free `queueDequeueA`. -/
def queueDequeueE (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState DequeueArgs where
  view         := chainView
  active       := queuesComponent LE cN hN hLE
  logUpdate    := some (fun s args => dequeueReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := dequeueGuardGates
  guardProp    := dequeueGuardProp
  guardWidth   := 1
  guardEncode  := dequeueGuardEncode
  guardLocal   := dequeueGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `queueDequeueE`. -/

theorem dequeueGuardDecodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (queueDequeueE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied dequeueGuardGates (dequeueGuardEncode s args s') at hsat
  show dequeueGuardProp s args
  have hg := hsat cBitGuard (by simp [dequeueGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dequeueGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem dequeueGuardEncodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (queueDequeueE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied dequeueGuardGates (dequeueGuardEncode s args s')
  intro c hc
  simp only [dequeueGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, dequeueGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem dequeueRestFrameDecodes (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoQueues S.RH) :
    RestFrameDecodes2 S (queueDequeueE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `QueueDequeueSpec` bridge. -/

/-- **`apex_iff_queueDequeueSpec`** — the framework's derived `apex` for `queueDequeueE` is EXACTLY
`QueueDequeueSpec`: the guard coincides; the component `postClause` (the canonical
`dequeuePostQueues`) matches the spec's per-found-`q`-`m`-`rest` clause via the guard's witnesses;
the log and the frame line up one-to-one. -/
theorem apex_iff_queueDequeueSpec (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState) :
    (queueDequeueE LE cN hN hLE).apex s args s'
      ↔ QueueDequeueSpec s args.id args.actor args.cell s' := by
  show (dequeueGuardProp s args
        ∧ s'.kernel.queues = dequeuePostQueues s args
        ∧ s'.log = dequeueReceipt args.actor args.cell :: s.log
        ∧ ((queueDequeueE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ QueueDequeueSpec s args.id args.actor args.cell s'
  unfold QueueDequeueSpec dequeueGuardProp queueDequeueE
  constructor
  · rintro ⟨hg, hq, hlog, hframe⟩
    obtain ⟨hauth, hacc, q, m0, rest0, hfq, ho, hd⟩ := hg
    refine ⟨⟨hauth, hacc, q, m0, rest0, hfq, ho, hd⟩, ?_, hlog, hframe⟩
    intro q' m' rest' hq' hd'
    rw [hfq] at hq'
    simp only [Option.some.injEq] at hq'
    subst hq'
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    rw [hq]
    simp only [dequeuePostQueues, hfq, hd]
    rw [hd'.2]
  · rintro ⟨hg, hq, hlog, hframe⟩
    obtain ⟨hauth, hacc, q, m0, rest0, hfq, ho, hd⟩ := hg
    refine ⟨⟨hauth, hacc, q, m0, rest0, hfq, ho, hd⟩, ?_, hlog, hframe⟩
    rw [hq q m0 rest0 hfq hd]
    simp only [dequeuePostQueues, hfq, hd]

/-! ### §2c — THE VALIDATION: `queueDequeueA_full_sound ⇒ QueueDequeueSpec` through the framework. -/

/-- **`queueDequeueA_full_sound` — the VALIDATION (queue-dequeue through the v2 framework).** A
satisfying v2 full-state witness for `queueDequeueE` proves the complete declarative bespoke
`QueueDequeueSpec`. Portals: `RestIffNoQueues RH`, `logHashInjective LH`, `compressNInjective cN` +
`listLeafInjective LE` (the `queues` list-component carriers). The circuit⟺spec corner of the
queue-dequeue triangle (whose executor corner is `execFullA_queueDequeueA_iff_spec`). -/
theorem queueDequeueA_full_sound
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DequeueArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueDequeueE LE cN hN hLE)
          (encodeE2 S (queueDequeueE LE cN hN hLE) s args s')) :
    QueueDequeueSpec s args.id args.actor args.cell s' := by
  have hapex : (queueDequeueE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (queueDequeueE LE cN hN hLE)
      (dequeueRestFrameDecodes S LE cN hN hLE hRest) hLog (dequeueGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_queueDequeueSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queueDequeueEWire : EffectSpec2 RecChainedState DequeueArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := dequeueGuardGates
  guardProp    := dequeueGuardProp
  guardWidth   := 1
  guardEncode  := dequeueGuardEncode
  guardLocal   := dequeueGuardLocal
  guardWidth_le := by decide

def queueDequeueAAirName : String := "dregg-queueDequeueA-v2"

def queueDequeueAEmitted : EmittedDescriptor := emittedEffect2 queueDequeueAAirName queueDequeueEWire

#guard queueDequeueAEmitted.name == queueDequeueAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms dequeueGuardLocal
#assert_axioms dequeueGuardDecodes
#assert_axioms dequeueGuardEncodes
#assert_axioms apex_iff_queueDequeueSpec
#assert_axioms queueDequeueA_full_sound

end Dregg2.Circuit.Inst.QueueDequeueA
