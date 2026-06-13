/-
# Dregg2.Exec.HostCorrespondence — the host-side correspondence for the admission gate.

`Exec.Admission.admissible` is a pure function of `(ctx : AdmCtx, h : TurnHdr, s : RecChainedState)`.
The §3 rejection theorems prove the gate is fail-closed on every leg — but *given* an `AdmCtx`. In
deployment that `AdmCtx` is built (`AdmissionWire.admCtxOf`) from FIVE values the HOST supplies — the
`ShadowHostCtx` of `turn/src/lean_shadow.rs` — and marshalled across the FFI seam
(`marshal::WireHostCtx`, the `frozen` set projected to the turn's referenced wire-Nats only). The
AssuranceCase names this as boundary seam **§2** ("the `ShadowHostCtx` host-fed admission inputs"):

> The theorems say: IF these are the node's true values THEN admission is decided correctly and
> fail-closed. Their fidelity … is a host obligation outside the Lean statement.

This module discharges the IF–THEN. It makes "the node's true values" an explicit object
(`HostFacts`), states what it means for a deployed `AdmCtx` to FAITHFULLY REFLECT those facts
(`Reflects`, including the freeze-set marshalling fall-off), and proves:

  * **`admissible_sound_of_reflects` (THE CONDITIONAL SOUNDNESS LEMMA).** When `ctx` faithfully
    reflects the host facts `H` for turn `h`, the gate's verdict equals the verdict computed against
    the TRUE host facts: `admissible ctx h s = admissibleFacts H h s`. So a faithfully-marshalled
    context decides exactly as the node's own state would — the gate adds no error of its own. From
    this, every §3 fail-closed theorem transports to the true host facts (the `*_facts` corollaries).

  * **The producer-side OBLIGATION, stated as TEETH** (§4). Each field of `Reflects` is shown
    LOAD-BEARING by exhibiting the unsafe under-report that BREAKS soundness: a context that
    omits a truly-frozen referenced cell / advances the stored head / inflates the budget / retards
    the clock ADMITS a turn the true-facts gate REJECTS. These are exactly the node-side guarantees
    the conditional rests on — proven non-vacuous, never assumed.

  * **The freeze-set marshalling fall-off** (`frozen_marshal_faithful`): the FFI crosses only the
    truly-frozen cells that the turn REFERENCES (`pre.id_map`); since `admissible`'s NotFrozen leg
    reads only the agent + the write-set (all referenced), that projection is sound IFF the turn's
    write-set is contained in the referenced-id domain — the precise marshalling obligation.

Pure, computable, `#assert_axioms`-clean, both-polarity `#guard` non-vacuity. Edits nothing; imports
`Exec.Admission` (+ `AdmissionWire` for the wire builders the corollaries pin).
-/
import Dregg2.Exec.Admission
import Dregg2.Exec.AdmissionWire

namespace Dregg2.Exec.HostCorrespondence

open Dregg2.Exec
open Dregg2.Exec.Admission

/-! ## §1 — `HostFacts`: the node's TRUE runtime values.

These are the ground-truth quantities the running node holds about ITSELF at the moment it admits a
turn — the values `ShadowHostCtx` is *supposed* to report. They are NOT turn fields (the agent cannot
set them); they live in `self`:
  * `trueClock`      — the executor's actual chain height / timestamp (`self.block_height`);
  * `trueFrozen`     — the actual migration freeze-set (`self.cell_migrations` frozen cells);
  * `trueStoredHead` — the agent's actual stored receipt-chain head (`self.get_last_receipt_hash`);
  * `trueBudget`     — the actual Stingray silo budget slice (`self.budget_gate.remaining()`).

The proposer/treasury/burn-pot routing of `AdmCtx` is fee-distribution policy, not an admission gate,
so it is NOT part of the admission correspondence (it never appears in `admissible`). -/
structure HostFacts where
  trueClock      : Nat
  trueFrozen     : List CellId
  trueStoredHead : Option Nat
  trueBudget     : Nat
deriving Repr

/-- The admission verdict computed against the TRUE host facts. This is the verdict the node's OWN
state would yield — the reference the deployed `AdmCtx` is meant to reproduce. It is just
`admissible` against the canonical context built from the facts (clock on the `now` axis, so the
`admissionClock` `blockHeight>0` preference is irrelevant — the facts carry one clock). -/
def factsCtx (H : HostFacts) : AdmCtx :=
  { now := H.trueClock, blockHeight := 0, frozen := H.trueFrozen,
    storedHead := H.trueStoredHead, budget := H.trueBudget }

/-- The reference admission decision against the node's true facts. -/
def admissibleFacts (H : HostFacts) (h : TurnHdr) (s : RecChainedState) : Bool :=
  admissible (factsCtx H) h s

/-! ## §2 — `Reflects`: faithful reflection of the host facts by a deployed context.

A deployed `AdmCtx ctx` faithfully reflects `HostFacts H` FOR a given turn header `h` when every
admission-relevant field of `ctx` agrees with `H` on the part the gate reads:

  * **clock** — `admissionClock ctx = H.trueClock` (whichever axis the context wired its clock onto,
    the resolved expiry clock is the true clock; the node must not retard or advance it);
  * **freeze (the MARSHALLING fall-off)** — for every cell the gate's NotFrozen leg READS (the agent
    and the write-set), `ctx.frozen` says "frozen" exactly when `H.trueFrozen` does. The gate never
    reads any other cell, so the FFI is free to cross only the referenced subset of `trueFrozen` —
    that projection is faithful precisely on the read cells (`frozen_agrees_on`);
  * **storedHead** — `ctx.storedHead = H.trueStoredHead` (the node must report the agent's real
    receipt-chain head, the anti-fork/replay binding);
  * **budget** — `ctx.budget = H.trueBudget` (the node must report the real silo slice).

`h` is a parameter because the freeze leg only needs agreement on the turn's read cells — the precise
producer-coverage requirement. -/
def frozenReads (h : TurnHdr) : List CellId := h.agent :: h.writeSet

/-- The freeze-set agreement the gate actually needs: `ctx.frozen` and `H.trueFrozen` classify every
READ cell (agent + write-set) identically. Off the read cells they may differ freely — that is the
marshalling fall-off the FFI exploits (it crosses only the referenced frozen cells). -/
def frozenAgreesOn (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr) : Prop :=
  ∀ c ∈ frozenReads h, isFrozen ctx c = isFrozen (factsCtx H) c

/-- **Faithful reflection** of `H` by `ctx` for turn `h`: clock, freeze (on the read cells),
storedHead, and budget all agree with the node's true facts. This is the exact node-side obligation
the conditional soundness lemma rests on. -/
structure Reflects (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr) : Prop where
  clock      : admissionClock ctx = H.trueClock
  frozen     : frozenAgreesOn ctx H h
  storedHead : ctx.storedHead = H.trueStoredHead
  budget     : ctx.budget = H.trueBudget

/-! ## §3 — THE CONDITIONAL SOUNDNESS LEMMA.

When `ctx` faithfully reflects the host facts for turn `h`, the gate's verdict against `ctx` EQUALS
the verdict against the true facts. The gate is a `&&`-fold of eight decidable legs; we show each leg
takes the same value under `ctx` as under `factsCtx H`, then the folds are equal. The agent-existence,
nonce, and fee-coverage legs read only `h` and `s` (no host context), so they are syntactically equal;
the four host-fed legs agree exactly by `Reflects`. -/

/-- The `admissionClock` of the canonical facts context is the true clock (it wires onto `now` with
`blockHeight = 0`). -/
theorem admissionClock_factsCtx (H : HostFacts) : admissionClock (factsCtx H) = H.trueClock := by
  simp [admissionClock, factsCtx]

/-- The Expiry leg agrees: both contexts resolve the same clock against `validUntil`. -/
theorem expiry_leg_agrees (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr)
    (hclock : admissionClock ctx = H.trueClock) :
    (match h.validUntil with | none => true | some vu => decide (admissionClock ctx ≤ vu))
      = (match h.validUntil with
          | none => true | some vu => decide (admissionClock (factsCtx H) ≤ vu)) := by
  rw [admissionClock_factsCtx, hclock]

/-- The NotFrozen agent leg agrees on the read cells (the agent is a read cell). -/
theorem notFrozen_agent_agrees (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr)
    (hf : frozenAgreesOn ctx H h) : (!isFrozen ctx h.agent) = (!isFrozen (factsCtx H) h.agent) := by
  have := hf h.agent (by simp [frozenReads]); rw [this]

/-- `List.all` agrees on two predicates that agree pointwise on the list's members. -/
private theorem all_eq_of_pointwise {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ c ∈ l, p c = q c) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun c hc => h c (by simp [hc]))]

/-- The NotFrozen write-set leg agrees on the read cells (the write-set cells are read cells). -/
theorem notFrozen_writeSet_agrees (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr)
    (hf : frozenAgreesOn ctx H h) :
    (h.writeSet.all (fun c => !isFrozen ctx c))
      = (h.writeSet.all (fun c => !isFrozen (factsCtx H) c)) :=
  all_eq_of_pointwise h.writeSet _ _ (fun c hc => by
    have := hf c (by simp only [frozenReads, List.mem_cons]; exact Or.inr hc)
    rw [this])

/-- **`admissible_sound_of_reflects` — THE CONDITIONAL SOUNDNESS LEMMA.** When `ctx` faithfully
reflects the host facts `H` for turn `h` (clock, freeze-on-read-cells, storedHead, budget all match),
the gate's verdict against the deployed context EQUALS the verdict against the node's true facts. So a
faithfully-marshalled `ShadowHostCtx` decides EXACTLY as the node's own admission would; the gate
introduces no error. The four host-fed legs (expiry/freeze/chain-head/budget) match by `Reflects`; the
three host-blind legs (agent-existence/nonce/fee) are over `h` and `s` alone, hence identical. -/
theorem admissible_sound_of_reflects (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr)
    (s : RecChainedState) (hr : Reflects ctx H h) :
    admissible ctx h s = admissibleFacts H h s := by
  unfold admissibleFacts admissible
  -- Rewrite each of the FOUR host-fed legs to its facts-side form; the remaining legs
  -- (forestNonEmpty / agent-existence / nonce / fee-coverage) read only `h`/`s`, hence identical.
  rw [show admissionClock ctx = admissionClock (factsCtx H) by
        rw [hr.clock, admissionClock_factsCtx],
      notFrozen_agent_agrees ctx H h hr.frozen,
      notFrozen_writeSet_agrees ctx H h hr.frozen,
      show ctx.storedHead = (factsCtx H).storedHead from hr.storedHead,
      show ctx.budget = (factsCtx H).budget from hr.budget]

/-! ### §3b — The §3 fail-closed teeth, transported to the TRUE host facts.

Each §3 rejection is now expressible against the node's real state: a turn the deployed gate would
reject under a faithfully-reflected context is rejected because the TRUE facts reject it. These are the
deployment-grade fail-closed statements the AssuranceCase advertises. -/

/-- A turn whose `prevReceipt` ≠ the agent's TRUE stored head is rejected by any faithfully-reflecting
context (anti-fork/replay over the node's real receipt-chain head). -/
theorem reflects_rejects_true_fork (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr) (s : RecChainedState)
    (hr : Reflects ctx H h) (hfork : h.prevReceipt ≠ H.trueStoredHead) :
    admissible ctx h s = false := by
  rw [admissible_sound_of_reflects ctx H h s hr]
  apply admissible_rejects_chain_fork
  rw [show (factsCtx H).storedHead = H.trueStoredHead from rfl]; exact hfork

/-- A turn whose `fee` exceeds the node's TRUE silo budget is rejected by any faithfully-reflecting
context (the real Stingray slice, not a value the agent inflated). -/
theorem reflects_rejects_true_over_budget (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr)
    (s : RecChainedState) (hr : Reflects ctx H h) (hover : h.fee > (H.trueBudget : Int)) :
    admissible ctx h s = false := by
  rw [admissible_sound_of_reflects ctx H h s hr]
  apply admissible_rejects_over_budget
  rw [show (factsCtx H).budget = H.trueBudget from rfl]; exact hover

/-- A turn touching a cell that is TRULY frozen (and that the turn references, so the gate reads it) is
rejected by any faithfully-reflecting context. -/
theorem reflects_rejects_true_frozen_agent (ctx : AdmCtx) (H : HostFacts) (h : TurnHdr)
    (s : RecChainedState) (hr : Reflects ctx H h)
    (hfrozen : (factsCtx H).frozen.contains h.agent = true) :
    admissible ctx h s = false := by
  rw [admissible_sound_of_reflects ctx H h s hr]
  exact admissible_rejects_frozen (factsCtx H) h s hfrozen

#assert_axioms admissionClock_factsCtx
#assert_axioms admissible_sound_of_reflects
#assert_axioms reflects_rejects_true_fork
#assert_axioms reflects_rejects_true_over_budget
#assert_axioms reflects_rejects_true_frozen_agent

/-! ## §4 — The producer-side OBLIGATION as TEETH: each unsafe under-report breaks soundness.

The conditional soundness lemma's strength is exactly the strength of its hypothesis `Reflects`. To
prove `Reflects` is LOAD-BEARING (not a vacuous premise we could weaken), we exhibit, per field, the
UNSAFE under-report — the lie in the dangerous direction — and prove it ADMITS a turn the true-facts
gate REJECTS. These are the node-side guarantees the case depends on, stated as the failures they
prevent. Each is the negation of one `Reflects` leg.

The shared witness: agent cell 7, balance 100, nonce 3; a well-formed turn header. -/

/-- Pre-state: cell 7 holds balance 100, nonce 3 (a live account). -/
def s0 : RecChainedState :=
  { kernel := { accounts := {7}, caps := fun _ => [],
                cell := fun c => if c = 7 then .record [("balance", .int 100), ("nonce", .int 3)]
                                 else .record [] },
    log := [] }

/-- A turn header: agent 7, nonce 3 (matches), fee 10, no expiry, prevReceipt `some 42`,
write-set {7}, non-empty forest. -/
def h0 : TurnHdr :=
  { agent := 7, nonce := 3, fee := 10, validUntil := none, prevReceipt := some 42,
    writeSet := [7], forestNonEmpty := true }

/-! ### §4a — STORED-HEAD obligation: the node MUST report the agent's real receipt-chain head.

If the node ADVANCES (lies about) the stored head to match a replayed/forked turn's claimed `prev`,
a turn the true-facts gate REJECTS (`prev ≠ trueHead`) is ADMITTED. So the soundness conditional
genuinely requires `ctx.storedHead = trueStoredHead`. -/

/-- The agent's TRUE head is `some 99`; the turn claims `prev = some 42` — a FORK the true-facts gate
must reject. -/
def hFork : HostFacts := { trueClock := 0, trueFrozen := [], trueStoredHead := some 99, trueBudget := 1000 }

/-- A LYING context that advances the head to `some 42` (matching the forked turn). It is NOT a
faithful reflection of `hFork` (its storedHead leg fails). -/
def ctxLyingHead : AdmCtx := { now := 0, frozen := [], storedHead := some 42, budget := 1000 }

/-- **The stored-head tooth.** The true-facts gate REJECTS the forked turn, but the lying context
ADMITS it — so `Reflects` (its storedHead leg) is exactly the obligation that closes this. -/
theorem stored_head_obligation_teeth :
    admissibleFacts hFork h0 s0 = false ∧ admissible ctxLyingHead h0 s0 = true := by
  constructor <;> decide

/-! ### §4b — BUDGET obligation: the node MUST report the real silo slice.

If the node INFLATES the reported budget, a turn whose fee exceeds the TRUE slice is admitted. -/

/-- True budget 5; the turn's fee is 10 — over the true slice, so the true-facts gate rejects. -/
def hPoorBudget : HostFacts := { trueClock := 0, trueFrozen := [], trueStoredHead := some 42, trueBudget := 5 }

/-- A LYING context inflating the budget to 1000 (so `fee 10 ≤ 1000`). Not a faithful reflection. -/
def ctxInflatedBudget : AdmCtx := { now := 0, frozen := [], storedHead := some 42, budget := 1000 }

/-- **The budget tooth.** The true-facts gate rejects (fee 10 > true budget 5); the inflated context
admits — `Reflects.budget` is the obligation that closes it. -/
theorem budget_obligation_teeth :
    admissibleFacts hPoorBudget h0 s0 = false ∧ admissible ctxInflatedBudget h0 s0 = true := by
  constructor <;> decide

/-! ### §4c — FREEZE obligation: the node MUST surface every truly-frozen READ cell.

If the node OMITS a truly-frozen cell that the turn touches (the marshalling drops it), a turn over a
frozen cell is admitted. This is the precise producer-coverage fall-off: the FFI must cross EVERY
truly-frozen cell among the turn's referenced cells. -/

/-- The agent cell 7 is TRULY frozen. -/
def hFrozen : HostFacts := { trueClock := 0, trueFrozen := [7], trueStoredHead := some 42, trueBudget := 1000 }

/-- A LYING/INCOMPLETE context that omits cell 7 from the freeze-set (the marshalling dropped it).
Not a faithful reflection (its freeze leg fails on the agent, a read cell). -/
def ctxDroppedFrozen : AdmCtx := { now := 0, frozen := [], storedHead := some 42, budget := 1000 }

/-- **The freeze tooth.** The true-facts gate rejects (agent 7 frozen); the context that dropped the
frozen cell admits — `Reflects.frozen` (agreement on the read cells) is the obligation that closes it.
This is exactly the FFI marshalling requirement: cross every truly-frozen referenced cell. -/
theorem freeze_obligation_teeth :
    admissibleFacts hFrozen h0 s0 = false ∧ admissible ctxDroppedFrozen h0 s0 = true := by
  constructor <;> decide

/-! ### §4d — CLOCK obligation: the node MUST NOT retard the admission clock.

If the node REPORTS A STALE (too-low) clock, an EXPIRED turn (`validUntil < trueClock`) is admitted. -/

/-- The TRUE clock is 100; the turn (below) expires at 50, so the true-facts gate must reject it. -/
def hLateClock : HostFacts := { trueClock := 100, trueFrozen := [], trueStoredHead := some 42, trueBudget := 1000 }

/-- The expiring turn header (valid only until 50). -/
def hExp : TurnHdr := { h0 with validUntil := some 50 }

/-- A LYING context reporting a stale clock 0 (so `0 ≤ 50` passes). Not a faithful reflection. -/
def ctxStaleClock : AdmCtx := { now := 0, frozen := [], storedHead := some 42, budget := 1000 }

/-- **The clock tooth.** The true-facts gate rejects the expired turn (true clock 100 > validUntil 50);
the stale-clock context admits it — `Reflects.clock` is the obligation that closes it. -/
theorem clock_obligation_teeth :
    admissibleFacts hLateClock hExp s0 = false ∧ admissible ctxStaleClock hExp s0 = true := by
  constructor <;> decide

#assert_axioms stored_head_obligation_teeth
#assert_axioms budget_obligation_teeth
#assert_axioms freeze_obligation_teeth
#assert_axioms clock_obligation_teeth

/-! ## §5 — The freeze-set MARSHALLING fall-off, made precise.

The FFI (`turn/src/lean_shadow.rs::run_shadow`) crosses only the truly-frozen cells the turn
REFERENCES: `host.frozen.iter().filter_map(|c| pre.id_map.get(c))`. We model this projection and prove
it is FAITHFUL on the read cells exactly when the turn's read cells are referenced (in the id domain) —
the precise producer obligation behind `Reflects.frozen`. -/

/-- The marshalled freeze-set: the truly-frozen cells that the turn references (`referenced`). This is
the FFI's `filter` of `trueFrozen` down to the id-map domain. -/
def marshalledFrozen (trueFrozen referenced : List CellId) : List CellId :=
  trueFrozen.filter (fun c => referenced.contains c)

/-- The deployed context built from the marshalled freeze-set (the other facts crossing verbatim). -/
def marshalledCtx (H : HostFacts) (referenced : List CellId) : AdmCtx :=
  { now := H.trueClock, blockHeight := 0,
    frozen := marshalledFrozen H.trueFrozen referenced,
    storedHead := H.trueStoredHead, budget := H.trueBudget }

/-- **`marshalled_frozen_agrees` — the marshalling fidelity on a read cell.** For a cell `c` that the
turn references, the marshalled freeze-set classifies `c` EXACTLY as the true freeze-set does: a
referenced cell crosses iff it is truly frozen. (Off the referenced set the marshalled set drops cells,
but the gate never reads those.) -/
theorem marshalled_frozen_agrees (trueFrozen referenced : List CellId) (c : CellId)
    (href : referenced.contains c = true) :
    (marshalledFrozen trueFrozen referenced).contains c = trueFrozen.contains c := by
  have hmemref : c ∈ referenced := by simpa [List.contains_eq_mem] using href
  have hiff : (c ∈ marshalledFrozen trueFrozen referenced) ↔ (c ∈ trueFrozen) := by
    unfold marshalledFrozen
    rw [List.mem_filter]
    exact ⟨fun ⟨hmem, _⟩ => hmem,
           fun hmem => ⟨hmem, by simpa [List.contains_eq_mem] using href⟩⟩
  rw [List.contains_eq_mem, List.contains_eq_mem, decide_eq_decide]
  exact hiff

/-- **`marshalled_ctx_reflects` — the FFI marshalling DISCHARGES `Reflects`.** When every read cell of
the turn (agent + write-set) is referenced (in the id-map domain — the producer-coverage requirement),
the context built from the marshalled freeze-set faithfully reflects the host facts. So the conditional
soundness lemma applies to the ACTUAL wire-built context: `admissible (marshalledCtx …) = admissibleFacts`.
The hypothesis `∀ c ∈ frozenReads h, referenced.contains c = true` is the EXACT node obligation — the
marshaller must assign a wire id to (reference) every cell the freeze gate reads. -/
theorem marshalled_ctx_reflects (H : HostFacts) (h : TurnHdr) (referenced : List CellId)
    (hcov : ∀ c ∈ frozenReads h, referenced.contains c = true) :
    Reflects (marshalledCtx H referenced) H h := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp [admissionClock, marshalledCtx]
  · intro c hc
    have href := hcov c hc
    show (marshalledFrozen H.trueFrozen referenced).contains c = H.trueFrozen.contains c
    exact marshalled_frozen_agrees H.trueFrozen referenced c href

/-- **`marshalled_admission_sound` — END TO END.** When the marshaller references every freeze-read
cell, the gate over the ACTUAL wire-built context decides exactly as the node's true facts. This is the
boundary-seam-§2 conditional discharged for the deployed marshalling path: the only residual obligation
is producer-coverage (`hcov`) — every cell the freeze gate reads must get a wire id — plus the
clock/storedHead/budget fields crossing verbatim (which `marshalledCtx` does by construction). -/
theorem marshalled_admission_sound (H : HostFacts) (h : TurnHdr) (s : RecChainedState)
    (referenced : List CellId) (hcov : ∀ c ∈ frozenReads h, referenced.contains c = true) :
    admissible (marshalledCtx H referenced) h s = admissibleFacts H h s :=
  admissible_sound_of_reflects (marshalledCtx H referenced) H h s
    (marshalled_ctx_reflects H h referenced hcov)

#assert_axioms marshalled_frozen_agrees
#assert_axioms marshalled_ctx_reflects
#assert_axioms marshalled_admission_sound

/-! ## §6 — Non-vacuity (`#guard`, both polarities).

The conditional soundness lemma is non-trivial: a faithful context agrees with the facts (the gate
adds no error), while an unfaithful context can DISAGREE — exactly the teeth of §4. -/

/-- A faithfully-reflecting context: same clock/freeze/head/budget as `hFrozen`'s facts but for a turn
that does NOT touch the frozen cell — so the gate AGREES with the facts (both admit). -/
def hClean : HostFacts := { trueClock := 0, trueFrozen := [], trueStoredHead := some 42, trueBudget := 1000 }
def ctxClean : AdmCtx := { now := 0, frozen := [], storedHead := some 42, budget := 1000 }

-- POSITIVE: a faithful context decides exactly as the facts (here, both ADMIT the well-formed turn):
#guard (admissible ctxClean h0 s0) == (admissibleFacts hClean h0 s0)
#guard (admissible ctxClean h0 s0) == true
-- The marshalled context (over the read cells, nothing frozen) likewise agrees and admits:
#guard (admissible (marshalledCtx hClean (frozenReads h0)) h0 s0) == (admissibleFacts hClean h0 s0)
#guard (admissible (marshalledCtx hClean (frozenReads h0)) h0 s0) == true

-- NEGATIVE (the teeth, restated as guards): an UNFAITHFUL context DISAGREES with the true facts —
-- the lemma's hypothesis is therefore load-bearing, not vacuous.
#guard (admissible ctxLyingHead h0 s0) != (admissibleFacts hFork h0 s0)         -- stored-head lie
#guard (admissible ctxInflatedBudget h0 s0) != (admissibleFacts hPoorBudget h0 s0) -- budget lie
#guard (admissible ctxDroppedFrozen h0 s0) != (admissibleFacts hFrozen h0 s0)   -- dropped frozen cell
#guard (admissible ctxStaleClock hExp s0) != (admissibleFacts hLateClock hExp s0) -- retarded clock

-- The marshalled freeze-set fidelity on a referenced cell (cross iff truly frozen):
#guard ((marshalledFrozen [7, 9] [7]).contains 7) == ([7, 9] : List CellId).contains 7  -- both true
#guard ((marshalledFrozen [7, 9] [7]).contains 9) == false   -- 9 not referenced ⇒ dropped (gate won't read it)

end Dregg2.Exec.HostCorrespondence
