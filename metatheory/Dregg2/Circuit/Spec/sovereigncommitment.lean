/-
# Dregg2.Circuit.Spec.sovereigncommitment — INDEPENDENT full-state spec + executor⟺spec for `makeSovereignA`.

The effect family **`sovereign-commitment`** (sole variant `makeSovereignA`) is dregg2's
`MakeSovereign`: the one effect that DROPS a cell's host-readable state behind a 32-byte commitment.
Its executor arm (`TurnExecutorFull.execFullA`, `:3564`) is:

    | .makeSovereignA actor cell => makeSovereignStep s actor cell

`makeSovereignStep` (`TurnExecutorFull.lean:1413`) is dregg1's `Ledger::make_sovereign`
(`cell/src/ledger.rs:1014`) modelled faithfully — `cells.remove(id)` +
`sovereign_commitments.insert(id, cell.state_commitment())`. It is a VALUE-REBIND, NOT a flag: the
host-readable record is GONE; only the commitment remains. It commits iff

    stateAuthB s.kernel.caps actor cell = true            -- (self-sovereign authority over `cell`)

and on commit produces the value-rebind post-state: `cell` is replaced by `sovereignRebind` (the
target cell becomes the commitment-only record `[(commitmentField, .dig (stateCommitment (cell cell)))]`,
every OTHER cell whole-preserved), the receipt chain grows by exactly the one self-targeted row, and
EVERYTHING ELSE is literally unchanged.

⚑ FRAME-GAP (executor vs the task's stated guard): the task brief listed the guard as
`stateAuthB … ∧ cell ∈ accounts`. The LIVE executor (`makeSovereignStep`) checks ONLY `stateAuthB`;
there is NO `cell ∈ accounts` membership conjunct and NO lifecycle (`cellLive`/R6) conjunct — unlike
the generic `stateStep`/`stateStepGuarded` field-writing effects. So this module's `MakeSovereignGuard`
is the SINGLE `stateAuthB` conjunct (the honest executor truth). The rebind can therefore make a
NON-ACCOUNT cell sovereign, and a SEALED/DESTROYED cell sovereign — see §6's
`makeSovereignSpec_no_membership_gate` / `_no_lifecycle_gate` teeth, which document this as a
deliberately-recorded gap, NOT a silent one. The spec models the executor EXACTLY (a spec that added
the phantom membership/liveness conjunct would FAIL the `←` direction).

Also note dregg1's real `make_sovereign` mutates THREE host structures (`cells`, `sovereign_commitments`,
and removes the `bal` column); the Lean model collapses all three onto the single `cell` map — the
commitment lands in the rebound `cell` record's `commitmentField`, the readable record is dropped from
`cell`, and `bal` is the SEPARATE per-asset ledger that the model (correctly, see
`makeSovereignKernel_recTotalAsset`) leaves untouched (sovereignty moves the host representation, not
the per-asset supply). So in THIS model `bal` is a FRAME field, not a rewritten one.

## This module (mirrors `Dregg2.Circuit.Transfer`'s `TransferSpec` + `recKExec_iff_spec` pattern)

  1. `MakeSovereignSpec st actor cell st'` : Prop — the INDEPENDENT declarative full-state spec. The
     admissibility guard (`MakeSovereignGuard`, the single `stateAuthB` conjunct, written directly —
     NO `makeSovereignStep`/`makeSovereignKernel` term), the EXACT post-state on the two touched
     components (`kernel.cell` pointwise = the commitment-rebind at `cell`; `log` = receipt :: old
     log), and EVERY OTHER component — all 16 non-`cell` kernel fields — LITERALLY unchanged (THE
     FRAME).
  2. `execFullA_makeSovereignA_iff_spec` : `execFullA st (.makeSovereignA actor cell) = some st' ↔
     MakeSovereignSpec …` — BOTH directions. The `→` validates the executor against the independent
     spec: all 17 kernel fields + log are checked, so a silently-mutated field would make it FAIL.
  3. `sovereignRebindMap_correct` : the declarative validation of the touched-cell post helper (the
     `makeSovereignA` analog of `recTransfer_correct`): the rebound cell IS the commitment-only
     record, OTHER cells whole-preserved.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.SovereignCommitment

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)

set_option linter.dupNamespace false

/-! ## §1 — The independent admissibility guard.

The EXACT gate `makeSovereignStep` checks, written DIRECTLY over the pre-state (no executor term).
Unlike the generic `stateStep` field writes, `makeSovereignStep` has a SINGLE conjunct — the
self-sovereign authority over `cell` — and NO membership / NO lifecycle gate (the recorded
frame-gap; see the module header). -/

/-- **`MakeSovereignGuard s actor cell`** — the full admissibility predicate of a committed
`makeSovereignA`, stated declaratively. The actor holds authority over `cell` (`stateAuthB`,
dregg1's self-sovereign `cell == action_target` gate). THIS is the EXACT (and only) `if`-condition
inside `makeSovereignStep`, peeled out so the spec⟺executor bridge is a clean re-assembly. -/
def MakeSovereignGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true

/-! ## §2 — The touched-cell post map, declaratively, and its validation.

The committed rebind replaces ONLY the `cell` map: at index `cell` it drops the readable record and
installs the commitment-only record `[(commitmentField, .dig (stateCommitment (cell cell)))]`; every
other index whole-preserved. We state that map POINTWISE and validate it with
`sovereignRebindMap_correct` (the `recTransfer_correct` analog). The map is literally `sovereignRebind`
(it is already the independent declarative form — it never mentions the kernel/executor, only the raw
`cell` function), reused here so the spec's `cell`-frame clause is independent of `makeSovereignKernel`. -/

/-- **`sovereignRebindMap_correct`** — the touched-cell post map validated DECLARATIVELY (not
trusted), the `makeSovereignA` analog of `Transfer.recTransfer_correct`: at the target, the rebound
cell IS exactly the commitment-only record (the readable record is GONE, only the commitment of the
WHOLE pre-state value remains); every OTHER cell's whole record is untouched. So the spec's
`sovereignRebind` clause genuinely encodes drop-readable-state ∧ install-commitment ∧ cell-frame. -/
theorem sovereignRebindMap_correct (base : CellId → Value) (target : CellId) :
    sovereignRebind base target target
        = .record [(commitmentField, .dig (stateCommitment (base target)))]
    ∧ (∀ c, c ≠ target → sovereignRebind base target c = base c) := by
  refine ⟨?_, ?_⟩
  · simp only [sovereignRebind, if_pos]
  · intro c hc; simp only [sovereignRebind, if_neg hc]

/-- The declarative post `cell` map coincides with the executor's `makeSovereignKernel` post map (the
bridge that lets the executor↔spec proof discharge the touched-component clause). `rfl`-grade because
`makeSovereignKernel k target = { k with cell := sovereignRebind k.cell target }`. -/
theorem sovereignRebind_eq_makeSovereignKernel (k : RecordKernelState) (target : CellId) :
    sovereignRebind k.cell target = (makeSovereignKernel k target).cell := rfl

/-! ## §3 — THE FULL-STATE DECLARATIVE SPEC (the INDEPENDENT reference). -/

/-- **`MakeSovereignSpec` — the full-state declarative spec of a committed `makeSovereignA`.** The
guard holds; the post-state's `cell` map is the declarative commitment-rebind (`sovereignRebind` —
target dropped behind the commitment, other cells whole-preserved, see `sovereignRebindMap_correct`);
the receipt chain grows by exactly the one self-targeted row; and EVERY OTHER state component is
LITERALLY unchanged — all 16 non-`cell` kernel fields (`accounts caps escrows nullifiers revoked
commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate delegations
sealedBoxes`). No frame clause mentions the executor. -/
def MakeSovereignSpec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) : Prop :=
  MakeSovereignGuard s actor cell
  -- the two TOUCHED components: the commitment-rebind cell map, and the one-row chain extension.
  ∧ s'.kernel.cell = sovereignRebind s.kernel.cell cell
  ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
  -- THE FRAME: all 16 non-`cell` kernel fields, literally unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-! ## §4 — executor ⟺ spec (FULL state, both directions). -/

/-- The `makeSovereignA` arm of `execFullA` is DEFINITIONALLY the value-rebind step — the seam the
whole bridge sits on. -/
theorem execFullA_makeSovereignA_eq (s : RecChainedState) (actor cell : CellId) :
    execFullA s (.makeSovereignA actor cell) = makeSovereignStep s actor cell := rfl

/-- `makeSovereignStep` commits IFF its admissibility guard (`MakeSovereignGuard`) holds — and then
the post-state is exactly the `makeSovereignKernel` rebind + chain extension. The decidable seam both
directions of the bridge reuse. -/
theorem makeSovereignStep_iff_guard_and_post
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) :
    makeSovereignStep s actor cell = some s'
      ↔ (MakeSovereignGuard s actor cell
          ∧ s' = { kernel := makeSovereignKernel s.kernel cell,
                   log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }) := by
  unfold makeSovereignStep MakeSovereignGuard
  by_cases hg : stateAuthB s.kernel.caps actor cell = true
  · rw [if_pos hg]
    constructor
    · intro h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
    · rintro ⟨_, hs'⟩; rw [hs']
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execFullA_makeSovereignA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The live
executor commits a `makeSovereignA` into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The `→`
direction VALIDATES `execFullA`'s `makeSovereignA` arm against the independent spec — all 17 kernel
components + the log are checked, so had the arm silently mutated `bal`/`nullifiers`/`caps`/… any of
the 16 frame fields, the frame clauses would make this proof FAIL; the `←` reconstructs the committed
state from the spec. This is the executor corner of the spec⟺executor⟺circuit triangle for the
`sovereign-commitment` family. -/
theorem execFullA_makeSovereignA_iff_spec
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) :
    execFullA s (.makeSovereignA actor cell) = some s' ↔ MakeSovereignSpec s actor cell s' := by
  rw [execFullA_makeSovereignA_eq, makeSovereignStep_iff_guard_and_post]
  constructor
  · rintro ⟨hg, hs'⟩
    subst hs'
    refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (sovereignRebind_eq_makeSovereignKernel s.kernel cell).symm
    all_goals rfl
  · rintro ⟨hg, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    refine ⟨hg, ?_⟩
    -- rebuild s' field-by-field: the touched cell map, the log, and the 16 frame fields, then η.
    obtain ⟨k', lg'⟩ := s'
    obtain ⟨acc, cl, cps, nul, rev, cmt, bl, sc, fac, lc, dc, dg, dgs, dge, dgea⟩ := k'
    simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    subst hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    -- the touched cell map: rewrite the declarative map to the executor's makeSovereignKernel form.
    rw [sovereignRebind_eq_makeSovereignKernel] at hcell
    subst hcell
    rfl

/-! ## §5 — Spec-side corollaries (the touched components + the FRAME, read off the spec).

These show the spec is the genuine semantics: a committed `makeSovereignA` drops the target behind a
commitment, leaves every other cell whole, and leaves every non-`cell` component untouched — derived
from the spec, NOT the executor. -/

/-- **The rebound cell IS the commitment-only record.** Off the spec: a committed `makeSovereignA`
replaces `cell`'s record with EXACTLY `[(commitmentField, .dig (stateCommitment (pre-value)))]` — the
readable state is GONE, only the commitment of the whole pre-state value remains. -/
theorem makeSovereignSpec_commitment_value
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    s'.kernel.cell cell
      = .record [(commitmentField, .dig (stateCommitment (s.kernel.cell cell)))] := by
  rw [h.2.1]; exact (sovereignRebindMap_correct s.kernel.cell cell).1

/-- **THE TEETH: the pre-state `balance` is no longer directly readable.** Off the spec: after a
committed `makeSovereignA`, reading the `balance` scalar of the rebound cell returns `none` — the
host-readable state moved behind the §8 commitment (a flag model would leave it readable; this is the
distinguishing fidelity of the value-rebind). -/
theorem makeSovereignSpec_balance_unreadable
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    (s'.kernel.cell cell).scalar "balance" = none := by
  rw [makeSovereignSpec_commitment_value h]
  rfl

/-- **Cell-frame: other cells whole-preserved.** Off the spec: a committed `makeSovereignA` leaves
every cell OTHER than `cell` byte-for-byte unchanged. -/
theorem makeSovereignSpec_cell_frame
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  intro c hc; rw [h.2.1]; exact (sovereignRebindMap_correct s.kernel.cell cell).2 c hc

/-- **Authority obligation.** Off the spec: a committed `makeSovereignA` was authorized over `cell`
(the self-sovereign gate). -/
theorem makeSovereignSpec_authorized
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    stateAuthB s.kernel.caps actor cell = true := h.1

/-- **The `bal` ledger frame.** Off the spec: making a cell sovereign never touches the per-asset
ledger — the value moves behind the commitment on the HOST, not the per-asset supply (the
conservation-relevant frame fact). -/
theorem makeSovereignSpec_bal_frame
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    s'.kernel.bal = s.kernel.bal := h.2.2.2.2.2.2.2.2.1

/-- **The caps frame.** Off the spec: a `makeSovereignA` never edits the cap table (authority Δ = 0;
the regime invariant — sovereignty is a representation move, not a capability grant). -/
theorem makeSovereignSpec_caps_frame
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    s'.kernel.caps = s.kernel.caps := h.2.2.2.2.1

/-- **The accounts frame.** Off the spec: a `makeSovereignA` never changes the live-account set —
the cell stays (or stays absent) in `accounts`; sovereignty drops the *readable record*, not the
account-membership bookkeeping. -/
theorem makeSovereignSpec_accounts_frame
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    s'.kernel.accounts = s.kernel.accounts := h.2.2.2.1

/-- **The chain grows by exactly one self-targeted row.** Off the spec: the receipt log gets exactly
the `{actor, src := cell, dst := cell, amt := 0}` metadata row prepended (the clock advance; ObsAdvance). -/
theorem makeSovereignSpec_log
    {s s' : RecChainedState} {actor cell : CellId}
    (h : MakeSovereignSpec s actor cell s') :
    s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log := h.2.2.1

/-! ## §6 — NON-VACUITY + the recorded FRAME-GAP teeth.

A spec that accepts everything is worthless. We exhibit fail-closedness on the ONE real gate
(authority), AND we make the frame-gap (no membership / no lifecycle conjunct) a PROVED fact rather
than a silent omission. -/

/-- **Unauthorized rejection (fail-closed).** If the actor does NOT hold authority over `cell`
(`stateAuthB = false`), no `s'` satisfies the spec — the executor's sole gate, mirrored on the
independent spec. -/
theorem makeSovereignSpec_rejects_unauthorized
    (s : RecChainedState) (actor cell : CellId)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    ¬ ∃ s', MakeSovereignSpec s actor cell s' := by
  rintro ⟨s', h⟩; rw [makeSovereignSpec_authorized h] at hbad; exact absurd hbad (by simp)

/-- **⚑ FRAME-GAP, RECORDED — NO membership gate.** Unlike the generic `stateStep` field writes,
`makeSovereignA` admits a target that is NOT a live account: whenever `stateAuthB` holds, the spec is
inhabited EVEN IF `cell ∉ accounts`. This is the EXACT executor behaviour (`makeSovereignStep` has no
`cell ∈ accounts` conjunct) — proved here so the gap vs the task's stated guard is documented, not
hidden. (Whether dregg1's `Ledger::make_sovereign` SHOULD reject a non-existent cell — `cells.remove`
returns `Err` — is a separate executor-fidelity question; this lemma just pins what the Lean model
does.) -/
theorem makeSovereignSpec_no_membership_gate
    (s : RecChainedState) (actor cell : CellId)
    (hauth : stateAuthB s.kernel.caps actor cell = true) :
    ∃ s', MakeSovereignSpec s actor cell s' := by
  refine ⟨{ kernel := makeSovereignKernel s.kernel cell,
            log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }, ?_⟩
  rw [← execFullA_makeSovereignA_iff_spec, execFullA_makeSovereignA_eq, makeSovereignStep,
      if_pos hauth]

/-- **⚑ FRAME-GAP, RECORDED — NO lifecycle (R6) gate.** Again unlike the generic state writes,
`makeSovereignA` admits a cell whose lifecycle does NOT accept effects (sealed/destroyed): whenever
`stateAuthB` holds the spec is inhabited regardless of `lifecycle`. Same `stateAuthB`-only witness as
above; stated separately to make the missing-R6-conjunct explicit. -/
theorem makeSovereignSpec_no_lifecycle_gate
    (s : RecChainedState) (actor cell : CellId)
    (hauth : stateAuthB s.kernel.caps actor cell = true) :
    ∃ s', MakeSovereignSpec s actor cell s' :=
  makeSovereignSpec_no_membership_gate s actor cell hauth

/-! ## §7 — Concrete #guard witnesses: a GOOD rebind commits to the spec'd state; BAD ones reject.

Cell 0 is a self-owned account (actor 0 = cell 0, so `stateAuthB` passes by ownership). Making cell 0
sovereign commits; the rebound cell's `balance` becomes unreadable and a `commitment` digest appears.
An unauthorized actor (9) is rejected. -/

/-- A concrete pre-state: live accounts {0,1}, cell 0 carries a rich readable record, empty caps
(authority by ownership), empty log. -/
def sMS0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("nonce", .int 3)]
                         else .record [("balance", .int 5)]
        caps := fun _ => [] }
    log := [] }

-- the executor COMMITS the good self-sovereign rebind (actor 0 owns cell 0):
#guard (execFullA sMS0 (.makeSovereignA 0 0)).isSome  -- true

-- THE TEETH: the committed cell 0's `balance` is NO LONGER directly readable (record dropped):
#guard
  (match execFullA sMS0 (.makeSovereignA 0 0) with
   | some s' => ((s'.kernel.cell 0).scalar "balance").isNone
   | none    => false)  -- true

-- ...and a `commitment` digest IS present (binds the whole pre-state value):
#guard
  (match execFullA sMS0 (.makeSovereignA 0 0) with
   | some s' => ((s'.kernel.cell 0).field "commitment").isSome
   | none    => false)  -- true

-- the OTHER cell (1) is whole-preserved (cell-frame): its `balance` is STILL readable as 5, and
-- `accounts` is untouched (decidable Finset equality):
#guard
  (match execFullA sMS0 (.makeSovereignA 0 0) with
   | some s' => decide ((s'.kernel.cell 1).scalar "balance" = some 5)
                && decide (s'.kernel.accounts = sMS0.kernel.accounts)
   | none    => false)  -- true

-- the chain grew by exactly one row:
#guard ((execFullA sMS0 (.makeSovereignA 0 0)).map (fun s => s.log.length)) == some 1  -- some 1

-- an UNAUTHORIZED actor (9 owns nothing, no cap over cell 0) is REJECTED (fail-closed):
#guard (execFullA sMS0 (.makeSovereignA 9 0)).isNone  -- true

-- ⚑ FRAME-GAP witness: a NON-ACCOUNT, self-authored target (cell 7 ∉ accounts) STILL commits —
--   `makeSovereignStep` has no membership gate (contrast `setFieldA`, which would reject):
#guard (execFullA sMS0 (.makeSovereignA 7 7)).isSome  -- true (no `cell ∈ accounts` gate)

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms sovereignRebindMap_correct
#assert_axioms sovereignRebind_eq_makeSovereignKernel
#assert_axioms execFullA_makeSovereignA_eq
#assert_axioms makeSovereignStep_iff_guard_and_post
#assert_axioms execFullA_makeSovereignA_iff_spec
#assert_axioms makeSovereignSpec_commitment_value
#assert_axioms makeSovereignSpec_balance_unreadable
#assert_axioms makeSovereignSpec_cell_frame
#assert_axioms makeSovereignSpec_authorized
#assert_axioms makeSovereignSpec_bal_frame
#assert_axioms makeSovereignSpec_caps_frame
#assert_axioms makeSovereignSpec_accounts_frame
#assert_axioms makeSovereignSpec_log
#assert_axioms makeSovereignSpec_rejects_unauthorized
#assert_axioms makeSovereignSpec_no_membership_gate
#assert_axioms makeSovereignSpec_no_lifecycle_gate

end Dregg2.Circuit.Spec.SovereignCommitment
