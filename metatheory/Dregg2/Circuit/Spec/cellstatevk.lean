/-
# Dregg2.Circuit.Spec.cellstatevk — INDEPENDENT full-state spec + executor⟺spec for the
  "cell-state-vk" effect family (variant: `setVKA`).

This is a LEAF spec module in the shape of `Dregg2.Circuit.Transfer` (`TransferSpec` +
`recKExec_iff_spec` + `recTransfer_correct`), but for the protocol-managed `verification_key` slot
write the live executor runs in its `.setVKA` arm
(`TurnExecutorFull.execFullA`, `:3496`):

    execFullA s (.setVKA actor cell vk)  =  stateStep s vkField actor cell (.int vk)

This is dregg1's `SetVerificationKey { cell, new_vk }` / `apply_set_verification_key`
(`apply.rs` ~:803): the upgrade-relevant VK-field write. Unlike the developer-facing `setFieldA` (which
routes through the per-slot caveat gate `stateStepGuarded`), `setVKA` writes a PROTOCOL-managed slot,
so it stays on the bare authority-gated `stateStep`.

`stateStep` (EffectsState.lean:207) commits iff its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY: the actor holds authority over `cell`
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP: `cell` is a live account
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS: `cell`'s lifecycle admits effects (R6)

— and on commit writes the `verification_key` field of `cell` to `vk` (`writeField`, touching ONLY
that cell's `verification_key` slot) and extends the receipt chain by one self-targeted row. NO
balance move, NO cap edit: the whole regime invariant. THIS module proves the executor meets an
INDEPENDENT declarative full-state spec EXACTLY (both directions), enumerating ALL 17 kernel fields +
the `log` so no ghost field can be silently mutated.

## What is proved (the §6b corner of the spec⟺executor triangle, copied from `Transfer.lean`)

  1. `SetVKSpec s actor cell vk s'` : Prop — the INDEPENDENT declarative post-state: the three-leg
     guard ∧ the EXACT `cell`-map post-image (the `verification_key` of `cell` set to `vk`, every other
     cell's whole record untouched) ∧ EVERY OTHER kernel field (16 of them) LITERALLY unchanged ∧ the
     `log` extended by exactly the one self-targeted receipt row. No frame clause mentions `execFullA`
     / `stateStep`.

  2. `execFullA_setVK_iff_spec` : `execFullA s (.setVKA actor cell vk) = some s' ↔
     SetVKSpec s actor cell vk s'` — BOTH directions. The `→` half VALIDATES the executor: all 17
     kernel components + the `log` are checked, so a silently-mutated field would make the proof FAIL.

  3. `setVK_cellWrite_correct` — the post-state-helper validation lemma (mirrors `recTransfer_correct`):
     the `verification_key`-write helper sets `cell`'s `verification_key` to exactly `vk`, leaves
     `cell`'s conserved `balance` (a DISTINCT slot) intact, and leaves every OTHER cell's whole record
     untouched.

  4. `#assert_axioms` on every theorem — whitelist `{propext, Classical.choice, Quot.sound}` only.

The family has the single executable variant `setVKA`. The generic `vkStateStep_iff_spec` engine
below is re-derived LOCALLY (so this leaf is self-contained — no dependence on a sibling spec module)
and specialized to `vkField`.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellStateVK

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps)

/-! ## §1 — the admissibility guard `stateStep`/`setVKA` checks, as a `Prop`.

The exact conjunction in `stateStep`'s `if` (EffectsState.lean:209) — extracting it makes the
spec⟺executor proof a clean re-assembly, mirroring `Transfer.admitGuard`. -/

/-- **`setVKGuard` — the three-leg admissibility gate** the executor checks before it commits a
`setVKA`: AUTHORITY over `cell`, `cell` is a live account (MEMBERSHIP), and `cell`'s lifecycle admits
effects (LIVENESS — the R6 gate). Stated independently of the executor term. -/
def setVKGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true
  ∧ cell ∈ s.kernel.accounts
  ∧ cellLive s.kernel cell = true

/-! ## §2 — the post-state cell-map helper, validated DECLARATIVELY (not trusted).

`setVKCellMap k cell vk` is the `cell`-indexed record map a committed VK write produces: cell `cell`'s
`verification_key` slot set to `vk` (its other fields kept), every other cell whole-preserved. Written
WITHOUT the executor's `writeField` so the spec's `cell`-clause is the genuine semantics, and proved
equal to `writeField … vkField …` so the executor's actual post-cell-map meets it. -/

/-- The declarative post-cell-map of a VK write: only `cell`'s `verification_key` field moves. -/
def setVKCellMap (k : RecordKernelState) (cell : CellId) (vk : Int) : CellId → Value :=
  fun c => if c = cell then setField vkField (k.cell c) (.int vk) else k.cell c

/-- **`setVKCellMap_eq_writeField` — the helper matches the executor's `writeField`** (so the
declarative cell-clause and the executor's actual post-cell-map are the SAME function). -/
theorem setVKCellMap_eq_writeField (k : RecordKernelState) (cell : CellId) (vk : Int) :
    setVKCellMap k cell vk = (writeField k vkField cell (.int vk)).cell := by
  rfl

/-- **`setVK_cellWrite_correct` — the cell-update helper validated DECLARATIVELY** (the
`recTransfer_correct` analog). A VK write (a) sets `cell`'s `verification_key` slot to exactly `vk`,
(b) leaves `cell`'s conserved `balance` field untouched (the regime's balance-Δ=0 obligation, via the
non-interference of a DISTINCT slot — `verification_key ≠ balance`), and (c) leaves every OTHER cell's
whole record untouched. So the spec's `cell`-clause genuinely encodes write ∧ balance-frame ∧
cell-frame, rather than blindly trusting the helper. -/
theorem setVK_cellWrite_correct (k : RecordKernelState) (cell : CellId) (vk : Int) :
    fieldOf vkField (setVKCellMap k cell vk cell) = vk
    ∧ balOf (setVKCellMap k cell vk cell) = balOf (k.cell cell)
    ∧ (∀ c, c ≠ cell → setVKCellMap k cell vk c = k.cell c) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [setVKCellMap, if_pos]; exact setField_fieldOf vkField (k.cell cell) vk
  · simp only [setVKCellMap, if_pos]
    exact setField_balOf vkField (k.cell cell) (.int vk) (by decide)
  · intro c hc; simp only [setVKCellMap, if_neg hc]

/-! ## §3 — the FULL-STATE declarative spec (the INDEPENDENT reference) + executor⟺spec.

`SetVKSpec` is the COMPLETE state transition of a committed VK write, written INDEPENDENTLY of the
executor (no `execFullA`/`stateStep` term in any frame clause): the three-leg guard holds; the
post-state's `cell` map is the VK write (`setVKCellMap`, validated above); the `log` is extended by
exactly the one self-targeted receipt row; and ALL 16 non-`cell` kernel components — `accounts` `caps`
`escrows` `nullifiers` `revoked` `commitments` `bal` `queues` `swiss` `slotCaveats` `factories`
`lifecycle` `deathCert` `delegate` `delegations` `sealedBoxes` — are LITERALLY unchanged. Missing ANY
of these reintroduces a ghost, so all 17 kernel fields + the `log` are enumerated. This is the apex
reference truth the executor is proved equal to. -/

/-- **The full-state declarative spec of a committed `setVKA`** — the INDEPENDENT reference semantics.
The guard holds; the post-state's `cell` map is the VK write (every other cell whole, `cell`'s other
fields kept — see `setVK_cellWrite_correct`); the `log` is the one-row self-targeted extension; and
every one of the 16 non-`cell` kernel components is unchanged. No frame clause mentions the
executor. -/
def SetVKSpec (s : RecChainedState) (actor cell : CellId) (vk : Int)
    (s' : RecChainedState) : Prop :=
  setVKGuard s actor cell
  -- the ONE touched component: cell `cell`'s `verification_key` slot written, every other cell whole
  ∧ s'.kernel.cell = setVKCellMap s.kernel cell vk
  -- the log: extended by EXACTLY one self-targeted receipt row
  ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
  -- THE FRAME: every one of the 16 OTHER kernel components literally unchanged
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.escrows = s.kernel.escrows ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.queues = s.kernel.queues
  ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-- **`vkStateStep_iff_spec` — the GENERIC `stateStep` characterization (executor⟺spec, full state),
re-derived LOCALLY.** The bare `stateStep` (the engine the `.setVKA` arm runs) commits a write of
field `f`:=`v` into `s'` IFF `s'` is EXACTLY the three-leg-gated full post-state: the `cell` map is the
single-field write, the `log` is the one-row self-targeted extension, and ALL 16 other kernel
components are literally unchanged. The `→` direction VALIDATES `stateStep` — all 17 kernel components
+ the `log` are checked, so a silently mutated `bal`/`nullifiers`/`caps`/… would make the frame clauses
FAIL; the `←` reconstructs the committed state from the spec. The `setVKA` theorem below is a clean
instance of this. -/
theorem vkStateStep_iff_spec (s : RecChainedState) (f : FieldName) (actor cell : CellId) (v : Value)
    (s' : RecChainedState) :
    stateStep s f actor cell v = some s' ↔
      ( (stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
            ∧ cellLive s.kernel cell = true)
        ∧ s'.kernel.cell = (fun c => if c = cell then setField f (s.kernel.cell c) v
                                     else s.kernel.cell c)
        ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
        ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.caps = s.kernel.caps
        ∧ s'.kernel.escrows = s.kernel.escrows ∧ s'.kernel.nullifiers = s.kernel.nullifiers
        ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
        ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.queues = s.kernel.queues
        ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
        ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
        ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
        ∧ s'.kernel.delegations = s.kernel.delegations
        ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes ) := by
  unfold stateStep
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
      ∧ cellLive s.kernel cell = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    · rintro ⟨_, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      obtain ⟨k', l'⟩ := s'
      obtain ⟨a, ce, ca, es, nu, re, co, ba, qu, sw, sl, fa, li, dc, de, dg, sb⟩ := k'
      simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- The `.setVKA` arm of `execFullA` is DEFINITIONALLY the bare authority-gated VK-field write — the
seam the whole bridge sits on. -/
theorem execFullA_setVK_eq (s : RecChainedState) (actor cell : CellId) (vk : Int) :
    execFullA s (.setVKA actor cell vk) = stateStep s vkField actor cell (.int vk) := rfl

/-- **`execFullA_setVK_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The live per-asset
executor's `.setVKA` arm commits a `verification_key` write into `s'` IFF `s'` is EXACTLY the spec'd
full post-state. The `→` direction VALIDATES the executor against the independent spec — all 17 kernel
components + the `log` are checked, so had the arm silently mutated `bal`/`nullifiers`/`caps`/… the
frame clauses would make this proof FAIL; the `←` reconstructs the committed state from the spec. This
is the executor corner of the spec⟺executor⟺circuit triangle for the cell-state-vk family. -/
theorem execFullA_setVK_iff_spec (s : RecChainedState) (actor cell : CellId) (vk : Int)
    (s' : RecChainedState) :
    execFullA s (.setVKA actor cell vk) = some s' ↔ SetVKSpec s actor cell vk s' := by
  -- the arm IS `stateStep s vkField actor cell (.int vk)` definitionally
  rw [execFullA_setVK_eq, vkStateStep_iff_spec]
  unfold SetVKSpec setVKGuard setVKCellMap
  -- the two statements are the SAME conjunction modulo `vkField`/`(.int vk)` substitution
  rfl

/-! ## §4 — corollaries: the projections onto the touched component + the balance/cap frame.

These are the cell-state-vk analogs of `Transfer`'s debit/credit/conservation facts: a committed VK
write leaves the conserved balance untouched (regime balance-Δ=0) and the cap-graph untouched (no
authority amplification), with the `verification_key` slot set to exactly `vk`. Each is a clean read
off `execFullA_setVK_iff_spec`. -/

/-- **`execFullA_setVK_vkWritten` — the `verification_key` slot is set to exactly `vk`.** -/
theorem execFullA_setVK_vkWritten {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (h : execFullA s (.setVKA actor cell vk) = some s') :
    fieldOf vkField (s'.kernel.cell cell) = vk := by
  have hspec := (execFullA_setVK_iff_spec s actor cell vk s').mp h
  rw [hspec.2.1]
  exact (setVK_cellWrite_correct s.kernel cell vk).1

/-- **`execFullA_setVK_balFrame` — BALANCE LEDGER untouched (the regime balance-Δ=0).** The per-asset
`bal` ledger is literally unchanged: a VK write moves NO value. -/
theorem execFullA_setVK_balFrame {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (h : execFullA s (.setVKA actor cell vk) = some s') :
    s'.kernel.bal = s.kernel.bal :=
  ((execFullA_setVK_iff_spec s actor cell vk s').mp h).2.2.2.2.2.2.2.2.2.1

/-- **`execFullA_setVK_capFrame` — CAP-GRAPH untouched (no authority amplification).** The `caps`
table is literally unchanged: a VK write edits NO capability. -/
theorem execFullA_setVK_capFrame {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (h : execFullA s (.setVKA actor cell vk) = some s') :
    s'.kernel.caps = s.kernel.caps :=
  ((execFullA_setVK_iff_spec s actor cell vk s').mp h).2.2.2.2.1

/-- **`execFullA_setVK_otherCellsFrame` — every OTHER cell's whole record untouched.** -/
theorem execFullA_setVK_otherCellsFrame {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (h : execFullA s (.setVKA actor cell vk) = some s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  have hspec := (execFullA_setVK_iff_spec s actor cell vk s').mp h
  intro c hc
  rw [hspec.2.1]
  exact (setVK_cellWrite_correct s.kernel cell vk).2.2 c hc

/-- **`execFullA_setVK_admits_guard` — a committed VK write means the guard held** (the soundness
projection: the arm commits IFF the three-leg admissibility gate is satisfied). -/
theorem execFullA_setVK_admits_guard {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (h : execFullA s (.setVKA actor cell vk) = some s') :
    setVKGuard s actor cell :=
  ((execFullA_setVK_iff_spec s actor cell vk s').mp h).1

/-! ## §5 — NON-VACUITY: the guard genuinely REJECTS bad inputs.

A spec that the executor meets vacuously (because the arm accepts everything) is worthless. These
exhibit the arm as a genuine gate: an unauthorized actor, a non-account `cell`, and a non-Live
(sealed/destroyed) `cell` each make the arm FAIL CLOSED (`= none`), so no spec post-state exists. -/

/-- **`setVK_rejects_unauthorized` — PROVED.** If the actor does NOT hold authority over `cell`, the
arm fails closed: no committed post-state exists. -/
theorem setVK_rejects_unauthorized (s : RecChainedState) (actor cell : CellId) (vk : Int)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    execFullA s (.setVKA actor cell vk) = none := by
  rw [execFullA_setVK_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨hauth, _, _⟩
  rw [hbad] at hauth; exact absurd hauth (by simp)

/-- **`setVK_rejects_nonaccount` — PROVED.** If `cell` is not a live account, the arm fails closed. -/
theorem setVK_rejects_nonaccount (s : RecChainedState) (actor cell : CellId) (vk : Int)
    (hbad : cell ∉ s.kernel.accounts) :
    execFullA s (.setVKA actor cell vk) = none := by
  rw [execFullA_setVK_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, hmem, _⟩; exact hbad hmem

/-- **`setVK_rejects_nonlive` — PROVED.** If `cell`'s lifecycle does NOT admit effects
(sealed/destroyed — the R6 gate), the arm fails closed. This is the executor-level lifecycle
enforcement: a VK write into a sealed cell is REJECTED — the very upgrade-safety property
`SetVerificationKey` needs (a destroyed cell cannot have its VK rotated out from under its proofs). -/
theorem setVK_rejects_nonlive (s : RecChainedState) (actor cell : CellId) (vk : Int)
    (hbad : cellLive s.kernel cell = false) :
    execFullA s (.setVKA actor cell vk) = none := by
  rw [execFullA_setVK_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, _, hlive⟩
  rw [hbad] at hlive; exact absurd hlive (by simp)

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms setVKCellMap_eq_writeField
#assert_axioms setVK_cellWrite_correct
#assert_axioms vkStateStep_iff_spec
#assert_axioms execFullA_setVK_eq
#assert_axioms execFullA_setVK_iff_spec
#assert_axioms execFullA_setVK_vkWritten
#assert_axioms execFullA_setVK_balFrame
#assert_axioms execFullA_setVK_capFrame
#assert_axioms execFullA_setVK_otherCellsFrame
#assert_axioms execFullA_setVK_admits_guard
#assert_axioms setVK_rejects_unauthorized
#assert_axioms setVK_rejects_nonaccount
#assert_axioms setVK_rejects_nonlive

end Dregg2.Circuit.Spec.CellStateVK
