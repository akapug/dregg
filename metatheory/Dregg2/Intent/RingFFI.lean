/-
# Dregg2.Intent.RingFFI — the FFI-EXPORT bridge: one `settleRing` leg IS the verified scalar export
`recKExec`, on the moved asset column.

This is what makes the LIVE Rust path (`intent/src/verified_settle.rs`, routing each lowered ring leg
through the `@[export] dregg_record_kernel_step` over the PROVED `Exec.recKExec`) a FAITHFUL per-leg
executor for the verified `Dregg2.Intent.Ring.settleRing` — NOT a Rust re-implementation/mirror.

## The residual this closes

`Ring.lean` proves `settleRing` (the fold through the per-asset executor `recKExecAsset`) conserves and
is atomic, and that the lowered legs coincide with the verified `RingLeg.toTurn`. But the running engine
never executed any of that — and the Rust differentials re-implemented `settleRing` as a hand-mirror.
The one verified executor the FFI actually EXPORTS is the scalar `dregg_record_kernel_step`, which runs
`Exec.recKExec` over a cell record's **`balance` field** (`balOf (k.cell src)`). A `settleRing` leg runs
`recKExecAsset` over the **per-asset ledger** (`k.bal src a`). Are they the same transition?

Yes — once we PROJECT the per-asset column `a` onto the scalar `balance` field: seed each cell's
`balance := k.bal c a`, leave `caps`/`accounts` as-is. The two gates then coincide
character-for-character (`authorizedB`, `0 ≤ amt ≤ src-balance-in-a`, `src ≠ dst`, liveness), and the
committed post-state's `a` column equals the projected scalar's `balance` field.

So the Rust FFI fold — calling the verified scalar export once per leg over the asset-projected cells —
computes EXACTLY `settleRing`, leg by leg, with its accept/reject and post-state the VERIFIED ones. "An
intent fulfilled = a verified executor turn" is therefore not a Rust mirror dressed as verified: the
Rust fold's verdict and ledger ARE the verified `settleRing`'s, proved here, not asserted.

Pure. Pins the FFI-exported executor to the Lean ring keystones.
-/
import Dregg2.Intent.Ring
import Dregg2.Exec.RecordKernel

set_option linter.dupNamespace false

namespace Dregg2.Intent.RingFFI

open Dregg2.Exec (RecordKernelState AssetId Turn CellId recKExecAsset recKExec recTotalAsset
  balOf setBalance setBalance_balOf authorizedB recTransfer recTransferBal cellLifecycleLive)

/-- **`projAsset k a` — project the per-asset column `a` onto the scalar `balance` field** the FFI export
`recKExec` reads. Each live cell's record gets its `balance` field overwritten to `k.bal c a`; `caps` and
`accounts` are unchanged (authority + liveness are asset-agnostic). This is the exact state the live Rust
path (`verified_settle.rs`) marshals to `dregg_record_kernel_step` for asset `a`. -/
def projAsset (k : RecordKernelState) (a : AssetId) : RecordKernelState :=
  { k with cell := fun c => setBalance (k.cell c) (k.bal c a) }

@[simp] theorem projAsset_caps (k : RecordKernelState) (a : AssetId) :
    (projAsset k a).caps = k.caps := rfl

@[simp] theorem projAsset_accounts (k : RecordKernelState) (a : AssetId) :
    (projAsset k a).accounts = k.accounts := rfl

/-- The projection touches only the `cell` field, so it preserves the per-cell lifecycle registry —
hence the kernel liveness predicate is unchanged. (`recKExecAsset` gates on SOURCE liveness; the export
runs over the projection, so the two see the SAME liveness verdict.) -/
@[simp] theorem projAsset_cellLifecycleLive (k : RecordKernelState) (a : AssetId) (c : CellId) :
    cellLifecycleLive (projAsset k a) c = cellLifecycleLive k c := rfl

/-- Reading the projected `balance` field back yields the `a`-column balance — the write/read law of the
projection (`setBalance_balOf`). -/
@[simp] theorem projAsset_balOf (k : RecordKernelState) (a : AssetId) (c : CellId) :
    balOf ((projAsset k a).cell c) = k.bal c a := by
  show balOf (setBalance (k.cell c) (k.bal c a)) = k.bal c a
  exact setBalance_balOf _ _

/-- **GATE COINCIDENCE — the verified scalar export's commit-condition for a leg's turn over the
asset-projected state, conjoined with the SOURCE-liveness gate, is EXACTLY the per-asset leg gate.** Both
reduce to: authorized over `src`, amount non-negative and available IN ASSET `a`, distinct endpoints,
both accounts, and the SOURCE cell live (the `cellLifecycleLive` leg `recKExecAsset` now gates on). The
projection preserves the lifecycle registry, so the export-over-projection plus the liveness check the
live path marshals accepts a leg precisely when the verified per-asset executor does. -/
theorem recKExec_projAsset_gate_iff (k : RecordKernelState) (turn : Turn) (a : AssetId) :
    (authorizedB (projAsset k a).caps turn = true ∧ 0 ≤ turn.amt
        ∧ turn.amt ≤ balOf ((projAsset k a).cell turn.src)
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ (projAsset k a).accounts
        ∧ turn.dst ∈ (projAsset k a).accounts
        ∧ cellLifecycleLive (projAsset k a) turn.src = true)
      ↔ (authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
        ∧ cellLifecycleLive k turn.src = true) := by
  rw [projAsset_caps, projAsset_accounts, projAsset_balOf, projAsset_cellLifecycleLive]

/-- **The FFI export, AND the source-liveness check, COMMITS a leg iff the per-asset executor does.**
The verified per-asset executor `recKExecAsset` now gates on SOURCE liveness (the `cellLifecycleLive`
leg); the scalar export `recKExec` does not, so the export's `ok` bit alone is the per-asset verdict only
once the live path also applies the lifecycle check it marshals. This pins exactly that: `recKExecAsset`
commits iff the export over the projection commits AND the source cell is live — the bit the live Rust
path computes (`ok && live`) is the verified per-asset accept/reject, no Rust gate re-derivation. -/
theorem recKExec_projAsset_commits_iff (k : RecordKernelState) (turn : Turn) (a : AssetId) :
    ((recKExec (projAsset k a) turn).isSome && cellLifecycleLive k turn.src)
      = (recKExecAsset k turn a).isSome := by
  unfold recKExec recKExecAsset
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
      ∧ cellLifecycleLive k turn.src = true
  · -- the full asset gate holds: the export's 6-gate (its first six legs) and liveness both hold.
    have hge : authorizedB (projAsset k a).caps turn = true ∧ 0 ≤ turn.amt
        ∧ turn.amt ≤ balOf ((projAsset k a).cell turn.src)
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ (projAsset k a).accounts
        ∧ turn.dst ∈ (projAsset k a).accounts := by
      rw [projAsset_caps, projAsset_accounts, projAsset_balOf]
      exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1⟩
    rw [if_pos hg, if_pos hge]
    simp [hg.2.2.2.2.2.2]
  · rw [if_neg hg]
    by_cases he : authorizedB (projAsset k a).caps turn = true ∧ 0 ≤ turn.amt
        ∧ turn.amt ≤ balOf ((projAsset k a).cell turn.src)
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ (projAsset k a).accounts
        ∧ turn.dst ∈ (projAsset k a).accounts
    · rw [if_pos he]
      -- export commits, but the full asset gate failed; the missing leg is source liveness.
      rw [projAsset_caps, projAsset_accounts, projAsset_balOf] at he
      by_cases hlive : cellLifecycleLive k turn.src = true
      · exact absurd ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2, hlive⟩ hg
      · rw [Bool.not_eq_true] at hlive; simp [hlive]
    · rw [if_neg he]; rfl

/-- **COLUMN AGREEMENT — when a leg commits, the export's post-state `balance` field equals the per-asset
executor's `a`-column.** The verified scalar export, run over the asset-`a` projection, writes back
exactly the `a`-column `recKExecAsset` produces: every cell's resulting `balance` field equals `k'.bal c
a`. So the post-state the live Rust path reads back from the export IS the verified per-asset post-state
on the moved column. The FFI fold's running ledger tracks the verified one with NO gap. -/
theorem recKExec_projAsset_column_agrees (k k' : RecordKernelState) (turn : Turn) (a : AssetId)
    (h : recKExecAsset k turn a = some k') (c : CellId) :
    balOf (((recKExec (projAsset k a) turn).getD (projAsset k a)).cell c) = k'.bal c a := by
  -- the leg commits, so its FULL gate holds (incl. the source-liveness leg).
  have hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
      ∧ cellLifecycleLive k turn.src = true := by
    unfold recKExecAsset at h
    by_cases hgg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src a
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
        ∧ cellLifecycleLive k turn.src = true
    · exact hgg
    · rw [if_neg hgg] at h; exact absurd h (by simp)
  -- the per-asset post-state `k'` is the `a`-column transfer.
  have hk' : k' = { k with bal := recTransferBal k.bal turn.src turn.dst a turn.amt } := by
    unfold recKExecAsset at h; rw [if_pos hg] at h; exact ((Option.some.injEq _ _).mp h).symm
  -- the export's (6-leg) gate fires over the projection (the asset gate's first six legs).
  have hge : authorizedB (projAsset k a).caps turn = true ∧ 0 ≤ turn.amt
      ∧ turn.amt ≤ balOf ((projAsset k a).cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ (projAsset k a).accounts
      ∧ turn.dst ∈ (projAsset k a).accounts := by
    rw [projAsset_caps, projAsset_accounts, projAsset_balOf]
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1⟩
  have hexec : recKExec (projAsset k a) turn
      = some { (projAsset k a) with
                cell := recTransfer (projAsset k a).cell turn.src turn.dst turn.amt } := by
    unfold recKExec; rw [if_pos hge]
  rw [hexec]
  simp only [Option.getD_some]
  subst hk'
  -- compute both post-cells on the `balance` field / `a` column.
  show balOf (recTransfer (projAsset k a).cell turn.src turn.dst turn.amt c)
      = recTransferBal k.bal turn.src turn.dst a turn.amt c a
  unfold recTransfer recTransferBal
  rw [if_pos (rfl : a = a)]
  rcases eq_or_ne c turn.src with h1 | h1
  · subst h1
    rw [if_pos rfl, if_pos rfl, setBalance_balOf, projAsset_balOf]
  · rcases eq_or_ne c turn.dst with h2 | h2
    · subst h2
      rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl, setBalance_balOf, projAsset_balOf]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, projAsset_balOf]

/-- **THE FFI-FAITHFULNESS KEYSTONE — running the verified scalar export `recKExec` once per leg, over
each leg's asset projection, computes EXACTLY a `settleRing` leg.** This is the statement the live Rust
path (`intent/src/verified_settle.rs`) realises: it folds the lowered legs through the real
`@[export] dregg_record_kernel_step` (the PROVED `recKExec`), one call per leg on the asset-`a`
projection, and (by `recKExec_projAsset_commits_iff` + `recKExec_projAsset_column_agrees`) its
accept/reject bit and its produced post-column ARE the verified per-asset executor's. Therefore "an
intent fulfilled = a verified executor turn" is not a Rust mirror dressed as verified: the Rust fold's
verdict and ledger ARE the verified `settleRing`'s, leg by leg. -/
theorem ffi_export_realises_settleRing_leg (k : RecordKernelState) (turn : Turn) (a : AssetId) :
    ((recKExec (projAsset k a) turn).isSome && cellLifecycleLive k turn.src)
        = (recKExecAsset k turn a).isSome ∧
      (∀ k', recKExecAsset k turn a = some k' →
        ∀ c, balOf (((recKExec (projAsset k a) turn).getD (projAsset k a)).cell c) = k'.bal c a) :=
  ⟨recKExec_projAsset_commits_iff k turn a,
   fun k' h c => recKExec_projAsset_column_agrees k k' turn a h c⟩

/-! ## Axiom hygiene — every FFI-bridge keystone pinned to the three kernel axioms. -/
#assert_axioms projAsset_balOf
#assert_axioms recKExec_projAsset_gate_iff
#assert_axioms recKExec_projAsset_commits_iff
#assert_axioms recKExec_projAsset_column_agrees
#assert_axioms ffi_export_realises_settleRing_leg

end Dregg2.Intent.RingFFI
