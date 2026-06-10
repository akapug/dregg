/-
# Dregg2.Circuit.Spec.supplydestruction — INDEPENDENT full-state spec ⟺ executor for the
**supply-destruction** effect family (variant: `burnA`).

This is a LEAF module copying the proven reference pattern of `Dregg2/Circuit/Transfer.lean`
(`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`), but applied to the per-asset SUPPLY
BURN — the only `supply-destruction` constructor of `FullActionA`. It does NOT import or extend
Transfer.lean; it stands on its own over the SAME real executor (`Exec.execFullA` →
`Exec.recCBurnAsset` → `Exec.recKBurnAsset`, `TurnExecutorFull.lean`).

## What the executor ACTUALLY does (read from CODE, `TurnExecutorFull.lean`)

The dispatch arm (`execFullA`, line 3484) is

    | .burnA actor cell a amt   => recCBurnAsset s actor cell a amt

and the chained burn (`recCBurnAsset`, line 762) runs the kernel burn and, on success, prepends a
DISCLOSING receipt `{ actor := actor, src := cell, dst := cell, amt := -amt }` to the log:

    def recCBurnAsset (s) (actor cell) (a) (amt) : Option RecChainedState :=
      match recKBurnAsset s.kernel actor cell a amt with
      | some k' => some { kernel := k', log := { actor, src:=cell, dst:=cell, amt:=-amt } :: s.log }
      | none    => none

The kernel burn (`recKBurnAsset`, line 696) is the GATED debit of cell `cell`'s asset `a` on the
PER-ASSET ledger `bal` (a credit of `-amt`):

    def recKBurnAsset (k) (actor cell) (a) (amt) : Option RecordKernelState :=
      if mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a ∧ cell ∈ k.accounts
      then some { k with bal := recBalCredit k.bal cell a (-amt) }
      else none

## ⚑ DISCREPANCY with the task brief (REPORTED, not silently fixed)

The brief stated the guard as `supplyAuthB s.kernel.caps actor cell ∧ amt ≤ balOf(kernel.cell cell)
at asset a`, rewriting `kernel.bal (cell debited -amt at asset a)`. The REAL code (which this spec is
faithful to) differs on two points:

  1. **Authority predicate** = `mintAuthorizedB` (a `node`/`control` privileged-supply cap — the SAME
     gate the mint uses), NOT a separate `supplyAuthB` (no such symbol exists in the executor).
  2. **Availability slice** = `amt ≤ k.bal cell a` (the PER-ASSET ledger `bal`), NOT
     `balOf (k.cell cell)` (the legacy scalar `balance` FIELD of the cell record). The brief's
     "at asset a" is the ledger read; "balOf(kernel.cell cell)" is the wrong component — the burn
     touches `bal`, never the `cell` record.
  3. Guard also carries `0 ≤ amt` (non-negativity, no negative-burn inflation) — present in code,
     absent from the brief.

These are documentation drift in the brief, not executor bugs. The spec below is bound to the CODE.

## The spec ⟺ executor theorem (BOTH directions — the crown-jewel shape)

`BurnSpec s t s'` is the INDEPENDENT declarative full-state post-condition: the guard holds, the
post-ledger is EXACTLY `recBalCredit s.kernel.bal cell a (-amt)`, the log gets the disclosing receipt
prepended, and EVERY OTHER kernel field (the 16 non-`bal` components) is LITERALLY unchanged (the
FRAME). No frame clause mentions the executor. `recCBurnAsset_iff_spec` proves the executor meets it
EXACTLY, both ways — the `→` VALIDATES the executor against the spec (a silently-mutated field would
make the proof FAIL), the `←` reconstructs the committed state. `recBurn_ledger_correct` validates
the `recBalCredit` post-ledger helper declaratively (the analog of `recTransfer_correct`).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SupplyDestruction

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — The full admissibility guard the executor checks (the `recKBurnAsset` `if`).

Extracted as a `Prop` so the spec ⟺ executor proof is a clean re-assembly. This is the EXACT
conjunction in `recKBurnAsset` (`TurnExecutorFull.lean:698`): privileged-supply authority over the
burned cell, non-negativity (no negative-burn value inflation), per-asset availability (no
over-burn / supply cannot go below what the cell holds in that asset), and cell-liveness. -/
def BurnGuard (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Prop :=
  mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a ∧ cell ∈ k.accounts

/-- The disclosing burn receipt the chained executor prepends to the log (`recCBurnAsset`,
`TurnExecutorFull.lean:765`): a self-loop turn `cell→cell` disclosing the NEGATIVE moved amount. -/
def burnReceipt (actor cell : CellId) (amt : ℤ) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := -amt }

/-! ## §2 — `recKBurnAsset` commits IFF its guard holds (the kernel side, both directions). -/

/-- The kernel burn commits IFF its admissibility guard holds; and the committed post-kernel is then
the `recBalCredit … (-amt)` debit (other kernel fields preserved by the record update `{ k with … }`).
This pins the kernel arm so the chained spec is a clean lift. -/
theorem recKBurnAsset_iff_guard (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    (∃ k', recKBurnAsset k actor cell a amt = some k') ↔ BurnGuard k actor cell a amt := by
  unfold recKBurnAsset BurnGuard
  constructor
  · rintro ⟨k', h⟩
    by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
        ∧ cell ∈ k.accounts
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · intro hg; exact ⟨_, by rw [if_pos hg]⟩

/-! ## §3 — DECLARATIVE validation of the post-ledger helper `recBalCredit` (the `recTransfer_correct`
analog).

`recBalCredit bal cell a (-amt)` is the ONLY component the burn rewrites. We validate it DECLARATIVELY
(not trusting the helper blindly): a burn lowers cell `cell`'s asset `a` by exactly `amt`, and leaves
EVERY OTHER `(cell, asset)` ledger entry literally untouched. So the spec's
`s'.kernel.bal = recBalCredit …` clause genuinely encodes debit ∧ ledger-frame. -/
theorem recBurn_ledger_correct (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId) (amt : ℤ) :
    recBalCredit bal cell a (-amt) cell a = bal cell a - amt
    ∧ (∀ c b, ¬ (c = cell ∧ b = a) → recBalCredit bal cell a (-amt) c b = bal c b) := by
  refine ⟨?_, ?_⟩
  · simp only [recBalCredit, and_self, if_true]; ring
  · intro c b hcb; simp only [recBalCredit, if_neg hcb]

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor ⟺ spec.

`BurnSpec` is the COMPLETE declarative state transition of a committed `burnA`, written INDEPENDENTLY
of the executor (no `recKBurnAsset`/`recCBurnAsset` term in any frame clause). It enumerates:
  * the guard `BurnGuard` (admissibility),
  * the post-ledger `bal` (the SOLE rewritten component): exactly `recBalCredit … (-amt)`,
  * the log: the disclosing receipt prepended (the ONLY other rewritten component, in `RecChainedState`),
  * EVERY OTHER of the 16 non-`bal` kernel fields LITERALLY unchanged (the FRAME) —
    `accounts cell caps escrows nullifiers revoked commitments queues swiss slotCaveats factories
     lifecycle deathCert delegate delegations sealedBoxes`.

Missing ANY field reintroduces a ghost; all 17 kernel components (16 frozen + `bal` rewritten) plus
the `log` are enumerated. -/
def BurnSpec (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (s' : RecChainedState) : Prop :=
  BurnGuard s.kernel actor cell a amt
  -- the SOLE rewritten kernel component: the per-asset ledger is debited at (cell, a)
  ∧ s'.kernel.bal = recBalCredit s.kernel.bal cell a (-amt)
  -- the SOLE rewritten chained component: the disclosing receipt is prepended (newest-first)
  ∧ s'.log = burnReceipt actor cell amt :: s.log
  -- the FRAME: all 16 OTHER kernel fields LITERALLY unchanged
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.queues = s.kernel.queues
  ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-- **`recCBurnAsset_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The chained record
executor commits a per-asset burn into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The `→`
direction VALIDATES `recCBurnAsset` against the independent spec — all 17 kernel components + the log
are checked, so had the executor silently mutated `caps`/`nullifiers`/`escrows`/any frozen field the
frame clauses would make this proof FAIL; the `←` reconstructs the committed state from the spec.
This is the executor corner of the spec ⟺ executor ⟺ circuit triangle for `supply-destruction`. -/
theorem recCBurnAsset_iff_spec (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (s' : RecChainedState) :
    recCBurnAsset s actor cell a amt = some s' ↔ BurnSpec s actor cell a amt s' := by
  unfold recCBurnAsset BurnSpec
  -- expose the inner kernel burn `if`
  unfold recKBurnAsset
  by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ s.kernel.bal cell a
      ∧ cell ∈ s.kernel.accounts
  · rw [if_pos hg]
    simp only [BurnGuard]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      -- rebuild `s'` field-by-field from the spec; destruct both records to expose components
      obtain ⟨k', log'⟩ := s'
      obtain ⟨acc, cl, cps, nul, rev, com, bl, qs, sw, sc, fac, lc, dc, dlg, dlgs, sb, dge, dgea⟩ := k'
      simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      rfl
  · rw [if_neg hg]
    simp only [BurnGuard]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §5 — corollaries: the headline projections of the full spec (committed-form). -/

/-- **`recCBurnAsset_commits_iff_guard`** — the chained burn commits IFF the guard holds (the
admissibility-only projection of the full spec). -/
theorem recCBurnAsset_commits_iff_guard (s : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) :
    (∃ s', recCBurnAsset s actor cell a amt = some s') ↔ BurnGuard s.kernel actor cell a amt := by
  constructor
  · rintro ⟨s', h⟩; exact ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1
  · intro hg
    obtain ⟨k', hk⟩ := (recKBurnAsset_iff_guard s.kernel actor cell a amt).mpr hg
    exact ⟨_, by unfold recCBurnAsset; rw [hk]⟩

/-- **`recCBurnAsset_debits`** — a committed burn debits cell `cell`'s asset `a` by exactly `amt`,
read off the full spec + the declarative ledger-helper validation. The conserved-slice projection
(supply of `a` falls by `amt`). -/
theorem recCBurnAsset_debits {s s' : RecChainedState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recCBurnAsset s actor cell a amt = some s') :
    s'.kernel.bal cell a = s.kernel.bal cell a - amt := by
  have hspec := (recCBurnAsset_iff_spec s actor cell a amt s').mp h
  rw [hspec.2.1]
  exact (recBurn_ledger_correct s.kernel.bal cell a amt).1

/-- **`recCBurnAsset_other_ledger_untouched`** — a committed burn leaves EVERY OTHER `(cell, asset)`
ledger entry untouched (the ledger-frame projection: only the burned slot moves). -/
theorem recCBurnAsset_other_ledger_untouched {s s' : RecChainedState} {actor cell : CellId}
    {a : AssetId} {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s')
    (c : CellId) (b : AssetId) (hcb : ¬ (c = cell ∧ b = a)) :
    s'.kernel.bal c b = s.kernel.bal c b := by
  have hspec := (recCBurnAsset_iff_spec s actor cell a amt s').mp h
  rw [hspec.2.1]
  exact (recBurn_ledger_correct s.kernel.bal cell a amt).2 c b hcb

/-- **`recCBurnAsset_no_negative_burn`** — fail-closed: a committed burn carries `0 ≤ amt`. So no
"negative burn" can inflate the supply through this arm (it would be a mint in disguise). -/
theorem recCBurnAsset_no_negative_burn {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') : 0 ≤ amt :=
  ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1.2.1

/-- **`recCBurnAsset_no_overburn`** — fail-closed: a committed burn carries `amt ≤ bal cell a`. So the
cell's asset-`a` holding cannot be driven negative by a burn (no over-destruction). -/
theorem recCBurnAsset_no_overburn {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') : amt ≤ s.kernel.bal cell a :=
  ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1.2.2.1

/-- **`recCBurnAsset_authorized`** — fail-closed: a committed burn carries privileged-supply
(`mintAuthorizedB`) authority over the burned cell. An unauthorized actor cannot destroy supply. -/
theorem recCBurnAsset_authorized {s s' : RecChainedState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recCBurnAsset s actor cell a amt = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true :=
  ((recCBurnAsset_iff_spec s actor cell a amt s').mp h).1.1

/-! ## §6 — executor-dispatch form: the SAME truths through `execFullA (.burnA …)`.

`execFullA s (.burnA actor cell a amt) = recCBurnAsset s actor cell a amt` definitionally
(`TurnExecutorFull.lean:3484`), so the full spec ⟺ holds through the top-level dispatch unchanged —
this is the `supply-destruction` arm of `execFullA` validated against its independent spec. -/

/-- **`execFullA_burnA_iff_spec` — the dispatch-level spec ⟺ executor.** Through the top-level
`execFullA` dispatch on `.burnA`, committing the turn into `s'` is EXACTLY `BurnSpec`. -/
theorem execFullA_burnA_iff_spec (s : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (s' : RecChainedState) :
    execFullA s (.burnA actor cell a amt) = some s' ↔ BurnSpec s actor cell a amt s' := by
  show recCBurnAsset s actor cell a amt = some s' ↔ BurnSpec s actor cell a amt s'
  exact recCBurnAsset_iff_spec s actor cell a amt s'

/-! ## §7 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recKBurnAsset_iff_guard
#assert_axioms recBurn_ledger_correct
#assert_axioms recCBurnAsset_iff_spec
#assert_axioms recCBurnAsset_commits_iff_guard
#assert_axioms recCBurnAsset_debits
#assert_axioms recCBurnAsset_other_ledger_untouched
#assert_axioms recCBurnAsset_no_negative_burn
#assert_axioms recCBurnAsset_no_overburn
#assert_axioms recCBurnAsset_authorized
#assert_axioms execFullA_burnA_iff_spec

end Dregg2.Circuit.Spec.SupplyDestruction
