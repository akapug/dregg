/-
# Dregg2.Circuit.Emit.EffectVmEmitBurn — the SUPPLY-BURN effect `burnA`, EMITTED onto the runnable
  EffectVM `bal_lo` (balance) column, with its full-state per-cell soundness, the anti-ghost
  commitment tooth, and the connector to the validated universe-A `BurnSpec` / `recCBurnAsset`.

## The "ONE circuit" thesis for `burnA` (a balance/field effect — the closest clone of transfer)

`burnA` is the per-asset privileged-supply BURN (`Inst/burnA.lean`, `Spec/supplydestruction.lean`):
the executor DEBITS the per-asset ledger `bal` at one `(cell, asset)` by `amt` (`recBalCredit … (-amt)`),
prepends a disclosing receipt, and freezes the 16 non-`bal` kernel fields. Its validation
`burnA_full_sound ⇒ BurnSpec` is DONE; this module emits the SAME effect onto the running EffectVM row
layout and welds the two — ONE circuit description, not a parallel spec.

The EffectVM state block carries ONE cell's conserved balance as the `bal_lo` limb (state offset 0,
`state.BALANCE_LO`). The running prover absorbs it into the GROUP-4 state-commitment chain
(`site0` reads `saCol BALANCE_LO`). So at the row level a burn is a `bal_lo` COLUMN DEBIT: the
post-`bal_lo` is the pre value MINUS the burn `amount`, every OTHER state column frozen, and the
post-state bound into the published `state_commit` under Poseidon2 collision-resistance.

`burnVmDescriptor` emits exactly that. The debit gate is `new_bal_lo - old_bal_lo + amount = 0`
(`new = old - amt`), the rest of the block (bal_hi / nonce / 8 fields / cap_root / reserved) is frozen
by passthrough gates, and the 4 GROUP-4 hash-sites bind the whole post-state into `state_commit`.

## What is PROVED here

  * `burnVm_faithful` — on a burn row the emitted per-row gates hold IFF `BurnRowIntent` (`bal_lo`
    debited by `amount`, frame frozen).
  * `burnDescriptor_full_sound` — satisfying the WHOLE descriptor under the `RowEncodes` decoding
    forces the structured per-cell `CellBurnSpec pre amt post` (debit + full frame freeze) AND
    publishes `post.commit = PI[NEW_COMMIT]`.
  * `burnDescriptor_commit_binds_state` — the KEYSTONE anti-ghost: two satisfying rows agreeing on the
    published `NEW_COMMIT` have IDENTICAL absorbed after-state columns (reusing the transfer keystone's
    `transferDescriptor_commit_binds_state`, since the hash sites are the SAME GROUP-4 chain).
  * `unify_burn` / `unify_burn_exec` — the CONNECTOR: a committed universe-A `BurnSpec` (= `recCBurnAsset`),
    projected per-`(cell, asset)` through `cellProjA`, satisfies `CellBurnSpec` EXACTLY (the conserved
    `bal cell a` drops by `amt`; the frame is `0 = 0`). So the runnable `bal_lo` column transition IS
    universe-A's `bal`-ledger transition, NOT a fourth spec.

## BOUNDARY (precise — do NOT over-read)

  * PER-CELL / PER-ROW. Single-row AIR: ONE `(cell, asset)` ledger entry's debit + its binding into the
    published `state_commit`. Cross-row composition (and the disclosing log receipt) is the turn layer
    (`TurnEmit`), cited not claimed.
  * The EffectVM row's `bal_lo` is a BARE limb; which `(cell, asset)` ledger entry it is comes from the
    `cellProjA` encoding choice, not a row gate. The AUTHORITY / non-negativity / availability / liveness
    GUARD of `recKBurnAsset` (`BurnGuard`) has no row column; it lives in universe-A's spec (cited).
  * NONCE DIVERGENCE: the EffectVM block carries a `nonce` column, and the burn descriptor FREEZES it
    (`gNonceFix`). Universe-A's burn touches ONLY `bal` (the cell record's `nonce` survives), so the
    descriptor's nonce-freeze MATCHES the executor (no divergence for burn — unlike transfer, which ticks
    the row nonce). Stated as `CellBurnSpec`'s nonce-freeze clause and proved against the executor.
  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone);
    pinned only by its per-row passthrough gate.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. No `sorry`, no `:= True`, no `native_decide`, no
`rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.supplydestruction

namespace Dregg2.Circuit.Emit.EffectVmEmitBurn

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites site0 site1 site2 site3 boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols transferDescriptor_commit_binds_state)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SupplyDestruction

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the burn effect row.

The running EffectVM lays one selector per effect (`columns.rs::NUM_EFFECTS = 54`); `burnA` has its own
selector index `sel.BURN`. The burn `amount` rides the SAME `param.AMOUNT` column transfer uses (offset 0).
On a genuine burn row the burn selector is `1` and `s_noop = 0`. -/

namespace selB
/-- The `burnA` effect selector column (the running prover's per-effect selector, `sel::BURN`). -/
def BURN : Nat := 46
end selB

/-- The `burnA` selector as an expression. -/
def eSelBurn : EmittedExpr := .var selB.BURN

/-! ### Burn parameter column (the running trace generator's convention).

`generate_effect_vm_trace` lays the burn row's params as `param0 = target_hash`,
`param1 = amount_lo` (the burn amount), `param2 = was_burn_flag` — see `columns.rs::param::BURN_*`
and the `Effect::Burn` arm of `trace.rs`. The hand-AIR's burn debit gate reads `prm(param::BURN_AMOUNT_LO)`
= param column **1**, NOT the transfer `param.AMOUNT` (= column 0, which carries the target hash on a
burn row). The descriptor MUST read the same column or it debits the wrong value (UNSAT on the honest
trace). -/
namespace param
/-- Burn amount lives at param column 1 (`columns.rs::param::BURN_AMOUNT_LO`). -/
def BURN_AMOUNT_LO : Nat := 1
end param

/-- Burn amount as an expression (param column 1). -/
def ePrmBurnAmt : EmittedExpr := .var (prmCol param.BURN_AMOUNT_LO)

/-! ## §1 — The burn row gates (term-for-term the running prover's, specialized to the row).

A burn DEBITS `bal_lo` by `amount` (read from `param1`, the trace-generator convention) and FREEZES
the rest of the block EXCEPT the nonce. As with EVERY non-NoOp EffectVM row, the running prover's
GLOBAL nonce gate ticks the row nonce by one (`new_nonce − old_nonce − (1 − s_noop) = 0`); the burn
row is non-NoOp, so it TICKS. (This is the per-cell runtime SEQUENCE counter, a distinct object from
universe-A's frozen ledger-entry nonce — see §7's connector, which reports the gap exactly as the
transfer keystone does.) -/

/-- Balance-lo DEBIT body: `new_bal_lo - old_bal_lo + amount` (so `new = old - amount`), reading the
burn amount from `param1` (the trace-generator + hand-AIR convention). -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmBurnAmt

/-- Balance-hi freeze body: `new_bal_hi - old_bal_hi`. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)

/-- Nonce TICK body (the running prover's global non-NoOp invariant): `new_nonce − old_nonce − (1 − s_noop)`.
On a burn row `s_noop = 0`, so this is `new_nonce − old_nonce − 1` (tick). Reused verbatim from the
transfer template (`gNonce`). -/
def gNonceTick : EmittedExpr := gNonce

/-- Cap-root passthrough body: `new_cap_root - old_cap_root`. -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)

/-- Reserved passthrough body: `new_reserved - old_reserved`. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` passthrough body: `field_after[i] - field_before[i]`. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-passthrough gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The burn-specialized per-row gates (balance debit, hi/cap/reserved freeze, nonce TICK, 8 fields freeze). -/
def burnRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHiFix, .gate gNonceTick, .gate gCapFix, .gate gResFix ]
  ++ gFieldFixAll

/-! ## §2 — The emitted BURN descriptor.

Per-row gates ++ transition continuity ++ the 7 boundary PI pins (reused from transfer), with the 4
ordered GROUP-4 hash sites and the balance-limb range checks. -/

/-- The burn AIR identity. -/
def burnVmAirName : String := "dregg-effectvm-burn-v1"

/-- **`burnVmDescriptor`** — the `burnA` effect's full concrete circuit, emitted through the EffectVM
IR: the per-row debit/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4
ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def burnVmDescriptor : EffectVmDescriptor :=
  { name := burnVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := burnRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates selB.BURN
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The BURN ROW INTENT (the independent faithfulness target).

`BurnRowIntent` is the field-level burn move written from protocol intent (NOT the gate bodies): on a
burn row, `bal_lo` drops by `amount`, the hi limb / nonce / cap_root / reserved / 8 fields are FIXED.
This is the EffectVM-row projection of `BurnSpec`'s `recBalCredit … (-amt)` debit, restricted to the
single ledger entry the row carries. -/

/-- **`BurnRowIntent env`** — the intended burn move on the row `env.loc`: `bal_lo` debited by the
`param1` amount, balHi/cap/reserved/8 fields frozen, and the runtime nonce TICKED by one (the per-cell
sequence counter — distinct from universe-A's frozen ledger nonce; see the §7 connector). -/
def BurnRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a burn row: `s_burn = 1`, `s_noop = 0`. The `s_noop = 0` clause is what the global
nonce-tick gate factors on (a burn row is non-NoOp, so the nonce ticks). -/
def IsBurnRow (env : VmRowEnv) : Prop :=
  env.loc selB.BURN = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`burnVm_faithful`.** On a burn row, the emitted descriptor's per-row gates hold IFF the burn
intent holds. The gate bodies are the running prover's polynomials (specialized to the burn row), and
they pin EXACTLY the intent move. -/
theorem burnVm_faithful (env : VmRowEnv) (hrow : IsBurnRow env) :
    (∀ c ∈ burnRowGates, c.holdsVm env false false) ↔ BurnRowIntent env := by
  obtain ⟨_hsB, hsN⟩ := hrow
  unfold burnRowGates gFieldFixAll BurnRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHiFix, gNonceTick, gNonce, gCapFix, gResFix,
      ePrmBurnAmt, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmBurnAmt, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **Anti-ghost (balance tamper).** A burn row whose post-`bal_lo` is NOT the debit `old - amount`
fails the `gBalLoDebit` gate (UNSAT). -/
theorem burnVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BURN_AMOUNT_LO)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmBurnAmt, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith [h]

/-! ## §5 — `CellBurnSpec` + `RowEncodes` → the structured per-cell soundness.

`CellBurnSpec pre amt post` is the per-cell FULL-state spec: `bal_lo` debited by `amt`, EVERY other
block component (balHi/nonce/8 fields/capRoot/reserved) LITERALLY frozen. `RowEncodes` decodes the row's
state-block columns into concrete `CellState` records. -/

/-- The per-cell burn spec (EffectVM-row image): balLo drops by `amt`, balHi/8-fields/cap/reserved
frozen, and the runtime nonce TICKS by one (the per-cell sequence counter). The universe-A connector
in §7 reconciles this tick against the FROZEN ledger nonce via `CellBurnSpecFrozenNonce`, exactly as
the transfer keystone reconciles its row nonce-tick. -/
def CellBurnSpec (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo - amt
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- `RowEncodes env pre amt post` — the row's `state_before`/`amount`/`state_after` columns decode to
`pre`/`amt`/`post` (column-by-column), plus the published OLD/NEW commitments. -/
def RowEncodes (env : VmRowEnv) (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.BURN_AMOUNT_LO) = amt
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- Under `RowEncodes`, `BurnRowIntent` IS the structured per-cell spec. -/
theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post) (hint : BurnRowIntent env) :
    CellBurnSpec pre amt post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - env.loc (prmCol param.BURN_AMOUNT_LO) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; have := hfld i.val i.isLt; rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ### The descriptor's per-row gates are a sub-list whose `holdsVm` is flag-independent. -/

/-- The per-row gates hold under any flags iff they hold under `(false, false)` (all are `.gate _`). -/
theorem burnRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ burnRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ burnRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold burnRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- **`burnDescriptor_full_sound`.** Satisfying the WHOLE descriptor under `RowEncodes` forces the
structured per-cell `CellBurnSpec` AND publishes `post.commit = PI[NEW_COMMIT]`. -/
theorem burnDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post)
    (hsat : satisfiedVm hash burnVmDescriptor env true true) :
    CellBurnSpec pre amt post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hgates : ∀ c ∈ burnRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold burnVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hgates' := burnRowGates_flag_indep env true true hgates
  have hint := (burnVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellSpec env pre post amt henc hint, ?_⟩
  -- last-row boundary pin: state_after.state_commit = PI[NEW_COMMIT]
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ burnVmDescriptor.constraints := by
      unfold burnVmDescriptor; simp only [List.mem_append]; exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — THE ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone).

`burnVmDescriptor` carries the SAME GROUP-4 `transferHashSites`, so the transfer keystone's
`transferDescriptor_commit_binds_state` applies verbatim once we reduce `satisfiedVm burnVmDescriptor`
to its hash-site component. Two satisfying burn rows that agree on the published `NEW_COMMIT` agree on
their WHOLE absorbed after-state. -/

/-- The descriptor's hash-site component is the transfer GROUP-4 chain. -/
theorem burn_sites_eq : burnVmDescriptor.hashSites = transferHashSites := rfl

/-- **`burnDescriptor_commit_binds_state` — THE KEYSTONE anti-ghost tooth for burn.** Under
`Poseidon2SpongeCR hash`, two rows satisfying the burn descriptor's hash-sites and publishing the SAME
`NEW_COMMIT` have IDENTICAL absorbed after-state columns. So a prover CANNOT keep `NEW_COMMIT` while
tampering any absorbed cell. (Proof reuses the transfer keystone — the hash chain is identical.) -/
theorem burnDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjA` to universe-A's `BurnSpec` / `recCBurnAsset`.

`cellProjA k c a` reads ONE `(cell, asset)` ledger entry of the real record-kernel state into the
keystone's `CellState`: `balLo` = the conserved `bal c a` measure (the SAME measure `recBalCredit` moves),
everything else `0` (universe-A's burn touches no high-limb / nonce / field-array / cap-root / reserved on
the ledger entry — all FROZEN). `commit` (the digest output) is `0`. -/

/-- Project ledger entry `(c, a)` of `k` into the keystone's `CellState` (balLo = `bal c a`; rest `0`). -/
def cellProjA (k : RecordKernelState) (c : CellId) (a : AssetId) : CellState where
  balLo    := k.bal c a
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-! ### The ONE genuine divergence (mirroring the transfer keystone): the EffectVM row TICKS the
runtime nonce; universe-A's burn FREEZES the ledger-entry nonce.

`CellBurnSpec` demands `post.nonce = pre.nonce + 1` (the runtime per-cell sequence counter the
EffectVM row increments on every non-NoOp effect, matching the validated hand-AIR's global nonce
gate). Universe-A's `recCBurnAsset` touches ONLY the `bal` ledger — the projected entry's nonce is
`0` before AND after (`cellProjA` sets it to `0`). So the executor's per-entry image is the
nonce-FREEZE variant. We unify against THAT and report the nonce-tick gap exactly as
`EffectVmEmitTransferUnify` does (`exec_nonce_is_frozen_not_ticked`). -/

/-- The executor's genuine per-entry image: `CellBurnSpec` with the nonce-TICK replaced by
nonce-FREEZE. Every other clause (balLo debit, balHi/fields/capRoot/reserved freeze) is identical. -/
def CellBurnSpecFrozenNonce (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo - amt
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce          -- FROZEN (executor ledger image) — keystone instead demands `+ 1`
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- **`unify_burn` — THE UNIFICATION (frozen-nonce variant).** A committed universe-A burn
(`BurnSpec`), projected onto the burned `(cell, asset)` entry under `cellProjA`, satisfies the
keystone's per-cell `CellBurnSpecFrozenNonce` EXACTLY: the conserved `bal cell a` drops by `amt`;
balHi/nonce/fields/capRoot/reserved are `0 = 0` (frozen). So the executor's per-entry effect IS the
keystone's frozen-nonce spec, NOT a fourth spec. -/
theorem unify_burn (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec s actor cell a amt s') :
    CellBurnSpecFrozenNonce (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal cell a = s.kernel.bal cell a - amt
  rw [hspec.2.1]
  exact (recBurn_ledger_correct s.kernel.bal cell a amt hspec.1.2.2.2.2.2).1

/-- **`unify_burn_well` — THE WELL LEG (W1).** The SAME committed burn, projected onto the ISSUER's
well `(a, a)`, satisfies the frozen-nonce spec with the NEGATED amount: the well RISES by exactly
`amt` (the burned value RETURNS to the well — supply shrinks). Holder `−amt` (above) and well
`+amt` (here) are the two rows of ONE return-to-well move — exact conservation at row level. -/
theorem unify_burn_well (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec s actor cell a amt s') :
    CellBurnSpecFrozenNonce (cellProjA s.kernel a a) (-amt) (cellProjA s'.kernel a a) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal a a = s.kernel.bal a a - (-amt)
  rw [hspec.2.1]
  have := (recBurn_ledger_correct s.kernel.bal cell a amt hspec.1.2.2.2.2.2).2.1
  omega

/-- **`unify_burn_exec` — same, stated against the executor directly.** A committed
`recCBurnAsset s actor cell a amt = some s'` (the REAL record-kernel transition) projects per-entry to
the keystone's `CellBurnSpecFrozenNonce` on the burned `(cell, asset)`. -/
theorem unify_burn_exec (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recCBurnAsset s actor cell a amt = some s') :
    CellBurnSpecFrozenNonce (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) :=
  unify_burn s s' actor cell a amt ((recCBurnAsset_iff_spec s actor cell a amt s').mp h)

/-- **`exec_nonce_is_frozen_not_ticked` — the nonce-tick gap, named precisely.** The executor's
projected burned-entry nonce is FROZEN (`0 = 0`), whereas the EffectVM row's `CellBurnSpec` TICKS it
(`pre.nonce + 1`). The two agree on the burned entry iff `0 = 0 + 1`, which is FALSE — so the gap is
pinned to exactly the nonce column (the EffectVM-row nonce being a runtime sequence counter, NOT the
universe-A ledger nonce). -/
theorem exec_nonce_is_frozen_not_ticked (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (h : recCBurnAsset s actor cell a amt = some s') :
    (cellProjA s'.kernel cell a).nonce = (cellProjA s.kernel cell a).nonce :=
  (unify_burn_exec s s' actor cell a amt h).2.2.1

/-- **`descriptor_agrees_with_executor` — THE per-cell circuit⟺executor agreement (modulo the
nonce-tick gap).** Suppose (a) the RUNNABLE descriptor is satisfied on a genuine burn row and its
`RowEncodes` decoding names `(pre, amt, post)` with `pre = cellProjA s.kernel cell a`, AND (b) the REAL
executor commits `recCBurnAsset s actor cell a amt = some s'`. Then the descriptor's pinned post-state
agrees with the executor's burned-entry post-state on EVERY conserved/frame clause: the debited balLo,
the frozen balHi/fields/capRoot/reserved. The ONE divergence is the nonce (descriptor ticks the runtime
counter; executor freezes the ledger entry — `exec_nonce_is_frozen_not_ticked`), reported, not papered. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hsat : satisfiedVm hash burnVmDescriptor env true true)
    (hexec : recCBurnAsset s actor cell a amt = some s') :
    post.balLo = (cellProjA s'.kernel cell a).balLo
    ∧ post.balHi = (cellProjA s'.kernel cell a).balHi
    ∧ (∀ i, post.fields i = (cellProjA s'.kernel cell a).fields i)
    ∧ post.capRoot = (cellProjA s'.kernel cell a).capRoot
    ∧ post.reserved = (cellProjA s'.kernel cell a).reserved := by
  obtain ⟨hcirc, _⟩ :=
    burnDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post amt henc hsat
  obtain ⟨hcLo, hcHi, _hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _heN, heF, heCap, heRes⟩ := unify_burn_exec s s' actor cell a amt hexec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §8 — NON-VACUITY: a concrete burn that the descriptor accepts; one it rejects.

`goodBurnRow` debits cell's `bal_lo` 100 → 70 by `amount = 30` (read from `param1`, the trace-generator
column), nonce ticks `5 → 6`, frame frozen. It realizes the intent. `badBurnRow` forges the post-`bal_lo`
to 999 ≠ 70 — the `gBalLoDebit` gate rejects it. -/

/-- A concrete burn row: selector `sel::BURN`, `bal_lo 100 → 70`, `amount = 30` at `param1`, frame
fixed at `0`, nonce 5 → 6 (TICK). -/
def goodBurnRow : VmRowEnv where
  loc := fun v =>
    if v = selB.BURN then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 70
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.BURN_AMOUNT_LO then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodBurnRow` is a genuine burn row (`s_burn = 1`, `s_noop = 0`). -/
theorem goodBurnRow_isBurnRow : IsBurnRow goodBurnRow := by
  unfold IsBurnRow goodBurnRow
  refine ⟨by norm_num [selB.BURN], ?_⟩
  -- s_noop = 0: col 0 is not the selector (46), nor any of the named columns.
  norm_num [sel.NOOP, selB.BURN, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
    param.BURN_AMOUNT_LO]

/-- **NON-VACUITY (witness TRUE).** `goodBurnRow` REALIZES the burn intent: `bal_lo 100 → 70 = 100 - 30`,
nonce ticks `5 → 6`, frame frozen. So the faithfulness biconditional's intent side is inhabited. -/
theorem goodBurnRow_realizes_intent : BurnRowIntent goodBurnRow := by
  unfold BurnRowIntent goodBurnRow
  simp only [sbCol, saCol, prmCol, selB.BURN, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.BURN_AMOUNT_LO]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 46) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 69) = False := by simp; omega
  have f1 : (54 + (3 + i) = 46) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 69) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED burn row: `goodBurnRow` with post-`bal_lo` tampered to `999 ≠ 70`. -/
def badBurnRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodBurnRow.loc v
  nxt := goodBurnRow.nxt
  pub := goodBurnRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badBurnRow`'s post-`bal_lo` is NOT the
debit, so `gBalLoDebit` REJECTS it — a concrete UNSAT. -/
theorem badBurnRow_rejected : ¬ (VmConstraint.gate gBalLoDebit).holdsVm badBurnRow false false := by
  apply burnVm_rejects_wrong_balance
  simp only [badBurnRow, goodBurnRow, sbCol, saCol, prmCol, selB.BURN, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.BURN_AMOUNT_LO]
  norm_num

/-! ## §8½ — THE CLASS-A CAPSTONE (per-cell, the transfer bar exactly).

burn's whole per-cell transition is the `bal_lo` DEBIT + the frozen frame — every state-block column
moved-or-frozen, ALL 13 absorbed into `state_commit` (anti-ghosted via the keystone), unified to the
verified executor (`recCBurnAsset`). This capstone bundles the corners into ONE class-A statement, the
shape transfer has. The ONE residual — the *global supply total* — is a CROSS-CELL / TURN-LEVEL
accumulator (burn changes total supply, carried by no single cell), the exact analogue of transfer's
two-sided conservation the keystone assigns to the turn layer. So burn meets the per-cell class-A bar;
the supply-total invariant is a turn property (cited). NOTE: the per-cell agreement here is the 5-clause
(bal/frame) one — burn TICKS the nonce on the row but `recCBurnAsset` freezes the projected entry's
nonce (the named `exec_nonce_is_frozen_not_ticked` divergence, off-universe-A like transfer's nonce). -/

/-- **`burnDescriptor_classA` — the per-cell class-A capstone.** Satisfying the runnable descriptor on a
burn row, for the burned `(cell, asset)` entry of a committed `recCBurnAsset`, forces the FULL per-cell
`CellBurnSpec` (bal_lo debited by `amt`, frame frozen), the published commit, AND agreement with the
executor's per-cell post-state on the bal/frame clauses. -/
theorem burnDescriptor_classA (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBurnRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hsat : satisfiedVm hash burnVmDescriptor env true true)
    (hexec : recCBurnAsset s actor cell a amt = some s') :
    CellBurnSpec (cellProjA s.kernel cell a) amt post
    ∧ post.commit = env.pub pi.NEW_COMMIT
    ∧ post.balLo = (cellProjA s'.kernel cell a).balLo
    ∧ post.balHi = (cellProjA s'.kernel cell a).balHi
    ∧ (∀ i, post.fields i = (cellProjA s'.kernel cell a).fields i)
    ∧ post.capRoot = (cellProjA s'.kernel cell a).capRoot
    ∧ post.reserved = (cellProjA s'.kernel cell a).reserved := by
  obtain ⟨hspec, hcommit⟩ :=
    burnDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post amt henc hsat
  obtain ⟨hLo, hHi, hF, hCap, hRes⟩ :=
    descriptor_agrees_with_executor hash env hrow s s' actor cell a amt post henc hsat hexec
  exact ⟨hspec, hcommit, hLo, hHi, hF, hCap, hRes⟩

/-! ## §9 — Axiom-hygiene tripwires. -/

#assert_axioms burnDescriptor_classA

#guard burnVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1  -- gates(5+8) + transitions + 4 + 3 + selectorGate
#guard burnVmDescriptor.hashSites.length == 4
#guard burnVmDescriptor.traceWidth == 187

#assert_axioms burnVm_faithful
#assert_axioms burnVm_rejects_wrong_balance
#assert_axioms intent_to_cellSpec
#assert_axioms burnRowGates_flag_indep
#assert_axioms burnDescriptor_full_sound
#assert_axioms burnDescriptor_commit_binds_state
#assert_axioms unify_burn
#assert_axioms unify_burn_well
#assert_axioms unify_burn_exec
#assert_axioms exec_nonce_is_frozen_not_ticked
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodBurnRow_isBurnRow
#assert_axioms goodBurnRow_realizes_intent
#assert_axioms badBurnRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitBurn
