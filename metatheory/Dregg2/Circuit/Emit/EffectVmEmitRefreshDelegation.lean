/-
# Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation — the REFRESH-DELEGATION effect `refreshDelegationA`
  on the runnable EffectVM row, with its SUPPORTED (frame-freeze) full-state soundness and a LOUD
  IR-BLOCKED flag for the genuinely-touched `delegations` sub-table (no EffectVM column).

## ⚠ IR-BLOCKED — `refreshDelegationA` touches `delegations`, which has NO EffectVM state column

`refreshDelegationA` (`Inst/refreshDelegationA.lean`) is the ONE cap-graph effect of this group that
does NOT touch `caps`. It touches the `delegations` field — a `CellId → List Cap` WHOLE-FUNCTION sub-
table — predicted post value `refreshDelegationsMap kernel child` (re-derive the child's parent-clist
delegation snapshot), and FREEZES every OTHER kernel field, INCLUDING `caps` (`RefreshDelegationSpec`'s
clause `s'.kernel.caps = s.kernel.caps`). Its validation `refreshDelegationA_full_sound ⇒
RefreshDelegationSpec` is DONE in universe A.

The running EffectVM state block (`EffectVmEmit.state`) carries `cap_root` (offset 11, the `caps`
digest), the balance limbs, the nonce, 8 generic field columns, `reserved`, and `state_commit`. It has
**NO `delegations_root` column** — the `delegations` sub-table is digested NOWHERE in the EffectVM row.
So the genuine `refreshDelegationA` move (`delegations := refreshDelegationsMap …`) is **not expressible
as an EffectVM column transition**. This is a REAL IR GAP, flagged loudly, NOT papered:

  * **NEEDS IR EXTENSION: a `delegations_root` state column + its hash-site.** To pin
    `refreshDelegationA`'s actual content in-circuit, the EffectVM state block would need a 15th data
    column `delegations_root := D_delegations(kernel.delegations)`, absorbed by a GROUP-4 hash site, with
    a MOVE gate `new_delegations_root = D(refreshDelegationsMap …)`. Until that IR extension lands, the
    `delegations` move rides ONLY universe-A's `refreshDelegationA_full_sound` (its `funcComponent
    (·.delegations) D hD` digest, the `Function.Injective D` portal), with NO runnable-row counterpart.

## What this module DOES prove (the SUPPORTED part — the frame-freeze the row CAN express)

`refreshDelegationA` FREEZES every EffectVM state column (its only moved field, `delegations`, has no
column, so at the EffectVM layer it is a pure FRAME-FREEZE row: `cap_root`, balance, nonce, fields,
reserved all `after = before`). We emit that runnable frame-freeze row (`refreshVmDescriptor`), prove it
pins the FULL per-cell freeze (`RefreshRowIntent` ⟺ gates; structured `RefreshCellSpec`), bind the frozen
post-state into `state_commit` (the keystone commitment tooth, reused), and CONNECT the part the row CAN
witness — the `caps`-FREEZE clause — to universe-A's `RefreshDelegationSpec` (`unify_refresh_capFreeze`):
a committed refresh leaves `cap_root` exactly as it was, which the runnable row's `cap_root` passthrough
gate pins. The `delegations` move is reported as the IR-blocked remainder.

## HONEST BOUNDARY (precise)

  * **PARTIAL — IR-BLOCKED on the touched field.** The runnable row pins the FRAME-FREEZE (incl. the
    `caps`/`cap_root` freeze `RefreshDelegationSpec` genuinely asserts) but does NOT witness the
    `delegations := refreshDelegationsMap …` move (no EffectVM column). That move is universe-A's, carried
    by `refreshDelegationA_full_sound` + `Function.Injective D` over `delegations`.

  * **The `RefreshDelegationGuard` (the actor-authorizes-child premise) is NOT a row gate.** It is
    enforced by `refreshDelegationA_full_sound`'s `propBit (RefreshDelegationGuard)` column, carried
    through the hypothesis of `unify_refresh_capFreeze_via_full_sound`.

  * `state.RESERVED` not commitment-bound (inherited finding); PER-CELL / PER-ROW.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
the `delegations` digest ONLY as universe-A's `Function.Injective D` (not claimed in-row). No
`sorry`/`:= True`/`native_decide`/rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.refreshDelegationA

namespace Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub gCapPass site0 site1 site2 site3 transitionAll boundaryFirstPins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.RefreshDelegationA (RefreshDelegationArgs refreshDelegationE refreshDelegationA_full_sound)
open Dregg2.Circuit.Spec.RefreshDelegation (RefreshDelegationSpec refreshDelegationsMap)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the refresh row. -/

namespace selR
/-- The `refreshDelegationA` effect selector column (the running prover's per-effect selector). -/
def REFRESH : Nat := 3
end selR

/-! ## §1 — The frame-freeze row gates (the SUPPORTED part: every EffectVM state column frozen).

`refreshDelegationA` moves only `delegations` (no EffectVM column), so at the EffectVM layer it FREEZES
every state column. The gate set is `cap_root`/`balance`/`nonce`/`reserved`/`fields` ALL passthrough. -/

/-- Balance-lo freeze: `new_bal_lo - old_bal_lo`. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze: `new_bal_hi - old_bal_hi`. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze: `new_nonce - old_nonce` (refresh does not tick the cell nonce). -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
/-- Reserved freeze: `new_reserved - old_reserved`. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
/-- Field-`i` freeze: `field_after[i] - field_before[i]`. -/
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint := (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The frame-freeze per-row gates: cap_root passthrough (`gCapPass`, reused from transfer) + balance/
nonce/reserved freeze + 8 fields freeze. The whole EffectVM state block is `after = before`. -/
def refreshRowGates : List VmConstraint :=
  [ .gate gCapPass, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix, .gate gResFix ] ++ gFieldFixAll

/-! ## §2 — The emitted descriptor. -/

/-- The `refreshDelegationA` AIR identity. -/
def refreshVmAirName : String := "dregg-effectvm-refreshDelegation-v1"

/-- **`refreshVmDescriptor`** — the runnable `refreshDelegationA` FRAME-FREEZE row: every EffectVM state
column frozen ++ transition continuity ++ the row-0 boundary pins, with the 4 ordered GROUP-4 hash sites
(binding the frozen post-state). The genuine `delegations` move is NOT here (no column — §IR-BLOCKED). -/
def refreshVmDescriptor : EffectVmDescriptor :=
  { name := refreshVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := refreshRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := transferHashSites
  , ranges := [] }

/-! ## §3 — The frame-freeze ROW INTENT + faithfulness. -/

/-- **`RefreshRowIntent env`** — every EffectVM state column is frozen (`after = before`): the SUPPORTED
content of a refresh row (its only moved field, `delegations`, has no column). -/
def RefreshRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- **`refreshVm_faithful`** — on a refresh row, the emitted frame-freeze gates all hold IFF
`RefreshRowIntent` holds. The gate bodies are the running prover's passthrough polynomials. -/
theorem refreshVm_faithful (env : VmRowEnv) :
    (∀ c ∈ refreshRowGates, c.holdsVm env false false) ↔ RefreshRowIntent env := by
  unfold refreshRowGates gFieldFixAll RefreshRowIntent
  constructor
  · intro h
    have hCap := h (.gate gCapPass) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gCapPass, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eSub, EmittedExpr.eval] at hCap hLo hHi hNon hRes
    refine ⟨by linarith [hCap], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hCap, hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hFld i hi]; ring

/-! ## §4 — ANTI-GHOST: a row that moves ANY frozen EffectVM column fails the descriptor. -/

/-- **Anti-ghost (cap_root tamper).** A refresh row whose post-`cap_root` ≠ pre-`cap_root` fails the
`gCapPass` gate (UNSAT) — refresh must leave `cap_root` (the `caps` digest) frozen. -/
theorem refreshVm_rejects_moved_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapPass).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (general).** A row that is NOT a full frame-freeze does not satisfy the per-row gates. -/
theorem refreshVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ RefreshRowIntent env) :
    ¬ (∀ c ∈ refreshRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((refreshVm_faithful env).mp h)

/-! ## §5 — Structured per-cell freeze soundness. -/

/-- **`RefreshRowEncodes env pre post`** — the row decodes to `(pre, post)` cell states. -/
def RefreshRowEncodes (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell refresh spec: the WHOLE EffectVM post-state equals the pre-state (every column frozen,
including `cap_root` — the part the runnable row witnesses). -/
def RefreshCellSpec (pre post : CellState) : Prop :=
  post.capRoot = pre.capRoot
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `RefreshRowEncodes`, `RefreshRowIntent` IS the structured per-cell `RefreshCellSpec`. -/
theorem intent_to_refreshCellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RefreshRowEncodes env pre post) (hint : RefreshRowIntent env) :
    RefreshCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hcap, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`refreshDescriptor_full_sound`** — satisfying the frame-freeze gates under the decoding forces the
structured per-cell freeze (the SUPPORTED part — every EffectVM column, incl. `cap_root`, frozen). -/
theorem refreshDescriptor_full_sound (env : VmRowEnv) (pre post : CellState)
    (henc : RefreshRowEncodes env pre post)
    (hgates : ∀ c ∈ refreshRowGates, c.holdsVm env false false) :
    RefreshCellSpec pre post :=
  intent_to_refreshCellSpec env pre post henc ((refreshVm_faithful env).mp hgates)

/-! ## §6 — Commitment tooth (the frozen post-state is bound into `state_commit`). -/

/-- The refresh hash sites ARE the transfer keystone's (same 4-site chain). -/
theorem refreshHashSites_eq : refreshVmDescriptor.hashSites = transferHashSites := rfl

/-- **`refreshDescriptor_commit_binds_state`** — two refresh rows that satisfy the hash sites and publish
equal `state_commit`s have identical absorbed columns (the frozen post-state, `cap_root` included). So a
prover cannot tamper any absorbed (frozen) cell while keeping the published commitment. -/
theorem refreshDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — THE CONNECTOR (the SUPPORTED part) — `cap_root` FREEZE to `refreshDelegationA_full_sound`.

`refreshDelegationA` freezes `caps` (`RefreshDelegationSpec`'s `s'.kernel.caps = s.kernel.caps`), so the
projected `cap_root` digest `D k'.caps` equals `D k.caps` — exactly the row's `cap_root` passthrough.
This is the part the runnable row WITNESSES. The `delegations` move is the IR-blocked remainder. -/

/-- **`capRootProj D k`** — the EffectVM `cap_root` column value: the `caps` whole-function digest. -/
def capRootProj (D : (CellId → List Cap) → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- **`unify_refresh_capFreeze` — THE CONNECTOR (supported part).** When `RefreshDelegationSpec` holds,
the projected `cap_root` is FROZEN (`D k'.caps = D k.caps`) — exactly the runnable row's `cap_root`
passthrough gate. So the row's `cap_root`-freeze clause IS universe-A's `caps`-freeze clause. -/
theorem unify_refresh_capFreeze (D : (CellId → List Cap) → ℤ)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (hspec : RefreshDelegationSpec s args.actor args.child s') :
    capRootProj D s'.kernel = capRootProj D s.kernel := by
  -- RefreshDelegationSpec's `caps`-freeze clause: `s'.kernel.caps = s.kernel.caps`.
  obtain ⟨_hguard, _hdeleg, _hlog, _hAcc, _hCell, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D s.kernel.caps
  rw [hcaps]

/-- **`unify_refresh_capFreeze_via_full_sound`** — chaining `refreshDelegationA_full_sound` (the
`RefreshDelegationGuard` enforced by its `propBit` column, ⟹ `RefreshDelegationSpec`) with
`unify_refresh_capFreeze`: a satisfying universe-A witness forces the projected `cap_root` FROZEN — the
runnable row's passthrough. The `delegations := refreshDelegationsMap …` move is the IR-blocked remainder
(no EffectVM column), carried by `refreshDelegationA_full_sound`'s `delegations` `funcComponent`. -/
theorem unify_refresh_capFreeze_via_full_sound
    (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RefreshDelegationA.RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (refreshDelegationE D hD) (encodeE2 S (refreshDelegationE D hD) s args s')) :
    capRootProj D s'.kernel = capRootProj D s.kernel :=
  unify_refresh_capFreeze D s args s'
    (refreshDelegationA_full_sound S D hD hRest hLog s args s' h)

/-! ## §8 — THE IR-BLOCKED REMAINDER, stated exactly (the touched field has no EffectVM column).

`refreshDelegationA`'s genuine content — `s'.kernel.delegations = refreshDelegationsMap s.kernel child`
— is over the `delegations` sub-table, which the EffectVM state block does NOT carry as a column. We
state the gap as a theorem: the runnable row's frozen `cap_root` column says NOTHING about `delegations`
(two kernel states agreeing on `caps` can DISAGREE on `delegations`), so the runnable descriptor does NOT
witness the `delegations` move. -/

/-- **`delegations_not_witnessed_by_capRoot` — the loud IR gap, as a theorem.** The runnable row's
`cap_root` column reads ONLY `caps`; it is independent of `delegations`. Concretely: there exist two
kernel states with IDENTICAL `caps` (hence identical projected `cap_root`) but DIFFERENT `delegations`.
So a `delegations` tamper rides the SAME frozen `cap_root` — the runnable row cannot witness the
`delegations := refreshDelegationsMap …` move. (This is the precise sense in which `refreshDelegationA`
is IR-BLOCKED: its touched field has no EffectVM column. A `delegations_root` column + hash-site would
internalize it.) -/
theorem delegations_not_witnessed_by_capRoot (D : (CellId → List Cap) → ℤ)
    (k : RecordKernelState) (g₁ g₂ : CellId → List Cap) (hne : g₁ ≠ g₂) :
    capRootProj D { k with delegations := g₁ } = capRootProj D { k with delegations := g₂ }
    ∧ ({ k with delegations := g₁ } : RecordKernelState).delegations
        ≠ ({ k with delegations := g₂ } : RecordKernelState).delegations := by
  refine ⟨?_, ?_⟩
  · -- both have `caps = k.caps`, so the projected cap_root agrees.
    show D ({ k with delegations := g₁ } : RecordKernelState).caps
        = D ({ k with delegations := g₂ } : RecordKernelState).caps
    rfl
  · -- the `delegations` fields differ.
    show g₁ ≠ g₂
    exact hne

/-! ## §9 — NON-VACUITY: a concrete frame-freeze row that satisfies the intent, and one that does not. -/

/-- A concrete refresh row: every EffectVM state column frozen (`cap_root 9 → 9`, all else 0). -/
def refreshGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selR.REFRESH then 1
    else if v = sbCol state.CAP_ROOT then 9
    else if v = saCol state.CAP_ROOT then 9
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `refreshGoodRow` REALIZES the frame-freeze intent: `cap_root 9 = 9`,
all other columns `0 = 0`. -/
theorem refreshGoodRow_realizes_intent : RefreshRowIntent refreshGoodRow := by
  unfold RefreshRowIntent refreshGoodRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cap_root: saCol CAP_ROOT (87) reads 9, sbCol CAP_ROOT (65) reads 9.
    have hsa : (if saCol state.CAP_ROOT = selR.REFRESH then (9:ℤ)
        else if saCol state.CAP_ROOT = sbCol state.CAP_ROOT then 9
        else if saCol state.CAP_ROOT = saCol state.CAP_ROOT then 9 else 0) = 9 := by
      rw [if_neg (by simp only [saCol, selR.REFRESH, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE,
        NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT]; omega),
        if_neg (by simp only [saCol, sbCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE,
          NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT]; omega), if_pos rfl]
    have hsb : (if sbCol state.CAP_ROOT = selR.REFRESH then (9:ℤ)
        else if sbCol state.CAP_ROOT = sbCol state.CAP_ROOT then 9
        else if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then 9 else 0) = 9 := by
      rw [if_neg (by simp only [sbCol, selR.REFRESH, STATE_BEFORE_BASE, NUM_EFFECTS]; omega),
        if_pos rfl]
    show (refreshGoodRow).loc (saCol state.CAP_ROOT) = (refreshGoodRow).loc (sbCol state.CAP_ROOT)
    show (if saCol state.CAP_ROOT = selR.REFRESH then (9:ℤ)
        else if saCol state.CAP_ROOT = sbCol state.CAP_ROOT then 9
        else if saCol state.CAP_ROOT = saCol state.CAP_ROOT then 9 else 0)
       = (if sbCol state.CAP_ROOT = selR.REFRESH then (9:ℤ)
        else if sbCol state.CAP_ROOT = sbCol state.CAP_ROOT then 9
        else if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then 9 else 0)
    rw [hsa, hsb]
  all_goals
    simp only [saCol, sbCol, selR.REFRESH, STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, state.BALANCE_LO, state.BALANCE_HI,
      state.NONCE, state.RESERVED, state.FIELD_BASE]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro i hi
    have e1 : ¬ (76 + (3 + i) = 3) := by omega
    have e2 : ¬ (76 + (3 + i) = 65) := by omega
    have e3 : ¬ (76 + (3 + i) = 87) := by omega
    have f1 : ¬ (54 + (3 + i) = 3) := by omega
    have f2 : ¬ (54 + (3 + i) = 65) := by omega
    have f3 : ¬ (54 + (3 + i) = 87) := by omega
    simp only [if_neg e1, if_neg e2, if_neg e3, if_neg f1, if_neg f2, if_neg f3]

/-- A forged refresh row: `refreshGoodRow` with the post-`cap_root` MOVED to `999 ≠ 9` (refresh must
freeze `cap_root`). -/
def refreshBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else refreshGoodRow.loc v
  nxt := refreshGoodRow.nxt
  pub := refreshGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `refreshBadRow`'s post-`cap_root` is MOVED, so
the `gCapPass` freeze gate REJECTS it — a concrete UNSAT. -/
theorem refreshBadRow_rejected : ¬ (VmConstraint.gate gCapPass).holdsVm refreshBadRow false false := by
  apply refreshVm_rejects_moved_capRoot
  have hsa : refreshBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else refreshGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have hne : ¬ (saCol state.CAP_ROOT = sbCol state.CAP_ROOT) := by
    simp only [saCol, sbCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.CAP_ROOT]; omega
  have hsb : refreshBadRow.loc (sbCol state.CAP_ROOT) = 9 := by
    show (if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else refreshGoodRow.loc (sbCol state.CAP_ROOT)) = 9
    rw [if_neg (fun h => hne h.symm)]
    show (if sbCol state.CAP_ROOT = selR.REFRESH then (9:ℤ)
      else if sbCol state.CAP_ROOT = sbCol state.CAP_ROOT then 9
      else if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then 9 else 0) = 9
    rw [if_neg (by simp only [sbCol, selR.REFRESH, STATE_BEFORE_BASE, NUM_EFFECTS]; omega), if_pos rfl]
  rw [hsa, hsb]; norm_num

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard refreshVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 freeze gates + 14 transitions + 4 first
#guard refreshVmDescriptor.hashSites.length == 4
#guard refreshVmDescriptor.traceWidth == 186

#assert_axioms refreshVm_faithful
#assert_axioms refreshVm_rejects_moved_capRoot
#assert_axioms refreshVm_rejects_wrong_output
#assert_axioms intent_to_refreshCellSpec
#assert_axioms refreshDescriptor_full_sound
#assert_axioms refreshDescriptor_commit_binds_state
#assert_axioms unify_refresh_capFreeze
#assert_axioms unify_refresh_capFreeze_via_full_sound
#assert_axioms delegations_not_witnessed_by_capRoot
#assert_axioms refreshGoodRow_realizes_intent
#assert_axioms refreshBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
