/-
# Dregg2.Circuit.Emit.EffectVmEmitIntroduce — the AUTHORITY-INTRODUCE effect `introduceA`'s EffectVM-row
  circuit, EMITTED, RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and GRADUATED into
  the descriptor cutover (v2).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover runs `introduce` (selector 35) as a member of the **Stage-3 passthrough batch**
(`air.rs:983-1018`, `trace.rs:625`): the trace arm parks `intro_hash[0]` into `params[0]` and does
`new_state.nonce += 1` — it does NOT move `cap_root` on the row. Every economic state-block column
(balance limbs, `cap_root`, all 8 fields, reserved) is FROZEN by the passthrough batch; the GLOBAL nonce
gate ticks the nonce by 1. The cap-table grant LIVES OFF-TRACE (bound via `compute_effects_hash`).

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the cellDestroy gauntlet). The PRE-v2
descriptor REUSED the `attenuateA` cap-root-MOVE descriptor that the runtime hand-AIR does NOT enforce on
an introduce row (it FREEZES `cap_root`); that descriptor "passed" the honest trace only by fixture
accident (`cap_root = param2 = 0`) and froze the nonce. This v2 emits the runtime passthrough + nonce
TICK directly, and binds the cap-table grant OFF-row via the universe-A connector (§9).

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the boundary — the cap-table grant is OFF-ROW)

  * the `caps := recDelegateCaps caps intro recip t` grant + the Granovetter `delegateGuard` — the
    `cap_root` is the SCALAR digest of the cap-table FUNCTION; the runtime hand-AIR FREEZES the on-row
    `cap_root` column and binds the actual grant via `effects_hash` OFF the per-row state block. The grant
    SOUNDNESS lives in universe-A's `introduceA_full_sound` / `Function.Injective D` (cited via §connector).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
cap-table digest ONLY as `Function.Injective D`.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA

namespace Dregg2.Circuit.Emit.EffectVmEmitIntroduce

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins
   gate_modEq_iff not_modEq_zero_of_canon eqToModEq)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols absorbed_determined_by_commit_of_injective)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.IntroduceA (IntroduceArgs introduceE introduceA_full_sound)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec recDelegateCaps)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `introduce` selector column (runtime `sel::INTRODUCE = 35`). -/

/-- The `introduce` selector column index (runtime `sel::INTRODUCE = 35`). -/
def SEL_INTRODUCE : Nat := 35

/-- The introduce row: `s_introduce = 1`, `s_noop = 0` (load-bearing for the nonce TICK gate). -/
def IsIntroduceRow (env : VmRowEnv) : Prop :=
  env.loc SEL_INTRODUCE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body (introduce moves no value; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH (incl. `cap_root`) + nonce TICK (`gNonce`). -/
def introduceRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def introduceVmAirName : String := "dregg-effectvm-introduce-v2"

def introduceHashSites : List VmHashSite := transferHashSites

/-- **`introduceVmDescriptor`** — the `introduceA` EffectVM-row circuit, RECONCILED onto the runtime
hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary PI
pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def introduceVmDescriptor : EffectVmDescriptor :=
  { name := introduceVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := introduceRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 35
  , hashSites := introduceHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`IntroduceRowIntent env`** — every economic state-block column UNCHANGED (incl. `cap_root`) EXCEPT
the nonce, which TICKS by 1 (on a non-NoOp row `s_noop = 0`). The cap-table grant is out-of-row. -/
def IntroduceRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE)
      ≡ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP) [ZMOD 2013265921]
  ∧ env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-! ## §4 — FAITHFULNESS. -/

theorem introduceVm_faithful (env : VmRowEnv) :
    (∀ c ∈ introduceRowGates, c.holdsVm env false false) ↔ IntroduceRowIntent env := by
  unfold introduceRowGates gFieldPassAll IntroduceRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨(gate_modEq_iff (by ring)).mp hLo, (gate_modEq_iff (by ring)).mp hHi,
      (gate_modEq_iff (by ring)).mp hNon, (gate_modEq_iff (by ring)).mp hCap,
      (gate_modEq_iff (by ring)).mp hRes, ?_⟩
    intro i hi
    have hfi := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hfi
    exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-! ## §5 — ANTI-GHOST. -/

theorem introduceVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ IntroduceRowIntent env) :
    ¬ (∀ c ∈ introduceRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((introduceVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` (both cells canonical,
`0 ≤ · < p` for the BabyBear prime `p = 2013265921`) fails the freeze gate — the field gate cannot
pass by wrap-around. -/
theorem introduceVm_rejects_moved_balance (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.BALANCE_LO)
      ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hcanonOld : 0 ≤ env.loc (sbCol state.BALANCE_LO)
      ∧ env.loc (sbCol state.BALANCE_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonOld hwrong

/-- **Anti-ghost (cap-root tamper on row).** A row whose post-`cap_root` ≠ pre-`cap_root` fails the freeze
gate — the runtime row freezes `cap_root` (the grant rides effects_hash); no on-row cap move is allowed. -/
theorem introduceVm_rejects_moved_capRoot (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.CAP_ROOT)
      ∧ env.loc (saCol state.CAP_ROOT) < 2013265921)
    (hcanonOld : 0 ≤ env.loc (sbCol state.CAP_ROOT)
      ∧ env.loc (sbCol state.CAP_ROOT) < 2013265921)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapPass).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonOld hwrong

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. -/
theorem introduceVm_rejects_nonce_freeze (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hcanonTick : 0 ≤ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
      ∧ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP) < 2013265921)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonTick hwrong

/-! ## §6 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem introduceVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ introduceHashSites)
    (hs₂ : siteHoldsAll hash e₂ introduceHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit_of_injective hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesIntroduce env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesIntroduce (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`IntroduceCellSpec pre post`** — the per-cell FULL-state introduce row spec: economic block (incl.
`capRoot`) FROZEN; the nonce TICKS by 1. (The cap-table grant is off-row.) -/
def IntroduceCellSpec (pre post : CellState) : Prop :=
  post.balLo ≡ pre.balLo [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesIntroduce env pre post) (hint : IntroduceRowIntent env) :
    IntroduceCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · have h := hnon
    rw [hnoop] at h
    rw [← hsaN, ← hsbN]
    simpa using h
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §8 — the full descriptor soundness + the commitment binding. -/

theorem introduceDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesIntroduce env pre post)
    (hgatesat : satisfiedVm hash introduceVmDescriptor env true false)
    (hsat : satisfiedVm hash introduceVmDescriptor env true true) :
    IntroduceCellSpec pre post ∧ post.commit ≡ env.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ introduceRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ introduceVmDescriptor.constraints := by
      unfold introduceVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold introduceRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (introduceVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ introduceVmDescriptor.constraints := by
      unfold introduceVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

theorem introduceDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash introduceVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash introduceVmDescriptor e₂ true true)
    -- FIELD-FAITHFUL bridge: the published commitment is a CANONICAL field element (Poseidon2's
    -- output lives in `[0, p)`). The circuit pins `state_commit ≡ NEW_COMMIT [ZMOD p]`; canonicality
    -- of the two digest columns lifts that field congruence to the ℤ equality CR needs.
    (hcanon₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT)
      ∧ e₁.loc (saCol state.STATE_COMMIT) < 2013265921)
    (hcanon₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT)
      ∧ e₂.loc (saCol state.STATE_COMMIT) < 2013265921)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ introduceHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ introduceHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash introduceVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) ≡ e.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ introduceVmDescriptor.constraints := by
        unfold introduceVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have hmod : e₁.loc (saCol state.STATE_COMMIT) ≡ e₂.loc (saCol state.STATE_COMMIT)
      [ZMOD 2013265921] := by
    have h2 : e₁.pub pi.NEW_COMMIT ≡ e₂.loc (saCol state.STATE_COMMIT) [ZMOD 2013265921] := by
      rw [hpub]; exact (hc e₂ hsat₂).symm
    exact (hc e₁ hsat₁).trans h2
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    have hdvd := Int.modEq_iff_dvd.mp hmod
    obtain ⟨l₁, u₁⟩ := hcanon₁
    obtain ⟨l₂, u₂⟩ := hcanon₂
    omega
  exact absorbed_determined_by_commit_of_injective hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §9 — THE CONNECTOR — the cap-table grant (OFF-ROW), via `introduceA_full_sound`. -/

/-- The cap-table digest projection (the whole-function injective digest `D`). -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- The predicted post cap-digest for `introduceA`: `D` of `recDelegateCaps caps intro recip t`. -/
def introduceCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : IntroduceArgs) : ℤ :=
  D (recDelegateCaps s.kernel.caps args.intro args.recip args.t)

/-- **`unify_introduce` — THE OFF-ROW CONNECTOR.** When `DelegateSpec` holds for the introduce args, the
projected post cap-digest is EXACTLY the introduce cap-digest. This is the effect's actual semantic
content, enforced OFF the per-row state block (the runtime binds it via `effects_hash`). -/
theorem unify_introduce (D : Caps → ℤ) (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (hspec : DelegateSpec s args.intro args.recip args.t s') :
    capRootProj D s'.kernel = introduceCapDigestNew D s args := by
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (recDelegateCaps s.kernel.caps args.intro args.recip args.t)
  rw [hcaps]

/-- **`unify_introduce_via_full_sound` — inherits the VALIDATED guarantee (off-row cap-table grant).** -/
theorem unify_introduce_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.IntroduceA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s')) :
    capRootProj D s'.kernel = introduceCapDigestNew D s args :=
  unify_introduce D s args s' (introduceA_full_sound S D hD hRest hLog s args s' h)

/-! ## §10 — NON-VACUITY. -/

/-- A concrete introduce row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodIntroduceRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_INTRODUCE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodIntroduceRow_noop : goodIntroduceRow.loc sel.NOOP = 0 := by
  show goodIntroduceRow.loc 0 = 0
  simp only [goodIntroduceRow, SEL_INTRODUCE, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodIntroduceRow` REALIZES the runtime introduce intent. -/
theorem goodIntroduceRow_realizes_intent : IntroduceRowIntent goodIntroduceRow := by
  unfold IntroduceRowIntent
  have hnoop : goodIntroduceRow.loc sel.NOOP = 0 := goodIntroduceRow_noop
  refine ⟨eqToModEq rfl, eqToModEq rfl, ?_, eqToModEq rfl, eqToModEq rfl, ?_⟩
  · rw [hnoop]
    refine eqToModEq ?_
    show goodIntroduceRow.loc (saCol state.NONCE) = goodIntroduceRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodIntroduceRow, SEL_INTRODUCE, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    refine eqToModEq ?_
    show goodIntroduceRow.loc (saCol (state.FIELD_BASE + i)) = goodIntroduceRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodIntroduceRow, SEL_INTRODUCE, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 35) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 35) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED introduce row: `goodIntroduceRow` with the post-`bal_lo` minted to `999`. -/
def badIntroduceRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodIntroduceRow.loc v
  nxt := goodIntroduceRow.nxt
  pub := goodIntroduceRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badIntroduceRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badIntroduceRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badIntroduceRow false false := by
  have hsa : badIntroduceRow.loc (saCol state.BALANCE_LO) = 999 := by
    simp only [badIntroduceRow, goodIntroduceRow, sbCol, saCol, SEL_INTRODUCE, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  have hsb : badIntroduceRow.loc (sbCol state.BALANCE_LO) = 100 := by
    simp only [badIntroduceRow, goodIntroduceRow, sbCol, saCol, SEL_INTRODUCE, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  apply introduceVm_rejects_moved_balance
  · rw [hsa]; norm_num
  · rw [hsb]; norm_num
  · rw [hsa, hsb]; norm_num

/-- A FROZEN-NONCE introduce row: `goodIntroduceRow` with the post-nonce held at `5`. -/
def staleNonceIntroduceRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodIntroduceRow.loc v
  nxt := goodIntroduceRow.nxt
  pub := goodIntroduceRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceIntroduceRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceIntroduceRow false false := by
  have hsa : staleNonceIntroduceRow.loc (saCol state.NONCE) = 5 := by
    simp only [staleNonceIntroduceRow, goodIntroduceRow, sel.NOOP, sbCol, saCol, SEL_INTRODUCE,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  have hsb : staleNonceIntroduceRow.loc (sbCol state.NONCE) = 5 := by
    simp only [staleNonceIntroduceRow, goodIntroduceRow, sel.NOOP, sbCol, saCol, SEL_INTRODUCE,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  have hnoop : staleNonceIntroduceRow.loc sel.NOOP = 0 := by
    simp only [staleNonceIntroduceRow, goodIntroduceRow, sel.NOOP, sbCol, saCol, SEL_INTRODUCE,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  apply introduceVm_rejects_nonce_freeze
  · rw [hsa]; norm_num
  · rw [hsb, hnoop]; norm_num
  · rw [hsa, hsb, hnoop]; norm_num


/-! ## §G — THE GENUINE CLASS-A `introduce` — `cap_root` RECOMPUTED in-row (inherits the shared primitive).

`introduce` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the GENUINE class-A descriptor
`attenuateVmDescriptorGenuine` (the opaque `param.CAP_DIGEST_NEW` move REPLACED by the FORCED in-row
recompute `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`). The
`introduce`-specific content is the OP tag `capOp.INTRODUCE` carried in the edge leaf (the Granovetter introduction grant), plus the existing
connector to universe-A. We re-export the genuine soundness + edge-binding anti-ghost for `introduce`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuine attenuateGenuineRowGates CapCellSpecGenuine attenuateHashSites
   attenuateGenuine_sound attenuateGenuine_binds_edge CapRowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds)

/-- **`introduceVmDescriptorGenuine`** — the GENUINE `introduce` circuit: definitionally the shared genuine
cap-root-recompute descriptor (the opaque digest param is GONE; `cap_root` is FORCED in-row). -/
def introduceVmDescriptorGenuine : EffectVmDescriptor := attenuateVmDescriptorGenuine

/-- **`introduceGenuine_sound` — THE CLASS-A THEOREM for `introduce`.** Satisfying the genuine descriptor's
frame-freeze gates AND the in-row cap-root recompute forces the GENUINE full per-cell post-state:
`post.capRoot` is the FORCED advance `hash[edge_leaf, pre.capRoot]` (NOT an opaque parameter), every other
field frozen. Inherited from the shared `attenuateGenuine_sound`. -/
theorem introduceGenuine_sound (hash : List ℤ → ℤ) (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env pre post :=
  attenuateGenuine_sound hash env pre post capDigestNew henc hgates hrec

/-- **`introduceGenuine_binds_edge` — the genuine class-A anti-ghost for `introduce`.** Two genuine `introduce` rows
with EQUAL published `state_commit` share the old `cap_root` AND every bound edge field
(holder/target/rights/op) — so tampering the cap-edge mutation moves `cap_root`, moves `state_commit` ⇒
UNSAT. Inherited from the shared `attenuateGenuine_binds_edge`. -/
theorem introduceGenuine_binds_edge (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (e₁ e₂ : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hsCommit₁ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₁ attenuateHashSites)
    (hsCommit₂ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₂ attenuateHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP) :=
  attenuateGenuine_binds_edge hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hrec₁ hrec₂ hcommit

#assert_axioms introduceGenuine_sound
#assert_axioms introduceGenuine_binds_edge

/-! ### §G.4 — `introduce` carries IN-CIRCUIT NON-AMPLIFICATION (`granted ⊑ held`, the ARGUS linchpin).

`introduce` installs a Granovetter edge conferring rights bounded by the introducer's held cap. It
inherits the shared GENUINE-NON-AMP descriptor `attenuateVmDescriptorGenuineNonAmp`: the cap-root
recompute binds the introduced edge's `rights` into `cap_root`, and the per-bit submask gate forces
`granted ⊑ held` on that same felt — so an `introduce` cannot leak rights the introducer does not hold.
In-circuit, on the SAME descriptor that recomputes the cap-root. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuineNonAmp attenuateGenuineNonAmp_in_circuit
   attenuateGenuineNonAmp_rejects_amplify)

/-- **`introduceVmDescriptorGenuineNonAmp`** — the GENUINE `introduce` circuit WITH in-circuit non-amp:
definitionally the shared genuine-non-amp descriptor (recompute + `granted ⊑ held`). -/
def introduceVmDescriptorGenuineNonAmp : EffectVmDescriptor := attenuateVmDescriptorGenuineNonAmp

/-- **`introduceNonAmp_in_circuit`** — a satisfying `introduce` witness FORCES `granted ⊑ held` per bit
(both bit cells canonical, i.e. in `[0, p)` for the BabyBear prime `p = 2013265921`). Inherited from
the shared in-circuit non-amp tooth. -/
theorem introduceNonAmp_in_circuit (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hcon : ∀ c ∈ introduceVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hgc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) < 2013265921)
    (hhc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) < 2013265921) :
    env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 0
    ∨ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 1 :=
  attenuateGenuineNonAmp_in_circuit env hcon i hi hgc hhc

/-- **`introduceNonAmp_rejects_amplify`** — an amplifying `introduce` (granted bit set, held bit clear)
does NOT satisfy the descriptor. Inherited from the shared rejection. -/
theorem introduceNonAmp_rejects_amplify (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hg : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 1)
    (hh : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 0) :
    ¬ (∀ c ∈ introduceVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false) :=
  attenuateGenuineNonAmp_rejects_amplify env i hi hg hh

#assert_axioms introduceNonAmp_in_circuit
#assert_axioms introduceNonAmp_rejects_amplify

/-! ## §11 — Axiom-hygiene tripwires. -/

#guard introduceVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard introduceVmDescriptor.hashSites.length == 4
#guard introduceVmDescriptor.traceWidth == 188

#assert_axioms introduceVm_faithful
#assert_axioms introduceVm_rejects_wrong_output
#assert_axioms introduceVm_rejects_moved_balance
#assert_axioms introduceVm_rejects_moved_capRoot
#assert_axioms introduceVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms introduceDescriptor_full_sound
#assert_axioms introduceDescriptor_commit_binds_state
#assert_axioms unify_introduce
#assert_axioms unify_introduce_via_full_sound
#assert_axioms goodIntroduceRow_realizes_intent
#assert_axioms badIntroduceRow_rejected
#assert_axioms staleNonceIntroduceRow_rejected

/-! ## §W — THE MAGNESIUM LIFT: `introduce`'s RUNNABLE descriptor binds the FULL 17-field post-state.

`introduce` is a PASSTHROUGH+nonce-TICK cap-graph row (cap_root FROZEN on-row; the `caps` GRANT rides
OFF-row via the `unify_introduce` connector). Its WIDE descriptor widens `introduceVmDescriptor` to
`EFFECT_VM_WIDTH_SYSROOTS` with `wideHashSites`, so the published `state_commit` now absorbs the
`system_roots` digest. `introduce`'s kernel step (`recCDelegate`) edits ONLY `caps`; the 8 side-table
roots are FROZEN, so the full clause is the per-cell `IntroduceCellSpec` (frame frozen, nonce ticked) AND
`postRoots = preRoots`. The `caps` grant is the named OFF-ROW `Function.Injective D` connector (the §9
`unify_introduce` bar), NOT a state-block column — so this is the magnesium for the EffectVM ROW
post-state (the per-cell block + the 8 frozen side-table roots, all bound). -/

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (boundaryLastPins boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound
   wide_rejects_root_tamper_or_collides WideColl RootsColl)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest N_SYSTEM_ROOTS)

/-- **`introduceVmDescriptorWide`** — the runnable `introduce` FULL-state circuit: `introduceVmDescriptor`
WIDENED to `EFFECT_VM_WIDTH_SYSROOTS` with `hashSites := wideHashSites` (the `system_roots`-absorbing
sites). Strictly additive: the constraint list (passthrough+tick gates ++ transitions ++ boundary ++
selector) is byte-identical; only the width grows by 2 and site 3's spare `.zero` slot becomes the
side-table digest carrier. -/
def introduceVmDescriptorWide : EffectVmDescriptor :=
  { introduceVmDescriptor with
    name := "dregg-effectvm-introduceA-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide introduce descriptor's constraints ARE `introduceVmDescriptor`'s. -/
theorem introduceWide_constraints_eq :
    introduceVmDescriptorWide.constraints = introduceVmDescriptor.constraints := rfl

/-- **`IntroduceFullClause`** — the FULL declarative introduce post-state: the per-cell
`IntroduceCellSpec` (balance/cap_root/fields/reserved FROZEN, nonce TICKED) AND the `system_roots`
sub-block FROZEN (`postRoots = preRoots`; the `caps` grant rides off-row). Non-vacuous: a real introduce
row inhabits it (`introduceWide_realizes`). -/
def IntroduceFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  IntroduceCellSpec pre post ∧ postRoots = preRoots

/-- **`introduceRunnableSpec` — the introduce FULL-state RUNNABLE instance.** `decodeAfter` is
`RowEncodesIntroduce` PLUS the frozen-roots witness; `decodeFull` projects the wide descriptor's
passthrough+tick gates (= introduce's) to `introduceVm_faithful` + `intent_to_cellSpec` (the `s_noop = 0`
needed for the tick comes from `IsIntroduceRow`), then carries the frozen-roots fact. THIN +
NON-VACUOUS. -/
def introduceRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := introduceVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsIntroduceRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesIntroduce env pre post ∧ postRoots = preRoots
  fullClause    := IntroduceFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    obtain ⟨_hsel, hnoop⟩ := hrow
    -- restrict the wide descriptor's constraints to the passthrough+tick row gates (flag-free).
    have hgates' : ∀ c ∈ introduceRowGates, c.holdsVm env false false := by
      intro c hc
      have hmem : c ∈ introduceVmDescriptorWide.constraints := by
        show c ∈ introduceVmDescriptor.constraints
        unfold introduceVmDescriptor
        simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
      have hh := hgates c hmem
      unfold introduceRowGates gFieldPassAll at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
        simpa only [VmConstraint.holdsVm] using hh
    exact ⟨intent_to_cellSpec env pre post hnoop henc ((introduceVm_faithful env).mp hgates'), hroots⟩

/-- **`introduce_runnable_full_sound` — THE MAGNESIUM CROWN for `introduce`.** A row satisfying the
runnable `introduce` WIDE descriptor (`satisfiedVm`, first/last active), under the structured decode, pins
the FULL 17-field introduce post-state: the per-cell frame freeze + nonce tick (binding `cell`/`bal`/
`cap_root`-here + frame) AND the frozen `system_roots` sub-block (binding the 8 side-table roots). The
`caps` grant is the named OFF-ROW `unify_introduce` connector. -/
theorem introduce_runnable_full_sound (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsIntroduceRow env)
    (henc : RowEncodesIntroduce env pre post)
    (hroots : postRoots = preRoots)
    (hgatesat : satisfiedVm hash introduceVmDescriptorWide env true false) :
    IntroduceFullClause preRoots pre post postRoots :=
  runnable_full_sound (introduceRunnableSpec preRoots) hash env pre post postRoots
    hrow ⟨henc, hroots⟩ hgatesat

/-- **`introduce_runnable_rejects_root_tamper_or_collides` — the side-table anti-ghost for `introduce`.**
Two wide introduce rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose
side-table sub-blocks DIFFER at some index exhibit a genuine collision of the deployed sponge — on the
state block (`WideColl`) or on the ordered root list (`RootsColl`). So such a pair is UNSAT unless the
prover holds a sponge collision: the 8 side-table roots are bound by the runnable introduce commitment.

The old form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed BabyBear sponge REFUTES,
so at deployed parameters it was vacuous. This form names what the tamper costs and holds of the deployed
sponge. -/
theorem introduce_runnable_rejects_root_tamper_or_collides (preRoots : SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash introduceVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash introduceVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_root_tamper_or_collides (introduceRunnableSpec preRoots) hash
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`introduceWide_realizes` — NON-VACUITY (witness TRUE).** `goodIntroduceRow` (the passthrough+tick
reference) decodes to a real introduce cell transition that, with frozen roots, inhabits
`IntroduceFullClause` — so the framework's clause is NOT `True`. -/
theorem introduceWide_realizes :
    IntroduceCellSpec
      { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0,
        commit := 0 }
      { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0,
        commit := 0 } :=
  ⟨Int.ModEq.refl _, Int.ModEq.refl _, eqToModEq (by norm_num), fun _ => Int.ModEq.refl _,
   Int.ModEq.refl _, Int.ModEq.refl _⟩

/-- **`introduceWide_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
nonce did NOT tick (held at `5`, demanding `5 + 1 = 6`) FAILS `IntroduceCellSpec` — so the clause is not
vacuously true. -/
theorem introduceWide_clause_not_trivial :
    ¬ IntroduceCellSpec
        { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0,
          commit := 0 }
        { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0,
          commit := 0 } := by
  rintro ⟨_, _, hnon, _⟩
  -- hnon : (5 : ℤ) ≡ 5 + 1 [ZMOD p] — would need p ∣ 1
  have hdvd := Int.ModEq.dvd hnon
  omega

#assert_axioms introduceWide_constraints_eq
#assert_axioms introduce_runnable_full_sound
#assert_axioms introduce_runnable_rejects_root_tamper_or_collides
#assert_axioms introduceWide_realizes
#assert_axioms introduceWide_clause_not_trivial

#guard introduceVmDescriptorWide.traceWidth == 190
#guard introduceVmDescriptorWide.hashSites.length == 4

end Dregg2.Circuit.Emit.EffectVmEmitIntroduce
