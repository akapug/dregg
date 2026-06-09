/-
# Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState — setField LIFTED to FULL-STATE on the RUNNABLE
descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitSetField` reaches per-cell CLASS A on the 186-wide RUNNABLE descriptor: the written field
column `fields[slot]` is among the 13 absorbed columns, so the move is bound + anti-ghosted by the
injective-commitment tooth (`setFieldDescriptor_classA`). But that `state_commit` absorbs only the 13
state-block columns, NOT the 8 side-table roots. This module CLOSES that by amplifying the per-slot
RUNNABLE descriptor to the WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell field-write block (`CellSetFieldSpec`: `fields[slot]`
written, every other column frozen) AND every one of the 8 side-table roots FROZEN (setField touches no
side-table). The anti-ghost tooth bites on all 17 (incl. any root).

The §RECIPE applied to setField (a per-slot family — one instance per `slot : Fin 8`). The "written
value" is read off `post.fields slot` (the `RowEncodesSF` clause `env.loc (prmCol VALUE) =
post.fields slot` ties the value carrier to it), so the clause is env-free + non-vacuous.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR only via the generic theorems.
No `sorry`/`:= True`/`native_decide`. `fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitSetField
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmEmitLifecycleGuard

namespace Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitSetField
  (SEL_SET_FIELD VALUE IsSetFieldRow setFieldRowGates setFieldVmDescriptor RowEncodesSF CellSetFieldSpec
   setFieldVm_faithful intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitLifecycleGuard
  (EFFECT_VM_WIDTH_GUARD guardBitCol gAdmit gAdmitBody BitEncodes gAdmit_pred_sound gAdmit_holds_iff
   gAdmit_rejects_zero gAdmit_iff_pred)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE setField descriptor (per slot; width + sites; constraints UNCHANGED).

`setFieldVmDescriptor slot` carries ONLY `setFieldRowGates slot` (no transition/boundary/selector), with
`hashSites := transferHashSites`. The wide form swaps in `EFFECT_VM_WIDTH_SYSROOTS` + `wideHashSites`. -/

def setFieldVmDescriptorWide (slot : Fin 8) : EffectVmDescriptor :=
  { setFieldVmDescriptor slot with
    name := (setFieldVmDescriptor slot).name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem setFieldWide_constraints_eq (slot : Fin 8) :
    (setFieldVmDescriptorWide slot).constraints = (setFieldVmDescriptor slot).constraints := rfl

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis — the THIN per-effect content).

`setFieldVmDescriptor slot`'s constraints ARE `setFieldRowGates slot`, so the per-row gates are the WHOLE
constraint list (membership is direct). All gates are `.gate`, flag-free. The written value is read off
`post.fields slot` via the `RowEncodesSF` value-carrier clause. -/

theorem setFieldGates_give_cellSpec (slot : Fin 8) (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesSF slot env pre post)
    (hgates : ∀ c ∈ (setFieldVmDescriptor slot).constraints, c.holdsVm env true true) :
    CellSetFieldSpec slot pre (post.fields slot) post := by
  -- the per-row gates are the whole constraint list; restrict to the flag-free `false false` form.
  have hrowgates : ∀ c ∈ setFieldRowGates slot, c.holdsVm env false false := by
    intro c hc
    have hh := hgates c hc
    -- every constraint is a `.gate`; `holdsVm` of a gate ignores the flags.
    unfold setFieldRowGates at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    -- dispatch on which gate (the 6 named + the filtered `gOtherFieldsAll` map).
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | hc <;>
      first
        | simpa only [VmConstraint.holdsVm] using hh
        | · -- the `gOtherFieldsAll slot` map members
            simp only [Dregg2.Circuit.Emit.EffectVmEmitSetField.gOtherFieldsAll, List.mem_map,
              List.mem_filter] at hc
            obtain ⟨i, _, rfl⟩ := hc
            simpa only [VmConstraint.holdsVm] using hh
  -- the value carrier IS `post.fields slot` (`RowEncodesSF`), so `intent_to_cellSpec`'s conclusion
  -- `CellSetFieldSpec slot pre (env.loc (prmCol VALUE)) post` rewrites to the env-free written value.
  have hval : env.loc (prmCol VALUE) = post.fields slot := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hVal, _, _⟩ := henc
    exact hVal
  have := intent_to_cellSpec slot env pre post henc ((setFieldVm_faithful slot env).mp hrowgates)
  rw [hval] at this
  exact this

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance (per slot). -/

/-- **`SetFieldFullClause slot`** — the FULL 17-field declarative post for a slot-`slot` setField:
`CellSetFieldSpec slot pre (post.fields slot) post` (the slot written, every other column frozen) AND the
`system_roots` sub-block FROZEN. NON-VACUOUS. -/
def SetFieldFullClause (slot : Fin 8) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellSetFieldSpec slot pre (post.fields slot) post ∧ postRoots = preRoots

/-- **`setFieldRunnableSpec slot`** — the FULL-state RUNNABLE instance for slot-`slot` setField. THIN;
NON-VACUOUS. -/
def setFieldRunnableSpec (slot : Fin 8) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := setFieldVmDescriptorWide slot
  usesWideSites := rfl
  isRow         := IsSetFieldRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesSF slot env pre post ∧ postRoots = preRoots
  fullClause    := SetFieldFullClause slot preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨setFieldGates_give_cellSpec slot env pre post henc
            (setFieldWide_constraints_eq slot ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `setField_runnable_full_sound`. -/

/-- **`setField_runnable_full_sound` — the magnesium crown for setField.** A row satisfying the WIDE
RUNNABLE slot-`slot` setField descriptor, decoded by `RowEncodesSF` with the frozen-roots witness, pins
the FULL 17-field post-state: the per-cell field-write block (`CellSetFieldSpec`) AND all 8 side-table
roots FROZEN. -/
theorem setField_runnable_full_sound (slot : Fin 8) (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsSetFieldRow env)
    (henc : RowEncodesSF slot env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash (setFieldVmDescriptorWide slot) env true true) :
    CellSetFieldSpec slot pre (post.fields slot) post ∧ postRoots = preRoots :=
  runnable_full_sound (setFieldRunnableSpec slot preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST. -/

theorem setField_runnable_full_commit_binds (slot : Fin 8) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₁ true true)
    (hsat₂ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (setFieldRunnableSpec slot preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`setField_rejects_root_tamper` — the side-table anti-ghost tooth.** Two wide slot-`slot` setField
rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose side-table sub-blocks
DIFFER at some root index cannot both satisfy. -/
theorem setField_rejects_root_tamper (slot : Fin 8) (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₁ true true)
    (hsat₂ : satisfiedVm hash (setFieldVmDescriptorWide slot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (setFieldRunnableSpec slot preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY (slot 0). -/

def setFieldPreRoots : SysRoots := emptySystemRoots

/-- The pre-state: bal_lo 100, all fields 0. -/
def setFieldPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The post-state: `fields[0] := 7` (the written value), everything else frozen. -/
def setFieldPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun i => if i = 0 then 7 else 0
  , capRoot := 0, reserved := 0, commit := 0 }

/-- **NON-VACUITY (witness TRUE).** The setField `fullClause` (slot 0) is inhabited by a real field
write: `setFieldPost` writes `fields[0] := 7` (= `setFieldPost.fields 0`), every other column frozen,
roots frozen. -/
theorem goodSetField_realizes :
    (setFieldRunnableSpec 0 setFieldPreRoots).fullClause setFieldPre setFieldPost setFieldPreRoots := by
  refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl, ?_⟩, rfl⟩
  · show setFieldPost.fields 0 = setFieldPost.fields 0; rfl
  · intro i hi
    show setFieldPost.fields i = setFieldPre.fields i
    simp only [setFieldPost, setFieldPre, if_neg hi]

/-- **NON-VACUITY (witness FALSE).** A forged post that MOVES the balance (`100 → 999`) FAILS the clause
(the field-write freezes the balance). -/
theorem setField_clause_not_trivial :
    ¬ SetFieldFullClause 0 setFieldPreRoots setFieldPre { setFieldPost with balLo := 999 } setFieldPreRoots := by
  rintro ⟨⟨_, hbal, _, _, _, _, _⟩, _⟩
  simp only [setFieldPre] at hbal
  norm_num at hbal

/-- **NON-VACUITY (side-table dimension).** A post whose `system_roots` sub-block is NOT the frozen
reference FAILS the clause — the frozen-roots leg is genuine. -/
theorem setField_clause_rejects_root_drop :
    ¬ SetFieldFullClause 0 setFieldPreRoots setFieldPre setFieldPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [setFieldPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §8 — THE GUARD-GATED RUNNABLE DESCRIPTOR: the executor's 4-conjunct admissibility guard
(caveat ∧ authority ∧ membership ∧ liveness) is now an IN-CIRCUIT CONJUNCT.

`EffectVmEmitSetField.setField_guard_is_offrow` honestly NAMED the executor's `SetFieldGuard` as an
off-row leg the runnable descriptor did NOT carry — a SEVERE completeness hole (a light client would
accept a field write by an UNAUTHORIZED actor, into a SEALED cell, violating a CLEARANCE caveat). This
section CLOSES it: the wide descriptor is extended with FOUR admissibility-bit gates
(`gAdmit (guardBitCol 0..3)`, the runnable-EffectVM analog of `SetFieldCommit.cSF{Caveat,Auth,Mem,Live}`),
the decode ties each bit column to the corresponding `SetFieldGuard` conjunct (`BitEncodes`, the honest
`encodeSF` discipline), and `fullClause` now CARRIES the four conjuncts — so a satisfying runnable
witness PROVES the executor's guard held. A row encoding a transition whose guard is false has a `0` bit
column, which the gate REJECTS (UNSAT). -/

/-- **`setFieldVmDescriptorWideGuarded slot`** — the WIDE setField descriptor EXTENDED with the four
admissibility-bit gates. `traceWidth := EFFECT_VM_WIDTH_GUARD` (the dedicated guard-bit block past 188);
`hashSites := wideHashSites` UNCHANGED (the guard bits are an admissibility side-condition, not committed
post-state — the commitment is byte-identical, exactly as `SetFieldCommit`'s guard bits are not in the
root). The four appended gates force the four bit columns `188..191` to `1`. -/
def setFieldVmDescriptorWideGuarded (slot : Fin 8) : EffectVmDescriptor :=
  { setFieldVmDescriptorWide slot with
    name := (setFieldVmDescriptorWide slot).name ++ "-guard"
    traceWidth := EFFECT_VM_WIDTH_GUARD
    constraints := (setFieldVmDescriptorWide slot).constraints
      ++ [gAdmit (guardBitCol 0), gAdmit (guardBitCol 1), gAdmit (guardBitCol 2), gAdmit (guardBitCol 3)] }

theorem setFieldGuarded_usesWideSites (slot : Fin 8) :
    (setFieldVmDescriptorWideGuarded slot).hashSites = wideHashSites := rfl

/-- **`SetFieldGuardedFullClause slot`** — the FULL post-state of a guard-gated setField: the per-cell
field-write block (`CellSetFieldSpec`), the frozen `system_roots`, AND the four admissibility conjuncts
`gCaveat ∧ gAuth ∧ gMem ∧ gLive` (instantiated, by the deliverable, at the `SetFieldGuard` conjuncts).
So the runnable clause now pins BOTH the state transition AND that it was admissible. -/
def SetFieldGuardedFullClause (slot : Fin 8) (preRoots : SysRoots)
    (gCaveat gAuth gMem gLive : Prop)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellSetFieldSpec slot pre (post.fields slot) post ∧ postRoots = preRoots
    ∧ gCaveat ∧ gAuth ∧ gMem ∧ gLive

/-- **`setFieldRunnableSpecGuarded`** — the guard-gated FULL-state RUNNABLE instance. The four
admissibility conjuncts are PARAMETERS (the deliverable instantiates them at the four `SetFieldGuard`
conjuncts of the real `(s, actor, cell, f, v)`); `decodeAfter` extends with the four `BitEncodes` ties
(the prover lays each conjunct's verdict on its bit column); `fullClause` extends with the conjunction;
`decodeFull` projects BOTH the per-cell gates (to `setFieldGates_give_cellSpec`) AND the four new
admissibility gates (to `gAdmit_pred_sound`). -/
def setFieldRunnableSpecGuarded (slot : Fin 8) (preRoots : SysRoots)
    (gCaveat gAuth gMem gLive : Prop)
    [Decidable gCaveat] [Decidable gAuth] [Decidable gMem] [Decidable gLive] :
    RunnableFullStateSpec CellState where
  descriptor    := setFieldVmDescriptorWideGuarded slot
  usesWideSites := setFieldGuarded_usesWideSites slot
  isRow         := IsSetFieldRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesSF slot env pre post ∧ postRoots = preRoots
      ∧ BitEncodes (guardBitCol 0) gCaveat env ∧ BitEncodes (guardBitCol 1) gAuth env
      ∧ BitEncodes (guardBitCol 2) gMem env ∧ BitEncodes (guardBitCol 3) gLive env
  fullClause    := SetFieldGuardedFullClause slot preRoots gCaveat gAuth gMem gLive
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, hb0, hb1, hb2, hb3⟩ := hdec
    -- the four NEW guard gates are members of the appended list; each forces its conjunct (via the
    -- honest `BitEncodes` decode + `gAdmit_pred_sound`).
    have hmemAppend : ∀ g ∈ [gAdmit (guardBitCol 0), gAdmit (guardBitCol 1), gAdmit (guardBitCol 2),
        gAdmit (guardBitCol 3)], g ∈ (setFieldVmDescriptorWideGuarded slot).constraints := by
      intro g hg; exact List.mem_append.mpr (Or.inr hg)
    have hgC : gCaveat := gAdmit_pred_sound (guardBitCol 0) gCaveat env true true hb0
      (hgates _ (hmemAppend _ (by simp)))
    have hgA : gAuth := gAdmit_pred_sound (guardBitCol 1) gAuth env true true hb1
      (hgates _ (hmemAppend _ (by simp)))
    have hgM : gMem := gAdmit_pred_sound (guardBitCol 2) gMem env true true hb2
      (hgates _ (hmemAppend _ (by simp)))
    have hgL : gLive := gAdmit_pred_sound (guardBitCol 3) gLive env true true hb3
      (hgates _ (hmemAppend _ (by simp)))
    -- the per-cell gates are the wide descriptor's (a prefix of the appended list); project them.
    have hcellGates : ∀ c ∈ (setFieldVmDescriptor slot).constraints, c.holdsVm env true true := by
      intro c hc
      exact hgates c (List.mem_append.mpr (Or.inl (by
        rw [setFieldWide_constraints_eq]; exact hc)))
    exact ⟨setFieldGates_give_cellSpec slot env pre post henc hcellGates, hroots, hgC, hgA, hgM, hgL⟩

/-- **`setField_runnable_full_sound_guarded` — THE GAP-CLOSING DELIVERABLE.** A row satisfying the
GUARD-GATED wide RUNNABLE setField descriptor, decoded by `RowEncodesSF` + the frozen-roots witness +
the four `BitEncodes` ties at the four `SetFieldGuard` conjuncts of a real chained `(s, actor, cell, f,
v)`, pins the FULL post-state AND PROVES `SetFieldGuard s actor cell f v`. So the runnable circuit the
prover RUNS now enforces the executor's admissibility guard: a light client checking the proof KNOWS the
actor was authorized over the cell, the cell was a live account, the cell's lifecycle admitted effects,
AND every slot caveat (incl. an SGM `clearanceGe`) admitted the write. The "off-row guard" hole closed. -/
theorem setField_runnable_full_sound_guarded (slot : Fin 8) (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (s : Dregg2.Exec.RecChainedState) (actor cell : Dregg2.Exec.CellId) (f : Dregg2.Exec.FieldName)
    (v : Int)
    (hrow : IsSetFieldRow env)
    (henc : RowEncodesSF slot env pre post) (hroots : postRoots = preRoots)
    (hb0 : BitEncodes (guardBitCol 0) (Dregg2.Exec.EffectsState.caveatsAdmit s.kernel f actor cell v = true) env)
    (hb1 : BitEncodes (guardBitCol 1) (Dregg2.Exec.EffectsState.stateAuthB s.kernel.caps actor cell = true) env)
    (hb2 : BitEncodes (guardBitCol 2) (cell ∈ s.kernel.accounts) env)
    (hb3 : BitEncodes (guardBitCol 3) (Dregg2.Exec.EffectsState.cellLive s.kernel cell = true) env)
    (hsat : satisfiedVm hash (setFieldVmDescriptorWideGuarded slot) env true true) :
    (CellSetFieldSpec slot pre (post.fields slot) post ∧ postRoots = preRoots)
      ∧ Dregg2.Circuit.Spec.CellStateField.SetFieldGuard s actor cell f v := by
  have h := runnable_full_sound
    (setFieldRunnableSpecGuarded slot preRoots
      (Dregg2.Exec.EffectsState.caveatsAdmit s.kernel f actor cell v = true)
      (Dregg2.Exec.EffectsState.stateAuthB s.kernel.caps actor cell = true)
      (cell ∈ s.kernel.accounts)
      (Dregg2.Exec.EffectsState.cellLive s.kernel cell = true))
    hash env pre post postRoots hrow ⟨henc, hroots, hb0, hb1, hb2, hb3⟩ hsat
  obtain ⟨hcell, hr, hC, hA, hM, hL⟩ := h
  exact ⟨⟨hcell, hr⟩, hC, hA, hM, hL⟩

/-! ### §8.1 — the ANTI-GATE tooth: a row with a `0` admissibility bit is UNSAT.

The contrapositive: a row whose authority bit (`guardBitCol 1`) is `0` (the actor is NOT authorized)
cannot satisfy the guarded descriptor — the authority gate `var 189 − 1 = 0` is violated. The guard
conjunct genuinely bites; an unauthorized field write is rejected by the runnable circuit. -/

theorem setFieldGuarded_rejects_unauth (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hzero : env.loc (guardBitCol 1) = 0) :
    ¬ satisfiedVm hash (setFieldVmDescriptorWideGuarded slot) env true true := by
  rintro ⟨hgates, _⟩
  have hmem : gAdmit (guardBitCol 1) ∈ (setFieldVmDescriptorWideGuarded slot).constraints :=
    List.mem_append.mpr (Or.inr (by simp))
  exact gAdmit_rejects_zero (guardBitCol 1) env true true hzero (hgates _ hmem)

/-! ### §8.2 — NON-VACUITY of the guard-gated clause (both bit values genuinely separated). -/

/-- **NON-VACUITY (witness TRUE).** The guarded clause (slot 0, all four conjuncts `True`) is inhabited:
the real field write of §6 + the four admitted conjuncts. -/
theorem goodSetFieldGuarded_realizes :
    (setFieldRunnableSpecGuarded 0 setFieldPreRoots True True True True).fullClause
      setFieldPre setFieldPost setFieldPreRoots := by
  refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl, ?_⟩, rfl, trivial, trivial, trivial, trivial⟩
  · show setFieldPost.fields 0 = setFieldPost.fields 0; rfl
  · intro i hi
    show setFieldPost.fields i = setFieldPre.fields i
    simp only [setFieldPost, setFieldPre, if_neg hi]

/-- **NON-VACUITY (witness FALSE — a denied conjunct refutes the clause).** With the authority conjunct
`False`, the guarded clause is UNINHABITABLE — so the guard conjunct is genuinely load-bearing in the
clause (a transition where authority fails cannot satisfy it). -/
theorem setFieldGuarded_clause_needs_auth :
    ¬ (setFieldRunnableSpecGuarded 0 setFieldPreRoots True False True True).fullClause
        setFieldPre setFieldPost setFieldPreRoots := by
  rintro ⟨_, _, _, hAuth, _, _⟩
  exact hAuth

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard (setFieldVmDescriptorWide 0).traceWidth == 188
#guard (setFieldVmDescriptorWide 0).hashSites.length == 4
#guard (setFieldVmDescriptorWide 0).constraints.length == (setFieldVmDescriptor 0).constraints.length
#guard (setFieldVmDescriptorWideGuarded 0).traceWidth == 192
#guard (setFieldVmDescriptorWideGuarded 0).constraints.length
        == (setFieldVmDescriptorWide 0).constraints.length + 4

#assert_axioms setFieldGates_give_cellSpec
#assert_axioms setField_runnable_full_sound
#assert_axioms setField_runnable_full_commit_binds
#assert_axioms setField_rejects_root_tamper
#assert_axioms goodSetField_realizes
#assert_axioms setField_clause_not_trivial
#assert_axioms setField_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState
