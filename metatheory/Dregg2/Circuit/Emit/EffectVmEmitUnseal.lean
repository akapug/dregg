/-
# Dregg2.Circuit.Emit.EffectVmEmitUnseal — the unseal (recover-a-cap-from-a-box) effect's concrete
EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/unsealA.lean`, `Spec/sealboxoperations.lean`) carries the FULL-state soundness
`execFullA_unseal_iff_spec ⇒ UnsealSpec`: a committed unseal GRANTS the box's `payload` cap into the
`recipient`'s c-list (`caps := grantedCaps caps recipient box.payload`), advances the chained `log`,
and is otherwise TOTALLY NEUTRAL — balance-neutral (`bal` frozen) and FREEZES the other 15 kernel
fields (INCLUDING `sealedBoxes` — the box is NOT consumed; it can be unsealed REPEATEDLY, the
documented FRAME-GAP). Guard: the actor HOLDS the unsealer cap for `pid` ∧ the box EXISTS.

## THE KEY STRUCTURAL FACT (and the honest IR boundary)

An unseal touches NEITHER the per-asset `bal` ledger NOR any per-cell state-block column — it only
GRANTS a cap into the `caps` SIDE-TABLE (a structure the EffectVM 14-column state block has NO column
for, absorbed by NO GROUP-4 hash-site). So, projected onto ONE EffectVM cell's state block, an unseal
is a PURE FREEZE: every state-block column UNCHANGED, and the published `state_commit` is the genuine
digest of the FROZEN after-state.

What the IR DOES support is exactly this FREEZE + the commitment binding of the frozen block — the
conservation / balance-neutrality tooth (a row claiming an unseal but mutating any cell is UNSAT).

## THE IR-EXTENSION FLAG (the cap-grant — the LOAD-BEARING leg, out-of-IR)

The actual effect — `caps := grantedCaps caps recipient box.payload` — is a GRANT of a CAPABILITY into
the cap-table side-structure. The EffectVM 14-column block has NO cap-table-root column, and the
GROUP-4 hash-sites absorb none of `caps`. So the per-row circuit CANNOT bind, or even witness, the
granted `payload` or the recipient.

  ⇒ **needs IR extension: a caps-table-root column in the EffectVM state block absorbed by a new
     hash-site, plus param columns carrying `recipient`/`payload`, so the grant is bound into the
     published `state_commit`.** The unsealer-cap-held / box-exists guard is likewise out-of-row.
     Reported, not papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sealboxoperations

namespace Dregg2.Circuit.Emit.EffectVmEmitUnseal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The unseal selector. -/

/-- The unseal-box selector column index. -/
def SEL_UNSEAL : Nat := 7

/-- The unseal row is an unseal row: `s_unseal = 1`, `s_noop = 0`. -/
def IsUnsealRow (env : VmRowEnv) : Prop :=
  env.loc SEL_UNSEAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (WHOLE state-block FREEZE). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — unsealing moves no value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted descriptor. -/

/-- The unseal-box AIR identity. -/
def unsealVmAirName : String := "dregg-effectvm-unseal-v1"

/-- The per-row gates: WHOLE state block frozen. -/
def unsealRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`unsealVmDescriptor`** — the unseal effect's concrete EffectVM circuit: the per-row WHOLE-block
freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash sites
(REUSED — binding the frozen block) and the 2 balance-limb range checks. -/
def unsealVmDescriptor : EffectVmDescriptor :=
  { name := unsealVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := unsealRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT: the WHOLE state block frozen. -/

/-- **`UnsealRowIntent env`** — the intended unseal move on the row `env.loc`: every state-block column
UNCHANGED. The cap-grant + held-cap/box-exists guard are out-of-row (the §IR flags). -/
def UnsealRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the freeze intent. -/

/-- **`unsealVm_faithful`.** On an unseal row, the emitted descriptor's per-row gates all hold IFF
`UnsealRowIntent` holds — the gates pin EXACTLY the whole-block freeze. -/
theorem unsealVm_faithful (env : VmRowEnv) :
    (∀ c ∈ unsealRowGates, c.holdsVm env false false) ↔ UnsealRowIntent env := by
  unfold unsealRowGates gFieldPassAll UnsealRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a row that MUTATES any state-block cell on an unseal is rejected. -/

/-- **Anti-ghost (general).** An unseal row whose state block is NOT frozen does NOT satisfy the
per-row gates — the conservation tooth. -/
theorem unsealVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ UnsealRowIntent env) :
    ¬ (∀ c ∈ unsealRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((unsealVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** An unseal row whose post-`bal_lo` is NOT the pre-`bal_lo` (value
forged on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem unsealVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesUnseal env pre post` ties the row's state-block columns to a `(pre, post)` cell
transition (no params — an unseal carries pid/recipient off-block). -/
def RowEncodesUnseal (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellUnsealSpec pre post`** — the per-cell FULL-state unseal spec: the WHOLE cell state is FROZEN.
This is the EffectVM-row projection of `UnsealSpec`'s balance-neutrality + per-cell frame freeze (the
cap-grant is off-block — the §IR flag). -/
def CellUnsealSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesUnseal`, `UnsealRowIntent` IS the structured `CellUnsealSpec`. -/
theorem intent_to_cellUnsealSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesUnseal env pre post) (hint : UnsealRowIntent env) :
    CellUnsealSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §7 — The full descriptor soundness + the commitment binding. -/

/-- **`unsealDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesUnseal`, forces the structured per-cell FREEZE `CellUnsealSpec` AND publishes the post-commit
as `PI[NEW_COMMIT]`. -/
theorem unsealDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesUnseal env pre post)
    (hsat : satisfiedVm hash unsealVmDescriptor env true true) :
    CellUnsealSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ unsealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ unsealVmDescriptor.constraints := by
      unfold unsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold unsealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (unsealVm_faithful env).mp hgates'
  refine ⟨intent_to_cellUnsealSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ unsealVmDescriptor.constraints := by
      unfold unsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §8 — The anti-ghost commitment tooth (REUSED; hash sites identical to transfer's). -/

/-- **`unsealDescriptor_commit_binds_state`** — two descriptor-satisfying unseal rows publishing the
SAME `NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep `NEW_COMMIT`
while tampering any absorbed cell of the (frozen) post-state. -/
theorem unsealDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash unsealVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash unsealVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash unsealVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ unsealVmDescriptor.constraints := by
        unfold unsealVmDescriptor
        simp only [List.mem_append]
        exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hc e₁ hsat₁, hc e₂ hsat₂, hpub]
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §9 — CONNECTOR to universe-A: `CellUnsealSpec` IS `UnsealSpec`'s per-cell frame image.

`execFullA_unseal_iff_spec ⇒ UnsealSpec` carries balance-neutrality (`bal' = bal`). We project ONE
cell into the keystone `CellState` and prove the projection of ANY cell satisfies `CellUnsealSpec`
EXACTLY (all FROZEN). The cap-grant is the §IR-extension flag, reported below as out-of-row. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId SealedBoxRecord)
open Dregg2.Circuit.Spec.SealBoxOperations
  (UnsealSpec execFullA_unseal_iff_spec grantedCaps unseal_grants_sealed_cap)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb; the other EffectVM limbs are `0`, frozen). -/
def cellProjUnseal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_unseal_freeze`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`UnsealSpec` post-state, satisfies the keystone's `CellUnsealSpec` EXACTLY: `balLo` FROZEN
(`bal' = bal`, balance-neutral); the rest frozen. So `CellUnsealSpec` IS `UnsealSpec`'s per-cell frame
image — NOT a fourth spec. -/
theorem unify_unseal_freeze (st st' : RecChainedState) (pid : Nat) (actor recipient c : CellId)
    (box : SealedBoxRecord) (asset : AssetId)
    (hspec : UnsealSpec st pid actor recipient box st') :
    CellUnsealSpec (cellProjUnseal st.kernel.bal c asset) (cellProjUnseal st'.kernel.bal c asset) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  -- UnsealSpec: guard ∧ caps ∧ log ∧ accounts ∧ cell ∧ escrows ∧ nullifiers ∧ revoked ∧
  --             commitments ∧ bal ∧ … — `bal` is the 10th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_unseal`** — a satisfying run of the runnable descriptor encoding
ANY cell of a committed unseal agrees with the executor's per-cell post-state: the descriptor's pinned
(frozen) post-state equals the executor's frozen cell on every state-block column. The cap-grant is
out-of-IR (reported as the §IR flag). -/
theorem descriptor_agrees_with_executor_unseal
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (pid : Nat) (actor recipient c : CellId) (box : SealedBoxRecord)
    (asset : AssetId) (pre post : CellState)
    (hpre : pre = cellProjUnseal st.kernel.bal c asset)
    (henc : RowEncodesUnseal env pre post)
    (hsat : satisfiedVm hash unsealVmDescriptor env true true)
    (hspec : UnsealSpec st pid actor recipient box st') :
    post.balLo = (cellProjUnseal st'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjUnseal st'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjUnseal st'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjUnseal st'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjUnseal st'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := unsealDescriptor_full_sound hash env pre post henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_unseal_freeze st st' pid actor recipient c box asset hspec
  subst hpre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — THE CAP-GRANT leg the per-row circuit does NOT enforce (honest, LOAD-BEARING). -/

/-- **`unseal_cap_grant_is_out_of_row` — the honest finding (LOAD-BEARING leg out-of-IR).** A committed
unseal GRANTS the box's `payload` cap into `recipient`'s c-list (`unseal_grants_sealed_cap`). This
cap-grant — the ACTUAL effect, moving a CAPABILITY through the box — is a universe-A property over the
`caps` side-table, NOT bound by any per-row gate or hash-site of `unsealVmDescriptor` (whose hash-sites
absorb only the 13 frozen state-block columns, none of `caps`). So the runnable descriptor does NOT
bind the grant or `payload` into `state_commit`: the §IR-extension flag, surfaced as a theorem. -/
theorem unseal_cap_grant_is_out_of_row (st st' : RecChainedState) (pid : Nat)
    (actor recipient : CellId) (box : SealedBoxRecord)
    (hspec : UnsealSpec st pid actor recipient box st') :
    box.payload ∈ st'.kernel.caps recipient :=
  unseal_grants_sealed_cap st pid actor recipient box st' hspec

/-! ## §12 — NON-VACUITY: a concrete frozen unseal row realizes the intent; a minting one rejected. -/

/-- A concrete unseal row: every state-block column frozen (bal_lo 100 → 100, nonce 5 → 5, frame 0). -/
def goodUnsealRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_UNSEAL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodUnsealRow` REALIZES the unseal freeze intent. -/
theorem goodUnsealRow_realizes_intent : UnsealRowIntent goodUnsealRow := by
  unfold UnsealRowIntent goodUnsealRow
  simp only [sbCol, saCol, SEL_UNSEAL, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 7) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have f1 : (54 + (3 + i) = 7) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED unseal row: `goodUnsealRow` with the post-`bal_lo` minted to `999`. -/
def badUnsealRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodUnsealRow.loc v
  nxt := goodUnsealRow.nxt
  pub := goodUnsealRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badUnsealRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badUnsealRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badUnsealRow false false := by
  apply unsealVm_rejects_balance_mint
  simp only [badUnsealRow, goodUnsealRow, sbCol, saCol, SEL_UNSEAL, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard unsealVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard unsealVmDescriptor.hashSites.length == 4
#guard unsealVmDescriptor.traceWidth == 186

#assert_axioms unsealVm_faithful
#assert_axioms unsealVm_rejects_wrong_output
#assert_axioms unsealVm_rejects_balance_mint
#assert_axioms intent_to_cellUnsealSpec
#assert_axioms unsealDescriptor_full_sound
#assert_axioms unsealDescriptor_commit_binds_state
#assert_axioms unify_unseal_freeze
#assert_axioms descriptor_agrees_with_executor_unseal
#assert_axioms unseal_cap_grant_is_out_of_row
#assert_axioms goodUnsealRow_realizes_intent
#assert_axioms badUnsealRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitUnseal
