/-
# Dregg2.Circuit.Emit.EffectVmEmitSeal — the seal (seal-a-cap-into-a-box) effect's concrete EffectVM
circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/sealA.lean`, `Spec/sealboxoperations.lean`) carries the FULL-state soundness
`execFullA_seal_iff_spec ⇒ SealSpec`: a committed seal PREPENDS a `SealedBoxRecord ⟨pid, actor,
payload⟩` onto the `sealedBoxes` holding-store, advances the chained `log`, and is otherwise TOTALLY
NEUTRAL — balance-neutral (`seal_preserves_balances`: `recTotal`/accounts/cell unchanged, `bal`
frozen) and FREEZES the other 15 kernel fields (INCLUDING `caps` — the sealer KEEPS the cap; it is
COPIED into the box, the documented FRAME-GAP). Guard: the actor HOLDS the sealer cap for `pid` ∧
HOLDS the `payload` cap.

## THE KEY STRUCTURAL FACT (and the honest IR boundary)

A seal touches NEITHER the per-asset `bal` ledger NOR any per-cell state-block column — it only
prepends a box into the `sealedBoxes` SIDE-TABLE (a structure the EffectVM 14-column state block has
NO column for, absorbed by NO GROUP-4 hash-site). So, projected onto ONE EffectVM cell's state block,
a seal is a PURE FREEZE: every state-block column UNCHANGED (`state_after = state_before`), and the
published `state_commit` is the genuine digest of the FROZEN after-state.

What the IR DOES support is exactly this FREEZE + the commitment binding of the frozen block. This is
the conservation / balance-neutrality tooth — genuine (a row claiming a seal but mutating any cell is
UNSAT).

## THE IR-EXTENSION FLAG (the box-store prepend — the LOAD-BEARING leg, out-of-IR)

The actual effect — `sealedBoxes := ⟨pid, actor, payload⟩ :: sealedBoxes` — is a PREPEND into the
sealed-box side-table binding a CAPABILITY `payload`. The EffectVM 14-column block has NO sealed-box-
root column, and the GROUP-4 hash-sites absorb none of `sealedBoxes`. So the per-row circuit CANNOT
bind, or even witness, the box or its `payload`.

  ⇒ **needs IR extension: a sealedBoxes-store-root column in the EffectVM state block absorbed by a
     new hash-site, plus param columns carrying `pid`/`payload`, so the box prepend is bound into the
     published `state_commit`.** The seal-cap-held / payload-held guard is likewise out-of-row (no
     cap-table column on the EffectVM row). Reported, not papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sealboxoperations

namespace Dregg2.Circuit.Emit.EffectVmEmitSeal

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

/-! ## §0 — The seal selector. -/

/-- The seal-box selector column index. -/
def SEL_SEAL : Nat := 6

/-- The seal row is a seal row: `s_seal = 1`, `s_noop = 0`. -/
def IsSealRow (env : VmRowEnv) : Prop :=
  env.loc SEL_SEAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (WHOLE state-block FREEZE). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — sealing moves no value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted descriptor. -/

/-- The seal-box AIR identity. -/
def sealVmAirName : String := "dregg-effectvm-seal-v1"

/-- The per-row gates: WHOLE state block frozen. -/
def sealRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`sealVmDescriptor`** — the seal effect's concrete EffectVM circuit: the per-row WHOLE-block
freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash sites
(REUSED — binding the frozen block) and the 2 balance-limb range checks. -/
def sealVmDescriptor : EffectVmDescriptor :=
  { name := sealVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := sealRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT: the WHOLE state block frozen. -/

/-- **`SealRowIntent env`** — the intended seal move on the row `env.loc`: every state-block column
UNCHANGED. The box-store prepend + held-cap guard are out-of-row (the §IR flags). -/
def SealRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the freeze intent. -/

/-- **`sealVm_faithful`.** On a seal row, the emitted descriptor's per-row gates all hold IFF
`SealRowIntent` holds — the gates pin EXACTLY the whole-block freeze. -/
theorem sealVm_faithful (env : VmRowEnv) :
    (∀ c ∈ sealRowGates, c.holdsVm env false false) ↔ SealRowIntent env := by
  unfold sealRowGates gFieldPassAll SealRowIntent
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

/-! ## §5 — ANTI-GHOST: a row that MUTATES any state-block cell on a seal is rejected. -/

/-- **Anti-ghost (general).** A seal row whose state block is NOT frozen does NOT satisfy the per-row
gates — the conservation tooth. -/
theorem sealVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SealRowIntent env) :
    ¬ (∀ c ∈ sealRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((sealVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A seal row whose post-`bal_lo` is NOT the pre-`bal_lo` (value
forged on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem sealVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesSeal env pre post` ties the row's state-block columns to a `(pre, post)` cell transition
(no params — a seal carries pid/payload off-block). -/
def RowEncodesSeal (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellSealSpec pre post`** — the per-cell FULL-state seal spec: the WHOLE cell state is FROZEN.
This is the EffectVM-row projection of `SealSpec`'s balance-neutrality + per-cell frame freeze (the
box-store prepend is off-block — the §IR flag). -/
def CellSealSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesSeal`, `SealRowIntent` IS the structured `CellSealSpec`. -/
theorem intent_to_cellSealSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesSeal env pre post) (hint : SealRowIntent env) :
    CellSealSpec pre post := by
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

/-- **`sealDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under `RowEncodesSeal`,
forces the structured per-cell FREEZE `CellSealSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem sealDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesSeal env pre post)
    (hsat : satisfiedVm hash sealVmDescriptor env true true) :
    CellSealSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ sealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ sealVmDescriptor.constraints := by
      unfold sealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold sealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (sealVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSealSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ sealVmDescriptor.constraints := by
      unfold sealVmDescriptor
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

/-- **`sealDescriptor_commit_binds_state`** — two descriptor-satisfying seal rows publishing the SAME
`NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep `NEW_COMMIT` while
tampering any absorbed cell of the (frozen) post-state. -/
theorem sealDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash sealVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash sealVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash sealVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ sealVmDescriptor.constraints := by
        unfold sealVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A: `CellSealSpec` IS `SealSpec`'s per-cell frame image.

`execFullA_seal_iff_spec ⇒ SealSpec` carries balance-neutrality (`bal' = bal`). We project ONE cell
into the keystone `CellState` and prove the projection of ANY cell satisfies `CellSealSpec` EXACTLY
(all FROZEN). The box-store prepend is the §IR-extension flag, reported below as out-of-row. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId)
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Spec.SealBoxOperations
  (SealSpec execFullA_seal_iff_spec sealedBoxPrepend seal_box_binds_payload)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb; the other EffectVM limbs are `0`, frozen). -/
def cellProjSeal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_seal_freeze`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`SealSpec` post-state, satisfies the keystone's `CellSealSpec` EXACTLY: `balLo` FROZEN (`bal' = bal`,
balance-neutral); the rest frozen (`0 = 0`). So `CellSealSpec` IS `SealSpec`'s per-cell frame image —
NOT a fourth spec. -/
theorem unify_seal_freeze (st st' : RecChainedState) (pid : Nat) (actor c : CellId)
    (payload : Cap) (asset : AssetId) (hspec : SealSpec st pid actor payload st') :
    CellSealSpec (cellProjSeal st.kernel.bal c asset) (cellProjSeal st'.kernel.bal c asset) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  -- SealSpec: guard ∧ sealedBoxes ∧ log ∧ accounts ∧ cell ∧ caps ∧ escrows ∧ nullifiers ∧ revoked ∧
  --           commitments ∧ bal ∧ … — `bal` is the 11th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_seal`** — a satisfying run of the runnable descriptor encoding
ANY cell of a committed seal agrees with the executor's per-cell post-state: the descriptor's pinned
(frozen) post-state equals the executor's frozen cell on every state-block column. The box-store
prepend is out-of-IR (reported as the §IR flag). -/
theorem descriptor_agrees_with_executor_seal
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (pid : Nat) (actor c : CellId) (payload : Cap) (asset : AssetId)
    (pre post : CellState)
    (hpre : pre = cellProjSeal st.kernel.bal c asset)
    (henc : RowEncodesSeal env pre post)
    (hsat : satisfiedVm hash sealVmDescriptor env true true)
    (hspec : SealSpec st pid actor payload st') :
    post.balLo = (cellProjSeal st'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjSeal st'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjSeal st'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjSeal st'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjSeal st'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := sealDescriptor_full_sound hash env pre post henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ := unify_seal_freeze st st' pid actor c payload asset hspec
  subst hpre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — THE BOX-STORE PREPEND leg the per-row circuit does NOT enforce (honest, LOAD-BEARING). -/

/-- **`seal_box_prepend_is_out_of_row` — the honest finding (LOAD-BEARING leg out-of-IR).** A committed
seal's `sealedBoxes` store gains the box `⟨pid, actor, payload⟩` at its head (`seal_box_binds_payload`).
This box prepend — the ACTUAL effect, binding the CAPABILITY `payload` — is a universe-A property over
the `sealedBoxes` side-table, NOT bound by any per-row gate or hash-site of `sealVmDescriptor` (whose
hash-sites absorb only the 13 frozen state-block columns, none of `sealedBoxes`). So the runnable
descriptor does NOT bind the box or `payload` into `state_commit`: the §IR-extension flag, surfaced as
a theorem. -/
theorem seal_box_prepend_is_out_of_row (st st' : RecChainedState) (pid : Nat) (actor : CellId)
    (payload : Cap) (hspec : SealSpec st pid actor payload st') :
    st'.kernel.sealedBoxes.head? = some { pairId := pid, sealer := actor, payload := payload } :=
  seal_box_binds_payload st pid actor payload st' hspec

/-! ## §12 — NON-VACUITY: a concrete frozen seal row realizes the intent; a minting one rejected. -/

/-- A concrete seal row: every state-block column frozen (bal_lo 100 → 100, nonce 5 → 5, frame 0). -/
def goodSealRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_SEAL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodSealRow` REALIZES the seal freeze intent. -/
theorem goodSealRow_realizes_intent : SealRowIntent goodSealRow := by
  unfold SealRowIntent goodSealRow
  simp only [sbCol, saCol, SEL_SEAL, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 6) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have f1 : (54 + (3 + i) = 6) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED seal row: `goodSealRow` with the post-`bal_lo` minted to `999`. -/
def badSealRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodSealRow.loc v
  nxt := goodSealRow.nxt
  pub := goodSealRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSealRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badSealRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badSealRow false false := by
  apply sealVm_rejects_balance_mint
  simp only [badSealRow, goodSealRow, sbCol, saCol, SEL_SEAL, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard sealVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard sealVmDescriptor.hashSites.length == 4
#guard sealVmDescriptor.traceWidth == 186

#assert_axioms sealVm_faithful
#assert_axioms sealVm_rejects_wrong_output
#assert_axioms sealVm_rejects_balance_mint
#assert_axioms intent_to_cellSealSpec
#assert_axioms sealDescriptor_full_sound
#assert_axioms sealDescriptor_commit_binds_state
#assert_axioms unify_seal_freeze
#assert_axioms descriptor_agrees_with_executor_seal
#assert_axioms seal_box_prepend_is_out_of_row
#assert_axioms goodSealRow_realizes_intent
#assert_axioms badSealRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSeal
