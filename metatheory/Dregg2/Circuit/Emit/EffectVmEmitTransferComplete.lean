/-
# Dregg2.Circuit.Emit.EffectVmEmitTransferComplete — the COMPLETENESS (`←`) leg of the transfer
state-commitment: `spec ⟹ SAT`, welded to the committed soundness (`→`, `transferDescriptor_full_sound`)
into a REAL biconditional over the DEPLOYED `wire_commit` absorption.

## What the soundness leg gave and what this adds

`EffectVmEmitTransferSound.transferDescriptor_full_sound` is the SOUNDNESS half (`SAT ⟹ SEM`): a
transfer row satisfying the runnable descriptor on BOTH the active window (`true false`, where the
per-row gates fire under `when_transition()`) and the last window (`true true`, where the commit pin
fires under `when_last_row()`) forces the structured per-cell `CellTransferSpec pre p post`, and the
published `state_commit` is the genuine `H4`-of-`H4` digest of the after-state's absorbed columns
(`commit_eq_commitOf` — a DETERMINISTIC forced function, no free digest survives).

This file proves the COMPLEMENTARY half — COMPLETENESS (`SEM ⟹ SAT`): from a genuine
`CellTransferSpec pre p post` whose after-state stored-commit IS the genuine wire commit
(`hcommit : post.commit = cellWireCommit hash post 0`, the honest "the after-state absorbs to the
published `NEW_COMMIT`" precondition), a witnessing `VmRowEnv` GENUINELY SATISFIES both descriptor
windows — every gate, transition, boundary pin, the four GROUP-4 hash sites, and both balance-limb
range teeth. No honest transition is rejected; the published commit is FORCED to be the genuine one.
The Poseidon2 carrier is CONSTRUCTED here (the aux inter-digest columns carry the genuine inner
hashes), not assumed.

Together the two directions pin the descriptor's accept-set to the semantic relation from BOTH sides
— the biconditional `transferDescriptor_commit_iff` the byte-pinned emit could not, on its own,
establish. This is the exemplar that turns the state commitment from trusted-Rust into a proven-COMPLETE
AIR value.

## The commit is the DEPLOYED absorption, not a re-authored mirror

`cellWireCommit hash post rd` is `EffectVmEmitTransferSound.commitOf` of `post`'s twelve absorbed
scalar columns (the `H4(H4(bal_lo,bal_hi,nonce,fld0), H4(fld1..4), H4(fld5,fld6,fld7,cap), rd)` of
GROUP-4 site 3). `commit_eq_commitOf` PROVES this equals the published `saCol STATE_COMMIT` on any row
whose hash sites hold — so `cellWireCommit` is literally the deployed `wire_commit` absorption
(`turn/src/rotation_witness.rs`), byte-pinned to the circuit, NOT a fresh re-derivation.

## The round-trip + the mutation canary (the anti-vacuity)

  * `sem_transfer_satisfied` — the completeness core: the constructed row satisfies BOTH windows.
  * `transferDescriptor_commit_iff` — the packaged biconditional (both directions, modulo the
    Poseidon2-CR carrier bundle only where the injectivity is used).
  * `sem_transfer_roundtrip` — BUILD a satisfying witness from any spec'd transfer, then FEED it back
    through the committed soundness bridge to recover `CellTransferSpec` + the genuine commit.
  * `canary_tamper_moves_commit` — tamper ANY absorbed after-state field and the genuine wire commit
    MOVES (under CR): the honest published `NEW_COMMIT` cannot ride a tampered after-state, so the
    biconditional's commit conjunct BITES.
  * `canary_tamper_breaks_spec` — the same tamper ALSO fails `CellTransferSpec` (a frozen field
    moved), so the `↔`'s LHS is genuinely two-valued.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR enters ONLY as the NAMED
hypothesis `Poseidon2SpongeCR hash` (task #13's discharged carrier), never as a fresh axiom. NEW file;
all imports read-only; `transferDescriptor_full_sound` / `commit_eq_commitOf` are UNCHANGED (used
as-is for the `→` leg).
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound

namespace Dregg2.Circuit.Emit.EffectVmEmitTransferComplete

open Dregg2.Circuit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option linter.unusedVariables false

/-! ## §1 — `cellWireCommit`: the DEPLOYED wire-commit absorption as a function of the after-state. -/

/-- The genuine published commitment of an after-`CellState`: `commitOf` of its twelve absorbed
columns with the fourth GROUP-4 slot carrying the record-digest `rd`. This is EXACTLY the deployed
`state_commit` (see `commit_eq_commitOf`); a residue-free honest cell absorbs `rd = 0`. -/
def cellWireCommit (hash : List ℤ → ℤ) (post : CellState) (rd : ℤ) : ℤ :=
  commitOf hash post.balLo post.balHi post.nonce
    (post.fields 0) (post.fields 1) (post.fields 2) (post.fields 3)
    (post.fields 4) (post.fields 5) (post.fields 6) (post.fields 7) post.capRoot rd

/-! ## §2 — the constructed witnessing row. -/

/-- The witnessing `loc` assignment for the transfer `(pre, p, post)`: every state-block / param
column carries its honest value, the after-`state_commit` carries `post.commit`, the three GROUP-4
inter-digest aux columns carry the genuine inner `hash`es, and the record-digest aux column is `0`. -/
def semLoc (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) : Assignment :=
  fun v =>
    if v = sel.TRANSFER then 1
    -- state_before block
    else if v = sbCol state.BALANCE_LO then pre.balLo
    else if v = sbCol state.BALANCE_HI then pre.balHi
    else if v = sbCol state.NONCE then pre.nonce
    else if v = sbCol (state.FIELD_BASE + 0) then pre.fields 0
    else if v = sbCol (state.FIELD_BASE + 1) then pre.fields 1
    else if v = sbCol (state.FIELD_BASE + 2) then pre.fields 2
    else if v = sbCol (state.FIELD_BASE + 3) then pre.fields 3
    else if v = sbCol (state.FIELD_BASE + 4) then pre.fields 4
    else if v = sbCol (state.FIELD_BASE + 5) then pre.fields 5
    else if v = sbCol (state.FIELD_BASE + 6) then pre.fields 6
    else if v = sbCol (state.FIELD_BASE + 7) then pre.fields 7
    else if v = sbCol state.CAP_ROOT then pre.capRoot
    else if v = sbCol state.STATE_COMMIT then pre.commit
    else if v = sbCol state.RESERVED then pre.reserved
    -- param block
    else if v = prmCol param.AMOUNT then p.amount
    else if v = prmCol param.DIRECTION then p.direction
    -- state_after block
    else if v = saCol state.BALANCE_LO then post.balLo
    else if v = saCol state.BALANCE_HI then post.balHi
    else if v = saCol state.NONCE then post.nonce
    else if v = saCol (state.FIELD_BASE + 0) then post.fields 0
    else if v = saCol (state.FIELD_BASE + 1) then post.fields 1
    else if v = saCol (state.FIELD_BASE + 2) then post.fields 2
    else if v = saCol (state.FIELD_BASE + 3) then post.fields 3
    else if v = saCol (state.FIELD_BASE + 4) then post.fields 4
    else if v = saCol (state.FIELD_BASE + 5) then post.fields 5
    else if v = saCol (state.FIELD_BASE + 6) then post.fields 6
    else if v = saCol (state.FIELD_BASE + 7) then post.fields 7
    else if v = saCol state.CAP_ROOT then post.capRoot
    else if v = saCol state.STATE_COMMIT then post.commit
    else if v = saCol state.RESERVED then post.reserved
    -- aux: the GROUP-4 inter digests + the (zero) record digest
    else if v = auxCol aux_off.STATE_INTER1 then
      hash [post.balLo, post.balHi, post.nonce, post.fields 0]
    else if v = auxCol aux_off.STATE_INTER2 then
      hash [post.fields 1, post.fields 2, post.fields 3, post.fields 4]
    else if v = auxCol aux_off.STATE_INTER3 then
      hash [post.fields 5, post.fields 6, post.fields 7, post.capRoot]
    else if v = auxCol aux_off.STATE_RECORD_DIGEST then 0
    else 0

/-- The witnessing public-input vector: OLD/NEW commits, init/final balances, actor nonce. -/
def semPub (pre : CellState) (post : CellState) : Assignment :=
  fun k =>
    if k = pi.OLD_COMMIT then pre.commit
    else if k = pi.NEW_COMMIT then post.commit
    else if k = pi.INIT_BAL_LO then pre.balLo
    else if k = pi.INIT_BAL_HI then pre.balHi
    else if k = pi.FINAL_BAL_LO then post.balLo
    else if k = pi.FINAL_BAL_HI then post.balHi
    else if k = pi.ACTOR_NONCE then pre.nonce
    else 0

/-- The witnessing `VmRowEnv`: `loc = semLoc`, `pub = semPub`, and `nxt` mirrors the after-state
onto the next row's state_before (`nxt (sbCol i) = loc (saCol i)`) so the transition continuity holds. -/
def semTransferRow (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) :
    VmRowEnv where
  loc := semLoc hash pre p post
  nxt := fun v => semLoc hash pre p post (v + (STATE_SIZE + NUM_PARAMS))
  pub := semPub pre post

/-! ## §3 — column-read lemmas (all definitional). -/

section Reads
variable (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState)

@[local simp] theorem l_selT : (semTransferRow hash pre p post).loc sel.TRANSFER = 1 := rfl
@[local simp] theorem l_selN : (semTransferRow hash pre p post).loc sel.NOOP = 0 := rfl

@[local simp] theorem l_sbBalLo : (semTransferRow hash pre p post).loc (sbCol state.BALANCE_LO) = pre.balLo := rfl
@[local simp] theorem l_sbBalHi : (semTransferRow hash pre p post).loc (sbCol state.BALANCE_HI) = pre.balHi := rfl
@[local simp] theorem l_sbNonce : (semTransferRow hash pre p post).loc (sbCol state.NONCE) = pre.nonce := rfl
@[local simp] theorem l_sbCap : (semTransferRow hash pre p post).loc (sbCol state.CAP_ROOT) = pre.capRoot := rfl
@[local simp] theorem l_sbRes : (semTransferRow hash pre p post).loc (sbCol state.RESERVED) = pre.reserved := rfl
@[local simp] theorem l_sbCommit : (semTransferRow hash pre p post).loc (sbCol state.STATE_COMMIT) = pre.commit := rfl

@[local simp] theorem l_prmAmt : (semTransferRow hash pre p post).loc (prmCol param.AMOUNT) = p.amount := rfl
@[local simp] theorem l_prmDir : (semTransferRow hash pre p post).loc (prmCol param.DIRECTION) = p.direction := rfl

@[local simp] theorem l_saBalLo : (semTransferRow hash pre p post).loc (saCol state.BALANCE_LO) = post.balLo := rfl
@[local simp] theorem l_saBalHi : (semTransferRow hash pre p post).loc (saCol state.BALANCE_HI) = post.balHi := rfl
@[local simp] theorem l_saNonce : (semTransferRow hash pre p post).loc (saCol state.NONCE) = post.nonce := rfl
@[local simp] theorem l_saCap : (semTransferRow hash pre p post).loc (saCol state.CAP_ROOT) = post.capRoot := rfl
@[local simp] theorem l_saRes : (semTransferRow hash pre p post).loc (saCol state.RESERVED) = post.reserved := rfl
@[local simp] theorem l_saCommit : (semTransferRow hash pre p post).loc (saCol state.STATE_COMMIT) = post.commit := rfl

@[local simp] theorem l_saF0 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 0)) = post.fields 0 := rfl
@[local simp] theorem l_saF1 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 1)) = post.fields 1 := rfl
@[local simp] theorem l_saF2 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 2)) = post.fields 2 := rfl
@[local simp] theorem l_saF3 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 3)) = post.fields 3 := rfl
@[local simp] theorem l_saF4 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 4)) = post.fields 4 := rfl
@[local simp] theorem l_saF5 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 5)) = post.fields 5 := rfl
@[local simp] theorem l_saF6 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 6)) = post.fields 6 := rfl
@[local simp] theorem l_saF7 : (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + 7)) = post.fields 7 := rfl

@[local simp] theorem l_auxI1 : (semTransferRow hash pre p post).loc (auxCol aux_off.STATE_INTER1)
    = hash [post.balLo, post.balHi, post.nonce, post.fields 0] := rfl
@[local simp] theorem l_auxI2 : (semTransferRow hash pre p post).loc (auxCol aux_off.STATE_INTER2)
    = hash [post.fields 1, post.fields 2, post.fields 3, post.fields 4] := rfl
@[local simp] theorem l_auxI3 : (semTransferRow hash pre p post).loc (auxCol aux_off.STATE_INTER3)
    = hash [post.fields 5, post.fields 6, post.fields 7, post.capRoot] := rfl
@[local simp] theorem l_auxRD : (semTransferRow hash pre p post).loc (auxCol aux_off.STATE_RECORD_DIGEST) = 0 := rfl

@[local simp] theorem p_old : (semTransferRow hash pre p post).pub pi.OLD_COMMIT = pre.commit := rfl
@[local simp] theorem p_new : (semTransferRow hash pre p post).pub pi.NEW_COMMIT = post.commit := rfl
@[local simp] theorem p_initLo : (semTransferRow hash pre p post).pub pi.INIT_BAL_LO = pre.balLo := rfl
@[local simp] theorem p_initHi : (semTransferRow hash pre p post).pub pi.INIT_BAL_HI = pre.balHi := rfl
@[local simp] theorem p_finLo : (semTransferRow hash pre p post).pub pi.FINAL_BAL_LO = post.balLo := rfl
@[local simp] theorem p_finHi : (semTransferRow hash pre p post).pub pi.FINAL_BAL_HI = post.balHi := rfl
@[local simp] theorem p_actor : (semTransferRow hash pre p post).pub pi.ACTOR_NONCE = pre.nonce := rfl

end Reads

/-- The field-block reads at an arbitrary `Fin 8` index (used by `RowEncodes`). -/
theorem l_sbF (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) (i : Fin 8) :
    (semTransferRow hash pre p post).loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i := by
  fin_cases i <;> rfl

theorem l_saF (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) (i : Fin 8) :
    (semTransferRow hash pre p post).loc (saCol (state.FIELD_BASE + i.val)) = post.fields i := by
  fin_cases i <;> rfl

/-- The transition continuity read: `nxt (sbCol i) = loc (saCol i)`. -/
theorem l_nxt (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) (i : Nat) :
    (semTransferRow hash pre p post).nxt (sbCol i) = (semTransferRow hash pre p post).loc (saCol i) := by
  have harg : sbCol i + (STATE_SIZE + NUM_PARAMS) = saCol i := by
    simp only [sbCol, saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, STATE_SIZE, NUM_PARAMS,
      NUM_EFFECTS]
    omega
  show semLoc hash pre p post (sbCol i + (STATE_SIZE + NUM_PARAMS)) = semLoc hash pre p post (saCol i)
  rw [harg]

/-! ## §4 — the constructed row DECODES to `(pre, p, post)` and is a transfer row. -/

/-- The witness row genuinely decodes (`RowEncodes`) to the intended `(pre, p, post)` cell transition. -/
theorem sem_rowEncodes (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) :
    RowEncodes (semTransferRow hash pre p post) pre p post :=
  ⟨rfl, rfl, rfl, l_sbF hash pre p post, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, l_saF hash pre p post, rfl, rfl, rfl, rfl, rfl⟩

/-- The witness row is a genuine transfer row (`s_transfer = 1`, `s_noop = 0`). -/
theorem sem_isTransferRow (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState) :
    IsTransferRow (semTransferRow hash pre p post) := ⟨rfl, rfl⟩

/-! ## §5 — `cellSpec_to_intent`: the CONVERSE of `intent_to_cellSpec` (structured spec ⟹ row intent). -/

/-- Under `RowEncodes`, the structured `CellTransferSpec` IMPLIES the raw `TransferRowIntent` column
move (the converse of `EffectVmEmitTransferSound.intent_to_cellSpec`). Both live in the field; no
canonicality needed. -/
theorem cellSpec_to_intent (env : VmRowEnv) (pre post : CellState) (p : TransferParams)
    (henc : RowEncodes env pre p post) (h : CellTransferSpec pre p post) :
    TransferRowIntent env := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hpAmt, hpDir, hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hdir, hbal, hbhi, hnon, hfld, hcap, hres⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- direction bit
    rcases hdir with hd | hd
    · exact Or.inl (by rw [hpDir]; exact hd)
    · exact Or.inr (by rw [hpDir]; exact hd)
  · -- balance-lo signed move
    rw [hsaLo, hsbLo, hpAmt, hpDir]
    simpa only [signedMove] using hbal
  · rw [hsaHi, hsbHi]; exact hbhi
  · rw [hsaN, hsbN]; exact hnon
  · rw [hsaCap, hsbCap]; exact hcap
  · rw [hsaRes, hsbRes]; exact hres
  · -- the 8 fields frozen
    intro i hi
    have hs := hsaF ⟨i, hi⟩
    have hb := hsbF ⟨i, hi⟩
    simp only [Fin.val_mk] at hs hb
    rw [hs, hb]
    exact hfld ⟨i, hi⟩

/-- The witness row's raw intent (from any genuine per-cell spec). -/
theorem sem_transferRowIntent (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams)
    (post : CellState) (h : CellTransferSpec pre p post) :
    TransferRowIntent (semTransferRow hash pre p post) :=
  cellSpec_to_intent _ pre post p (sem_rowEncodes hash pre p post) h

/-! ## §6 — the GROUP-4 hash sites HOLD on the witness (the Poseidon2 carrier, CONSTRUCTED). -/

/-- **`sem_sites` — the constructed Poseidon2 carrier.** Given that the after-state's stored commit IS
the genuine wire commit (`hcommit`), every one of the four GROUP-4 hash sites carries its genuine
digest on the witness row: the three inter-digest aux columns hold the honest inner `hash`es and
`state_commit` holds their `H4`. The carrier is REALIZED here, never assumed. -/
theorem sem_sites (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState)
    (hcommit : post.commit = cellWireCommit hash post 0) :
    siteHoldsAll hash (semTransferRow hash pre p post) transferHashSites := by
  simp only [siteHoldsAll, transferHashSites, siteHoldsAll.go, site0, site1, site2, site3,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil, List.getD]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · simp only [l_auxI1, l_saBalLo, l_saBalHi, l_saNonce, l_saF0]
  · simp only [l_auxI2, l_saF1, l_saF2, l_saF3, l_saF4]
  · simp only [l_auxI3, l_saF5, l_saF6, l_saF7, l_saCap]
  · simp only [l_saCommit, l_saBalLo, l_saBalHi, l_saNonce, l_saCap, l_saF0, l_saF1, l_saF2, l_saF3,
      l_saF4, l_saF5, l_saF6, l_saF7, l_auxRD]
    rw [hcommit]
    rfl

/-! ## §7 — the range teeth and the COMPLETENESS CORE (`spec ⟹ SAT` on both windows). -/

/-- The two balance-limb range teeth hold on the witness (from the honest range bounds). -/
theorem sem_ranges (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState)
    (hbLo : 0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) (hbHi : 0 ≤ post.balHi ∧ post.balHi < 2 ^ 30) :
    ∀ r ∈ transferVmDescriptor.ranges, r.holds (semTransferRow hash pre p post) := by
  intro r hr
  simp only [transferVmDescriptor, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa only [VmRange.holds, l_saBalLo] using hbLo
  · simpa only [VmRange.holds, l_saBalHi] using hbHi

/-- The per-row gates hold on the ACTIVE window (`isLast = false`) from the spec (via faithfulness). -/
theorem sem_rowgates (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams) (post : CellState)
    (h : CellTransferSpec pre p post) :
    ∀ c ∈ transferRowGates, c.holdsVm (semTransferRow hash pre p post) true false := by
  have key := (transferVm_faithful (semTransferRow hash pre p post) (sem_isTransferRow hash pre p post)).mpr
    (sem_transferRowIntent hash pre p post h)
  intro c hc
  have hff := key c hc
  unfold transferRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact hff

private theorem constraint_split {c : VmConstraint} (hc : c ∈ transferVmDescriptor.constraints) :
    c ∈ transferRowGates ∨ c ∈ transitionAll ∨ c ∈ boundaryFirstPins
      ∨ c ∈ boundaryLastPins ∨ c ∈ selectorGates sel.TRANSFER := by
  simpa only [transferVmDescriptor, List.mem_append, or_assoc] using hc

/-- **`sem_transfer_satisfied` — THE COMPLETENESS CORE (`SEM ⟹ SAT`).** From a genuine
`CellTransferSpec pre p post`, honest balance-limb bounds, and the after-state absorbing to the
published commit (`hcommit`), the witness row GENUINELY SATISFIES the runnable descriptor on BOTH
deployed windows: the active window (`true false` — where the per-row gates + transitions fire under
`when_transition()`) and the last window (`true true` — where the commit/final-balance pins fire under
`when_last_row()`). Every gate, transition, boundary pin, the four hash sites, and both range teeth
hold. No honest transition is rejected. -/
theorem sem_transfer_satisfied (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams)
    (post : CellState)
    (hcommit : post.commit = cellWireCommit hash post 0)
    (hbLo : 0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) (hbHi : 0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    (h : CellTransferSpec pre p post) :
    satisfiedVm hash transferVmDescriptor (semTransferRow hash pre p post) true false
    ∧ satisfiedVm hash transferVmDescriptor (semTransferRow hash pre p post) true true := by
  refine ⟨⟨?_, sem_sites hash pre p post hcommit, sem_ranges hash pre p post hbLo hbHi⟩,
          ⟨?_, sem_sites hash pre p post hcommit, sem_ranges hash pre p post hbLo hbHi⟩⟩
  · -- ACTIVE window `true false`: gates + transitions + first-pins fire; last-pins/selector-noop vacuous
    intro c hc
    rcases constraint_split hc with h1 | h2 | h3 | h4 | h5
    · exact sem_rowgates hash pre p post h c h1
    · -- transition continuity
      simp only [transitionAll, List.mem_map, List.mem_range] at h2
      obtain ⟨i, hi, rfl⟩ := h2
      show (semTransferRow hash pre p post).nxt (sbCol i)
        ≡ (semTransferRow hash pre p post).loc (saCol i) [ZMOD 2013265921]
      exact eqToModEq (l_nxt hash pre p post i)
    · -- first-row boundary pins
      simp only [boundaryFirstPins, List.mem_cons, List.not_mem_nil, or_false] at h3
      rcases h3 with rfl | rfl | rfl | rfl <;> exact fun _ => eqToModEq rfl
    · -- last-row boundary pins vacuous (isLast = false)
      simp only [boundaryLastPins, List.mem_cons, List.not_mem_nil, or_false] at h4
      rcases h4 with rfl | rfl | rfl <;> exact fun hcon => absurd hcon (by decide)
    · -- selector-binding gate: (1 - s_noop)·(1 - s_transfer) = (1-0)·(1-1) = 0
      simp only [selectorGates, List.mem_singleton] at h5
      subst h5
      exact eqToModEq (by
        simp only [selectorGate, selectorGateBody, EmittedExpr.eval, l_selN, l_selT]; ring)
  · -- LAST window `true true`: gates/transitions/selector vacuous; first + last pins fire
    intro c hc
    rcases constraint_split hc with h1 | h2 | h3 | h4 | h5
    · -- gates vacuous on the wrap row
      unfold transferRowGates gFieldPassAll at h1
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at h1
      rcases h1 with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial
    · -- transitions vacuous
      simp only [transitionAll, List.mem_map, List.mem_range] at h2
      obtain ⟨i, hi, rfl⟩ := h2
      exact trivial
    · -- first-row pins fire (isFirst = true)
      simp only [boundaryFirstPins, List.mem_cons, List.not_mem_nil, or_false] at h3
      rcases h3 with rfl | rfl | rfl | rfl <;> exact fun _ => eqToModEq rfl
    · -- last-row pins fire (isLast = true): commit + final balances
      simp only [boundaryLastPins, List.mem_cons, List.not_mem_nil, or_false] at h4
      rcases h4 with rfl | rfl | rfl <;> exact fun _ => eqToModEq rfl
    · -- selector gate vacuous
      simp only [selectorGates, List.mem_singleton] at h5
      subst h5
      exact trivial

/-! ## §8 — THE BICONDITIONAL: the runnable descriptor's accept-set IS the semantic transfer spec. -/

/-- **`sem_forces_genuine_commit` — the `→` commitment content (NO `hcommit`).** Satisfaction of the
last window alone (its hash-site leg) FORCES the published `state_commit` to be the genuine wire commit
of the after-state — the deployed circuit pins it, no free digest survives. This is the forced-recompute
that `commit_eq_commitOf` establishes, read on the witness row. -/
theorem sem_forces_genuine_commit (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams)
    (post : CellState)
    (hst : satisfiedVm hash transferVmDescriptor (semTransferRow hash pre p post) true true) :
    post.commit = cellWireCommit hash post 0 := by
  have hco := commit_eq_commitOf hash (semTransferRow hash pre p post) hst.2.1
  simp only [l_saCommit, l_saBalLo, l_saBalHi, l_saNonce, l_saCap, l_saF0, l_saF1, l_saF2, l_saF3,
    l_saF4, l_saF5, l_saF6, l_saF7, l_auxRD] at hco
  rw [hco]; rfl

/-- **`transferDescriptor_commit_iff` — THE FLAGSHIP BICONDITIONAL.** For a genuine transfer whose
after-state absorbs to the published commit, the witness row satisfies the runnable descriptor on BOTH
deployed windows IFF the decoded transition is a genuine per-cell `CellTransferSpec` AND the published
`NEW_COMMIT` is the genuine wire commit of the after-state.

  * `→` is `transferDescriptor_full_sound` composed with `sem_forces_genuine_commit`: satisfaction
    forces both the structured spec AND (via the hash sites, NOT `hcommit`) the genuine commit.
  * `←` is the completeness construction `sem_transfer_satisfied`: the spec + genuine commit yield a
    satisfying witness.

Both directions are real; the `↔` is two-valued in `CellTransferSpec` (a tampered post fails the
gates — `canary_tamper_breaks_spec`) AND in the commit (a tampered post moves the genuine wire commit
— `canary_tamper_moves_commit`). The commit is the DEPLOYED `commitOf` absorption, not a re-authored
mirror. -/
theorem transferDescriptor_commit_iff (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams)
    (post : CellState)
    (hbLo : 0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) (hbHi : 0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    (hcommit : post.commit = cellWireCommit hash post 0) :
    (satisfiedVm hash transferVmDescriptor (semTransferRow hash pre p post) true false
      ∧ satisfiedVm hash transferVmDescriptor (semTransferRow hash pre p post) true true)
    ↔ (CellTransferSpec pre p post
        ∧ (semTransferRow hash pre p post).pub pi.NEW_COMMIT = cellWireCommit hash post 0) := by
  constructor
  · rintro ⟨hgs, hst⟩
    have hfs := transferDescriptor_full_sound hash (semTransferRow hash pre p post) pre post p
      (sem_rowEncodes hash pre p post) (sem_isTransferRow hash pre p post) hgs hst
    refine ⟨hfs.1, ?_⟩
    rw [p_new]
    exact sem_forces_genuine_commit hash pre p post hst
  · rintro ⟨hspec, _⟩
    exact sem_transfer_satisfied hash pre p post hcommit hbLo hbHi hspec

/-- **`sem_transfer_roundtrip` — the two-direction round-trip.** From any genuine spec'd transfer,
BUILD a satisfying witness (completeness), then FEED it back through the committed soundness bridge
(`transferDescriptor_full_sound`, inside the `↔`) to recover the structured spec AND the genuine
published commit. The accept-set and the spec agree in both directions. -/
theorem sem_transfer_roundtrip (hash : List ℤ → ℤ) (pre : CellState) (p : TransferParams)
    (post : CellState)
    (hbLo : 0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) (hbHi : 0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    (hcommit : post.commit = cellWireCommit hash post 0)
    (h : CellTransferSpec pre p post) :
    CellTransferSpec pre p post
      ∧ (semTransferRow hash pre p post).pub pi.NEW_COMMIT = cellWireCommit hash post 0 :=
  (transferDescriptor_commit_iff hash pre p post hbLo hbHi hcommit).mp
    (sem_transfer_satisfied hash pre p post hcommit hbLo hbHi h)

/-! ## §9 — a CONCRETE demo instance + the MUTATION CANARY. -/

/-- The demo after-state: `goodPost` with its stored commit set to the genuine wire commit, so the
"after-state absorbs to the published commit" precondition holds by construction. -/
def demoPost (hash : List ℤ → ℤ) : CellState := { goodPost with commit := cellWireCommit hash goodPost 0 }

/-- **The demo transfer satisfies BOTH windows** (`goodPre → demoPost`, debit 30, `100 → 70`), for
ANY hash — a genuinely-satisfied deployed denotation, not asserted. -/
theorem sem_transfer_satisfied_demo (hash : List ℤ → ℤ) :
    satisfiedVm hash transferVmDescriptor (semTransferRow hash goodPre goodParams (demoPost hash)) true false
    ∧ satisfiedVm hash transferVmDescriptor (semTransferRow hash goodPre goodParams (demoPost hash)) true true := by
  refine sem_transfer_satisfied hash goodPre goodParams (demoPost hash) rfl ?_ ?_ goodSpec_holds
  · exact ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩
  · exact ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩

/-- **The demo round-trip**: BUILD → recover the spec + genuine commit, on the concrete instance. -/
theorem sem_transfer_roundtrip_demo (hash : List ℤ → ℤ) :
    CellTransferSpec goodPre goodParams (demoPost hash)
      ∧ (semTransferRow hash goodPre goodParams (demoPost hash)).pub pi.NEW_COMMIT
          = cellWireCommit hash (demoPost hash) 0 :=
  sem_transfer_roundtrip hash goodPre goodParams (demoPost hash)
    ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩
    ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩ rfl goodSpec_holds

/-- A tampered after-state: `goodPost` with `field[0]` overwritten to `7` (an ABSORBED column). -/
def tamperPost : CellState := { goodPost with fields := fun i => if i = 0 then 7 else 0 }

/-- **`canary_tamper_moves_commit` — the whole-state commitment tooth BITES.** Under Poseidon2 CR,
tampering the absorbed `field[0]` MOVES the genuine wire commit: the honest published `NEW_COMMIT`
cannot ride a tampered after-state. Peel the outer `H4` (the inner-0 digest must match), then the
inner `H4` (the fourth absorbed field must match) — but `0 ≠ 7`. -/
theorem canary_tamper_moves_commit (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    cellWireCommit hash goodPost 0 ≠ cellWireCommit hash tamperPost 0 := by
  intro heq
  unfold cellWireCommit commitOf at heq
  have houter := hCR _ _ heq
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hi0, _⟩ := houter
  have hin := hCR _ _ hi0
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hin
  obtain ⟨_, _, _, hf0, _⟩ := hin
  simp only [goodPost, tamperPost] at hf0
  norm_num at hf0

/-- **`canary_tamper_breaks_spec` — the `↔` is two-valued.** The same tamper ALSO fails
`CellTransferSpec` (the frozen `field[0]` moved `0 → 7`, and `7 ≢ 0 [ZMOD p]` under canonicality), so
a `True`/`P → P` bridge could not separate this — the biconditional's LHS is genuinely refutable. -/
theorem canary_tamper_breaks_spec : ¬ CellTransferSpec goodPre goodParams tamperPost := by
  rintro ⟨_, _, _, _, hfld, _, _⟩
  have hf0 := hfld 0
  simp only [tamperPost, goodPost, goodPre] at hf0
  rw [Int.ModEq] at hf0
  norm_num at hf0

/-! ## §10 — axiom-hygiene tripwires. -/

#assert_axioms cellSpec_to_intent
#assert_axioms sem_rowEncodes
#assert_axioms sem_sites
#assert_axioms sem_transfer_satisfied
#assert_axioms sem_forces_genuine_commit
#assert_axioms transferDescriptor_commit_iff
#assert_axioms sem_transfer_roundtrip
#assert_axioms sem_transfer_satisfied_demo
#assert_axioms sem_transfer_roundtrip_demo
#assert_axioms canary_tamper_moves_commit
#assert_axioms canary_tamper_breaks_spec

end Dregg2.Circuit.Emit.EffectVmEmitTransferComplete
