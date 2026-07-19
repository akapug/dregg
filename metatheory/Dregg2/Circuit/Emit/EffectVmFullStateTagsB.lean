/-
# Dregg2.Circuit.Emit.EffectVmFullStateTagsB — per-tag COMPLETENESS (`←`) instantiations of the Cycle-3
completeness ENGINE (`EffectVmFullStateRunnableComplete.runnable_full_commit_iff`), for the KERNEL-ONLY
effect tags in lane B: createCell, createCellFromFactory, emitEvent, exercise, pipelinedSend,
receiptArchive, burn, bridgeMint, setField.

## What this adds (the `⟺`, per tag)

`EffectVmFullStateRunnable.runnable_full_sound` gave the GENERIC SOUNDNESS (`SAT ⟹ fullClause`), and each
tag already rides it as a THIN `RunnableFullStateSpec` instance (`*_runnable_full_sound`). The
COMPLETENESS engine (`EffectVmFullStateRunnableComplete`) discharged the crypto ONCE: it CONSTRUCTS the
Poseidon GROUP-4 carrier (`wide_sites_of_carrier`) and FORCES the commit (`runnable_forces_genuine_commit`),
welding the two directions into `runnable_full_commit_iff` over a `RunnableFullStateCompleteSpec`.

This module supplies, PER TAG, that `RunnableFullStateCompleteSpec` — so each tag gets its literal
`air_accepts ⟺ (fullClause ∧ NEW_COMMIT = wireCommitOfRow)` (`*_commit_iff`), plus a concrete demo and a
per-tag canary. The genuine per-tag content is `build_active`/`build_last` (the effect's own per-row gates
on the honest witness, the CONVERSE of `decodeFull`); the crypto is the engine's ONE named
`Poseidon2SpongeCR` carrier, never a fresh `axiom`.

## The shared witness engine (§A)

Every kernel-only tag over `CellState` shares ONE witness row `mkRow SEL hash pre post pA` (the state
blocks carry `pre`/`post`, the GROUP-4 aux inter-digests carry the genuine inner `hash`es, the params
carry `pA`, and `nxt` mirrors the after-state onto the next row's `state_before`). The `WReads` bundle
captures its column reads; `wreads_*` prove — ONCE, generically — the transition continuity, the 7
boundary PI pins, the selector gate, the GROUP-4 carrier (`WideCarrier`, under the honest-witness
precondition), and the balance-limb range teeth. A per-tag instance then only casts its OWN descriptor's
constraint list onto those shared facts + supplies its rowGates from the clause (via the tag's
`*_faithful.mpr`) — the ONLY genuine per-tag proof obligation.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; all imports
read-only. The sole crypto carrier is the engine's `Poseidon2SpongeCR` portal.
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState
import Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide
import Dregg2.Circuit.Emit.EffectVmEmitExerciseWide
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide
import Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable

namespace Dregg2.Circuit.Emit.EffectVmFullStateTagsB

open Dregg2.Circuit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transitionAll boundaryFirstPins boundaryLastPins eqToModEq)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec wideHashSites wideCommitOf baseAbsorbedCols)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete
  (RunnableFullStateCompleteSpec WideCarrier wireCommitOfRow
   runnable_full_commit_iff runnable_full_complete runnable_forces_genuine_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §A — THE SHARED WITNESS ENGINE (the reusable, crypto-discharged core). -/

/-- The genuine wide commitment of an after-`CellState` (record-digest `0`): the deployed GROUP-4
`H4`-of-`H4` absorption of the 12 scalar columns + the `0` record digest, EXACTLY `wideCommitOf` at the
row's frozen (empty) side-table carrier. This is the honest-witness commit the `absorbsTo` precondition
names. -/
def cellWideCommit (hash : List ℤ → ℤ) (post : CellState) : ℤ :=
  wideCommitOf hash post.balLo post.balHi post.nonce
    (post.fields 0) (post.fields 1) (post.fields 2) (post.fields 3) (post.fields 4)
    (post.fields 5) (post.fields 6) (post.fields 7) post.capRoot 0

/-- The honest-witness precondition (the generic `hcommit`): the after-state absorbs to the published
commit, the untouched side-tables are frozen (`sr = preRoots`), and the range-checked balance limbs are
in range. Shared across every frozen-side-table kernel tag. -/
def cellAbsorbsTo (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots) : Prop :=
  post.commit = cellWideCommit hash post
  ∧ sr = preRoots
  ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30)
  ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)

/-- The witnessing `loc` VALUE assignment (state block + params + honest GROUP-4 aux), WITHOUT a
selector. Every column carries its honest value; unmatched columns (incl. `sysRootsDigestCol`, the
record digest) are `0`. -/
def valLoc (hash : List ℤ → ℤ) (pre post : CellState) (pA : Nat → ℤ) : Assignment :=
  fun v =>
    if v = sbCol state.BALANCE_LO then pre.balLo
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
    else if v = prmCol 0 then pA 0
    else if v = prmCol 1 then pA 1
    else if v = prmCol 2 then pA 2
    else if v = prmCol 3 then pA 3
    else if v = prmCol 4 then pA 4
    else if v = prmCol 5 then pA 5
    else if v = prmCol 6 then pA 6
    else if v = prmCol 7 then pA 7
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
    else if v = auxCol aux_off.STATE_INTER1 then
      hash [post.balLo, post.balHi, post.nonce, post.fields 0]
    else if v = auxCol aux_off.STATE_INTER2 then
      hash [post.fields 1, post.fields 2, post.fields 3, post.fields 4]
    else if v = auxCol aux_off.STATE_INTER3 then
      hash [post.fields 5, post.fields 6, post.fields 7, post.capRoot]
    else 0

/-- The witnessing public-input vector: OLD/NEW commits, init/final balances, actor nonce. -/
def valPub (pre post : CellState) : Assignment :=
  fun k =>
    if k = pi.OLD_COMMIT then pre.commit
    else if k = pi.NEW_COMMIT then post.commit
    else if k = pi.INIT_BAL_LO then pre.balLo
    else if k = pi.INIT_BAL_HI then pre.balHi
    else if k = pi.FINAL_BAL_LO then post.balLo
    else if k = pi.FINAL_BAL_HI then post.balHi
    else if k = pi.ACTOR_NONCE then pre.nonce
    else 0

/-- **`mkRow SEL hash pre post pA`** — the shared witness `VmRowEnv`. The `loc` is the value assignment
with a hot `SEL` selector, structured as `if v < NUM_EFFECTS then (selector bits) else valLoc v` so that
EVERY state/param/aux column (all `≥ NUM_EFFECTS`) reads through to `valLoc` DEFINITIONALLY (independent
of the abstract `SEL`). `nxt` mirrors the after-state onto the next row's `state_before`. -/
def mkRow (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) (pA : Nat → ℤ) : VmRowEnv where
  loc := fun v => if v < NUM_EFFECTS then (if v = SEL then 1 else 0) else valLoc hash pre post pA v
  nxt := fun v => valLoc hash pre post pA (v + (STATE_SIZE + NUM_PARAMS))
  pub := valPub pre post

/-- Read a low column (`< NUM_EFFECTS`, i.e. a selector) off `mkRow`. -/
theorem mkRow_locLt (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) (pA : Nat → ℤ)
    (v : Nat) (hv : v < NUM_EFFECTS) :
    (mkRow SEL hash pre post pA).loc v = (if v = SEL then 1 else 0) := by
  show (if v < NUM_EFFECTS then (if v = SEL then (1:ℤ) else 0) else valLoc hash pre post pA v)
      = (if v = SEL then 1 else 0)
  rw [if_pos hv]

/-- Read a high column (`≥ NUM_EFFECTS`, i.e. state/param/aux) off `mkRow` as its value assignment. -/
theorem mkRow_locGe (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) (pA : Nat → ℤ)
    (v : Nat) (hv : NUM_EFFECTS ≤ v) :
    (mkRow SEL hash pre post pA).loc v = valLoc hash pre post pA v := by
  show (if v < NUM_EFFECTS then (if v = SEL then (1:ℤ) else 0) else valLoc hash pre post pA v)
      = valLoc hash pre post pA v
  rw [if_neg (by omega)]

/-! ### The `WReads` interface: the column reads of the witness row. -/

/-- The column reads of a witness row: the selector hot / NoOp cold, the `pre`/`post` state blocks (both
the `∀ i`-form field reads and the 8 literal field reads used by the GROUP-4 carrier), the honest aux
inter-digests (in post form), the frozen side-table carrier (`= 0`), the 7 public pins, and the
transition mirror. `mkRow_reads` establishes it for `mkRow` under `0 < SEL < NUM_EFFECTS`. -/
structure WReads (env : VmRowEnv) (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) : Prop where
  selHot : env.loc SEL = 1
  noopCold : env.loc sel.NOOP = 0
  sbLo : env.loc (sbCol state.BALANCE_LO) = pre.balLo
  sbHi : env.loc (sbCol state.BALANCE_HI) = pre.balHi
  sbN : env.loc (sbCol state.NONCE) = pre.nonce
  sbF : ∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i
  sbCap : env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  sbRes : env.loc (sbCol state.RESERVED) = pre.reserved
  sbC : env.loc (sbCol state.STATE_COMMIT) = pre.commit
  saLo : env.loc (saCol state.BALANCE_LO) = post.balLo
  saHi : env.loc (saCol state.BALANCE_HI) = post.balHi
  saN : env.loc (saCol state.NONCE) = post.nonce
  saF : ∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i
  saF0 : env.loc (saCol (state.FIELD_BASE + 0)) = post.fields 0
  saF1 : env.loc (saCol (state.FIELD_BASE + 1)) = post.fields 1
  saF2 : env.loc (saCol (state.FIELD_BASE + 2)) = post.fields 2
  saF3 : env.loc (saCol (state.FIELD_BASE + 3)) = post.fields 3
  saF4 : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields 4
  saF5 : env.loc (saCol (state.FIELD_BASE + 5)) = post.fields 5
  saF6 : env.loc (saCol (state.FIELD_BASE + 6)) = post.fields 6
  saF7 : env.loc (saCol (state.FIELD_BASE + 7)) = post.fields 7
  saCap : env.loc (saCol state.CAP_ROOT) = post.capRoot
  saRes : env.loc (saCol state.RESERVED) = post.reserved
  saC : env.loc (saCol state.STATE_COMMIT) = post.commit
  aux1 : env.loc (auxCol aux_off.STATE_INTER1) = hash [post.balLo, post.balHi, post.nonce, post.fields 0]
  aux2 : env.loc (auxCol aux_off.STATE_INTER2) = hash [post.fields 1, post.fields 2, post.fields 3, post.fields 4]
  aux3 : env.loc (auxCol aux_off.STATE_INTER3) = hash [post.fields 5, post.fields 6, post.fields 7, post.capRoot]
  sysZero : env.loc sysRootsDigestCol = 0
  pOld : env.pub pi.OLD_COMMIT = pre.commit
  pNew : env.pub pi.NEW_COMMIT = post.commit
  pInitLo : env.pub pi.INIT_BAL_LO = pre.balLo
  pInitHi : env.pub pi.INIT_BAL_HI = pre.balHi
  pFinLo : env.pub pi.FINAL_BAL_LO = post.balLo
  pFinHi : env.pub pi.FINAL_BAL_HI = post.balHi
  pActor : env.pub pi.ACTOR_NONCE = pre.nonce
  trans : ∀ i : Nat, env.nxt (sbCol i) = env.loc (saCol i)

/-- **`mkRow_reads`** — the shared witness row satisfies the `WReads` interface (under `0 < SEL <
NUM_EFFECTS`, which every real effect selector meets). -/
theorem mkRow_reads (SEL : Nat) (h0 : 0 < SEL) (hlt : SEL < NUM_EFFECTS) (hash : List ℤ → ℤ)
    (pre post : CellState) (pA : Nat → ℤ) :
    WReads (mkRow SEL hash pre post pA) SEL hash pre post := by
  have haGe : ∀ off : Nat, NUM_EFFECTS ≤ saCol off := by
    intro off; simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, STATE_SIZE, NUM_PARAMS]; omega
  refine {
    selHot := ?_, noopCold := ?_
    sbLo := rfl, sbHi := rfl, sbN := rfl, sbF := ?_, sbCap := rfl, sbRes := rfl, sbC := rfl
    saLo := rfl, saHi := rfl, saN := rfl, saF := ?_
    saF0 := rfl, saF1 := rfl, saF2 := rfl, saF3 := rfl, saF4 := rfl, saF5 := rfl, saF6 := rfl, saF7 := rfl
    saCap := rfl, saRes := rfl, saC := rfl
    aux1 := rfl, aux2 := rfl, aux3 := rfl, sysZero := rfl
    pOld := rfl, pNew := rfl, pInitLo := rfl, pInitHi := rfl, pFinLo := rfl, pFinHi := rfl, pActor := rfl
    trans := ?_ }
  · rw [mkRow_locLt SEL hash pre post pA SEL hlt, if_pos rfl]
  · rw [mkRow_locLt SEL hash pre post pA sel.NOOP (by decide),
        if_neg (by simp only [sel.NOOP]; omega)]
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i
    have harg : sbCol i + (STATE_SIZE + NUM_PARAMS) = saCol i := by
      simp only [sbCol, saCol, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_SIZE, NUM_PARAMS]; omega
    show valLoc hash pre post pA (sbCol i + (STATE_SIZE + NUM_PARAMS))
      = (mkRow SEL hash pre post pA).loc (saCol i)
    rw [harg, mkRow_locGe SEL hash pre post pA (saCol i) (haGe i)]

/-! ### The shared satisfaction facts (proved ONCE off `WReads`). -/

/-- The transition-continuity constraints hold on the witness (on any window with `isLast = false`). -/
theorem wreads_trans {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (b : Bool) (c : VmConstraint) (hc : c ∈ transitionAll) :
    c.holdsVm env b false := by
  simp only [transitionAll, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  show env.nxt (sbCol i) ≡ env.loc (saCol i) [ZMOD 2013265921]
  exact eqToModEq (h.trans i)

/-- The 4 first-row boundary PI pins hold on the witness (when `isFirst = true`). -/
theorem wreads_first {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (b : Bool) (c : VmConstraint) (hc : c ∈ boundaryFirstPins) :
    c.holdsVm env true b := by
  simp only [boundaryFirstPins, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact fun _ => eqToModEq (h.sbN.trans h.pActor.symm)
  · exact fun _ => eqToModEq (h.sbLo.trans h.pInitLo.symm)
  · exact fun _ => eqToModEq (h.sbHi.trans h.pInitHi.symm)
  · exact fun _ => eqToModEq (h.sbC.trans h.pOld.symm)

/-- The 3 last-row boundary PI pins hold on the witness (when `isLast = true`). -/
theorem wreads_last {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (b : Bool) (c : VmConstraint) (hc : c ∈ boundaryLastPins) :
    c.holdsVm env b true := by
  simp only [boundaryLastPins, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact fun _ => eqToModEq (h.saC.trans h.pNew.symm)
  · exact fun _ => eqToModEq (h.saLo.trans h.pFinLo.symm)
  · exact fun _ => eqToModEq (h.saHi.trans h.pFinHi.symm)

/-- The selector-binding gate holds on the witness (active window). -/
theorem wreads_sel {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (b : Bool) (c : VmConstraint) (hc : c ∈ selectorGates SEL) :
    c.holdsVm env b false := by
  simp only [selectorGates, List.mem_singleton] at hc
  subst hc
  show (selectorGateBody SEL).eval env.loc ≡ 0 [ZMOD 2013265921]
  have : (selectorGateBody SEL).eval env.loc = 0 := by
    simp only [selectorGateBody, EmittedExpr.eval, h.noopCold, h.selHot]; ring
  exact eqToModEq this

/-- The GROUP-4 carrier holds on the witness (under the honest-witness commit precondition). -/
theorem wreads_carrier {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (hcommit : post.commit = cellWideCommit hash post) :
    WideCarrier hash env := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.aux1, h.saLo, h.saHi, h.saN, h.saF0]
  · rw [h.aux2, h.saF1, h.saF2, h.saF3, h.saF4]
  · rw [h.aux3, h.saF5, h.saF6, h.saF7, h.saCap]
  · rw [h.saC, h.aux1, h.aux2, h.aux3, h.sysZero]; exact hcommit

/-- The two balance-limb range teeth hold on the witness (from the honest range bounds). -/
theorem wreads_ranges {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post)
    (hbLo : 0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) (hbHi : 0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    (c : VmRange) (hc : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩]) :
    c.holds env := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simpa only [VmRange.holds, h.saLo] using hbLo
  · simpa only [VmRange.holds, h.saHi] using hbHi

/-- `NEW_COMMIT` published as `state_commit` on the witness (the engine's `build_newcommit`). -/
theorem wreads_newcommit {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) :
    env.pub pi.NEW_COMMIT = env.loc (saCol state.STATE_COMMIT) := by
  rw [h.pNew, h.saC]

/-! ## §B — createCell (born-empty; constraints = row-gates only). -/

section CreateCell

open Dregg2.Circuit.Emit.EffectVmEmitCreateCell
  (SEL_CREATECELL createCellRowGates createCellVmDescriptor BornEmptyRowIntent createCellVm_faithful)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState
  (createCellVmDescriptorWide createCellWide_constraints_eq IsCreateCellRow RowEncodesCreate
   ZeroBlockSpec CreateCellFullClause createCellRunnableSpec)

/-- createCell's witness row (selector `SEL_CREATECELL`, no params). -/
def createCellRow (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow SEL_CREATECELL hash pre post (fun _ => 0)

theorem createCellRow_reads (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (createCellRow hash pre post) SEL_CREATECELL hash pre post :=
  mkRow_reads SEL_CREATECELL (by decide) (by decide) hash pre post _

/-- born-empty intent on the witness, from the zero-block clause. -/
theorem createCell_intent (hash : List ℤ → ℤ) (pre post : CellState) (hz : ZeroBlockSpec post) :
    BornEmptyRowIntent (createCellRow hash pre post) := by
  have h := createCellRow_reads hash pre post
  obtain ⟨hzLo, hzHi, hzN, hzF, hzCap, hzRes⟩ := hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo]; exact hzLo
  · rw [h.saHi]; exact hzHi
  · rw [h.saN]; exact hzN
  · rw [h.saCap]; exact hzCap
  · rw [h.saRes]; exact hzRes
  · intro i hi; rw [h.saF ⟨i, hi⟩]; exact hzF ⟨i, hi⟩

/-- createCell's row gates hold on the witness (from the clause, via `createCellVm_faithful.mpr`). -/
theorem createCell_gates (hash : List ℤ → ℤ) (pre post : CellState) (hz : ZeroBlockSpec post) (b : Bool)
    (c : VmConstraint) (hc : c ∈ createCellRowGates) :
    c.holdsVm (createCellRow hash pre post) b false := by
  have hg := (createCellVm_faithful (createCellRow hash pre post)).mpr (createCell_intent hash pre post hz)
  have hcc := hg c hc
  -- createCellRowGates are all `.gate`; `holdsVm` at `isLast = false` is flag-independent.
  simp only [createCellRowGates, Dregg2.Circuit.Emit.EffectVmEmitCreateCell.gZero, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

/-- **`createCellRunnableCompleteSpec`** — the per-tag `RunnableFullStateCompleteSpec` for createCell. -/
def createCellRunnableCompleteSpec (preRoots : SysRoots) :
    RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := createCellRunnableSpec preRoots
  buildRow := fun hash pre post _sr => createCellRow hash pre post
  absorbsTo := cellAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr => (createCellRow_reads hash pre post).selHot
  build_decode := by
    intro hash pre post sr habsorb
    exact ⟨⟨(createCellRow_reads hash pre post).saLo, (createCellRow_reads hash pre post).saHi,
            (createCellRow_reads hash pre post).saN, (createCellRow_reads hash pre post).saF,
            (createCellRow_reads hash pre post).saCap, (createCellRow_reads hash pre post).saRes⟩,
           habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (createCellRow_reads hash pre post) habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hz, _⟩ := hclause
    have hc2 : c ∈ createCellRowGates := hc
    exact createCell_gates hash pre post hz true c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ createCellRowGates := hc
    -- createCell's constraints are all `.gate`; vacuous on the wrap row.
    simp only [createCellRowGates, Dregg2.Circuit.Emit.EffectVmEmitCreateCell.gZero, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hc2
    rcases hc2 with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (createCellRow_reads hash pre post) habsorb.2.2.1 habsorb.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (createCellRow_reads hash pre post)

/-- **`createCell_commit_iff` — the per-tag `⟺`.** The witness satisfies the WIDE createCell descriptor on
BOTH windows IFF the decoded transition is the genuine born-empty full clause AND the published
`NEW_COMMIT` is the genuine wire commit of the after-state. -/
theorem createCell_commit_iff (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : cellAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (createCellRunnableCompleteSpec preRoots).descriptor
        ((createCellRunnableCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (createCellRunnableCompleteSpec preRoots).descriptor
        ((createCellRunnableCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((createCellRunnableCompleteSpec preRoots).fullClause pre post sr
        ∧ ((createCellRunnableCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((createCellRunnableCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (createCellRunnableCompleteSpec preRoots) hash pre post sr habsorb

/-- The concrete demo after-state (`createCellPost` with its commit set to the genuine wire commit). -/
def createCellDemoPost (hash : List ℤ → ℤ) : CellState :=
  { Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPost with
    commit := cellWideCommit hash Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPost }

theorem createCell_demo_absorbs (hash : List ℤ → ℤ) :
    cellAbsorbsTo Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots hash
      Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre (createCellDemoPost hash)
      Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [createCellDemoPost, Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPost]

/-- **`createCell_commit_iff_demo` — the both-windows `⟺`, concretely discharged.** -/
theorem createCell_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (createCellRunnableCompleteSpec
          Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots).descriptor
        (createCellRow hash Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre
          (createCellDemoPost hash)) true false
      ∧ satisfiedVm hash (createCellRunnableCompleteSpec
          Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots).descriptor
        (createCellRow hash Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre
          (createCellDemoPost hash)) true true)
    ↔ ((createCellRunnableCompleteSpec
          Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots).fullClause
          Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre (createCellDemoPost hash)
          Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots
        ∧ (createCellRow hash Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre
            (createCellDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (createCellRow hash
                Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre
                (createCellDemoPost hash))) :=
  createCell_commit_iff Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots hash
    Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre (createCellDemoPost hash)
    Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots
    (createCell_demo_absorbs hash)

/-- **`createCell_canary_clause` — the clause conjunct is REFUTABLE (the `↔` LHS is two-valued).** -/
theorem createCell_canary_clause :
    ¬ (createCellRunnableCompleteSpec
          Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots).fullClause
        Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPre
        { Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPost with balLo := 999 }
        Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCellPreRoots :=
  Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.createCell_clause_not_trivial

#assert_axioms createCellRow_reads
#assert_axioms createCell_commit_iff
#assert_axioms createCell_commit_iff_demo
#assert_axioms createCell_canary_clause

end CreateCell

end Dregg2.Circuit.Emit.EffectVmFullStateTagsB
