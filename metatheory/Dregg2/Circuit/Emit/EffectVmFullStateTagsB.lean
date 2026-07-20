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
on the honest witness, the CONVERSE of `decodeFull`).

⚑ **NO CRYPTO CARRIER.** These `⟺` do NOT ride `Poseidon2SpongeCR` — an earlier version of this header
said they did, and that was wrong. The `→` leg composes `runnable_full_sound` with
`runnable_forces_genuine_commit`, which reads the commit off the hash SITES the constraint system pins;
the `←` leg CONSTRUCTS those columns. No injectivity is invoked, so each `*_commit_iff` is TRUE at
deployed BabyBear parameters — where `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` refutes the
injective floor. What did ride the false floor was the surrounding evidence (the whole-state anti-ghost
and the mutation canaries), now cured to unconditional disjunctions.

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
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. All imports read-only.
There is no crypto carrier on any theorem in this file.
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState
import Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide
import Dregg2.Circuit.Emit.EffectVmEmitExerciseWide
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide
import Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable
import Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint

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

/-- The last-row boundary pins are VACUOUS on the active window (`isLast = false`). -/
theorem wreads_last_vac (env : VmRowEnv) (c : VmConstraint) (hc : c ∈ boundaryLastPins) :
    c.holdsVm env true false := by
  simp only [boundaryLastPins, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact fun hcon => absurd hcon (by decide)

/-- **`canonical_active`** — the ACTIVE-window (`true false`) satisfaction for the CANONICAL descriptor
shape `rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates SEL`, given
the tag's rowGates on the witness. -/
theorem canonical_active {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (rowGates : List VmConstraint)
    (hrg : ∀ c ∈ rowGates, c.holdsVm env true false)
    (c : VmConstraint)
    (hc : c ∈ rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates SEL) :
    c.holdsVm env true false := by
  simp only [List.mem_append] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc)
  · exact hrg c hc
  · exact wreads_trans h true c hc
  · exact wreads_first h false c hc
  · exact wreads_last_vac env c hc
  · exact wreads_sel h true c hc

/-- **`canonical_last`** — the LAST-window (`true true`) satisfaction for the canonical shape, given the
rowGates VACUOUS on the wrap row (they are all `.gate`). -/
theorem canonical_last {env : VmRowEnv} {SEL : Nat} {hash : List ℤ → ℤ} {pre post : CellState}
    (h : WReads env SEL hash pre post) (rowGates : List VmConstraint)
    (hrgVac : ∀ c ∈ rowGates, c.holdsVm env true true)
    (c : VmConstraint)
    (hc : c ∈ rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates SEL) :
    c.holdsVm env true true := by
  simp only [List.mem_append] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc)
  · exact hrgVac c hc
  · simp only [transitionAll, List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc; exact trivial
  · exact wreads_first h true c hc
  · exact wreads_last h true c hc
  · simp only [selectorGates, List.mem_singleton] at hc; subst hc; exact trivial

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

/-! ## §C — createCellFromFactory (born-empty; constraints = row-gates only). -/

section Factory

open Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
  (SEL_CREATECELLFROMFACTORY factoryRowGates factoryVmDescriptor BornEmptyRowIntent factoryVm_faithful gZero)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState
  (factoryVmDescriptorWide factoryWide_constraints_eq IsFactoryRow RowEncodesFactory ZeroBlockSpec
   FactoryFullClause factoryRunnableSpec factoryPre factoryPost factoryPreRoots factory_clause_not_trivial)

def factoryRow (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow SEL_CREATECELLFROMFACTORY hash pre post (fun _ => 0)

theorem factoryRow_reads (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (factoryRow hash pre post) SEL_CREATECELLFROMFACTORY hash pre post :=
  mkRow_reads SEL_CREATECELLFROMFACTORY (by decide) (by decide) hash pre post _

theorem factory_intent (hash : List ℤ → ℤ) (pre post : CellState) (hz : ZeroBlockSpec post) :
    BornEmptyRowIntent (factoryRow hash pre post) := by
  have h := factoryRow_reads hash pre post
  obtain ⟨hzLo, hzHi, hzN, hzF, hzCap, hzRes⟩ := hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo]; exact hzLo
  · rw [h.saHi]; exact hzHi
  · rw [h.saN]; exact hzN
  · rw [h.saCap]; exact hzCap
  · rw [h.saRes]; exact hzRes
  · intro i hi; rw [h.saF ⟨i, hi⟩]; exact hzF ⟨i, hi⟩

theorem factory_gates (hash : List ℤ → ℤ) (pre post : CellState) (hz : ZeroBlockSpec post) (b : Bool)
    (c : VmConstraint) (hc : c ∈ factoryRowGates) :
    c.holdsVm (factoryRow hash pre post) b false := by
  have hg := (factoryVm_faithful (factoryRow hash pre post)).mpr (factory_intent hash pre post hz)
  have hcc := hg c hc
  simp only [factoryRowGates, gZero, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

def factoryRunnableCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := factoryRunnableSpec preRoots
  buildRow := fun hash pre post _sr => factoryRow hash pre post
  absorbsTo := cellAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr => (factoryRow_reads hash pre post).selHot
  build_decode := by
    intro hash pre post sr habsorb
    exact ⟨⟨(factoryRow_reads hash pre post).saLo, (factoryRow_reads hash pre post).saHi,
            (factoryRow_reads hash pre post).saN, (factoryRow_reads hash pre post).saF,
            (factoryRow_reads hash pre post).saCap, (factoryRow_reads hash pre post).saRes⟩,
           habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (factoryRow_reads hash pre post) habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hz, _⟩ := hclause
    have hc2 : c ∈ factoryRowGates := hc
    exact factory_gates hash pre post hz true c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ factoryRowGates := hc
    simp only [factoryRowGates, gZero, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at hc2
    rcases hc2 with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (factoryRow_reads hash pre post) habsorb.2.2.1 habsorb.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (factoryRow_reads hash pre post)

/-- **`factory_commit_iff` — the per-tag `⟺`.** -/
theorem factory_commit_iff (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : cellAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (factoryRunnableCompleteSpec preRoots).descriptor
        ((factoryRunnableCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (factoryRunnableCompleteSpec preRoots).descriptor
        ((factoryRunnableCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((factoryRunnableCompleteSpec preRoots).fullClause pre post sr
        ∧ ((factoryRunnableCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((factoryRunnableCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (factoryRunnableCompleteSpec preRoots) hash pre post sr habsorb

def factoryDemoPost (hash : List ℤ → ℤ) : CellState :=
  { factoryPost with commit := cellWideCommit hash factoryPost }

theorem factory_demo_absorbs (hash : List ℤ → ℤ) :
    cellAbsorbsTo factoryPreRoots hash factoryPre (factoryDemoPost hash) factoryPreRoots := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num [factoryDemoPost, factoryPost]

theorem factory_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (factoryRunnableCompleteSpec factoryPreRoots).descriptor
        (factoryRow hash factoryPre (factoryDemoPost hash)) true false
      ∧ satisfiedVm hash (factoryRunnableCompleteSpec factoryPreRoots).descriptor
        (factoryRow hash factoryPre (factoryDemoPost hash)) true true)
    ↔ ((factoryRunnableCompleteSpec factoryPreRoots).fullClause factoryPre (factoryDemoPost hash) factoryPreRoots
        ∧ (factoryRow hash factoryPre (factoryDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (factoryRow hash factoryPre (factoryDemoPost hash))) :=
  factory_commit_iff factoryPreRoots hash factoryPre (factoryDemoPost hash) factoryPreRoots
    (factory_demo_absorbs hash)

theorem factory_canary_clause :
    ¬ (factoryRunnableCompleteSpec factoryPreRoots).fullClause factoryPre
        { factoryPost with balLo := 999 } factoryPreRoots :=
  factory_clause_not_trivial

#assert_axioms factoryRow_reads
#assert_axioms factory_commit_iff
#assert_axioms factory_commit_iff_demo
#assert_axioms factory_canary_clause

end Factory

/-! ## §D — emitEvent (freeze + nonce tick; canonical descriptor). -/

section EmitEvent

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll gFieldPass)
open Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
  (SEL_EMIT_EVENT emitTickRowGates emitEventVmDescriptor EmitTickRowIntent emitTickVm_faithful
   RowEncodes EmitTickCellSpec)
open Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide
  (emitEventVmDescriptorWide emitEventWide_constraints_eq EmitEventFullClause emitEventRunnableSpec
   emitPre emitPost goodPreRoots emitEvent_clause_not_trivial)
open Dregg2.Circuit.Emit.EffectVmEmitEmitEvent (IsEmitRow)

def emitEventRow (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow SEL_EMIT_EVENT hash pre post (fun _ => 0)

theorem emitEventRow_reads (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (emitEventRow hash pre post) SEL_EMIT_EVENT hash pre post :=
  mkRow_reads SEL_EMIT_EVENT (by decide) (by decide) hash pre post _

theorem emitEvent_intent (hash : List ℤ → ℤ) (pre post : CellState) (hspec : EmitTickCellSpec pre post) :
    EmitTickRowIntent (emitEventRow hash pre post) := by
  have h := emitEventRow_reads hash pre post
  obtain ⟨hLo, hHi, hN, hFld, hCap, hRes⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo, h.sbLo]; exact hLo
  · rw [h.saHi, h.sbHi]; exact hHi
  · rw [h.saN, h.sbN, h.noopCold]; simpa using hN
  · rw [h.saCap, h.sbCap]; exact hCap
  · rw [h.saRes, h.sbRes]; exact hRes
  · intro i hi; rw [h.saF ⟨i, hi⟩, h.sbF ⟨i, hi⟩]; exact hFld ⟨i, hi⟩

theorem emitEvent_gates (hash : List ℤ → ℤ) (pre post : CellState) (hspec : EmitTickCellSpec pre post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ emitTickRowGates) :
    c.holdsVm (emitEventRow hash pre post) b false := by
  have hg := (emitTickVm_faithful (emitEventRow hash pre post)).mpr (emitEvent_intent hash pre post hspec)
  have hcc := hg c hc
  simp only [emitTickRowGates, gFieldPassAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem emitEvent_gates_vac (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ emitTickRowGates) : c.holdsVm (emitEventRow hash pre post) true true := by
  simp only [emitTickRowGates, gFieldPassAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

def emitEventRunnableCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := emitEventRunnableSpec preRoots
  buildRow := fun hash pre post _sr => emitEventRow hash pre post
  absorbsTo := cellAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(emitEventRow_reads hash pre post).selHot, (emitEventRow_reads hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    have h := emitEventRow_reads hash pre post
    exact ⟨⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.sbC, h.saLo, h.saHi, h.saN, h.saF,
            h.saCap, h.saRes, h.saC, h.pOld, h.pNew⟩, habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (emitEventRow_reads hash pre post) habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ emitTickRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates SEL_EMIT_EVENT := hc
    exact canonical_active (emitEventRow_reads hash pre post) emitTickRowGates
      (emitEvent_gates hash pre post hspec true) c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ emitTickRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates SEL_EMIT_EVENT := hc
    exact canonical_last (emitEventRow_reads hash pre post) emitTickRowGates
      (emitEvent_gates_vac hash pre post) c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (emitEventRow_reads hash pre post) habsorb.2.2.1 habsorb.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (emitEventRow_reads hash pre post)

/-- **`emitEvent_commit_iff` — the per-tag `⟺`.** -/
theorem emitEvent_commit_iff (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : cellAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (emitEventRunnableCompleteSpec preRoots).descriptor
        ((emitEventRunnableCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (emitEventRunnableCompleteSpec preRoots).descriptor
        ((emitEventRunnableCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((emitEventRunnableCompleteSpec preRoots).fullClause pre post sr
        ∧ ((emitEventRunnableCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((emitEventRunnableCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (emitEventRunnableCompleteSpec preRoots) hash pre post sr habsorb

def emitEventDemoPost (hash : List ℤ → ℤ) : CellState :=
  { emitPost with commit := cellWideCommit hash emitPost }

theorem emitEvent_demo_absorbs (hash : List ℤ → ℤ) :
    cellAbsorbsTo goodPreRoots hash emitPre (emitEventDemoPost hash) goodPreRoots := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num [emitEventDemoPost, emitPost, emitPre]

theorem emitEvent_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (emitEventRunnableCompleteSpec goodPreRoots).descriptor
        (emitEventRow hash emitPre (emitEventDemoPost hash)) true false
      ∧ satisfiedVm hash (emitEventRunnableCompleteSpec goodPreRoots).descriptor
        (emitEventRow hash emitPre (emitEventDemoPost hash)) true true)
    ↔ ((emitEventRunnableCompleteSpec goodPreRoots).fullClause emitPre (emitEventDemoPost hash) goodPreRoots
        ∧ (emitEventRow hash emitPre (emitEventDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (emitEventRow hash emitPre (emitEventDemoPost hash))) :=
  emitEvent_commit_iff goodPreRoots hash emitPre (emitEventDemoPost hash) goodPreRoots
    (emitEvent_demo_absorbs hash)

theorem emitEvent_canary_clause :
    ¬ (emitEventRunnableCompleteSpec goodPreRoots).fullClause emitPre
        { emitPost with balLo := 999 } goodPreRoots :=
  emitEvent_clause_not_trivial

#assert_axioms emitEventRow_reads
#assert_axioms emitEvent_commit_iff
#assert_axioms emitEvent_commit_iff_demo
#assert_axioms emitEvent_canary_clause

end EmitEvent

/-! ## §E — exercise (hold layer: freeze + nonce tick; canonical descriptor). -/

section Exercise

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll gFieldPass)
open Dregg2.Circuit.Emit.EffectVmEmitExercise
  (SEL_EXERCISE exerciseRowGates exerciseVmDescriptor ExerciseRowIntent exerciseVm_faithful
   RowEncodesExercise ExerciseCellSpec IsExerciseRow)
open Dregg2.Circuit.Emit.EffectVmEmitExerciseWide
  (exerciseVmDescriptorWide exerciseWide_constraints_eq ExerciseFullClause exerciseRunnableSpec
   exPre exPost goodPreRoots exercise_clause_not_trivial)

def exerciseRow (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow SEL_EXERCISE hash pre post (fun _ => 0)

theorem exerciseRow_reads (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (exerciseRow hash pre post) SEL_EXERCISE hash pre post :=
  mkRow_reads SEL_EXERCISE (by decide) (by decide) hash pre post _

theorem exercise_intent (hash : List ℤ → ℤ) (pre post : CellState) (hspec : ExerciseCellSpec pre post) :
    ExerciseRowIntent (exerciseRow hash pre post) := by
  have h := exerciseRow_reads hash pre post
  obtain ⟨hLo, hHi, hN, hFld, hCap, hRes⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo, h.sbLo]; exact hLo
  · rw [h.saHi, h.sbHi]; exact hHi
  · rw [h.saN, h.sbN, h.noopCold]; simpa using hN
  · rw [h.saCap, h.sbCap]; exact hCap
  · rw [h.saRes, h.sbRes]; exact hRes
  · intro i hi; rw [h.saF ⟨i, hi⟩, h.sbF ⟨i, hi⟩]; exact hFld ⟨i, hi⟩

theorem exercise_gates (hash : List ℤ → ℤ) (pre post : CellState) (hspec : ExerciseCellSpec pre post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ exerciseRowGates) :
    c.holdsVm (exerciseRow hash pre post) b false := by
  have hg := (exerciseVm_faithful (exerciseRow hash pre post)).mpr (exercise_intent hash pre post hspec)
  have hcc := hg c hc
  simp only [exerciseRowGates, gFieldPassAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem exercise_gates_vac (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ exerciseRowGates) : c.holdsVm (exerciseRow hash pre post) true true := by
  simp only [exerciseRowGates, gFieldPassAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

def exerciseRunnableCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := exerciseRunnableSpec preRoots
  buildRow := fun hash pre post _sr => exerciseRow hash pre post
  absorbsTo := cellAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(exerciseRow_reads hash pre post).selHot, (exerciseRow_reads hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    have h := exerciseRow_reads hash pre post
    exact ⟨⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.sbC, h.saLo, h.saHi, h.saN, h.saF,
            h.saCap, h.saRes, h.saC, h.pOld, h.pNew⟩, habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (exerciseRow_reads hash pre post) habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ exerciseRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates SEL_EXERCISE := hc
    exact canonical_active (exerciseRow_reads hash pre post) exerciseRowGates
      (exercise_gates hash pre post hspec true) c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ exerciseRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates SEL_EXERCISE := hc
    exact canonical_last (exerciseRow_reads hash pre post) exerciseRowGates
      (exercise_gates_vac hash pre post) c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (exerciseRow_reads hash pre post) habsorb.2.2.1 habsorb.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (exerciseRow_reads hash pre post)

theorem exercise_commit_iff (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : cellAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (exerciseRunnableCompleteSpec preRoots).descriptor
        ((exerciseRunnableCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (exerciseRunnableCompleteSpec preRoots).descriptor
        ((exerciseRunnableCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((exerciseRunnableCompleteSpec preRoots).fullClause pre post sr
        ∧ ((exerciseRunnableCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((exerciseRunnableCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (exerciseRunnableCompleteSpec preRoots) hash pre post sr habsorb

def exerciseDemoPost (hash : List ℤ → ℤ) : CellState :=
  { exPost with commit := cellWideCommit hash exPost }

theorem exercise_demo_absorbs (hash : List ℤ → ℤ) :
    cellAbsorbsTo goodPreRoots hash exPre (exerciseDemoPost hash) goodPreRoots := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num [exerciseDemoPost, exPost, exPre]

theorem exercise_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (exerciseRunnableCompleteSpec goodPreRoots).descriptor
        (exerciseRow hash exPre (exerciseDemoPost hash)) true false
      ∧ satisfiedVm hash (exerciseRunnableCompleteSpec goodPreRoots).descriptor
        (exerciseRow hash exPre (exerciseDemoPost hash)) true true)
    ↔ ((exerciseRunnableCompleteSpec goodPreRoots).fullClause exPre (exerciseDemoPost hash) goodPreRoots
        ∧ (exerciseRow hash exPre (exerciseDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (exerciseRow hash exPre (exerciseDemoPost hash))) :=
  exercise_commit_iff goodPreRoots hash exPre (exerciseDemoPost hash) goodPreRoots
    (exercise_demo_absorbs hash)

theorem exercise_canary_clause :
    ¬ (exerciseRunnableCompleteSpec goodPreRoots).fullClause exPre
        { exPost with nonce := 9 } goodPreRoots :=
  exercise_clause_not_trivial

#assert_axioms exerciseRow_reads
#assert_axioms exercise_commit_iff
#assert_axioms exercise_commit_iff_demo
#assert_axioms exercise_canary_clause

end Exercise

/-! ## §F — receiptArchive (field[1] set to 1 + frame freeze; no last-pins / selector). -/

section ReceiptArchive

open Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
  (archiveRowGates receiptArchiveVmDescriptor ArchiveRowIntent archiveVm_faithful ArchiveRowEncodes
   ArchiveCellSpec IsArchiveRow gFieldFixRest LIFE_FIELD selRA.RECEIPT_ARCHIVE)
open Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide
  (archiveVmDescriptorWide archiveWide_constraints_eq ReceiptArchiveFullClause archiveRunnableSpec
   arPre arPost goodPreRoots archive_clause_not_trivial)

def archiveRow (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow selRA.RECEIPT_ARCHIVE hash pre post (fun _ => 0)

theorem archiveRow_reads (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (archiveRow hash pre post) selRA.RECEIPT_ARCHIVE hash pre post :=
  mkRow_reads selRA.RECEIPT_ARCHIVE (by decide) (by decide) hash pre post _

theorem archive_intent (hash : List ℤ → ℤ) (pre post : CellState) (hspec : ArchiveCellSpec pre post) :
    ArchiveRowIntent (archiveRow hash pre post) := by
  have h := archiveRow_reads hash pre post
  obtain ⟨hlife, hlo, hhi, hnon, hfld, hcap, hres⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [LIFE_FIELD]; rw [h.saF1]; exact hlife
  · rw [h.saLo, h.sbLo]; exact hlo
  · rw [h.saHi, h.sbHi]; exact hhi
  · rw [h.saN, h.sbN]; exact hnon
  · rw [h.saCap, h.sbCap]; exact hcap
  · rw [h.saRes, h.sbRes]; exact hres
  · intro i hi1 hi8
    rw [h.saF ⟨i, hi8⟩, h.sbF ⟨i, hi8⟩]
    exact hfld ⟨i, hi8⟩ (fun hc => hi1 (congrArg Fin.val hc))

theorem archive_gates (hash : List ℤ → ℤ) (pre post : CellState) (hspec : ArchiveCellSpec pre post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ archiveRowGates) :
    c.holdsVm (archiveRow hash pre post) b false := by
  have hg := (archiveVm_faithful (archiveRow hash pre post)).mpr (archive_intent hash pre post hspec)
  have hcc := hg c hc
  simp only [archiveRowGates, gFieldFixRest, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem archive_gates_vac (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ archiveRowGates) : c.holdsVm (archiveRow hash pre post) true true := by
  simp only [archiveRowGates, gFieldFixRest, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

def archiveRunnableCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := archiveRunnableSpec preRoots
  buildRow := fun hash pre post _sr => archiveRow hash pre post
  absorbsTo := cellAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(archiveRow_reads hash pre post).selHot, (archiveRow_reads hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    have h := archiveRow_reads hash pre post
    exact ⟨⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.saLo, h.saHi, h.saN, h.saF,
            h.saCap, h.saRes⟩, habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (archiveRow_reads hash pre post) habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ archiveRowGates ++ transitionAll ++ boundaryFirstPins := hc
    simp only [List.mem_append] at hc2
    rcases hc2 with (hc2 | hc2) | hc2
    · exact archive_gates hash pre post hspec true c hc2
    · exact wreads_trans (archiveRow_reads hash pre post) true c hc2
    · exact wreads_first (archiveRow_reads hash pre post) false c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ archiveRowGates ++ transitionAll ++ boundaryFirstPins := hc
    simp only [List.mem_append] at hc2
    rcases hc2 with (hc2 | hc2) | hc2
    · exact archive_gates_vac hash pre post c hc2
    · simp only [transitionAll, List.mem_map, List.mem_range] at hc2
      obtain ⟨i, hi, rfl⟩ := hc2; exact trivial
    · exact wreads_first (archiveRow_reads hash pre post) true c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ ([] : List VmRange) := hc
    cases hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (archiveRow_reads hash pre post)

theorem receiptArchive_commit_iff (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : cellAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (archiveRunnableCompleteSpec preRoots).descriptor
        ((archiveRunnableCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (archiveRunnableCompleteSpec preRoots).descriptor
        ((archiveRunnableCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((archiveRunnableCompleteSpec preRoots).fullClause pre post sr
        ∧ ((archiveRunnableCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((archiveRunnableCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (archiveRunnableCompleteSpec preRoots) hash pre post sr habsorb

def archiveDemoPost (hash : List ℤ → ℤ) : CellState :=
  { arPost with commit := cellWideCommit hash arPost }

theorem archive_demo_absorbs (hash : List ℤ → ℤ) :
    cellAbsorbsTo goodPreRoots hash arPre (archiveDemoPost hash) goodPreRoots := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num [archiveDemoPost, arPost]

theorem receiptArchive_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (archiveRunnableCompleteSpec goodPreRoots).descriptor
        (archiveRow hash arPre (archiveDemoPost hash)) true false
      ∧ satisfiedVm hash (archiveRunnableCompleteSpec goodPreRoots).descriptor
        (archiveRow hash arPre (archiveDemoPost hash)) true true)
    ↔ ((archiveRunnableCompleteSpec goodPreRoots).fullClause arPre (archiveDemoPost hash) goodPreRoots
        ∧ (archiveRow hash arPre (archiveDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (archiveRow hash arPre (archiveDemoPost hash))) :=
  receiptArchive_commit_iff goodPreRoots hash arPre (archiveDemoPost hash) goodPreRoots
    (archive_demo_absorbs hash)

theorem receiptArchive_canary_clause :
    ¬ (archiveRunnableCompleteSpec goodPreRoots).fullClause arPre
        { arPost with fields := fun _ => 999 } goodPreRoots :=
  archive_clause_not_trivial

#assert_axioms archiveRow_reads
#assert_axioms receiptArchive_commit_iff
#assert_axioms receiptArchive_commit_iff_demo
#assert_axioms receiptArchive_canary_clause

end ReceiptArchive

/-! ## §G — burn (balance debit by the amount param + nonce tick; canonical descriptor). -/

section Burn

open Dregg2.Circuit.Emit.EffectVmEmitBurn
  (burnRowGates burnVmDescriptor BurnRowIntent burnVm_faithful RowEncodes CellBurnSpec IsBurnRow gFieldFixAll)
open Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable
  (burnVmDescriptorWide burnWide_constraints_eq BurnFullClause burnRunnableSpec
   goodBurnPre goodBurnPost goodBurnPreRoots burnFullClause_not_trivial)

/-- The burn amount lives in the `BURN_AMOUNT_LO` param column. -/
def burnPA (amt : ℤ) : Nat → ℤ :=
  fun i => if i = Dregg2.Circuit.Emit.EffectVmEmitBurn.param.BURN_AMOUNT_LO then amt else 0

def burnRow (amt : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN hash pre post (burnPA amt)

theorem burnRow_reads (amt : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (burnRow amt hash pre post) Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN hash pre post :=
  mkRow_reads Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN (by decide) (by decide) hash pre post _

theorem burnRow_amt (amt : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) :
    (burnRow amt hash pre post).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitBurn.param.BURN_AMOUNT_LO) = amt := by
  show (mkRow Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN hash pre post (burnPA amt)).loc
      (prmCol Dregg2.Circuit.Emit.EffectVmEmitBurn.param.BURN_AMOUNT_LO) = amt
  rw [mkRow_locGe Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN hash pre post (burnPA amt) _ (by decide)]
  rfl

theorem burn_intent (amt : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) (hspec : CellBurnSpec pre amt post) :
    BurnRowIntent (burnRow amt hash pre post) := by
  have h := burnRow_reads amt hash pre post
  have hamt := burnRow_amt amt hash pre post
  obtain ⟨hLo, hHi, hN, hFld, hCap, hRes⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo, h.sbLo, hamt]; exact hLo
  · rw [h.saHi, h.sbHi]; exact hHi
  · rw [h.saN, h.sbN]; exact hN
  · rw [h.saCap, h.sbCap]; exact hCap
  · rw [h.saRes, h.sbRes]; exact hRes
  · intro i hi; rw [h.saF ⟨i, hi⟩, h.sbF ⟨i, hi⟩]; exact hFld ⟨i, hi⟩

theorem burn_gates (amt : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) (hspec : CellBurnSpec pre amt post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ burnRowGates) :
    c.holdsVm (burnRow amt hash pre post) b false := by
  have h := burnRow_reads amt hash pre post
  have hg := (burnVm_faithful (burnRow amt hash pre post) ⟨h.selHot, h.noopCold⟩).mpr
    (burn_intent amt hash pre post hspec)
  have hcc := hg c hc
  simp only [burnRowGates, gFieldFixAll, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem burn_gates_vac (amt : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ burnRowGates) : c.holdsVm (burnRow amt hash pre post) true true := by
  simp only [burnRowGates, gFieldFixAll, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

def burnRunnableCompleteSpec (amt : ℤ) (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := burnRunnableSpec amt preRoots
  buildRow := fun hash pre post _sr => burnRow amt hash pre post
  absorbsTo := cellAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(burnRow_reads amt hash pre post).selHot, (burnRow_reads amt hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    have h := burnRow_reads amt hash pre post
    exact ⟨⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.sbC, burnRow_amt amt hash pre post,
            h.saLo, h.saHi, h.saN, h.saF, h.saCap, h.saRes, h.saC, h.pOld, h.pNew⟩, habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (burnRow_reads amt hash pre post) habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ burnRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN := hc
    exact canonical_active (burnRow_reads amt hash pre post) burnRowGates
      (burn_gates amt hash pre post hspec true) c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ burnRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates Dregg2.Circuit.Emit.EffectVmEmitBurn.selB.BURN := hc
    exact canonical_last (burnRow_reads amt hash pre post) burnRowGates
      (burn_gates_vac amt hash pre post) c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (burnRow_reads amt hash pre post) habsorb.2.2.1 habsorb.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (burnRow_reads amt hash pre post)

theorem burn_commit_iff (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : cellAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (burnRunnableCompleteSpec amt preRoots).descriptor
        ((burnRunnableCompleteSpec amt preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (burnRunnableCompleteSpec amt preRoots).descriptor
        ((burnRunnableCompleteSpec amt preRoots).buildRow hash pre post sr) true true)
    ↔ ((burnRunnableCompleteSpec amt preRoots).fullClause pre post sr
        ∧ ((burnRunnableCompleteSpec amt preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((burnRunnableCompleteSpec amt preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (burnRunnableCompleteSpec amt preRoots) hash pre post sr habsorb

def burnDemoPost (hash : List ℤ → ℤ) : CellState :=
  { goodBurnPost with commit := cellWideCommit hash goodBurnPost }

theorem burn_demo_absorbs (hash : List ℤ → ℤ) :
    cellAbsorbsTo goodBurnPreRoots hash goodBurnPre (burnDemoPost hash) goodBurnPreRoots := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num [burnDemoPost, goodBurnPost]

theorem burn_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (burnRunnableCompleteSpec 30 goodBurnPreRoots).descriptor
        (burnRow 30 hash goodBurnPre (burnDemoPost hash)) true false
      ∧ satisfiedVm hash (burnRunnableCompleteSpec 30 goodBurnPreRoots).descriptor
        (burnRow 30 hash goodBurnPre (burnDemoPost hash)) true true)
    ↔ ((burnRunnableCompleteSpec 30 goodBurnPreRoots).fullClause goodBurnPre (burnDemoPost hash) goodBurnPreRoots
        ∧ (burnRow 30 hash goodBurnPre (burnDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (burnRow 30 hash goodBurnPre (burnDemoPost hash))) :=
  burn_commit_iff 30 goodBurnPreRoots hash goodBurnPre (burnDemoPost hash) goodBurnPreRoots
    (burn_demo_absorbs hash)

theorem burn_canary_clause :
    ¬ (burnRunnableCompleteSpec 30 goodBurnPreRoots).fullClause goodBurnPre
        { goodBurnPost with balLo := 999 } goodBurnPreRoots :=
  burnFullClause_not_trivial

#assert_axioms burnRow_reads
#assert_axioms burn_commit_iff
#assert_axioms burn_commit_iff_demo
#assert_axioms burn_canary_clause

end Burn

/-! ## §H — pipelinedSend (freeze + nonce tick; canonical descriptor + the deployed range envelope).

pipelinedSend's per-cell faithfulness runs UNDER the explicit `PipelinedSendRowCanon` range envelope (the
deployed range-check invariant — every state-block cell of both windows is a canonical BabyBear
representative, incl. the `state_commit` column). Since our carrier `hash` is ABSTRACT (an arbitrary
`List ℤ → ℤ`, not the field-valued Poseidon2), the envelope on the commit column cannot be discharged for
an abstract `hash`; it is threaded through `absorbsTo` as the honest, named precondition it is (the same
one the deployed soundness carries). The `⟺` is real under it. -/

section PipelinedSend

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll gFieldPass)
open Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
  (SEL_PIPELINED_SEND pipelinedSendRowGates pipelinedSendVmDescriptor PipelinedSendRowIntent
   PipelinedSendRowCanon pipelinedSendVm_faithful RowEncodesSend CellSendSpec IsPipelinedSendRow)
open Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide
  (pipelinedSendVmDescriptorWide pipelinedSendWide_constraints_eq PipelinedSendFullClause
   pipelinedSendRunnableSpec sendPre sendPost goodPreRoots pipelinedSend_clause_not_trivial)

def pipelinedSendRow (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow SEL_PIPELINED_SEND hash pre post (fun _ => 0)

theorem pipelinedSendRow_reads (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (pipelinedSendRow hash pre post) SEL_PIPELINED_SEND hash pre post :=
  mkRow_reads SEL_PIPELINED_SEND (by decide) (by decide) hash pre post _

/-- The honest-witness precondition for pipelinedSend: the generic `cellAbsorbsTo` PLUS the deployed
`PipelinedSendRowCanon` range envelope on the witness (the field-representative invariant its
faithfulness runs under). -/
def pipelinedSendAbsorbsTo (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots) : Prop :=
  cellAbsorbsTo preRoots hash pre post sr ∧ PipelinedSendRowCanon (pipelinedSendRow hash pre post)

theorem pipelinedSend_intent (hash : List ℤ → ℤ) (pre post : CellState) (hspec : CellSendSpec pre post) :
    PipelinedSendRowIntent (pipelinedSendRow hash pre post) := by
  have h := pipelinedSendRow_reads hash pre post
  obtain ⟨hLo, hHi, hN, hFld, hCap, hRes⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo, h.sbLo]; exact hLo
  · rw [h.saHi, h.sbHi]; exact hHi
  · rw [h.saN, h.sbN, h.noopCold, sub_zero]; exact hN
  · rw [h.saCap, h.sbCap]; exact hCap
  · rw [h.saRes, h.sbRes]; exact hRes
  · intro i hi; rw [h.saF ⟨i, hi⟩, h.sbF ⟨i, hi⟩]; exact hFld ⟨i, hi⟩

theorem pipelinedSend_gates (hash : List ℤ → ℤ) (pre post : CellState)
    (hcanon : PipelinedSendRowCanon (pipelinedSendRow hash pre post)) (hspec : CellSendSpec pre post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ pipelinedSendRowGates) :
    c.holdsVm (pipelinedSendRow hash pre post) b false := by
  have hg := (pipelinedSendVm_faithful (pipelinedSendRow hash pre post) hcanon).mpr
    (pipelinedSend_intent hash pre post hspec)
  have hcc := hg c hc
  simp only [pipelinedSendRowGates, gFieldPassAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem pipelinedSend_gates_vac (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ pipelinedSendRowGates) : c.holdsVm (pipelinedSendRow hash pre post) true true := by
  simp only [pipelinedSendRowGates, gFieldPassAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

def pipelinedSendRunnableCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := pipelinedSendRunnableSpec preRoots
  buildRow := fun hash pre post _sr => pipelinedSendRow hash pre post
  absorbsTo := pipelinedSendAbsorbsTo preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(pipelinedSendRow_reads hash pre post).selHot, (pipelinedSendRow_reads hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    have h := pipelinedSendRow_reads hash pre post
    exact ⟨⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.sbC, h.saLo, h.saHi, h.saN, h.saF,
            h.saCap, h.saRes, h.saC, h.pOld, h.pNew⟩, habsorb.2, habsorb.1.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (pipelinedSendRow_reads hash pre post) habsorb.1.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ pipelinedSendRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates SEL_PIPELINED_SEND := hc
    exact canonical_active (pipelinedSendRow_reads hash pre post) pipelinedSendRowGates
      (pipelinedSend_gates hash pre post habsorb.2 hspec true) c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ pipelinedSendRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates SEL_PIPELINED_SEND := hc
    exact canonical_last (pipelinedSendRow_reads hash pre post) pipelinedSendRowGates
      (pipelinedSend_gates_vac hash pre post) c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (pipelinedSendRow_reads hash pre post) habsorb.1.2.2.1 habsorb.1.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (pipelinedSendRow_reads hash pre post)

theorem pipelinedSend_commit_iff (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState) (sr : SysRoots)
    (habsorb : pipelinedSendAbsorbsTo preRoots hash pre post sr) :
    (satisfiedVm hash (pipelinedSendRunnableCompleteSpec preRoots).descriptor
        ((pipelinedSendRunnableCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (pipelinedSendRunnableCompleteSpec preRoots).descriptor
        ((pipelinedSendRunnableCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((pipelinedSendRunnableCompleteSpec preRoots).fullClause pre post sr
        ∧ ((pipelinedSendRunnableCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((pipelinedSendRunnableCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (pipelinedSendRunnableCompleteSpec preRoots) hash pre post sr habsorb

def pipelinedSendDemoPost (hash : List ℤ → ℤ) : CellState :=
  { sendPost with commit := cellWideCommit hash sendPost }

/-- **`pipelinedSend_commit_iff_demo` — the both-windows `⟺`, concretely, UNDER the deployed range
envelope.** The envelope on the abstract-`hash` commit column cannot be discharged for an arbitrary
`hash`; it is the honest named hypothesis `hcanon` (true of the field-valued deployed Poseidon2 output). -/
theorem pipelinedSend_commit_iff_demo (hash : List ℤ → ℤ)
    (hcanon : PipelinedSendRowCanon (pipelinedSendRow hash sendPre (pipelinedSendDemoPost hash))) :
    (satisfiedVm hash (pipelinedSendRunnableCompleteSpec goodPreRoots).descriptor
        (pipelinedSendRow hash sendPre (pipelinedSendDemoPost hash)) true false
      ∧ satisfiedVm hash (pipelinedSendRunnableCompleteSpec goodPreRoots).descriptor
        (pipelinedSendRow hash sendPre (pipelinedSendDemoPost hash)) true true)
    ↔ ((pipelinedSendRunnableCompleteSpec goodPreRoots).fullClause sendPre (pipelinedSendDemoPost hash) goodPreRoots
        ∧ (pipelinedSendRow hash sendPre (pipelinedSendDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (pipelinedSendRow hash sendPre (pipelinedSendDemoPost hash))) :=
  pipelinedSend_commit_iff goodPreRoots hash sendPre (pipelinedSendDemoPost hash) goodPreRoots
    ⟨⟨rfl, rfl, ⟨by norm_num [pipelinedSendDemoPost, sendPost], by norm_num [pipelinedSendDemoPost, sendPost]⟩,
       ⟨by norm_num [pipelinedSendDemoPost, sendPost], by norm_num [pipelinedSendDemoPost, sendPost]⟩⟩, hcanon⟩

theorem pipelinedSend_canary_clause :
    ¬ (pipelinedSendRunnableCompleteSpec goodPreRoots).fullClause sendPre
        { sendPost with nonce := 5 } goodPreRoots :=
  pipelinedSend_clause_not_trivial

#assert_axioms pipelinedSendRow_reads
#assert_axioms pipelinedSend_commit_iff
#assert_axioms pipelinedSend_commit_iff_demo
#assert_axioms pipelinedSend_canary_clause

end PipelinedSend

/-! ## §I — setField (write `fields[slot]` + nonce tick; row-gates-only descriptor + range envelope).

CLASSIFICATION: setField is KERNEL-FIELD-ONLY (`gFieldWrite slot` writes `fields[slot]` = the runtime
`param1` NEW_VALUE directly; the write is bound into `state_commit` by the same per-row GROUP-4 layout the
other kernel tags use; there is NO heap / sorted-tree gate). So it is instantiated HERE.

The deployed `EffectVmEmitSetFieldFullState.setFieldRunnableSpec` places the range envelope
`SetFieldRowCanon` in its `isRow` field (`isRow := IsSetFieldRow ∧ SetFieldRowCanon`). The completeness
engine's `build_isRow` is UNCONDITIONAL (`∀ hash pre post sr`), and the envelope's `state_commit` column
(= the abstract `hash` output) is not field-bounded for an arbitrary `hash`, so that spec cannot be fed to
the engine directly. We supply an EQUIVALENT soundness base (`setFieldRunnableSpecB`) — the SAME wide
descriptor + SAME `fullClause`, with the envelope relocated from `isRow` to `decodeAfter` (where the
completeness engine's `build_decode` provides it under the honest-witness `absorbsTo`). This is a faithful
re-partition of the precondition, not a weakening: `decodeFull` still discharges via
`setFieldGates_give_cellSpec` from BOTH `IsSetFieldRow` and `SetFieldRowCanon`. -/

section SetField

open Dregg2.Circuit.Emit.EffectVmEmitSetField
  (SEL_SET_FIELD VALUE setFieldRowGates setFieldVmDescriptor gFieldWrite gOtherFieldsAll
   SetFieldRowIntent SetFieldRowCanon setFieldVm_faithful RowEncodesSF CellSetFieldSpec IsSetFieldRow)
open Dregg2.Circuit.Emit.EffectVmEmitSetFieldFullState
  (setFieldVmDescriptorWide setFieldWide_constraints_eq SetFieldFullClause setFieldGates_give_cellSpec
   setFieldPre setFieldPost setFieldPreRoots setField_clause_not_trivial)

def setFieldRow (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow SEL_SET_FIELD hash pre post (fun i => if i = VALUE then post.fields slot else 0)

theorem setFieldRow_reads (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (setFieldRow slot hash pre post) SEL_SET_FIELD hash pre post :=
  mkRow_reads SEL_SET_FIELD (by decide) (by decide) hash pre post _

theorem setFieldRow_val (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState) :
    (setFieldRow slot hash pre post).loc (prmCol VALUE) = post.fields slot := by
  show (mkRow SEL_SET_FIELD hash pre post (fun i => if i = VALUE then post.fields slot else 0)).loc
      (prmCol VALUE) = post.fields slot
  rw [mkRow_locGe SEL_SET_FIELD hash pre post _ (prmCol VALUE) (by decide)]
  rfl

/-- The structured decode of the witness (`RowEncodesSF`, incl. the value-carrier `= post.fields slot`). -/
theorem setFieldRow_encodes (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState) :
    RowEncodesSF slot (setFieldRow slot hash pre post) pre post := by
  have h := setFieldRow_reads slot hash pre post
  exact ⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.sbC, h.saLo, h.saHi, h.saN, h.saF,
         h.saCap, h.saRes, h.saC, setFieldRow_val slot hash pre post, h.pOld, h.pNew⟩

theorem setField_intent (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState)
    (hspec : CellSetFieldSpec slot pre (post.fields slot) post) :
    SetFieldRowIntent slot (setFieldRow slot hash pre post) := by
  have h := setFieldRow_reads slot hash pre post
  have hval := setFieldRow_val slot hash pre post
  obtain ⟨hwr, hlo, hhi, hnon, hcap, hres, hflds⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saF slot, hval]
  · rw [h.saLo, h.sbLo]; exact hlo
  · rw [h.saHi, h.sbHi]; exact hhi
  · rw [h.saN, h.sbN]; exact hnon
  · rw [h.saCap, h.sbCap]; exact hcap
  · rw [h.saRes, h.sbRes]; exact hres
  · intro i hi8 hine
    rw [h.saF ⟨i, hi8⟩, h.sbF ⟨i, hi8⟩]
    exact hflds ⟨i, hi8⟩ (fun hc => hine (congrArg Fin.val hc))

theorem setField_gates (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState)
    (hcanon : SetFieldRowCanon (setFieldRow slot hash pre post))
    (hspec : CellSetFieldSpec slot pre (post.fields slot) post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ setFieldRowGates slot) :
    c.holdsVm (setFieldRow slot hash pre post) b false := by
  have h := setFieldRow_reads slot hash pre post
  have hg := (setFieldVm_faithful slot (setFieldRow slot hash pre post) ⟨h.selHot, h.noopCold⟩ hcanon).mpr
    (setField_intent slot hash pre post hspec)
  have hcc := hg c hc
  simp only [setFieldRowGates, gOtherFieldsAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_filter] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem setField_gates_vac (slot : Fin 8) (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ setFieldRowGates slot) : c.holdsVm (setFieldRow slot hash pre post) true true := by
  simp only [setFieldRowGates, gOtherFieldsAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_filter] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

/-- The soundness base with the range envelope in `decodeAfter` (faithful re-partition; see the section
header). Same wide descriptor + `fullClause` as the deployed `setFieldRunnableSpec`. -/
def setFieldRunnableSpecB (slot : Fin 8) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor := setFieldVmDescriptorWide slot
  usesWideSites := rfl
  isRow := IsSetFieldRow
  decodeAfter := fun env pre post postRoots =>
    RowEncodesSF slot env pre post ∧ SetFieldRowCanon env ∧ postRoots = preRoots
  fullClause := SetFieldFullClause slot preRoots
  decodeFull := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hcanon, hroots⟩ := hdec
    exact ⟨setFieldGates_give_cellSpec slot env pre post hrow hcanon henc
            (setFieldWide_constraints_eq slot ▸ hgates), hroots⟩

def setFieldAbsorbsTo (slot : Fin 8) (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState)
    (sr : SysRoots) : Prop :=
  cellAbsorbsTo preRoots hash pre post sr ∧ SetFieldRowCanon (setFieldRow slot hash pre post)

def setFieldRunnableCompleteSpec (slot : Fin 8) (preRoots : SysRoots) :
    RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := setFieldRunnableSpecB slot preRoots
  buildRow := fun hash pre post _sr => setFieldRow slot hash pre post
  absorbsTo := setFieldAbsorbsTo slot preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(setFieldRow_reads slot hash pre post).selHot, (setFieldRow_reads slot hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    exact ⟨setFieldRow_encodes slot hash pre post, habsorb.2, habsorb.1.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (setFieldRow_reads slot hash pre post) habsorb.1.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ setFieldRowGates slot := hc
    exact setField_gates slot hash pre post habsorb.2 hspec true c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ setFieldRowGates slot := hc
    exact setField_gates_vac slot hash pre post c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (setFieldRow_reads slot hash pre post) habsorb.1.2.2.1 habsorb.1.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (setFieldRow_reads slot hash pre post)

theorem setField_commit_iff (slot : Fin 8) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (pre post : CellState) (sr : SysRoots) (habsorb : setFieldAbsorbsTo slot preRoots hash pre post sr) :
    (satisfiedVm hash (setFieldRunnableCompleteSpec slot preRoots).descriptor
        ((setFieldRunnableCompleteSpec slot preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (setFieldRunnableCompleteSpec slot preRoots).descriptor
        ((setFieldRunnableCompleteSpec slot preRoots).buildRow hash pre post sr) true true)
    ↔ ((setFieldRunnableCompleteSpec slot preRoots).fullClause pre post sr
        ∧ ((setFieldRunnableCompleteSpec slot preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((setFieldRunnableCompleteSpec slot preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (setFieldRunnableCompleteSpec slot preRoots) hash pre post sr habsorb

def setFieldDemoPost (hash : List ℤ → ℤ) : CellState :=
  { setFieldPost with commit := cellWideCommit hash setFieldPost }

/-- **`setField_commit_iff_demo` — the both-windows `⟺`, concretely (slot 0), UNDER the deployed range
envelope** (`SetFieldRowCanon`, an honest named hypothesis — the abstract-`hash` commit column is not
field-bounded, exactly as for pipelinedSend). -/
theorem setField_commit_iff_demo (hash : List ℤ → ℤ)
    (hcanon : SetFieldRowCanon (setFieldRow 0 hash setFieldPre (setFieldDemoPost hash))) :
    (satisfiedVm hash (setFieldRunnableCompleteSpec 0 setFieldPreRoots).descriptor
        (setFieldRow 0 hash setFieldPre (setFieldDemoPost hash)) true false
      ∧ satisfiedVm hash (setFieldRunnableCompleteSpec 0 setFieldPreRoots).descriptor
        (setFieldRow 0 hash setFieldPre (setFieldDemoPost hash)) true true)
    ↔ ((setFieldRunnableCompleteSpec 0 setFieldPreRoots).fullClause setFieldPre (setFieldDemoPost hash) setFieldPreRoots
        ∧ (setFieldRow 0 hash setFieldPre (setFieldDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (setFieldRow 0 hash setFieldPre (setFieldDemoPost hash))) :=
  setField_commit_iff 0 setFieldPreRoots hash setFieldPre (setFieldDemoPost hash) setFieldPreRoots
    ⟨⟨rfl, rfl, ⟨by norm_num [setFieldDemoPost, setFieldPost], by norm_num [setFieldDemoPost, setFieldPost]⟩,
       ⟨by norm_num [setFieldDemoPost, setFieldPost], by norm_num [setFieldDemoPost, setFieldPost]⟩⟩, hcanon⟩

theorem setField_canary_clause :
    ¬ (setFieldRunnableCompleteSpec 0 setFieldPreRoots).fullClause setFieldPre
        { setFieldPost with balLo := 999 } setFieldPreRoots :=
  setField_clause_not_trivial

#assert_axioms setFieldRow_reads
#assert_axioms setField_commit_iff
#assert_axioms setField_commit_iff_demo
#assert_axioms setField_canary_clause

end SetField

/-! ## §J — bridgeMint (balance credit by the value param + nonce tick; canonical descriptor + envelope).

Like setField, the deployed `bridgeMintRunnableSpec` places `BridgeMintRowCanon` in `isRow` (the engine's
`build_isRow` cannot discharge it for abstract `hash` — the commit column is an unbounded hash output) AND
pins the side-table carrier `sysRootsDigestCol = systemRootsDigest hash postRoots` in `decodeAfter` (which
`decodeFull` never reads — vestigial for the `⟺`). We supply an equivalent soundness base
(`bridgeMintRunnableSpecB`) — SAME wide descriptor + SAME `fullClause` — with the envelope relocated to
`decodeAfter` and the vestigial carrier pin dropped (the witness carries the frozen-empty carrier `0`, as
every other tag here does). Faithful re-partition; `decodeFull` still discharges via
`bridgeMintGates_give_cellSpec` from BOTH `IsBridgeMintRow` and `BridgeMintRowCanon`. -/

section BridgeMint

open Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
  (bridgeMintRowGates bridgeMintVmDescriptorWide bridgeMintWide_constraints_eq BridgeMintRowIntent
   BridgeMintRowCanon bridgeMintVm_faithful RowEncodes CellBridgeMintSpec IsBridgeMintRow
   BridgeMintFullClause bridgeMintGates_give_cellSpec gFieldFixAll widePreCell widePostCell wideRefRoots
   bridgeMint_wide_clause_refutable)

def bridgeMintPA (value : ℤ) : Nat → ℤ :=
  fun i => if i = Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.param.BRIDGE_MINT_VALUE_LO then value else 0

def bridgeMintRow (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv :=
  mkRow Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT hash pre post (bridgeMintPA value)

theorem bridgeMintRow_reads (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) :
    WReads (bridgeMintRow value hash pre post) Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT hash pre post :=
  mkRow_reads Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT (by decide) (by decide) hash pre post _

theorem bridgeMintRow_val (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) :
    (bridgeMintRow value hash pre post).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.param.BRIDGE_MINT_VALUE_LO) = value := by
  show (mkRow Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT hash pre post (bridgeMintPA value)).loc
      (prmCol Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.param.BRIDGE_MINT_VALUE_LO) = value
  rw [mkRow_locGe Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT hash pre post (bridgeMintPA value) _ (by decide)]
  rfl

theorem bridgeMintRow_encodes (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) :
    RowEncodes (bridgeMintRow value hash pre post) pre value post := by
  have h := bridgeMintRow_reads value hash pre post
  exact ⟨h.sbLo, h.sbHi, h.sbN, h.sbF, h.sbCap, h.sbRes, h.sbC, bridgeMintRow_val value hash pre post,
         h.saLo, h.saHi, h.saN, h.saF, h.saCap, h.saRes, h.saC, h.pOld, h.pNew⟩

theorem bridgeMint_intent (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState)
    (hspec : CellBridgeMintSpec pre value post) :
    BridgeMintRowIntent (bridgeMintRow value hash pre post) := by
  have h := bridgeMintRow_reads value hash pre post
  have hval := bridgeMintRow_val value hash pre post
  obtain ⟨hLo, hHi, hN, hFld, hCap, hRes⟩ := hspec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.saLo, h.sbLo, hval]; exact hLo
  · rw [h.saHi, h.sbHi]; exact hHi
  · rw [h.saN, h.sbN]; exact hN
  · rw [h.saCap, h.sbCap]; exact hCap
  · rw [h.saRes, h.sbRes]; exact hRes
  · intro i hi; rw [h.saF ⟨i, hi⟩, h.sbF ⟨i, hi⟩]; exact hFld ⟨i, hi⟩

theorem bridgeMint_gates (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState)
    (hcanon : BridgeMintRowCanon (bridgeMintRow value hash pre post))
    (hspec : CellBridgeMintSpec pre value post)
    (b : Bool) (c : VmConstraint) (hc : c ∈ bridgeMintRowGates) :
    c.holdsVm (bridgeMintRow value hash pre post) b false := by
  have h := bridgeMintRow_reads value hash pre post
  have hg := (bridgeMintVm_faithful (bridgeMintRow value hash pre post) ⟨h.selHot, h.noopCold⟩ hcanon).mpr
    (bridgeMint_intent value hash pre post hspec)
  have hcc := hg c hc
  simp only [bridgeMintRowGates, gFieldFixAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hcc

theorem bridgeMint_gates_vac (value : ℤ) (hash : List ℤ → ℤ) (pre post : CellState) (c : VmConstraint)
    (hc : c ∈ bridgeMintRowGates) : c.holdsVm (bridgeMintRow value hash pre post) true true := by
  simp only [bridgeMintRowGates, gFieldFixAll, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

/-- The soundness base with the envelope in `decodeAfter` + the vestigial carrier pin dropped (faithful
re-partition; see the section header). Same wide descriptor + `fullClause`. -/
def bridgeMintRunnableSpecB (value : ℤ) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor := bridgeMintVmDescriptorWide
  usesWideSites := rfl
  isRow := IsBridgeMintRow
  decodeAfter := fun env pre post postRoots =>
    RowEncodes env pre value post ∧ BridgeMintRowCanon env ∧ postRoots = preRoots
  fullClause := BridgeMintFullClause value preRoots
  decodeFull := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hcanon, hroots⟩ := hdec
    exact ⟨bridgeMintGates_give_cellSpec env pre post value hrow hcanon henc
            (bridgeMintWide_constraints_eq ▸ hgates), hroots⟩

def bridgeMintAbsorbsTo (value : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ) (pre post : CellState)
    (sr : SysRoots) : Prop :=
  cellAbsorbsTo preRoots hash pre post sr ∧ BridgeMintRowCanon (bridgeMintRow value hash pre post)

def bridgeMintRunnableCompleteSpec (value : ℤ) (preRoots : SysRoots) :
    RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := bridgeMintRunnableSpecB value preRoots
  buildRow := fun hash pre post _sr => bridgeMintRow value hash pre post
  absorbsTo := bridgeMintAbsorbsTo value preRoots
  build_isRow := fun hash pre post _sr =>
    ⟨(bridgeMintRow_reads value hash pre post).selHot, (bridgeMintRow_reads value hash pre post).noopCold⟩
  build_decode := by
    intro hash pre post sr habsorb
    exact ⟨bridgeMintRow_encodes value hash pre post, habsorb.2, habsorb.1.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact wreads_carrier (bridgeMintRow_reads value hash pre post) habsorb.1.1
  build_active := by
    intro hash pre post sr hclause habsorb c hc
    obtain ⟨hspec, _⟩ := hclause
    have hc2 : c ∈ bridgeMintRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT := hc
    exact canonical_active (bridgeMintRow_reads value hash pre post) bridgeMintRowGates
      (bridgeMint_gates value hash pre post habsorb.2 hspec true) c hc2
  build_last := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ bridgeMintRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                  ++ selectorGates Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.selBM.BRIDGE_MINT := hc
    exact canonical_last (bridgeMintRow_reads value hash pre post) bridgeMintRowGates
      (bridgeMint_gates_vac value hash pre post) c hc2
  build_ranges := by
    intro hash pre post sr hclause habsorb c hc
    have hc2 : c ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩] := hc
    exact wreads_ranges (bridgeMintRow_reads value hash pre post) habsorb.1.2.2.1 habsorb.1.2.2.2 c hc2
  build_newcommit := by
    intro hash pre post sr
    exact wreads_newcommit (bridgeMintRow_reads value hash pre post)

theorem bridgeMint_commit_iff (value : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (pre post : CellState) (sr : SysRoots) (habsorb : bridgeMintAbsorbsTo value preRoots hash pre post sr) :
    (satisfiedVm hash (bridgeMintRunnableCompleteSpec value preRoots).descriptor
        ((bridgeMintRunnableCompleteSpec value preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (bridgeMintRunnableCompleteSpec value preRoots).descriptor
        ((bridgeMintRunnableCompleteSpec value preRoots).buildRow hash pre post sr) true true)
    ↔ ((bridgeMintRunnableCompleteSpec value preRoots).fullClause pre post sr
        ∧ ((bridgeMintRunnableCompleteSpec value preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((bridgeMintRunnableCompleteSpec value preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (bridgeMintRunnableCompleteSpec value preRoots) hash pre post sr habsorb

def bridgeMintDemoPost (hash : List ℤ → ℤ) : CellState :=
  { widePostCell with commit := cellWideCommit hash widePostCell }

/-- **`bridgeMint_commit_iff_demo` — the both-windows `⟺`, concretely (credit 30), UNDER the deployed
range envelope** (`BridgeMintRowCanon`, an honest named hypothesis — the abstract-`hash` commit column is
not field-bounded, exactly as for pipelinedSend / setField). -/
theorem bridgeMint_commit_iff_demo (hash : List ℤ → ℤ)
    (hcanon : BridgeMintRowCanon (bridgeMintRow 30 hash widePreCell (bridgeMintDemoPost hash))) :
    (satisfiedVm hash (bridgeMintRunnableCompleteSpec 30 wideRefRoots).descriptor
        (bridgeMintRow 30 hash widePreCell (bridgeMintDemoPost hash)) true false
      ∧ satisfiedVm hash (bridgeMintRunnableCompleteSpec 30 wideRefRoots).descriptor
        (bridgeMintRow 30 hash widePreCell (bridgeMintDemoPost hash)) true true)
    ↔ ((bridgeMintRunnableCompleteSpec 30 wideRefRoots).fullClause widePreCell (bridgeMintDemoPost hash) wideRefRoots
        ∧ (bridgeMintRow 30 hash widePreCell (bridgeMintDemoPost hash)).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (bridgeMintRow 30 hash widePreCell (bridgeMintDemoPost hash))) :=
  bridgeMint_commit_iff 30 wideRefRoots hash widePreCell (bridgeMintDemoPost hash) wideRefRoots
    ⟨⟨rfl, rfl, ⟨by norm_num [bridgeMintDemoPost, widePostCell], by norm_num [bridgeMintDemoPost, widePostCell]⟩,
       ⟨by norm_num [bridgeMintDemoPost, widePostCell], by norm_num [bridgeMintDemoPost, widePostCell]⟩⟩, hcanon⟩

theorem bridgeMint_canary_clause :
    ¬ (bridgeMintRunnableCompleteSpec 30 wideRefRoots).fullClause widePreCell
        { widePostCell with balLo := 999 } wideRefRoots :=
  bridgeMint_wide_clause_refutable

#assert_axioms bridgeMintRow_reads
#assert_axioms bridgeMint_commit_iff
#assert_axioms bridgeMint_commit_iff_demo
#assert_axioms bridgeMint_canary_clause

end BridgeMint

end Dregg2.Circuit.Emit.EffectVmFullStateTagsB
