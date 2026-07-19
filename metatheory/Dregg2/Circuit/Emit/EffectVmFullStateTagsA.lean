/-
# Dregg2.Circuit.Emit.EffectVmFullStateTagsA — the COMPLETENESS (`←`) leg + the literal `⟺`
(`runnable_full_commit_iff`) for the KERNEL/LIFECYCLE effect tags, as THIN instantiations of the
`EffectVmFullStateRunnableComplete` engine.

## What this adds

`EffectVmFullStateRunnable.runnable_full_sound` (+ each tag's `*_runnable_full_sound` in the
`*FullState` modules) is the SOUNDNESS half (`SAT ⟹ SEM`) over the WIDE runnable descriptor. The
engine `EffectVmFullStateRunnableComplete.runnable_full_commit_iff` welds the GENERIC completeness
(`SEM ⟹ SAT`, constructed witness) to that soundness into the literal biconditional, over the DEPLOYED
GROUP-4 `wideCommitOf` absorption. This file supplies the per-tag `RunnableFullStateCompleteSpec`
(the six completeness fields the engine recipe names) for eight kernel/lifecycle tags and FIRES the
`⟺` for each:

  IncrementNonce · SetVK · SetPermissions · MakeSovereign · CellSeal · CellUnseal · CellDestroy · Noop

Each rides the SAME crypto carrier (`Poseidon2Binding.Poseidon2SpongeCR`, discharged ONCE in the
engine); the genuine per-tag work is `build_active` — the effect's own per-row gates hold on the
honest witness (the CONVERSE of `decodeFull`), plus the shared transition/boundary/selector structure
proved once here over the constructed witness row `semKernelRow`.

## The witness row (`semKernelRow`)

`semKernelRow SEL hash pre post` is the analog of transfer's `semTransferRow` for the kernel/lifecycle
tags: the `state_before` block carries `pre`, the `state_after` block carries `post`, the GROUP-4
inter-digest aux columns carry the genuine inner `H4`s of `post`, the `sysRootsDigestCol` carrier is
`0` (the frozen-empty side-table digest, EXACTLY as transfer's reference completeness instance takes
it), the row's own effect selector `SEL` is hot, and `nxt` mirrors the after-block onto the next row's
before-block. The selector `SEL` is placed LAST in the `loc` if-chain (after every state/aux column and
the carrier), so every state/aux read reduces by `rfl` INDEPENDENTLY of `SEL` — one set of read lemmas
serves all tags; only `loc SEL = 1` / `loc NOOP = 0` are per-tag facts.

## The shared window helpers (`kernelWindowsSel` / `kernelWindowsNoSel`)

The kernel/lifecycle descriptors share the shape `rowGates ++ transitionAll ++ boundaryFirstPins ++
boundaryLastPins (++ selectorGates SEL)`. The transition continuity (from the `nxt` mirror), the four
boundary PI pins (from the witness `pub`), and the selector gate (`(1-noop)(1-sel)=0`) are proved ONCE
over `semKernelRow`; the per-tag content is only the row-gate satisfaction (`hrowActive`) from the full
clause, plus `hrowGate` (the row gates are all `.gate`, so vacuous on the wrap window).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; Poseidon2 CR enters ONLY
through the engine's `runnable_full_commit_iff` (the named carrier). NEW file; all imports read-only.
`fullClause` non-vacuous per tag (each `*FullState` module's `*_clause_not_trivial`); the commit
conjunct BITES (per-tag `canary_tamper_moves_commit`).
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState
import Dregg2.Circuit.Emit.EffectVmEmitSetVKFullState
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState
import Dregg2.Circuit.Emit.EffectVmEmitCellSealFullState
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState
import Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
import Dregg2.Circuit.Emit.EffectVmEmitNoopWide

namespace Dregg2.Circuit.Emit.EffectVmFullStateTagsA

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins eqToModEq gate_modEq_iff)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable (RunnableFullStateSpec wideHashSites wideCommitOf)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete
  (RunnableFullStateCompleteSpec WideCarrier wireCommitOfRow runnable_full_commit_iff
   runnable_full_complete)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec.SystemRoots (SysRoots emptySystemRoots)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — THE WITNESS ROW `semKernelRow` (shared across all kernel/lifecycle tags). -/

/-- The witnessing `loc` assignment for a kernel/lifecycle `(pre, post)` on selector `SEL`: the
`state_before` block carries `pre`, the `state_after` block carries `post`, the three GROUP-4 aux
inter-digest columns carry the genuine inner `H4`s of `post`, the `sysRootsDigestCol` carrier is `0`,
and the effect selector `SEL` is `1`. `SEL` is checked LAST, so every state/aux/carrier read reduces
by `rfl` regardless of `SEL`. -/
def semKernelLoc (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) : Assignment :=
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
    else if v = sysRootsDigestCol then 0
    else if v = SEL then 1
    else 0

/-- The witnessing public-input vector (OLD/NEW commits, init/final balances, actor nonce). -/
def semKernelPub (pre post : CellState) : Assignment :=
  fun k =>
    if k = pi.OLD_COMMIT then pre.commit
    else if k = pi.NEW_COMMIT then post.commit
    else if k = pi.INIT_BAL_LO then pre.balLo
    else if k = pi.INIT_BAL_HI then pre.balHi
    else if k = pi.FINAL_BAL_LO then post.balLo
    else if k = pi.FINAL_BAL_HI then post.balHi
    else if k = pi.ACTOR_NONCE then pre.nonce
    else 0

/-- The witnessing `VmRowEnv`: `loc = semKernelLoc`, `pub = semKernelPub`, and `nxt` mirrors the
after-state onto the next row's before-block (`nxt (sbCol i) = loc (saCol i)`). -/
def semKernelRow (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) : VmRowEnv where
  loc := semKernelLoc SEL hash pre post
  nxt := fun v => semKernelLoc SEL hash pre post (v + (STATE_SIZE + NUM_PARAMS))
  pub := semKernelPub pre post

/-! ### §1.1 — column reads (all `rfl`, generic in `SEL`; the selector reads are per-tag). -/

section Reads
variable (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)

@[local simp] theorem l_sbBalLo : (semKernelRow SEL hash pre post).loc (sbCol state.BALANCE_LO) = pre.balLo := rfl
@[local simp] theorem l_sbBalHi : (semKernelRow SEL hash pre post).loc (sbCol state.BALANCE_HI) = pre.balHi := rfl
@[local simp] theorem l_sbNonce : (semKernelRow SEL hash pre post).loc (sbCol state.NONCE) = pre.nonce := rfl
@[local simp] theorem l_sbCap : (semKernelRow SEL hash pre post).loc (sbCol state.CAP_ROOT) = pre.capRoot := rfl
@[local simp] theorem l_sbRes : (semKernelRow SEL hash pre post).loc (sbCol state.RESERVED) = pre.reserved := rfl
@[local simp] theorem l_sbCommit : (semKernelRow SEL hash pre post).loc (sbCol state.STATE_COMMIT) = pre.commit := rfl

@[local simp] theorem l_saBalLo : (semKernelRow SEL hash pre post).loc (saCol state.BALANCE_LO) = post.balLo := rfl
@[local simp] theorem l_saBalHi : (semKernelRow SEL hash pre post).loc (saCol state.BALANCE_HI) = post.balHi := rfl
@[local simp] theorem l_saNonce : (semKernelRow SEL hash pre post).loc (saCol state.NONCE) = post.nonce := rfl
@[local simp] theorem l_saCap : (semKernelRow SEL hash pre post).loc (saCol state.CAP_ROOT) = post.capRoot := rfl
@[local simp] theorem l_saRes : (semKernelRow SEL hash pre post).loc (saCol state.RESERVED) = post.reserved := rfl
@[local simp] theorem l_saCommit : (semKernelRow SEL hash pre post).loc (saCol state.STATE_COMMIT) = post.commit := rfl

@[local simp] theorem l_saF0 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 0)) = post.fields 0 := rfl
@[local simp] theorem l_saF1 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 1)) = post.fields 1 := rfl
@[local simp] theorem l_saF2 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 2)) = post.fields 2 := rfl
@[local simp] theorem l_saF3 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 3)) = post.fields 3 := rfl
@[local simp] theorem l_saF4 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 4)) = post.fields 4 := rfl
@[local simp] theorem l_saF5 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 5)) = post.fields 5 := rfl
@[local simp] theorem l_saF6 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 6)) = post.fields 6 := rfl
@[local simp] theorem l_saF7 : (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + 7)) = post.fields 7 := rfl

@[local simp] theorem l_auxI1 : (semKernelRow SEL hash pre post).loc (auxCol aux_off.STATE_INTER1)
    = hash [post.balLo, post.balHi, post.nonce, post.fields 0] := rfl
@[local simp] theorem l_auxI2 : (semKernelRow SEL hash pre post).loc (auxCol aux_off.STATE_INTER2)
    = hash [post.fields 1, post.fields 2, post.fields 3, post.fields 4] := rfl
@[local simp] theorem l_auxI3 : (semKernelRow SEL hash pre post).loc (auxCol aux_off.STATE_INTER3)
    = hash [post.fields 5, post.fields 6, post.fields 7, post.capRoot] := rfl
@[local simp] theorem l_sysroots : (semKernelRow SEL hash pre post).loc sysRootsDigestCol = 0 := rfl

@[local simp] theorem p_old : (semKernelRow SEL hash pre post).pub pi.OLD_COMMIT = pre.commit := rfl
@[local simp] theorem p_new : (semKernelRow SEL hash pre post).pub pi.NEW_COMMIT = post.commit := rfl
@[local simp] theorem p_initLo : (semKernelRow SEL hash pre post).pub pi.INIT_BAL_LO = pre.balLo := rfl
@[local simp] theorem p_initHi : (semKernelRow SEL hash pre post).pub pi.INIT_BAL_HI = pre.balHi := rfl
@[local simp] theorem p_finLo : (semKernelRow SEL hash pre post).pub pi.FINAL_BAL_LO = post.balLo := rfl
@[local simp] theorem p_finHi : (semKernelRow SEL hash pre post).pub pi.FINAL_BAL_HI = post.balHi := rfl
@[local simp] theorem p_actor : (semKernelRow SEL hash pre post).pub pi.ACTOR_NONCE = pre.nonce := rfl

/-- The field-block before-read at an arbitrary `Fin 8` index. -/
theorem l_sbF (i : Fin 8) :
    (semKernelRow SEL hash pre post).loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i := by
  fin_cases i <;> rfl

/-- The field-block after-read at an arbitrary `Fin 8` index. -/
theorem l_saF (i : Fin 8) :
    (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + i.val)) = post.fields i := by
  fin_cases i <;> rfl

/-- The transition continuity read: `nxt (sbCol i) = loc (saCol i)`. -/
theorem l_nxt (i : Nat) :
    (semKernelRow SEL hash pre post).nxt (sbCol i)
      = (semKernelRow SEL hash pre post).loc (saCol i) := by
  have harg : sbCol i + (STATE_SIZE + NUM_PARAMS) = saCol i := by
    simp only [sbCol, saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, STATE_SIZE, NUM_PARAMS,
      NUM_EFFECTS]
    omega
  show semKernelLoc SEL hash pre post (sbCol i + (STATE_SIZE + NUM_PARAMS))
      = semKernelLoc SEL hash pre post (saCol i)
  rw [harg]

end Reads

/-! ### §1.2 — the DECODE + CARRIER on `semKernelRow` (shared). -/

/-- The generic `RowEncodes`-shape decode of `semKernelRow` (before/after blocks + OLD/NEW pins), the
common body every tag's `RowEncodes*` is (a permutation/subset of). -/
theorem semKernel_decodes (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) :
    ((semKernelRow SEL hash pre post).loc (sbCol state.BALANCE_LO) = pre.balLo
      ∧ (semKernelRow SEL hash pre post).loc (sbCol state.BALANCE_HI) = pre.balHi
      ∧ (semKernelRow SEL hash pre post).loc (sbCol state.NONCE) = pre.nonce
      ∧ (∀ i : Fin 8, (semKernelRow SEL hash pre post).loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
      ∧ (semKernelRow SEL hash pre post).loc (sbCol state.CAP_ROOT) = pre.capRoot
      ∧ (semKernelRow SEL hash pre post).loc (sbCol state.RESERVED) = pre.reserved
      ∧ (semKernelRow SEL hash pre post).loc (sbCol state.STATE_COMMIT) = pre.commit
      ∧ (semKernelRow SEL hash pre post).loc (saCol state.BALANCE_LO) = post.balLo
      ∧ (semKernelRow SEL hash pre post).loc (saCol state.BALANCE_HI) = post.balHi
      ∧ (semKernelRow SEL hash pre post).loc (saCol state.NONCE) = post.nonce
      ∧ (∀ i : Fin 8, (semKernelRow SEL hash pre post).loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
      ∧ (semKernelRow SEL hash pre post).loc (saCol state.CAP_ROOT) = post.capRoot
      ∧ (semKernelRow SEL hash pre post).loc (saCol state.RESERVED) = post.reserved
      ∧ (semKernelRow SEL hash pre post).loc (saCol state.STATE_COMMIT) = post.commit
      ∧ (semKernelRow SEL hash pre post).pub pi.OLD_COMMIT = pre.commit
      ∧ (semKernelRow SEL hash pre post).pub pi.NEW_COMMIT = post.commit) :=
  ⟨rfl, rfl, rfl, l_sbF SEL hash pre post, rfl, rfl, rfl, rfl, rfl, rfl,
   l_saF SEL hash pre post, rfl, rfl, rfl, rfl, rfl⟩

/-- **`kernelWireCommit`** — the genuine wide commitment of `post`'s absorbed columns with the frozen
`0` side-table carrier: `wideCommitOf` of the 12 scalar cols + `0`. This is `wireCommitOfRow` read on
`semKernelRow` (whose carrier is `0`), and the honest-witness precondition names it. -/
def kernelWireCommit (hash : List ℤ → ℤ) (post : CellState) : ℤ :=
  wideCommitOf hash post.balLo post.balHi post.nonce
    (post.fields 0) (post.fields 1) (post.fields 2) (post.fields 3)
    (post.fields 4) (post.fields 5) (post.fields 6) (post.fields 7) post.capRoot 0

/-- `wireCommitOfRow` on `semKernelRow` IS `kernelWireCommit` of `post` (the carrier is `0`). -/
theorem semKernel_wireCommit (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) :
    wireCommitOfRow hash (semKernelRow SEL hash pre post) = kernelWireCommit hash post := rfl

/-- The GROUP-4 carrier columns of `semKernelRow` are honestly filled (`WideCarrier`), GIVEN the
honest-witness commit precondition `post.commit = kernelWireCommit hash post`. -/
theorem semKernel_carrier (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (hcommit : post.commit = kernelWireCommit hash post) :
    WideCarrier hash (semKernelRow SEL hash pre post) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact hcommit

/-! ## §2 — the SHARED window helpers.

The kernel/lifecycle descriptors are `rowGates ++ transitionAll ++ boundaryFirstPins ++
boundaryLastPins (++ selectorGates SEL)`. The transition/pin/selector structure is proved ONCE over
`semKernelRow`; a per-tag instance supplies only the row-gate satisfaction and the "all gates" witness. -/

/-- Transitions hold on the ACTIVE window (from the `nxt` mirror). -/
theorem kernel_trans_active (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) :
    ∀ c ∈ transitionAll, c.holdsVm (semKernelRow SEL hash pre post) true false := by
  intro c hc
  simp only [transitionAll, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  show (semKernelRow SEL hash pre post).nxt (sbCol i)
      ≡ (semKernelRow SEL hash pre post).loc (saCol i) [ZMOD 2013265921]
  exact eqToModEq (l_nxt SEL hash pre post i)

/-- Transitions are vacuous on the WRAP window (`isLast = true`). -/
theorem kernel_trans_last (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) :
    ∀ c ∈ transitionAll, c.holdsVm (semKernelRow SEL hash pre post) true true := by
  intro c hc
  simp only [transitionAll, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact trivial

/-- The first-row boundary PI pins hold whenever `isFirst = true` (any `isLast`). -/
theorem kernel_first (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) (bLast : Bool) :
    ∀ c ∈ boundaryFirstPins, c.holdsVm (semKernelRow SEL hash pre post) true bLast := by
  intro c hc
  simp only [boundaryFirstPins, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact fun _ => eqToModEq rfl

/-- The last-row boundary PI pins are vacuous on the ACTIVE window (`isLast = false`). -/
theorem kernel_last_active (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) :
    ∀ c ∈ boundaryLastPins, c.holdsVm (semKernelRow SEL hash pre post) true false := by
  intro c hc
  simp only [boundaryLastPins, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact fun hcon => absurd hcon (by decide)

/-- The last-row boundary PI pins hold on the WRAP window (`isLast = true`). -/
theorem kernel_last_last (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState) :
    ∀ c ∈ boundaryLastPins, c.holdsVm (semKernelRow SEL hash pre post) true true := by
  intro c hc
  simp only [boundaryLastPins, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> exact fun _ => eqToModEq rfl

/-- The selector-binding gate holds on the ACTIVE window: `(1 - noop)·(1 - sel) = (1-0)(1-1) = 0`. -/
theorem kernel_selector_active (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (hsel : (semKernelRow SEL hash pre post).loc SEL = 1)
    (hnoop : (semKernelRow SEL hash pre post).loc sel.NOOP = 0) :
    (selectorGate SEL).holdsVm (semKernelRow SEL hash pre post) true false := by
  show selectorGateBody SEL |>.eval (semKernelRow SEL hash pre post).loc ≡ 0 [ZMOD 2013265921]
  simp only [selectorGateBody, EmittedExpr.eval]
  rw [hsel, hnoop]
  exact eqToModEq (by ring)

/-- **`kernelWindowsSel` — the ACTIVE + WRAP windows for a variant-A (effect-selector) descriptor.**
Given the row-gate satisfaction on the active window and the "all gates" witness, both deployed
windows of `rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates SEL`
hold on `semKernelRow`. -/
theorem kernelWindowsSel (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (rowGates : List VmConstraint)
    (hsel : (semKernelRow SEL hash pre post).loc SEL = 1)
    (hnoop : (semKernelRow SEL hash pre post).loc sel.NOOP = 0)
    (hrowActive : ∀ c ∈ rowGates, c.holdsVm (semKernelRow SEL hash pre post) true false)
    (hrowGate : ∀ c ∈ rowGates, ∃ b, c = VmConstraint.gate b) :
    (∀ c ∈ rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates SEL,
        c.holdsVm (semKernelRow SEL hash pre post) true false)
    ∧ (∀ c ∈ rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates SEL,
        c.holdsVm (semKernelRow SEL hash pre post) true true) := by
  constructor
  · intro c hc
    simp only [List.mem_append, or_assoc] at hc
    rcases hc with h | h | h | h | h
    · exact hrowActive c h
    · exact kernel_trans_active SEL hash pre post c h
    · exact kernel_first SEL hash pre post false c h
    · exact kernel_last_active SEL hash pre post c h
    · simp only [selectorGates, List.mem_singleton] at h
      subst h
      exact kernel_selector_active SEL hash pre post hsel hnoop
  · intro c hc
    simp only [List.mem_append, or_assoc] at hc
    rcases hc with h | h | h | h | h
    · obtain ⟨b, rfl⟩ := hrowGate c h; exact trivial
    · exact kernel_trans_last SEL hash pre post c h
    · exact kernel_first SEL hash pre post true c h
    · exact kernel_last_last SEL hash pre post c h
    · simp only [selectorGates, List.mem_singleton] at h
      subst h
      exact trivial

/-- **`kernelWindowsNoSel` — the ACTIVE + WRAP windows for a no-selector descriptor (the no-op).**
Both windows of `rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins`. -/
theorem kernelWindowsNoSel (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (rowGates : List VmConstraint)
    (hrowActive : ∀ c ∈ rowGates, c.holdsVm (semKernelRow SEL hash pre post) true false)
    (hrowGate : ∀ c ∈ rowGates, ∃ b, c = VmConstraint.gate b) :
    (∀ c ∈ rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins,
        c.holdsVm (semKernelRow SEL hash pre post) true false)
    ∧ (∀ c ∈ rowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins,
        c.holdsVm (semKernelRow SEL hash pre post) true true) := by
  constructor
  · intro c hc
    simp only [List.mem_append, or_assoc] at hc
    rcases hc with h | h | h | h
    · exact hrowActive c h
    · exact kernel_trans_active SEL hash pre post c h
    · exact kernel_first SEL hash pre post false c h
    · exact kernel_last_active SEL hash pre post c h
  · intro c hc
    simp only [List.mem_append, or_assoc] at hc
    rcases hc with h | h | h | h
    · obtain ⟨b, rfl⟩ := hrowGate c h; exact trivial
    · exact kernel_trans_last SEL hash pre post c h
    · exact kernel_first SEL hash pre post true c h
    · exact kernel_last_last SEL hash pre post c h

/-! ### §2.1 — the FREEZE+TICK row gates on the witness (shared by 6 tags).

The tags IncrementNonce / SetVK / SetPermissions / CellSeal / CellUnseal / CellDestroy all use the row
gate list `[gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass] ++ gFieldPassAll` (the frozen economic
block + the nonce TICK), with `gBalLoFreeze` a per-module def whose body is
`eSub (eSA BALANCE_LO) (eSB BALANCE_LO)`. This helper proves that list satisfied on `semKernelRow` from
the FROZEN+TICK per-cell facts (stated as mod-`p` congruences, so both the ℤ-equality specs and the
mod-`p` spec of setVK feed it). -/

/-- The freeze+tick row-gate list (with the explicit `gBalLoFreeze` body). -/
def freezeTickGates : List VmConstraint :=
  [ .gate (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)), .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`freezeTick_active`** — the freeze+tick row gates hold on `semKernelRow` (active window), from
the frozen economic block + nonce tick (mod-`p`). `hnoop` supplies `loc NOOP = 0` for the tick. -/
theorem freezeTick_active (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (hnoop : (semKernelRow SEL hash pre post).loc sel.NOOP = 0)
    (hbLo : post.balLo ≡ pre.balLo [ZMOD 2013265921])
    (hbHi : post.balHi ≡ pre.balHi [ZMOD 2013265921])
    (hnon : post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921])
    (hfld : ∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
    (hcap : post.capRoot ≡ pre.capRoot [ZMOD 2013265921])
    (hres : post.reserved ≡ pre.reserved [ZMOD 2013265921]) :
    ∀ c ∈ freezeTickGates, c.holdsVm (semKernelRow SEL hash pre post) true false := by
  intro c hc
  unfold freezeTickGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · show (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)).eval _ ≡ 0 [ZMOD 2013265921]
    simp only [eSA, eSB, eSub, EmittedExpr.eval, l_saBalLo, l_sbBalLo]
    exact (gate_modEq_iff (by ring)).mpr hbLo
  · show (gBalHi).eval _ ≡ 0 [ZMOD 2013265921]
    simp only [gBalHi, eSA, eSB, eSub, EmittedExpr.eval, l_saBalHi, l_sbBalHi]
    exact (gate_modEq_iff (by ring)).mpr hbHi
  · show (gNonce).eval _ ≡ 0 [ZMOD 2013265921]
    simp only [gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval, l_saNonce, l_sbNonce]
    rw [hnoop]
    exact (gate_modEq_iff (a := post.nonce) (b := pre.nonce + 1) (by ring)).mpr hnon
  · show (gCapPass).eval _ ≡ 0 [ZMOD 2013265921]
    simp only [gCapPass, eSA, eSB, eSub, EmittedExpr.eval, l_saCap, l_sbCap]
    exact (gate_modEq_iff (by ring)).mpr hcap
  · show (gResPass).eval _ ≡ 0 [ZMOD 2013265921]
    simp only [gResPass, eSA, eSB, eSub, EmittedExpr.eval, l_saRes, l_sbRes]
    exact (gate_modEq_iff (by ring)).mpr hres
  · show (gFieldPass i).eval _ ≡ 0 [ZMOD 2013265921]
    have hs := l_saF SEL hash pre post ⟨i, hi⟩
    have hb := l_sbF SEL hash pre post ⟨i, hi⟩
    simp only [Fin.val_mk] at hs hb
    simp only [gFieldPass, eSA, eSB, eSub, EmittedExpr.eval, hs, hb]
    exact (gate_modEq_iff (by ring)).mpr (hfld ⟨i, hi⟩)

/-- The freeze+tick row gates are all `.gate`. -/
theorem freezeTick_allGate : ∀ c ∈ freezeTickGates, ∃ b, c = VmConstraint.gate b := by
  intro c hc
  unfold freezeTickGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact ⟨_, rfl⟩

/-- The range teeth `[balLo:30, balHi:30]` hold on `semKernelRow` from the honest limb bounds. -/
theorem kernel_ranges2 (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (hbLo : 0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) (hbHi : 0 ≤ post.balHi ∧ post.balHi < 2 ^ 30) :
    ∀ r ∈ [(⟨saCol state.BALANCE_LO, 30⟩ : VmRange), ⟨saCol state.BALANCE_HI, 30⟩],
      r.holds (semKernelRow SEL hash pre post) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simpa only [VmRange.holds, l_saBalLo] using hbLo
  · simpa only [VmRange.holds, l_saBalHi] using hbHi

/-! ### §2.2 — the CANONICALITY envelope on the witness (for the tags whose spec bakes a range-check
invariant into `isRow`/`decodeAfter`).

The freeze+tick tags' `*RowCanon` (the deployed range-check invariant) is `∀ off < STATE_SIZE, both
windows' cells in [0,p)`, the NOOP selector boolean, and the pre-nonce tick in-field. On `semKernelRow`
each `sbCol off`/`saCol off` read is a `pre`/`post` cell, so the envelope reduces to per-cell
canonicality of `pre`/`post` (an honest precondition on the semantic states). -/

/-- Per-cell canonicality: every `CellState` field a canonical BabyBear representative in `[0, p)`. -/
def CellCanon (c : CellState) : Prop :=
  (0 ≤ c.balLo ∧ c.balLo < 2013265921)
  ∧ (0 ≤ c.balHi ∧ c.balHi < 2013265921)
  ∧ (0 ≤ c.nonce ∧ c.nonce < 2013265921)
  ∧ (∀ i : Fin 8, 0 ≤ c.fields i ∧ c.fields i < 2013265921)
  ∧ (0 ≤ c.capRoot ∧ c.capRoot < 2013265921)
  ∧ (0 ≤ c.commit ∧ c.commit < 2013265921)
  ∧ (0 ≤ c.reserved ∧ c.reserved < 2013265921)

/-- On `semKernelRow`, every `state_before`/`state_after` cell (`off < STATE_SIZE`) is canonical, from
per-cell canonicality of `pre`/`post`. -/
theorem semKernel_stateCanon (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (hpre : CellCanon pre) (hpost : CellCanon post) :
    ∀ off, off < STATE_SIZE →
      (0 ≤ (semKernelRow SEL hash pre post).loc (sbCol off)
        ∧ (semKernelRow SEL hash pre post).loc (sbCol off) < 2013265921)
      ∧ (0 ≤ (semKernelRow SEL hash pre post).loc (saCol off)
        ∧ (semKernelRow SEL hash pre post).loc (saCol off) < 2013265921) := by
  obtain ⟨pLo, pHi, pN, pF, pCap, pC, pR⟩ := hpre
  obtain ⟨qLo, qHi, qN, qF, qCap, qC, qR⟩ := hpost
  intro off hoff
  simp only [STATE_SIZE] at hoff
  interval_cases off
  · exact ⟨pLo, qLo⟩
  · exact ⟨pHi, qHi⟩
  · exact ⟨pN, qN⟩
  · exact ⟨pF 0, qF 0⟩
  · exact ⟨pF 1, qF 1⟩
  · exact ⟨pF 2, qF 2⟩
  · exact ⟨pF 3, qF 3⟩
  · exact ⟨pF 4, qF 4⟩
  · exact ⟨pF 5, qF 5⟩
  · exact ⟨pF 6, qF 6⟩
  · exact ⟨pF 7, qF 7⟩
  · exact ⟨pCap, qCap⟩
  · exact ⟨pC, qC⟩
  · exact ⟨pR, qR⟩

/-- The full freeze+tick `*RowCanon` envelope on `semKernelRow` (the `∀ off` cell canonicality ∧ the
boolean NOOP ∧ the in-field pre-nonce tick), from per-cell canonicality + the honest `hnoop`/`hnonce`. -/
theorem semKernel_rowCanon (SEL : Nat) (hash : List ℤ → ℤ) (pre post : CellState)
    (hnoop : (semKernelRow SEL hash pre post).loc sel.NOOP = 0)
    (hpre : CellCanon pre) (hpost : CellCanon post) (hnonce : pre.nonce + 1 < 2013265921) :
    (∀ off, off < STATE_SIZE →
        (0 ≤ (semKernelRow SEL hash pre post).loc (sbCol off)
          ∧ (semKernelRow SEL hash pre post).loc (sbCol off) < 2013265921)
        ∧ (0 ≤ (semKernelRow SEL hash pre post).loc (saCol off)
          ∧ (semKernelRow SEL hash pre post).loc (saCol off) < 2013265921))
    ∧ ((semKernelRow SEL hash pre post).loc sel.NOOP = 0
        ∨ (semKernelRow SEL hash pre post).loc sel.NOOP = 1)
    ∧ (semKernelRow SEL hash pre post).loc (sbCol state.NONCE) + 1 < 2013265921 :=
  ⟨semKernel_stateCanon SEL hash pre post hpre hpost, Or.inl hnoop, hnonce⟩

/-! ## §3 — INCREMENTNONCE: the per-tag `RunnableFullStateCompleteSpec` + the literal `⟺`.

The `*FullState` module's `incNonceRunnableSpec` bakes the range-check envelope `IncNonceRowCanon` into
`isRow`; the completeness engine's `build_isRow` has NO precondition, so we RE-PACKAGE the soundness
spec with the envelope moved to `decodeAfter` (exactly cellUnseal's shape) — `decodeFull` is the SAME
`incNonceGates_give_cellSpec`, so the `→` soundness is unchanged. -/

section IncrementNonce
open Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
  (SEL_INCREMENT_NONCE IsIncNonceRow IncNonceRowCanon incrementNonceVmDescriptor RowEncodesIncNonce
   CellIncNonceSpec)
open Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState
  (incrementNonceVmDescriptorWide incNonceWide_constraints_eq incNonceGates_give_cellSpec
   IncNonceFullClause)

/-- The soundness spec re-packaged with `IncNonceRowCanon` in `decodeAfter` (so the completeness
engine's precondition-free `build_isRow` is dischargeable). `decodeFull` is `incNonceGates_give_cellSpec`. -/
def incNonceSpec' (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := incrementNonceVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsIncNonceRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesIncNonce env pre post ∧ postRoots = preRoots ∧ IncNonceRowCanon env
  fullClause    := IncNonceFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, hcanon⟩ := hdec
    exact ⟨incNonceGates_give_cellSpec env pre post hrow.2 hcanon henc
            (incNonceWide_constraints_eq ▸ hgates), hroots⟩

/-- `loc SEL_INCREMENT_NONCE = 1` on the witness row. -/
theorem incNonce_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_INCREMENT_NONCE hash pre post).loc SEL_INCREMENT_NONCE = 1 := by
  show semKernelLoc SEL_INCREMENT_NONCE hash pre post SEL_INCREMENT_NONCE = 1
  simp only [semKernelLoc, SEL_INCREMENT_NONCE, sbCol, saCol, auxCol, sysRootsDigestCol,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    EFFECT_VM_WIDTH, state.BALANCE_LO, state.BALANCE_HI, state.NONCE, state.FIELD_BASE, state.CAP_ROOT,
    state.STATE_COMMIT, state.RESERVED, aux_off.STATE_INTER1, aux_off.STATE_INTER2,
    aux_off.STATE_INTER3]
  norm_num

/-- `loc sel.NOOP = 0` on the witness row. -/
theorem incNonce_noop (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_INCREMENT_NONCE hash pre post).loc sel.NOOP = 0 := by
  show semKernelLoc SEL_INCREMENT_NONCE hash pre post sel.NOOP = 0
  simp only [semKernelLoc, SEL_INCREMENT_NONCE, sel.NOOP, sbCol, saCol, auxCol, sysRootsDigestCol,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    EFFECT_VM_WIDTH, state.BALANCE_LO, state.BALANCE_HI, state.NONCE, state.FIELD_BASE, state.CAP_ROOT,
    state.STATE_COMMIT, state.RESERVED, aux_off.STATE_INTER1, aux_off.STATE_INTER2,
    aux_off.STATE_INTER3]
  norm_num

/-- **`incNonceCompleteSpec`** — the completeness data for incrementNonce: extends the soundness
`incNonceRunnableSpec` with the constructed witness `semKernelRow SEL_INCREMENT_NONCE`, the honest-witness
precondition (genuine wire commit + frozen roots + in-range limbs + per-cell canonicality), and the six
completeness fields. The genuine per-tag work is `build_active` (the freeze+tick row gates on the honest
witness, via `freezeTick_active`). -/
def incNonceCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := incNonceSpec' preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_INCREMENT_NONCE hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post
    ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30)
    ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    ∧ CellCanon pre ∧ CellCanon post ∧ pre.nonce + 1 < 2013265921
  build_isRow := by
    intro hash pre post sr
    exact ⟨incNonce_sel hash pre post, incNonce_noop hash pre post⟩
  build_decode := by
    intro hash pre post sr habsorb
    obtain ⟨_, hroots, _, _, hpre, hpost, hnonce⟩ := habsorb
    exact ⟨semKernel_decodes _ hash pre post, hroots,
      semKernel_rowCanon SEL_INCREMENT_NONCE hash pre post (incNonce_noop hash pre post) hpre hpost hnonce⟩
  build_carrier := by
    intro hash pre post sr habsorb
    exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_INCREMENT_NONCE hash pre post freezeTickGates
      (incNonce_sel hash pre post) (incNonce_noop hash pre post)
      (freezeTick_active SEL_INCREMENT_NONCE hash pre post (incNonce_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres]))
      freezeTick_allGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_INCREMENT_NONCE hash pre post freezeTickGates
      (incNonce_sel hash pre post) (incNonce_noop hash pre post)
      (freezeTick_active SEL_INCREMENT_NONCE hash pre post (incNonce_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres]))
      freezeTick_allGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_INCREMENT_NONCE hash pre post habsorb.2.2.1 habsorb.2.2.2.1
  build_newcommit := by
    intro hash pre post sr
    rfl

/-- **`incNonce_commit_iff` — THE LITERAL `⟺` for incrementNonce.** The constructed witness satisfies
the WIDE runnable incrementNonce descriptor on BOTH deployed windows IFF the decoded transition is the
genuine full 17-field post-state (`IncNonceFullClause` — economic block frozen, nonce ticked, roots
frozen) AND the published `NEW_COMMIT` is the genuine wire commit. Both directions REAL, modulo the ONE
named Poseidon2 carrier discharged in the engine. -/
theorem incNonce_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (pre post : CellState) (sr : SysRoots)
    (habsorb : (incNonceCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (incNonceCompleteSpec preRoots).descriptor
        ((incNonceCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (incNonceCompleteSpec preRoots).descriptor
        ((incNonceCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((incNonceCompleteSpec preRoots).fullClause pre post sr
        ∧ ((incNonceCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((incNonceCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (incNonceCompleteSpec preRoots) hash pre post sr habsorb

/-! ### The concrete demo (bal_lo 100 frozen, nonce 5 → 6) + the clause canary. -/

/-- The demo pre-state (bal_lo 100, nonce 5, everything else 0 — canonical). -/
def incNonceDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The demo post-state's non-commit block (bal_lo 100 FROZEN, nonce 6 TICKED). -/
def incNonceDemoPostBase : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The demo post-state: the non-commit block with the stored commit set to the genuine wire commit
(so the honest-witness commit precondition holds by construction). -/
def incNonceDemoPost (hash : List ℤ → ℤ) : CellState :=
  { incNonceDemoPostBase with commit := kernelWireCommit hash incNonceDemoPostBase }

/-- **`incNonce_commit_iff_demo` — the both-windows `⟺`, discharged on a concrete transition.** The
honest side condition `hcanon` (the deployed Poseidon2 digest is a reduced field element in `[0, p)`)
is the same one the base soundness carries (`incNonceDescriptor_full_sound`'s `hpubc`). -/
theorem incNonce_commit_iff_demo (hash : List ℤ → ℤ)
    (hcanon : 0 ≤ kernelWireCommit hash incNonceDemoPostBase
      ∧ kernelWireCommit hash incNonceDemoPostBase < 2013265921) :
    (satisfiedVm hash (incNonceCompleteSpec emptySystemRoots).descriptor
        ((incNonceCompleteSpec emptySystemRoots).buildRow hash incNonceDemoPre (incNonceDemoPost hash) emptySystemRoots) true false
      ∧ satisfiedVm hash (incNonceCompleteSpec emptySystemRoots).descriptor
        ((incNonceCompleteSpec emptySystemRoots).buildRow hash incNonceDemoPre (incNonceDemoPost hash) emptySystemRoots) true true)
    ↔ ((incNonceCompleteSpec emptySystemRoots).fullClause incNonceDemoPre (incNonceDemoPost hash) emptySystemRoots
        ∧ ((incNonceCompleteSpec emptySystemRoots).buildRow hash incNonceDemoPre (incNonceDemoPost hash) emptySystemRoots).pub pi.NEW_COMMIT
            = wireCommitOfRow hash
                ((incNonceCompleteSpec emptySystemRoots).buildRow hash incNonceDemoPre (incNonceDemoPost hash) emptySystemRoots)) := by
  refine incNonce_commit_iff hash emptySystemRoots incNonceDemoPre (incNonceDemoPost hash) emptySystemRoots ?_
  refine ⟨rfl, rfl, ⟨by norm_num [incNonceDemoPost, incNonceDemoPostBase], by norm_num [incNonceDemoPost, incNonceDemoPostBase]⟩,
    ⟨by norm_num [incNonceDemoPost, incNonceDemoPostBase], by norm_num [incNonceDemoPost, incNonceDemoPostBase]⟩, ?_, ?_, ?_⟩
  · exact ⟨by norm_num [incNonceDemoPre], by norm_num [incNonceDemoPre], by norm_num [incNonceDemoPre],
      fun i => by norm_num [incNonceDemoPre], by norm_num [incNonceDemoPre], by norm_num [incNonceDemoPre],
      by norm_num [incNonceDemoPre]⟩
  · exact ⟨by norm_num [incNonceDemoPost, incNonceDemoPostBase], by norm_num [incNonceDemoPost, incNonceDemoPostBase],
      by norm_num [incNonceDemoPost, incNonceDemoPostBase], fun i => by norm_num [incNonceDemoPost, incNonceDemoPostBase],
      by norm_num [incNonceDemoPost, incNonceDemoPostBase], hcanon,
      by norm_num [incNonceDemoPost, incNonceDemoPostBase]⟩
  · norm_num [incNonceDemoPre]

/-- **`incNonce_canary_clause` — the `⟺` LHS is two-valued (the clause conjunct BITES).** A post whose
nonce is NOT the tick (`incNonceDemoPre.nonce = 5`, demanding `6`, but a forged `99`) FAILS the full
clause — so a `True`/`P → P` bridge could not separate this. (The commit conjunct BITES via the
engine's `canary_bogus_commit_unsat` / `canary_tamper_moves_commit`.) -/
theorem incNonce_canary_clause :
    ¬ (incNonceCompleteSpec emptySystemRoots).fullClause incNonceDemoPre
        { incNonceDemoPre with nonce := 99 } emptySystemRoots := by
  rintro ⟨⟨_, _, hn, _, _, _⟩, _⟩
  simp only [incNonceDemoPre] at hn
  norm_num at hn

end IncrementNonce

/-! ## §4 — a per-tag `loc SEL = 1` / `loc NOOP = 0` tactic macro (the selector reads). -/

/-- Discharges `(semKernelRow SEL ..).loc c = k` for a concrete selector/NOOP column by unfolding the
witness `loc` to a literal if-chain. -/
macro "kernel_col_tac" : tactic =>
  `(tactic| (simp only [semKernelRow, semKernelLoc, sbCol, saCol, auxCol, sysRootsDigestCol,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    EFFECT_VM_WIDTH, sel.NOOP, state.BALANCE_LO, state.BALANCE_HI, state.NONCE, state.FIELD_BASE,
    state.CAP_ROOT, state.STATE_COMMIT, state.RESERVED, aux_off.STATE_INTER1, aux_off.STATE_INTER2,
    aux_off.STATE_INTER3]; norm_num))

/-! ## §5 — SETVK (EXTEND the `*FullState` spec; the per-cell spec is mod-`p`, no canon envelope). -/

section SetVK
open Dregg2.Circuit.Emit.EffectVmEmitSetVK (SEL_SET_VK IsSetVKRow RowEncodesVK CellSetVKSpec)
open Dregg2.Circuit.Emit.EffectVmEmitSetVKFullState (setVKVmDescriptorWide setVKRunnableSpec SetVKFullClause)

theorem setVK_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_SET_VK hash pre post).loc SEL_SET_VK = 1 := by
  show semKernelLoc SEL_SET_VK hash pre post SEL_SET_VK = 1
  simp only [SEL_SET_VK]; kernel_col_tac

theorem setVK_noop (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_SET_VK hash pre post).loc sel.NOOP = 0 := by
  show semKernelLoc SEL_SET_VK hash pre post sel.NOOP = 0
  simp only [SEL_SET_VK]; kernel_col_tac

/-- **`setVKCompleteSpec`** — completeness data for setVerificationKey (extends `setVKRunnableSpec`). -/
def setVKCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := setVKRunnableSpec preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_SET_VK hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
  build_isRow := by intro hash pre post sr; exact ⟨setVK_sel hash pre post, setVK_noop hash pre post⟩
  build_decode := by intro hash pre post sr habsorb; exact ⟨semKernel_decodes _ hash pre post, habsorb.2.1⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_SET_VK hash pre post freezeTickGates
      (setVK_sel hash pre post) (setVK_noop hash pre post)
      (freezeTick_active SEL_SET_VK hash pre post (setVK_noop hash pre post)
        hbLo hbHi hnon hfld hcap hres) freezeTick_allGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_SET_VK hash pre post freezeTickGates
      (setVK_sel hash pre post) (setVK_noop hash pre post)
      (freezeTick_active SEL_SET_VK hash pre post (setVK_noop hash pre post)
        hbLo hbHi hnon hfld hcap hres) freezeTick_allGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_SET_VK hash pre post habsorb.2.2.1 habsorb.2.2.2
  build_newcommit := by intro hash pre post sr; rfl

/-- **`setVK_commit_iff` — THE LITERAL `⟺` for setVerificationKey.** -/
theorem setVK_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (setVKCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (setVKCompleteSpec preRoots).descriptor
        ((setVKCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (setVKCompleteSpec preRoots).descriptor
        ((setVKCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((setVKCompleteSpec preRoots).fullClause pre post sr
        ∧ ((setVKCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((setVKCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (setVKCompleteSpec preRoots) hash pre post sr habsorb

/-- Demo states + the clause canary. -/
def setVKDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`setVK_canary_clause` — the clause conjunct BITES.** A forged frozen `bal_lo` (`999 ≠ 100`) fails
the full clause. -/
theorem setVK_canary_clause :
    ¬ (setVKCompleteSpec emptySystemRoots).fullClause setVKDemoPre
        { setVKDemoPre with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [setVKDemoPre, Int.ModEq] at hbal
  norm_num at hbal

end SetVK

/-! ## §6 — SETPERMISSIONS (FRESH spec; `PermCellSpec` is ℤ-equality, canon envelope in isRow → relocated). -/

section SetPermissions
open Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
  (SEL_SET_PERMS IsSetPermsRow SetPermsRowCanon setPermsVmDescriptor RowEncodesPerms PermCellSpec)
open Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState
  (setPermsVmDescriptorWide setPermsWide_constraints_eq setPermsGates_give_cellSpec SetPermsFullClause)

theorem setPerms_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_SET_PERMS hash pre post).loc SEL_SET_PERMS = 1 := by
  show semKernelLoc SEL_SET_PERMS hash pre post SEL_SET_PERMS = 1
  simp only [SEL_SET_PERMS]; kernel_col_tac

theorem setPerms_noop (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_SET_PERMS hash pre post).loc sel.NOOP = 0 := by
  show semKernelLoc SEL_SET_PERMS hash pre post sel.NOOP = 0
  simp only [SEL_SET_PERMS]; kernel_col_tac

/-- The soundness spec re-packaged with `SetPermsRowCanon` in `decodeAfter`. -/
def setPermsSpec' (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := setPermsVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsSetPermsRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesPerms env pre post ∧ postRoots = preRoots ∧ SetPermsRowCanon env
  fullClause    := SetPermsFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, hcanon⟩ := hdec
    exact ⟨setPermsGates_give_cellSpec env pre post hrow.2 hcanon henc
            (setPermsWide_constraints_eq ▸ hgates), hroots⟩

/-- **`setPermsCompleteSpec`** — completeness data for setPermissions. -/
def setPermsCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := setPermsSpec' preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_SET_PERMS hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    ∧ CellCanon pre ∧ CellCanon post ∧ pre.nonce + 1 < 2013265921
  build_isRow := by intro hash pre post sr; exact ⟨setPerms_sel hash pre post, setPerms_noop hash pre post⟩
  build_decode := by
    intro hash pre post sr habsorb
    obtain ⟨_, hroots, _, _, hpre, hpost, hnonce⟩ := habsorb
    exact ⟨semKernel_decodes _ hash pre post, hroots,
      semKernel_rowCanon SEL_SET_PERMS hash pre post (setPerms_noop hash pre post) hpre hpost hnonce⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_SET_PERMS hash pre post freezeTickGates
      (setPerms_sel hash pre post) (setPerms_noop hash pre post)
      (freezeTick_active SEL_SET_PERMS hash pre post (setPerms_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_SET_PERMS hash pre post freezeTickGates
      (setPerms_sel hash pre post) (setPerms_noop hash pre post)
      (freezeTick_active SEL_SET_PERMS hash pre post (setPerms_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_SET_PERMS hash pre post habsorb.2.2.1 habsorb.2.2.2.1
  build_newcommit := by intro hash pre post sr; rfl

/-- **`setPerms_commit_iff` — THE LITERAL `⟺` for setPermissions.** -/
theorem setPerms_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (setPermsCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (setPermsCompleteSpec preRoots).descriptor
        ((setPermsCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (setPermsCompleteSpec preRoots).descriptor
        ((setPermsCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((setPermsCompleteSpec preRoots).fullClause pre post sr
        ∧ ((setPermsCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((setPermsCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (setPermsCompleteSpec preRoots) hash pre post sr habsorb

def setPermsDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`setPerms_canary_clause` — the clause conjunct BITES.** -/
theorem setPerms_canary_clause :
    ¬ (setPermsCompleteSpec emptySystemRoots).fullClause setPermsDemoPre
        { setPermsDemoPre with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [setPermsDemoPre] at hbal
  norm_num at hbal

end SetPermissions

/-! ## §7 — CELLSEAL (FRESH spec; ℤ-equality per-cell spec, canon envelope relocated). -/

section CellSeal
open Dregg2.Circuit.Emit.EffectVmEmitCellSeal (SEL_CELLSEAL CellSealRowCanon cellSealVmDescriptor RowEncodesSeal CellSealCellSpec)
open Dregg2.Circuit.Emit.EffectVmEmitCellSealFullState
  (IsCellSealRow cellSealVmDescriptorWide cellSealWide_constraints_eq cellSealGates_give_cellSpec CellSealFullClause)

theorem cellSeal_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_CELLSEAL hash pre post).loc SEL_CELLSEAL = 1 := by
  show semKernelLoc SEL_CELLSEAL hash pre post SEL_CELLSEAL = 1
  simp only [SEL_CELLSEAL]; kernel_col_tac

theorem cellSeal_noop (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_CELLSEAL hash pre post).loc sel.NOOP = 0 := by
  show semKernelLoc SEL_CELLSEAL hash pre post sel.NOOP = 0
  simp only [SEL_CELLSEAL]; kernel_col_tac

def cellSealSpec' (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := cellSealVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsCellSealRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesSeal env pre post ∧ postRoots = preRoots ∧ CellSealRowCanon env
  fullClause    := CellSealFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, hcanon⟩ := hdec
    exact ⟨cellSealGates_give_cellSpec env pre post hrow.2 hcanon henc
            (cellSealWide_constraints_eq ▸ hgates), hroots⟩

def cellSealCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := cellSealSpec' preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_CELLSEAL hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    ∧ CellCanon pre ∧ CellCanon post ∧ pre.nonce + 1 < 2013265921
  build_isRow := by intro hash pre post sr; exact ⟨cellSeal_sel hash pre post, cellSeal_noop hash pre post⟩
  build_decode := by
    intro hash pre post sr habsorb
    obtain ⟨_, hroots, _, _, hpre, hpost, hnonce⟩ := habsorb
    exact ⟨semKernel_decodes _ hash pre post, hroots,
      semKernel_rowCanon SEL_CELLSEAL hash pre post (cellSeal_noop hash pre post) hpre hpost hnonce⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_CELLSEAL hash pre post freezeTickGates
      (cellSeal_sel hash pre post) (cellSeal_noop hash pre post)
      (freezeTick_active SEL_CELLSEAL hash pre post (cellSeal_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_CELLSEAL hash pre post freezeTickGates
      (cellSeal_sel hash pre post) (cellSeal_noop hash pre post)
      (freezeTick_active SEL_CELLSEAL hash pre post (cellSeal_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_CELLSEAL hash pre post habsorb.2.2.1 habsorb.2.2.2.1
  build_newcommit := by intro hash pre post sr; rfl

/-- **`cellSeal_commit_iff` — THE LITERAL `⟺` for cellSeal.** -/
theorem cellSeal_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (cellSealCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (cellSealCompleteSpec preRoots).descriptor
        ((cellSealCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (cellSealCompleteSpec preRoots).descriptor
        ((cellSealCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((cellSealCompleteSpec preRoots).fullClause pre post sr
        ∧ ((cellSealCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((cellSealCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (cellSealCompleteSpec preRoots) hash pre post sr habsorb

def cellSealDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`cellSeal_canary_clause` — the clause conjunct BITES.** -/
theorem cellSeal_canary_clause :
    ¬ (cellSealCompleteSpec emptySystemRoots).fullClause cellSealDemoPre
        { cellSealDemoPre with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [cellSealDemoPre] at hbal
  norm_num at hbal

end CellSeal

/-! ## §8 — CELLUNSEAL (EXTEND; canon envelope ALREADY in `decodeAfter`). -/

section CellUnseal
open Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
  (SEL_CELLUNSEAL IsCellUnsealRow CellUnsealRowCanon cellUnsealVmDescriptorWide cellUnsealRunnableSpec
   RowEncodesUnseal CellUnsealCellSpec CellUnsealFullClause)

theorem cellUnseal_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_CELLUNSEAL hash pre post).loc SEL_CELLUNSEAL = 1 := by
  show semKernelLoc SEL_CELLUNSEAL hash pre post SEL_CELLUNSEAL = 1
  simp only [SEL_CELLUNSEAL]; kernel_col_tac

theorem cellUnseal_noop (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_CELLUNSEAL hash pre post).loc sel.NOOP = 0 := by
  show semKernelLoc SEL_CELLUNSEAL hash pre post sel.NOOP = 0
  simp only [SEL_CELLUNSEAL]; kernel_col_tac

def cellUnsealCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := cellUnsealRunnableSpec preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_CELLUNSEAL hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    ∧ CellCanon pre ∧ CellCanon post ∧ pre.nonce + 1 < 2013265921
  build_isRow := by intro hash pre post sr; exact ⟨cellUnseal_sel hash pre post, cellUnseal_noop hash pre post⟩
  build_decode := by
    intro hash pre post sr habsorb
    obtain ⟨_, hroots, _, _, hpre, hpost, hnonce⟩ := habsorb
    exact ⟨semKernel_decodes _ hash pre post, hroots,
      semKernel_rowCanon SEL_CELLUNSEAL hash pre post (cellUnseal_noop hash pre post) hpre hpost hnonce⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_CELLUNSEAL hash pre post freezeTickGates
      (cellUnseal_sel hash pre post) (cellUnseal_noop hash pre post)
      (freezeTick_active SEL_CELLUNSEAL hash pre post (cellUnseal_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_CELLUNSEAL hash pre post freezeTickGates
      (cellUnseal_sel hash pre post) (cellUnseal_noop hash pre post)
      (freezeTick_active SEL_CELLUNSEAL hash pre post (cellUnseal_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_CELLUNSEAL hash pre post habsorb.2.2.1 habsorb.2.2.2.1
  build_newcommit := by intro hash pre post sr; rfl

/-- **`cellUnseal_commit_iff` — THE LITERAL `⟺` for cellUnseal.** -/
theorem cellUnseal_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (cellUnsealCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (cellUnsealCompleteSpec preRoots).descriptor
        ((cellUnsealCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (cellUnsealCompleteSpec preRoots).descriptor
        ((cellUnsealCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((cellUnsealCompleteSpec preRoots).fullClause pre post sr
        ∧ ((cellUnsealCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((cellUnsealCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (cellUnsealCompleteSpec preRoots) hash pre post sr habsorb

def cellUnsealDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`cellUnseal_canary_clause` — the clause conjunct BITES.** -/
theorem cellUnseal_canary_clause :
    ¬ (cellUnsealCompleteSpec emptySystemRoots).fullClause cellUnsealDemoPre
        { cellUnsealDemoPre with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [cellUnsealDemoPre] at hbal
  norm_num at hbal

end CellUnseal

/-! ## §9 — CELLDESTROY (FRESH spec; ℤ-equality per-cell spec, canon envelope relocated). -/

section CellDestroy
open Dregg2.Circuit.Emit.EffectVmEmitCellDestroy (SEL_CELLDESTROY CellDestroyRowCanon cellDestroyVmDescriptor RowEncodesDestroy CellDestroyCellSpec)
open Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState
  (IsCellDestroyRow cellDestroyVmDescriptorWide cellDestroyWide_constraints_eq cellDestroyGates_give_cellSpec CellDestroyFullClause)

theorem cellDestroy_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_CELLDESTROY hash pre post).loc SEL_CELLDESTROY = 1 := by
  show semKernelLoc SEL_CELLDESTROY hash pre post SEL_CELLDESTROY = 1
  simp only [SEL_CELLDESTROY]; kernel_col_tac

theorem cellDestroy_noop (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_CELLDESTROY hash pre post).loc sel.NOOP = 0 := by
  show semKernelLoc SEL_CELLDESTROY hash pre post sel.NOOP = 0
  simp only [SEL_CELLDESTROY]; kernel_col_tac

def cellDestroySpec' (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := cellDestroyVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsCellDestroyRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesDestroy env pre post ∧ postRoots = preRoots ∧ CellDestroyRowCanon env
  fullClause    := CellDestroyFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, hcanon⟩ := hdec
    exact ⟨cellDestroyGates_give_cellSpec env pre post hrow.2 hcanon henc
            (cellDestroyWide_constraints_eq ▸ hgates), hroots⟩

def cellDestroyCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := cellDestroySpec' preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_CELLDESTROY hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
    ∧ CellCanon pre ∧ CellCanon post ∧ pre.nonce + 1 < 2013265921
  build_isRow := by intro hash pre post sr; exact ⟨cellDestroy_sel hash pre post, cellDestroy_noop hash pre post⟩
  build_decode := by
    intro hash pre post sr habsorb
    obtain ⟨_, hroots, _, _, hpre, hpost, hnonce⟩ := habsorb
    exact ⟨semKernel_decodes _ hash pre post, hroots,
      semKernel_rowCanon SEL_CELLDESTROY hash pre post (cellDestroy_noop hash pre post) hpre hpost hnonce⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_CELLDESTROY hash pre post freezeTickGates
      (cellDestroy_sel hash pre post) (cellDestroy_noop hash pre post)
      (freezeTick_active SEL_CELLDESTROY hash pre post (cellDestroy_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hbLo, hbHi, hnon, hfld, hcap, hres⟩ := hclause.1
    exact (kernelWindowsSel SEL_CELLDESTROY hash pre post freezeTickGates
      (cellDestroy_sel hash pre post) (cellDestroy_noop hash pre post)
      (freezeTick_active SEL_CELLDESTROY hash pre post (cellDestroy_noop hash pre post)
        (by rw [hbLo]) (by rw [hbHi]) (by rw [hnon]) (fun i => by rw [hfld i])
        (by rw [hcap]) (by rw [hres])) freezeTick_allGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_CELLDESTROY hash pre post habsorb.2.2.1 habsorb.2.2.2.1
  build_newcommit := by intro hash pre post sr; rfl

/-- **`cellDestroy_commit_iff` — THE LITERAL `⟺` for cellDestroy.** -/
theorem cellDestroy_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (cellDestroyCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (cellDestroyCompleteSpec preRoots).descriptor
        ((cellDestroyCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (cellDestroyCompleteSpec preRoots).descriptor
        ((cellDestroyCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((cellDestroyCompleteSpec preRoots).fullClause pre post sr
        ∧ ((cellDestroyCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((cellDestroyCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (cellDestroyCompleteSpec preRoots) hash pre post sr habsorb

def cellDestroyDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`cellDestroy_canary_clause` — the clause conjunct BITES.** -/
theorem cellDestroy_canary_clause :
    ¬ (cellDestroyCompleteSpec emptySystemRoots).fullClause cellDestroyDemoPre
        { cellDestroyDemoPre with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [cellDestroyDemoPre] at hbal
  norm_num at hbal

end CellDestroy

/-! ## §10 — MAKESOVEREIGN (EXTEND; the descriptor is the DROP-TO-ZERO gates ONLY — no transition/pin/
selector segment — so the wrap window is vacuous and the active window is the `gZero` satisfaction). -/

section MakeSovereign
open Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign (SEL_MAKESOVEREIGN makeSovereignRowGates gZero)
open Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState
  (IsMakeSovereignRow makeSovereignVmDescriptorWide makeSovRunnableSpec RowEncodesMakeSov ZeroBlockSpec
   MakeSovFullClause)

theorem makeSov_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow SEL_MAKESOVEREIGN hash pre post).loc SEL_MAKESOVEREIGN = 1 := by
  show semKernelLoc SEL_MAKESOVEREIGN hash pre post SEL_MAKESOVEREIGN = 1
  simp only [SEL_MAKESOVEREIGN]; kernel_col_tac

/-- The drop-to-zero row gates hold on the witness (active window), from `ZeroBlockSpec`. -/
theorem makeSov_active (hash : List ℤ → ℤ) (pre post : CellState) (hz : ZeroBlockSpec post) :
    ∀ c ∈ makeSovereignRowGates, c.holdsVm (semKernelRow SEL_MAKESOVEREIGN hash pre post) true false := by
  obtain ⟨hLo, hHi, hN, hF, hCap, hRes⟩ := hz
  intro c hc
  unfold makeSovereignRowGates gZero at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · simp only [holdsVm_gate_false, eSA, EmittedExpr.eval, l_saBalLo]; exact hLo
  · simp only [holdsVm_gate_false, eSA, EmittedExpr.eval, l_saBalHi]; exact hHi
  · simp only [holdsVm_gate_false, eSA, EmittedExpr.eval, l_saNonce]; exact hN
  · simp only [holdsVm_gate_false, eSA, EmittedExpr.eval, l_saCap]; exact hCap
  · simp only [holdsVm_gate_false, eSA, EmittedExpr.eval, l_saRes]; exact hRes
  · have hs := l_saF SEL_MAKESOVEREIGN hash pre post ⟨i, hi⟩
    simp only [Fin.val_mk] at hs
    simp only [holdsVm_gate_false, eSA, EmittedExpr.eval, hs]
    exact hF ⟨i, hi⟩

/-- The drop-to-zero row gates are vacuous on the wrap window (all `.gate`). -/
theorem makeSov_last (hash : List ℤ → ℤ) (pre post : CellState) :
    ∀ c ∈ makeSovereignRowGates, c.holdsVm (semKernelRow SEL_MAKESOVEREIGN hash pre post) true true := by
  intro c hc
  unfold makeSovereignRowGates gZero at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;> exact trivial

/-- **`makeSovCompleteSpec`** — completeness data for makeSovereign. -/
def makeSovCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := makeSovRunnableSpec preRoots
  buildRow := fun hash pre post _sr => semKernelRow SEL_MAKESOVEREIGN hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30) ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
  build_isRow := by intro hash pre post sr; exact makeSov_sel hash pre post
  build_decode := by
    intro hash pre post sr habsorb
    exact ⟨⟨rfl, rfl, rfl, l_saF _ hash pre post, rfl, rfl⟩, habsorb.2.1⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    exact makeSov_active hash pre post hclause.1
  build_last := by
    intro hash pre post sr hclause habsorb
    exact makeSov_last hash pre post
  build_ranges := by
    intro hash pre post sr hclause habsorb
    exact kernel_ranges2 SEL_MAKESOVEREIGN hash pre post habsorb.2.2.1 habsorb.2.2.2
  build_newcommit := by intro hash pre post sr; rfl

/-- **`makeSov_commit_iff` — THE LITERAL `⟺` for makeSovereign.** -/
theorem makeSov_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (makeSovCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (makeSovCompleteSpec preRoots).descriptor
        ((makeSovCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (makeSovCompleteSpec preRoots).descriptor
        ((makeSovCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((makeSovCompleteSpec preRoots).fullClause pre post sr
        ∧ ((makeSovCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((makeSovCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (makeSovCompleteSpec preRoots) hash pre post sr habsorb

def makeSovDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`makeSov_canary_clause` — the clause conjunct BITES.** A post whose `bal_lo` is NOT dropped to
zero (`999`) fails the full clause (`ZeroBlockSpec`). -/
theorem makeSov_canary_clause :
    ¬ (makeSovCompleteSpec emptySystemRoots).fullClause makeSovDemoPre
        { makeSovDemoPre with balLo := 999 } emptySystemRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [makeSovDemoPre, Int.ModEq] at hbal
  norm_num at hbal

end MakeSovereign

/-! ## §11 — NOOP (EXTEND; the FAITHFUL runnable no-op — 14 whole-block freeze gates INCLUDING the
`state_commit` column, NO selector gate; the row's `sel.NOOP = 1` IS the pad selector). -/

section Noop
open Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
  (gFreeze emitRowGates EmitRowIntent emitEventVm_faithful CellFreezeSpec)
open Dregg2.Circuit.Emit.EffectVmEmitNoopWide (IsNoopRow noopVmDescriptorWide noopRunnableSpec NoopFullClause)

theorem noop_sel (hash : List ℤ → ℤ) (pre post : CellState) :
    (semKernelRow 0 hash pre post).loc sel.NOOP = 1 := by
  show semKernelLoc 0 hash pre post sel.NOOP = 1
  kernel_col_tac

/-- The emit freeze gates are all `.gate`. -/
theorem noop_emitAllGate : ∀ c ∈ emitRowGates, ∃ b, c = VmConstraint.gate b := by
  intro c hc
  simp only [emitRowGates, List.mem_map, List.mem_range] at hc
  obtain ⟨off, hoff, rfl⟩ := hc
  exact ⟨gFreeze off, rfl⟩

/-- The 14 whole-block freeze gates hold on the witness (active window), from `CellFreezeSpec` (offsets
0..11,13) + the honest frozen-commit fact `hcm` (offset 12 = `state_commit`). -/
theorem noop_freeze_active (hash : List ℤ → ℤ) (pre post : CellState)
    (hfz : CellFreezeSpec pre post) (hcm : post.commit ≡ pre.commit [ZMOD 2013265921]) :
    ∀ c ∈ emitRowGates, c.holdsVm (semKernelRow 0 hash pre post) true false := by
  obtain ⟨hLo, hHi, hN, hF, hCap, hRes⟩ := hfz
  have hintent : EmitRowIntent (semKernelRow 0 hash pre post) := by
    intro off hoff
    simp only [STATE_SIZE] at hoff
    interval_cases off
    · exact hLo
    · exact hHi
    · exact hN
    · exact hF 0
    · exact hF 1
    · exact hF 2
    · exact hF 3
    · exact hF 4
    · exact hF 5
    · exact hF 6
    · exact hF 7
    · exact hCap
    · exact hcm
    · exact hRes
  have hff := (emitEventVm_faithful (semKernelRow 0 hash pre post)).mpr hintent
  intro c hc
  obtain ⟨b, rfl⟩ := noop_emitAllGate c hc
  exact hff (VmConstraint.gate b) hc

/-- **`noopCompleteSpec`** — completeness data for the runnable no-op. -/
def noopCompleteSpec (preRoots : SysRoots) : RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := noopRunnableSpec preRoots
  buildRow := fun hash pre post _sr => semKernelRow 0 hash pre post
  absorbsTo := fun hash pre post sr =>
    post.commit = kernelWireCommit hash post ∧ sr = preRoots
    ∧ post.commit ≡ pre.commit [ZMOD 2013265921]
  build_isRow := by intro hash pre post sr; exact noop_sel hash pre post
  build_decode := by intro hash pre post sr habsorb; exact ⟨semKernel_decodes _ hash pre post, habsorb.2.1⟩
  build_carrier := by intro hash pre post sr habsorb; exact semKernel_carrier _ hash pre post habsorb.1
  build_active := by
    intro hash pre post sr hclause habsorb
    exact (kernelWindowsNoSel 0 hash pre post emitRowGates
      (noop_freeze_active hash pre post hclause.1 habsorb.2.2) noop_emitAllGate).1
  build_last := by
    intro hash pre post sr hclause habsorb
    exact (kernelWindowsNoSel 0 hash pre post emitRowGates
      (noop_freeze_active hash pre post hclause.1 habsorb.2.2) noop_emitAllGate).2
  build_ranges := by
    intro hash pre post sr hclause habsorb r hr
    cases hr
  build_newcommit := by intro hash pre post sr; rfl

/-- **`noop_commit_iff` — THE LITERAL `⟺` for the runnable no-op.** The constructed pad row satisfies
the WIDE no-op descriptor on BOTH windows IFF the transition is the genuine full clause
(`CellFreezeSpec` — the whole block frozen — ∧ roots frozen) AND the published `NEW_COMMIT` is the
genuine wire commit. -/
theorem noop_commit_iff (hash : List ℤ → ℤ) (preRoots : SysRoots) (pre post : CellState) (sr : SysRoots)
    (habsorb : (noopCompleteSpec preRoots).absorbsTo hash pre post sr) :
    (satisfiedVm hash (noopCompleteSpec preRoots).descriptor
        ((noopCompleteSpec preRoots).buildRow hash pre post sr) true false
      ∧ satisfiedVm hash (noopCompleteSpec preRoots).descriptor
        ((noopCompleteSpec preRoots).buildRow hash pre post sr) true true)
    ↔ ((noopCompleteSpec preRoots).fullClause pre post sr
        ∧ ((noopCompleteSpec preRoots).buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash ((noopCompleteSpec preRoots).buildRow hash pre post sr)) :=
  runnable_full_commit_iff (noopCompleteSpec preRoots) hash pre post sr habsorb

def noopDemoPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`noop_canary_clause` — the clause conjunct BITES.** A post whose nonce is NOT frozen (`6 ≠ 5`)
fails the full clause — the no-op must NOT tick the nonce. -/
theorem noop_canary_clause :
    ¬ (noopCompleteSpec emptySystemRoots).fullClause noopDemoPre
        { noopDemoPre with nonce := 6 } emptySystemRoots := by
  rintro ⟨⟨_, _, hn, _, _, _⟩, _⟩
  simp only [noopDemoPre, Int.ModEq] at hn
  norm_num at hn

end Noop

/-! ## §12 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}) on the eight `⟺`s. -/

#assert_axioms incNonce_commit_iff
#assert_axioms setVK_commit_iff
#assert_axioms setPerms_commit_iff
#assert_axioms cellSeal_commit_iff
#assert_axioms cellUnseal_commit_iff
#assert_axioms cellDestroy_commit_iff
#assert_axioms makeSov_commit_iff
#assert_axioms noop_commit_iff

#assert_axioms incNonce_commit_iff_demo
#assert_axioms incNonce_canary_clause
#assert_axioms setVK_canary_clause
#assert_axioms setPerms_canary_clause
#assert_axioms cellSeal_canary_clause
#assert_axioms cellUnseal_canary_clause
#assert_axioms cellDestroy_canary_clause
#assert_axioms makeSov_canary_clause
#assert_axioms noop_canary_clause

end Dregg2.Circuit.Emit.EffectVmFullStateTagsA
