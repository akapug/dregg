/-
# Dregg2.Circuit.Emit.EffectVmEmitSwissDrop — the CapTP sturdy-ref DROP/GC `swissDropA`, EMITTED onto
  the runnable EffectVM `swiss_root` (digest) column, with the supported per-row faithfulness +
  anti-ghost commitment tooth + the connector to universe-A `swissDropA_full_sound`, and a PRECISE,
  LOUD flag of the IR-blocked guard/list-structure parts.

## The supported part vs where the per-row IR STOPS

`swissDropA sw actor exporter` DECREMENTS the swiss entry `sw`'s `refcount`, GC-ing the entry when it
hits 0 (`swissDropK`: `removeSwiss` at zero / `replaceSwiss` with `refcount-1` otherwise), prepends an
authority receipt, freezes the 16 non-`swiss` kernel fields. Touched component = the `List SwissRecord`
side-table `swiss` (FULL-list digest), GATED on a 3-way guard `DropGuard` (AUTHORITY ∧ MEMBERSHIP ∧
LIVE-REF). Validation `swissDropA_full_sound ⇒ DropSpec` is DONE (`Inst/swissDropA.lean`).

The EffectVM row has only a scalar 14-column block (one `cap_root` column absorbed into the GROUP-4
commitment) — NO swiss-list/lookup/guard columns. So the SUPPORTED row-expressible part is the SCALAR
DIGEST-COLUMN MOVE: post `swiss_root` = digest of the post (decremented/GC'd) swiss-list, every other
column frozen, the moved digest bound into `state_commit` under Poseidon2 CR. We emit that via the
`cap_root`-move template (cap_root REINTERPRETED as the swiss digest for this `caps`-freezing effect).
`swissDropVmDescriptor` pins post `swiss_root` to `paramSD.SWISS_DIGEST_NEW`.

## The CONNECTOR — `swissRootProj` to universe-A's `swissDropA_full_sound`

`swissRootProj D k = D k.swiss`. `unify_swissDrop`: when `DropSpec` holds (so `swissDropK s.kernel sw =
some k'`, `s'.kernel = k'`), the projected post-`swiss_root` `D s'.kernel.swiss = D k'.swiss`, and
`k'.swiss` is the genuine decremented/GC'd post-list (`swissDropK_only_swiss`). So the runnable
`swiss_root` transition IS universe-A's `swiss`-digest transition; not a fourth spec.

## ===================  IR-BLOCKED — the precise asks  ===================

  * **IR GAP 1 — the 3-way guard `DropGuard` (AUTHORITY ∧ MEMBERSHIP ∧ LIVE-REF).** Set-membership /
    c-list / refcount predicates over `s.kernel.caps`, `findSwiss s.kernel.swiss sw`, and the entry's
    `refcount`. No EffectVM cap-graph/swiss-list/refcount columns; no `findSwiss` gate. Universe-A
    commits it as one `propBit`; the per-row IR has no guard column and cannot re-derive the
    lookup/refcount. ASK: a guard-bit `VmConstraint` internalizes the PRESENCE; the membership/refcount
    content needs a lookup argument the IR lacks. Enforced only inside `swissDropA_full_sound`.

  * **IR GAP 2 — the LIST STRUCTURE (decrement vs GC-remove of which entry).** `swiss_root` carries the
    scalar digest only; `VmHashSite` absorbs trace COLUMNS, with NO site re-deriving `swiss_root` from a
    per-row serialization of `List SwissRecord`. So the descriptor pins `new_swiss_root = D(post.swiss)`
    (witness-supplied) and binds THAT into `state_commit`, but does NOT prove in-circuit that
    `swiss_root` IS the genuine list digest, nor whether entry `sw` was decremented or GC-removed. Lives
    in `listLeafInjective LE` + `compressNInjective cN`. ASK: a swiss-list-absorbing `VmHashSite`.

  * PER-CELL / PER-ROW; `state.RESERVED` absorbed nowhere (inherited keystone finding).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR
hash`; the swiss-list digest ONLY as the abstract `D`. No `sorry`/`:= True`/`native_decide`/`rfl`-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.swissDropA

namespace Dregg2.Circuit.Emit.EffectVmEmitSwissDrop

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop site0 site1 transitionAll boundaryFirstPins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SwissFrame (swissDropK_only_swiss)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets. -/

namespace selSD
/-- The `swissDropA` effect selector column. -/
def SWISS_DROP : Nat := 5
end selSD

namespace paramSD
/-- The post swiss-table digest parameter (witness fills `D (post.swiss)`). -/
def SWISS_DIGEST_NEW : Nat := 2
end paramSD

/-- The `swissDropA` selector as an expression. -/
def eSelSwissDrop : EmittedExpr := .var selSD.SWISS_DROP

/-- The post swiss-digest param as an expression. -/
def eSwissDigestNew : EmittedExpr := .var (prmCol paramSD.SWISS_DIGEST_NEW)

/-! ## §1 — The swiss-drop row gates (the SUPPORTED part: a digest-column MOVE + frame freeze). -/

/-- Swiss-root MOVE body: `new_swiss_root - swissDigestNew`. -/
def gSwissMove : EmittedExpr := eSub (eSA state.CAP_ROOT) eSwissDigestNew
/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body. -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
/-- Field-`i` freeze body. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `swissDropA` AIR identity. -/
def swissDropVmAirName : String := "dregg-effectvm-swissDropA-v1"

/-- The swiss-drop per-row gates: swiss-root MOVE, balance/nonce/reserved freeze, 8 fields freeze. -/
def swissDropRowGates : List VmConstraint :=
  [ .gate gSwissMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gResFix ] ++ gFieldFixAll

/-- Site 2 absorbing the post `swiss_root` (cap-root column). -/
def site2 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER3
  , inputs := [ .col (saCol (state.FIELD_BASE + 5)), .col (saCol (state.FIELD_BASE + 6))
              , .col (saCol (state.FIELD_BASE + 7)), .col (saCol state.CAP_ROOT) ]
  , arity := 4 }

/-- Site 3: `state_commit = H4(inter1, inter2, inter3, 0)`. -/
def site3 : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .zero ]
  , arity := 4 }

/-- The ordered GROUP-4 hash sites (identical chain to the transfer keystone). -/
def swissDropHashSites : List VmHashSite := [site0, site1, site2, site3]

/-- **`swissDropVmDescriptor`** — the `swissDropA` SUPPORTED concrete circuit. Guard + list-structure
are IR-BLOCKED (header), NOT in this descriptor. -/
def swissDropVmDescriptor : EffectVmDescriptor :=
  { name := swissDropVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := swissDropRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := swissDropHashSites
  , ranges := [] }

/-! ## §3 — The swiss-drop ROW INTENT. -/

/-- **`SwissDropRowIntent env`** — post `swiss_root` is the digest param, frame frozen. -/
def SwissDropRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (prmCol paramSD.SWISS_DIGEST_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a swiss-drop row: `s_swissDrop = 1`, `s_noop = 0`. -/
def IsSwissDropRow (env : VmRowEnv) : Prop :=
  env.loc selSD.SWISS_DROP = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

/-- **`swissDropRowGates_holds_iff`** — on a swiss-drop row, the gates all hold IFF
`SwissDropRowIntent` holds. -/
theorem swissDropRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ swissDropRowGates, c.holdsVm env false false) ↔ SwissDropRowIntent env := by
  unfold swissDropRowGates gFieldFixAll SwissDropRowIntent
  constructor
  · intro h
    have hSw := h (.gate gSwissMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gSwissMove, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eSwissDigestNew, eSub, EmittedExpr.eval] at hSw hLo hHi hNon hRes
    refine ⟨by linarith [hSw], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hSw, hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
      rw [hSw]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **`swissDropVm_faithful` — THE supported deliverable.** -/
theorem swissDropVm_faithful (env : VmRowEnv) :
    (∀ c ∈ swissDropRowGates, c.holdsVm env false false) ↔ SwissDropRowIntent env :=
  swissDropRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (swiss-root tamper).** -/
theorem swissDropVm_rejects_wrong_swissRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (prmCol paramSD.SWISS_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gSwissMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** -/
theorem swissDropVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SwissDropRowIntent env) :
    ¬ (∀ c ∈ swissDropRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((swissDropVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness. -/

/-- **`SwissRowEncodes env pre post swissDigestNew`** — the row decodes to `(pre, post)` cell states. -/
def SwissRowEncodes (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramSD.SWISS_DIGEST_NEW) = swissDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell swiss spec: post-`swiss_root` set to the new digest, every other field frozen. -/
def SwissCellSpec (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  post.capRoot = swissDigestNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `SwissRowEncodes`, `SwissDropRowIntent` IS the structured per-cell `SwissCellSpec`. -/
theorem intent_to_swissCellSpec (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew) (hint : SwissDropRowIntent env) :
    SwissCellSpec pre post swissDigestNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hsw, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hpDig]; exact hsw
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`swissDropDescriptor_full_sound` — the structured soundness (supported part).** -/
theorem swissDropDescriptor_full_sound (env : VmRowEnv)
    (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew)
    (hgates : ∀ c ∈ swissDropRowGates, c.holdsVm env false false) :
    SwissCellSpec pre post swissDigestNew :=
  intent_to_swissCellSpec env pre post swissDigestNew henc ((swissDropVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `swissDropHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem swissDropHashSites_eq : swissDropHashSites = transferHashSites := rfl

/-- **`swissDropDescriptor_commit_binds_state` — the whole-state tooth.** -/
theorem swissDropDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ swissDropHashSites)
    (hs₂ : siteHoldsAll hash e₂ swissDropHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [swissDropHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `swissRootProj` to universe-A's `swissDropA_full_sound`. -/

open Dregg2.Circuit.Inst.SwissDropA (DropArgs)
open Dregg2.Circuit.Spec.SwissDrop (DropSpec)

/-- **`swissRootProj D k`** — the EffectVM `swiss_root` column value: the whole-list digest `D`. -/
def swissRootProj (D : List SwissRecord → ℤ) (k : RecordKernelState) : ℤ := D k.swiss

/-- **`unify_swissDrop` — THE CONNECTOR.** When universe-A's `DropSpec` holds (so `swissDropK s.kernel
sw = some k'`, `s'.kernel = k'`), the projected post-`swiss_root` `D s'.kernel.swiss = D k'.swiss` —
and `k'.swiss` is the genuine decremented/GC'd post-list (`swissDropK_only_swiss`). So
`SwissCellSpec`'s `swiss_root` clause IS universe-A's `swiss`-clause, projected to the digest column. -/
theorem unify_swissDrop (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState) (k' : RecordKernelState)
    (hk : swissDropK s.kernel args.sw = some k')
    (hs' : s' = { kernel := k', log := s'.log }) :
    swissRootProj D s'.kernel = D k'.swiss := by
  show D s'.kernel.swiss = D k'.swiss
  rw [hs']

/-- **`unify_swissDrop_via_full_sound` — the runnable column move inherits the VALIDATED guarantee.**
A satisfying universe-A `swissDropA_full_sound` witness ⟹ `DropSpec` ⟹ the projected post-`swiss_root`
equals `D` of the genuine decremented/GC'd post-list `k'.swiss` (the existential post-kernel). So the
runnable `swiss_root` move is universe-A's validated `swiss` transition, not a fourth spec. (Guard +
list-structure stay enforced ONLY inside the full_sound — IR-BLOCKED at the row, header.) -/
theorem unify_swissDrop_via_full_sound
    (S : Surface2) (D : List SwissRecord → ℤ)
    (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissDropA.RestIffNoSwiss S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Dregg2.Circuit.Inst.SwissDropA.swissDropE LE cN hN hLE)
        (encodeE2 S (Dregg2.Circuit.Inst.SwissDropA.swissDropE LE cN hN hLE) s args s')) :
    ∃ k', swissDropK s.kernel args.sw = some k'
      ∧ swissRootProj D s'.kernel = D k'.swiss
      ∧ k' = { s.kernel with swiss := k'.swiss } := by
  have hspec : DropSpec s args.sw args.actor args.exporter s' :=
    Dregg2.Circuit.Inst.SwissDropA.swissDropA_full_sound S LE cN hN hLE hRest hLog s args s' h
  obtain ⟨_hg, k', hk, hs'⟩ := hspec
  refine ⟨k', hk, ?_, swissDropK_only_swiss hk⟩
  exact unify_swissDrop D s args s' k' hk (by rw [hs'])

/-! ## §9 — NON-VACUITY. -/

/-- A concrete swiss-drop row: `swiss_root` moves to the param digest `77`, frame frozen at `0`. -/
def swissGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selSD.SWISS_DROP then 1
    else if v = sbCol state.CAP_ROOT then 11
    else if v = saCol state.CAP_ROOT then 77
    else if v = prmCol paramSD.SWISS_DIGEST_NEW then 77
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `swissGoodRow` is a genuine swiss-drop row. -/
theorem swissGoodRow_isSwissDropRow : IsSwissDropRow swissGoodRow := by
  unfold IsSwissDropRow swissGoodRow
  constructor <;> norm_num [selSD.SWISS_DROP, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT,
    paramSD.SWISS_DIGEST_NEW]

/-- **NON-VACUITY (witness TRUE).** `swissGoodRow` REALIZES the swiss-drop intent. -/
theorem swissGoodRow_realizes_intent : SwissDropRowIntent swissGoodRow := by
  have hsa  : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramSD.SWISS_DIGEST_NEW = 70 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramSD.SWISS_DIGEST_NEW; rfl
  have rsa : swissGoodRow.loc (saCol state.CAP_ROOT) = 77 := by
    rw [hsa]
    show (if (87:Nat) = selSD.SWISS_DROP then (1:ℤ)
      else if (87:Nat) = sbCol state.CAP_ROOT then 11
      else if (87:Nat) = saCol state.CAP_ROOT then 77
      else if (87:Nat) = prmCol paramSD.SWISS_DIGEST_NEW then 77 else 0) = 77
    rw [hsa]; norm_num [selSD.SWISS_DROP, sbCol, prmCol, STATE_BEFORE_BASE, PARAM_BASE,
      NUM_EFFECTS, STATE_SIZE, state.CAP_ROOT, paramSD.SWISS_DIGEST_NEW]
  have rprm : swissGoodRow.loc (prmCol paramSD.SWISS_DIGEST_NEW) = 77 := by
    rw [hprm]
    show (if (70:Nat) = selSD.SWISS_DROP then (1:ℤ)
      else if (70:Nat) = sbCol state.CAP_ROOT then 11
      else if (70:Nat) = saCol state.CAP_ROOT then 77
      else if (70:Nat) = prmCol paramSD.SWISS_DIGEST_NEW then 77 else 0) = 77
    rw [hprm]; norm_num [selSD.SWISS_DROP, sbCol, saCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramSD.SWISS_DIGEST_NEW]
  refine ⟨by rw [rsa, rprm], ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [saCol, sbCol, prmCol, selSD.SWISS_DROP, STATE_AFTER_BASE, STATE_BEFORE_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, state.BALANCE_LO,
      state.BALANCE_HI, state.NONCE, state.RESERVED, state.FIELD_BASE, paramSD.SWISS_DIGEST_NEW,
      swissGoodRow]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro i hi
    have e1 : ¬ (76 + (3 + i) = 5) := by omega
    have e2 : ¬ (76 + (3 + i) = 65) := by omega
    have e3 : ¬ (76 + (3 + i) = 87) := by omega
    have e4 : ¬ (76 + (3 + i) = 70) := by omega
    have f1 : ¬ (54 + (3 + i) = 5) := by omega
    have f2 : ¬ (54 + (3 + i) = 65) := by omega
    have f3 : ¬ (54 + (3 + i) = 87) := by omega
    have f4 : ¬ (54 + (3 + i) = 70) := by omega
    simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg f1, if_neg f2, if_neg f3, if_neg f4]

/-- A forged swiss-drop row: post-`swiss_root` tampered to `999 ≠ 77`. -/
def swissBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else swissGoodRow.loc v
  nxt := swissGoodRow.nxt
  pub := swissGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** -/
theorem swissBadRow_rejected : ¬ (VmConstraint.gate gSwissMove).holdsVm swissBadRow false false := by
  apply swissDropVm_rejects_wrong_swissRoot
  have hsa  : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramSD.SWISS_DIGEST_NEW = 70 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramSD.SWISS_DIGEST_NEW; rfl
  have rsa : swissBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ) else swissGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have rprm : swissBadRow.loc (prmCol paramSD.SWISS_DIGEST_NEW) = 77 := by
    show (if prmCol paramSD.SWISS_DIGEST_NEW = saCol state.CAP_ROOT then (999:ℤ)
      else swissGoodRow.loc (prmCol paramSD.SWISS_DIGEST_NEW)) = 77
    have hne : ¬ (prmCol paramSD.SWISS_DIGEST_NEW = saCol state.CAP_ROOT) := by rw [hsa, hprm]; decide
    rw [if_neg hne, hprm]
    show (if (70:Nat) = selSD.SWISS_DROP then (1:ℤ)
      else if (70:Nat) = sbCol state.CAP_ROOT then 11
      else if (70:Nat) = saCol state.CAP_ROOT then 77
      else if (70:Nat) = prmCol paramSD.SWISS_DIGEST_NEW then 77 else 0) = 77
    rw [hprm]; norm_num [selSD.SWISS_DROP, sbCol, saCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramSD.SWISS_DIGEST_NEW]
  rw [rsa, rprm]; decide

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard swissDropVmDescriptor.constraints.length == 13 + 14 + 4
#guard swissDropVmDescriptor.hashSites.length == 4
#guard swissDropVmDescriptor.traceWidth == 186

#assert_axioms swissDropRowGates_holds_iff
#assert_axioms swissDropVm_faithful
#assert_axioms swissDropVm_rejects_wrong_swissRoot
#assert_axioms swissDropVm_rejects_wrong_output
#assert_axioms intent_to_swissCellSpec
#assert_axioms swissDropDescriptor_full_sound
#assert_axioms swissDropDescriptor_commit_binds_state
#assert_axioms unify_swissDrop
#assert_axioms unify_swissDrop_via_full_sound
#assert_axioms swissGoodRow_realizes_intent
#assert_axioms swissBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSwissDrop
