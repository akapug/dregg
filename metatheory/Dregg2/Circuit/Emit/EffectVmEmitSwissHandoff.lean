/-
# Dregg2.Circuit.Emit.EffectVmEmitSwissHandoff — the CapTP sturdy-ref HANDOFF `swissHandoffA`, EMITTED
  onto the runnable EffectVM **dedicated `sturdyref_root` column** (the STAGE-3 `system_roots` home),
  with the supported per-row faithfulness + anti-ghost commitment tooth + the connector to universe-A
  `swissHandoffA_full_sound`, and a PRECISE, LOUD flag of the IR-blocked guard/list-structure parts +
  the runtime-cutover status.

## AMPLIFICATION (STAGE 3 `system_roots`)

STAGE 3 (`Exec.SystemRoots`, `6aa29e996`) homed the swiss/sturdyref side-table's root at the dedicated
kernel-owned index `systemRoot.STURDYREF` (the reconciliation note records it "was `fields[4]`"). On the
EffectVM that root is MATERIALISED at `state.FIELD_BASE + 4` — the committed `swiss_table_root` mirror
the runtime EnlivenRef AIR writes to (`air.rs:1626`) and the column the GROUP-4 chain already ABSORBS
(`transferHashSites` site1 input #4; `absorbedCols` lists it). The OLD handoff descriptor carried the
digest on the REINTERPRETED `cap_root` (col 11) and FROZE the nonce. THIS file binds the genuine
dedicated `sturdyref_root` and TICKS the nonce (the runtime's global non-NoOp invariant, `air.rs:2631`):

  * **sturdyref-root MOVE** at `state.FIELD_BASE + 4` (was `cap_root`): post `sturdyref_root` IS the
    param swiss-digest (`D (post.swiss)` — the refcount-bumped/cert-bound post-list digest).
  * **nonce TICK** `+1` (was freeze): the runtime's global non-NoOp nonce constraint.
  * **freeze** balance limbs, `cap_root`, `reserved`, fields `{0,1,2,3,5,6,7}` (the residual frame).

The moved dedicated root is bound into `state_commit` with ZERO change to the hash-site chain (it is an
absorbed column), so the anti-ghost tooth carries verbatim over the dedicated root.

## RUNTIME-CUTOVER STATUS — genuinely BLOCKED (honest)

`swissHandoffA` has NO dedicated Rust selector / `Effect` variant in the running EffectVM
(`columns.rs::sel` has `EXPORT_STURDY_REF`/`ENLIVEN_REF`/`DROP_REF`/`VALIDATE_HANDOFF` — `ValidateHandoff`
is a DIFFERENT operation: it does a cert-membership check and moves `cap_root`, NOT the swiss refcount).
So there is NO honest runtime trace for `swissHandoffA` to AGREE with in the cutover harness; it is a
`NAME_ONLY_DESCRIPTOR` (`effect_vm_descriptors.rs:221`). This descriptor is now ROOT-BOUND and ready the
moment a `SwissHandoff` selector lands, but it CANNOT pass the cutover harness today — reported, not
papered.

## The CONNECTOR — `sturdyrefRootProj` to universe-A's `swissHandoffA_full_sound`

`sturdyrefRootProj D k = D k.swiss`. `unify_swissHandoff`: when `HandoffSpec` holds (so `swissHandoffK
s.kernel sw certHash = some k'`, `s'.kernel = k'`), the projected post-`sturdyref_root` `D s'.kernel.swiss
= D k'.swiss`, and `k'.swiss` is the genuine refcount-bumped/cert-bound post-list
(`swissHandoffK_only_swiss`). So the runnable `field[4]` (sturdyref_root) transition IS universe-A's
`swiss`-digest transition.

## ===================  IR-BLOCKED — the precise asks  ===================

  * **IR GAP 1 — the 2-way guard `HandoffGuard` (AUTHORITY ∧ MEMBERSHIP).** Set-membership / c-list
    predicates over `s.kernel.caps` and `findSwiss s.kernel.swiss sw` (the MEMBERSHIP conjunct is a
    swiss-table lookup). The EffectVM row has no cap-graph / swiss-list columns and no `findSwiss` gate.
    Enforced only inside `swissHandoffA_full_sound` (carried).

  * **IR GAP 2 — the LIST STRUCTURE (which entry bumped, `replaceSwiss … sw …`).** The `sturdyref_root`
    column carries only the scalar digest; `VmHashSite` absorbs trace COLUMNS only, with NO site
    re-deriving the root from a per-row serialization of `List SwissRecord`. So the descriptor pins
    `new_sturdyref_root = D(post.swiss)` (witness-supplied) and binds THAT into `state_commit`, but does
    NOT prove in-circuit that the root IS the genuine list digest. Lives in `listLeafInjective LE` +
    `compressNInjective cN`. ASK: a swiss-list-absorbing `VmHashSite`.

  * PER-CELL / PER-ROW; `state.RESERVED` absorbed nowhere (inherited keystone finding).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR
hash`; the swiss-list digest ONLY as the abstract `D`. No `sorry`/`:= True`/`native_decide`/`rfl`-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.swissHandoffA

namespace Dregg2.Circuit.Emit.EffectVmEmitSwissHandoff

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce site0 site1 transitionAll boundaryFirstPins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SwissFrame (swissHandoffK_only_swiss)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets + the dedicated `sturdyref_root` column.

`swissHandoffA` has NO running-prover selector yet (NAME-ONLY; header). We carry a stable local
selector index `selSH.SWISS_HANDOFF` distinct from the live `EXPORT/ENLIVEN/DROP/VALIDATE_HANDOFF`
selectors. The dedicated `sturdyref_root` is `sturdyrefRootOff = state.FIELD_BASE + 4` (the STAGE-3
`systemRoot.STURDYREF` materialisation column). -/

namespace selSH
/-- The `swissHandoffA` effect selector column (NAME-ONLY; not a live runtime selector — header). -/
def SWISS_HANDOFF : Nat := 4
end selSH

namespace paramSH
/-- The post swiss-table digest parameter (witness fills `D (post.swiss)` — the new `sturdyref_root`). -/
def SWISS_DIGEST_NEW : Nat := 2
end paramSH

/-- The dedicated `sturdyref_root` materialisation state-offset: `state.FIELD_BASE + 4` (the STAGE-3
`systemRoot.STURDYREF` home — "was `fields[4]`"). One of the GROUP-4-absorbed columns. -/
def sturdyrefRootOff : Nat := state.FIELD_BASE + 4

/-- The `swissHandoffA` selector as an expression. -/
def eSelSwissHandoff : EmittedExpr := .var selSH.SWISS_HANDOFF

/-- The post swiss-digest param as an expression. -/
def eSwissDigestNew : EmittedExpr := .var (prmCol paramSH.SWISS_DIGEST_NEW)

/-! ## §1 — The swiss-handoff row gates (sturdyref-root MOVE + nonce TICK + residual freeze). -/

/-- Sturdyref-root MOVE body: `new_sturdyref_root - swissDigestNew` (post `field[4]` IS the param
digest). -/
def gSwissMove : EmittedExpr := eSub (eSA sturdyrefRootOff) eSwissDigestNew

/-- Nonce TICK body (the running prover's GLOBAL non-NoOp invariant): `new_nonce − old_nonce − (1 −
s_noop)`. Reused verbatim from the transfer template (`gNonce`). -/
def gNonceTick : EmittedExpr := gNonce

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Cap-root freeze body (handoff does NOT touch `caps`). -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- The residual frozen fields `{0,1,2,3,5,6,7}` (`field[4]` MOVES — the sturdyref root). -/
def frozenFields : List Nat := [0, 1, 2, 3, 5, 6, 7]

/-- Field-`i` freeze body. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The seven residual field-freeze gates. -/
def gFieldFixAll : List VmConstraint :=
  frozenFields.map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `swissHandoffA` AIR identity. -/
def swissHandoffVmAirName : String := "dregg-effectvm-swissHandoffA-v1"

/-- The swiss-handoff per-row gates: sturdyref-root MOVE, nonce TICK, balance/cap/reserved freeze, the
seven residual fields freeze. -/
def swissHandoffRowGates : List VmConstraint :=
  [ .gate gSwissMove, .gate gNonceTick, .gate gBalLoFix, .gate gBalHiFix
  , .gate gCapFix, .gate gResFix ] ++ gFieldFixAll

/-- Site 2 absorbing the post `cap_root` (unchanged from the transfer keystone — the dedicated
`sturdyref_root` at `field[4]` is absorbed by site1). -/
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

/-- The ordered GROUP-4 hash sites (identical chain to the transfer keystone — `field[4]` carrying the
dedicated `sturdyref_root` is absorbed by site1). -/
def swissHandoffHashSites : List VmHashSite := [site0, site1, site2, site3]

/-- **`swissHandoffVmDescriptor`** — the `swissHandoffA` concrete circuit: sturdyref-root MOVE
(`field[4]`) + nonce TICK + residual frame freeze ++ transition continuity ++ row-0 boundary pins, with
the 4 GROUP-4 hash sites binding the moved dedicated root. Guard + list-structure IR-BLOCKED (header). -/
def swissHandoffVmDescriptor : EffectVmDescriptor :=
  { name := swissHandoffVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := swissHandoffRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := swissHandoffHashSites
  , ranges := [] }

/-! ## §3 — The swiss-handoff ROW INTENT. -/

/-- **`SwissHandoffRowIntent env`** — post `sturdyref_root` (`field[4]`) is the digest param, nonce
ticks `+1`, balance/cap/reserved + residual fields `{0,1,2,3,5,6,7}` frozen. -/
def SwissHandoffRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol sturdyrefRootOff) = env.loc (prmCol paramSH.SWISS_DIGEST_NEW)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i ∈ frozenFields, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a swiss-handoff row: `s_swissHandoff = 1`, `s_noop = 0`. -/
def IsSwissHandoffRow (env : VmRowEnv) : Prop :=
  env.loc selSH.SWISS_HANDOFF = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

/-- **`swissHandoffRowGates_holds_iff`** — on a swiss-handoff row (`s_noop = 0`), the gates all hold IFF
`SwissHandoffRowIntent` holds. -/
theorem swissHandoffRowGates_holds_iff (env : VmRowEnv) (hrow : IsSwissHandoffRow env) :
    (∀ c ∈ swissHandoffRowGates, c.holdsVm env false false) ↔ SwissHandoffRowIntent env := by
  obtain ⟨_hsH, hsN⟩ := hrow
  unfold swissHandoffRowGates gFieldFixAll frozenFields SwissHandoffRowIntent
  constructor
  · intro h
    have hSw := h (.gate gSwissMove) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i ∈ frozenFields → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gSwissMove, gNonceTick, gNonce, gBalLoFix, gBalHiFix, gCapFix,
      gResFix, eSA, eSB, eSwissDigestNew, eSub, eSelNoop, EmittedExpr.eval]
      at hSw hNon hLo hHi hCap hRes
    rw [hsN] at hNon
    refine ⟨by linarith [hSw], by linarith [hNon], by linarith [hLo], by linarith [hHi],
      by linarith [hCap], by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hSw, hNon, hLo, hHi, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
      rw [hSw]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      have hmem : i ∈ frozenFields := by
        simp only [frozenFields, List.mem_cons, List.mem_singleton]; tauto
      rw [hFld i hmem]; ring

/-- **`swissHandoffVm_faithful` — THE deliverable.** -/
theorem swissHandoffVm_faithful (env : VmRowEnv) (hrow : IsSwissHandoffRow env) :
    (∀ c ∈ swissHandoffRowGates, c.holdsVm env false false) ↔ SwissHandoffRowIntent env :=
  swissHandoffRowGates_holds_iff env hrow

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (sturdyref-root tamper).** -/
theorem swissHandoffVm_rejects_wrong_swissRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol sturdyrefRootOff) ≠ env.loc (prmCol paramSH.SWISS_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gSwissMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** -/
theorem swissHandoffVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsSwissHandoffRow env)
    (hwrong : ¬ SwissHandoffRowIntent env) :
    ¬ (∀ c ∈ swissHandoffRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((swissHandoffVm_faithful env hrow).mp h)

/-! ## §6 — The structured per-cell soundness. -/

/-- **`SwissRowEncodes env pre post swissDigestNew`** — the row decodes to `(pre, post)` cell states.
The `sturdyref_root` is carried on the `field[4]` column. -/
def SwissRowEncodes (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramSH.SWISS_DIGEST_NEW) = swissDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell handoff spec: post `field[4]` (sturdyref_root) = the new digest, nonce ticks,
balance/cap/reserved + residual fields `{0,1,2,3,5,6,7}` frozen. -/
def SwissCellSpec (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  post.fields ⟨4, by decide⟩ = swissDigestNew
  ∧ post.nonce = pre.nonce + 1
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved
  ∧ post.fields ⟨0, by decide⟩ = pre.fields ⟨0, by decide⟩
  ∧ post.fields ⟨1, by decide⟩ = pre.fields ⟨1, by decide⟩
  ∧ post.fields ⟨2, by decide⟩ = pre.fields ⟨2, by decide⟩
  ∧ post.fields ⟨3, by decide⟩ = pre.fields ⟨3, by decide⟩
  ∧ post.fields ⟨5, by decide⟩ = pre.fields ⟨5, by decide⟩
  ∧ post.fields ⟨6, by decide⟩ = pre.fields ⟨6, by decide⟩
  ∧ post.fields ⟨7, by decide⟩ = pre.fields ⟨7, by decide⟩

/-- Under `SwissRowEncodes`, `SwissHandoffRowIntent` IS the structured per-cell `SwissCellSpec`. -/
theorem intent_to_swissCellSpec (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew) (hint : SwissHandoffRowIntent env) :
    SwissCellSpec pre post swissDigestNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hsw, hnon, hlo, hhi, hcap, hres, hfld⟩ := hint
  have frozen : ∀ i : Fin 8, i.val ∈ frozenFields → post.fields i = pre.fields i := by
    intro i hi
    have hp := hsaF i; have hq := hsbF i
    have := hfld i.val hi
    rw [hp, hq] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp4 : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    rw [← hp4]; show env.loc (saCol sturdyrefRootOff) = swissDigestNew
    rw [hsw, hpDig]
  · rw [← hsaN, ← hsbN]; exact hnon
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres
  · exact frozen ⟨0, by decide⟩ (by decide)
  · exact frozen ⟨1, by decide⟩ (by decide)
  · exact frozen ⟨2, by decide⟩ (by decide)
  · exact frozen ⟨3, by decide⟩ (by decide)
  · exact frozen ⟨5, by decide⟩ (by decide)
  · exact frozen ⟨6, by decide⟩ (by decide)
  · exact frozen ⟨7, by decide⟩ (by decide)

/-- **`swissHandoffDescriptor_full_sound` — the structured soundness.** -/
theorem swissHandoffDescriptor_full_sound (env : VmRowEnv) (hrow : IsSwissHandoffRow env)
    (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew)
    (hgates : ∀ c ∈ swissHandoffRowGates, c.holdsVm env false false) :
    SwissCellSpec pre post swissDigestNew :=
  intent_to_swissCellSpec env pre post swissDigestNew henc ((swissHandoffVm_faithful env hrow).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, dedicated sturdyref_root included). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `swissHandoffHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem swissHandoffHashSites_eq : swissHandoffHashSites = transferHashSites := rfl

/-- **`swissHandoffDescriptor_commit_binds_state` — the whole-state tooth.** -/
theorem swissHandoffDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ swissHandoffHashSites)
    (hs₂ : siteHoldsAll hash e₂ swissHandoffHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [swissHandoffHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-- **`swissHandoffDescriptor_binds_sturdyref_root` — the per-column anti-ghost.** Equal published
`state_commit`s force the moved dedicated `sturdyref_root` (`field[4]`, absorbed column #7) equal. -/
theorem swissHandoffDescriptor_binds_sturdyref_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ swissHandoffHashSites)
    (hs₂ : siteHoldsAll hash e₂ swissHandoffHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (saCol sturdyrefRootOff) = e₂.loc (saCol sturdyrefRootOff) := by
  have h := swissHandoffDescriptor_commit_binds_state hash hCR e₁ e₂ hs₁ hs₂ hcommit
  have := congrArg (fun l => l.getD 7 0) h
  simpa only [absorbedCols, List.getD_cons_succ, List.getD_cons_zero, sturdyrefRootOff] using this

/-! ## §8 — THE CONNECTOR — `sturdyrefRootProj` to universe-A's `swissHandoffA_full_sound`. -/

open Dregg2.Circuit.Inst.SwissHandoffA (HandoffArgs)
open Dregg2.Circuit.Spec.SwissHandoff (HandoffSpec)

/-- **`sturdyrefRootProj D k`** — the EffectVM dedicated `sturdyref_root` column value: the whole-list
digest `D`. -/
def sturdyrefRootProj (D : List SwissRecord → ℤ) (k : RecordKernelState) : ℤ := D k.swiss

/-- **`unify_swissHandoff` — THE CONNECTOR.** When universe-A's `HandoffSpec` holds (so `swissHandoffK
s.kernel sw certHash = some k'`, `s'.kernel = k'`), the projected post-`sturdyref_root` `D s'.kernel.swiss
= D k'.swiss` — and `k'.swiss` is the genuine refcount-bumped/cert-bound post-list. -/
theorem unify_swissHandoff (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) (k' : RecordKernelState)
    (hk : swissHandoffK s.kernel args.sw args.certHash = some k')
    (hs' : s' = { kernel := k', log := s'.log }) :
    sturdyrefRootProj D s'.kernel = D k'.swiss := by
  show D s'.kernel.swiss = D k'.swiss
  rw [hs']

/-- **`unify_swissHandoff_via_full_sound` — the runnable dedicated-root move inherits the VALIDATED
guarantee.** A satisfying universe-A `swissHandoffA_full_sound` witness ⟹ `HandoffSpec` ⟹ the projected
post-`sturdyref_root` equals `D` of the genuine refcount-bumped/cert-bound post-list `k'.swiss`. -/
theorem unify_swissHandoff_via_full_sound
    (S : Surface2) (D : List SwissRecord → ℤ)
    (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissHandoffA.RestIffNoSwiss S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Dregg2.Circuit.Inst.SwissHandoffA.swissHandoffE LE cN hN hLE)
        (encodeE2 S (Dregg2.Circuit.Inst.SwissHandoffA.swissHandoffE LE cN hN hLE) s args s')) :
    ∃ k', swissHandoffK s.kernel args.sw args.certHash = some k'
      ∧ sturdyrefRootProj D s'.kernel = D k'.swiss
      ∧ k' = { s.kernel with swiss := k'.swiss } := by
  have hspec : HandoffSpec s args.sw args.certHash args.introducer args.exporter s' :=
    Dregg2.Circuit.Inst.SwissHandoffA.swissHandoffA_full_sound S LE cN hN hLE hRest hLog s args s' h
  obtain ⟨_hg, k', hk, hs'⟩ := hspec
  refine ⟨k', hk, ?_, swissHandoffK_only_swiss hk⟩
  exact unify_swissHandoff D s args s' k' hk (by rw [hs'])

/-! ## §9 — NON-VACUITY: a concrete row that satisfies the intent, and one that does not. The good row
moves `field[4]@83` (sturdyref_root) `0 → 77`, ticks nonce@78 `9 → 10`, freezes the rest. -/

/-- A concrete swiss-handoff row, on RESOLVED ABSOLUTE columns. Selector `SWISS_HANDOFF@4 = 1`,
`nonce@56 = 9`, `nonce@78 = 10`, `field[4]@83 = 77`, digest@70 = 77; everything else `0`/frozen. -/
def swissGoodRow : VmRowEnv where
  loc := fun v =>
    if v = 4 then 1           -- SWISS_HANDOFF selector
    else if v = 56 then 9     -- sbCol NONCE
    else if v = 78 then 10    -- saCol NONCE
    else if v = 83 then 77    -- saCol sturdyrefRootOff (field[4])
    else if v = 70 then 77    -- prmCol SWISS_DIGEST_NEW
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The resolved absolute indices. -/
theorem col_facts :
    saCol sturdyrefRootOff = 83 ∧ prmCol paramSH.SWISS_DIGEST_NEW = 70
    ∧ sbCol state.NONCE = 56 ∧ saCol state.NONCE = 78 ∧ selSH.SWISS_HANDOFF = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- For any field index `i`, the absolute pre/post field columns are `57+i` / `79+i`. -/
theorem field_col_facts (i : Nat) :
    saCol (state.FIELD_BASE + i) = 79 + i ∧ sbCol (state.FIELD_BASE + i) = 57 + i := by
  constructor
  · simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE]; omega
  · simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.FIELD_BASE]; omega

/-- `swissGoodRow` is a genuine swiss-handoff row. -/
theorem swissGoodRow_isSwissHandoffRow : IsSwissHandoffRow swissGoodRow := by
  obtain ⟨_, _, _, _, hsel⟩ := col_facts
  refine ⟨?_, ?_⟩
  · show swissGoodRow.loc selSH.SWISS_HANDOFF = 1; rw [hsel]; rfl
  · show swissGoodRow.loc sel.NOOP = 0; rfl

/-- **NON-VACUITY (witness TRUE).** `swissGoodRow` REALIZES the swiss-handoff intent. -/
theorem swissGoodRow_realizes_intent : SwissHandoffRowIntent swissGoodRow := by
  obtain ⟨hsa, hprm, hsbN, hsaN, _hsel⟩ := col_facts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsa, hprm]; rfl
  · rw [hsaN, hsbN]; rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    obtain ⟨hfa, hfb⟩ := field_col_facts i
    rw [hfa, hfb]
    simp only [frozenFields, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    have lhs0 : swissGoodRow.loc (79 + i) = 0 := by
      show (if (79 + i) = 4 then (1:ℤ) else if (79+i) = 56 then 9 else if (79+i) = 78 then 10
        else if (79+i) = 83 then 77 else if (79+i) = 70 then 77 else 0) = 0
      rcases hi with h|h|h|h|h|h|h <;> subst h <;> rfl
    have rhs0 : swissGoodRow.loc (57 + i) = 0 := by
      show (if (57 + i) = 4 then (1:ℤ) else if (57+i) = 56 then 9 else if (57+i) = 78 then 10
        else if (57+i) = 83 then 77 else if (57+i) = 70 then 77 else 0) = 0
      rcases hi with h|h|h|h|h|h|h <;> subst h <;> rfl
    rw [lhs0, rhs0]

/-- A forged swiss-handoff row: post-`sturdyref_root` (`field[4]`@83) tampered to `999 ≠ 77`. -/
def swissBadRow : VmRowEnv where
  loc := fun v => if v = 83 then 999 else swissGoodRow.loc v
  nxt := swissGoodRow.nxt
  pub := swissGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** -/
theorem swissBadRow_rejected : ¬ (VmConstraint.gate gSwissMove).holdsVm swissBadRow false false := by
  apply swissHandoffVm_rejects_wrong_swissRoot
  obtain ⟨hsa, hprm, _, _, _⟩ := col_facts
  have rRoot : swissBadRow.loc (saCol sturdyrefRootOff) = 999 := by
    rw [hsa]; show (if (83:Nat) = 83 then (999:ℤ) else swissGoodRow.loc 83) = 999; rfl
  have rPrm : swissBadRow.loc (prmCol paramSH.SWISS_DIGEST_NEW) = 77 := by
    rw [hprm]; show (if (70:Nat) = 83 then (999:ℤ) else swissGoodRow.loc 70) = 77; rfl
  rw [rRoot, rPrm]; decide

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard swissHandoffVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates (move/tick + 5 freeze + 7 fields)
#guard swissHandoffVmDescriptor.hashSites.length == 4
#guard swissHandoffVmDescriptor.traceWidth == 186
#guard swissHandoffRowGates.length == 13

#assert_axioms swissHandoffRowGates_holds_iff
#assert_axioms swissHandoffVm_faithful
#assert_axioms swissHandoffVm_rejects_wrong_swissRoot
#assert_axioms swissHandoffVm_rejects_wrong_output
#assert_axioms intent_to_swissCellSpec
#assert_axioms swissHandoffDescriptor_full_sound
#assert_axioms swissHandoffDescriptor_commit_binds_state
#assert_axioms swissHandoffDescriptor_binds_sturdyref_root
#assert_axioms unify_swissHandoff
#assert_axioms unify_swissHandoff_via_full_sound
#assert_axioms swissGoodRow_realizes_intent
#assert_axioms swissBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSwissHandoff
