/-
# Dregg2.Circuit.Emit.EffectVmEmitSwissExport — the CapTP sturdy-ref MINT `swissExportA` (export), EMITTED
  onto the runnable EffectVM **dedicated `sturdyref_root` column** (the STAGE-3 `system_roots` home),
  with the supported per-row faithfulness + anti-ghost commitment tooth + the connector to universe-A
  `swissExportA_full_sound`, and a PRECISE, LOUD flag of the IR-blocked guard/list-structure parts +
  the runtime-cutover status.

## AMPLIFICATION (STAGE 3 `system_roots`)

STAGE 3 (`Exec.SystemRoots`, `6aa29e996`) homed the swiss/sturdyref side-table's root at the dedicated
kernel-owned index `systemRoot.STURDYREF` (the reconciliation note records it "was `fields[4]`"). On the
EffectVM that root is MATERIALISED at `state.FIELD_BASE + 4` — the committed `swiss_table_root` mirror
the runtime EnlivenRef AIR writes to (`air.rs:1626`) and the column the GROUP-4 chain already ABSORBS
(`transferHashSites` site1 input #4; `absorbedCols` lists it). The OLD export descriptor carried the
digest on the REINTERPRETED `cap_root` (col 11) and FROZE the nonce. THIS file binds the genuine
dedicated `sturdyref_root` (universe-A's `ExportSpec` GROWS the swiss list — a real root move) and TICKS
the nonce (the runtime's global non-NoOp invariant, `air.rs:2631`):

  * **sturdyref-root MOVE** at `state.FIELD_BASE + 4` (was `cap_root`): post `sturdyref_root` IS the
    param swiss-digest (`D (post.swiss)` = `D (exportRecord … :: pre.swiss)` — the grown-list digest).
  * **nonce TICK** `+1` (was freeze): the runtime's global non-NoOp nonce constraint.
  * **freeze** balance limbs, `cap_root`, `reserved`, fields `{0,1,2,3,5,6,7}` (the residual frame).

The moved dedicated root is bound into `state_commit` with ZERO change to the hash-site chain (it is an
absorbed column), so the anti-ghost tooth carries verbatim over the dedicated root.

## RUNTIME-CUTOVER STATUS — genuinely BLOCKED (honest), a DEEPER divergence than handoff/drop

`swissExportA` DOES have a live Rust selector (`EXPORT_STURDY_REF=14`), but that runtime export is
COUNTER-ONLY: it writes `fields[7] += 1` (the export counter), derives a swiss number into `aux[0]`, and
does NOT materialise any swiss-table root (`air.rs:1547-1588`, `trace.rs:828-848`). Universe-A's
`ExportSpec` instead GROWS the swiss list — a genuine root move. So this root-BINDING descriptor (which
moves `sturdyref_root` at `field[4]`) DIVERGES from the live counter-only `EXPORT_STURDY_REF` and CANNOT
pass the cutover harness against it; it carries a LOCAL selector (§0). The descriptor is universe-A-FULL
(root-bound, anti-ghost) but cutover-BLOCKED until the runtime export materialises the swiss root
(`generate_effect_vm_trace` would write `new_state.fields[4] = D(post.swiss)` on the export row, the way
EnlivenRef already does). Reported, not papered.

## The CONNECTOR — `sturdyrefRootProj` to universe-A's `swissExportA_full_sound`

`sturdyrefRootProj D k = D k.swiss`. `unify_swissExport`: when `ExportSpec` holds (so `s'.kernel.swiss =
exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss`), the projected
post-`sturdyref_root` `D s'.kernel.swiss` is EXACTLY `D (exportRecord … :: s.kernel.swiss)` — the grown
swiss-list digest the descriptor's `paramSE.SWISS_DIGEST_NEW` carries. So the runnable `field[4]`
(sturdyref_root) transition IS universe-A's `swiss`-digest transition.

## ===================  IR-BLOCKED — the precise asks  ===================

  * **IR GAP 1 — the 3-way guard `ExportGuard` (AUTHORITY ∧ FRESHNESS ∧ NON-AMPLIFICATION).**
    Set-membership / c-list predicates over `s.kernel.caps`, the swiss-table freshness of `sw`, and
    `rightsNarrowerOrEqual`. The EffectVM row has no cap-graph / swiss-list / rights columns and no
    `findSwiss`/`rightsNarrowerOrEqual` gate. Enforced only inside `swissExportA_full_sound` (carried).

  * **IR GAP 2 — the LIST STRUCTURE (the inserted record, `swiss = exportRecord … :: pre`).** The
    `sturdyref_root` column carries only the scalar digest; `VmHashSite` absorbs trace COLUMNS only, with
    NO site re-deriving the root from a per-row serialization of `List SwissRecord`. So the descriptor
    pins `new_sturdyref_root = D(post.swiss)` (witness-supplied) and binds THAT into `state_commit`, but
    does NOT prove in-circuit that the root IS the genuine list digest, nor that the post-list is the
    pre-list with `exportRecord` consed. Lives in `listLeafInjective LE` + `compressNInjective cN`. ASK:
    a swiss-list-absorbing `VmHashSite`.

  * PER-CELL / PER-ROW; `state.RESERVED` absorbed nowhere (inherited keystone finding).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR
hash`; the swiss-list digest ONLY as the abstract `D`. No `sorry`/`:= True`/`native_decide`/`rfl`-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.swissExportA

namespace Dregg2.Circuit.Emit.EffectVmEmitSwissExport

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

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets + the dedicated `sturdyref_root` column.

`swissExportA`'s universe-A spec MOVES the sturdyref root (it GROWS the swiss list). The live runtime
`EXPORT_STURDY_REF=14` is COUNTER-ONLY (it writes `fields[7] += 1`, derives a swiss number into aux[0],
and does NOT materialise a swiss-table root — `air.rs:1547-1588`, `trace.rs:828-848`). So we carry a
LOCAL selector index `selSE.SWISS_EXPORT` for the root-BINDING descriptor (universe-A-faithful), DISTINCT
from the live counter-only `EXPORT_STURDY_REF` — matching it would falsely claim runtime agreement
(header §RUNTIME-CUTOVER). The dedicated `sturdyref_root` is `sturdyrefRootOff = state.FIELD_BASE + 4`
(the STAGE-3 `systemRoot.STURDYREF` materialisation column). -/

namespace selSE
/-- The `swissExportA` root-binding selector column (LOCAL; DISTINCT from the live counter-only
`EXPORT_STURDY_REF=14` — header §RUNTIME-CUTOVER). -/
def SWISS_EXPORT : Nat := 3
end selSE

namespace paramSE
/-- The post swiss-table digest parameter (witness fills `D (post.swiss)` — the new `sturdyref_root`). -/
def SWISS_DIGEST_NEW : Nat := 2
end paramSE

/-- The dedicated `sturdyref_root` materialisation state-offset: `state.FIELD_BASE + 4` (the STAGE-3
`systemRoot.STURDYREF` home — "was `fields[4]`"). One of the GROUP-4-absorbed columns. -/
def sturdyrefRootOff : Nat := state.FIELD_BASE + 4

/-- The `swissExportA` selector as an expression. -/
def eSelSwissExport : EmittedExpr := .var selSE.SWISS_EXPORT

/-- The post swiss-digest param as an expression. -/
def eSwissDigestNew : EmittedExpr := .var (prmCol paramSE.SWISS_DIGEST_NEW)

/-! ## §1 — The swiss-export row gates (sturdyref-root MOVE + nonce TICK + residual freeze). -/

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

/-- The `swissExportA` AIR identity. -/
def swissExportVmAirName : String := "dregg-effectvm-swissExportA-v1"

/-- The swiss-export per-row gates: sturdyref-root MOVE, nonce TICK, balance/cap/reserved freeze, the
seven residual fields freeze. -/
def swissExportRowGates : List VmConstraint :=
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
def swissExportHashSites : List VmHashSite := [site0, site1, site2, site3]

/-- **`swissExportVmDescriptor`** — the `swissExportA` concrete circuit: sturdyref-root MOVE
(`field[4]`) + nonce TICK + residual frame freeze ++ transition continuity ++ row-0 boundary pins, with
the 4 GROUP-4 hash sites binding the moved dedicated root. Guard + list-structure IR-BLOCKED (header). -/
def swissExportVmDescriptor : EffectVmDescriptor :=
  { name := swissExportVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := swissExportRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := swissExportHashSites
  , ranges := [] }

/-! ## §3 — The swiss-export ROW INTENT. -/

/-- **`SwissExportRowIntent env`** — post `sturdyref_root` (`field[4]`) is the digest param, nonce
ticks `+1`, balance/cap/reserved + residual fields `{0,1,2,3,5,6,7}` frozen. -/
def SwissExportRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol sturdyrefRootOff) = env.loc (prmCol paramSE.SWISS_DIGEST_NEW)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i ∈ frozenFields, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a swiss-export row: `s_swissExport = 1`, `s_noop = 0`. -/
def IsSwissExportRow (env : VmRowEnv) : Prop :=
  env.loc selSE.SWISS_EXPORT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

/-- **`swissExportRowGates_holds_iff`** — on a swiss-export row (`s_noop = 0`), the gates all hold IFF
`SwissExportRowIntent` holds. -/
theorem swissExportRowGates_holds_iff (env : VmRowEnv) (hrow : IsSwissExportRow env) :
    (∀ c ∈ swissExportRowGates, c.holdsVm env false false) ↔ SwissExportRowIntent env := by
  obtain ⟨_hsH, hsN⟩ := hrow
  unfold swissExportRowGates gFieldFixAll frozenFields SwissExportRowIntent
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

/-- **`swissExportVm_faithful` — THE deliverable.** -/
theorem swissExportVm_faithful (env : VmRowEnv) (hrow : IsSwissExportRow env) :
    (∀ c ∈ swissExportRowGates, c.holdsVm env false false) ↔ SwissExportRowIntent env :=
  swissExportRowGates_holds_iff env hrow

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (sturdyref-root tamper).** -/
theorem swissExportVm_rejects_wrong_swissRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol sturdyrefRootOff) ≠ env.loc (prmCol paramSE.SWISS_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gSwissMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** -/
theorem swissExportVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsSwissExportRow env)
    (hwrong : ¬ SwissExportRowIntent env) :
    ¬ (∀ c ∈ swissExportRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((swissExportVm_faithful env hrow).mp h)

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
  ∧ env.loc (prmCol paramSE.SWISS_DIGEST_NEW) = swissDigestNew
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

/-- Under `SwissRowEncodes`, `SwissExportRowIntent` IS the structured per-cell `SwissCellSpec`. -/
theorem intent_to_swissCellSpec (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew) (hint : SwissExportRowIntent env) :
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

/-- **`swissExportDescriptor_full_sound` — the structured soundness.** -/
theorem swissExportDescriptor_full_sound (env : VmRowEnv) (hrow : IsSwissExportRow env)
    (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew)
    (hgates : ∀ c ∈ swissExportRowGates, c.holdsVm env false false) :
    SwissCellSpec pre post swissDigestNew :=
  intent_to_swissCellSpec env pre post swissDigestNew henc ((swissExportVm_faithful env hrow).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, dedicated sturdyref_root included). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `swissExportHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem swissExportHashSites_eq : swissExportHashSites = transferHashSites := rfl

/-- **`swissExportDescriptor_commit_binds_state` — the whole-state tooth.** -/
theorem swissExportDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ swissExportHashSites)
    (hs₂ : siteHoldsAll hash e₂ swissExportHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [swissExportHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-- **`swissExportDescriptor_binds_sturdyref_root` — the per-column anti-ghost.** Equal published
`state_commit`s force the moved dedicated `sturdyref_root` (`field[4]`, absorbed column #7) equal. -/
theorem swissExportDescriptor_binds_sturdyref_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ swissExportHashSites)
    (hs₂ : siteHoldsAll hash e₂ swissExportHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (saCol sturdyrefRootOff) = e₂.loc (saCol sturdyrefRootOff) := by
  have h := swissExportDescriptor_commit_binds_state hash hCR e₁ e₂ hs₁ hs₂ hcommit
  have := congrArg (fun l => l.getD 7 0) h
  simpa only [absorbedCols, List.getD_cons_succ, List.getD_cons_zero, sturdyrefRootOff] using this

/-! ## §8 — THE CONNECTOR — `sturdyrefRootProj` to universe-A's `swissExportA_full_sound`. -/

open Dregg2.Circuit.Inst.SwissExportA (ExportArgs)
open Dregg2.Circuit.Spec.SwissExport (ExportSpec exportRecord)

/-- **`sturdyrefRootProj D k`** — the EffectVM dedicated `sturdyref_root` column value: the whole-list
digest `D`. -/
def sturdyrefRootProj (D : List SwissRecord → ℤ) (k : RecordKernelState) : ℤ := D k.swiss

/-- The predicted post swiss-digest the descriptor's `paramSE.SWISS_DIGEST_NEW` carries: `D` of the
post (grown) swiss-list `exportRecord … :: pre.swiss`. -/
def exportSwissDigestNew (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : ExportArgs) : ℤ :=
  D (exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)

/-- **`unify_swissExport` — THE CONNECTOR.** When universe-A's `ExportSpec` holds (so `s'.kernel.swiss =
exportRecord … :: s.kernel.swiss`), the projected post-`sturdyref_root` is EXACTLY
`exportSwissDigestNew D s args` — the column move the descriptor pins. -/
theorem unify_swissExport (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (hspec : ExportSpec s args.sw args.actor args.exporter args.target args.rights s') :
    sturdyrefRootProj D s'.kernel = exportSwissDigestNew D s args := by
  obtain ⟨_, hsw, _⟩ := hspec
  show D s'.kernel.swiss
      = D (exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)
  rw [hsw]

/-- **`unify_swissExport_via_full_sound` — the runnable dedicated-root move inherits the VALIDATED
guarantee.** A satisfying universe-A `swissExportA_full_sound` witness ⟹ `ExportSpec` ⟹ the projected
post-`sturdyref_root` equals `D` of the genuine grown post-list — the column value the descriptor's
`paramSE.SWISS_DIGEST_NEW` carries. -/
theorem unify_swissExport_via_full_sound
    (S : Surface2) (D : List SwissRecord → ℤ)
    (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Dregg2.Circuit.Inst.SwissExportA.swissExportE LE cN hN hLE)
        (encodeE2 S (Dregg2.Circuit.Inst.SwissExportA.swissExportE LE cN hN hLE) s args s')) :
    sturdyrefRootProj D s'.kernel = exportSwissDigestNew D s args :=
  unify_swissExport D s args s'
    (Dregg2.Circuit.Inst.SwissExportA.swissExportA_full_sound S LE cN hN hLE hRest hLog s args s' h)

/-! ## §9 — NON-VACUITY: a concrete row that satisfies the intent, and one that does not. The good row
moves `field[4]@83` (sturdyref_root) `0 → 77`, ticks nonce@78 `9 → 10`, freezes the rest. -/

/-- A concrete swiss-export row, on RESOLVED ABSOLUTE columns. Selector `SWISS_EXPORT@3 = 1`,
`nonce@56 = 9`, `nonce@78 = 10`, `field[4]@83 = 77`, digest@70 = 77; everything else `0`/frozen. -/
def swissGoodRow : VmRowEnv where
  loc := fun v =>
    if v = 3 then 1           -- SWISS_EXPORT selector
    else if v = 56 then 9     -- sbCol NONCE
    else if v = 78 then 10    -- saCol NONCE
    else if v = 83 then 77    -- saCol sturdyrefRootOff (field[4])
    else if v = 70 then 77    -- prmCol SWISS_DIGEST_NEW
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The resolved absolute indices. -/
theorem col_facts :
    saCol sturdyrefRootOff = 83 ∧ prmCol paramSE.SWISS_DIGEST_NEW = 70
    ∧ sbCol state.NONCE = 56 ∧ saCol state.NONCE = 78 ∧ selSE.SWISS_EXPORT = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- For any field index `i`, the absolute pre/post field columns are `57+i` / `79+i`. -/
theorem field_col_facts (i : Nat) :
    saCol (state.FIELD_BASE + i) = 79 + i ∧ sbCol (state.FIELD_BASE + i) = 57 + i := by
  constructor
  · simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE]; omega
  · simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.FIELD_BASE]; omega

/-- `swissGoodRow` is a genuine swiss-export row. -/
theorem swissGoodRow_isSwissExportRow : IsSwissExportRow swissGoodRow := by
  obtain ⟨_, _, _, _, hsel⟩ := col_facts
  refine ⟨?_, ?_⟩
  · show swissGoodRow.loc selSE.SWISS_EXPORT = 1; rw [hsel]; rfl
  · show swissGoodRow.loc sel.NOOP = 0; rfl

/-- **NON-VACUITY (witness TRUE).** `swissGoodRow` REALIZES the swiss-export intent. -/
theorem swissGoodRow_realizes_intent : SwissExportRowIntent swissGoodRow := by
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
      show (if (79 + i) = 3 then (1:ℤ) else if (79+i) = 56 then 9 else if (79+i) = 78 then 10
        else if (79+i) = 83 then 77 else if (79+i) = 70 then 77 else 0) = 0
      rcases hi with h|h|h|h|h|h|h <;> subst h <;> rfl
    have rhs0 : swissGoodRow.loc (57 + i) = 0 := by
      show (if (57 + i) = 3 then (1:ℤ) else if (57+i) = 56 then 9 else if (57+i) = 78 then 10
        else if (57+i) = 83 then 77 else if (57+i) = 70 then 77 else 0) = 0
      rcases hi with h|h|h|h|h|h|h <;> subst h <;> rfl
    rw [lhs0, rhs0]

/-- A forged swiss-export row: post-`sturdyref_root` (`field[4]`@83) tampered to `999 ≠ 77`. -/
def swissBadRow : VmRowEnv where
  loc := fun v => if v = 83 then 999 else swissGoodRow.loc v
  nxt := swissGoodRow.nxt
  pub := swissGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** -/
theorem swissBadRow_rejected : ¬ (VmConstraint.gate gSwissMove).holdsVm swissBadRow false false := by
  apply swissExportVm_rejects_wrong_swissRoot
  obtain ⟨hsa, hprm, _, _, _⟩ := col_facts
  have rRoot : swissBadRow.loc (saCol sturdyrefRootOff) = 999 := by
    rw [hsa]; show (if (83:Nat) = 83 then (999:ℤ) else swissGoodRow.loc 83) = 999; rfl
  have rPrm : swissBadRow.loc (prmCol paramSE.SWISS_DIGEST_NEW) = 77 := by
    rw [hprm]; show (if (70:Nat) = 83 then (999:ℤ) else swissGoodRow.loc 70) = 77; rfl
  rw [rRoot, rPrm]; decide

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard swissExportVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates (move/tick + 5 freeze + 7 fields)
#guard swissExportVmDescriptor.hashSites.length == 4
#guard swissExportVmDescriptor.traceWidth == 186
#guard swissExportRowGates.length == 13

#assert_axioms swissExportRowGates_holds_iff
#assert_axioms swissExportVm_faithful
#assert_axioms swissExportVm_rejects_wrong_swissRoot
#assert_axioms swissExportVm_rejects_wrong_output
#assert_axioms intent_to_swissCellSpec
#assert_axioms swissExportDescriptor_full_sound
#assert_axioms swissExportDescriptor_commit_binds_state
#assert_axioms swissExportDescriptor_binds_sturdyref_root
#assert_axioms unify_swissExport
#assert_axioms unify_swissExport_via_full_sound
#assert_axioms swissGoodRow_realizes_intent
#assert_axioms swissBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSwissExport
