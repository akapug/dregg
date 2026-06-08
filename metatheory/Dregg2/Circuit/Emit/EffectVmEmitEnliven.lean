/-
# Dregg2.Circuit.Emit.EffectVmEmitEnliven — the CapTP sturdy-ref ENLIVEN `enlivenRefA`, EMITTED onto
  the runnable EffectVM **dedicated `sturdyref_root` column** (the STAGE-3 `system_roots` home), FULL,
  RECONCILED ONTO THE RUNTIME TRACE-GENERATOR LAYOUT, with the supported per-row faithfulness +
  anti-ghost commitment tooth + the connector to universe-A `enlivenRefA_full_sound`, and a PRECISE,
  LOUD flag of the IR-blocked guard/list-structure parts.

## AMPLIFICATION (STAGE 3 `system_roots` + runtime reconcile)

STAGE 3 (`Exec.SystemRoots`, `6aa29e996`) gave each side-table its OWN committed root in a dedicated
kernel-owned namespace. The swiss/sturdyref side-table's root index is `systemRoot.STURDYREF` (the
reconciliation note records it "was `fields[4]`"). On the running EffectVM the dedicated
`sturdyref_root` is MATERIALISED at the state column `state.FIELD_BASE + 4` — the cell's committed
`swiss_table_root` mirror — which the runtime EnlivenRef AIR (`circuit/src/effect_vm/air.rs:1626`,
`f4_after == aux_root`) and `generate_effect_vm_trace` (`trace.rs:882`, `new_state.fields[4] = root`)
BOTH write the post-enliven root to. STAGE 3's GROUP-4 chain already ABSORBS this column
(`transferHashSites` site1 input #4 = `saCol (state.FIELD_BASE + 4)`; `absorbedCols` lists it), so the
moved root is bound into `state_commit` with ZERO change to the hash-site chain — the anti-ghost tooth
carries verbatim.

The OLD swiss descriptors carried the digest on the REINTERPRETED `cap_root` (col 11) and FROZE the
whole frame including the nonce. That DISAGREED with the runtime on three counts (the cutover bug the
`3aaf0772d` reconciliation fixed for the economic effects): (1) the runtime writes the root at
`fields[4]`, NOT `cap_root`; (2) the runtime AIR TICKS the nonce on every non-NoOp row
(`air.rs:2631`, `new_nonce - old_nonce - (1 - s_noop)`); (3) EnlivenRef TICKS `fields[6]` (use_count,
`air.rs:1646`). So the OLD descriptor made the honest enliven trace UNSAT. THIS file RECONCILES enliven
onto the runtime convention and binds the genuine dedicated `sturdyref_root`:

  * **sturdyref-root MOVE** at `state.FIELD_BASE + 4` (was `cap_root`): post `sturdyref_root` IS the
    param swiss-digest (`D (post.swiss)`), the runtime's `new_state.fields[4] = root`.
  * **`fields[6]` use-count TICK** `+1` (was freeze): the runtime's `c_use` constraint.
  * **nonce TICK** `+1` (was freeze): the runtime's global non-NoOp nonce constraint.
  * **freeze** balance limbs, `cap_root`, `reserved`, fields `{0,1,2,3,5,7}` (the runtime's residual
    frame).

This makes enliven a FULL, cutover-ready descriptor: it AGREES with the hand-AIR on the honest trace,
binds the dedicated sturdyref root into `state_commit`, and rejects a tampered root (anti-ghost).

## The CONNECTOR — `sturdyrefRootProj` to universe-A's `enlivenRefA_full_sound`

`sturdyrefRootProj D k = D k.swiss`. `unify_enliven`: when `EnlivenSpec` holds (so `swissEnlivenK
s.kernel sw claimed = some k'`, `s'.kernel = k'`), the projected post-`sturdyref_root` `D s'.kernel.swiss
= D k'.swiss`, and `k'.swiss` is the genuine refcount-bumped post-list (`swissEnlivenK_only_swiss`). So
the runnable `sturdyref_root` (fields[4]) transition IS universe-A's `swiss`-digest transition.

## ===================  IR-BLOCKED — the precise asks  ===================

  * **IR GAP 1 — the 3-way guard `EnlivenGuard` (AUTHORITY ∧ MEMBERSHIP ∧ NON-AMPLIFICATION).**
    Set-membership / c-list / rights-subset predicates over `s.kernel.caps`, `findSwiss s.kernel.swiss
    sw` (MEMBERSHIP is a swiss-table lookup), and `rightsNarrowerOrEqual claimed e.rights`
    (NON-AMPLIFICATION reads the LOOKED-UP entry's rights). No EffectVM cap-graph/swiss-list/rights
    columns; no `findSwiss`/`rightsNarrowerOrEqual` gate. Universe-A commits it as one `propBit`; the
    per-row IR has no guard column and cannot re-derive the lookup/subset. (The runtime DOES enforce a
    1-hop Merkle membership against the committed root — `air.rs:1610-1640` — so the runtime's enliven
    is partially guarded; the per-row descriptor IR still cannot re-derive the c-list/rights content.)
    ASK: a guard-bit `VmConstraint` internalizes the PRESENCE; the membership/rights-subset content
    needs a lookup argument the IR lacks. Enforced only inside `enlivenRefA_full_sound`.

  * **IR GAP 2 — the LIST STRUCTURE (which entry refcount-bumped).** `sturdyref_root` carries the
    scalar digest only; `VmHashSite` absorbs trace COLUMNS, with NO site re-deriving `sturdyref_root`
    from a per-row serialization of `List SwissRecord`. So the descriptor pins `new_sturdyref_root =
    D(post.swiss)` (witness-supplied) and binds THAT into `state_commit`, but does NOT prove in-circuit
    that the root IS the genuine list digest, nor that the post-list is the pre-list with entry `sw`
    refcount-bumped. Lives in `listLeafInjective LE` + `compressNInjective cN`. ASK: a
    swiss-list-absorbing `VmHashSite`.

  * PER-CELL / PER-ROW; `state.RESERVED` absorbed nowhere (inherited keystone finding).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR
hash`; the swiss-list digest ONLY as the abstract `D`. No `sorry`/`:= True`/`native_decide`/`rfl`-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.enlivenRefA

namespace Dregg2.Circuit.Emit.EffectVmEmitEnliven

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
open Dregg2.Circuit.Spec.SwissFrame (swissEnlivenK_only_swiss)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets + the dedicated `sturdyref_root` column.

The running EffectVM's `enlivenRefA` selector is `ENLIVEN_REF = 15` (`columns.rs::sel::ENLIVEN_REF`).
The post swiss-table digest the row pins is carried in `paramEN.SWISS_DIGEST_NEW`. The **dedicated
`sturdyref_root` column** is `sturdyrefRootOff = state.FIELD_BASE + 4` — the STAGE-3
`systemRoot.STURDYREF` materialisation column (the cell's committed `swiss_table_root` mirror) the
runtime writes the post-enliven root to. The use-count counter is `useCountOff = state.FIELD_BASE +
6` (the runtime's `field[6]`). -/

namespace selEN
/-- The `enlivenRefA` effect selector column (`columns.rs::sel::ENLIVEN_REF`). -/
def ENLIVEN : Nat := 15
end selEN

namespace paramEN
/-- The post swiss-table digest parameter (witness fills `D (post.swiss)` — the new `sturdyref_root`). -/
def SWISS_DIGEST_NEW : Nat := 2
end paramEN

/-! The dedicated side-table-root state offsets (read-only references to the STAGE-3 home + runtime
layout). `sturdyrefRootOff` is the swiss/sturdyref root materialisation column-offset (`field[4]`);
`useCountOff` is the runtime's enliven use-count counter offset (`field[6]`). -/

/-- The dedicated `sturdyref_root` materialisation state-offset: `state.FIELD_BASE + 4` (the STAGE-3
`systemRoot.STURDYREF` home — "was `fields[4]`" — and the runtime's committed `swiss_table_root` mirror,
`air.rs:1626`). One of the GROUP-4-absorbed columns (`transferHashSites` site1 input #4). -/
def sturdyrefRootOff : Nat := state.FIELD_BASE + 4
/-- The runtime enliven use-count counter state-offset: `state.FIELD_BASE + 6` (`air.rs:1644`). -/
def useCountOff : Nat := state.FIELD_BASE + 6

/-- The `enlivenRefA` selector as an expression. -/
def eSelEnliven : EmittedExpr := .var selEN.ENLIVEN

/-- The post swiss-digest param as an expression. -/
def eSwissDigestNew : EmittedExpr := .var (prmCol paramEN.SWISS_DIGEST_NEW)

/-! ## §1 — The enliven row gates (RECONCILED: sturdyref-root MOVE + use-count TICK + nonce TICK +
residual freeze). -/

/-- Sturdyref-root MOVE body: `new_sturdyref_root - swissDigestNew` (post `field[4]` IS the param
digest — the runtime's `new_state.fields[4] = root`). -/
def gSwissMove : EmittedExpr := eSub (eSA sturdyrefRootOff) eSwissDigestNew

/-- Use-count TICK body: `new_field6 - old_field6 - 1` (the runtime's `c_use`, `air.rs:1646`). The
runtime's enliven gate is selector-multiplied (`s_enliven * (new_f6 - old_f6 - 1)`); on an enliven row
`s_enliven = 1`, so the per-row polynomial is exactly this difference. -/
def gUseCountTick : EmittedExpr :=
  eSub (eSub (eSA useCountOff) (eSB useCountOff)) (.const 1)

/-- Nonce TICK body (the running prover's GLOBAL non-NoOp invariant, `air.rs:2631`):
`new_nonce − old_nonce − (1 − s_noop)`. On an enliven row `s_noop = 0`, so this ticks. Reused verbatim
from the transfer template (`gNonce`) — the exact runtime polynomial, not a simplified `−1`. -/
def gNonceTick : EmittedExpr := gNonce

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Cap-root freeze body (enliven does NOT touch `caps`; the runtime `c_cap` holds it, `air.rs:1659`). -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- The runtime's residual frozen fields `{0,1,2,3,5,7}` (`field[4]` MOVES, `field[6]` TICKS). -/
def frozenFields : List Nat := [0, 1, 2, 3, 5, 7]

/-- Field-`i` freeze body. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The six residual field-freeze gates (`{0,1,2,3,5,7}`). -/
def gFieldFixAll : List VmConstraint :=
  frozenFields.map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `enlivenRefA` AIR identity. -/
def enlivenVmAirName : String := "dregg-effectvm-enlivenRefA-v1"

/-- The enliven per-row gates: sturdyref-root MOVE, use-count TICK, nonce TICK, balance/cap/reserved
freeze, the six residual fields freeze. -/
def enlivenRowGates : List VmConstraint :=
  [ .gate gSwissMove, .gate gUseCountTick, .gate gNonceTick
  , .gate gBalLoFix, .gate gBalHiFix, .gate gCapFix, .gate gResFix ] ++ gFieldFixAll

/-- Site 2 absorbing the post `cap_root` (unchanged from the transfer keystone — the dedicated
`sturdyref_root` at `field[4]` is absorbed by site1, so the GROUP-4 chain is the keystone's verbatim). -/
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

/-- The ordered GROUP-4 hash sites (identical chain to the transfer keystone — `field[4]`, carrying the
dedicated `sturdyref_root`, is absorbed by site1). -/
def enlivenHashSites : List VmHashSite := [site0, site1, site2, site3]

/-- **`enlivenVmDescriptor`** — the `enlivenRefA` FULL concrete circuit, RECONCILED onto the runtime
layout: sturdyref-root MOVE (`field[4]`) + use-count TICK (`field[6]`) + nonce TICK + residual frame
freeze ++ transition continuity ++ row-0 boundary pins, with the 4 GROUP-4 hash sites binding the moved
dedicated root. Guard + list-structure are IR-BLOCKED (header), NOT in this descriptor. -/
def enlivenVmDescriptor : EffectVmDescriptor :=
  { name := enlivenVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := enlivenRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := enlivenHashSites
  , ranges := [] }

/-! ## §3 — The enliven ROW INTENT (RECONCILED). -/

/-- **`EnlivenRowIntent env`** — post `sturdyref_root` (`field[4]`) is the digest param, use-count
(`field[6]`) ticks `+1`, nonce ticks `+1`, balance/cap/reserved + residual fields `{0,1,2,3,5,7}`
frozen. -/
def EnlivenRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol sturdyrefRootOff) = env.loc (prmCol paramEN.SWISS_DIGEST_NEW)
  ∧ env.loc (saCol useCountOff) = env.loc (sbCol useCountOff) + 1
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i ∈ frozenFields, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is an enliven row: `s_enliven = 1`, `s_noop = 0`. -/
def IsEnlivenRow (env : VmRowEnv) : Prop :=
  env.loc selEN.ENLIVEN = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

/-- **`enlivenRowGates_holds_iff`** — on an enliven row (`s_noop = 0`, so the global nonce gate ticks),
the gates all hold IFF `EnlivenRowIntent` holds. The `IsEnlivenRow` premise supplies `s_noop = 0`, the
factor the runtime's global nonce gate (`gNonce = new_nonce − old_nonce − (1 − s_noop)`) reduces by. -/
theorem enlivenRowGates_holds_iff (env : VmRowEnv) (hrow : IsEnlivenRow env) :
    (∀ c ∈ enlivenRowGates, c.holdsVm env false false) ↔ EnlivenRowIntent env := by
  obtain ⟨_hsE, hsN⟩ := hrow
  unfold enlivenRowGates gFieldFixAll frozenFields EnlivenRowIntent
  constructor
  · intro h
    have hSw := h (.gate gSwissMove) (by simp)
    have hUse := h (.gate gUseCountTick) (by simp)
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
    simp only [VmConstraint.holdsVm, gSwissMove, gUseCountTick, gNonceTick, gNonce, gBalLoFix,
      gBalHiFix, gCapFix, gResFix, eSA, eSB, eSwissDigestNew, eSub, eSelNoop, EmittedExpr.eval]
      at hSw hUse hNon hLo hHi hCap hRes
    rw [hsN] at hNon
    refine ⟨by linarith [hSw], by linarith [hUse], by linarith [hNon], by linarith [hLo],
      by linarith [hHi], by linarith [hCap], by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    simp only [frozenFields] at hi
    linarith
  · rintro ⟨hSw, hUse, hNon, hLo, hHi, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
      rw [hSw]; ring
    · simp only [VmConstraint.holdsVm, gUseCountTick, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hUse]; ring
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

/-- **`enlivenVm_faithful` — THE deliverable.** -/
theorem enlivenVm_faithful (env : VmRowEnv) (hrow : IsEnlivenRow env) :
    (∀ c ∈ enlivenRowGates, c.holdsVm env false false) ↔ EnlivenRowIntent env :=
  enlivenRowGates_holds_iff env hrow

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (sturdyref-root tamper).** A row whose post-`sturdyref_root` (`field[4]`) is NOT the
supplied post-digest fails the `gSwissMove` gate (UNSAT). -/
theorem enlivenVm_rejects_wrong_swissRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol sturdyrefRootOff) ≠ env.loc (prmCol paramEN.SWISS_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gSwissMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** On an enliven row, a post-state that is NOT the intent move fails the
gates. -/
theorem enlivenVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsEnlivenRow env)
    (hwrong : ¬ EnlivenRowIntent env) :
    ¬ (∀ c ∈ enlivenRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((enlivenVm_faithful env hrow).mp h)

/-! ## §6 — The structured per-cell soundness. -/

/-- **`SwissRowEncodes env pre post swissDigestNew`** — the row decodes to `(pre, post)` cell states.
The `sturdyref_root` is carried on the `field[4]` column (`CellState.fields ⟨4,_⟩`); the use-count on
`field[6]`. -/
def SwissRowEncodes (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramEN.SWISS_DIGEST_NEW) = swissDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell enliven spec: post `field[4]` (sturdyref_root) = the new digest, `field[6]` ticks,
nonce ticks, balance/cap/reserved + residual fields `{0,1,2,3,5,7}` frozen. The per-cell projection of
universe-A's `swiss` move (`swiss` whole-list move ⟹ sturdyref-DIGEST column move) plus the runtime's
use-count/nonce ticks. -/
def SwissCellSpec (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  post.fields ⟨4, by decide⟩ = swissDigestNew
  ∧ post.fields ⟨6, by decide⟩ = pre.fields ⟨6, by decide⟩ + 1
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
  ∧ post.fields ⟨7, by decide⟩ = pre.fields ⟨7, by decide⟩

/-- Under `SwissRowEncodes`, `EnlivenRowIntent` IS the structured per-cell `SwissCellSpec`. -/
theorem intent_to_swissCellSpec (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew) (hint : EnlivenRowIntent env) :
    SwissCellSpec pre post swissDigestNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hsw, huse, hnon, hlo, hhi, hcap, hres, hfld⟩ := hint
  -- a reader for any field index: post.fields i = pre.fields i from the frozen-field intent.
  have frozen : ∀ i : Fin 8, i.val ∈ frozenFields → post.fields i = pre.fields i := by
    intro i hi
    have hp := hsaF i; have hq := hsbF i
    have := hfld i.val hi
    rw [hp, hq] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.fields[4] = digest
    have hp4 : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    rw [← hp4]; show env.loc (saCol sturdyrefRootOff) = swissDigestNew
    rw [hsw, hpDig]
  · have hp6 : env.loc (saCol (state.FIELD_BASE + 6)) = post.fields ⟨6, by decide⟩ := hsaF ⟨6, by decide⟩
    have hq6 : env.loc (sbCol (state.FIELD_BASE + 6)) = pre.fields ⟨6, by decide⟩ := hsbF ⟨6, by decide⟩
    show post.fields ⟨6, by decide⟩ = pre.fields ⟨6, by decide⟩ + 1
    rw [← hp6, ← hq6]; exact huse
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
  · exact frozen ⟨7, by decide⟩ (by decide)

/-- **`enlivenDescriptor_full_sound` — the structured soundness.** -/
theorem enlivenDescriptor_full_sound (env : VmRowEnv) (hrow : IsEnlivenRow env)
    (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew)
    (hgates : ∀ c ∈ enlivenRowGates, c.holdsVm env false false) :
    SwissCellSpec pre post swissDigestNew :=
  intent_to_swissCellSpec env pre post swissDigestNew henc ((enlivenVm_faithful env hrow).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, dedicated sturdyref_root included). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `enlivenHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites` (the dedicated
`sturdyref_root` at `field[4]` is absorbed by site1, input #4 — `absorbedCols` lists it). -/
theorem enlivenHashSites_eq : enlivenHashSites = transferHashSites := rfl

/-- **`enlivenDescriptor_commit_binds_state` — the whole-state tooth.** Two enliven rows that satisfy
the hash-sites and publish equal `state_commit`s have identical absorbed columns — the moved dedicated
`sturdyref_root` (`field[4]`, an absorbed column at site1 input #4) included. So a prover CANNOT tamper
the post-`sturdyref_root` (or any absorbed cell) while keeping the published commitment. -/
theorem enlivenDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ enlivenHashSites)
    (hs₂ : siteHoldsAll hash e₂ enlivenHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [enlivenHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-- **`enlivenDescriptor_binds_sturdyref_root` — the per-column anti-ghost.** Equal published
`state_commit`s force the moved dedicated `sturdyref_root` (`field[4]`) equal across the two rows: a
prover cannot forge a different post-sturdyref-root under the same commitment. (`field[4]` is absorbed
column #7 in `absorbedCols`; equal absorbed-column lists ⇒ equal #7 entry.) -/
theorem enlivenDescriptor_binds_sturdyref_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ enlivenHashSites)
    (hs₂ : siteHoldsAll hash e₂ enlivenHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (saCol sturdyrefRootOff) = e₂.loc (saCol sturdyrefRootOff) := by
  have h := enlivenDescriptor_commit_binds_state hash hCR e₁ e₂ hs₁ hs₂ hcommit
  -- absorbedCols entry #7 is `loc (saCol (FIELD_BASE + 4))` = `loc (saCol STURDYREF_ROOT)`.
  have := congrArg (fun l => l.getD 7 0) h
  simpa only [absorbedCols, List.getD_cons_succ, List.getD_cons_zero, sturdyrefRootOff] using this

/-! ## §8 — THE CONNECTOR — `sturdyrefRootProj` to universe-A's `enlivenRefA_full_sound`. -/

open Dregg2.Circuit.Inst.EnlivenRefA (EnlivenArgs)
open Dregg2.Circuit.Spec.SwissEnliven (EnlivenSpec)

/-- **`sturdyrefRootProj D k`** — the EffectVM dedicated `sturdyref_root` column value: the whole-list
digest `D` of the swiss side-table. -/
def sturdyrefRootProj (D : List SwissRecord → ℤ) (k : RecordKernelState) : ℤ := D k.swiss

/-- **`unify_enliven` — THE CONNECTOR.** When universe-A's `EnlivenSpec` holds (so `swissEnlivenK
s.kernel sw claimed = some k'`, `s'.kernel = k'`), the projected post-`sturdyref_root` `D s'.kernel.swiss
= D k'.swiss` — and `k'.swiss` is the genuine refcount-bumped post-list (`swissEnlivenK_only_swiss`). So
`SwissCellSpec`'s sturdyref-root clause IS universe-A's `swiss`-clause, projected to the digest column. -/
theorem unify_enliven (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState) (k' : RecordKernelState)
    (hk : swissEnlivenK s.kernel args.sw args.claimed = some k')
    (hs' : s' = { kernel := k', log := s'.log }) :
    sturdyrefRootProj D s'.kernel = D k'.swiss := by
  show D s'.kernel.swiss = D k'.swiss
  rw [hs']

/-- **`unify_enliven_via_full_sound` — the runnable dedicated-root move inherits the VALIDATED
guarantee.** A satisfying universe-A `enlivenRefA_full_sound` witness ⟹ `EnlivenSpec` ⟹ the projected
post-`sturdyref_root` equals `D` of the genuine refcount-bumped post-list `k'.swiss`. So the runnable
`field[4]` (sturdyref_root) move is universe-A's validated `swiss` transition, not a fourth spec. (Guard
+ list-structure stay enforced ONLY inside the full_sound — IR-BLOCKED at the row, header.) -/
theorem unify_enliven_via_full_sound
    (S : Surface2) (D : List SwissRecord → ℤ)
    (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.EnlivenRefA.RestIffNoSwiss S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Dregg2.Circuit.Inst.EnlivenRefA.enlivenE LE cN hN hLE)
        (encodeE2 S (Dregg2.Circuit.Inst.EnlivenRefA.enlivenE LE cN hN hLE) s args s')) :
    ∃ k', swissEnlivenK s.kernel args.sw args.claimed = some k'
      ∧ sturdyrefRootProj D s'.kernel = D k'.swiss
      ∧ k' = { s.kernel with swiss := k'.swiss } := by
  have hspec : EnlivenSpec s args.sw args.actor args.exporter args.claimed s' :=
    Dregg2.Circuit.Inst.EnlivenRefA.enlivenRefA_full_sound S LE cN hN hLE hRest hLog s args s' h
  obtain ⟨_hg, k', hk, hs'⟩ := hspec
  refine ⟨k', hk, ?_, swissEnlivenK_only_swiss hk⟩
  exact unify_enliven D s args s' k' hk (by rw [hs'])

/-! ## §9 — NON-VACUITY: a concrete RECONCILED enliven row that satisfies the intent, and one that does
not. The good row moves `field[4]` (sturdyref_root) `0 → 77`, ticks `field[6]` `5 → 6` and nonce `9 →
10`, freezes the rest. -/

/-- A concrete reconciled enliven row, defined directly on RESOLVED ABSOLUTE columns (no symbolic
`saCol`/`sbCol` at the call site). Pre-cols: `nonce@56 = 9`, `field[6]@63 = 5`; post-cols:
`field[4]@83 = 77` (the new sturdyref_root), `field[6]@85 = 6`, `nonce@78 = 10`; param digest@70 = 77.
Selector `ENLIVEN@15 = 1`. Everything else `0`/frozen. (Resolved column arithmetic:
`STATE_BEFORE_BASE=54`, `PARAM_BASE=68`, `STATE_AFTER_BASE=76`, `FIELD_BASE=3`.) -/
def swissGoodRow : VmRowEnv where
  loc := fun v =>
    if v = 15 then 1          -- ENLIVEN selector
    else if v = 56 then 9     -- sbCol NONCE
    else if v = 78 then 10    -- saCol NONCE
    else if v = 63 then 5     -- sbCol useCountOff (field[6])
    else if v = 85 then 6     -- saCol useCountOff (field[6])
    else if v = 83 then 77    -- saCol sturdyrefRootOff (field[4])
    else if v = 70 then 77    -- prmCol SWISS_DIGEST_NEW
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- Column constants for the good row (the resolved absolute indices). All by `rfl` after unfolding the
layout constants. -/
theorem col_facts :
    saCol sturdyrefRootOff = 83 ∧ prmCol paramEN.SWISS_DIGEST_NEW = 70
    ∧ sbCol state.NONCE = 56 ∧ saCol state.NONCE = 78
    ∧ sbCol useCountOff = 63 ∧ saCol useCountOff = 85
    ∧ selEN.ENLIVEN = 15 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- For any in-range field index `i`, the absolute pre/post field columns are `57+i` / `79+i`. -/
theorem field_col_facts (i : Nat) :
    saCol (state.FIELD_BASE + i) = 79 + i ∧ sbCol (state.FIELD_BASE + i) = 57 + i := by
  constructor
  · simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE]; omega
  · simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.FIELD_BASE]; omega

/-- `swissGoodRow` is a genuine enliven row. -/
theorem swissGoodRow_isEnlivenRow : IsEnlivenRow swissGoodRow := by
  obtain ⟨_, _, _, _, _, _, hsel⟩ := col_facts
  refine ⟨?_, ?_⟩
  · show swissGoodRow.loc selEN.ENLIVEN = 1; rw [hsel]; rfl
  · show swissGoodRow.loc sel.NOOP = 0; rfl

/-- **NON-VACUITY (witness TRUE).** `swissGoodRow` REALIZES the reconciled enliven intent. -/
theorem swissGoodRow_realizes_intent : EnlivenRowIntent swissGoodRow := by
  obtain ⟨hsa, hprm, hsbN, hsaN, hsbU, hsaU, _hsel⟩ := col_facts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- root@83 = 77 = digest@70
    rw [hsa, hprm]; rfl
  · -- field[6]: 6 = 5 + 1
    rw [hsaU, hsbU]; rfl
  · -- nonce: 10 = 9 + 1
    rw [hsaN, hsbN]; rfl
  · -- bal_lo freeze: both unnamed ⇒ 0 = 0
    rfl
  · rfl  -- bal_hi
  · rfl  -- cap_root
  · rfl  -- reserved
  · -- residual fields {0,1,2,3,5,7}: pre@57+i / post@79+i are both unnamed (≠ all the if-keys) ⇒ 0 = 0
    intro i hi
    obtain ⟨hfa, hfb⟩ := field_col_facts i
    rw [hfa, hfb]
    simp only [frozenFields, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    have lhs0 : swissGoodRow.loc (79 + i) = 0 := by
      show (if (79 + i) = 15 then (1:ℤ) else if (79+i) = 56 then 9 else if (79+i) = 78 then 10
        else if (79+i) = 63 then 5 else if (79+i) = 85 then 6 else if (79+i) = 83 then 77
        else if (79+i) = 70 then 77 else 0) = 0
      rcases hi with h|h|h|h|h|h <;> subst h <;> rfl
    have rhs0 : swissGoodRow.loc (57 + i) = 0 := by
      show (if (57 + i) = 15 then (1:ℤ) else if (57+i) = 56 then 9 else if (57+i) = 78 then 10
        else if (57+i) = 63 then 5 else if (57+i) = 85 then 6 else if (57+i) = 83 then 77
        else if (57+i) = 70 then 77 else 0) = 0
      rcases hi with h|h|h|h|h|h <;> subst h <;> rfl
    rw [lhs0, rhs0]

/-- A forged enliven row: `swissGoodRow` with the post-`sturdyref_root` (`field[4]`@83) tampered to
`999 ≠ 77`. -/
def swissBadRow : VmRowEnv where
  loc := fun v => if v = 83 then 999 else swissGoodRow.loc v
  nxt := swissGoodRow.nxt
  pub := swissGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `swissBadRow`'s post-`sturdyref_root` is NOT
the param digest, so the `gSwissMove` gate REJECTS it — a concrete UNSAT. -/
theorem swissBadRow_rejected : ¬ (VmConstraint.gate gSwissMove).holdsVm swissBadRow false false := by
  apply enlivenVm_rejects_wrong_swissRoot
  obtain ⟨hsa, hprm, _, _, _, _, _⟩ := col_facts
  have rRoot : swissBadRow.loc (saCol sturdyrefRootOff) = 999 := by
    rw [hsa]; show (if (83:Nat) = 83 then (999:ℤ) else swissGoodRow.loc 83) = 999; rfl
  have rPrm : swissBadRow.loc (prmCol paramEN.SWISS_DIGEST_NEW) = 77 := by
    rw [hprm]; show (if (70:Nat) = 83 then (999:ℤ) else swissGoodRow.loc 70) = 77; rfl
  rw [rRoot, rPrm]; decide

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard enlivenVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates (3 move/tick + 4 freeze + 6 fields)
#guard enlivenVmDescriptor.hashSites.length == 4
#guard enlivenVmDescriptor.traceWidth == 186
#guard enlivenRowGates.length == 13

#assert_axioms enlivenRowGates_holds_iff
#assert_axioms enlivenVm_faithful
#assert_axioms enlivenVm_rejects_wrong_swissRoot
#assert_axioms enlivenVm_rejects_wrong_output
#assert_axioms intent_to_swissCellSpec
#assert_axioms enlivenDescriptor_full_sound
#assert_axioms enlivenDescriptor_commit_binds_state
#assert_axioms enlivenDescriptor_binds_sturdyref_root
#assert_axioms unify_enliven
#assert_axioms unify_enliven_via_full_sound
#assert_axioms swissGoodRow_realizes_intent
#assert_axioms swissBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitEnliven
