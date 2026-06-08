/-
# Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce — the NONCE-BUMP effect `incrementNonceA`, EMITTED
  onto the runnable EffectVM `nonce` column, welded to universe-A's `IncrementNonceSpec`.

## The "ONE circuit" thesis for `incrementNonceA` — the effect that GENUINELY ticks the nonce

Unlike transfer (whose descriptor TICKS a nonce column that the executor FREEZES — the named
`CellTransferSpecFrozenNonce` divergence in the transfer connector), `incrementNonceA` is the effect
whose nonce column move HAS a real executor counterpart. The executor's `.incrementNonceA` arm
(`Spec/cellstatemonotone.lean`) runs `stateStep s nonceField actor cell (.int n)`, which WRITES the cell's
`nonce` field to exactly `n` (`fieldOf nonceField (s'.kernel.cell cell) = n`,
`execFullA_incrementNonce_nonceBumped`), freezing the conserved `bal` ledger, the `caps` graph, and every
other cell. So the EffectVM `nonce` column genuinely moves, and we PROVE the descriptor's nonce move
MATCHES the executor — NO divergence isolated.

NOTE on the semantics: the running executor SETS the nonce to the supplied value `n` (a monotone
metadata write), it does NOT compute `pre + 1` in-kernel. So the descriptor's nonce gate is a MOVE to a
parameter `param.NONCE_NEW` (the value the witness fills with `n`), pinned `new_nonce = nonceNew`. The
"+1" framing is the protocol's monotone-advance intent (the caller passes the bumped value); the kernel
write is `:= n`. We pin the column to the param and connect that param to the executor's written `n`.

`incrementNonceVmDescriptor` emits exactly that: the nonce MOVE gate `new_nonce - nonceNew = 0`, with the
balance limbs / cap_root / reserved / 8 fields FROZEN (a metadata bump moves no value, edits no
capability), and the GROUP-4 hash chain binding the post-state (incl. the moved nonce) into
`state_commit`.

## What is PROVED

  * `incNonceVm_faithful` — emitted per-row gates ⟺ `IncNonceRowIntent` (nonce := nonceNew, frame freeze).
  * `incNonceDescriptor_full_sound` — satisfying the descriptor under `RowEncodes` forces
    `CellIncNonceSpec` AND publishes `post.commit = PI[NEW_COMMIT]`.
  * `incNonceDescriptor_commit_binds_state` — anti-ghost (reuses the transfer keystone; same hash chain).
    Because the nonce column (`site0`) IS absorbed, a tampered post-nonce that claims the published
    `NEW_COMMIT` is UNSAT.
  * `unify_incNonce` / `unify_incNonce_exec` — a committed `IncrementNonceSpec`, projected per cell under
    `cellProjN`, satisfies `CellIncNonceSpec` EXACTLY with the nonce MOVE param equal to the executor's
    written `n` (`fieldOf nonceField (s'.kernel.cell cell) = n`). THE NONCE MOVE MATCHES — proved, not
    isolated. The conserved `bal` / `caps` / frame are `0 = 0` frozen (the projection carries no high-limb
    / cap-root / reserved analogue), matching the executor's literal `bal`/`caps`-freeze.

## HONEST BOUNDARY

  * PER-CELL / PER-ROW. The nonce write on ONE cell + its binding into `state_commit`. Cross-row
    composition + the disclosing log receipt = the turn layer, cited.
  * The `cell` index + the `incNonceGuard` (authority/membership/liveness) GUARD have no row column; in
    universe-A's spec (cited).
  * The EffectVM block's `bal_lo` is a SINGLE limb projected from the conserved `balOf (cell record)`
    (`Transfer.balOf`); the executor's nonce bump leaves the cell record's `balance` field intact
    (`incrementNonce_cellWrite_correct`), so `bal_lo` freezes — MATCHES. (The per-asset `bal` ledger is
    likewise frozen by the spec frame; the row carries the conserved cell-record balance, frozen here.)
  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding).

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatemonotone

namespace Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.CellStateMonotone

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param for the increment-nonce effect row.

The bumped nonce value `n` rides a parameter column `param.NONCE_NEW` (offset 2, after AMOUNT/DIRECTION),
the value the witness generator fills with the supplied `n`. -/

namespace selIN
/-- The `incrementNonceA` effect selector column. -/
def INC_NONCE : Nat := 6
end selIN

namespace paramIN
/-- The new-nonce parameter: the value the witness fills with the supplied `n`. -/
def NONCE_NEW : Nat := 2
end paramIN

def eSelIncNonce : EmittedExpr := .var selIN.INC_NONCE
def eNonceNew : EmittedExpr := .var (prmCol paramIN.NONCE_NEW)

/-! ## §1 — The increment-nonce row gates (nonce MOVE to the param, frame freeze). -/

/-- Nonce MOVE body: `new_nonce - nonceNew` (the post nonce IS the param value `n`). -/
def gNonceMove : EmittedExpr := eSub (eSA state.NONCE) eNonceNew

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The increment-nonce per-row gates (nonce move + balance/cap/reserved freeze + 8 fields freeze). -/
def incNonceRowGates : List VmConstraint :=
  [ .gate gNonceMove, .gate gBalLoFix, .gate gBalHiFix, .gate gCapFix, .gate gResFix ]
  ++ gFieldFixAll

/-! ## §2 — The emitted INCREMENT-NONCE descriptor. -/

def incNonceVmAirName : String := "dregg-effectvm-incrementNonce-v1"

/-- **`incrementNonceVmDescriptor`** — the `incrementNonceA` effect's full concrete circuit. -/
def incrementNonceVmDescriptor : EffectVmDescriptor :=
  { name := incNonceVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := incNonceRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The INCREMENT-NONCE ROW INTENT. -/

/-- **`IncNonceRowIntent env`** — `nonce` is set to the param `nonceNew`, the rest of the block fixed. -/
def IncNonceRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.NONCE) = env.loc (prmCol paramIN.NONCE_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

def IsIncNonceRow (env : VmRowEnv) : Prop :=
  env.loc selIN.INC_NONCE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

theorem incNonceVm_faithful (env : VmRowEnv) :
    (∀ c ∈ incNonceRowGates, c.holdsVm env false false) ↔ IncNonceRowIntent env := by
  unfold incNonceRowGates gFieldFixAll IncNonceRowIntent
  constructor
  · intro h
    have hN := h (.gate gNonceMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi; apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gNonceMove, gBalLoFix, gBalHiFix, gCapFix, gResFix,
      eSA, eSB, ePrm, eNonceNew, eSub, EmittedExpr.eval] at hN hLo hHi hCap hRes
    refine ⟨by linarith [hN], by linarith [hLo], by linarith [hHi], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hN, hLo, hHi, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gNonceMove, eSA, eSB, ePrm, eNonceNew, eSub, EmittedExpr.eval]
      rw [hN]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **Anti-ghost (nonce tamper).** A row whose post-`nonce` is NOT the param `nonceNew` fails the
`gNonceMove` gate (UNSAT). -/
theorem incNonceVm_rejects_wrong_nonce (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (prmCol paramIN.NONCE_NEW)) :
    ¬ (VmConstraint.gate gNonceMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonceMove, eSA, eSB, ePrm, eNonceNew, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith [h]

/-! ## §5 — `CellIncNonceSpec` + `RowEncodes` → structured per-cell soundness. -/

/-- The per-cell increment-nonce spec: nonce := `nonceNew`, the rest of the block frozen. -/
def CellIncNonceSpec (pre : CellState) (nonceNew : ℤ) (post : CellState) : Prop :=
  post.nonce = nonceNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

def RowEncodes (env : VmRowEnv) (pre : CellState) (nonceNew : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol paramIN.NONCE_NEW) = nonceNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (nonceNew : ℤ)
    (henc : RowEncodes env pre nonceNew post) (hint : IncNonceRowIntent env) :
    CellIncNonceSpec pre nonceNew post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpN,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hnon, hbal, hbhi, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaN, ← hpN]; exact hnon
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · intro i; have := hfld i.val i.isLt; rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem incNonceRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ incNonceRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ incNonceRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold incNonceRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

theorem incNonceDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (nonceNew : ℤ)
    (henc : RowEncodes env pre nonceNew post)
    (hsat : satisfiedVm hash incrementNonceVmDescriptor env true true) :
    CellIncNonceSpec pre nonceNew post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hgates : ∀ c ∈ incNonceRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold incrementNonceVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := incNonceRowGates_flag_indep env true true hgates
  have hint := (incNonceVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post nonceNew henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ incrementNonceVmDescriptor.constraints := by
      unfold incrementNonceVmDescriptor; simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone). The nonce column is
absorbed (`site0`), so a tampered post-nonce that claims the published `NEW_COMMIT` is UNSAT. -/

theorem incNonce_sites_eq : incrementNonceVmDescriptor.hashSites = transferHashSites := rfl

theorem incNonceDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjN` to universe-A's `IncrementNonceSpec`.

`cellProjN k c` reads cell `c`'s `nonce` field (`fieldOf nonceField`) into the keystone's `nonce`; the
conserved `balLo` reads `Transfer.balOf (k.cell c)` (the cell record's `balance` field — the SAME measure
the spec's `incrementNonce_cellWrite_correct` proves FROZEN across the bump). The EffectVM columns with no
record analogue (balHi/fields/capRoot/reserved) are `0` (FROZEN). -/

/-- Project cell `c` of `k` into the keystone's `CellState`: `nonce` = the cell's `nonce` field
(`fieldOf nonceField`), `balLo` = the conserved `balOf` measure, the rest `0`. -/
def cellProjN (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := fieldOf nonceField (k.cell c)
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- The conserved `balOf` measure is FROZEN across a committed nonce bump (the spec's
`incrementNonce_cellWrite_correct` balance-frame). So `cellProjN`'s `balLo` is unchanged. -/
theorem proj_balLo_frozen (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hspec : IncrementNonceSpec s actor cell n s') :
    (cellProjN s'.kernel cell).balLo = (cellProjN s.kernel cell).balLo := by
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hspec.2.1]
  exact (incrementNonce_cellWrite_correct s.kernel cell n).2.1

/-- **`unify_incNonce` — THE UNIFICATION (the nonce move MATCHES).** A committed universe-A nonce bump
(`IncrementNonceSpec`), projected onto `cell` under `cellProjN` with the new-nonce param `= n`, satisfies
the keystone's per-cell `CellIncNonceSpec` EXACTLY: the post `nonce` IS the written `n`
(`incrementNonce_cellWrite_correct`); the conserved `balLo` is frozen; balHi/fields/capRoot/reserved are
`0 = 0` (frozen). The descriptor's NONCE MOVE column genuinely matches the executor's write — NO divergence
isolated (the transfer connector's `CellTransferSpecFrozenNonce` gap does NOT arise here). -/
theorem unify_incNonce (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (hspec : IncrementNonceSpec s actor cell n s') :
    CellIncNonceSpec (cellProjN s.kernel cell) (n : ℤ) (cellProjN s'.kernel cell) := by
  refine ⟨?_, ?_, rfl, fun _ => rfl, rfl, rfl⟩
  · -- the post nonce IS the written n
    show fieldOf nonceField (s'.kernel.cell cell) = (n : ℤ)
    rw [hspec.2.1]
    exact (incrementNonce_cellWrite_correct s.kernel cell n).1
  · exact proj_balLo_frozen s s' actor cell n hspec

/-- **`unify_incNonce_exec` — same, against the executor directly.** A committed
`execFullA s (.incrementNonceA actor cell n) = some s'` projects per-cell to the keystone's
`CellIncNonceSpec` with the nonce moved to exactly `n`. The runnable nonce column transition IS the
executor's nonce write. -/
theorem unify_incNonce_exec (s s' : RecChainedState) (actor cell : CellId) (n : Int)
    (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    CellIncNonceSpec (cellProjN s.kernel cell) (n : ℤ) (cellProjN s'.kernel cell) :=
  unify_incNonce s s' actor cell n ((execFullA_incrementNonce_iff_spec s actor cell n s').mp h)

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement.** With the new-nonce param
encoded as the executor's written `n`, the descriptor's pinned post-state agrees with the executor's
post-cell state on EVERY clause INCLUDING the nonce (the move MATCHES) and the frozen frame. This is the
one effect in the balance/field group where the nonce column has a genuine executor counterpart. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (actor cell : CellId) (n : Int) (post : CellState)
    (henc : RowEncodes env (cellProjN s.kernel cell) (n : ℤ) post)
    (hsat : satisfiedVm hash incrementNonceVmDescriptor env true true)
    (hexec : execFullA s (.incrementNonceA actor cell n) = some s') :
    post.nonce = (cellProjN s'.kernel cell).nonce
    ∧ post.balLo = (cellProjN s'.kernel cell).balLo
    ∧ post.balHi = (cellProjN s'.kernel cell).balHi
    ∧ (∀ i, post.fields i = (cellProjN s'.kernel cell).fields i)
    ∧ post.capRoot = (cellProjN s'.kernel cell).capRoot
    ∧ post.reserved = (cellProjN s'.kernel cell).reserved := by
  obtain ⟨hcirc, _⟩ := incNonceDescriptor_full_sound hash env (cellProjN s.kernel cell) post (n : ℤ)
    henc hsat
  obtain ⟨hcN, hcLo, hcHi, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heN, heLo, heHi, heF, heCap, heRes⟩ := unify_incNonce_exec s s' actor cell n hexec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.nonce = n (circuit) ; (cellProjN s' cell).nonce = n (executor) — THE MOVE MATCHES
    rw [hcN, heN]
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §8 — NON-VACUITY. -/

/-- A concrete increment-nonce row: `nonce 5 → 9`, `nonceNew = 9`, balance/frame fixed. -/
def goodIncNonceRow : VmRowEnv where
  loc := fun v =>
    if v = selIN.INC_NONCE then 1
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 9
    else if v = prmCol paramIN.NONCE_NEW then 9
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodIncNonceRow` REALIZES the intent (`nonce → 9 = nonceNew`,
balance/frame frozen). -/
theorem goodIncNonceRow_realizes_intent : IncNonceRowIntent goodIncNonceRow := by
  unfold IncNonceRowIntent goodIncNonceRow
  simp only [sbCol, saCol, prmCol, selIN.INC_NONCE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, paramIN.NONCE_NEW]
  refine ⟨by norm_num, ?_, rfl, rfl, rfl, ?_⟩
  · -- bal_lo frozen: sa bal_lo (76) = sb bal_lo (54); both miss named cols ⇒ 0 = 0
    norm_num
  · intro i hi
    have e1 : (76 + (3 + i) = 6) = False := by simp; omega
    have e2 : (76 + (3 + i) = 56) = False := by simp; omega
    have e3 : (76 + (3 + i) = 78) = False := by simp; omega
    have e4 : (76 + (3 + i) = 70) = False := by simp; omega
    have f1 : (54 + (3 + i) = 6) = False := by simp; omega
    have f2 : (54 + (3 + i) = 56) = False := by simp; omega
    have f3 : (54 + (3 + i) = 78) = False := by simp; omega
    have f4 : (54 + (3 + i) = 70) = False := by simp; omega
    simp only [e1, e2, e3, e4, f1, f2, f3, f4, if_false]

/-- A FORGED row: `goodIncNonceRow` with post-`nonce` tampered to `999 ≠ 9`. -/
def badIncNonceRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 999 else goodIncNonceRow.loc v
  nxt := goodIncNonceRow.nxt
  pub := goodIncNonceRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badIncNonceRow`'s post-`nonce` is NOT the
param, so `gNonceMove` REJECTS it. -/
theorem badIncNonceRow_rejected :
    ¬ (VmConstraint.gate gNonceMove).holdsVm badIncNonceRow false false := by
  apply incNonceVm_rejects_wrong_nonce
  simp only [badIncNonceRow, goodIncNonceRow, sbCol, saCol, prmCol, selIN.INC_NONCE,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.NONCE, paramIN.NONCE_NEW]
  norm_num

/-! ## §9 — Axiom-hygiene tripwires. -/

#guard incrementNonceVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard incrementNonceVmDescriptor.hashSites.length == 4
#guard incrementNonceVmDescriptor.traceWidth == 186

#assert_axioms incNonceVm_faithful
#assert_axioms incNonceVm_rejects_wrong_nonce
#assert_axioms intent_to_cellSpec
#assert_axioms incNonceRowGates_flag_indep
#assert_axioms incNonceDescriptor_full_sound
#assert_axioms incNonceDescriptor_commit_binds_state
#assert_axioms proj_balLo_frozen
#assert_axioms unify_incNonce
#assert_axioms unify_incNonce_exec
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodIncNonceRow_realizes_intent
#assert_axioms badIncNonceRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
