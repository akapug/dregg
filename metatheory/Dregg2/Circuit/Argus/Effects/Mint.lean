/-
# Dregg2.Circuit.Argus.Effects.Mint — the SUPPLY-MINT effect's FULL-STATE-on-RUNNABLE welded into Argus.

`mintA`'s per-cell EffectVM soundness (`EffectVmEmitMint.mintDescriptor_full_sound`) and its Argus weld
(`Argus/Compile.lean`, `compileE .mint = mintVmDescriptor`) already stand. `EffectVmEmitMintRunnable`
amplified the per-cell soundness to FULL-state on the RUNNABLE descriptor via the validated recipe
(`mintVmDescriptorWide` + the generic `runnable_full_sound`): a satisfying wide mint row pins all 17
RecordKernelState fields (the per-cell credit + frame freeze AND the 8 side-table roots frozen), with the
anti-ghost on every column/root (`mint_rejects_state_tamper`/`mint_rejects_root_tamper`).

This module welds that full-state-on-RUNNABLE result into the Argus library (so the coherence anchor
`Dregg2.Circuit.Argus` carries it), re-exporting the deliverable under the Argus effect namespace. It owns
only its own declarations and imports the audited runnable module read-only.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the sole crypto carrier is the NAMED
`Poseidon2SpongeCR` portal (inside the reused generic theorem). No `sorry` / `:= True` / `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitMintRunnable

namespace Dregg2.Circuit.Argus.Effects.Mint

open Dregg2.Circuit.Emit.EffectVmEmit
  (VmRowEnv VmConstraint satisfiedVm EffectVmDescriptor siteHoldsAll prmCol)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitMint (CellMintSpec RowEncodes IsMintRow)
open Dregg2.Circuit.Emit.EffectVmEmitMintRunnable
  (mintVmDescriptorWide mint_runnable_full_sound)
open Dregg2.Exec.SystemRoots (SysRoots)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit.param (AMOUNT)

/-- **`mint_full_state_on_runnable` — the Argus-welded deliverable.** A row satisfying the RUNNABLE wide
mint descriptor `mintVmDescriptorWide` (the circuit the EffectVM prover runs), under the structured decode,
pins the FULL 17-field declarative post-state: the per-cell `CellMintSpec` (balance credited by `amt`, the
whole frame — incl. the frozen nonce — frozen) AND the 8 side-table roots FROZEN. The genuine full-state
soundness lives in `EffectVmEmitMintRunnable.mint_runnable_full_sound`; this names it under the Argus effect
namespace so the coherence anchor carries it. -/
theorem mint_full_state_on_runnable (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsMintRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash mintVmDescriptorWide env true true) :
    CellMintSpec pre amt post ∧ postRoots = preRoots :=
  mint_runnable_full_sound amt preRoots hash env pre post postRoots hrow henc hroots hsat

#assert_axioms mint_full_state_on_runnable

/-! ## §2 — COMPLETENESS FIX: the AMOUNT-NON-NEGATIVITY in-circuit conjunct (`0 ≤ amt`).

### The gap (per the overnight completeness audit)

Every economic-family executor step gates on `0 ≤ amt` BEFORE it commits
(`recKMint`/`recKBurn` `TurnExecutorFull.lean:91,100`, `recKExec`/`recKExecAsset`
`RecordKernel.lean:641,757`). But the RUNNABLE EffectVM descriptors
(`mintVmDescriptorWide` / `burnVmDescriptorWide` / `transferVmDescriptorWide`) carry NO gate forcing
non-negativity: their per-row gates pin only the *arithmetic* of the move
(`new_bal = old_bal ± amount`, frame frozen). The `EffectVmDescriptor.ranges` field DECLARES a
`[0,2^b)` bound, but `EffectVmEmit.satisfiedVm` enforces ONLY `constraints` + `hashSites` — the
`ranges` list is rendered to JSON for the Rust prover and is INERT in the Lean soundness denotation.
So a witness with a NEGATIVE `amt` satisfies `mintVmDescriptorWide` (it satisfies `post.balLo =
pre.balLo + amt` for the negative `amt`): a "negative mint" is a covert BURN, and a negative transfer
reverses direction — the executor rejects both, the circuit (as it stood) accepts them. A light client
seeing only the proof would accept a proof over an amount the executor would NEVER admit. This is the
COMPLETENESS half of the acceptance criterion failing, and `amt` (unlike authority/liveness) IS a
column the row already carries, so it is genuinely fixable as an in-circuit conjunct.

### The fix (a faithful arithmetic range gadget — bit-decomposition)

Gates are equalities (`body.eval = 0`); `0 ≤ amt` cannot be a single polynomial identity over `ℤ`
without a witness, so we use the STANDARD range-check arithmetization (the meaning the `ranges` field
intends): introduce `b` bit-witness columns, gate each to a Boolean (`bᵢ·(bᵢ−1) = 0`, reusing the
proven `selectorGate` pattern), and gate the amount column to their base-2 recomposition
(`amt − Σ bᵢ·2ⁱ = 0`). A satisfying assignment then has `amt = Σ bᵢ·2ⁱ` with each `bᵢ ∈ {0,1}`, hence
`0 ≤ amt < 2^b` — a genuine in-circuit conjunct (the prover CANNOT publish a negative amount). The
gadget is generic over the amount column + the bit-witness columns (so burn's `param.BURN_AMOUNT_LO`
column and transfer/balanceA's `param.AMOUNT` column reuse it), proved by list induction so the proof
is width-independent. Imports read-only; this owned leaf module adds only its own declarations. -/

/-! ### §2.1 — the generic range gadget (bit-decomposition), proved sound + a UNSAT tooth. -/

/-- A single Boolean-witness gate on column `c`: `c·(c−1) = 0` (so `loc c ∈ {0,1}`). Term-identical to
`EffectVmEmit.selectorGateBody`; we restate it locally so this module stays self-contained. -/
def bitGate (c : Nat) : VmConstraint :=
  .gate (.mul (.var c) (.add (.var c) (.const (-1))))

/-- The base-2 recomposition expression `Σ_{i<cols.length} 2^i · var (cols[i])`, head = least-significant
bit. Built by structural recursion so its soundness is a clean list induction. -/
def recomposeExpr : List Nat → EmittedExpr
  | []        => .const 0
  | c :: cs   => .add (.var c) (.mul (.const 2) (recomposeExpr cs))

/-- The amount-non-negativity gadget for amount column `amtCol` decomposed over bit columns `bits`:
each `bit` is Boolean, and `amtCol` equals their base-2 recomposition (`amtCol − Σ 2^i·bitᵢ = 0`). -/
def amountRangeGates (amtCol : Nat) (bits : List Nat) : List VmConstraint :=
  bits.map bitGate
  ++ [ .gate (.add (.var amtCol) (.mul (.const (-1)) (recomposeExpr bits))) ]

/-- The integer value of the recomposition under a row assignment: `Σ 2^i · loc (bits[i])`. -/
def recomposeVal (loc : Nat → ℤ) : List Nat → ℤ
  | []      => 0
  | c :: cs => loc c + 2 * recomposeVal loc cs

/-- `recomposeExpr`'s `eval` IS `recomposeVal` (structural; the gadget computes what it claims). -/
theorem recomposeExpr_eval (loc : Nat → ℤ) (bits : List Nat) :
    (recomposeExpr bits).eval loc = recomposeVal loc bits := by
  induction bits with
  | nil => rfl
  | cons c cs ih => simp only [recomposeExpr, recomposeVal, EmittedExpr.eval, ih]

/-- **The bit gates force each witness column to a Boolean** (`loc c ∈ {0,1}`). -/
theorem bitGate_forces_bit (env : VmRowEnv) (c : Nat)
    (h : (bitGate c).holdsVm env true true) :
    env.loc c = 0 ∨ env.loc c = 1 := by
  simp only [bitGate, VmConstraint.holdsVm, EmittedExpr.eval] at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- **A base-2 recomposition of Booleans is non-negative** (`0 ≤ Σ 2^i·bᵢ` when every `bᵢ ∈ {0,1}`).
List induction: head term `loc c ≥ 0` (a bit), tail `2·(…) ≥ 0` (IH, `2 > 0`). -/
theorem recomposeVal_nonneg (loc : Nat → ℤ) (bits : List Nat)
    (hbits : ∀ c ∈ bits, loc c = 0 ∨ loc c = 1) :
    0 ≤ recomposeVal loc bits := by
  induction bits with
  | nil => simp [recomposeVal]
  | cons c cs ih =>
    simp only [recomposeVal]
    have hc : 0 ≤ loc c := by rcases hbits c (by simp) with h | h <;> rw [h] <;> norm_num
    have hcs : 0 ≤ recomposeVal loc cs :=
      ih (fun x hx => hbits x (by simp [hx]))
    linarith

/-- **THE GADGET SOUNDNESS — `0 ≤ loc amtCol`.** If every gate of `amountRangeGates amtCol bits`
holds on a row, then the amount column is non-negative: the bit gates make each witness a Boolean
(`recomposeVal_nonneg`), and the recomposition gate equates `loc amtCol` to that non-negative sum.
This is the in-circuit decode of the executor's `0 ≤ amt` precondition. -/
theorem amountRangeGates_force_nonneg (env : VmRowEnv) (amtCol : Nat) (bits : List Nat)
    (h : ∀ g ∈ amountRangeGates amtCol bits, g.holdsVm env true true) :
    0 ≤ env.loc amtCol := by
  -- the recomposition (last) gate: `loc amtCol − recomposeVal = 0`, i.e. `loc amtCol = recomposeVal`.
  have hrec : (VmConstraint.gate
      (.add (.var amtCol) (.mul (.const (-1)) (recomposeExpr bits)))).holdsVm env true true := by
    apply h; simp only [amountRangeGates, List.mem_append, List.mem_singleton]; exact Or.inr rfl
  simp only [VmConstraint.holdsVm, EmittedExpr.eval, recomposeExpr_eval] at hrec
  have heq : env.loc amtCol = recomposeVal env.loc bits := by linarith
  -- every bit column is Boolean (each `bitGate` is among the gates).
  have hbits : ∀ c ∈ bits, env.loc c = 0 ∨ env.loc c = 1 := by
    intro c hc
    refine bitGate_forces_bit env c (h (bitGate c) ?_)
    simp only [amountRangeGates, List.mem_append]
    exact Or.inl (List.mem_map_of_mem hc)
  rw [heq]; exact recomposeVal_nonneg env.loc bits hbits

/-- **THE UNSAT (anti-gate) TOOTH — a negative amount is rejected.** If `loc amtCol < 0`, then the
range gates CANNOT all hold (they would force `0 ≤ loc amtCol`). So the strengthened descriptor
genuinely REJECTS a witness violating the executor's `0 ≤ amt` gate — non-vacuity from the rejecting
side, the anti-ghost the brief requires. -/
theorem amountRangeGates_reject_negative (env : VmRowEnv) (amtCol : Nat) (bits : List Nat)
    (hneg : env.loc amtCol < 0) :
    ¬ (∀ g ∈ amountRangeGates amtCol bits, g.holdsVm env true true) := by
  intro h
  exact absurd (amountRangeGates_force_nonneg env amtCol bits h) (not_le.mpr hneg)

/-! ### §2.2 — the MINT amount-non-negative descriptor + the strengthened full-state soundness.

Concrete instantiation for mint: amount column `prmCol param.AMOUNT` (mint reads its credit from the
transfer `AMOUNT` column), bit-decomposed over 30 fresh aux witness columns `mintAmtBits` (the
`[0,2^30)` bound the `ranges` field declared but `satisfiedVm` ignored). The new descriptor APPENDS
`amountRangeGates` to `mintVmDescriptorWide`'s constraints; everything else (width, hash-sites, the
13/14 + 8-root commitment) is byte-identical, so the FULL-state soundness `mint_runnable_full_sound`
lifts unchanged AND now additionally pins `0 ≤ amt`. -/

/-- 30 fresh aux witness columns (`106..135`) for the mint amount's bit decomposition. Disjoint from
every column the wide mint descriptor's gates/sites touch: selectors `0..53`, state blocks `54..89`,
the referenced params `AMOUNT=68`/(mint reads only AMOUNT), the `STATE_INTER` aux `98..100`, and the
`system_roots` digest carriers `186/187`. So a satisfying wide row can freely carry the bits. -/
def mintAmtBits : List Nat := (List.range 30).map (· + 106)

/-- **`mintVmDescriptorNonNeg`** — `mintVmDescriptorWide` with the amount-non-negativity gadget APPENDED
to its constraints (the `0 ≤ amt` in-circuit conjunct the executor's `recKMint` gate demands, now
enforced in the runnable circuit). Width / hash-sites / PI / ranges are UNCHANGED, so it binds the same
FULL 17-field post-state, PLUS non-negativity. -/
def mintVmDescriptorNonNeg : EffectVmDescriptor :=
  { mintVmDescriptorWide with
    constraints := mintVmDescriptorWide.constraints
      ++ amountRangeGates (prmCol AMOUNT) mintAmtBits }

/-- The non-negative mint descriptor's hash-sites ARE the wide descriptor's (only constraints grew). -/
theorem mintNonNeg_sites_eq :
    mintVmDescriptorNonNeg.hashSites = mintVmDescriptorWide.hashSites := rfl

/-- A row satisfying `mintVmDescriptorNonNeg` also satisfies `mintVmDescriptorWide` (its constraints
are a prefix sub-list; the hash-sites are identical). The bridge that lets the strengthened theorem
reuse `mint_runnable_full_sound` for the 17-field clause and add `0 ≤ amt` from the new gates. -/
theorem mintNonNeg_sat_implies_wide (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hsat : satisfiedVm hash mintVmDescriptorNonNeg env true true) :
    satisfiedVm hash mintVmDescriptorWide env true true := by
  obtain ⟨hcs, hsites⟩ := hsat
  refine ⟨fun c hc => hcs c ?_, hsites⟩
  -- the wide constraints are the LEFT summand of the non-neg constraint list.
  simp only [mintVmDescriptorNonNeg, List.mem_append]
  exact Or.inl hc

/-- **`mint_runnable_full_sound_nonneg` — THE STRENGTHENED DELIVERABLE.** A row satisfying the
RUNNABLE `mintVmDescriptorNonNeg` (the wide mint circuit PLUS the amount-non-negativity gadget), under
the structured decode, pins the FULL 17-field declarative post-state (`CellMintSpec` + frozen roots)
AND `0 ≤ amt` — the executor's `recKMint` `0 ≤ amt` precondition, now an in-circuit conjunct rather
than an out-of-band hypothesis. So a light client verifying this proof can no longer accept a "negative
mint" (a covert burn). The 17-field clause routes through the unchanged `mint_runnable_full_sound`
(via `mintNonNeg_sat_implies_wide`); the non-negativity is `amountRangeGates_force_nonneg` decoded
through `RowEncodes`' `loc(AMOUNT) = amt`. -/
theorem mint_runnable_full_sound_nonneg (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsMintRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash mintVmDescriptorNonNeg env true true) :
    CellMintSpec pre amt post ∧ postRoots = preRoots ∧ 0 ≤ amt := by
  -- 17-field clause: from the wide descriptor (the new gates are extra; sites unchanged).
  obtain ⟨hspec, hpost⟩ :=
    mint_runnable_full_sound amt preRoots hash env pre post postRoots hrow henc hroots
      (mintNonNeg_sat_implies_wide hash env hsat)
  -- 0 ≤ amt: the range gates force `0 ≤ loc(AMOUNT)`, and `RowEncodes` ties `loc(AMOUNT) = amt`.
  have hrange : ∀ g ∈ amountRangeGates (prmCol AMOUNT) mintAmtBits, g.holdsVm env true true := by
    intro g hg
    exact hsat.1 g (by simp only [mintVmDescriptorNonNeg, List.mem_append]; exact Or.inr hg)
  have hamtcol : 0 ≤ env.loc (prmCol AMOUNT) :=
    amountRangeGates_force_nonneg env (prmCol AMOUNT) mintAmtBits hrange
  -- `henc`'s AMOUNT clause: `env.loc (prmCol param.AMOUNT) = amt`.
  have hamt : env.loc (prmCol AMOUNT) = amt := by
    obtain ⟨_, _, _, _, _, _, _, hpAmt, _⟩ := henc
    exact hpAmt
  exact ⟨hspec, hpost, hamt ▸ hamtcol⟩

#assert_axioms mint_runnable_full_sound_nonneg

/-- **The Argus-welded strengthened deliverable** (named under the Argus effect namespace so the
coherence anchor carries the `0 ≤ amt` in-circuit conjunct alongside the full-state soundness). -/
theorem mint_full_state_on_runnable_nonneg (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsMintRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash mintVmDescriptorNonNeg env true true) :
    CellMintSpec pre amt post ∧ postRoots = preRoots ∧ 0 ≤ amt :=
  mint_runnable_full_sound_nonneg amt preRoots hash env pre post postRoots hrow henc hroots hsat

#assert_axioms mint_full_state_on_runnable_nonneg

/-! ### §2.3 — NON-VACUITY of the gadget (witness TRUE + witness FALSE), gate-level.

The gate-level bar the per-cell `EffectVmEmitMint` non-vacuity uses (a concrete satisfying row + a
concrete rejected forgery), now for the amount-non-negativity gadget: a Boolean-bit assignment whose
recomposition is a concrete non-negative amount SATISFIES the range gates (TRUE), and a row whose
amount column is negative is REJECTED (FALSE). -/

/-- A concrete row carrying `amt = 30 = 0b11110` over `mintAmtBits` (bits 1,2,3,4 set ⇒ 2+4+8+16=30),
the amount column `prmCol AMOUNT` = 30. -/
def amt30Row : VmRowEnv where
  loc := fun v =>
    if v = prmCol AMOUNT then 30
    else if v = 106 + 1 then 1
    else if v = 106 + 2 then 1
    else if v = 106 + 3 then 1
    else if v = 106 + 4 then 1
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- Every bit column of `amt30Row` is Boolean (`0` or `1`) — the `loc` is an `if`-chain returning only
`0`/`1` on columns `≥ 106` (the amount column `68` is the only `30`, and `68 ∉ mintAmtBits`). -/
theorem amt30Row_bits_boolean (c : Nat) (hc : c ∈ mintAmtBits) :
    amt30Row.loc c = 0 ∨ amt30Row.loc c = 1 := by
  simp only [mintAmtBits, List.mem_map, List.mem_range] at hc
  obtain ⟨i, _, rfl⟩ := hc
  -- `i + 106 ≠ 68` (the amount column), so the first branch is false; the rest give 0 or 1.
  have hne : i + 106 ≠ prmCol AMOUNT := by
    simp only [prmCol, Dregg2.Circuit.Emit.EffectVmEmit.PARAM_BASE,
      Dregg2.Circuit.Emit.EffectVmEmit.STATE_BEFORE_BASE,
      Dregg2.Circuit.Emit.EffectVmEmit.STATE_SIZE, Dregg2.Circuit.Emit.EffectVmEmit.NUM_EFFECTS,
      AMOUNT]
    omega
  simp only [amt30Row, hne, if_false]
  by_cases h1 : i + 106 = 106 + 1 <;> by_cases h2 : i + 106 = 106 + 2 <;>
    by_cases h3 : i + 106 = 106 + 3 <;> by_cases h4 : i + 106 = 106 + 4 <;>
    simp only [h1, h2, h3, h4, if_true, if_false] <;> tauto

/-- **NON-VACUITY (witness TRUE).** The honest `amt = 30` bit assignment SATISFIES every range gate —
each `mintAmtBits` column is `0` or `1`, and their base-2 recomposition is `30 = loc(AMOUNT)`. So the
gadget is INHABITED (not vacuously unsatisfiable). -/
theorem amt30Row_satisfies_range :
    ∀ g ∈ amountRangeGates (prmCol AMOUNT) mintAmtBits, g.holdsVm amt30Row true true := by
  intro g hg
  simp only [amountRangeGates, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with ⟨c, hc, rfl⟩ | rfl
  · -- a bit gate `bitGate c`: column value is 0 or 1, so `c·(c−1) = 0`.
    simp only [bitGate, VmConstraint.holdsVm, EmittedExpr.eval]
    rcases amt30Row_bits_boolean c hc with h | h <;> rw [h] <;> ring
  · -- the recomposition gate: `loc(AMOUNT) − Σ 2^i·bᵢ = 30 − 30 = 0`.
    simp only [VmConstraint.holdsVm, EmittedExpr.eval, recomposeExpr_eval, mintAmtBits, amt30Row,
      prmCol, Dregg2.Circuit.Emit.EffectVmEmit.PARAM_BASE,
      Dregg2.Circuit.Emit.EffectVmEmit.STATE_BEFORE_BASE,
      Dregg2.Circuit.Emit.EffectVmEmit.STATE_SIZE, Dregg2.Circuit.Emit.EffectVmEmit.NUM_EFFECTS]
    decide

/-- A FORGED row: the amount column carries a NEGATIVE amount (`−5`). -/
def amtNegRow : VmRowEnv where
  loc := fun v => if v = prmCol AMOUNT then -5 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness FALSE / the anti-gate tooth, concrete).** A row whose amount column is
`−5 < 0` is REJECTED by the range gadget — no Boolean bit assignment recomposes to a negative integer.
So the strengthened mint descriptor genuinely FAILS a witness violating `0 ≤ amt` (the executor's gate
is now enforced in-circuit, not merely declared). -/
theorem amtNegRow_rejected :
    ¬ (∀ g ∈ amountRangeGates (prmCol AMOUNT) mintAmtBits, g.holdsVm amtNegRow true true) := by
  apply amountRangeGates_reject_negative
  simp only [amtNegRow, prmCol, Dregg2.Circuit.Emit.EffectVmEmit.PARAM_BASE,
    Dregg2.Circuit.Emit.EffectVmEmit.STATE_BEFORE_BASE, Dregg2.Circuit.Emit.EffectVmEmit.STATE_SIZE,
    Dregg2.Circuit.Emit.EffectVmEmit.NUM_EFFECTS]
  norm_num

#assert_axioms amt30Row_satisfies_range
#assert_axioms amtNegRow_rejected

#assert_axioms amountRangeGates_force_nonneg
#assert_axioms amountRangeGates_reject_negative

end Dregg2.Circuit.Argus.Effects.Mint
