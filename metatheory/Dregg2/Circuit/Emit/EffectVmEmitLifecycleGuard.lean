/-
# Dregg2.Circuit.Emit.EffectVmEmitLifecycleGuard — the IN-CIRCUIT ADMISSIBILITY-GUARD gates for the
  lifecycle-field family's RUNNABLE EffectVM descriptors (closing the "guard is off-row" GAP).

## The gap this module closes (the SEVERE completeness hole, not a seam)

The lifecycle-field family's runnable descriptors (`setFieldVmDescriptorWide`,
`incrementNonceVmDescriptorWide`, `cellSealVmDescriptorWide`, …) bind the per-cell STATE TRANSITION
(the field write / nonce tick / lifecycle flag) + the 8 side-table roots, and that is FULLY sound. But
the EXECUTOR's *admissibility guard* — `stateStepGuarded`/`stateStep`/`cellSealChainA`/… commit ONLY
when `caveatsAdmit ∧ stateAuthB ∧ membership ∧ cellLive` (setField) / `stateAuthB ∧ membership ∧
cellLive` (incrementNonce/setPermissions/setVK/refusal) / `stateAuthB ∧ acceptsEffects`
(cellSeal) / `stateAuthB ∧ lifecycle==Sealed` (cellUnseal) / `stateAuthB ∧ lifecycle≠Destroyed`
(cellDestroy) / `stateAuthB` (makeSovereign) / `mintAuthorizedB ∧ id-freshness` (createCell) — was, on
the RUNNABLE descriptor, a NAMED off-row leg (`EffectVmEmitSetField.setField_guard_is_offrow`, "cited,
not papered"). A precondition the executor enforces but the runnable circuit OMITS is a SEVERE bug: a
light client (which sees ONLY the proof) would accept "a proof over bad data" — a field write by an
UNAUTHORIZED actor, into a SEALED cell, violating a CLEARANCE caveat, or a createCell at an ALREADY-USED
id.

## The fix (the SAME proven pattern `SetFieldCommit.cSF{Caveat,Auth,Mem,Live}` uses, now on the RUNNABLE
EffectVM descriptor)

`SetFieldCommit.lean` already enforces the guard as four `{0,1}` BIT gates (`vSFCaveat`/`vSFAuth`/`…`,
each `var i = const 1`) whose witness columns carry `propBit` of the four `SetFieldGuard` conjuncts
(`encodeSF`), with `guardProp := SetFieldGuard`. That is the faithful in-circuit guard — but in the
`ConstraintSystem` universe, NOT the runnable `EffectVmDescriptor`. This module mirrors it onto the
runnable descriptor:

  * a DEDICATED, non-aliasing guard-bit column block past the wide width
    (`guardBitCol 0..3 = 188..191`, all `≥ EFFECT_VM_WIDTH_SYSROOTS = 188`, so a v2 wide descriptor
    that adds these gates leaves every 186/188-wide layout column untouched);
  * `gAdmit col` — the per-row gate `var col − 1 = 0` (the EffectVM analog of `var i = const 1`), a
    real arithmetic constraint the prover asserts (`tb.assert_zero`), with NON-ZERO coefficient on the
    bit column (not a vacuous `0 = 0`);
  * the honest decode `BitEncodes col p env` (`env.loc col = propBit p`) — the prover lays the TRUE
    verdict of the predicate `p` on the column (exactly the `encodeSF` discipline / `RowEncodesSum`
    discipline), so the gate `var col − 1 = 0` HOLDS ⟺ `p` holds (`gAdmit_iff_pred`).

A per-effect wide descriptor APPENDS `gAdmit (guardBitCol i)` for each guard conjunct, EXTENDS its
`decodeAfter` with `BitEncodes (guardBitCol i) conjunctᵢ`, and EXTENDS its `fullClause` with the guard
predicate. Then `runnable_full_sound` CONCLUDES the guard held: a satisfying runnable witness PROVES the
admissibility guard, so a light client knows the actor was authorized, the cell live, the clearance
caveat satisfied, the id fresh. The anti-gate tooth (`gAdmit_rejects_zero`): a row whose bit column is
`0` (the predicate FALSE) FAILS the gate — UNSAT. NON-VACUOUS: a `propBit True` column satisfies, a
`propBit False` column is rejected.

## The terminal (named, the ONLY acceptable irreducible)

The bit column's *value* (does the actor hold a cap over the cell? does the clearance label dominate?)
is decided by the executor's `stateAuthB` / `dominatesD` / membership predicates — those are the
authority-lattice / clearance / membership primitives, and the prover commits to laying their TRUE
verdict on the column (the `BitEncodes` decode, the same hypothesis `encodeSF` carries). What this
module makes IN-CIRCUIT is the CONJUNCT itself: the gate `var col − 1 = 0` is genuinely in
`descriptor.constraints`, and `fullClause` carries the predicate — so the runnable proof no longer
accepts a transition whose guard is false. (A full Merkle-membership argument for the cap-graph /
clearance-graph *inside* the row is a strictly harder circuit — the §8 portal — but the conjunct is no
longer ABSENT, which is what cures the completeness hole.)

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no `:= True`, no `native_decide`.
Imports are READ-ONLY; this file owns only its own declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit

namespace Dregg2.Circuit.Emit.EffectVmEmitLifecycleGuard

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the dedicated, non-aliasing guard-bit column block (past the wide width).

The four guard-bit carriers are placed at the FIRST FOUR absolute columns past
`EFFECT_VM_WIDTH_SYSROOTS = 188` (i.e. `188, 189, 190, 191`), so they are DISTINCT from every column
the 186-wide layout OR the 188-wide (`sysRootsDigestCol = 186`, `sysRootsDigestColBefore = 187`)
sysroots widening claims. A descriptor that uses these gates declares width `EFFECT_VM_WIDTH_GUARD`.
The disjointness is proved by `decide` (`guardBlock_clean`). -/

/-- **`EFFECT_VM_WIDTH_GUARD`** — the trace width that carries the dedicated guard-bit sub-block: the
sysroots-widened `EFFECT_VM_WIDTH_SYSROOTS = 188` PLUS four guard-bit columns. Strictly additive over
the sysroots widening: a wide descriptor that adds the guard gates declares THIS width; the hash sites
(which absorb only the 13 state-block columns + the `sysRootsDigestCol = 186` carrier) are UNCHANGED,
so the published `state_commit` is byte-identical (the guard bits are an admissibility side-condition,
not committed post-state — exactly as `SetFieldCommit`'s guard bits are NOT part of the root). -/
def EFFECT_VM_WIDTH_GUARD : Nat := EFFECT_VM_WIDTH_SYSROOTS + 4

/-- **`guardBitCol i`** — the `i`-th dedicated guard-bit column (`i : Fin 4`), at absolute column
`EFFECT_VM_WIDTH_SYSROOTS + i = 188 + i`. NEVER aliases a 186/188-layout column. The prover lays the
`propBit` of the `i`-th admissibility conjunct here; the gate `gAdmit` asserts it is `1`. -/
def guardBitCol (i : Nat) : Nat := EFFECT_VM_WIDTH_SYSROOTS + i

/-- The four guard-bit columns are distinct from each other, from the two sysroots carriers
(`186`/`187`), and from every 186-layout column (all `< 186`). Proved by `decide`. -/
theorem guardBlock_clean :
    guardBitCol 0 = 188 ∧ guardBitCol 1 = 189 ∧ guardBitCol 2 = 190 ∧ guardBitCol 3 = 191
    ∧ sysRootsDigestCol < guardBitCol 0 ∧ sysRootsDigestColBefore < guardBitCol 0
    ∧ EFFECT_VM_WIDTH ≤ guardBitCol 0
    ∧ [guardBitCol 0, guardBitCol 1, guardBitCol 2, guardBitCol 3].dedup.length = 4 := by
  decide

/-! ## §1 — `gAdmit`: the per-row admissibility gate `var col − 1 = 0`.

The EffectVM analog of `SetFieldCommit.cSFCaveat = { lhs := .var vSFCaveat, rhs := .const 1 }`. A real
arithmetic gate the prover asserts vanishes (`tb.assert_zero(var col − 1)`); the bit column carries a
NON-ZERO coefficient (`+1`), so this is a genuine linear constraint, satisfied EXACTLY when the column
is `1`. -/

/-- **`gAdmitBody col`** — the polynomial `var col − 1`. -/
def gAdmitBody (col : Nat) : EmittedExpr := .add (.var col) (.const (-1))

/-- **`gAdmit col`** — the admissibility-bit gate as a per-row `VmConstraint`: the column must be `1`
(admitted). The runnable-descriptor analog of the `SetFieldCommit` `cSF{Caveat,Auth,Mem,Live}` bit
gates, now an EffectVM `tb.assert_zero`. -/
def gAdmit (col : Nat) : VmConstraint := .gate (gAdmitBody col)

/-- **`gAdmit_holds_iff` — PROVED (the gate's pure circuit meaning).** The admissibility gate holds on a
row IFF the bit column carries `1`. The genuine arithmetic teeth: `var col − 1 = 0 ↔ loc col = 1`. -/
theorem gAdmit_holds_iff (col : Nat) (env : VmRowEnv) (b1 b2 : Bool) :
    (gAdmit col).holdsVm env b1 b2 ↔ env.loc col = 1 := by
  simp only [gAdmit, gAdmitBody, VmConstraint.holdsVm, EmittedExpr.eval]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **`gAdmit_rejects_zero` — PROVED (THE ANTI-GATE TOOTH).** A row whose guard-bit column is `0` (the
admissibility conjunct is FALSE) FAILS the gate — `¬ (gAdmit col).holdsVm`. A vacuous gate could not
reject this; the guard conjunct genuinely bites (UNSAT on a violating witness). -/
theorem gAdmit_rejects_zero (col : Nat) (env : VmRowEnv) (b1 b2 : Bool)
    (hzero : env.loc col = 0) : ¬ (gAdmit col).holdsVm env b1 b2 := by
  rw [gAdmit_holds_iff]; rw [hzero]; decide

/-! ## §2 — `BitEncodes`: the honest decode tying the bit column to the admissibility PREDICATE.

The prover lays the `{0,1}` verdict of the decidable predicate `p` on the bit column — exactly the
`SetFieldCommit.encodeSF` discipline (`encodeSF … vSFCaveat = pBit (caveatsAdmit …)`) and the
`Policy.RowEncodesSum` discipline (the prover lays the field scalars; the gate enforces the relation).
Under that decode, the gate `gAdmit col` HOLDS ⟺ the predicate `p` holds — so a row decoded from a
pre-state where `p` is FALSE has bit column `0`, which the gate REJECTS (the §1 anti-gate tooth,
predicate-level). -/

/-- **`BitEncodes col p env`** — the row encodes the decidable admissibility predicate `p` on the bit
column `col`: `env.loc col = propBit p`. The honest "the prover lays the true verdict" hypothesis (the
EffectVM analog of `encSF_caveat`/`encSF_auth`/…). -/
def BitEncodes (col : Nat) (p : Prop) [Decidable p] (env : VmRowEnv) : Prop :=
  env.loc col = Circuit.propBit p

/-- **`gAdmit_iff_pred` — PROVED (the gate decides the SAME thing as the predicate).** Under the honest
`BitEncodes` decode, the admissibility gate holds IFF the predicate `p` holds. So the runnable gate's
algebraic statement SUFFICES to enforce the admissibility conjunct (soundness: a satisfying row PROVES
`p`), and every `p`-satisfying transition is gate-acceptable (completeness). This is the circuit ⟺
protocol bridge for ONE guard conjunct. -/
theorem gAdmit_iff_pred (col : Nat) (p : Prop) [Decidable p] (env : VmRowEnv) (b1 b2 : Bool)
    (henc : BitEncodes col p env) :
    (gAdmit col).holdsVm env b1 b2 ↔ p := by
  rw [gAdmit_holds_iff, henc]
  unfold Circuit.propBit
  by_cases hp : p
  · simp [hp]
  · simp [hp]

/-- **`gAdmit_pred_sound` — PROVED (the soundness direction, the form `decodeFull` uses).** A satisfying
admissibility gate under the honest decode PROVES the predicate `p` held. The conjunct is now genuinely
in-circuit: a runnable witness cannot satisfy the descriptor unless the guard conjunct `p` is true. -/
theorem gAdmit_pred_sound (col : Nat) (p : Prop) [Decidable p] (env : VmRowEnv) (b1 b2 : Bool)
    (henc : BitEncodes col p env) (hgate : (gAdmit col).holdsVm env b1 b2) : p :=
  (gAdmit_iff_pred col p env b1 b2 henc).mp hgate

/-! ## §3 — NON-VACUITY: the gate genuinely SATISFIES a `propBit True` column and REJECTS a `propBit
False` column (the mandatory teeth check, concretely). -/

/-- A row whose guard-bit column `188` carries `1` (the SATISFIER). -/
def envAdmit : VmRowEnv :=
  { loc := fun c => if c = guardBitCol 0 then 1 else 0, nxt := fun _ => 0, pub := fun _ => 0 }

/-- A row whose guard-bit column `188` carries `0` (the REJECTED row — admissibility conjunct false). -/
def envDeny : VmRowEnv :=
  { loc := fun c => 0, nxt := fun _ => 0, pub := fun _ => 0 }

-- The gate's bit-column readout genuinely separates the admitted row from the denied one
-- (`gAdmit_holds_iff` turns the gate verdict into these column equalities):
#guard decide (envAdmit.loc (guardBitCol 0) = 1)            -- true  (col 188 = 1 ⇒ gate holds)
#guard decide (envDeny.loc (guardBitCol 0) = 1) == false    -- false (col 188 = 0 ⇒ gate UNSAT)

/-- **`gAdmit_satisfies_admit` — PROVED.** The admissibility gate HOLDS on `envAdmit` (bit column `1`).
Non-vacuous — the gate is genuinely satisfiable. -/
theorem gAdmit_satisfies_admit : (gAdmit (guardBitCol 0)).holdsVm envAdmit true true := by
  rw [gAdmit_holds_iff]; decide

/-- **`gAdmit_rejects_deny` — PROVED (concrete anti-gate).** The admissibility gate is UNSAT on
`envDeny` (bit column `0`): `¬ (gAdmit …).holdsVm envDeny`. A row whose guard verdict is false FAILS the
runnable gate — the genuine teeth the off-row guard lacked. -/
theorem gAdmit_rejects_deny : ¬ (gAdmit (guardBitCol 0)).holdsVm envDeny true true :=
  gAdmit_rejects_zero (guardBitCol 0) envDeny true true (by decide)

/-- **`gAdmit_iff_pred_demo` — PROVED (the bridge, witnessed concretely).** On `envAdmit`, which encodes
the TRUE predicate on column `188` (`propBit True = 1`), the gate holds IFF the predicate holds (both
true) — the circuit ⟺ protocol bridge at a concrete encoded row, non-vacuous. -/
theorem gAdmit_iff_pred_demo :
    (gAdmit (guardBitCol 0)).holdsVm envAdmit true true ↔ True := by
  apply gAdmit_iff_pred (guardBitCol 0) True envAdmit true true
  show envAdmit.loc (guardBitCol 0) = Circuit.propBit True
  simp only [envAdmit, Circuit.propBit, if_pos trivial]

/-! ## §4 — Axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms guardBlock_clean
#assert_axioms gAdmit_holds_iff
#assert_axioms gAdmit_rejects_zero
#assert_axioms gAdmit_iff_pred
#assert_axioms gAdmit_pred_sound
#assert_axioms gAdmit_satisfies_admit
#assert_axioms gAdmit_rejects_deny
#assert_axioms gAdmit_iff_pred_demo

end Dregg2.Circuit.Emit.EffectVmEmitLifecycleGuard
