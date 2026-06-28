/-
# Dregg2.Deos.CapacitySatisfaction — the capacity gate is SATISFIED over the BOUND rotated state
blocks, so a PURE light client witnesses the gate HELD over the committed transition.

This is **PIECE 2 of the VK epoch** (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6, the
genuinely-VK-affecting *in-AIR gate-satisfaction weld*). `CapacityCarrier.lean` (PIECE 1) discharged
the COVERAGE half for a pure light client: the manifest a light client checks is FORCED by the
caveat-commit PI (the entry cannot be OMITTED). This module discharges the SATISFACTION half: the
gate's slot reads, welded IN-AIR to the rotated BEFORE/AFTER state-block FIELD columns (the `r3..r10`
limbs the deployed weld carries), are FORCED by the before/after state commits a pure light client
binds in the ~124-bit wide commit — so a satisfying proof witnesses the gate held over the COMMITTED
state, not re-evaluated against caller-supplied `initial_fields`/`final_fields` views.

## The gap this closes (the deep one)

The deployed off-AIR re-evaluation (`circuit/src/effect_vm/verify.rs::verify_slot_caveat_manifest`,
the `SETTLE_ESCROW` arm) reads `initial_fields[slot]` / `final_fields[slot]` — **caller-supplied**
8-felt slot views. A pure light client (commitments only) does NOT bind those arrays: it binds the
wide commit, which absorbs the rotated state-block columns. So today satisfaction is witnessed only
by a verifier WITH the committed-state opening (the cap-membership posture — `SealedEscrow.lean` §6
`settle_gate_root_bound` transports the verdict across equal HEAP roots, but the caller must still
hold the heap). The genuinely-VK-affecting fix is to read the gate's slots from the rotated
state-block field columns IN-AIR (a new selector-gated constraint = new VK bytes), so a satisfying
proof forces the gate over the columns the wide commit binds. This module is the Lean rung for
*that*: the satisfaction verdict is FIXED by the before/after state commits (the field-level analog
of `settle_gate_root_bound`, over the columns the in-AIR weld actually touches and the wide commit
directly absorbs), and composed with PIECE 1's coverage it gives the full pure-light-client capacity
witness.

## The model — faithful to the deployed weld

* A rotated state block is its limb vector (`cells_root · r0..r23 · …`), `Block := List ℤ`. The
  field-slot `k` rides limb `4 + k` (the `r3..r10 ↔ fields[0..8]` weld, `trace_rotated.rs`: `r3` is
  pre-limb index 4). The gate reads `fieldAt b k`, EXACTLY the column the deployed weld pins and the
  Rust off-AIR arm reads as `fields[k]`.
* The block's `stateCommit` is the sponge over its limbs — the chained `wireCommitR` digest the wide
  commit absorbs, modeled under the ONE `Poseidon2SpongeCR` floor (the SAME collision-resistance the
  cap/heap roots and the `caveatCommit` carry; the chain binds its limbs under it, as
  `EffectVmEmitRotationCaveat.caveatCommit_binds` does for the caveat manifest).
* `SettleFieldGate` is the EXACT shape of the deployed `SETTLE_ESCROW` arm: both legs `Deposited` in
  the BEFORE block fields, both `Consumed` in the AFTER block fields (reusing `SealedEscrow`'s status
  codes). The in-AIR weld is the assertion that a satisfying proof has this gate true over the bound
  block columns.

## What is and is NOT witnessed yet (no overclaim)

This rung proves the SOUNDNESS the in-AIR weld *would* carry: the satisfaction verdict is forced by
the committed state commits a pure light client binds. It is NOT itself the deployed AIR constraint —
the in-AIR gate is built STAGED in `circuit/src/effect_vm/satisfaction_weld.rs` (the
`VmConstraint::Gate` constraints over the rotated field columns) and is NOT yet emitted into a
committed welded descriptor / VK, and NOT flipped onto the live path. So a pure light client does NOT
yet witness satisfaction in production — only once the staged welded descriptor is emitted, its VK
committed, and the live path routed through it. The honest remaining distance + the gated-flip plan
are in `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6.

## Axiom hygiene

`#assert_all_clean` at the close. The only named hypothesis is `Poseidon2SpongeCR` (the ONE
collision-resistance floor — the same one `CapacityCarrier` and the heap/cap roots carry); never an
axiom; no core edit.
-/
import Dregg2.Deos.CapacityCarrier

namespace Dregg2.Deos.CapacitySatisfaction

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Deos.SealedEscrow (stEmpty stDeposited stConsumed)
open Dregg2.Deos.ConstraintBinding (Tag tagSettleEscrow covers)
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat (RotCaveatEntry RotCaveatManifest caveatCommit)
open Dregg2.Deos.CapacityCarrier (toConstraintManifest carrier_manifest_forced)
open Dregg2.Substrate.Heap (refSponge)

set_option autoImplicit false

/-! ## §1 — the rotated state block + the field projection (the columns the in-AIR weld reads). -/

/-- A rotated state block, modeled as its limb vector (`cells_root · r0..r23 · cap_root · …`). The
in-AIR satisfaction weld reads the FIELD columns of the BEFORE/AFTER blocks; the chained
`wireCommitR` → `stateCommit` absorbs the whole vector into the wide commit. -/
abbrev Block := List ℤ

/-- The in-block offset of field-slot `k`: the `r3..r10 ↔ fields[0..8]` weld. `r3` is pre-limb index
4 (`cells_root = 0`, `r0 = 1`, `r1 = 2`, `r2 = 3`, `r3 = 4`), so `fields[k]` rides limb `4 + k`
(`trace_rotated.rs`). -/
def fieldOffset (k : Nat) : Nat := 4 + k

/-- Read field-slot `k` from a block — the rotated `r{3+k}` column the deployed weld pins, EXACTLY
the felt the Rust off-AIR `SETTLE_ESCROW` arm reads as `fields[k]`. -/
def fieldAt (b : Block) (k : Nat) : ℤ := b.getD (fieldOffset k) 0

/-- The block's committed `stateCommit`: the sponge over its limb vector — the chained `wireCommitR`
digest a pure light client binds in the ~124-bit wide commit. Modeled under the ONE
`Poseidon2SpongeCR` floor (the chain binds its limbs under it). -/
def stateCommit (hash : List ℤ → ℤ) (b : Block) : ℤ := hash b

/-- **THE FIELD-BINDING FLOOR (reuse).** Equal state commits ⟹ equal field-at-slot — a forger cannot
present a block with a forged field column while keeping the honest state commit. DIRECT consequence
of `Poseidon2SpongeCR` over the block limbs (the field-level analog of `Heap.root_binds_get`); no new
floor. -/
theorem fieldAt_bound_in_commit (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {b b' : Block} (hc : stateCommit hash b = stateCommit hash b') (k : Nat) :
    fieldAt b k = fieldAt b' k := by
  have hbb : b = b' := hCR b b' hc
  rw [hbb]

/-! ## §2 — the sealed-escrow satisfaction gate over the ROTATED FIELD COLUMNS.

`SettleFieldGate` is the EXACT shape of the deployed `verify.rs` `SETTLE_ESCROW` arm (both legs
`Deposited` before, both `Consumed` after), read from the BEFORE/AFTER block FIELD columns the in-AIR
weld pins — the rotated-leg twin of `SealedEscrow.SettleGate` (which reads heap slots). -/

/-- **The in-AIR settlement gate.** Both escrow legs (`legA`/`legB` field-slot indices) read
`Deposited` in the BEFORE block fields and `Consumed` in the AFTER block fields. The Lean image of the
deployed `SETTLE_ESCROW` off-AIR arm, now over the rotated state-block columns the wide commit binds. -/
def SettleFieldGate (before after : Block) (legA legB : Nat) : Prop :=
  fieldAt before legA = stDeposited ∧
  fieldAt before legB = stDeposited ∧
  fieldAt after  legA = stConsumed ∧
  fieldAt after  legB = stConsumed

instance (before after : Block) (legA legB : Nat) : Decidable (SettleFieldGate before after legA legB) := by
  unfold SettleFieldGate; infer_instance

/-! ## §3 — THE TEETH: partial / phantom settle, both polarities. -/

/-- **THE NO-PARTIAL-SETTLE TOOTH.** A forged "partial settle" — leg B left `Deposited` in the AFTER
block fields (B walks away un-swapped) — FAILS the in-AIR gate: it requires B `Consumed`, and
`Deposited ≠ Consumed`. The half-open trade is INEXPRESSIBLE in-AIR. The rotated-field face of
`SealedEscrow.partial_settle_rejected`. -/
theorem partial_settle_field_rejected (before after : Block) (legA legB : Nat)
    (hpartial : fieldAt after legB = stDeposited) :
    ¬ SettleFieldGate before after legA legB := by
  intro hgate
  have hB := hgate.2.2.2
  rw [hpartial] at hB
  exact (by decide : (stDeposited : ℤ) ≠ stConsumed) hB

/-- **THE NO-PHANTOM-SETTLE TOOTH.** A settle whose BEFORE leg-A field was never `Deposited` (no
genuine conforming lock) FAILS the in-AIR gate: it requires `Deposited` before. A consumption cannot
be conjured from a leg that never locked. -/
theorem phantom_settle_field_rejected (before after : Block) (legA legB : Nat) (s : ℤ)
    (hbefore : fieldAt before legA = s) (hne : s ≠ stDeposited) :
    ¬ SettleFieldGate before after legA legB := by
  intro hgate
  have hA := hgate.1
  rw [hbefore] at hA
  exact hne hA

/-! ## §4 — THE SATISFACTION KEYSTONE: the gate verdict is FIXED by the committed state commits.

A pure light client binds the BEFORE/AFTER state commits (the rotated `wireCommitR` digests folded
into the wide commit). The in-AIR gate constraint (a satisfying proof has `SettleFieldGate` true over
the witnessed block columns) then forces the gate over the COMMITTED state: ANY block pair a forger
presents matching the same committed state commits has the SAME verdict — so a forger cannot pass the
in-AIR gate over FAKE field columns while the genuine committed state fails it. This is the in-AIR
analog of `SealedEscrow.settle_gate_root_bound`, over the FIELD columns the weld touches and the
state-commit the wide commit DIRECTLY absorbs (vs the heap root the caller had to hold). -/

/-- **THE SATISFACTION KEYSTONE (pure light client).** Equal before/after state commits ⟹ the same
gate verdict. The forger's presented (committed-equal) state satisfies the gate iff the genuine one
does. REUSE of `fieldAt_bound_in_commit`; the one named `Poseidon2SpongeCR` floor. -/
theorem satisfaction_witnessed (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {before after before' after' : Block} (legA legB : Nat)
    (hb : stateCommit hash before = stateCommit hash before')
    (ha : stateCommit hash after = stateCommit hash after')
    (hgate : SettleFieldGate before after legA legB) :
    SettleFieldGate before' after' legA legB := by
  obtain ⟨h1, h2, h3, h4⟩ := hgate
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← fieldAt_bound_in_commit hash hCR hb legA]; exact h1
  · rw [← fieldAt_bound_in_commit hash hCR hb legB]; exact h2
  · rw [← fieldAt_bound_in_commit hash hCR ha legA]; exact h3
  · rw [← fieldAt_bound_in_commit hash hCR ha legB]; exact h4

/-- **THE ANTI-GHOST (satisfaction).** A forged block whose committed field differs from the honest
one CANNOT keep the honest state commit — it must publish a different commit (where the satisfaction
keystone's binding bites). The contrapositive of `fieldAt_bound_in_commit`. -/
theorem forged_field_moves_commit (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {b b' : Block} (k : Nat) (hne : fieldAt b k ≠ fieldAt b' k) :
    stateCommit hash b ≠ stateCommit hash b' :=
  fun hc => hne (fieldAt_bound_in_commit hash hCR hc k)

/-! ## §5 — THE PURE-LIGHT-CLIENT CAPACITY WITNESS: coverage (PIECE 1) ∧ satisfaction (PIECE 2).

Composed: a pure light client binding, in the ONE wide commit, BOTH the caveat-commit PI (forces the
manifest = the committed one — `CapacityCarrier`) AND the before/after state commits (force the gate
verdict — §4) witnesses BOTH that the capacity entry is PRESENT (coverage, cannot be omitted) AND
that the gate HELD over the committed state (satisfaction, cannot be passed over fake fields) — WITHOUT
the caller holding any state opening. The cap-membership posture is fully discharged. -/

/-- **THE CAPACITY KEYSTONE (pure light client).** Given the carrier binding (the published caveat
manifest matches the committed one) and the satisfaction binding (the published before/after state
commits match the committed ones), a forger's published proof BOTH covers the sealed-escrow tag
(coverage — the entry cannot be dropped) AND has the genuine committed state satisfy the in-AIR gate
(satisfaction — the gate cannot be faked over alternate field columns). The full pure-light-client
sealed-escrow witness: omission AND a hollow/faked gate are both impossible. -/
theorem capacity_witnessed_pure_lightclient (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (gate : RotCaveatEntry → Bool)
    -- COVERAGE side (PIECE 1, the carrier): the published manifest matches the committed one's commit.
    {mBound mPub : RotCaveatManifest}
    (hccommit : caveatCommit hash mPub = caveatCommit hash mBound)
    (hcov : covers (toConstraintManifest gate mBound) tagSettleEscrow)
    -- SATISFACTION side (PIECE 2, this rung): the published state commits match the committed ones.
    {before after before' after' : Block} (legA legB : Nat)
    (hb : stateCommit hash before = stateCommit hash before')
    (ha : stateCommit hash after = stateCommit hash after')
    (hgate : SettleFieldGate before after legA legB) :
    covers (toConstraintManifest gate mPub) tagSettleEscrow ∧
      SettleFieldGate before' after' legA legB := by
  refine ⟨?_, ?_⟩
  · rw [carrier_manifest_forced hash hCR gate hccommit]; exact hcov
  · exact satisfaction_witnessed hash hCR legA legB hb ha hgate

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the in-AIR gate BITES, both polarities.

Computed on the reference sponge so the honest settle passes the gate AND a forged field MOVES the
committed state commit (a pure light client binding it detects the fake). Legs in slots 0/1. -/

section Witnesses

/-- An honest BEFORE block: both leg slots (0, 1 → limbs 4, 5) read `Deposited`. -/
private def honestBefore : Block := [0, 0, 0, 0, stDeposited, stDeposited, 0, 0, 0, 0, 0, 0]
/-- An honest AFTER block: both leg slots read `Consumed`. -/
private def honestAfter : Block := [0, 0, 0, 0, stConsumed, stConsumed, 0, 0, 0, 0, 0, 0]
/-- A forged PARTIAL after: leg A consumed, leg B still deposited (the half-open trade). -/
private def partialAfter : Block := [0, 0, 0, 0, stConsumed, stDeposited, 0, 0, 0, 0, 0, 0]

-- The field projection reads the rotated `r3..r10` columns (limbs 4..11).
#guard fieldAt honestBefore 0 == stDeposited
#guard fieldAt honestBefore 1 == stDeposited
#guard fieldAt honestAfter 0 == stConsumed
#guard fieldAt honestAfter 1 == stConsumed

-- HONEST: the genuine settle transition passes the in-AIR gate.
#guard decide (SettleFieldGate honestBefore honestAfter 0 1)
-- NO-PARTIAL: leg B left deposited fails the gate.
#guard !decide (SettleFieldGate honestBefore partialAfter 0 1)
-- NO-PHANTOM: an un-deposited before (leg A empty) fails the gate.
private def phantomBefore : Block := [0, 0, 0, 0, stEmpty, stDeposited, 0, 0, 0, 0, 0, 0]
#guard !decide (SettleFieldGate phantomBefore honestAfter 0 1)

-- THE SATISFACTION BINDING BITES: forging leg B's after field (Consumed → Deposited) MOVES the
-- committed state commit, so a pure light client binding it detects the fake (it cannot match the
-- honest commit). Computed on the reference sponge.
#guard stateCommit refSponge honestAfter != stateCommit refSponge partialAfter
-- ...and the honest recompute is stable (the positive polarity).
#guard stateCommit refSponge honestAfter == stateCommit refSponge honestAfter

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  fieldAt_bound_in_commit,
  partial_settle_field_rejected,
  phantom_settle_field_rejected,
  satisfaction_witnessed,
  forged_field_moves_commit,
  capacity_witnessed_pure_lightclient
]

end Dregg2.Deos.CapacitySatisfaction
