/-
# Dregg2.Deos.Hatchery — the abstraction-mint house-capacity: a user-defined verified KIND's declared
invariant IS enforced, forever, and its attestation is REAL (bound to a machine-checked contract).

`sdk/src/hatchery_mint.rs` is the Rust house-capacity: the kernel ships a *fixed* vocabulary of cell
shapes, and the Hatchery (`HATCHERY.md`) opens it to an **OPEN vocabulary of verified KINDS**. A
`MintedKind = FactoryDescriptor + Invariant + HpresProof`: an author declares a new cell-KIND with its
own invariant (`BalanceNeverBelow`, `MonotoneField`, …), the invariant is baked perpetual into every
child's `state_constraints`, and the executor enforces it on every state-modifying turn. Enforcement is
NOT a new mint-layer gate — it is the SAME `CellProgram::evaluate_with_meta` every settlement / storage
/ governance cell faces: `MintedKind::evaluate_transition` delegates straight to it, and a violating
turn returns `Err(ProgramError::ConstraintViolated{..})` — a real refusal a re-executing validator
reproduces bit-for-bit. The forge-detector `attest_membership` rejects membership-without-conformance
(`ForgeRejection::ProgramMissingInvariant`): a cell that claims the kind but installs a program omitting
the invariant constraints is rejected.

This module is the Lean RUNG for that capacity, in the shape the MEMBRANE / DERIVED-CELL set: name the
invariant, prove it **by reuse** of an already-proven discipline (here the per-step constraint check
plus the Hatchery's `Verify.Contract.CellContract` carry skeleton), exhibit both-polarity `#guard`
witnesses, `#assert_all_clean`, and wire the Rust to it (`sdk/src/hatchery_mint.rs::tests::
invariant_matches_lean_rung`). It is the LAST of the six house capacities — completing the set.

## What is proven — and what it REUSES (no hatchery-local mathematics)

The hatchery's enforcement is the per-turn constraint gate (`evalStep`, the Lean image of the
`FieldGte` / `Monotonic` arms of `evaluate_with_meta`), and the "holds forever" crown is the SAME carry
skeleton the Hatchery's `Dregg2.Verify.Contract.CellContract` mechanizes (`Inv` + `step_ob` ⟹ `forever`,
`Verify/Contract.lean:84`/`110`). The rung proves:

  * `evalStep_admits_iff_*` (THE GATE IS THE INVARIANT) — a turn is admitted by the kind's constraint
    iff it satisfies the kind's declared invariant on the new state. The `evaluate_with_meta` gate and
    the author's declared property are the SAME predicate.

  * `step_preserves` (THE SINGLE-STEP INVARIANT, the **hpres**) — an admitted step preserves the kind's
    carried invariant: `Inv old → evalStep = ok → Inv new`. The author's ONE real obligation
    (`CellContract.step_ob`), discharged uniformly for every minted kind. For balance it is the gate
    itself; for the monotone field it is `le_trans` carrying the baseline forward.

  * **`CellContract.forever` / `invariant_forever` (THE REUSE KEYSTONE)** — `step_ob` lifted to the
    unbounded trajectory: under EVERY schedule of admitted turns, the invariant holds at every index.
    The executor-image of `Verify.Contract.CellContract.forever` (= `livingCellA_carries`): a minted
    cell carries its invariant for life, against every adversarial schedule. No new induction — the
    Hatchery's carry skeleton, instantiated.

  * `Attested` + `attested_enforces_forever` (THE REAL-ATTESTATION BINDING) — `HpresProof::Attested` is
    bound to a machine-checked `CellContract`: the `Attested` structure CANNOT be constructed without a
    real `CellContract` (which itself cannot be constructed without a real `step_ob` proof term) AND the
    pointwise equalities tying that contract to THIS kind's invariant. So an attestation is a *proved
    forever-crown*, not a trusted assertion — `attested_enforces_forever` cashes it out into the
    unbounded carry. `binds_pending_is_false` and `forged_attestation_rejected` are the negative teeth:
    a `Pending` kind carries no crown, and an attestation whose certified invariant is NOT the kind's is
    rejected (the content-hash mismatch, decidably).

  * `Conforms` + `program_missing_invariant_rejected` (THE FORGE-DETECTOR) — the Lean image of
    `ForgeRejection::ProgramMissingInvariant`: a claimed program that does not carry the kind's invariant
    constraint is rejected; the empty program is a forge for any invariant-bearing kind.

  * `violating_*_rejected` (THE VIOLATING TURN IS REFUSED) — a turn breaking the invariant (a balance
    below the floor, a field stepping backward) makes `evalStep` return `constraintViolated`, the Lean
    image of the `Err(ConstraintViolated)` the kernel program returns.

This is NOT new mathematics: the gate is an ordinary constraint check, and the "forever" is the proven
`CellContract` carry. The hatchery is a NAMING of "a minted kind's declared constraint, enforced by the
real `evaluate_with_meta` step and carried by the real `CellContract` skeleton" — exactly as the
membrane is a naming of iterated kernel attenuation and the derived cell of a committed-heap binding.

## The light-client crown (BUILT) + the named residual

This rung grounds the EXECUTOR-witnessed invariant: a re-executing validator running the cell's
program refuses a violating turn, and a proved `CellContract` certifies the forever-crown. The
companion refutation `Dregg2/Circuit/HatcheryBackingAttack.lean` shows that crown was, as DEPLOYED,
vacuous for a pure LIGHT CLIENT: the `contract_hash` of `HpresProof::Attested` is only STORED, read by
no circuit constraint, so the deployed AIR admits a mint whose forever-crown verifies nothing
(`deployed_admits_unbacked_hatchery`). The REPAIR is BUILT — the per-turn FOLD over a re-proved
contract-attestation leaf (`circuit-prove::hatchery_leaf_adapter::prove_hatchery_leaf`) connected to
the mint leg's claimed `contract_hash` teeth via `prove_hatchery_binding_node_segmented`: the
`(contract_hash, invariant_digest)` tuple is bound IN the recursion tree the light client folds, and a
`contract_hash` no attestation leaf backs is UNSAT (the tooth
`forged_contract_hash_is_rejected_by_the_fold`). So `HpresProof::Attested` is now a forever-crown
backed by the FOLD, not the executor/Lean carry alone. Two named residuals remain (NOT vacuity): the
deployed mint leg must DUAL-EXPOSE its `contract_hash` teeth (the VK-affecting "big-bang" descriptor
PI-exposure piece named in `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`, hatchery row — the same
lane the cap-root reshape drives), and full in-AIR re-verification that the `contract_hash` resolves to
a verifying `CellContract` proof term stays the named off-AIR digest-of-attestation cost.

## Axiom hygiene

`#assert_all_clean` at the close — kernel-clean (`propext` / `Classical.choice` / `Quot.sound` only). NO
core edit; every gate is an ordinary constraint check and every carry is the `CellContract` skeleton's
own induction.
-/
import Dregg2.Tactics

namespace Dregg2.Deos.Hatchery

/-! ## §1 — the minted-kind state, invariant, and the per-turn constraint gate.

A cell's state is its field slots (the Lean image of `CellState`'s fields); a kind's invariant lowers
to ONE perpetual `StateConstraint` the executor checks on every turn (`Invariant::constraints`). The
gate `evalStep` is the Lean image of the `FieldGte` / `Monotonic` arms of `CellProgram::
evaluate_with_meta`: a conforming turn returns `ok`, a violating one `constraintViolated`. -/

/-- A cell's field slots — the Lean image of `CellState`'s fields. `slotV s i` reads slot `i` (0 off
the end), the integer a `StateConstraint` reads. -/
abbrev St := List ℤ

/-- Read field slot `i` of a state (0 if unset) — the Lean image of `CellState::field`. -/
def slotV (s : St) (i : ℕ) : ℤ := s.getD i 0

/-- The structured invariant an author declares for a new kind — the Lean image of
`sdk/src/hatchery_mint.rs::Invariant`. -/
inductive Invariant
  /-- "balance slot `slot` never below `floor`" — `StateConstraint::FieldGte`. -/
  | balanceNeverBelow (slot : ℕ) (floor : ℤ)
  /-- "field slot `slot` only ever moves forward" — `StateConstraint::Monotonic`. -/
  | monotoneField (slot : ℕ)
deriving DecidableEq, Repr

/-- The perpetual `StateConstraint` a kind's invariant lowers to (the Lean image of
`Invariant::constraints`) — the program-for-life baked onto every child. -/
inductive Constraint
  | fieldGte (slot : ℕ) (floor : ℤ)
  | monotonic (slot : ℕ)
deriving DecidableEq, Repr

/-- Lower a declared invariant to the constraint the executor enforces (`Invariant::constraints`). -/
def Invariant.constraint : Invariant → Constraint
  | .balanceNeverBelow slot floor => .fieldGte slot floor
  | .monotoneField slot => .monotonic slot

/-- The result of the per-turn program gate — the Lean image of `Result<(), ProgramError>`. -/
inductive Result
  | ok
  | constraintViolated
deriving DecidableEq, Repr

/-- **`evalStep inv new old`** — the per-turn constraint gate, the Lean image of the `FieldGte` /
`Monotonic` arms of `CellProgram::evaluate_with_meta`. `FieldGte` checks the NEW state regardless of
history; `Monotonic` checks `new ≥ old`, with the `old = none` creation case admitted (the first write
establishes the slot). A conforming turn returns `ok`; a violating one `constraintViolated`. -/
def evalStep : Invariant → St → Option St → Result
  | .balanceNeverBelow slot floor, new, _ =>
      if floor ≤ slotV new slot then .ok else .constraintViolated
  | .monotoneField _, _, none => .ok
  | .monotoneField slot, new, some old =>
      if slotV old slot ≤ slotV new slot then .ok else .constraintViolated

/-- **`Invariant.holds inv base s`** — the carried state predicate a minted cell of this kind upholds.
For a balance kind it is the floor bound on the slot; for a monotone kind it is "the slot never dropped
below its value at the cell's start `base`" — the `logAppendOnly`/`subsetNullifiers` carry shape
(`Verify/Contract.lean`), the property the `Monotonic` constraint preserves step by step. -/
def Invariant.holds : Invariant → St → St → Prop
  | .balanceNeverBelow slot floor, _base, s => floor ≤ slotV s slot
  | .monotoneField slot, base, s => slotV base slot ≤ slotV s slot

instance instDecidableHolds (inv : Invariant) (base s : St) : Decidable (inv.holds base s) := by
  cases inv with
  | balanceNeverBelow slot floor => unfold Invariant.holds; infer_instance
  | monotoneField slot => unfold Invariant.holds; infer_instance

/-! ## §2 — the gate IS the invariant, and an admitted step preserves it (the **hpres**).

The `evaluate_with_meta` gate and the author's declared property are the SAME predicate on the new
state (for balance) / the SAME monotone relation (for the field). `step_preserves` is the author's ONE
real obligation (`CellContract.step_ob`): an admitted turn keeps the carried invariant. -/

/-- The balance gate admits a turn IFF the new state satisfies the floor invariant — the gate and the
declared property are the same predicate. -/
theorem evalStep_admits_iff_balance (slot : ℕ) (floor : ℤ) (new : St) (old : Option St) :
    evalStep (.balanceNeverBelow slot floor) new old = .ok ↔ floor ≤ slotV new slot := by
  simp only [evalStep]
  by_cases h : floor ≤ slotV new slot <;> simp [h]

/-- The monotone gate admits a transition IFF the field did not step backward. -/
theorem evalStep_admits_iff_monotone (slot : ℕ) (new old : St) :
    evalStep (.monotoneField slot) new (some old) = .ok ↔ slotV old slot ≤ slotV new slot := by
  simp only [evalStep]
  by_cases h : slotV old slot ≤ slotV new slot <;> simp [h]

/-- **THE SINGLE-STEP INVARIANT (the hpres).** An admitted step preserves the kind's carried invariant:
`Inv old → evalStep = ok → Inv new`. This IS `CellContract.step_ob`, discharged uniformly for every
minted kind — for balance it is the gate itself; for the monotone field it carries the baseline forward
by `le_trans`. The author supplies nothing bespoke: the constraint check IS the proof. -/
theorem step_preserves (inv : Invariant) (base new old : St)
    (hold : inv.holds base old) (hstep : evalStep inv new (some old) = .ok) :
    inv.holds base new := by
  cases inv with
  | balanceNeverBelow slot floor =>
      exact (evalStep_admits_iff_balance slot floor new (some old)).1 hstep
  | monotoneField slot =>
      have hmono := (evalStep_admits_iff_monotone slot new old).1 hstep
      exact le_trans hold hmono

/-! ## §3 — the `CellContract` carry skeleton (REUSE of `Verify.Contract.CellContract`).

The Hatchery's first-class invariant object is `Inv` + `step_ob` ⟹ `forever` (`Verify/Contract.lean`).
Here is its executor image: a `CellContract` over cell states, whose `forever` carries the invariant
along an arbitrary schedule of admitted turns. A minted kind's canonical contract is `Invariant.contract`,
discharged by `step_preserves`. -/

/-- **`CellContract`** — the executor image of `Verify.Contract.CellContract`: a verified invariant on
cell states, packaged as a value. `guard` is the per-turn gate it reasons about; `Inv` the carried
predicate; `step_ob` the proof an admitted turn preserves it. It CANNOT be constructed without a real
`step_ob` proof term — that is what makes an attestation real. -/
structure CellContract where
  guard : St → Option St → Result
  Inv : St → Prop
  step_ob : ∀ new old, Inv old → guard new (some old) = .ok → Inv new

/-- **THE FOREVER CARRY (the reuse keystone).** `step_ob` lifted to the unbounded trajectory: from the
invariant at the start and EVERY turn admitted by the gate, the invariant holds at every index. The
executor image of `Verify.Contract.CellContract.forever` (= `livingCellA_carries`): a minted cell
carries its invariant for life, against every adversarial schedule. -/
theorem CellContract.forever (C : CellContract) (traj : ℕ → St)
    (h0 : C.Inv (traj 0))
    (hadm : ∀ n, C.guard (traj (n + 1)) (some (traj n)) = .ok) :
    ∀ n, C.Inv (traj n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact C.step_ob (traj (k + 1)) (traj k) ih (hadm k)

/-- A minted kind's canonical contract: the gate is the kind's `evalStep`, the carried invariant the
kind's `holds`, and `step_ob` is `step_preserves`. The contract a properly-attested kind binds. -/
def Invariant.contract (inv : Invariant) (base : St) : CellContract where
  guard new old := evalStep inv new old
  Inv s := inv.holds base s
  step_ob new old hold hstep := step_preserves inv base new old hold hstep

/-- **`invariant_forever`** — the minted-kind crown stated directly: under every schedule of admitted
turns, the kind's declared invariant holds at every index of the cell's life. `Invariant.contract`'s
`forever`, named. -/
theorem invariant_forever (inv : Invariant) (base : St) (traj : ℕ → St)
    (h0 : inv.holds base (traj 0))
    (hadm : ∀ n, evalStep inv (traj (n + 1)) (some (traj n)) = .ok) :
    ∀ n, inv.holds base (traj n) :=
  (inv.contract base).forever traj h0 hadm

/-! ## §4 — THE REAL-ATTESTATION BINDING: `HpresProof::Attested` ⟺ a machine-checked contract.

The crux of the hatchery. `HpresProof::Attested { contract_hash }` must be bound to a PROVED
`CellContract`, not a trusted flag. `Attested` bundles the certified invariant with a real
`CellContract` AND the pointwise equalities tying that contract to the certified invariant — so it
cannot be forged: building it requires the contract (hence a real `step_ob`). `binds` is the
content-hash check (decidable): an attestation binds to a kind iff it certifies the kind's invariant. -/

/-- **`Attested`** — a machine-checked attestation: a certified `Invariant`, a baseline, the proved
`CellContract` discharging it, and the pointwise bridge tying the contract to the certified invariant.
The Lean image of a `HpresProof::Attested` whose `contract_hash` resolves to a real
`Verify.Contract.CellContract`. It carries a real `step_ob` (inside `C`); it cannot be a bare flag. -/
structure Attested where
  cert : Invariant
  base : St
  C : CellContract
  hguard : ∀ new old, C.guard new old = evalStep cert new old
  hinv : ∀ s, C.Inv s ↔ cert.holds base s

/-- `HpresProof` — the Hatchery attestation slot (`sdk/src/hatchery_mint.rs::HpresProof`). `pending`
relies on the runtime gate alone; `attested` carries the machine-checked forever-crown. -/
inductive HpresProof
  | pending
  | attested (a : Attested)

/-- **`HpresProof.binds inv base`** — the content-hash check: an attestation binds to a kind iff it is
`attested` by a contract certifying THIS kind's invariant (decidably, by `cert = inv`). `pending`
carries no crown; an attestation for a different invariant does not bind. -/
def HpresProof.binds (inv : Invariant) (base : St) : HpresProof → Prop
  | .pending => False
  | .attested a => a.cert = inv ∧ a.base = base

/-- **The canonical attestation of a kind** — built from `Invariant.contract`. Witnesses that
attestation is achievable for every well-formed invariant (non-vacuity of the crown): the contract's
gate and invariant are definitionally the kind's, so `hguard`/`hinv` are `rfl`. -/
def attest (inv : Invariant) (base : St) : Attested where
  cert := inv
  base := base
  C := inv.contract base
  hguard _ _ := rfl
  hinv _ := Iff.rfl

/-- The canonical attestation binds to its own kind (the honest round-trip: minting then attesting). -/
theorem attest_binds (inv : Invariant) (base : St) :
    (HpresProof.attested (attest inv base)).binds inv base :=
  ⟨rfl, rfl⟩

/-- **THE REAL-ATTESTATION CROWN.** An attestation that binds to a kind cashes out into the unbounded
forever-carry: under every schedule of turns admitted by the kind's gate, the kind's declared invariant
holds at every index. So `HpresProof::Attested` is a *proved* forever-crown — the contract's real
`step_ob` (inside `a.C`) drives `CellContract.forever`, translated through `hguard`/`hinv`. Not a
trusted assertion. -/
theorem attested_enforces_forever (inv : Invariant) (base : St) (a : Attested)
    (hbind : (HpresProof.attested a).binds inv base)
    (traj : ℕ → St)
    (h0 : inv.holds base (traj 0))
    (hadm : ∀ n, evalStep inv (traj (n + 1)) (some (traj n)) = .ok) :
    ∀ n, inv.holds base (traj n) := by
  obtain ⟨hcert, hbase⟩ := hbind
  subst hcert; subst hbase
  -- run the carried contract `a.C` along the trajectory, bridging gate/inv by `hguard`/`hinv`.
  have hC0 : a.C.Inv (traj 0) := (a.hinv (traj 0)).2 h0
  have hCadm : ∀ n, a.C.guard (traj (n + 1)) (some (traj n)) = .ok := by
    intro n; rw [a.hguard]; exact hadm n
  intro n
  exact (a.hinv (traj n)).1 (a.C.forever traj hC0 hCadm n)

/-- **NEGATIVE TOOTH — a `Pending` kind carries no crown.** `pending` does not bind: the
machine-checked forever-crown is genuinely absent (honestly, not laundered). -/
theorem binds_pending_is_false (inv : Invariant) (base : St) :
    ¬ HpresProof.pending.binds inv base :=
  id

/-- **NEGATIVE TOOTH — a forged attestation is rejected.** An attestation whose certified invariant is
NOT the kind's does not bind to the kind — the content-hash mismatch, decidably. So claiming `Attested`
with a contract for a *different* (e.g. weaker) invariant cannot pass as this kind's crown. -/
theorem forged_attestation_rejected (inv : Invariant) (base : St) (a : Attested)
    (hforge : a.cert ≠ inv) :
    ¬ (HpresProof.attested a).binds inv base := by
  intro hbind; exact hforge hbind.1

/-! ## §5 — THE FORGE-DETECTOR: membership-without-conformance is rejected.

The Lean image of `MintedKind::attest_membership` / `ForgeRejection::ProgramMissingInvariant`: a cell
claiming a kind must install a program carrying the kind's invariant constraint. A program that omits
it — or an empty program — is a forge. -/

/-- **`Conforms inv program`** — the claimed program carries the kind's invariant constraint
(`MintedKind::attest_membership`'s containment leg). A stricter superset (extra caveats) still
conforms; dropping the invariant does not. -/
def Conforms (inv : Invariant) (program : List Constraint) : Prop :=
  inv.constraint ∈ program

instance (inv : Invariant) (program : List Constraint) : Decidable (Conforms inv program) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- A cell installing exactly the kind's constraint conforms (the honest member). -/
theorem own_program_conforms (inv : Invariant) : Conforms inv [inv.constraint] := by
  simp [Conforms]

/-- A cell adding extra caveats while still carrying the invariant conforms (a stricter superset). -/
theorem superset_conforms (inv : Invariant) (extra : List Constraint) :
    Conforms inv (inv.constraint :: extra) := by
  simp [Conforms]

/-- **THE FORGE TOOTH (`ProgramMissingInvariant`).** A claimed program that does not carry the kind's
invariant constraint is rejected — membership-without-conformance is a forge. -/
theorem program_missing_invariant_rejected (inv : Invariant) (program : List Constraint)
    (hmiss : inv.constraint ∉ program) : ¬ Conforms inv program :=
  hmiss

/-- The empty program is a forge for any invariant-bearing kind (it carries no constraint). -/
theorem empty_program_is_forge (inv : Invariant) : ¬ Conforms inv [] := by
  simp [Conforms]

/-! ## §6 — THE VIOLATING TURN IS REFUSED — the `Err(ConstraintViolated)` the kernel returns. -/

/-- A balance turn dropping the slot below the floor is refused (`ConstraintViolated`). -/
theorem violating_balance_rejected (slot : ℕ) (floor : ℤ) (new old : St)
    (h : ¬ floor ≤ slotV new slot) :
    evalStep (.balanceNeverBelow slot floor) new (some old) = .constraintViolated := by
  simp only [evalStep, if_neg h]

/-- A monotone turn stepping the field backward is refused (`ConstraintViolated`). -/
theorem violating_monotone_rejected (slot : ℕ) (new old : St)
    (h : ¬ slotV old slot ≤ slotV new slot) :
    evalStep (.monotoneField slot) new (some old) = .constraintViolated := by
  simp only [evalStep, if_neg h]

/-! ## §7 — NON-VACUITY TEETH (`#guard`): the kind's invariant BITES, both polarities. -/

section Witnesses

/-- A balance kind: slot 0 never below floor 50 (`sdk` `balance_violating_turn_is_refused`). -/
private def balInv : Invariant := .balanceNeverBelow 0 50
/-- A monotone kind: slot 1 never decreases (`sdk` `monotone_*`). -/
private def monInv : Invariant := .monotoneField 1

-- THE GATE: a conforming balance (slot0 = 100 ≥ 50) is admitted; a violating one (slot0 = 10) refused.
#guard evalStep balInv [100] (some [100]) == Result.ok
#guard evalStep balInv [10] (some [100]) == Result.constraintViolated
-- THE GATE: a forward monotone step (5 → 9) admitted; a backward one (9 → 4) refused.
#guard evalStep monInv [0, 9] (some [0, 5]) == Result.ok
#guard evalStep monInv [0, 4] (some [0, 9]) == Result.constraintViolated
-- creation (no old) is admitted for a monotone field — the first write establishes the slot.
#guard evalStep monInv [0, 7] none == Result.ok

-- THE INVARIANT predicate, both polarities (balance floor 50, monotone baseline [0,5]).
#guard decide (balInv.holds [] [100])
#guard !decide (balInv.holds [] [10])
#guard decide (monInv.holds [0, 5] [0, 9])
#guard !decide (monInv.holds [0, 5] [0, 4])

-- THE FORGE-DETECTOR: the kind's own constraint conforms; a different / empty program is a forge.
#guard decide (Conforms balInv [balInv.constraint])
#guard decide (Conforms balInv [balInv.constraint, Constraint.monotonic 5])  -- stricter superset
#guard !decide (Conforms balInv [Constraint.monotonic 0])                    -- wrong constraint
#guard !decide (Conforms balInv ([] : List Constraint))                      -- empty program

-- THE ATTESTATION: the canonical attestation binds to its kind; an attestation for a DIFFERENT
-- invariant does NOT bind to the balance kind (the content-hash mismatch is decidable).
#guard decide ((attest balInv []).cert = balInv)
#guard !decide ((attest monInv [0, 5]).cert = balInv)
#guard decide (balInv.constraint = Constraint.fieldGte 0 50)
#guard decide (monInv.constraint = Constraint.monotonic 1)
#guard !decide (balInv.constraint = monInv.constraint)

end Witnesses

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  evalStep_admits_iff_balance,
  evalStep_admits_iff_monotone,
  step_preserves,
  CellContract.forever,
  invariant_forever,
  attest_binds,
  attested_enforces_forever,
  binds_pending_is_false,
  forged_attestation_rejected,
  own_program_conforms,
  superset_conforms,
  program_missing_invariant_rejected,
  empty_program_is_forge,
  violating_balance_rejected,
  violating_monotone_rejected
]

end Dregg2.Deos.Hatchery
