/-
# Dregg2.Exec.HandlerFloors — the UNIFORM FLOOR-OBLIGATION SURFACE (P0 of the
proof-carrying handler-executor campaign).

`EffectHandler` (`Dregg2/Exec/Handler.lean`) captures exactly THREE floors as typed proof fields
(`auth_gated` / `admission_gated` / `conserves`). The other six floors the campaign names —
reserved-field, caveat-admission, freshness/delegation-epoch, non-amplification, monotone-nonce,
index-bounds/membership — are enforced AD-HOC inside individual `step` functions. Where a handler's
`step` is *weaker* than `execFullA`'s arm, the corresponding `handler_refines_execFullA_*` theorem
carries the missing gate as a SIDE-HYPOTHESIS (`hnr` / `hcav` / `hmono` / `hb` / `hmem` / the
epoch-residual). **Those side-hypotheses are the silent-gate holes**: the handler type-checks WITHOUT
the gate, and the gate only re-appears as something the *caller* must supply.

This module is the P0 beachhead — the structural retirement of that hole class. It defines a single
uniform **`FloorObligation`** surface: a named floor is a `Prop`-valued post/pre-condition the
handler's `step` must satisfy on every commit, bundled WITH the proof that it does. Promoting a floor
to a `FloorObligation` makes the missing-gate UNREPRESENTABLE — the floor becomes a typing condition,
exactly as `auth_gated`/`conserves` already are.

## The key design risk — and how this settles it

The research flagged (RESEARCH-handler-executor.md §5) that the floors are NOT uniform: authority and
admission are `St → Args → Bool` GATES, but `conserves`, `freshness`, and `non-amplification` are
RELATIONAL — predicates over the post-state / over delegation edges, not single Bool gates. A naive
"add three more Bool fields" under-models the relational floors.

**The settle: make the floor `Prop`-valued, not `Bool`-valued.** `FloorObligation.floor : St → Args →
Prop` is general enough to express BOTH:

  * a Bool gate `g : St → Args → Bool` lifts via `g s a = true` (the `ofBoolGate` constructor below),
    so the existing auth/admission/reserved-field floors fit WITHOUT change of meaning; AND

  * a relational floor (e.g. `fieldOf "nonce" (cell target) < n`, or `granted ⊆ held`) IS ALREADY a
    `Prop` — it drops straight in, no Bool encoding required.

So the surface is genuinely uniform over both floor kinds. We SETTLE this by proving BOTH a Bool-gate
floor (reserved-field, §3) AND a relational floor (monotone-nonce, §4) inhabit the SAME
`FloorObligation` structure, each discharged from the EXISTING just-banked gate lemmas
(`stateStepDev_notReserved`, `incrementNonceStep_advances`) — no new gate logic, only the uniform
re-presentation.

Pure, additive: imports the existing `EffectsState`/`StateSupply` infra, edits no existing file.
Verified: `lake build Dregg2.Exec.HandlerFloors`.
-/
import Dregg2.Exec.Handler
import Dregg2.Exec.EffectsState
import Dregg2.Exec.Handlers.StateSupply
import Dregg2.Tactics

namespace Dregg2.Exec.HandlerFloors

open Dregg2.Exec
open Dregg2.Exec.EffectsState (reservedField stateStepDev stateStepDev_notReserved
  incrementNonceStep incrementNonceStep_advances fieldOf)

/-! ## §1 — The uniform `FloorObligation` surface (`Prop`-valued).

`FloorObligation St Args step` is parameterized by the handler's transition `step : St → Args →
Option St` (so the floor is ABOUT that step). It bundles:

  * `floor : St → Args → Prop` — the named precondition/postcondition the commit must satisfy; AND
  * `gated : ∀ s a s', step s a = some s' → floor s a` — the PROOF that every commit satisfies it.

A `FloorObligation` literal is ILL-TYPED until `gated` is discharged against `step`. So registering a
handler with its floor obligation is the typing condition that retires the silent-gate hole: a handler
whose `step` could commit while VIOLATING the floor cannot inhabit this structure.

`St` is left general (`RecChainedState` for the field-write/nonce family, `RecordKernelState` for the
authority family) so ONE surface covers every handler. -/
structure FloorObligation (St : Type) (Args : Type) (step : St → Args → Option St) where
  /-- The named floor: a `Prop` the commit's pre-state + args must satisfy. `Prop`-valued (NOT
  `Bool`) so it uniformly expresses Bool gates (`g s a = true`) AND relational floors. -/
  floor : St → Args → Prop
  /-- OBLIGATION: every commit satisfies the floor. Discharging this is the typing condition that
  makes the missing gate unrepresentable. -/
  gated : ∀ s a s', step s a = some s' → floor s a

/-- **`ofBoolGate` — the Bool-gate floors fit the uniform surface.** A handler's existing
`St → Args → Bool` gate `gate` (the shape of `auth`/`admission`/`reservedField`), together with its
`*_gated` proof, becomes a `FloorObligation` by reading the floor as `gate s a = true`. This is the
witness that the THREE existing typed floors (`auth_gated`/`admission_gated`) and the Bool-shaped new
floors (reserved-field, index-bounds) all live on the SAME surface — no relational machinery needed
for them, but they share the structure with the floors that DO need it. -/
def ofBoolGate {St Args : Type} {step : St → Args → Option St}
    (gate : St → Args → Bool)
    (gated : ∀ s a s', step s a = some s' → gate s a = true) :
    FloorObligation St Args step where
  floor := fun s a => gate s a = true
  gated := gated

/-- A committed step DISCHARGES its floor obligation — the projection every downstream refinement
reuses to SHED its side-hypothesis. Where today `handler_refines_execFullA_setField` takes `hnr`/`hcav`
as hypotheses, once the handler carries the matching `FloorObligation` this lemma SUPPLIES them from
the commit itself — the side-hyp becomes a derived fact, not a caller obligation. -/
theorem FloorObligation.discharge {St Args : Type} {step : St → Args → Option St}
    (fo : FloorObligation St Args step) {s : St} {a : Args} {s' : St}
    (h : step s a = some s') : fo.floor s a :=
  fo.gated s a s' h

/-! ## §2 — Floor argument records (the args the two PoC floors range over).

These mirror the existing `StateWriteArgs` shape (a developer field write) but expose the `(actor,
target, field, value)` the floor predicates read. Reusing concrete records keeps the floors
`#assert_axioms`-clean and ties them to the live `stateStepDev`/`incrementNonceStep` steps. -/

/-- Args for a developer `SetField` (the reserved-field floor ranges over `field`). -/
structure SetFieldArgs where
  /-- The actor performing the write. -/
  actor : CellId
  /-- The cell whose field is written. -/
  target : CellId
  /-- The named field written (the reserved-field floor forbids the four protocol slots). -/
  field : FieldName
  /-- The scalar value written. -/
  value : Int

/-- Args for a monotone-nonce write (the floor relates the stored nonce to the new value). -/
structure NonceArgs where
  /-- The actor bumping the nonce. -/
  actor : CellId
  /-- The cell whose nonce advances. -/
  target : CellId
  /-- The new nonce value (must STRICTLY exceed the stored nonce). -/
  value : Int

/-! ## §3 — POC INSTANCE A (BOOL-GATE FLOOR): reserved-field, over the developer `SetField`.

The reserved-field floor is the just-banked `c4f4f0012` fix: a developer `SetField` may NOT write a
protocol-managed slot (`nonce`/`permissions`/`verification_key`/`program`) — only its dedicated effect
owns it. This is a BOOL gate (`reservedField f = false`). It WAS carried as the `hnr` side-hyp of
`handler_refines_execFullA_setField` — now SHED (§P1): the `.setFieldA` handler's own step carries it.

We give the developer-write step `stateStepDev` a `FloorObligation` whose floor is `reservedField
a.field = false`, discharged from `stateStepDev_notReserved` (the just-banked lemma proving a committed
developer write touched a NON-reserved slot). The floor is Bool-shaped — but we present it directly as
the `Prop` `reservedField a.field = false` (a `Bool = false` equation IS a `Prop`), demonstrating the
Bool floors live on the uniform surface natively. -/

/-- The developer-write step lifted to `SetFieldArgs` (the field-write the reserved gate guards). -/
def setFieldStep (s : RecChainedState) (a : SetFieldArgs) : Option RecChainedState :=
  stateStepDev s a.field a.actor a.target a.value

/-- **`reservedFieldFloor` — the BOOL-GATE floor as a `FloorObligation`.** Floor: the written slot is
NOT a protocol-managed slot (`reservedField a.field = false`). Discharged on every commit by
`stateStepDev_notReserved` — the just-banked reserved gate is now a TYPED obligation, not a refinement
side-hypothesis. A `stateStepDev` variant that wrote a reserved slot could not inhabit this. -/
def reservedFieldFloor : FloorObligation RecChainedState SetFieldArgs setFieldStep where
  floor := fun _ a => reservedField a.field = false
  gated := by
    intro s a s' h
    exact stateStepDev_notReserved h

/-! ## §4 — POC INSTANCE B (RELATIONAL FLOOR): monotone-nonce, over `incrementNonceStep`.

The monotone-nonce floor is the just-banked nonce-no-replay fix: `IncrementNonce` may only ADVANCE the
nonce (`old < n`), never reset it (a reset is the same replay vector as `setField "nonce"`). This is
RELATIONAL — it relates the PRE-STATE's stored nonce (`fieldOf "nonce" (s.kernel.cell target)`) to the
new value `n`. It is NOT a `St → Args → Bool` gate over args alone; it reads the state. It is carried
TODAY as the `hmono` side-hyp of `handler_refines_execFullA_stateWrite`.

This is the floor the research flagged as the genuine risk — and it inhabits the SAME `FloorObligation`
structure as the Bool floor above, because `floor` is `Prop`-valued. The floor IS the relation
`fieldOf "nonce" (cell target) < value`, discharged from `incrementNonceStep_advances`. No Bool
encoding; the relation drops straight in. -/

/-- The monotone-nonce step lifted to `NonceArgs`. -/
def nonceStep (s : RecChainedState) (a : NonceArgs) : Option RecChainedState :=
  incrementNonceStep s a.actor a.target a.value

/-- **`nonceMonotoneFloor` — the RELATIONAL floor as a `FloorObligation`.** Floor: the new nonce
STRICTLY exceeds the stored nonce (`fieldOf "nonce" (cell target) < value`) — a relation over the
pre-state, NOT a Bool gate. Discharged on every commit by `incrementNonceStep_advances`. THIS is the
proof that the uniform `Prop`-valued surface handles the relational floor kind — the research's main
design risk, settled affirmatively: the relational floor needs NO different treatment, it is just a
different `floor` body in the SAME structure. -/
def nonceMonotoneFloor : FloorObligation RecChainedState NonceArgs nonceStep where
  floor := fun s a => fieldOf "nonce" (s.kernel.cell a.target) < a.value
  gated := by
    intro s a s' h
    exact incrementNonceStep_advances h

/-! ## §5 — TEETH: the floors BITE (a violating step does not commit), and DISCHARGE works.

The methodology pin: a step that would VIOLATE the floor returns `none`, so `gated` is never asked to
prove something false — the floor is load-bearing, not vacuous. And `discharge` recovers the floor fact
from any commit (the shape that lets a refinement shed its side-hyp). -/

/-- A developer write of a RESERVED slot does NOT commit — so the reserved floor never lies (it bites
fail-closed, the just-banked teeth, now witnessed AT the obligation surface). -/
theorem reservedFieldFloor_bites (s : RecChainedState) (a : SetFieldArgs)
    (h : reservedField a.field = true) : setFieldStep s a = none := by
  unfold setFieldStep
  exact EffectsState.stateStepDev_reserved_fails s a.field a.actor a.target a.value h

/-- A non-advancing nonce write does NOT commit — the relational floor bites fail-closed. -/
theorem nonceMonotoneFloor_bites (s : RecChainedState) (a : NonceArgs)
    (h : ¬ fieldOf "nonce" (s.kernel.cell a.target) < a.value) : nonceStep s a = none := by
  unfold nonceStep
  exact EffectsState.incrementNonceStep_nonincreasing_fails s a.actor a.target a.value h

/-- **`reservedFieldFloor` DISCHARGES** — a committed developer write SUPPLIES `reservedField = false`
WITHOUT a side-hypothesis. This is the `hnr` that `handler_refines_execFullA_setField` USED to take
as input (now SHED, §P1), produced by the commit via the obligation. -/
theorem reservedFieldFloor_discharges {s s' : RecChainedState} {a : SetFieldArgs}
    (h : setFieldStep s a = some s') : reservedField a.field = false :=
  reservedFieldFloor.discharge h

/-- **`nonceMonotoneFloor` DISCHARGES** — a committed nonce write SUPPLIES the monotone relation
WITHOUT a side-hypothesis. This is the `hmono` that `handler_refines_execFullA_stateWrite` USED to
take as input (now SHED, §P1), produced by the commit via the obligation (the relational floor shed too). -/
theorem nonceMonotoneFloor_discharges {s s' : RecChainedState} {a : NonceArgs}
    (h : nonceStep s a = some s') : fieldOf "nonce" (s.kernel.cell a.target) < a.value :=
  nonceMonotoneFloor.discharge h

/-! ## §6 — Axiom-hygiene pins (the floor surface + both instances rest only on the kernel triple). -/

#assert_axioms FloorObligation.discharge
#assert_axioms reservedFieldFloor
#assert_axioms nonceMonotoneFloor
#assert_axioms reservedFieldFloor_discharges
#assert_axioms nonceMonotoneFloor_discharges
#assert_axioms reservedFieldFloor_bites
#assert_axioms nonceMonotoneFloor_bites

/-! ## §P1 — DONE (the field-write family migrated; THREE side-hyps SHED). § P2 — THE NEXT FAMILY.

**P1 LANDED.** The developer `SetField` (`.setFieldA`) and the dedicated `IncrementNonce`
(`.incrementNonceA`) now route through their OWN floor-carrying handlers (`Handlers/StateSupply.lean`,
`setFieldDevH` / `incrementNonceDevH`) whose `step` ITSELF fail-closes on the floor — the reserved
protocol slot + slot caveat for `.setFieldA` (`setFieldDevStep`), the strict-advance for
`.incrementNonceA` (`incrementNonceDevStep`). The refinement theorems read the floor OFF the commit
(`setFieldDevStep_notReserved` / `_caveatsAdmit`, `incrementNonceDevStep_advances`) instead of taking
it as a caller hypothesis, so:

  * `handler_refines_execFullA_setField` SHED `hnr` (`reservedField f = false`) AND `hcav`
    (`caveatsAdmit … = true`); and
  * `handler_refines_execFullA_stateWrite` (=`…_incrementNonce`) SHED `hmono` (the monotone relation).

The generic `stateWriteH` STAYS for the protocol-slot writers (`setPermissions`/`setVK`/`setProgram`/…)
— each OWNS its (reserved) slot, so the reserved gate must NOT apply to them. The teeth
(`Handlers/StateSupply.lean §TEETH-9a/9b/9c`) confirm the floors BITE through the migrated handlers (a
`SetField` of `"nonce"`/`"permissions"`/… and a non-advancing `IncrementNonce` are all REJECTED) and
do NOT over-reject (a non-reserved write and a strict advance commit).

**P2 — the next floor families** (the obligation table, `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`):
  * **authority non-amplification** — the `delegateAtten`/`introduce` family: a granted cap-set must be
    `⊆` the held set (a relational floor, like monotone-nonce). Carried as the descent side-condition.
  * **lifecycle freshness / delegation-epoch** — the `refreshDelegationA` residual (the
    `delegationEpochAt` re-stamp `handler_refines_execFullA_refreshDelegation` carries as a named
    kernel residual): route through an epoch-stamping step so the residual is internal.
  * **forest-path / index-membership floors** — the `noteSpend`/heap-membership family: the spend's
    non-membership + the heap leaf-index bound. -/

end Dregg2.Exec.HandlerFloors
