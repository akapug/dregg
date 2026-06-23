/-
# Dregg2.Apps.CapSlotFactory — F3/W2: CAPS-IN-SLOTS + the R7 retrieval-epoch freshness rule.

THE CLAIM, DISCHARGED HERE (DREGG3 §6 R7): *the seal/swiss/sturdyref verb family
(`CreateSealPair`/`Seal`/`Unseal`/`ExportSturdyRef`/`EnlivenRef`/`DropRef`/`ValidateHandoff` over
the off-ledger `sealedBoxes` + `swiss` side-tables) is the CAPS-IN-SLOTS cell-program pattern: a
stored capability is a VALUE IN A SLOT carrying `(cap payload, grantor, stored_epoch)`, and every
LOAD+EXERCISE is a survivor-verb GRANT gated on RETRIEVAL-EPOCH FRESHNESS.* This module is the
land-before-kill leg for the F3 reduction (the same move `EscrowFactory`/`QueueFactory`/
`BridgeCell` made for their families).

## The reframe (the SAME move escrow/queue/bridge made)

In the verb world a sealed box / sturdy ref is a kernel side-table entry (`SealedBoxRecord` /
`SwissRecord`) with seven bespoke verbs. The cell-program rebuild does the OPPOSITE: **a stored
cap is a slot value** `CapSlot = (payload, grantor, storedEpoch)` minted by `storeCap` (the
store-side gate: the grantor must genuinely HOLD the payload — non-forgeability at store time)
and redeemed by `retrieveCap` (the load-side gate: the R7 freshness comparison, then a plain
survivor `grant`). The family maps:

  * `CreateSealPair` / `Seal`      → `storeCap` (park a HELD cap in a slot, epoch-stamped)
  * `Unseal` / `EnlivenRef`        → `retrieveCap` (freshness-gated grant to the bearer)
  * `ExportSturdyRef`              → `storeCap` (the slot IS the sturdy ref; unguessability is
                                      the §8 swiss-number portal, orthogonal to this gate)
  * `ValidateHandoff`              → `retrieveCap` to a THIRD party (the 3-vat recipient; the
                                      two-signature cert crypto is the §8 portal)
  * `DropRef`                      → dropping the slot VALUE (a cell-program field write; no
                                      kernel op needed — the slot owner forgets the value)

## THE R7 RULE (DREGG3 §6 R7 — a correctness COMPLETION, not just a reduction)

The investigation confirmed the gap is LIVE in dregg1: `apply_exercise_via_capability` +
`apply_unseal` perform NO epoch re-check — a sealed/stored capability SURVIVES its grantor's
revocation. R7 closes it: a slot records the grantor's `delegationEpoch` AT STORE TIME
(`storedEpoch`); at LOAD+EXERCISE the retrieval is REFUSED iff
`storedEpoch < current_epoch(grantor)`. Conservatively, ANY grantor epoch-bump (every faithful
`recKRevokeDelegationFull`) stales EVERY earlier-stored cap — sound; the holder's duty is to
re-store (refresh). Orthogonal to sturdyref `max_staleness` (both must pass).

## The two R7 keystones (DREGG3 names them; both PROVED here, axiom-clean)

  * `stored_cap_only_fresh_if_epoch_unrevoked` — a retrieval that COMMITS implies the grantor's
    epoch has NOT advanced past the stored epoch (the gate is real, fail-closed).
  * `no_forge_from_storage` — the storage round-trip confers NO authority beyond what the
    original grant conferred: the retrieved cap IS the stored cap, the stored cap was genuinely
    HELD by the grantor at store time, and no other holder's c-list moves. Non-forgeability
    extends across storage.

plus the revocation tooth `revoke_stales_stored_cap`: a faithful delegation-revoke on the
grantor REFUSES every slot stored at-or-under the pre-revoke epoch (the pale-ghost foil:
storage does not launder freshness).

## Non-vacuity

`kCS` is a concrete world (grantor 0 holds a read cap on cell 5). `#guard` witnesses: the store
COMMITS and stamps epoch 0; a FRESH retrieval COMMITS (the recipient genuinely gains the cap); a
retrieval AFTER the grantor's revoke (epoch bump) is REFUSED; an unheld payload cannot be stored
(no forging at the store mouth). No keystone vacuous.

NEW file only (the F3 lane's land-before-kill). Imports the epoch machinery (`Exec/AuthTurn`) +
the executor surface. Every keystone `#assert_axioms`-pinned.
-/
import Dregg2.Exec.AuthTurn
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.CapSlotFactory

open Dregg2.Exec
open Dregg2.Authority (Caps Cap Auth Label)

/-! ## §1 — The stored-cap SLOT. -/

/-- **`CapSlot`** — a capability stored in a slot (the caps-in-slots value): the `payload` cap
itself, the `grantor` who parked it, and the R7 `storedEpoch` — the grantor's `delegationEpoch`
captured AT STORE TIME (DREGG3 §6 R7: `CapabilityRef.stored_epoch` / `SealedBox.seal_epoch`). -/
structure CapSlot where
  /-- the stored capability — the REAL payload (a sealed box binds a SPECIFIC cap, not a flag). -/
  payload     : Cap
  /-- the cell that parked the cap (the sealer / exporter / delegator of record). -/
  grantor     : CellId
  /-- the grantor's `delegationEpoch` at store time — the R7 freshness stamp. -/
  storedEpoch : Nat
deriving DecidableEq, Repr

/-! ## §2 — STORE (epoch-stamped, held-gated) and RETRIEVE (freshness-gated grant). -/

/-- **`storeCap k grantor payload`** — park a cap in a slot. FAIL-CLOSED unless the grantor
genuinely HOLDS the payload in the CURRENT state (`payload ∈ k.caps grantor` — the same
held-bound `swissExportK`/`sealChainA` enforced; non-forgeability at the store mouth). The slot
is stamped with the grantor's CURRENT `delegationEpoch` (the R7 store-time capture). -/
def storeCap (k : RecordKernelState) (grantor : CellId) (payload : Cap) : Option CapSlot :=
  if payload ∈ k.caps grantor
  then some { payload := payload, grantor := grantor, storedEpoch := k.delegationEpoch grantor }
  else none

/-- **`slotFresh k slot`** — THE R7 GATE: the stored cap is fresh iff the grantor's CURRENT
epoch has not advanced past the stored stamp (`¬ stored_epoch < current_epoch(grantor)`).
Conservatively, ANY grantor epoch-bump stales every earlier-stored cap. -/
def slotFresh (k : RecordKernelState) (slot : CapSlot) : Bool :=
  decide (k.delegationEpoch slot.grantor ≤ slot.storedEpoch)

/-- **`retrieveCap k slot recipient`** — LOAD+EXERCISE a stored cap: REFUSED iff the slot is
stale (`storedEpoch < current_epoch(grantor)`, the R7 rule); on commit the stored cap is granted
to the `recipient` by the SURVIVOR grant verb (`Exec.grant`, the same c-list move
delegate/introduce use). Unseal, enliven, and handoff are all THIS operation (handoff with a
third-party recipient). -/
def retrieveCap (k : RecordKernelState) (slot : CapSlot) (recipient : CellId) :
    Option RecordKernelState :=
  if slotFresh k slot
  then some { k with caps := grant k.caps recipient slot.payload }
  else none

/-! ## §3 — The two R7 keystones (DREGG3 §6 R7 names them). -/

/-- **`stored_cap_only_fresh_if_epoch_unrevoked` — R7 keystone (a), PROVED.** A retrieval that
COMMITS implies the grantor's epoch has NOT advanced past the stored epoch: the freshness gate is
real and fail-closed. Contrapositive: any grantor epoch-bump after the store (every faithful
revoke bumps, `recKRevokeDelegationFull_bumps_parent_epoch`) makes EVERY later retrieval refuse.
A stored/sealed capability can no longer outlive its grantor's revocation. -/
theorem stored_cap_only_fresh_if_epoch_unrevoked {k k' : RecordKernelState} {slot : CapSlot}
    {recipient : CellId} (h : retrieveCap k slot recipient = some k') :
    k.delegationEpoch slot.grantor ≤ slot.storedEpoch := by
  unfold retrieveCap at h
  by_cases hf : slotFresh k slot
  · exact of_decide_eq_true hf
  · rw [if_neg hf] at h; exact absurd h (by simp)

/-- **`no_forge_from_storage` — R7 keystone (b), PROVED.** The storage ROUND-TRIP confers no
authority beyond what the original grant conferred:
  (i)   the stored payload was genuinely HELD by the grantor at store time;
  (ii)  the slot carries EXACTLY that payload (storage cannot swap/amplify it);
  (iii) the retrieval's entire effect is ONE grant of THAT payload to the recipient — every cap
        anyone holds afterwards was either already held, or IS the original stored cap landing
        in the recipient's slot. Non-forgeability extends across storage. -/
theorem no_forge_from_storage {k0 k k' : RecordKernelState} {grantor recipient : CellId}
    {payload : Cap} {slot : CapSlot}
    (hstore : storeCap k0 grantor payload = some slot)
    (hret : retrieveCap k slot recipient = some k') :
    payload ∈ k0.caps grantor ∧ slot.payload = payload ∧
      (∀ x c, c ∈ k'.caps x → c ∈ k.caps x ∨ (x = recipient ∧ c = payload)) := by
  unfold storeCap at hstore
  by_cases hheld : payload ∈ k0.caps grantor
  · rw [if_pos hheld] at hstore
    have hslot : slot.payload = payload := by
      cases hstore; rfl
    refine ⟨hheld, hslot, ?_⟩
    unfold retrieveCap at hret
    by_cases hf : slotFresh k slot
    · rw [if_pos hf] at hret
      cases hret
      intro x c hc
      have hc' : c ∈ grant k.caps recipient slot.payload x := hc
      by_cases hx : x = recipient
      · have hmem : c = slot.payload ∨ c ∈ k.caps x :=
          List.mem_cons.mp (by simpa [grant, hx] using hc')
        rcases hmem with h | h
        · exact Or.inr ⟨hx, hslot ▸ h⟩
        · exact Or.inl h
      · exact Or.inl (by simpa [grant, hx] using hc')
    · rw [if_neg hf] at hret; exact absurd hret (by simp)
  · rw [if_neg hheld] at hstore; exact absurd hstore (by simp)

/-! ## §4 — The revocation TOOTH: storage does not launder freshness. -/

/-- **`revoke_stales_stored_cap` — THE R7 TOOTH (PROVED).** A faithful delegation-revoke on the
grantor (`recKRevokeDelegationFull`, the op that bumps the grantor's `delegationEpoch` by `+1`)
REFUSES every retrieval of a slot stored at-or-under the pre-revoke epoch. The sealed-box /
sturdy-ref laundering path (store before the revoke, redeem after) is CLOSED — the pale-ghost
foil for stored capabilities. -/
theorem revoke_stales_stored_cap (k : RecordKernelState) (child recipient : CellId)
    (slot : CapSlot) (hstamp : slot.storedEpoch ≤ k.delegationEpoch slot.grantor) :
    retrieveCap (recKRevokeDelegationFull k slot.grantor child) slot recipient = none := by
  unfold retrieveCap
  rw [if_neg ?_]
  intro hf
  have hle : (recKRevokeDelegationFull k slot.grantor child).delegationEpoch slot.grantor
      ≤ slot.storedEpoch := of_decide_eq_true hf
  rw [recKRevokeDelegationFull_bumps_parent_epoch] at hle
  omega

/-- **`store_then_revoke_refused` — the end-to-end staleness corollary (PROVED).** Store a cap
NOW, let the grantor revoke (epoch bump), and the retrieval REFUSES — directly in terms of
`storeCap`'s own stamp. -/
theorem store_then_revoke_refused {k : RecordKernelState} {grantor child recipient : CellId}
    {payload : Cap} {slot : CapSlot}
    (hstore : storeCap k grantor payload = some slot) :
    retrieveCap (recKRevokeDelegationFull k grantor child) slot recipient = none := by
  unfold storeCap at hstore
  by_cases hheld : payload ∈ k.caps grantor
  · rw [if_pos hheld] at hstore
    cases hstore
    exact revoke_stales_stored_cap k child recipient _ (Nat.le_refl _)
  · rw [if_neg hheld] at hstore; exact absurd hstore (by simp)

/-! ## §5 — Non-vacuity (a fresh retrieval COMMITS; a stale one is REFUSED; no store-forging). -/

/-- A concrete world: cell `0` (the grantor) holds a read cap on cell `5`; epoch 0 everywhere. -/
def kCS : RecordKernelState :=
  { accounts := {0, 5, 9}
  , cell     := fun _ => Value.record []
  , caps     := fun c => if c = 0 then [Cap.endpoint 5 [Auth.read]] else [] }

/-- The stored slot: grantor `0` parks its held read cap (commits, stamped epoch 0). -/
def slotCS : Option CapSlot := storeCap kCS 0 (Cap.endpoint 5 [Auth.read])

-- the store COMMITS (the grantor held the payload) and stamps the CURRENT epoch (0).
#guard (slotCS.map (fun s => s.storedEpoch)) == some 0
-- a FRESH retrieval COMMITS — and the recipient (cell 9) genuinely GAINS the stored cap.
#guard ((slotCS.bind (fun s => retrieveCap kCS s 9)).map
        (fun k => (k.caps 9).contains (Cap.endpoint 5 [Auth.read]))) == some true
-- ...and nobody else's c-list moved (cell 5 still holds nothing).
#guard ((slotCS.bind (fun s => retrieveCap kCS s 5)).map
        (fun k => k.caps 0 == kCS.caps 0)) == some true
-- a retrieval AFTER the grantor's revoke (epoch bump) is REFUSED — the R7 tooth, executable.
#guard ((slotCS.bind (fun s => retrieveCap (recKRevokeDelegationFull kCS 0 7) s 9)).isSome) == false
-- no forging at the store mouth: an UNHELD payload cannot be stored.
#guard (storeCap kCS 0 (Cap.endpoint 5 [Auth.read, Auth.write])).isSome == false
#guard (storeCap kCS 9 (Cap.endpoint 5 [Auth.read])).isSome == false

#assert_axioms stored_cap_only_fresh_if_epoch_unrevoked
#assert_axioms no_forge_from_storage
#assert_axioms revoke_stales_stored_cap
#assert_axioms store_then_revoke_refused

end Dregg2.Apps.CapSlotFactory
