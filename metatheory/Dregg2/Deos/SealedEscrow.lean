/-
# Dregg2.Deos.SealedEscrow — an atomic 2-of-2 value swap completes ALL-OR-NOTHING and ONCE
(the sealed-escrow house-capacity, grounded BY REUSE of the committed-heap root + the one-shot
Consumed discipline).

`cell/src/escrow_sealed.rs` is the Rust house-capacity: a cell that escrows a two-party exchange
"A gives X iff B gives Y". Each party locks one *leg* (party, asset, amount) into the escrow cell's
committed heap; the exchange completes atomically only when BOTH conforming legs are present; and
each leg carries a one-shot `Consumed` flag so it can never be claimed/settled/reclaimed twice. Its
soundness is *forge/replay rejection*: no party walks away holding the counterparty's leg without
having genuinely deposited its own conforming leg, no leg is claimed twice, and no claim exceeds the
locked amount.

This module is the Lean RUNG for that capacity, in the SAME shape the MEMBRANE and DERIVED-CELL
rungs set (`docs/deos/HOUSE-CAPACITY-FRAMEWORK.md`): add the invariant leg, prove it **by reuse** of
an already-proven commitment (here `Substrate.Heap`'s sorted-Poseidon2 root), exhibit both-polarity
`#guard` witnesses, `#assert_all_clean`, and wire the Rust to it
(`cell/src/escrow_sealed.rs::tests::invariant_matches_lean_rung`).

## What is proven — and what it REUSES (no escrow-local commitment)

The escrow binds each leg's STATUS (`Empty`/`Deposited`/`Consumed`) and AMOUNT into reserved heap
slots (the SAME `set_heap`/`compute_heap_root` sorted-Poseidon2 map `cell/src/escrow_sealed.rs`
writes, folded into the canonical state commitment with NO VK bump). A verifier holding the cell's
committed heap reads those slots and gates claim/settlement. The rung proves:

  * `deposit_both_ready` / `deposit_binds_amounts` (HONEST ROUND-TRIP + BOTH-LEG BINDING) —
    depositing both conforming legs makes the settlement gate ready AND binds each leg's amount into
    the commitment (a claim binds BOTH legs: settlement reads both). Read-after-write is
    `Heap.hget_hset_self`; the un-touched leg's slot survives by `Heap.hget_hset_frame` (the ONE
    named `Poseidon2SpongeCR` floor — the cap-root floor, reused).

  * `settle_consumes_both` + `replay_rejected` (THE ONE-SHOT TOOTH) — settlement flips BOTH legs to
    `Consumed`; a re-settle/replay of a consumed leg is REJECTED because the gate requires
    `Deposited` and `Consumed ≠ Deposited`. `cell/src/escrow_sealed.rs`'s
    `replay_of_settled_leg_is_rejected`, as a theorem — a spent leg is a spent nullifier.

  * `nonconforming_claim_rejected` (THE NO-CONFORMING-DEPOSIT TOOTH) — a claimant whose own leg is
    not `Deposited` (it never genuinely locked a conforming leg) cannot take the counterparty leg.
    `cell/src/escrow_sealed.rs`'s `claim_without_own_deposit_is_rejected`.

  * `over_claim_rejected` (THE OVER-CLAIM TOOTH) — a claim asserting MORE than the taken leg's
    committed amount is REJECTED — the claimed value is bounded by the locked amount, exactly as a
    forged derived value diverges from its sources. `cell/src/escrow_sealed.rs`'s
    `over_claim_is_rejected`.

  * **`leg_status_bound_in_root` / `leg_amount_bound_in_root` (THE REUSE KEYSTONE)** — equal
    committed roots ⟹ equal leg status AND equal leg amount: a forge cannot present the honest root
    with a flipped status (a `Consumed` leg masquerading as `Deposited`) or a swollen amount. DIRECT
    instances of `Heap.root_binds_get` (the anti-ghost), under the one named `Poseidon2SpongeCR`
    floor. With it, `forged_leg_moves_root`: a forged leg MUST publish a different root, where the
    status/amount teeth then bite.

This is NOT new mathematics: the legs are committed scalars and the BINDING is the proven
sorted-Poseidon2 root (`Substrate.Heap`). The sealed escrow is a NAMING of "a committed-heap
binding whose two leg slots gate an atomic, once-only swap" — exactly as the membrane is a naming of
iterated kernel attenuation and the derived cell a committed fold over sources.

## The named follow-up (VK-affecting, NOT forced here)

This rung grounds the EXECUTOR-witnessed invariant: a verifier WITH the committed heap rejects forges
and replays. Binding "both legs present ∧ conforming ∧ not-yet-consumed ⟹ both consumed" into the
EffectVM circuit — so a light client verifying a *batch* sees settlement-atomicity as part of the
proven kernel transition (a `SettleEscrow` effect descriptor) — is the VK-affecting weld named in
`docs/deos/SEALED-ESCROW.md` §"Next slice: circuit binding" and
`metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`, the same lane the cap-root reshape drives. The teeth
here are the *executor* teeth; the circuit tooth is their shadow.

## Axiom hygiene

`#assert_all_clean` at the close. Crypto enters ONLY as the named `Poseidon2SpongeCR` hypothesis (the
cap-root floor the heap carries), never as an axiom. NO core/heap edit — every binding is the REAL
`Substrate.Heap.hset`/`hget` and the root is the REAL `Substrate.Heap.root`.
-/
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Deos.SealedEscrow

open Dregg2.Substrate.Heap
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the escrow as committed heap slots (REUSE of `Substrate.Heap`).

The escrow ledger lives in a reserved heap collection (`cell/src/escrow_sealed.rs`'s
`ESCROW_COLL = 0x5_E5C_E0`), with the terms digest at `keyDigest`, each leg's amount at
`keyAmount{A,B}`, and each leg's status at `keyStatus{A,B}` — all folded into the canonical state
commitment by the SAME sorted-Poseidon2 `Heap.root`. We do not add a commitment: we WRITE into the
proven one. -/

/-- The reserved escrow collection (`ESCROW_COLL = 0x5_E5C_E0`). -/
def escrowColl : ℤ := 6184160
/-- Heap key holding the terms digest (`KEY_TERMS_DIGEST`). -/
def keyDigest : ℤ := 0

/-- A leg's lifecycle code, as stored (one felt) in the committed heap — the Lean image of
`cell/src/escrow_sealed.rs::LegStatus`. -/
def stEmpty : ℤ := 0
/-- A conforming leg is locked and unconsumed — claimable / settleable. -/
def stDeposited : ℤ := 1
/-- The leg has been consumed (settled to the counterparty OR reclaimed): the one-shot terminal. -/
def stConsumed : ℤ := 2

/-- Which of the two legs (`cell/src/escrow_sealed.rs::Side`). -/
inductive Side where
  | A | B
deriving DecidableEq, Repr

/-- The counterparty side. -/
def Side.other : Side → Side
  | .A => .B
  | .B => .A

/-- Heap key holding leg `side`'s committed amount (`KEY_LEG_{A,B}_AMOUNT` = 1/2). -/
def amountKey : Side → ℤ
  | .A => 1
  | .B => 2

/-- Heap key holding leg `side`'s status code (`KEY_LEG_{A,B}_STATUS` = 3/4). -/
def statusKey : Side → ℤ
  | .A => 3
  | .B => 4

/-- The status of leg `side` bound in a cell's committed heap. -/
def boundStatus (hash : List ℤ → ℤ) (h : FeltHeap) (side : Side) : Option ℤ :=
  hget hash h escrowColl (statusKey side)

/-- The committed amount of leg `side` bound in a cell's committed heap. -/
def boundAmount (hash : List ℤ → ℤ) (h : FeltHeap) (side : Side) : Option ℤ :=
  hget hash h escrowColl (amountKey side)

/-- **`deposit hash h side amt`** — lock a conforming leg: write its amount, then mark it
`Deposited`. The Lean image of `cell/src/escrow_sealed.rs::deposit_leg` on a conforming leg. -/
def deposit (hash : List ℤ → ℤ) (h : FeltHeap) (side : Side) (amt : ℤ) : FeltHeap :=
  hset hash (hset hash h escrowColl (amountKey side) amt) escrowColl (statusKey side) stDeposited

/-- **`settle hash h`** — complete the swap atomically: flip BOTH legs to `Consumed` in one step.
The Lean image of `cell/src/escrow_sealed.rs::settle` (no partial settlement). -/
def settle (hash : List ℤ → ℤ) (h : FeltHeap) : FeltHeap :=
  hset hash (hset hash h escrowColl (statusKey Side.A) stConsumed) escrowColl (statusKey Side.B)
    stConsumed

/-! ## §2 — the verification core (the forge-detector, as a predicate).

`Ready` (the settlement gate) and `ClaimOk` (the claim gate) are the Lean images of
`EscrowState::settlement` / `EscrowState::check_claim`: the honest-accept path and every forge-reject
path consult THESE, so a stub in either direction fails one polarity. -/

/-- **The settlement gate.** Both legs are `Deposited` (live, unconsumed) — the precondition
`cell/src/escrow_sealed.rs::settlement` checks before consuming both. -/
abbrev Ready (hash : List ℤ → ℤ) (h : FeltHeap) : Prop :=
  boundStatus hash h Side.A = some stDeposited ∧ boundStatus hash h Side.B = some stDeposited

/-- A claim to TAKE the `take` leg by presenting one's OWN deposited leg (`cell/src/escrow_sealed.rs::Claim`). -/
structure Claim where
  /-- The claimant's own side (the leg it deposited). -/
  own : Side
  /-- The leg the claimant wants to take (the counterparty's). -/
  take : Side
  /-- The amount the claimant asserts its own leg locked. -/
  ownAmt : ℤ
  /-- The value the claimant asserts the taken leg is worth. -/
  claimedValue : ℤ

/-- **The claim gate.** The claim accepts (given the taken leg's committed `locked` amount) iff the
claimant's own leg is `Deposited` at the committed amount it asserts, the taken leg is live
(`Deposited`, not consumed), and the claimed value does not exceed the taken leg's locked amount.
The Lean image of `cell/src/escrow_sealed.rs::check_claim` returning `Ok`. -/
abbrev ClaimOk (hash : List ℤ → ℤ) (h : FeltHeap) (c : Claim) (locked : ℤ) : Prop :=
  boundStatus hash h c.own = some stDeposited ∧
  boundAmount hash h c.own = some c.ownAmt ∧
  boundStatus hash h c.take = some stDeposited ∧
  boundAmount hash h c.take = some locked ∧
  c.claimedValue ≤ locked

/-! ## §3 — THE HONEST ROUND-TRIP + BOTH-LEG BINDING.

Depositing both conforming legs makes settlement ready AND binds each leg's amount — so settlement
reads BOTH legs (the atomic swap binds both). The frames ride the ONE named `Poseidon2SpongeCR`
floor; the read-backs are crypto-free. -/

/-- **HONEST ROUND-TRIP.** After both legs are deposited, the settlement gate is `Ready`. Leg B's
status reads back by `Heap.hget_hset_self`; leg A's survives the leg-B writes by
`Heap.hget_hset_frame` (the named cap-root `Poseidon2SpongeCR` floor). -/
theorem deposit_both_ready (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (aA aB : ℤ) :
    Ready hash (deposit hash (deposit hash h Side.A aA) Side.B aB) := by
  refine ⟨?_, ?_⟩
  · -- leg A's status: frame off leg B's status write and amount write, then read-after-write.
    show hget hash (deposit hash (deposit hash h Side.A aA) Side.B aB) escrowColl (statusKey Side.A)
        = some stDeposited
    unfold deposit
    rw [hget_hset_frame hash hCR _ escrowColl (statusKey Side.B) escrowColl (statusKey Side.A)
        stDeposited (by decide),
      hget_hset_frame hash hCR _ escrowColl (amountKey Side.B) escrowColl (statusKey Side.A)
        aB (by decide)]
    exact hget_hset_self hash _ escrowColl (statusKey Side.A) stDeposited
  · -- leg B's status: read-after-write (written last).
    exact hget_hset_self hash _ escrowColl (statusKey Side.B) stDeposited

/-- **BOTH-LEG BINDING.** After both deposits, EACH leg's committed amount is bound — settlement and
the claim gate read the genuine `(aA, aB)`. A swap binds BOTH legs into the one commitment. -/
theorem deposit_binds_amounts (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (aA aB : ℤ) :
    boundAmount hash (deposit hash (deposit hash h Side.A aA) Side.B aB) Side.A = some aA ∧
    boundAmount hash (deposit hash (deposit hash h Side.A aA) Side.B aB) Side.B = some aB := by
  refine ⟨?_, ?_⟩
  · -- leg A's amount: frame off all three later writes, then read-after-write.
    show hget hash (deposit hash (deposit hash h Side.A aA) Side.B aB) escrowColl (amountKey Side.A)
        = some aA
    unfold deposit
    rw [hget_hset_frame hash hCR _ escrowColl (statusKey Side.B) escrowColl (amountKey Side.A)
        stDeposited (by decide),
      hget_hset_frame hash hCR _ escrowColl (amountKey Side.B) escrowColl (amountKey Side.A)
        aB (by decide),
      hget_hset_frame hash hCR _ escrowColl (statusKey Side.A) escrowColl (amountKey Side.A)
        stDeposited (by decide)]
    exact hget_hset_self hash _ escrowColl (amountKey Side.A) aA
  · -- leg B's amount: frame off leg B's status write, then read-after-write.
    show hget hash (deposit hash (deposit hash h Side.A aA) Side.B aB) escrowColl (amountKey Side.B)
        = some aB
    unfold deposit
    rw [hget_hset_frame hash hCR _ escrowColl (statusKey Side.B) escrowColl (amountKey Side.B)
        stDeposited (by decide)]
    exact hget_hset_self hash _ escrowColl (amountKey Side.B) aB

/-- **HONEST CLAIM ACCEPTS** (non-vacuity). On the both-deposited escrow, B's claim of A's leg
(presenting its own conforming leg, claiming no more than A locked) is accepted by the gate. The
live path the one-shot tooth later closes. -/
theorem honest_claim_accepts (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (h : FeltHeap) (aA aB v : ℤ) (hv : v ≤ aA) :
    ClaimOk hash (deposit hash (deposit hash h Side.A aA) Side.B aB)
      ⟨Side.B, Side.A, aB, v⟩ aA := by
  have hready := deposit_both_ready hash hCR h aA aB
  have hamt := deposit_binds_amounts hash hCR h aA aB
  exact ⟨hready.2, hamt.2, hready.1, hamt.1, hv⟩

/-! ## §4 — THE TEETH: one-shot replay, no-conforming-deposit, over-claim.

Each forge is rejected by the SAME gate the honest path passes — a stub fails one polarity. -/

/-- Settlement flips BOTH legs to `Consumed`. -/
theorem settle_consumes_both (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (h : FeltHeap) :
    boundStatus hash (settle hash h) Side.A = some stConsumed ∧
    boundStatus hash (settle hash h) Side.B = some stConsumed := by
  refine ⟨?_, ?_⟩
  · show hget hash (settle hash h) escrowColl (statusKey Side.A) = some stConsumed
    unfold settle
    rw [hget_hset_frame hash hCR _ escrowColl (statusKey Side.B) escrowColl (statusKey Side.A)
        stConsumed (by decide)]
    exact hget_hset_self hash _ escrowColl (statusKey Side.A) stConsumed
  · exact hget_hset_self hash _ escrowColl (statusKey Side.B) stConsumed

/-- **THE ONE-SHOT TOOTH.** A settled escrow is no longer `Ready`: leg A is `Consumed`, and
`Consumed ≠ Deposited`, so the settlement gate REFUSES a replay. `cell/src/escrow_sealed.rs`'s
`replay_of_settled_leg_is_rejected`, as a theorem — a spent leg is a spent nullifier. -/
theorem replay_rejected (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (h : FeltHeap) :
    ¬ Ready hash (settle hash h) := by
  intro hr
  have hA := hr.1
  rw [(settle_consumes_both hash hCR h).1] at hA
  exact (by decide : stConsumed ≠ stDeposited) (Option.some.inj hA)

/-- **THE NO-CONFORMING-DEPOSIT TOOTH.** A claimant whose own leg is not `Deposited` (it never
locked a conforming leg) cannot claim: the gate's own-leg leg fails. `cell/src/escrow_sealed.rs`'s
`claim_without_own_deposit_is_rejected`, as a theorem. -/
theorem nonconforming_claim_rejected (hash : List ℤ → ℤ) (h : FeltHeap) (c : Claim) (locked : ℤ)
    (hnodep : boundStatus hash h c.own = some stEmpty) :
    ¬ ClaimOk hash h c locked := by
  intro hok
  have hown := hok.1
  rw [hnodep] at hown
  exact (by decide : stEmpty ≠ stDeposited) (Option.some.inj hown)

/-- **THE TAKEN-LEG ONE-SHOT TOOTH.** A claim against an already-`Consumed` taken leg is REJECTED —
the taken leg must be live. The claim-path face of the one-shot discipline. -/
theorem consumed_taken_leg_rejected (hash : List ℤ → ℤ) (h : FeltHeap) (c : Claim) (locked : ℤ)
    (hconsumed : boundStatus hash h c.take = some stConsumed) :
    ¬ ClaimOk hash h c locked := by
  intro hok
  have htake := hok.2.2.1
  rw [hconsumed] at htake
  exact (by decide : stConsumed ≠ stDeposited) (Option.some.inj htake)

/-- **THE OVER-CLAIM TOOTH.** A claim asserting MORE than the taken leg's committed `locked` amount
is REJECTED: the claimed value is bounded by the locked amount. `cell/src/escrow_sealed.rs`'s
`over_claim_is_rejected`, as a theorem. -/
theorem over_claim_rejected (hash : List ℤ → ℤ) (h : FeltHeap) (c : Claim) (locked : ℤ)
    (hover : locked < c.claimedValue) :
    ¬ ClaimOk hash h c locked := by
  intro hok
  exact absurd hok.2.2.2.2 (not_le.mpr hover)

/-! ## §5 — THE REUSE KEYSTONE: each leg is bound into the committed root.

Each leg's status and amount ride the SAME sorted-Poseidon2 `Heap.root` the cap crown proves binds.
So equal committed roots open to the SAME leg state — a forge cannot present the honest root with a
flipped status (a consumed leg posing as deposited) or a swollen amount. DIRECT instances of
`Heap.root_binds_get` (the anti-ghost), under the one named `Poseidon2SpongeCR` floor. -/

/-- **THE REUSE KEYSTONE (status).** Two heaps with EQUAL roots open to the SAME leg status. Proven
by REUSE of `Heap.root_binds_get` — no escrow-local commitment. -/
theorem leg_status_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) (side : Side) :
    boundStatus hash h₁ side = boundStatus hash h₂ side :=
  root_binds_get hash hCR hroot escrowColl (statusKey side)

/-- **THE REUSE KEYSTONE (amount).** Equal roots ⟹ equal leg amount — a forge cannot swell a locked
amount while keeping the honest root. -/
theorem leg_amount_bound_in_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (hroot : root hash h₁ = root hash h₂) (side : Side) :
    boundAmount hash h₁ side = boundAmount hash h₂ side :=
  root_binds_get hash hCR hroot escrowColl (amountKey side)

/-- **THE ANTI-GHOST.** A forged leg whose committed status differs from the honest one CANNOT keep
the honest root — it must publish a different root (where the status tooth then bites). The
contrapositive of `leg_status_bound_in_root`. -/
theorem forged_leg_moves_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : FeltHeap} (side : Side) (hne : boundStatus hash h₁ side ≠ boundStatus hash h₂ side) :
    root hash h₁ ≠ root hash h₂ :=
  fun hroot => hne (leg_status_bound_in_root hash hCR hroot side)

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the swap invariant BITES, both polarities.

Computed on the reference sponge (`Substrate.Heap.refSponge`) so the honest swap settles, a replay
fails AND moves the root, and an over-claim fails — the executable shadow of §3/§4/§5. -/

section Witnesses

/-- An escrow with leg A locking 100, leg B locking 250 (the Rust `sample_terms`), over the empty
heap. -/
private def both : FeltHeap := deposit refSponge (deposit refSponge [] Side.A 100) Side.B 250

-- HONEST: both legs read back `Deposited` at their committed amounts; settlement is ready.
#guard boundStatus refSponge both Side.A == some stDeposited
#guard boundStatus refSponge both Side.B == some stDeposited
#guard boundAmount refSponge both Side.A == some 100
#guard boundAmount refSponge both Side.B == some 250
#guard decide (Ready refSponge both)
-- HONEST CLAIM: B takes A's leg presenting its own (claims exactly the 100 A locked) — accepts.
#guard decide (ClaimOk refSponge both ⟨Side.B, Side.A, 250, 100⟩ 100)

-- THE ONE-SHOT: settle (both Consumed). The escrow is no longer ready, and — critically — the
-- consumption MOVED the committed root (a settled leg cannot hide under the deposited root).
private def settled : FeltHeap := settle refSponge both
#guard boundStatus refSponge settled Side.A == some stConsumed
#guard boundStatus refSponge settled Side.B == some stConsumed
#guard !decide (Ready refSponge settled)
#guard (root refSponge settled != root refSponge both)
-- and a claim against the now-consumed taken leg is refused (the claim-path one-shot):
#guard !decide (ClaimOk refSponge settled ⟨Side.B, Side.A, 250, 100⟩ 100)

-- THE OVER-CLAIM: claiming A's leg is worth 9999 when it locks 100 is refused.
#guard !decide (ClaimOk refSponge both ⟨Side.B, Side.A, 250, 9999⟩ 100)

-- THE NO-CONFORMING-DEPOSIT: only A deposits; B never locks a leg, yet tries to take A's.
private def onlyA : FeltHeap := deposit refSponge [] Side.A 100
#guard boundStatus refSponge onlyA Side.B == none
#guard !decide (ClaimOk refSponge onlyA ⟨Side.B, Side.A, 250, 100⟩ 100)

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  deposit_both_ready,
  deposit_binds_amounts,
  honest_claim_accepts,
  settle_consumes_both,
  replay_rejected,
  nonconforming_claim_rejected,
  consumed_taken_leg_rejected,
  over_claim_rejected,
  leg_status_bound_in_root,
  leg_amount_bound_in_root,
  forged_leg_moves_root
]

end Dregg2.Deos.SealedEscrow
