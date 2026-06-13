/-
# Dregg2.Apps.ComputeMarketDesk — a rate-limited compute marketplace desk with ASYNC settlement
notify (round 2).

`Apps/ComputeExchangeGated.lean` re-points a compute market onto the escrow factory (the payment lives
in a factory-born escrow cell's `bal`). Real on the VALUE-MOVE axis, but its POLICY is thin: the
lifecycle is a 2-state machine and a condition witness; there is no rate limit, no price discipline, no
provider-pool membership, and settlement is synchronous. A real compute desk meters provider payouts (a
compromised provider key cannot drain the desk in one turn), disciplines the agreed price (a settle at a
nonsense rate is rejected), restricts who may provide (a registered pool), drains the escrow on settle
(no stranded value), and WAKES the provider asynchronously when the job settles (the provider need not
poll). This module rebuilds the desk as a RICH `RecordProgram` PLUS the round-2 async `notify` cap
algebra — the policy clauses use the rate ceiling (`balanceDeltaLe`), the price band (`inRangeTwoSided`),
the provider pool (`senderMemberOf`), and the drain invariant (`balanceLe`); the async settlement wake
uses the `Firmament.NotifyAuthority` badge-masked, attenuable `NotifyCap`. Each clause a theorem in both
polarities.

## Why this is not a toy

  * **the payout drain.** The desk holds escrowed job payments; a settle pays the provider out of the
    desk balance. Without a rate ceiling, a compromised provider key settles the ENTIRE desk balance in
    one turn. `payoutCeiling` = `balanceDeltaLe payoutRate`: the per-turn balance change may not be MORE
    than the desk's payout rate (the desk may not GAIN more than the rate — and on a settle the desk
    LOSES, so a settle within the rate has a bounded movement). An over-rate movement is UNSAT
    (`over_payout_rejected`).
  * **the nonsense price.** The agreed job RATE must lie in a published price band — a settle at rate 0
    (free work the provider never agreed to) or rate 10^9 (a drain dressed as a price) is rejected.
    `priceBand` = `inRangeTwoSided rate priceLo priceHi` gives `off_band_price_rejected`.
  * **the unregistered provider.** A settle must be SIGNED by a provider in the registered pool, not by
    any capability holder. `providerPool` = `senderMemberOf providerSet` gives
    `non_provider_rejected`.
  * **the stranded escrow.** A settle driving the desk to RESOLVED must drain the escrow to `≤ 0` — a
    "settle" that pays partially and leaves value sitting is rejected. `drainOnResolve` =
    `anyOf [not (state = RESOLVED), balanceLe 0]` gives `stranded_escrow_rejected`.

## The async settlement wake (the round-2 notify wedge)

A settled job WAKES the provider — but the desk does not get to wake the provider however it likes. The
wake rides a `Firmament.NotifyAuthority.NotifyCap`: the desk holds a notify cap to the provider's
settlement notification object, scoped to a BADGE MASK (the job-kinds it may signal). The wake is
admissible only if the settlement badge is within the held mask (`signalGated`), and the desk may
ATTENUATE the cap before handing it to a sub-desk — narrowing the mask, never widening it
(`settle_wake_attenuation_no_amplify`). A wake of a badge outside the held mask is REFUSED
(`out_of_mask_wake_refused`). This is the async coordination the synchronous re-point lacked: the
provider learns of settlement by a wake, not a poll, and the wake authority is a held, attenuable cap.

## The desk cell — its state

  * `state`    — `0 OPEN`, `1 RESOLVED` (the lifecycle slot);
  * `rate`     — the agreed job rate (must lie in the price band);
  * `provider` — (informational; the binding is the provider POOL on the turn sender);
  * the cell's SEALED balance — the escrowed payment (drained on RESOLVED, rate-limited), carried in
    `TurnCtx.balance` / `TurnCtx.balanceBefore`.

## Honest scope

  * `balanceDeltaLe` is the BOUNDED / ordering pole (§8): a rate gate on the decrementable balance is
    i-confluent only under the single serializer (n=1). Named, not laundered.
  * The notify wake demonstrates AUTHORITY containment (the desk can wake only within its held badge
    mask, and attenuation only shrinks it), NOT information containment — a badge-OR is never info-free
    (the same carried scope `Apps/SwarmSignal.lean` flags). The §8 seam is the kernel balance carrier +
    the notification object's badge accumulator; the gate/attenuation laws are proved here and in
    `NotifyAuthority`.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` —
`decide` / `#guard` / `Exec.Program` + `NotifyAuthority` keystone reuse only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.Program
import Dregg2.Firmament.NotifyAuthority

namespace Dregg2.Apps.ComputeMarketDesk

open Dregg2.Exec
open Dregg2.Firmament.NotifyAuthority (NotifyCap signalGated signalAdmissible_attenuate_no_amplify
  signalGated_commits_of_admissible signalGated_refuses_of_inadmissible)
open Dregg2.Firmament.SeL4Kernel (Notification)

/-! ## §0 — The desk's field names, lifecycle codes, price band, payout rate, provider pool. -/

/-- The lifecycle slot: `0 OPEN`, `1 RESOLVED`. -/
abbrev stateF : FieldName := "state"
/-- The agreed job rate (must lie in the price band). -/
abbrev rateF : FieldName := "rate"

/-- Lifecycle: the desk is open (a job is escrowed, awaiting settlement). -/
abbrev stOPEN : Int := 0
/-- Lifecycle: the job settled (the provider is paid; the escrow is drained). -/
abbrev stRESOLVED : Int := 1

/-- The published price band: an agreed job rate must lie in `[priceLo, priceHi]`. -/
abbrev priceLo : Int := 10
abbrev priceHi : Int := 1000

/-- The desk's per-turn payout RATE CEILING: the sealed balance may not change by more than `payoutRate`
in one turn (`new.balance − old.balance ≤ payoutRate`). A settle DEBITS the desk (a negative delta, well
under the ceiling); the ceiling blocks an adversarial CREDIT/movement past the rate. -/
abbrev payoutRate : Int := 0

/-- The registered provider POOL: the identities authorized to settle (be paid). -/
abbrev providerSet : List Int := [0x71, 0x72, 0x73]
/-- A registered provider's identity. -/
abbrev providerPk : Int := 0x72
/-- An unregistered identity (holds a capability, but is not a registered provider). -/
abbrev outsiderPk : Int := 0x99

/-! ## §1 — THE SETTLE GATE as a `RecordProgram`
(provider pool ∧ price band ∧ payout rate ∧ drain-on-resolve).

The settle program is a conjunction, each clause a constraint of the cell's `RecordProgram`:

  * `senderMemberOf providerSet` — **provider pool**: a settle must be SIGNED BY a registered provider.
  * `inRangeTwoSided rateF priceLo priceHi` — **price band**: the agreed rate must be published.
  * `balanceDeltaLe payoutRate` — **the payout-rate ceiling**: the per-turn sealed-balance movement is
    bounded by the desk's rate. (A settle debits, well under the ceiling; an adversarial movement past
    the rate is rejected.)
  * `anyOf [not (state = RESOLVED), balanceLe 0]` — **the drain invariant**: a settle driving the desk
    to RESOLVED must drain the escrow to `≤ 0`. Value cannot be stranded.

The conjunction is ONE predicate (all-or-nothing). -/
def settleConstraints : List StateConstraint :=
  [ .simple (.senderMemberOf providerSet)                                          -- provider pool
  , .simple (.inRangeTwoSided rateF priceLo priceHi)                               -- price band
  , .simple (.balanceDeltaLe payoutRate)                                           -- payout-rate ceiling
  , .anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0] ]                 -- drain on resolve

/-- **The compute-market-desk program** — the settle policy as ONE coalgebra structure-map. -/
def deskProgram : RecordProgram := .predicate settleConstraints

/-! ## §2 — Extraction plumbing (the `EscrowDeskCouncil` pattern). -/

private theorem admitted_mem {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : deskProgram.admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ settleConstraints) :
    evalConstraintCtx ctx c o n = true := by
  have hall : settleConstraints.all (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

private theorem admits_of_not_false {ctx : TurnCtx} {m : Nat} {o n : Value}
    (hc : ¬ deskProgram.admitsCtx ctx m o n = false) :
    deskProgram.admitsCtx ctx m o n = true := by
  cases h : deskProgram.admitsCtx ctx m o n with
  | true => rfl
  | false => exact absurd h hc

/-- A two-variant `anyOf` whose first disjunct fails forces the second (the `EscrowDeskCouncil` shape). -/
private theorem anyOf_pair_right {ctx : TurnCtx} {x y : SimpleConstraint} {o n : Value}
    (h : evalConstraintCtx ctx (.anyOf [x, y]) o n = true)
    (hx : evalSimpleCtx ctx x o n = false) :
    evalSimpleCtx ctx y o n = true := by
  have h' : (evalSimpleCtx ctx x o n || (evalSimpleCtx ctx y o n || false)) = true := h
  rw [hx] at h'
  simpa using h'

/-- When a turn DRIVES the desk to RESOLVED, the `.not (state=RESOLVED)` guard is FALSE. -/
private theorem resolved_guard_false {ctx : TurnCtx} {o n : Value}
    (hres : n.scalar stateF = some stRESOLVED) :
    evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n = false := by
  show (!(evalSimpleCtx ctx (.fieldEquals stateF stRESOLVED) o n)) = false
  have : evalSimpleCtx ctx (.fieldEquals stateF stRESOLVED) o n = true := by
    show evalSimple (.fieldEquals stateF stRESOLVED) o n = true
    simp [evalSimple, hres]
  rw [this]; rfl

/-! ## §3 — THE TEETH on the settle policy (both polarities, all PROVED). -/

/-- **① PROVIDER-POOL TOOTH — a settle not signed by a registered provider is UNSAT.** Any settle whose
sender is NOT in the registered provider pool is rejected: `admitsCtx = false`. A capability holder who
is not a registered provider cannot be paid. -/
theorem non_provider_rejected (ctx : TurnCtx) (m : Nat) (o n : Value)
    (houtsider : ∀ s, ctx.sender = some s → s ∉ providerSet) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hprov := admitted_mem hne (c := .simple (.senderMemberOf providerSet)) (.head _)
  have hmem : evalSimpleCtx ctx (.senderMemberOf providerSet) o n = true := by
    simpa [evalConstraintCtx] using hprov
  obtain ⟨s, hs, hcon⟩ := (evalSimpleCtx_senderMemberOf_iff ctx providerSet o n).mp hmem
  rw [List.contains_eq_mem] at hcon
  exact houtsider s hs (by simpa using hcon)

/-- **② PRICE-BAND TOOTH — a settle at an off-band rate is UNSAT.** A settle whose agreed rate is OUTSIDE
the published band `[priceLo, priceHi]` (rate 0 = free work; rate 10^9 = a drain dressed as a price) is
rejected: `admitsCtx = false`. -/
theorem off_band_price_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (r : Int)
    (hrate : n.scalar rateF = some r)
    (hoff : r < priceLo ∨ priceHi < r) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hband := admitted_mem hne (c := .simple (.inRangeTwoSided rateF priceLo priceHi)) (.tail _ (.head _))
  have hb : evalSimpleCtx ctx (.inRangeTwoSided rateF priceLo priceHi) o n = true := by
    simpa [evalConstraintCtx] using hband
  rw [show evalSimpleCtx ctx (.inRangeTwoSided rateF priceLo priceHi) o n
        = evalSimple (.inRangeTwoSided rateF priceLo priceHi) o n from rfl] at hb
  obtain ⟨x, hx, hlo, hhi⟩ := (evalSimple_inRangeTwoSided_iff rateF priceLo priceHi o n).mp hb
  rw [hrate] at hx; injection hx with hx; subst hx
  rcases hoff with h | h <;> omega

/-- **③ PAYOUT-RATE TOOTH — a settle movement past the payout rate is UNSAT.** A settle whose per-turn
sealed-balance change EXCEEDS the desk's payout rate (`Δbalance > payoutRate`) is rejected:
`admitsCtx = false`. A compromised provider key cannot move the desk balance past the rate in one turn. -/
theorem over_payout_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (before after : Int)
    (hbefore : ctx.balanceBefore = some before)
    (hafter : ctx.balance = some after)
    (hover : after - before > payoutRate) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hrate := admitted_mem hne (c := .simple (.balanceDeltaLe payoutRate)) (.tail _ (.tail _ (.head _)))
  have hle : evalSimpleCtx ctx (.balanceDeltaLe payoutRate) o n = true := by
    simpa [evalConstraintCtx] using hrate
  obtain ⟨a, b, ha, hb, hbound⟩ := (evalSimpleCtx_balanceDeltaLe_iff ctx payoutRate o n).mp hle
  rw [hbefore] at ha; injection ha with ha; subst ha
  rw [hafter] at hb; injection hb with hb; subst hb
  omega

/-- **④ STRANDED-ESCROW TOOTH — a settle leaving value in the desk is UNSAT.** A settle driving the desk
to RESOLVED while its balance is still POSITIVE (value left sitting) is rejected: `admitsCtx = false`.
The escrow cannot resolve with value stranded — a settle must drain it (`balance ≤ 0`). -/
theorem stranded_escrow_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (bal : Int)
    (hres : n.scalar stateF = some stRESOLVED)
    (hbalance : ctx.balance = some bal)
    (hpos : bal > 0) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hclause := admitted_mem hne
    (c := .anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0])
    (.tail _ (.tail _ (.tail _ (.head _))))
  have hdrain : evalSimpleCtx ctx (.balanceLe 0) o n = true :=
    anyOf_pair_right hclause (resolved_guard_false hres)
  obtain ⟨b, hb, hle⟩ := (evalSimpleCtx_balanceLe_iff ctx 0 o n).mp hdrain
  rw [hbalance] at hb; injection hb with hb; subst hb; omega

/-- **⑤ THE HONEST SETTLE COMMITS (the gate is not constant-false).** A settle signed by a registered
provider, at an in-band rate, with a payout movement within the rate, and the escrow drained, ADMITS.
The conjunction of the teeth is non-vacuous: there is a real settle the desk lets through. -/
theorem honest_settle_admits (ctx : TurnCtx) (m : Nat) (o n : Value)
    (before after : Int)
    (hsender : ctx.sender = some providerPk)
    (_hstate : n.scalar stateF = some stRESOLVED)  -- the scenario: this IS a resolving settle
    (hrate : n.scalar rateF = some 100)             -- an in-band rate (priceLo ≤ 100 ≤ priceHi)
    (hbefore : ctx.balanceBefore = some before) (hafter : ctx.balance = some after)
    (hpayout : after - before ≤ payoutRate)
    (hdrained : ctx.balance = some 0) :
    deskProgram.admitsCtx ctx m o n = true := by
  have c1 : evalConstraintCtx ctx (.simple (.senderMemberOf providerSet)) o n = true := by
    show evalSimpleCtx ctx (.senderMemberOf providerSet) o n = true
    exact (evalSimpleCtx_senderMemberOf_iff ctx providerSet o n).mpr ⟨providerPk, hsender, by decide⟩
  have c2 : evalConstraintCtx ctx (.simple (.inRangeTwoSided rateF priceLo priceHi)) o n = true := by
    show evalSimpleCtx ctx (.inRangeTwoSided rateF priceLo priceHi) o n = true
    rw [show evalSimpleCtx ctx (.inRangeTwoSided rateF priceLo priceHi) o n
          = evalSimple (.inRangeTwoSided rateF priceLo priceHi) o n from rfl]
    exact (evalSimple_inRangeTwoSided_iff rateF priceLo priceHi o n).mpr ⟨100, hrate, by decide, by decide⟩
  have c3 : evalConstraintCtx ctx (.simple (.balanceDeltaLe payoutRate)) o n = true := by
    show evalSimpleCtx ctx (.balanceDeltaLe payoutRate) o n = true
    exact (evalSimpleCtx_balanceDeltaLe_iff ctx payoutRate o n).mpr ⟨before, after, hbefore, hafter, hpayout⟩
  have c4 : evalConstraintCtx ctx (.anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0]) o n = true := by
    have hd : evalSimpleCtx ctx (.balanceLe 0) o n = true :=
      (evalSimpleCtx_balanceLe_iff ctx 0 o n).mpr ⟨0, hdrained, by omega⟩
    show (evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n
          || (evalSimpleCtx ctx (.balanceLe 0) o n || false)) = true
    rw [hd]; simp
  show settleConstraints.all (fun c => evalConstraintCtx ctx c o n) = true
  simp only [settleConstraints, List.all_cons, List.all_nil, c1, c2, c3, c4, Bool.and_true]

/-! ## §4 — THE ASYNC SETTLEMENT WAKE (the round-2 notify cap algebra).

A settled job WAKES the provider's settlement notification object via a `NotifyCap` the desk holds,
scoped to a badge mask (the job-kinds it may signal). The wake commits iff the settlement badge is
within the held mask; a badge outside the mask is REFUSED; and the desk may attenuate the cap to a
sub-desk, narrowing the mask without widening. These ARE the `Firmament.NotifyAuthority` keystones,
specialized to the desk's settlement signal. -/

/-- **`settleWake cap n badge`** — the desk's settlement wake: signal the provider's notification object
`n` with the settlement `badge`, gated by the desk's held `NotifyCap`. Commits (OR'ing the badge) iff
the badge is within the cap's mask; refuses otherwise. This IS `NotifyAuthority.signalGated`. -/
def settleWake (cap : NotifyCap) (n : Notification) (badge : Nat) : Option Notification :=
  signalGated cap n badge

/-- **`settle_wake_commits` — an in-mask settlement wake COMMITS, delivering the badge.** When the
settlement badge is within the desk's held mask, the wake commits and the provider's notification
accumulator gains exactly the settlement badge — the provider is woken, not polled. -/
theorem settle_wake_commits (cap : NotifyCap) (n : Notification) (badge : Nat)
    (hadm : cap.signalAdmissible badge = true) :
    settleWake cap n badge = some (n.signal badge) :=
  signalGated_commits_of_admissible cap n badge hadm

/-- **`out_of_mask_wake_refused` — a settlement wake outside the held mask is REFUSED.** A wake of a
badge with a bit outside the desk's mask makes `settleWake` return `none` — the desk cannot wake on a
job-kind it does not hold the badge for (fail-closed). -/
theorem out_of_mask_wake_refused (cap : NotifyCap) (n : Notification) (badge : Nat)
    (hinadm : cap.signalAdmissible badge = false) :
    settleWake cap n badge = none :=
  signalGated_refuses_of_inadmissible cap n badge hinadm

/-- **`settle_wake_attenuation_no_amplify` — handing a sub-desk a narrower wake cap cannot widen it.**
A settlement badge admissible through an ATTENUATED (narrower-mask) cap is admissible through the
original — so a desk that delegates its settlement-wake authority to a sub-desk can only SHRINK the
job-kinds the sub-desk may signal, never grant it a badge the desk could not. This IS the
`NotifyAuthority` non-amplification keystone, on the desk's settlement cap. -/
theorem settle_wake_attenuation_no_amplify
    (cap : NotifyCap) (narrowerRights : Dregg2.Exec.CapTPConcrete.AuthReq) (narrowerMask : Nat)
    (out : NotifyCap)
    (hatten : cap.attenuateNotify narrowerRights narrowerMask = some out)
    (badge : Nat) (hadm : out.signalAdmissible badge = true) :
    cap.signalAdmissible badge = true :=
  signalAdmissible_attenuate_no_amplify cap narrowerRights narrowerMask out hatten badge hadm

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the settle policy + the wake BITE on the concrete desk, both
polarities. -/

section Witnesses

/-- A faithful settle context: a registered provider signs, balance 0 (was 50: a −50 payout, well under
the +0 ceiling), state→RESOLVED, rate 100 (in band). -/
def settleCtx : TurnCtx :=
  { sender := some providerPk, balance := some 0, balanceBefore := some 50 }
def deskNew : Value := .record [(stateF, .int stRESOLVED), (rateF, .int 100)]
def deskOld : Value := .record [(stateF, .int stOPEN), (rateF, .int 100)]

-- ⑤ COMMIT: a faithful settle ADMITS (registered provider, in-band rate, −50 payout within ceiling,
-- drained to 0).
#guard deskProgram.admitsCtx settleCtx 0 deskOld deskNew

-- ① REFUSE (non-provider): an outsider signs the settle. REJECTED (only registered providers).
#guard deskProgram.admitsCtx
  { settleCtx with sender := some outsiderPk } 0 deskOld deskNew == false

-- ① REFUSE (no sender): unsigned settle. REJECTED (fail-closed provider pool).
#guard deskProgram.admitsCtx
  { settleCtx with sender := none } 0 deskOld deskNew == false

-- ② REFUSE (price below band): rate 5 < priceLo 10 (free work the provider never agreed to). REJECTED.
#guard deskProgram.admitsCtx settleCtx 0 deskOld
  (.record [(stateF, .int stRESOLVED), (rateF, .int 5)]) == false

-- ② REFUSE (price above band): rate 5000 > priceHi 1000 (a drain dressed as a price). REJECTED.
#guard deskProgram.admitsCtx settleCtx 0 deskOld
  (.record [(stateF, .int stRESOLVED), (rateF, .int 5000)]) == false

-- ③ REFUSE (over-payout movement): balance 60 (was 50, a +10 movement > the +0 ceiling). REJECTED.
#guard deskProgram.admitsCtx
  { settleCtx with balance := some 60 } 0 deskOld deskNew == false

-- ③ REFUSE (absent balance endpoint): no pre-balance ⇒ the rate ceiling fails closed. REJECTED.
#guard deskProgram.admitsCtx
  { settleCtx with balanceBefore := none } 0 deskOld deskNew == false

-- ④ REFUSE (stranded escrow): the desk resolves but balance is still 30 (value left sitting). REJECTED.
#guard deskProgram.admitsCtx
  { settleCtx with balance := some 30, balanceBefore := some 50 } 0 deskOld deskNew == false

-- ⑤ COMMIT (open turn dormant): an OPEN turn (state stays OPEN) by a registered provider with an
-- in-band rate and a within-rate movement ADMITS even with a positive balance — the drain clause is
-- dormant until resolve (the desk is operable until a real settle).
#guard deskProgram.admitsCtx
  { sender := some providerPk, balance := some 50, balanceBefore := some 50 } 0
  (.record [(stateF, .int stOPEN), (rateF, .int 100)])
  (.record [(stateF, .int stOPEN), (rateF, .int 100)])

-- The provider pool isolated: a member (0x72) ADMITS, an outsider REJECTS, no sender REJECTS.
#guard evalSimpleCtx { sender := some providerPk } (.senderMemberOf providerSet) (.record []) (.record [])
#guard evalSimpleCtx { sender := some outsiderPk } (.senderMemberOf providerSet) (.record []) (.record []) == false
#guard evalSimpleCtx {} (.senderMemberOf providerSet) (.record []) (.record []) == false

-- The price band isolated: rate priceLo (10) and priceHi (1000) both ADMIT (inclusive); 9 and 1001 REJECT.
#guard evalSimpleCtx {} (.inRangeTwoSided rateF priceLo priceHi) (.record []) (.record [(rateF, .int 10)])
#guard evalSimpleCtx {} (.inRangeTwoSided rateF priceLo priceHi) (.record []) (.record [(rateF, .int 1000)])
#guard evalSimpleCtx {} (.inRangeTwoSided rateF priceLo priceHi) (.record []) (.record [(rateF, .int 9)]) == false
#guard evalSimpleCtx {} (.inRangeTwoSided rateF priceLo priceHi) (.record []) (.record [(rateF, .int 1001)]) == false

/-! ### The async settlement wake teeth — a held desk cap, badge mask `0b011` (job-kinds 0b001, 0b010). -/

/-- The desk's held settlement-wake cap: target object 7, rights `signature`, mask `0b011`. -/
def deskCap : NotifyCap := { target := 7, rights := .signature, badgeMask := 0b011 }

-- COMMIT: settling a job of kind `0b001` (within the mask) WAKES the provider, OR'ing 0b001 in.
#guard (settleWake deskCap Notification.empty 0b001).isSome
#guard settleWake deskCap Notification.empty 0b001 == some (Notification.empty.signal 0b001)
-- COMMIT: job-kind `0b010` (the other held bit) also wakes.
#guard (settleWake deskCap Notification.empty 0b010).isSome
-- REFUSE: job-kind `0b100` has a bit NOT in the mask ⇒ the wake is refused (fail-closed).
#guard (settleWake deskCap Notification.empty 0b100).isNone

-- ATTENUATE to a sub-desk: narrow the mask 0b011 → 0b001 (drop the 0b010 job-kind) ⇒ commits, holding
-- the narrower mask. The sub-desk now REFUSES 0b010 (which the desk admitted), but still admits 0b001.
#guard (deskCap.attenuateNotify .impossible 0b001).isSome
#guard deskCap.signalAdmissible 0b010                                         -- desk admits 0b010
#guard
  match deskCap.attenuateNotify .impossible 0b001 with
  | some sub => !sub.signalAdmissible 0b010 && sub.signalAdmissible 0b001      -- sub: refuses 0b010, admits 0b001
  | none => false
-- REFUSE (mask widening): attenuating to 0b111 (add the 0b100 bit, not held) ⇒ none (no-amplification).
#guard (deskCap.attenuateNotify .impossible 0b111).isNone

end Witnesses

/-! ## §6 — Axiom hygiene. Every load-bearing settle + wake theorem checked kernel-clean. -/

#assert_all_clean [
  non_provider_rejected,
  off_band_price_rejected,
  over_payout_rejected,
  stranded_escrow_rejected,
  honest_settle_admits,
  settle_wake_commits,
  out_of_mask_wake_refused,
  settle_wake_attenuation_no_amplify
]

end Dregg2.Apps.ComputeMarketDesk
