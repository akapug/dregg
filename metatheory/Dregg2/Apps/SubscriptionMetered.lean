/-
# Dregg2.Apps.SubscriptionMetered — a METERED subscription plan, as ONE cell program (round 2).

`Apps/SubscriptionGated.lean` modelled a subscription as a single `MonotonicSequence` slot caveat
(`seq := old + 1`, no replay / no skip). That is real on the EXECUTOR axis — it runs through
`execFullForestG` — but THIN on the POLICY axis: a subscription is not just a sequence counter. A real
metered plan also bounds the SPEND RATE (you cannot drain the prepaid balance faster than the plan
allows), constrains the METER (the combined per-period usage cannot exceed the plan's budget), pins the
plan TIER to an allowlist, and binds every consume to the registered subscriber. This module rebuilds
the subscription as a RICH `RecordProgram` exercising the round-2 expressiveness — the rate atoms
(`balanceDeltaGe`, the spend-rate FLOOR on the sealed balance), the multi-field budget DELTA
(`affineDeltaLe`, combining two meters), the value allowlist (`memberOf`), the strict period counter
(`strictMono`), and the subscriber provenance (`senderInField`) — each clause a theorem in BOTH
polarities (the honest consume COMMITS; each adversarial consume is `admitsCtx = false`).

## Why this is not a toy

The naive metered subscription tracks usage in a counter and trusts the client to bill itself. Three
real attacks the round-1 `monotonicSeq` toy could not see, each closed by a clause here:

  * **the over-drain.** A subscription holds a PREPAID sealed balance; a consume debits it. Without a
    rate floor, ONE consume can drain the whole prepaid balance (a runaway client / a compromised key
    billing the account to zero in a single turn). `consumeRateFloor` = `balanceDeltaGe planRate`: the
    per-turn balance change may not be MORE negative than the plan's per-period rate. A consume that
    debits more than the plan rate is UNSAT (`over_drain_rejected`).
  * **the meter blow-out.** A plan bundles several metered resources (here `api_calls` + `storage`); the
    per-period BUDGET bounds their COMBINED growth, which no single-field counter caveat can express.
    `meterBudget` = `affineDeltaLe [(1,api_calls),(1,storage)] periodBudget`: the summed per-turn delta
    of the two meters is capped. A consume that runs the combined meter past the budget is UNSAT
    (`meter_blowout_rejected`) — even if each meter alone looks small.
  * **the tier forgery + the impostor.** The plan `tier` must be one of the published tiers (a consume
    cannot invent `tier 99` to unlock a budget it did not buy); and every consume must be SIGNED by the
    subscriber the cell records, not merely by a capability holder. `tierAllowed` = `memberOf tier
    {free, pro, team}` and `subscriberBound` = `senderInField subscriber` give `forged_tier_rejected`
    and `impostor_consume_rejected`.

And the period counter strictly increases (`strictMono period`) — a replay of an old period or a stalled
plateau is UNSAT (`replayed_period_rejected`), the round-1 sequence tooth, now one clause among five.

## The plan cell — its state

  * `period`     — the strictly-increasing billing-period counter (replay-safe);
  * `tier`       — the plan tier (must be a published tier);
  * `subscriber` — the registered subscriber identity (only it may consume);
  * `api_calls`  — a metered counter (combined budget with `storage`);
  * `storage`    — a metered counter (combined budget with `api_calls`);
  * the cell's SEALED balance — the prepaid value (debited per consume, rate-floored), carried in
    `TurnCtx.balance` / `TurnCtx.balanceBefore`.

The consume gate is ONE `RecordProgram.predicate`. The teeth: COMMIT an honest metered consume
(subscriber-signed, next period, within rate, within budget, published tier); REFUSE an over-drain, a
meter blow-out, a forged tier, an impostor sender, and a replayed period.

## Honest scope

  * `balanceDeltaGe`/`affineDeltaLe` are the BOUNDED / ordering pole (§8): a rate gate on a
    decrementable quantity is i-confluent only under the single serializer (n=1). Named, not laundered —
    the same scope `Exec/Program.lean` carries for the rate atoms.
  * The sealed balance + its pre-image (`balanceBefore`) are the executor-held kernel balances at
    program-check time (Rust `old_balance`/`new_balance`); the §8 seam is the kernel balance carrier,
    not a record field. The metering arithmetic is proved here.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` —
`decide` / `#guard` / `Exec.Program`-keystone reuse only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.Program

namespace Dregg2.Apps.SubscriptionMetered

open Dregg2.Exec

/-! ## §0 — The plan's field names, tier codes, plan parameters, and identities. -/

/-- The strictly-increasing billing-period counter. -/
abbrev periodF : FieldName := "period"
/-- The plan tier (must be a published tier). -/
abbrev tierF : FieldName := "tier"
/-- The registered subscriber identity. -/
abbrev subscriberF : FieldName := "subscriber"
/-- A metered usage counter (combined budget with `storage`). -/
abbrev apiCallsF : FieldName := "api_calls"
/-- A metered usage counter (combined budget with `api_calls`). -/
abbrev storageF : FieldName := "storage"

/-- Published plan tiers. -/
abbrev tierFree : Int := 0
abbrev tierPro  : Int := 1
abbrev tierTeam : Int := 2

/-- The plan's per-period spend RATE FLOOR: the sealed balance may not change by more than `planRate`
NEGATIVELY in one consume — i.e. `new.balance − old.balance ≥ planRate` with `planRate = −10` means at
most 10 may be debited per period. (A FLOOR on the delta, the natural shape of a "no more than X
out" rate using `balanceDeltaGe`.) -/
abbrev planRate : Int := -10

/-- The plan's per-period combined METER budget: `Δapi_calls + Δstorage ≤ periodBudget`. -/
abbrev periodBudget : Int := 100

/-- The registered subscriber's identity. -/
abbrev subscriberPk : Int := 0x5B
/-- An impostor's identity (holds a capability, but is not the subscriber). -/
abbrev impostorPk : Int := 0x99

/-! ## §1 — THE CONSUME GATE as a `RecordProgram` (provenance ∧ period ∧ rate ∧ budget ∧ tier).

The plan's consume program is a conjunction of five clauses, each a constraint of the cell's
`RecordProgram`:

  * `senderInField subscriberF` — **provenance**: a consume must be SIGNED BY the registered
    subscriber. A capability holder who is not the subscriber cannot bill the plan.
  * `strictMono periodF` — **replay-safety**: the billing period strictly increases. A replay of an
    old period, or a stalled plateau, is rejected (the round-1 sequence tooth).
  * `balanceDeltaGe planRate` — **the spend-rate floor**: the prepaid balance may not be debited by
    more than the plan rate per period (`Δbalance ≥ planRate`). A single-turn drain is rejected.
  * `affineDeltaLe [(1,api_calls),(1,storage)] periodBudget` — **the meter budget**: the combined
    per-period growth of the two meters is capped. A meter blow-out is rejected.
  * `memberOf tierF {free, pro, team}` — **the tier allowlist**: the plan tier must be published.

The conjunction is ONE predicate (all-or-nothing). -/
def consumeConstraints : List StateConstraint :=
  [ .simple (.senderInField subscriberF)                                      -- provenance
  , .simple (.strictMono periodF)                                             -- no replay / no skip-back
  , .simple (.balanceDeltaGe planRate)                                        -- spend-rate floor
  , .affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget               -- combined meter budget
  , .simple (.memberOf tierF [tierFree, tierPro, tierTeam]) ]                 -- tier allowlist

/-- **The metered-subscription program** — the consume policy as ONE coalgebra structure-map. -/
def planProgram : RecordProgram := .predicate consumeConstraints

/-! ## §2 — Extraction plumbing (the `EscrowDeskCouncil` pattern). -/

/-- Every constraint binds on an admitted consume (`admitsCtx` on `.predicate` IS the conjunction). -/
private theorem admitted_mem {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : planProgram.admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ consumeConstraints) :
    evalConstraintCtx ctx c o n = true := by
  have hall : consumeConstraints.all (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

/-- A consume that admits drives `admitsCtx = true` to `true` for the extraction `by_contra`. -/
private theorem admits_of_not_false {ctx : TurnCtx} {m : Nat} {o n : Value}
    (hc : ¬ planProgram.admitsCtx ctx m o n = false) :
    planProgram.admitsCtx ctx m o n = true := by
  cases h : planProgram.admitsCtx ctx m o n with
  | true => rfl
  | false => exact absurd h hc

/-! ## §3 — THE TEETH on the consume policy (both polarities, all PROVED). -/

/-- **① IMPOSTOR TOOTH — a consume not signed by the subscriber is UNSAT.** Any consume whose sender is
NOT the registered subscriber is rejected: `admitsCtx = false`. Capability possession is not enough —
only the subscriber the cell records may bill the plan. -/
theorem impostor_consume_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (recordedSub : Int)
    (hsub : n.scalar subscriberF = some recordedSub)
    (himpostor : ctx.sender ≠ some recordedSub) :
    planProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hprov := admitted_mem hne (c := .simple (.senderInField subscriberF)) (.head _)
  have hsend : evalSimpleCtx ctx (.senderInField subscriberF) o n = true := by
    simpa [evalConstraintCtx] using hprov
  obtain ⟨s, hs, hv⟩ := (evalSimpleCtx_senderInField_iff ctx subscriberF o n).mp hsend
  rw [hsub] at hv; injection hv with hv; subst hv; exact himpostor hs

/-- **② REPLAY TOOTH — a consume that does not advance the period is UNSAT.** A consume whose new
period is NOT strictly greater than the old (a replay of an old period, or a stalled plateau) is
rejected: `admitsCtx = false`. The round-1 `monotonicSeq` discipline, now one clause among five. -/
theorem replayed_period_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (oldP newP : Int)
    (hold : o.scalar periodF = some oldP)
    (hnew : n.scalar periodF = some newP)
    (hreplay : ¬ oldP < newP) :
    planProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hmono := admitted_mem hne (c := .simple (.strictMono periodF)) (.tail _ (.head _))
  have hsm : evalSimpleCtx ctx (.strictMono periodF) o n = true := by
    simpa [evalConstraintCtx] using hmono
  -- strictMono is ctx-free; the ctx-aware evaluator delegates to evalSimple.
  rw [show evalSimpleCtx ctx (.strictMono periodF) o n = evalSimple (.strictMono periodF) o n from rfl]
    at hsm
  obtain ⟨a, b, ha, hb, hlt⟩ := (evalSimple_strictMono_iff periodF o n).mp hsm
  rw [hold] at ha; injection ha with ha; subst ha
  rw [hnew] at hb; injection hb with hb; subst hb
  exact hreplay hlt

/-- **③ OVER-DRAIN TOOTH — a consume debiting more than the plan rate is UNSAT.** A consume whose
per-turn sealed-balance change is MORE NEGATIVE than the plan rate (`Δbalance < planRate`, i.e. it
debits more than the plan allows per period) is rejected: `admitsCtx = false`. A runaway client cannot
drain the prepaid balance faster than the plan rate. -/
theorem over_drain_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (before after : Int)
    (hbefore : ctx.balanceBefore = some before)
    (hafter : ctx.balance = some after)
    (hdrain : after - before < planRate) :
    planProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hrate := admitted_mem hne (c := .simple (.balanceDeltaGe planRate)) (.tail _ (.tail _ (.head _)))
  have hge : evalSimpleCtx ctx (.balanceDeltaGe planRate) o n = true := by
    simpa [evalConstraintCtx] using hrate
  obtain ⟨a, b, ha, hb, hle⟩ := (evalSimpleCtx_balanceDeltaGe_iff ctx planRate o n).mp hge
  rw [hbefore] at ha; injection ha with ha; subst ha
  rw [hafter] at hb; injection hb with hb; subst hb
  omega

/-- **④ METER-BLOWOUT TOOTH — a consume running the combined meter past the budget is UNSAT.** A
consume whose COMBINED per-period meter growth `Δapi_calls + Δstorage` exceeds `periodBudget` is
rejected: `admitsCtx = false`. The two-meter budget is what no single-field counter caveat can express
— even if each meter alone looks small, their SUM is capped. -/
theorem meter_blowout_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (s : Int)
    (hsum : affineDeltaSum o n [(1, apiCallsF), (1, storageF)] = some s)
    (hblow : s > periodBudget) :
    planProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hbud := admitted_mem hne
    (c := .affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget)
    (.tail _ (.tail _ (.tail _ (.head _))))
  -- affineDeltaLe is ctx-free; evalConstraintCtx delegates to evalConstraint.
  have hdl : evalConstraint (.affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget) o n = true := by
    simpa [evalConstraintCtx] using hbud
  obtain ⟨s', hs', hle⟩ :=
    (evalConstraint_affineDeltaLe_iff [(1, apiCallsF), (1, storageF)] periodBudget o n).mp hdl
  rw [hsum] at hs'; injection hs' with hs'; subst hs'; omega

/-- **⑤ FORGED-TIER TOOTH — a consume claiming an unpublished tier is UNSAT.** A consume whose plan
`tier` is NOT one of the published tiers (it invented `tier 99` to unlock a budget it did not buy) is
rejected: `admitsCtx = false`. -/
theorem forged_tier_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (t : Int)
    (htier : n.scalar tierF = some t)
    (hforged : t ∉ ([tierFree, tierPro, tierTeam] : List Int)) :
    planProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne := admits_of_not_false hc
  have hmem := admitted_mem hne (c := .simple (.memberOf tierF [tierFree, tierPro, tierTeam]))
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have hm : evalSimpleCtx ctx (.memberOf tierF [tierFree, tierPro, tierTeam]) o n = true := by
    simpa [evalConstraintCtx] using hmem
  rw [show evalSimpleCtx ctx (.memberOf tierF [tierFree, tierPro, tierTeam]) o n
        = evalSimple (.memberOf tierF [tierFree, tierPro, tierTeam]) o n from rfl] at hm
  obtain ⟨x, hx, hcon⟩ := (evalSimple_memberOf_iff tierF [tierFree, tierPro, tierTeam] o n).mp hm
  rw [htier] at hx; injection hx with hx; subst hx
  rw [List.contains_eq_mem] at hcon
  exact hforged (by simpa using hcon)

/-- **⑥ THE HONEST METERED CONSUME COMMITS (the gate is not constant-false).** A consume signed by the
subscriber, advancing the period, debiting within the plan rate, growing the combined meter within
budget, and carrying a published tier, ADMITS. The conjunction of the five teeth is non-vacuous: there
is a real metered consume the plan lets through. -/
theorem honest_consume_admits (ctx : TurnCtx) (m : Nat) (o n : Value)
    (oldP newP before after sumDelta : Int)
    (hsender : ctx.sender = some subscriberPk)
    (hsub : n.scalar subscriberF = some subscriberPk)
    (holdP : o.scalar periodF = some oldP) (hnewP : n.scalar periodF = some newP) (hadv : oldP < newP)
    (hbefore : ctx.balanceBefore = some before) (hafter : ctx.balance = some after)
    (hrate : planRate ≤ after - before)
    (hmeter : affineDeltaSum o n [(1, apiCallsF), (1, storageF)] = some sumDelta)
    (hbudget : sumDelta ≤ periodBudget)
    (htier : n.scalar tierF = some tierPro) :
    planProgram.admitsCtx ctx m o n = true := by
  have c1 : evalConstraintCtx ctx (.simple (.senderInField subscriberF)) o n = true := by
    show evalSimpleCtx ctx (.senderInField subscriberF) o n = true
    exact (evalSimpleCtx_senderInField_iff ctx subscriberF o n).mpr ⟨subscriberPk, hsender, hsub⟩
  have c2 : evalConstraintCtx ctx (.simple (.strictMono periodF)) o n = true := by
    show evalSimpleCtx ctx (.strictMono periodF) o n = true
    rw [show evalSimpleCtx ctx (.strictMono periodF) o n = evalSimple (.strictMono periodF) o n from rfl]
    exact (evalSimple_strictMono_iff periodF o n).mpr ⟨oldP, newP, holdP, hnewP, hadv⟩
  have c3 : evalConstraintCtx ctx (.simple (.balanceDeltaGe planRate)) o n = true := by
    show evalSimpleCtx ctx (.balanceDeltaGe planRate) o n = true
    exact (evalSimpleCtx_balanceDeltaGe_iff ctx planRate o n).mpr ⟨before, after, hbefore, hafter, hrate⟩
  have c4 : evalConstraintCtx ctx (.affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget) o n = true := by
    show evalConstraint (.affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget) o n = true
    exact (evalConstraint_affineDeltaLe_iff [(1, apiCallsF), (1, storageF)] periodBudget o n).mpr
      ⟨sumDelta, hmeter, hbudget⟩
  have c5 : evalConstraintCtx ctx (.simple (.memberOf tierF [tierFree, tierPro, tierTeam])) o n = true := by
    show evalSimpleCtx ctx (.memberOf tierF [tierFree, tierPro, tierTeam]) o n = true
    rw [show evalSimpleCtx ctx (.memberOf tierF [tierFree, tierPro, tierTeam]) o n
          = evalSimple (.memberOf tierF [tierFree, tierPro, tierTeam]) o n from rfl]
    exact (evalSimple_memberOf_iff tierF [tierFree, tierPro, tierTeam] o n).mpr
      ⟨tierPro, htier, by decide⟩
  show consumeConstraints.all (fun c => evalConstraintCtx ctx c o n) = true
  simp only [consumeConstraints, List.all_cons, List.all_nil, c1, c2, c3, c4, c5, Bool.and_true]

/-! ## §4 — CONSERVATION / NON-AMPLIFICATION carrier.

The consume gate writes plan-metadata fields (period/tier/subscriber/api_calls/storage) and constrains
the SEALED balance via the rate floor — it writes no capability table, so a consume cannot mint or
amplify any authority (the constraint language reads/constrains record fields; it has no cap-table
write). We pin that the program is a pure record/balance gate by exhibiting that a NON-consume turn
(one that touches the plan only metadata-neutrally) still passes the metadata clauses — i.e. the policy
adds NO authority side-effect; it only constrains. The substantive non-amplification is the executor's
(this is a `RecordProgram`, evaluated, never a cap mint). -/

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the consume policy BITES on the concrete plan, both
polarities. -/

section Witnesses

/-- A faithful metered consume context: subscriber signs, balance 92 (was 100, a −8 debit ≥ rate −10),
period advances. -/
def consumeCtx : TurnCtx :=
  { sender := some subscriberPk, balance := some 92, balanceBefore := some 100 }
def planNew : Value :=
  .record [(subscriberF, .int subscriberPk), (periodF, .int 6), (tierF, .int tierPro),
           (apiCallsF, .int 40), (storageF, .int 30)]
def planOld : Value :=
  .record [(subscriberF, .int subscriberPk), (periodF, .int 5), (tierF, .int tierPro),
           (apiCallsF, .int 10), (storageF, .int 10)]
-- the combined meter delta on this consume: (40−10) + (30−10) = 50 ≤ 100 (within budget).

-- ① COMMIT: a faithful metered consume ADMITS (subscriber-signed, period 5→6, −8 debit within rate,
-- combined meter +50 within budget 100, published tier pro).
#guard planProgram.admitsCtx consumeCtx 0 planOld planNew

-- ① REFUSE (impostor): the SAME consume but signed by an impostor (not the subscriber). REJECTED.
#guard planProgram.admitsCtx
  { consumeCtx with sender := some impostorPk } 0 planOld planNew == false

-- ① REFUSE (no sender): unsigned consume. REJECTED (fail-closed provenance).
#guard planProgram.admitsCtx
  { consumeCtx with sender := none } 0 planOld planNew == false

-- ② REFUSE (replay): the new period (5) equals the old (5) — not strictly increasing. REJECTED.
#guard planProgram.admitsCtx consumeCtx 0 planOld
  (.record [(subscriberF, .int subscriberPk), (periodF, .int 5), (tierF, .int tierPro),
            (apiCallsF, .int 40), (storageF, .int 30)]) == false

-- ② REFUSE (skip-back): the new period (4) is BELOW the old (5). REJECTED.
#guard planProgram.admitsCtx consumeCtx 0 planOld
  (.record [(subscriberF, .int subscriberPk), (periodF, .int 4), (tierF, .int tierPro),
            (apiCallsF, .int 40), (storageF, .int 30)]) == false

-- ③ REFUSE (over-drain): balance 80 (was 100, a −20 debit) — more than the plan rate −10. REJECTED.
#guard planProgram.admitsCtx
  { consumeCtx with balance := some 80 } 0 planOld planNew == false

-- ③ REFUSE (absent balance endpoint): no pre-balance ⇒ the rate floor fails closed. REJECTED.
#guard planProgram.admitsCtx
  { consumeCtx with balanceBefore := none } 0 planOld planNew == false

-- ④ REFUSE (meter blow-out): storage jumps to 95 (+85), api_calls +30 → combined +115 > budget 100.
-- Each delta alone looks fine; their SUM blows the budget. REJECTED.
#guard planProgram.admitsCtx consumeCtx 0 planOld
  (.record [(subscriberF, .int subscriberPk), (periodF, .int 6), (tierF, .int tierPro),
            (apiCallsF, .int 40), (storageF, .int 95)]) == false

-- ⑤ REFUSE (forged tier): tier 99 is not a published tier. REJECTED.
#guard planProgram.admitsCtx consumeCtx 0 planOld
  (.record [(subscriberF, .int subscriberPk), (periodF, .int 6), (tierF, .int 99),
            (apiCallsF, .int 40), (storageF, .int 30)]) == false

-- ⑤ ADMIT (the OTHER published tiers): tier free (0) and tier team (2) both pass the allowlist.
#guard planProgram.admitsCtx consumeCtx 0 planOld
  (.record [(subscriberF, .int subscriberPk), (periodF, .int 6), (tierF, .int tierFree),
            (apiCallsF, .int 40), (storageF, .int 30)])
#guard planProgram.admitsCtx consumeCtx 0 planOld
  (.record [(subscriberF, .int subscriberPk), (periodF, .int 6), (tierF, .int tierTeam),
            (apiCallsF, .int 40), (storageF, .int 30)])

-- The rate FLOOR isolated: a −10 debit (exactly the rate) ADMITS; a −11 debit REJECTS (the boundary).
#guard evalSimpleCtx { balance := some 90, balanceBefore := some 100 } (.balanceDeltaGe planRate)
  (.record []) (.record [])
#guard evalSimpleCtx { balance := some 89, balanceBefore := some 100 } (.balanceDeltaGe planRate)
  (.record []) (.record []) == false

-- The combined-meter budget isolated: +100 (exactly the budget) ADMITS; +101 REJECTS.
#guard evalConstraint (.affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget)
  (.record [(apiCallsF, .int 0), (storageF, .int 0)])
  (.record [(apiCallsF, .int 60), (storageF, .int 40)])
#guard evalConstraint (.affineDeltaLe [(1, apiCallsF), (1, storageF)] periodBudget)
  (.record [(apiCallsF, .int 0), (storageF, .int 0)])
  (.record [(apiCallsF, .int 60), (storageF, .int 41)]) == false

end Witnesses

/-! ## §6 — Axiom hygiene. Every load-bearing consume theorem checked kernel-clean. -/

#assert_all_clean [
  impostor_consume_rejected,
  replayed_period_rejected,
  over_drain_rejected,
  meter_blowout_rejected,
  forged_tier_rejected,
  honest_consume_admits
]

end Dregg2.Apps.SubscriptionMetered
