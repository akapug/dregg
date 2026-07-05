# The Replenishing Budget — one primitive under metering, settlement, and escrow

Status: design sketch (2026-06-30). Scope: DreggNet's control plane (`control/`,
`webapp/`, `durable/`) grounded on a dregg cell primitive. This unifies three
billing/contention surfaces the red-team passes keep re-finding as separate gaps
(SRV-3 metering, hot-account settlement serialization, host-API escrow griefing)
onto a single attenuable cell.

> One sentence: a **replenishing budget** is a `(budget, period, replenishment-queue)`
> object that meters *actual* consumption against a ceiling that refills *lazily up to
> now* — the seL4 MCS scheduling-context shape, realized as a sovereign, forge-detectable
> dregg cell rather than a side-counter in the control plane's RAM.

---

## 0. The primitive already half-exists — don't reinvent it

dregg ships `cell/src/allowance.rs` (the **rate-limited allowance**, doc
`docs/deos/RATE-LIMITED-ALLOWANCE.md`): a beneficiary may spend up to
`limit_per_epoch` of an asset per `epoch_length`-block epoch, the spend cursors bound
into the Poseidon2 commitment so headroom is *computed, not trusted*. That is exactly
the dregg-native answer to the primitive this document designs. The replenishing
budget is the **generalization** of that allowance along one axis: replacing the
single discrete "reset `spent_this_epoch` to 0 on an epoch crossing" with a **refill
queue** of `{at_block, amount}` entries drained lazily up to `now` — the seL4 MCS
sporadic-server move. Where `allowance.rs` does *reset-per-epoch*, the replenishing
budget does *per-chunk replenishment over a sliding window*; the allowance is the
`refill_max = 1` special case.

So the work here is not greenfield: it is (a) widen the allowance cell's refill model
from one-reset-per-epoch to a bounded refill queue, and (b) put **three control-plane
uses** on that one cell. The verification skeleton (`StandingObligation.lean`'s
committed `next_due` cursor under the reused `StrictMonotonic` law + `root_binds_get`
anti-ghost) already exists to copy.

### The three reference points on one axis

All three "don't serialize on a hot balance, bound the *rate*" mechanisms we draw on:

| source | mechanism | reconciliation | bound |
|---|---|---|---|
| seL4 MCS sched-context | `(budget, period)` + refill queue `{rTime,rAmount}` | lazy, at schedule time roll the queue forward to `now` | sporadic-server: ≤ `budget` per `period` sliding window |
| Hellas Stingray bounded-counter | N per-validator LOCAL budgets, spent without coordination | after-the-fact: `ResetBudget` + signed `BudgetCertificate`s | Byzantine ceiling `η = (f+1)/(2f+1)` per validator, `n ≥ 3f+1` |
| dregg `allowance.rs` | committed epoch budget, cursors in the heap root | discrete reset on a *derived* (not asserted) epoch crossing | `spent_baseline + amount ≤ limit_per_epoch`, forge-detectable |

The dregg one is the only point with a soundness obligation, and it is the one we
build on; the other two are the model (MCS) and the parallelism pattern (Stingray)
we fold in.

---

## 1. The cell shape

A replenishing budget is a heap-committed cell program (the house-capacity template:
state in sorted-Poseidon2 `set_heap`/`compute_heap_root`, folded into the canonical
commitment). Its sealed **terms** and its **cursors** live in a reserved heap
collection.

```
Terms  (sealed at open, never mutated; one digest binds them):
    asset          : CellId        # what is metered/spent
    budget         : i64           # the ceiling — max outstanding consumption in a window
    period         : i64           # the GRANULARITY of replenishment (blocks), NOT a sale window
    refill_amount  : i64           # how much each matured refill returns (default = budget)
    refill_max     : u16           # bound on the live refill queue length (MCS refill_max)
    start          : i64           # genesis block, so the schedule is absolute/derivable

Cursors (committed; the load-bearing witnessed state):
    consumed       : i64           # total drawn against this budget, ever (monotone)
    refilled       : i64           # total returned by matured refills, ever (monotone)
    refill_head    : i64           # block of the oldest still-pending refill (queue front)
    queue_digest   : Field         # commitment to the pending refill queue {at_block, amount}*
```

`outstanding(now) = consumed − refilled_up_to(now)`, where `refilled_up_to` drains the
refill queue of every entry with `at_block ≤ now` (computed at use time, never pushed
on a timer). **Headroom** is `budget − outstanding(now)`; a draw of `amount` is
admissible iff `amount ≤ headroom`.

Two committed monotone totals (`consumed`, `refilled`) rather than one net counter:
the same anti-ghost discipline as `allowance.rs`'s independent `spent_total` — a
forged-*down* net counter is caught because the monotone witnesses disagree with the
recomputed `consumed − refilled`.

### The operations

```
open_budget(terms)              -> seals terms, cursors = 0, empty queue
draw(amount, at_block)          -> charge ACTUAL consumption against headroom-at-now;
                                   on full consumption, SCHEDULE a refill at at_block+period
mature(at_block)                -> drain the refill queue up to at_block into `refilled`
                                   (lazy, event-driven; idempotent; the MCS unblock-check)
headroom_at(at_block)           -> read-only, recomputes outstanding-at-now (no mutation)
attenuate(sub_budget, sub_period) -> mint a CHILD budget cap (sub_budget ≤ budget, ...)
```

The verification core — the single function both the honest `draw` and every forge
reject run through — is `check_draw(state, amount, at_block) -> Result<NewCursors, _>`,
exactly mirroring `allowance.rs::check_spend` (non-vacuity by construction: it is
proven RED-on-break by stubbing it to always-accept). Its logic:

1. terms well-formed (`0 < budget`, `0 < period`, `refill_amount > 0`, `refill_max ≥ 1`);
2. `at_block ≥ refill_head` (no backdated draw — the `StaleEpoch` analog);
3. `outstanding = consumed − refilled_up_to(at_block)` (refills matured up to now);
4. `amount > 0` and `outstanding + amount ≤ budget` else `ExceedsCeiling`;
5. the new refill (if the draw consumes a chunk) is scheduled at `at_block + period` —
   **early refill is structurally inexpressible**, because the refill block is *derived*
   from `at_block`, never supplied by the caller (the same property that makes the
   allowance's epoch un-forgeable).

### Why `period` is a granularity knob, not a wall-clock sale

This is the load-bearing reframing for the metering use. In seL4 MCS, crossing into
the next period does not "sell" a fresh full budget at the boundary; each consumed
chunk independently becomes eligible again exactly `period` later, enforcing a
`budget/period` bandwidth ceiling over a *sliding* window. Translated: dregg never
commits to "we sell wall-clock time." `period` only sets how finely consumption is
billed and how fast headroom returns. Drop tick-counting entirely — consumption is
charged against *measured* usage, and `period` is the accounting granularity. A
control plane that stalls for an hour and then resumes does not over- or under-bill;
it `mature`s the queue up to `now` and the arithmetic is identical to a plane that
ticked every block.

---

## 2. Use A — Metering (red-team SRV-3): the lease budget IS the cell

**Today.** `control/src/server.rs::meter_period` bills "one period per sweep tick"
(`periods_metered + 1`), with no relation to elapsed wall-clock; SRV-3's independent
idle reaper (`reap_idle`) is a safety net bolted on because a stalled driver otherwise
holds a backend unbilled. The persistent-server lease budget
(`budget_units`/`per_period_units`) and the `BandwidthMeter`'s funded byte budget are
two *different* ad-hoc counters.

**On the primitive.** The lease's compute budget and the site's bandwidth budget both
*become* replenishing-budget cells:

- compute: `Terms { asset: $DREGG, budget = budget_units, period = the billing
  granularity, refill_amount = per_period_units, ... }`. A metering pass is
  `mature(now)` then `draw(measured_units, now)` — it charges *actual* consumption
  (CPU-seconds the backend reports, not sweep-tick count). The "uptime period" stops
  being a tick; it is a `draw` against the headroom the budget has refilled up to
  `now`. `meter_period`'s `periods_metered` cursor folds into the cell's `consumed`.

- bandwidth: the `BandwidthMeter`'s funded byte budget is already this shape (HB-1
  gave it `set_budget`/`would_exceed_budget`/`add_budget`). `set_budget` = `open` /
  top-up; the in-band serving gate is exactly `headroom_at(now) ≥ body.len()`.

The SRV-3 finding dissolves: there is no "stalled driver holds a backend unbilled"
window, because billing is `draw`-against-measured-consumption rolled lazily up to
`now`, not a count of how many times an external loop ran. The independent reaper
stays as a *liveness* tooth (reap a backend whose owner stopped funding), but it is no
longer load-bearing for *correctness of the bill*.

**Migration.** Incremental, behind the existing seams: (1) replace
`ServerRecord.{periods_metered, budget_units, per_period_units}` reads with a
budget-cell handle while keeping the durable `(server_id, period)` settlement key as
the `draw` nullifier (exactly-once is preserved — a `draw` is keyed, replays are inert);
(2) feed `draw` the backend's *measured* consumption instead of a constant
`per_period_units` (the SRV-3 "remaining half" the partial fix explicitly deferred —
"per-tick billing recomputed as elapsed-wall-clock catch-up" — this is its principled
form); (3) `webapp`'s `BandwidthMeter` already matches and needs only the queue
generalization for lazy refill.

---

## 3. Use B — Settlement contention (the hot-account bottleneck)

**The problem.** A popular provider receiving thousands of credits serializes on one
balance: every settler that pays it contends the same conserving-ledger account. The
durable settlement rail is exactly-once per `(lease, period)`, but N parallel settlers
writing the *same beneficiary balance* serialize.

**On the primitive — the Stingray split.** Give each settler a LOCAL replenishing
budget *over the hot account* that it spends without coordinating, periodically
reconciled — the Hellas bounded-counter pattern (`bounded_counter.rs`). Concretely:

- the hot account mints, by `attenuate`, one child budget cell per settler:
  `attenuate(sub_budget = η · balance / N, period)`, where `η = (f+1)/(2f+1)` is the
  Stingray ceiling under `n ≥ 3f+1` — a fixed fraction of the true balance, never the
  whole thing, so even `f` malicious settlers spending their full local budget cannot
  over-draw the parent;
- a settler's `draw` against its *own* child cell needs no lock on the parent;
- reconciliation is the MCS `mature` + a periodic fold: each settler emits a signed
  spend certificate (the `BudgetCertificate` shape — `validator, total_spent,
  transactions, signature`), the parent verifies the set (rejecting unknown/duplicate
  signers, `verify_budget_certificates`), folds `Σ total_spent` into the parent's
  `consumed`, and re-attenuates fresh child budgets for the next window.

This is the cap-attenuation lattice doing the work the Stingray protocol does by hand:
a child budget IS an attenuated parent budget (`sub_budget ≤ budget`), so "N settlers
don't contend" is just "N children of one cap, each draws locally."

**Migration.** `durable/src/settle.rs`'s `ConservingLedger::settle` stays the
conserving floor (Σδ=0 in one critical section); the contention fix is a layer *above*
it: settlers hold child-budget caps and settle against those, with a per-window
`fold_certificates` reconciliation that does the one serialized write. The Byzantine
ceiling `η` is a config knob with `f = 0` (trusted operator set) collapsing to "each
settler gets `balance/N`, reconciled each window" — the n=1 strong-local case.

---

## 4. Use C — The escrow bond (host-API griefing: who eats a failed paid call)

**The problem (red-team Surface 4 LOW + the broader host-API).** A paid `invoke` runs
the provider's handler before the conserving charge; a handler that does costly work
then hits a guest-controllable failure is never charged — provider compute griefing.
Symmetrically, a consumer who pre-pays a call the provider never honors wants its money
back. Who bonds the risk?

**On the primitive — the Hellas marketplace escrow, over existing dregg cells.** dregg
already has the two capacities this needs, proven and `#assert_axioms`-clean:
`SealedEscrow.lean` (a two-leg escrow with `deposit`/`settle`, the one-shot
`replay_rejected` + `over_claim_rejected` teeth) and `StandingObligation.lean` (the
recurring duty with the `next_due` cursor). The marketplace flow maps directly:

- **`SettleDirectly`** (Hellas `transactions.rs`: a 2-of-2 multisig fast-path) — both
  parties sign, no escrow, no bond. The trusted/curated path: a known provider, an
  interactive call, settle on success. This is the host-API's current happy path; keep
  it for curated providers.

- **`PostJob → ClaimJob → CommitResult → FinalizeJob`** (Hellas `JobEscrow`,
  `JobStatus { Posted, Claimed, Committed, Finalized, Aborted }`) — the permissionless
  path. The consumer `PostJob` **locks the payment** in a `SealedEscrow` leg; the
  provider `ClaimJob` **locks a slashable bond** (its own `SealedEscrow` leg, the
  `provider_bond_locked` field) — this is the anti-griefing stake; `CommitResult`
  records the result hash; `FinalizeJob` releases payment to the provider **after a
  challenge period** (`finalization_delay`, default 50 blocks). A no-show or a
  bad result lets the consumer `AbortJob` past the deadline and **slash the bond**.

The replenishing budget enters here as the **bond's funding source and the consumer's
spend ceiling**: a consumer's `PostJob` is a `draw` against its replenishing budget (so
a runaway agent cannot post unbounded jobs — its rate is bounded); the provider's bond
is itself a budget cell whose slash is a forced `draw`. The challenge window is a
`StandingObligation`-style `next_due` gate (`FinalizeJob` admissible only at
`block ≥ finalize_after`, the `behind_schedule`/`early_discharge` teeth).

**Migration.** This is the heaviest of the three and the least urgent (the host-API
*substantially holds* today — charge-before-effect, cap-gate, receipt chain all sound).
Land it as a new house capacity reusing `SealedEscrow` + `StandingObligation`: a
`MarketplaceJob` cell whose state machine is `JobStatus`, whose payment+bond legs are
`SealedEscrow` deposits, whose finalize gate is an obligation cursor. The LOW host-API
fix the red-team named (charge the price for an admitted call regardless of handler
success) is the `SettleDirectly` discipline applied inline; the full escrow machine is
for the permissionless, untrusted-provider case.

---

## 5. Verifiability — the house-capacity template

Each of the three uses is verified the same way (the `HOUSE-CAPACITY-FRAMEWORK.md`
five-part object), reusing already-proven bases — **no new circuit math, no VK bump**:

1. **cell** — the heap-committed budget program above (`cell/src/budget.rs`, a widening
   of `allowance.rs`); state in sorted-Poseidon2, folded into the canonical commitment.
2. **invariant** — "outstanding never exceeds budget; refills mature only on a derived
   block, never early; the monotone `consumed`/`refilled` witnesses agree with the
   recomputed net."
3. **Lean rung — by reuse** — copy `StandingObligation.lean`'s skeleton: the refill
   schedule is the `cursorAt`/`expectedPeriod` derived clock; the `consumed`/`refilled`
   monotones ride the `StrictMonotonic` law; `root_binds_get` is the anti-ghost
   (`forged_cursor_moves_root`). Teeth: `over_draw_rejected`, `early_refill_rejected`
   (= `early_discharge_rejected`), `backdated_draw_rejected` (= `StaleEpoch`),
   `forged_down_counter_caught` (the independent monotone), `draw_binds_in_root`.
4. **forge-detector** — the executor `check_draw`, the EXECUTOR IMAGE of the Lean rung,
   with both-polarity `#guard`s.
5. **wiring** — `tests::budget_invariant_matches_lean_rung` tying the Rust check to the
   Lean statement.

**The one named seam** (per the house-capacities discipline): the circuit/light-client
**weld** — binding "never over-drew its rate" into the EffectVM so a LIGHT CLIENT, not
just a re-executing validator, witnesses it. This is VK-affecting and tracked exactly
like the other capacities' welds (`SettleEscrowSatDescriptor.lean` is the worked
example: a satisfying trace FORCES the gate, emitted into the staged registry with no
live routing until the deliberate VK epoch). The executor tooth is real and
load-bearing today; the circuit tooth is its named shadow.

---

## 6. What this buys, concretely

- **Metering** stops counting ticks and bills measured consumption with `period` as a
  pure granularity knob — closing SRV-3's deferred "elapsed-wall-clock catch-up" half
  on principle, not with a second reaper.
- **Settlement** stops serializing on a hot account: N settlers each draw a locally-held
  attenuated child budget, reconciled per window under the Stingray `η` ceiling — and
  "N children of one cap" is *already* what dregg's attenuation lattice expresses.
- **Escrow** gets a real anti-griefing bond via the proven `SealedEscrow` +
  `StandingObligation` cells in the Hellas marketplace shape (`SettleDirectly` for
  curated, `PostJob…FinalizeJob` for permissionless), with the consumer's posting rate
  bounded by its own budget.

One cell, three uses, one verification template, one named VK seam — and most of the
parts (`allowance.rs`, `SealedEscrow.lean`, `StandingObligation.lean`, the
`BandwidthMeter` budget, the attenuation lattice) already exist.

---

## Appendix — grounding (file:line, read 2026-06-30)

- seL4 MCS scheduling context = `(budget, period)` + bounded refill queue
  `{rTime, rAmount}`; consume against actual execution, replenish lazily up to `now`,
  `period` = replenishment granularity (sporadic-server `budget/period` sliding window),
  sched-contexts donatable across endpoints (`Call` donates the client's SC).
- dregg rate-limited allowance — `cell/src/allowance.rs`: `AllowanceTerms {
  beneficiary, asset, limit_per_epoch, epoch_length, start }`, cursors
  `current_epoch`/`spent_this_epoch`/`spent_total`, shared `check_spend` core, epoch
  *derived* from the block (early refill inexpressible). Doc:
  `docs/deos/RATE-LIMITED-ALLOWANCE.md`.
- `metatheory/Dregg2/Deos/StandingObligation.lean` — committed `next_due` cursor,
  `StrictMonotonic` reuse, `root_binds_get` anti-ghost; teeth `replay_rejected`,
  `early_discharge_rejected`, `over_discharge_rejected`, `behind_schedule_rejected`.
- `metatheory/Dregg2/Deos/SealedEscrow.lean` — two-leg escrow `deposit`/`settle`,
  `replay_rejected` + `over_claim_rejected`; weld example
  `SettleEscrowSatDescriptor.lean` (staged, no live routing).
- `docs/deos/HOUSE-CAPACITY-FRAMEWORK.md` — the five-part capacity template, the two
  reuse bases (cap lattice `attenuate_subset`, heap-root `root_binds_get`), the one
  named per-capacity VK weld.
- Hellas `original-stingrayish-protocol/transactions.rs`+`objects.rs` —
  `Transaction::{PostJob, ClaimJob, CommitResult, FinalizeJob, AbortJob, SettleDirectly}`,
  `JobEscrow { requestor, provider, payment, provider_bond_required,
  provider_bond_locked, finalization_delay }`, `JobStatus { Posted, Claimed, Committed,
  Finalized, Aborted }`; `bounded_counter.rs` — per-validator `ValidatorBudgetState`,
  `BudgetCertificate`, `ResetBudget`, Stingray ceiling `η = (f+1)/(2f+1)` under
  `n ≥ 3f+1`.
