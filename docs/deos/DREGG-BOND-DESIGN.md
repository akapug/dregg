# The $DREGG bond: a correlation-aware collateral design

*Design doc (VISION, with a named smallest rung). This is the design `docs/TOKENOMICS.md`
§role-4 calls **NAMED** — "a $DREGG bond/collateral sink via the ordinary Payable rail …
any design must price the correlated-devaluation problem." It prices it. Nothing here is
built unless labeled otherwise; maturity labels follow the TOKENOMICS convention
(**RUNS** / **BUILT** / **NAMED** / **VISION**). Sibling sources: `docs/TOKENOMICS.md`
(the canonical statement this must not contradict), `docs/deos/FHEGG-CODEX-ROUND4.md`
§C (the rolling exposure-indexed bond and the quote-denomination argument),
`node/src/relay_dispute.rs` (the real slash machinery this rides),
`tools/deployer-gate/README.md` (the existing ETH-denominated bond arm).*

## 1. The problem, and the pathology we refuse to ship

dregg has no staking. That is deliberate (`docs/TOKENOMICS.md`: no staking yield, no
burn, no P2E), but it leaves the token without the one demand shape staking provides
elsewhere: **a reason for an operator to acquire and lock the token in order to
operate**. The bonded subsystems that exist are denominated in other units — relay
operator bonds in internal computrons (`node/src/relay_dispute.rs`, RUNS in test), the
launchpad deployer bond in ETH (`tools/deployer-gate/`, RUNS as PoC) — so today the
token has service-purchase demand and governance-weight demand, but no
collateral-shaped sink.

The naive fix — "let operators post their bond in $DREGG" — has a pathology the project
record already names (`docs/deos/FHEGG-CODEX-ROUND4.md` §C, assessed GOLD):

> **a bond denominated in the token it polices loses value exactly when misconduct
> occurs** — denominate in the QUOTE asset, not the launch token.

The deterrence condition is `α·S ≥ Ḡ + C` for every provable misconduct action
(detection probability `α`, slash value `S`, certified gain bound `Ḡ`, enforcement cost
`C`). `S` there is not the face amount of the bond; it is the bond's **value conditional
on the misconduct having happened**. Three correlation regimes, in descending severity:

- **ρ ≈ 1 — the bonded party can move the bond asset, and the misconduct is the move.**
  A launch creator bonded in their own launch token: the dump that triggers the slash is
  the same event that zeroes the collateral. Crash-conditional `S ≈ 0`. No haircut
  rescues this; the honest collateral weight is **zero**.
- **ρ high — misconduct is protocol-scandal-shaped.** A major dregg operator provably
  dropping custody is $DREGG news; the slash event and a token drawdown share a cause.
  Crash-conditional `S` is some fraction of face value, and that fraction is not
  estimable to the precision a deterrence floor needs.
- **ρ = market beta.** Ordinary crypto drawdown, uncorrelated with any specific fault.
  A haircut and a conservative mark handle this regime — and only this regime.

Any design in which token collateral is load-bearing for the **deterrence floor** must
survive the first two regimes, and it cannot: at deployed adversarial conditions the
crash-conditional price has no positive lower bound (the misconduct can *be* the crash).
So the design below never lets the token touch the floor. That constraint is the whole
shape of the mechanism.

## 2. Inherited constraints (what this design may not contradict)

From `docs/TOKENOMICS.md`, all binding:

1. **Fixed supply, no protocol mint, no burn.** Slash proceeds are conserving
   transfers; `node/src/relay_dispute.rs` already asserts no `Effect::Burn` on the
   slash turn — seizures route to a deployment-chosen remainder cell
   (`default_slash_treasury()`), never destroyed, never a protocol-governed windfall.
2. **$DREGG buys services, never power, never yield.** A bond may buy an operator
   *operating capacity*; it may not buy governance weight, consensus weight, or a
   return. No yield attaches to bonded tokens — the lock is the whole sink.
3. **Bridged $DREGG is an ordinary Payable asset** (1:1 mirror against the vault,
   conservation-gated in `turn/src/executor/bridge_ledger.rs`). The bond mechanism
   sees it as an `AssetId` like any other; and because the bridge's three value-path
   soundness suspects remain open (P1, `HORIZONLOG.md`), no rung below holds real
   bridged value before those close.
4. **Computrons are not the token.** A computron-denominated tranche creates no token
   demand and must not be narrated as if it does.

From the codebase, the rails this must ride rather than duplicate:

- **The Payable rail** — `dregg_payable::resolve_pay`
  (`dregg-payable/src/payable.rs:123`): `pay(asset, amount, to)` desugars through the
  shared verified descriptor to one conserving `Effect::Transfer`; the kernel enforces
  per-asset Σδ = 0. Posting, topping up, and disposing of a bond are all `pay` turns.
- **The relay-operator bond template** —
  `dregg_storage_templates::relay_operator`: `bond_amount` (slot 0), `bond_min`
  (slot 1), `dispute_count` (slot 7); the slash transition is executor-enforced as
  `BoundedBy { bond_amount, dispute_count }` + `FieldDelta { dispute_count, +1 }` —
  a forgotten floor is a constraint violation, not a code-review hope.
- **The slash loop** — `node/src/relay_dispute.rs`: referee verdict
  (`adjudicate_from_inbox`, a bilateral owner-anchored fraud proof) → floor-capped
  `SlashPlan` (`seized = min(request, bond − bond_min)`) → `SlashPayout::split`
  (restitution = `min(seized, proven_fee + bounty)`, remainder to treasury,
  `restitution + remainder == seized`) → `build_slash_turn` (the real `Action` with
  conserving Transfers). The cell-program intake
  (`node/src/relay_slash_intake.rs::intake_dispute`) is the successor path.
- **A fail-closed price oracle** — `dregg-pay/src/pricing.rs::PriceOracle`
  (Jupiter-backed, `Err` on stale/invalid, never a silent default). Available, and used
  below only where failing closed is safe.
- **The launchpad bond arm** — `tools/deployer-gate/` (ETH-denominated, slashable on a
  proven rug, live-recheck tooth). The quote-denominated precedent already in tree.

## 3. Three candidate shapes, and the pick

**(a) Quote-asset floor with a token top-up tranche.** The deterrence floor is covered
entirely in a quote asset (computrons internally; bridged USDC externally); $DREGG rides
above the floor as a junior, first-loss tranche that buys operating headroom. The slash
path never consults a price. *Cost:* token demand is bounded by what headroom is worth
to operators — honest but not dramatic. *Benefit:* sound in all three correlation
regimes by construction; zero new kernel mechanism; oracle failure degrades headroom,
never deterrence.

**(b) Over-collateralization curve (all-token bond at a haircut).** Required posting
`= floor / (p·(1−h))` with maintenance margin and liquidation. *Rejected.* To be sound
against the ρ-high regime the haircut must bound the crash-conditional price from below,
and no such bound exists — the required over-collateralization diverges, so any finite
curve (150%, 300%, pick one) is theater at exactly the moment it is needed. It also
drags a live oracle and a liquidation engine into the slash path (new mechanism, against
the ride-existing-rails constraint), and liquidating seized tokens sells into the crash
the misconduct caused — reflexive, value-destroying, and the proceeds are unbounded
below the penalty.

**(c) Oracle-marked hybrid counting toward the floor.** A mixed quote/token portfolio
marked to the oracle, with margin calls maintaining quote-value coverage, token value
partially satisfying the deterrence requirement. *Rejected for the floor, adopted for
headroom.* The same divergence as (b) applies to whatever fraction of the floor the
token covers; and it makes the slash path's soundness conditional on oracle liveness and
honesty — a `PriceError` at dispute time would leave a provable fault under-deterred.
Marking is fine where failing closed is safe (admission and headroom); it is not fine
where a conviction must seize full value (the floor).

**The pick is (a), with (c)'s marking machinery confined to the headroom tier: a
quote-floored two-tranche bond.** The record's tooth — quote-denominate the bond —
is satisfied literally: the *bond*, meaning the deterrence-bearing collateral, is quote.
The token tranche is real collateral (first-loss, genuinely forfeited on a slash) but
its value is never load-bearing for deterrence, so its correlation with misconduct is
priced at exactly what it is worth in the worst regime: nothing.

## 4. The mechanism

An operator's bond is two tranches, each an ordinary Payable holding in a bond cell:

**Senior tranche (quote asset — computrons internally, bridged USDC externally).**
- `senior_amount ≥ senior_floor`, where `senior_floor ≥ max_a (Ḡ_t(a) + C_t(a)) / α_t(a)`
  over the misconduct actions the deployment's referees can prove. For auto-replayable
  predicates (the custody referee) `α ≈ 1`; statistical accusations have `α ≪ 1` and —
  per the record — must not trigger automatic confiscation at all, so they never enter
  the max.
- Rolling, exposure-indexed (`FHEGG-CODEX-ROUND4.md` §C): `senior_floor` tracks current
  certified exposure (in-flight custody deposits, promised-not-delivered value), not a
  flat worst case — equal deterrence at lower average locked capital.
- This is the tranche the existing relay-operator template already implements: slot 0 /
  slot 1 / slot 7 with the `BoundedBy` + `FieldDelta` executor constraints.

**Junior tranche ($DREGG — the sink).**
- Posted by `resolve_pay(operator_cell, DREGG_ASSET, amount, bond_cell, …)` — one
  conserving Transfer, no new mechanism.
- **Counts toward the deterrence floor: never.** Its marked value
  `junior_amount × p_mark × (1 − h)` counts only toward the operator's **headroom
  tier**: the exposure ceiling above the senior-covered base (how much in-flight
  custody the operator may hold), and service-tier placement. `p_mark` is a trailing
  low (e.g. the 7-day minimum from `PriceOracle`), not spot; `h` is a deployment
  haircut. Oracle unavailable ⇒ marked value 0 ⇒ headroom collapses to the
  senior-covered base — fails closed, deterrence untouched.
- **ρ ≈ 1 exclusion, hard rule:** an asset the bonded party is being policed *about*
  has collateral weight zero in that bond. A launch creator's own launch token never
  counts in their conduct bond (the launchpad case keeps its quote/ETH arm); $DREGG
  itself is excluded from any bond whose policed conduct is $DREGG-market conduct.
  For relay/service operators — whose provable faults are custody faults, not token
  trades — $DREGG sits in the ρ-high regime, which is exactly why it is
  headroom-only.
- **No yield.** Bonded $DREGG earns nothing. What it buys is operating capacity —
  a service-shaped privilege on the operator side, consistent with the locked "$DREGG
  buys services, never power" posture. Explicit edge: headroom must never gate
  governance or consensus weight; proof-of-holdings weight remains non-custodial and
  separate (`docs/deos/PROOF-OF-HOLDINGS.md`).

**The slash waterfall (oracle-free, pure function of cell state + verdict).**
On a conviction with quote-denominated penalty `P` (floor-capped as today):

1. **Senior pays the penalty in full.** `seized_senior = min(P, senior_amount −
   senior_maintenance)` — the existing `plan_slash` line, unchanged semantics. The
   split is the existing `SlashPayout::split`: restitution to the wronged party is
   `min(seized_senior, proven_fee + bounty)` **in the quote asset** (the wronged
   party's make-whole must not arrive in an asset the fault just cratered); remainder
   to the deployment's remainder cell. Conserving, both legs.
2. **Junior forfeits proportionally, first-loss in spirit and in economics.**
   `seized_junior = min(junior_amount, ⌊junior_amount × seized_senior /
   slashable_senior_headroom⌋)` where `slashable_senior_headroom = senior_amount −
   senior_maintenance` at dispute time — the same *fraction* of slashable collateral,
   computed in integer arithmetic with no price input. The forfeited tokens go, as one
   conserving Transfer, to the same remainder cell. Never to the wronged party (their
   restitution is quote), never to the disputer (no windfall), never burned.
3. A zero-amount leg is omitted, exactly as `build_slash_turn` does today.

Why proportional rather than junior-absorbs-first-in-value: absorbing the penalty
in token value requires pricing the tokens at dispute time — the oracle re-enters the
slash path, and a crashed mark converts "junior is first-loss" into "junior is
worthless, senior pays anyway, plus we argued about a price." The proportional rule
keeps the deterrence accounting entirely in quote (senior always pays `P` in full),
keeps the slash plan deterministic and offline-checkable, and still makes the token
tranche genuinely at risk: an operator who misbehaves loses quote *and* tokens, and
the token loss scales with the severity fraction.

**Posting, top-up, exit.**
- Post/top-up: `pay` Transfers into the bond cell (asset-tagged; the cell's two
  holdings are per-asset kernel-conserved). Top-up is how an operator answers a
  headroom margin call after a mark decline — voluntarily, to keep their ceiling; a
  missed call shrinks the ceiling, it never slashes.
- Exit: withdrawal is a timelocked decrement with the same `BoundedBy`-floor shape as
  the slash transition, and the unbonding delay must exceed the dispute admissibility
  horizon (`accept_by` + dispute window), so an operator cannot front-run a pending
  provable fault out the door. (The template has no withdrawal transition today —
  named as rung-2 work below, not assumed.)

## 5. Lean obligations

The Rust slash loop is unit-tested (`node/src/relay_dispute.rs` tests: conservation,
floor cap, restitution bound, both polarities). The Lean obligations extend the same
three properties to the two-tranche plan — stated here as the theorem shapes to be
proven alongside the storage-template metatheory, none of which exist yet (**NAMED**):

1. **Per-asset conservation of the split.** For each asset `a ∈ {quote, dregg}`:
   `restitution a + remainder a = seized a`, and the emitted turn's Transfers for
   asset `a` sum to `seized a` out of the bond cell. (The kernel's per-asset Σδ = 0
   conserves any Transfer it admits; this obligation is that the *plan* accounts for
   the whole seizure — the plan-level mirror of today's `payout_split_conserves` test.)
2. **No seizure beyond the bond, per tranche.** `seized_senior ≤ senior_amount −
   senior_maintenance` and `seized_junior ≤ junior_amount`; post-state
   `senior_amount' ≥ senior_maintenance ≥ 0` and `junior_amount' ≥ 0`. The executor
   already enforces the senior bound structurally (`BoundedBy`); the theorem discharges
   that the plan never *requests* more, so a well-formed plan always executes.
3. **Restitution bounded, and quote-only.** `restitution_quote ≤ proven_fee + bounty`,
   `restitution_quote ≤ seized_senior`, `restitution_dregg = 0`. (The wronged party is
   made whole, never enriched, and never paid in the correlated asset.)
4. **Oracle-independence of the slash path.** The slash plan is a pure function of
   (cell state, verdict, requested penalty, proven fee) — no price term appears in its
   definition. In Lean this is free by construction (the definition takes no oracle
   argument); its value is as a *stated* invariant so a future refactor that threads a
   mark into the plan is a type-visible regression, not a silent one.
5. **Deterrence-floor preservation.** Every transition of the bond cell (post, top-up,
   slash, timelocked withdraw) preserves `senior_amount ≥ senior_maintenance`, and the
   admission gate for new exposure requires `senior_amount − senior_maintenance ≥
   required(exposure)`. This is the handler-floor pattern (a forgotten gate is a type
   error), applied to exposure admission.

Non-obligations, stated so nobody proves theater: there is no theorem that the junior
tranche retains value — the design's soundness explicitly does not depend on it — and
no theorem about oracle honesty, because nothing load-bearing consumes the oracle.

## 6. Staged delivery

**Rung 1 — the smallest shippable rung (all-internal, no bridge, no oracle).**
Two-tranche bond on the existing relay-operator loop: extend the bond cell with a
junior $DREGG holding (a Payable holding posted via `resolve_pay`), extend
`SlashPlan`/`SlashPayout` to the per-asset vector with the proportional junior-forfeit
rule, emit the junior leg from `build_slash_turn` as a third conserving Transfer.
Senior stays computron-denominated exactly as today. Adversarial tests first, both
polarities: (i) conviction seizes senior penalty + proportional junior, per-asset
conservation asserted; (ii) acquit touches neither; (iii) junior forfeit capped at
`junior_amount`; (iv) a plan constructed with a price argument does not compile
(obligation 4's Rust shadow). No oracle, no bridge value at risk, no headroom tier yet
— the junior tranche at this rung is pure first-loss forfeit. *This rung already
creates the sink:* an operator who wants the (rung-2) headroom must have locked tokens,
and the forfeit tooth is real from day one.

**Rung 2 — headroom tier + exit.** The marked headroom ceiling (trailing-low mark from
`PriceOracle`, fail-closed to the senior base), the exposure admission gate as a
handler-floor, and the timelocked withdrawal transition (unbonding > dispute horizon).
The Lean obligations 1–3 and 5 land with this rung, alongside the executor-constraint
extensions in `dregg-storage-templates`.

**Rung 3 — external quote senior.** Bridged-USDC senior tranche for externally-facing
operators, via the same Payable rail (USDC is just another `AssetId` once bridged).
**Gated on closing the three bridge value-path suspects** — no real external value
rides the bond before the bridge holds real value soundly.

**Rung 4 — the launchpad conduct bond.** The rolling exposure-indexed creator bond
from `FHEGG-CODEX-ROUND4.md` §C (quote senior sized by `max_a (Ḡ+C)/α` over the
certified gain bounds; forbid-first vesting escrow shrinking the residual `a`-set),
with the deployer-gate bond arm as its posting surface and — per the ρ ≈ 1 rule — the
creator's launch token at weight zero, $DREGG junior admitted at the headroom tier
only. This rung is where the design and the launchpad's existing ETH arm merge.

## 7. What creates token demand, and what is plumbing — plainly

**Genuine token demand (the sink, honestly sized):** the junior tranche, and only it.
Operators acquire and lock $DREGG to buy operating headroom above their quote-covered
base, and stand to forfeit it on proven misconduct. The demand is
`Σ over operators (junior posting)` — it scales with the number of bonded operators
and what headroom is worth to them, and it is **zero if nobody runs bonded services**.
It is staking-*shaped* (acquire, lock, slashable) without staking's lie: no yield, no
emission funding it, no pretense that the locked tokens secure the deterrence floor.
The forfeit routing (conserving Transfer to the remainder cell) also means slashes
never destroy supply and never enrich the protocol — consistent with the existing
posture, and with the treasury-pile economics of `dregg-pay`.

**Neutral plumbing (creates no token demand; say so):** the senior tranche (computron
or USDC demand, not $DREGG); the referee, split, and dispute route; the oracle marking;
the withdrawal timelock; every Lean obligation. And one explicit anti-theater rule: if
a future iteration proposes letting the junior tranche count toward the deterrence
floor "at a conservative haircut," that is the §3(b) design wearing a coat — the
correlation argument in §1 is the standing falsifier, and the number it needs
(a positive lower bound on crash-conditional price) does not exist.
