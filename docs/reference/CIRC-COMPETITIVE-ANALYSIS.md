# CircuitLLM / $CIRC vs dregg — competitive analysis + a verifiable-flywheel design

*Status: competitive intelligence + a verifiable-finance design. The CircuitLLM/$CIRC
facts are cited to public sources (their site, docs, X); where a claim could not be
independently confirmed it is flagged UNVERIFIED. The dregg capabilities are cited to
code and Lean, graded PROVEN vs BUILT vs NAMED-WELD per `docs/reference/MARKET-METATHEORY-REVIEW.md`
and `docs/deos/DREGG-LAUNCHPAD-DESIGN.md`. The thesis — "prove it accrued fairly, don't
just watch it accrue" — is a **designed and measurable** claim, not a boast: §7 says
exactly what to build and how to measure "we surpass CIRC." No deploys; nothing filed.*

---

## 0. The one-paragraph thesis

CircuitLLM's fee-flywheel is **visible**: an autonomous LP Agent claims pump.fun dev
rewards in SOL, splits 50/50, market-buys $CIRC and pairs it into a locked LP, all
observable on-chain because Solana transactions are public. Nothing about the split, the
timing, or the honesty of the buy is **verified** — the split is enforced by the LP-Agent's
own key, the market buy is a front-runnable public swap, "LP-add strengthens the market" is
a narrative not a theorem, and (their own architecture confirms) the fees are **pump.fun
trading fees, not usage** — the token buying the token. dregg's answer is not a better
narrative but a different epistemics: a
recycle mechanism where the split is **contract-enforced**, the buy is a **sealed-bid
uniform-price clearing** (no order to front-run, adversarially shown unconstructable),
value-neutrality is a **machine-checked Lean theorem**, and every step **emits a
prev-hash-chained signed receipt a non-witness re-checks**. The pitch is: *prove it
accrued fairly.*

---

## 1. What CircuitLLM / $CIRC actually is (cited)

**Contract:** `8fQgfsRnRkKSeNUhevT7wp8mhNvMSJdLn1fJi4oVpump`
([Solscan](https://solscan.io/token/8fQgfsRnRkKSeNUhevT7wp8mhNvMSJdLn1fJi4oVpump)). The
`…pump` suffix means **$CIRC itself launched on pump.fun** — the exact bonding-curve
launchpad class whose abuses dregg's launchpad is built to make unconstructable (§4). It
trades on **PumpSwap** (pump.fun's AMM). This is the central irony of the comparison: CIRC
is a pump.fun token whose "flywheel" runs on pump.fun fees.

**What it is** ([circuitllm.xyz](https://circuitllm.xyz/),
[Circuit-LLM/Circuit-LLM README](https://raw.githubusercontent.com/Circuit-LLM/Circuit-LLM/main/README.md)):
a self-described "vertically integrated Solana infrastructure stack" — simultaneously agent
infra + inference marketplace + SDK + a trading-agent swarm, unified by one metering token.
Their **six-layer stack**: L0 Solana settlement + CIRC (Token-2022); L1 data/indexing
(Geyser→Redis/Postgres); L2 "decentralized Qwen2.5-72B" inference on community GPUs; L3
open-source trading agents/swarm; L4 `@circuit-llm/*` npm SDK + CLI + Python; L5 a live
terminal at [/data](https://circuitllm.xyz/data).

**Real, but early/beta code** (not vaporware; low traction). The
[github.com/Circuit-LLM](https://github.com/Circuit-LLM) org has real repos:
`circuit-agent` v0.12.0 (beta, MIT) — a deterministic, no-LLM-in-hot-path dip-reversal
Solana trading bot (~2 stars, README warns "Beta software … Expect breaking changes,
incomplete features"); `circuit-node-client` v0.1.0 (stake CIRC, optional GPU inference
stage — Phase-2/3 features unshipped); `circuit-geyser` (Rust), `circuit-indexer`,
`circuit-price-feed`.

**$CIRC token mechanics** (VERIFIED from site + README):
- **Solana Token-2022** — "CIRC (Token-2022) is the meter."
- **x402 micropayments** — "Every paid API call is settled in CIRC using the x402
  micropayment protocol — no subscriptions, no API keys, no monthly bills. Agents pay per
  call, at market rate, autonomously" (links [x402.org](https://x402.org)).
- **Pay-per-call + stake-to-serve** — apps pay per call in CIRC; node operators **stake
  CIRC** to run a node and earn free RPC.
- **Jupiter spot pricing** — USD prices converted to CIRC at the current Jupiter spot rate
  (site-claimed, single-source).
- **Wallet architecture** ([Where the CIRC Lives](https://circuitllm.xyz/articles/where-the-circ-lives)):
  distinct **Treasury** (receives x402 revenue), **Distributor** (pays stakers every 30
  min), **Task Escrow** (CIRC bounties), and **Dev/LP** wallet (the flywheel).

**Market state (VERIFIED, dated 2026-07-17,
[GeckoTerminal CIRC/SOL on PumpSwap](https://www.geckoterminal.com/solana/pools/GTaHe1DbJab7kD7QVZnVxqxZDemasRyo5ApsH8SWgfTx)):**
price ~$0.0000556, **FDV ≈ $55.6K** (the ~$60K "very early" figure is accurate),
liquidity/TVL ~$18.1K, **24h volume $8,385 across 176 txns, 286 holders**, pool ~1 month
old (~163.8M CIRC + 121 SOL). Security: LP **100% locked**, mint & freeze authority
disabled.

**Team**: founder @0xAlex_300 ("Alex"), project @CircuitLLM (X). ⚑ Their tweets could not
be read directly (X returns 403 to the fetcher, nitter was down), so the founder's exact
tweet wording is UNVERIFIED; the substance below comes from the project's own site/article.

### 1.1 The fee-flywheel exactly as described (VERIFIED)

From CircuitLLM's own article
[**"Where the CIRC Lives"**](https://circuitllm.xyz/articles/where-the-circ-lives), quoted
verbatim — the flywheel is run by an autonomous **"Circuit LP Agent"** on the dev wallet,
"on a fixed schedule with no human in the loop," doing four things per cycle:

> "**Checks for and claims the accrued pump.fun dev rewards. Splits the proceeds 50 / 50.
> Market-buys CIRC with one half, on-chain at the market price. Pairs that CIRC with the
> other half (SOL) and deposits it into the liquidity pool.**"

And on the "locked, nothing comes out" substance:

> "The liquidity the LP Agent deposits is **locked**. It is not a position we manage,
> rebalance, or pull. **CIRC and SOL go in; nothing comes out.** This is a deliberate,
> permanent holding."

⚑ The literal phrase **"not a burn"** could NOT be confirmed — it does not appear in this
article and the founder's tweets were unreachable. The *substance* ("add to LP, locked,
nothing comes out" — i.e. recycled into liquidity, not destroyed) is VERIFIED; the exact
"not a burn" wording is UNVERIFIED (likely a tweet).

The founder's own key question — **where the fees come from** — is answered by their own
architecture, and the answer is stark: not x402 inference usage, but **pump.fun dev
rewards** (§5). That single fact reframes the whole flywheel.

---

## 2. The flywheel's math — honest properties, both directions

Analyzed as a mechanism, independent of whether one likes the project.

### 2.1 What "buy + LP-add" actually does (the honest failure modes)

**(a) LP-add is not value-to-holders the way a burn is.** A burn removes supply
permanently: every remaining holder's fractional claim rises, monotonically, and
irreversibly. "Buy CIRC + pair with SOL + add to LP" does something categorically
different: it **converts treasury SOL into protocol-owned liquidity**. The bought CIRC is
not retired — it sits in the pool as inventory. Holder value accrues only indirectly and
conditionally:
- The **buy** does exert transient upward price pressure (demand added to the book).
- But **pairing + LP-add simultaneously deepens the book on both sides**, which *reduces*
  the price impact of the very buy that funded it, and reduces the price impact of all
  future buys and sells. Deeper liquidity is *lower volatility*, not *higher price*.
- Net: a burn is a **supply-side** value transfer to holders; LP-add is a
  **liquidity-side** structural change whose benefit to a holder is "you can exit with
  less slippage," not "your coins are worth more." These are different goods. Marketing
  that equates them is the first honest gap.

**(b) The buyer of CIRC funds the seller.** Every market buy is matched by a sell. The
flywheel's buy leg transfers treasury SOL to whoever is selling CIRC at that moment —
frequently insiders, early holders, or bots taking the other side. "Value accrual" that
routes protocol revenue to *current sellers* is a wealth transfer from the treasury (all
holders) to *exiting* holders. Whether that is good depends entirely on who is selling.

**(c) Impermanent loss on the added LP.** The protocol-owned LP position is exposed to
impermanent loss (divergence loss): if CIRC appreciates against SOL after the add, the LP
position underperforms simply holding; if CIRC depreciates, the LP eats the loss on the
way down. The treasury is systematically **selling into strength and buying into
weakness** on its own LP inventory. IL is a real, quantifiable cost of the "add to LP"
choice that "not a burn, we strengthen the market" narration omits.

**(d) Who captures the deepened liquidity.** Deeper liquidity is a **public good** for the
pool — it benefits arbitrageurs, MEV bots, and large sellers *at least* as much as
long-term holders, arguably more (they are the ones who need depth to move size). The
treasury pays; the professional flow captures a large share of the benefit.

**(e) Front-running / sandwiching the buy.** This is the sharpest failure. The flywheel's
market buy is a **public, predictable, periodic swap of known approximate size**. On
Solana, transactions are visible in-flight; a sandwich bot front-runs the flywheel buy
(buys CIRC first, lets the flywheel buy push price up, sells into it), and can sandwich
the LP-add too. The flywheel is a **standing, telegraphed order** — close to the ideal
target for extraction. Every basis point the sandwich bot takes is treasury value (holder
value) leaking to MEV. A telegraphed recurring buy is *strictly worse* than a private or
batched one on this axis.

**(f) "Reduce slippage / strengthen the market" — real or narrative?** *Partly real,
mostly narrative.* Real: deeper liquidity genuinely lowers slippage and is a legitimate
protocol asset (protocol-owned liquidity is a defensible design, cf. OlympusDAO-lineage).
Narrative: framing it as **value accrual to holders** overstates it — it is a volatility
reduction and a treasury-composition change, funded by buying from sellers and exposed to
IL and MEV. It is a defensible use of fees; it is **not** the monotone holder-value pump
that "flywheel" connotes.

### 2.2 The genuinely good properties (credit where due)

To be fair to the mechanism:
- **Protocol-owned, LOCKED liquidity is real and non-trivial.** The LP is 100% locked
  (GeckoTerminal), "not managed, rebalanced, or pulled" — so the *classic LP-withdrawal
  rug is blocked at this position* (the CIRC the flywheel adds cannot be yanked). Mint and
  freeze authority are disabled. This is a genuine, checkable good — CIRC is not, at the
  LP layer, a pull-the-rug setup. (Note the scope: the flywheel LP is locked; this says
  nothing about early-holder/insider distribution from the original pump.fun launch.)
- **Autonomous, no-human-in-loop execution** removes *discretionary* timing abuse of the
  flywheel itself (the LP Agent runs on a schedule). It does NOT remove the front-run of
  its telegraphed buy (§2.1e) — a scheduled public buy is, if anything, *easier* to predict.
- **A usage-fed pool would be a legitimate flywheel** — *if* the fees were genuine usage
  revenue. They are not; they are pump.fun trading fees (§5). So this good property is
  aspirational for CIRC, not realized.

The honest picture: locked-LP is a real mitigation of *one* rug vector; the value-accrual,
MEV, IL, and provenance problems of §2.1 and §5 stand.

---

## 3. Fairness + transparency — VERIFIED or merely VISIBLE?

This is the crux, and the answer is unambiguous.

**Everything about the CIRC flywheel is VISIBLE. Nothing about it is VERIFIED.**

| Property | CIRC posture | Grade |
|---|---|---|
| Fee split is 50/50 | Observable after the fact by reading treasury txns | **VISIBLE, trusted** — enforced by the team's signing key, not a contract invariant. The team *can* deviate (change the ratio, skim, time it) and you learn only afterward, if you audit. |
| The buy happened at a fair price | The swap is on-chain | **VISIBLE** — but nothing proves it wasn't self-sandwiched, routed through a friendly maker, or timed to benefit insiders. |
| The buy is not front-run | — | **NOT ADDRESSED** — a public market buy is inherently front-runnable; no mechanism prevents it. |
| Value actually accrued to holders | Price/LP charts | **NARRATED, not measured** — see §2; LP-add ≠ holder value; no conservation statement exists. |
| Fees come from real usage | Treasury inflows visible | **VISIBLE amount, OPAQUE provenance** — you can see SOL arrive; you cannot prove it came from paid inference vs wash volume vs the team topping it up (§6). |

**Transparency-of-transactions ≠ verified-correctness.** Visibility is *ex-post* and
*trust-based*: you can watch, and if you have the skill and time you can audit, and you
must *trust that the pattern continues*. Verification is *ex-ante* and *structural*: the
undesired action is **unconstructable** or **rejected by a checker anyone can run**, so
there is nothing to trust and nothing to audit after the fact. CIRC offers the former.
Every failure mode in §2 is invisible-until-you-look and reversible-by-the-team. That is
the gap dregg is built to close.

---

## 4. How dregg surpasses it — the provably-fair verifiable flywheel

The design goal: **the CIRC-style recycle mechanism, but where every property CIRC leaves
"visible" is instead enforced-by-contract or proven-in-Lean, and every step leaves a
receipt a non-witness re-checks.** dregg already has the four load-bearing pieces; the
flywheel is a *composition*, and this section is honest about what is PROVEN, what is
BUILT (code, tested, not yet a theorem), and what is a NAMED WELD (designed, not written).

### 4.1 The pieces dregg actually has (cited, graded)

**A. Sealed-bid uniform-price clearing — kills the front-run the CIRC buy suffers.**
The launchpad raise does not fill at time-priority; it **clears the whole revealed book at
one uniform price** computed on-chain by a permutation-checked descending sort (no-drop /
no-insert) + marginal fill (`chain/contracts/launchpad/DreggLaunchpad.sol:382` `finalizeClearing`,
`:424` `_runClearing`, `:455` `_assertPermutation`). Bids are sealed
`H(price‖qty‖salt‖bidder)` during commit, revealed only in the reveal window, and a reveal
that does not open its seal is rejected (`:312` `commitBid`, `:337` `revealBid`,
`BidMismatch`). The adversarial parity suite `chain/test/P0ParityLaunchLoop.t.sol` proves
the three inherited abuses **unconstructable, not mitigated**:
- **Sniping** — `test_Abuse_A_SnipingRefused_NoTimePriorityEdge` runs the *identical book
  in opposite order* and gets an identical uniform price and identical fills
  (`:446`, order-invariance asserted `:508-513`): being first buys nothing because arrival
  order is not an input to the clearing. A late/uncommitted sniper is refused
  `NotCommitPhase` / `NoCommit` (`:472`, `:477`).
- **Hidden supply** — `test_Abuse_B_HiddenSupplyRefused_CapIsAbsolute` (`:557`):
  `SupplyDoesNotClose` (sale + creator + pool must equal cap, `DreggLaunchpad.sol:255`),
  one-shot mint, `AlreadyMinted` / `CapExceeded`.
- **LP / owner drain** — `test_Abuse_C_LpAndOwnerDrainRefused` (`:622`): the graduated
  pool has no owner and no withdraw door; `PoolFloorBreached` refuses any swap that would
  push a reserve below its disclosed floor (`DreggSolventPool.sol:135`, `:161`).

  The mechanism's *fairness* (not just the code) is **PROVEN in Lean**:
  `Market/Optimality.lean:174 uniform_price_optimal` = individual rationality + no-arbitrage
  / value-neutrality + envy-freeness, verified non-vacuous with split-price arbitrage teeth
  (`MARKET-METATHEORY-REVIEW.md` §"Optimality.lean": PROVEN, `#assert_all_clean: 10
  keystones pinned kernel-clean`, build-verified). ⚑ HONEST scope-note per the review:
  `no_improving_deviation` is the algebraic value-neutrality identity, slightly OVER-NAMED
  as "no improving deviation"; the load-bearing content is `uniform_price_no_arbitrage`.

**B. Conservation / value-neutrality / IR — PROVEN, so "value accrued fairly" is a
theorem, not a chart.** `Market/Priced.lean:240 priced_clearing_keystone` proves
per-asset conservation (`netFlow = 0`, a real cross-party Σ) + limit-respect + partial-fill
consistency, with two-polarity teeth (`overfill_refused`, `badPrice_refused`); non-vacuous
(`MARKET-METATHEORY-REVIEW.md` §"Priced.lean": PROVEN). `Market/Fairness.lean:112`
`clearing_respects_limits` is bound to the REAL executor `settleRing` /
`settleRing_conserves` (not a mirror). This is the exact thing CIRC's "value accrual" is
narrated but never has: a **conservation statement** that says value was neither minted nor
destroyed by the recycle.

**C. Attested clearing — Cert-F, verify-not-find.** `Market/CertF.lean` proves
`weak_duality` and `certifies_epsilon_optimal`: a primal-dual certificate `(f,π,s)` with
duality gap `cᵀs − wᵀf ≤ ε` CERTIFIES `f` is ε-optimal **independent of how it was found**
(`CertF.lean` header; review §"CertF.lean": PROVEN, richly inhabited, teeth genuinely
refuse). The solver is untrusted search; the certificate is the checked output. This is the
verify-not-find spine: the flywheel's clearing carries a *proof it cleared optimally*, and
anyone re-checks the certificate without re-running the solver.

**D. Provably-solvent graduation pool — the LP that cannot be drained below its floor.**
`DreggSolventPool.sol` enforces a disclosed per-reserve floor on every swap
(`PoolFloorBreached`, `:135`/`:161`), the on-chain realization of `Market/Liquidity.lean`
`pool_solvent_forever` (∀-schedule fold-invariant, PROVEN, review §"Liquidity.lean"). ⚑
HONEST welds per the review: the `.sol ↔ Lean` correspondence for `DreggSolventPool` is
asserted in `GraduationPool.lean`'s prose and graded **OVER-NAMED (prose)** — the Lean
proves a *model* statement; the deployed-Solidity tie is not itself in the Lean statement.
The `x·y=k` pricing *above* the floor is BUILT (tested), not proven (design doc §5.2). So:
**solvency floor = PROVEN (model) + BUILT (on-chain, both polarities); pricing policy =
BUILT; model↔deployed tie = NAMED WELD.**

**E. The receipt system — every step re-checkable by a non-witness.** A receipt is
prev-hash-chained + Ed25519-signed (or BLS-QC-bearing) + re-witnessable
(`docs/RECEIPT-CONTRACT.md`); `TurnReceipt` (`turn/src/turn.rs`) chain tamper-evidence is
PROVEN in Lean (`metatheory/Dregg2/Exec/Receipt.lean` `chain_tamper_evident`). This is the
"every move is a receipt" substrate — the flywheel emits its generation certificate rather
than asking you to watch a block explorer.

**F. Verifiable randomness — for any lottery/timing leg.** `pqvrf` is a real
post-quantum one-time LB-VRF (Esgin et al., FC 2021, `pqvrf/src/lib.rs`) with a Lean map
(`metatheory/Dregg2/Crypto/VRF.lean`); `dregg-dice` wraps it as non-grindable randomness
with a pure re-derivation verifier (`dice/src/lib.rs`). If the flywheel ever schedules or
randomizes its buys (a real anti-MEV tactic — unpredictable timing), the randomness is
*verifiable*, not a `block.timestamp` a validator grinds.

### 4.2 The design — a verifiable fee-flywheel inside dregg

Map the CIRC flywheel onto dregg's pieces, replacing each "visible/trusted" step with an
"enforced/proven + receipted" one:

| CIRC step | dregg replacement | What changes | Grade |
|---|---|---|---|
| Collect fees in SOL | Fees accrue as an **attested-provenance stream** — each fee is a receipt tied to the turn/SDK-call/game that produced it (§6) | Provenance is *proven*, not assumed | receipts PROVEN; provenance binding = BUILT/NAMED per surface |
| Split 50/50 by team key | **Contract-enforced split** — the recycle contract computes the split as a pure function of the accrued amount and a **disclosed, committed** ratio (mirror `DreggLaunchpad`'s `scheduleCommit` + `GraduationSeedMismatch` pattern: a wrong/hidden split *reverts*) | Team **cannot** deviate; ratio is a committed public input | design over BUILT patterns (the `graduationSeed`/mismatch-revert mechanism exists, `DreggLaunchpad.sol:583`,`:602`) |
| Market-buy CIRC (front-runnable) | **Sealed-bid uniform-price clearing** — the recycle "buy" is a batch that clears the whole book at one price; the recycle order is *sealed* and *order-invariant*, so there is **no telegraphed swap to sandwich** | The §2.1(e) sandwich is **unconstructable** (parity-suite proven) | clearing PROVEN; wiring the recycle as a clearing participant = NAMED WELD |
| Add to LP | **Graduate into / top up the solvent pool** with a **disclosed seed**, floor-guarded | LP cannot be drained below floor; seed is checked (`GraduationSeedMismatch`) | solvency PROVEN (model)+BUILT; deployed-tie = NAMED WELD |
| "Value accrued" (narrated) | **Conservation + value-neutrality theorem** attached to the recycle turn (`priced_clearing_keystone`, `uniform_price_no_arbitrage`) | "accrued fairly" is a *checked certificate*, not a chart | PROVEN (mechanism); recycle-turn instance = to-build |
| "Trust me, it's on-chain" | **Cert-F attested clearing + receipt** — the recycle emits `(clearing, certificate, receipt)`; a non-witness verifies the certificate and re-checks the receipt chain | Ex-ante verification replaces ex-post trust | Cert-F PROVEN; the attestor that binds it on-chain is BUILT with a NAMED statement-weld (below) |

**The dregg pitch, precisely:** not "watch the value accrue" but "**prove** it accrued
fairly" — the split is a committed public input a wrong value *reverts against*, the buy is
a clearing with **no order to front-run** (adversarially shown unconstructable), the
value-neutrality is a **Lean theorem**, and the whole recycle turn emits a **prev-hash-chained
signed receipt** anyone re-checks.

### 4.3 Honest edges — what is NOT proven (do not overclaim)

Per `MARKET-METATHEORY-REVIEW.md` and the launchpad design §5, stated plainly:

1. **The on-chain proof does not bind the clearing price.** `DreggProofAttestor.sol` /
   `IClearingAttestor.sol` are explicit: the dregg wrap statement is 25 pinned lanes
   (`genesis_root · final_root · num_turns · chain_digest`) with **no lane for a clearing
   price or book commitment**. So a verified proof attests "a conserved, rule-abiding dregg
   transition exists," and the *binding* of that transition to "this launch's clearing at
   price p*" is a **TRUSTED assertion by the binder, not a theorem** (`DreggProofAttestor.sol`
   §Trust). This is honest and *cheap*, because the price is computed on-chain from the
   public book (rung-1 REPLAYABLE) — a corrupt binder **cannot misprice**, it can only
   withhold (→ timeout-refund). Closing it needs the clearing tuple *inside* the proof's
   public statement (a circuit/statement change, `cert_f_air.rs` apex→Groth16 path — NOT
   done).
2. **Model↔deployed ties are prose, not Lean.** `GraduationPool.lean` asserting
   `DreggSolventPool.sol` "exactly realizes" the floor discipline is graded **OVER-NAMED
   (prose)**; the Solidity↔Lean correspondence is unverified. The Rust↔Lean market
   denotation is an honestly-named re-authored model (review §3, HONEST-CARRIER), not a
   mechanized faithful denotation.
3. **The MPC "joined" optimality is the WEAK uniform-price sense, not volume-max** (review
   Finding 1, OVER-NAMED) — irrelevant to a simple recycle-buy but must not be cited as
   "optimal clearing" without qualification.
4. **epoch-0 VK is a single-party dev ceremony** (toxic-waste-known); the proof rung is a
   DEMO-TRUST interface end-to-end, not production trust, until the MPC ceremony
   (ember-gated).
5. **The recycle contract itself is TO-BUILD.** The pieces exist; the composition (a
   recycle turn that clears the buy, splits by committed ratio, tops the pool, emits the
   certificate+receipt) is *designed here, not written.* No `RecycleFlywheel.sol` exists
   yet.

None of these are hidden; naming them is the point (`feedback-named-seam-is-not-a-hole`).
The honest scorecard: dregg surpasses CIRC on **front-run resistance** (PROVEN
unconstructable vs unaddressed), **split enforcement** (contract-revert vs team key),
**conservation** (PROVEN vs narrated), and **re-checkability** (signed receipt chain vs
block-explorer visibility) — *today, at the mechanism level*. The **on-chain proof binding
the exact clearing tuple** and the **model↔deployed ties** are the named welds still open.

---

## 5. Where the fees come from — the killer finding, and dregg's answer

### 5.1 CIRC's flywheel is fed by token-trading fees, not usage (VERIFIED from their own doc)

The founder's sharp question — real usage or speculation? — **is answered by CircuitLLM's
own architecture, and the answer is speculation.** The
[Where the CIRC Lives](https://circuitllm.xyz/articles/where-the-circ-lives) flywheel
diagram names the source explicitly:

> "SOURCE │ **PUMP.FUN DEV REWARDS** │ protocol fees accrue to the dev position" → claimed
> by the LP Agent → 50% market-buy CIRC → "LOCKED LP (permanent, deepening)."

pump.fun "dev rewards" / creator fees are a **cut of the token's own trading volume**
(bonding-curve / PumpSwap trade fees, [pump.fun fee docs](https://pump.fun/docs/fees)). So
the buy-pressure loop is **self-referential**: *people trading $CIRC generate the fees that
buy $CIRC.* The token buys the token. It is NOT fed by external agents paying x402 for
inference/data.

There *is* a separate, genuinely usage-driven loop (x402 CIRC → Treasury → Distributor →
stakers every 30 min) — but that loop **pays stakers**; it is not what buys CIRC off the
market. And the team admits the scale is tiny and partly self-funded: their own copy says
the treasury "holds only what the network has actually earned … still modest," and "**We
periodically fund [the agents] to keep that flow running**" — i.e. the team tops up the
agents rather than external demand driving it.

The evidence all points to minimal real usage: **$8,385 24h volume, 176 txns, 286 holders,
$18K liquidity** (2026-07-17); GPU inference is beta/opt-in with Phase-2/3 unshipped; and
**no** published endpoint/inference-usage metrics exist (they link a `/proof` and `/data`
terminal but no verifiable usage numbers were retrievable). Bottom line: **CIRC's flywheel
runs on trading the token, dressed as "protocol revenue."**

### 5.2 dregg's answer — attested-provenance fees

The reason CIRC *can only narrate* the answer is structural: treasury inflows are visible in
amount but **opaque in provenance** (§3). A SOL arriving at the treasury is
indistinguishable, on-chain, between "an agent paid for inference," "someone traded the
token," and "the team topped it up." pump.fun dev rewards and genuine x402 revenue land as
the same kind of transfer.

dregg's fees are **attested-provenance** by construction, because dregg's revenue surfaces
are *turns that leave receipts*:
- **Verifiable compute / SDK / clearing.** Every dregg turn is the exercise of a
  proof-carrying token over owned state, leaving a `TurnReceipt` (prev-hash-chained,
  signed, tamper-evident in Lean). A fee charged for a turn is bound to *that receipt* — the
  provenance is the receipt chain, not an anonymous transfer. "This fee came from real
  work" is re-checkable, not asserted.
- **Games as receipts.** `docs/GAMES-AS-RECEIPTS.md` — every move in the deployed games
  (Descent, multiway-tug, automatafl) is a receipt; game-fee revenue carries its provenance.
- **Attested clearing fees.** A clearing that pays a fee carries its Cert-F certificate;
  the fee's provenance is a verified optimal clearing, not a self-trade.

So where CIRC's flywheel is fed by inflows of *unprovable* origin, a dregg flywheel is fed
by inflows each **tied to a re-witnessable receipt of the work that produced them** —
directly closing the "where do the fees come from" question with evidence instead of a
chart. ⚑ HONEST: the *provenance binding* (fee-receipt ↔ recycle-inflow) is a BUILT wiring
task per revenue surface, not yet a single theorem; the receipt substrate it rests on is
PROVEN.

---

## 6. Measurement plan — "we surpass CIRC" as a measured claim

A prototype + a measurement harness so the surpass-claim is *numbers*, not rhetoric.

### 6.1 What to build (minimal verifiable-flywheel prototype)

`RecycleFlywheel.sol` composing the existing pieces (no new science):
1. **Accrue** — a fee sink that records each inflow with its source receipt hash
   (provenance).
2. **Split** — a pure function of `(accrued, committedRatio)`; a wrong claimed split
   **reverts** (`SplitMismatch`, mirroring `GraduationSeedMismatch`, `DreggLaunchpad.sol:619`).
   The ratio is a committed public input (`scheduleCommit` pattern).
3. **Clear the buy** — route the buy-half through a sealed-bid uniform-price batch
   (`DreggLaunchpad.finalizeClearing` mechanics) instead of a market swap; assert
   order-invariance.
4. **Top the pool** — seed/top `DreggSolventPool` with the disclosed amount, floor-guarded.
5. **Emit** — `(clearing, CertF certificate, TurnReceipt)` for the whole recycle.

Baseline to compare against: a faithful **CIRC-style flywheel mock** on the same testnet
(public market buy + LP-add, team-key split) so every metric is head-to-head on identical
infrastructure.

### 6.2 Metrics (each an A/B number, dregg vs CIRC-mock)

| Axis | Metric | How measured | Surpass criterion |
|---|---|---|---|
| **Front-run resistance** | MEV extracted from the recycle buy (bps of buy value) | Run a sandwich bot against both in a forked-testnet mempool sim; measure value captured | dregg = **0 by construction** (order-invariant sealed clearing, parity-suite proven) vs CIRC-mock > 0 |
| **Fairness** | Envy / price-dispersion across recycle participants; order-invariance | Re-run identical book in permuted orders (as `test_Abuse_A`); measure Δprice, Δfills | dregg Δ = **0** (proven); report the distribution for the mock |
| **Split integrity** | Can the operator deviate from the disclosed split? | Attempt a deviating split tx against both | dregg: **reverts** (`SplitMismatch`); mock: succeeds (team key) |
| **Value-neutrality** | Is the recycle conserving? | Check `netFlow = 0` per asset against `priced_clearing_keystone`; emit the Cert-F certificate and re-verify it off-chain | dregg: **certificate verifies**; mock: no certificate exists |
| **Re-checkability** | Can a non-witness verify the recycle happened as claimed, from public data alone? | Hand a third party only the receipt + certificate; have them re-derive | dregg: **yes** (receipt chain + Cert-F); mock: only block-explorer inspection |
| **Provenance** | Fraction of recycle inflow with a verifiable source receipt | Count inflows carrying a valid `TurnReceipt` hash | dregg: measurable %; mock: **0** (opaque transfers) |
| **Throughput / latency** | Recycle turns/sec; time-to-finalize a clearing | Bench on testnet (persvati/hbox); report p50/p99 | Report honestly — sealed commit→reveal adds latency; the trade is *latency for front-run-immunity*. State the number. |
| **Gas** | Gas per recycle (clearing + settle + top + emit) vs a market-buy+LP-add | Foundry `forge test --gas-report` on both | Report honestly — verification costs gas; quantify the premium and justify it against the MEV+deviation it prevents. |

### 6.3 Honest measurement discipline

- **The latency and gas axes will likely favor the CIRC-mock** — a market buy is one cheap
  tx; a sealed-bid batch clearing is several, with a commit→reveal delay. The surpass-claim
  is **not** "cheaper/faster"; it is "front-run-immune, deviation-proof, conserving, and
  re-checkable — at a stated, bounded latency/gas premium." Report the premium as a first-
  class number so the trade is honest.
- **Measure against the mock, not against marketing** — build the CIRC-style flywheel
  faithfully and beat *it*, not a strawman.
- **Every green must mean something** (`project-ci-meaningfulness-audit`): the front-run
  and split-deviation metrics must be *adversarial* (a real bot, a real deviating tx), not
  a happy-path assertion.

---

## 7. Honest failure modes of BOTH flywheels (the symmetric ledger)

**CIRC's flywheel:**
- **Self-referential fee source** — fed by pump.fun dev rewards = CIRC trading fees, not
  usage; the token buys the token; usage revenue is "modest" and partly team-funded (§5).
- LP-add ≠ holder value (≠ burn); the buy funds sellers; IL on protocol LP; deepened
  liquidity is a public good captured largely by professional flow; the **telegraphed,
  scheduled buy is a prime sandwich target** (autonomy makes it *more* predictable, not
  less); "strengthen the market" overstates a volatility-reduction as value-accrual (§2.1).
- Split enforced by the LP-Agent/team key, not a contract invariant; provenance unprovable
  (§3, §5).
- **Credit:** the flywheel LP is 100% locked and mint/freeze are disabled — the classic
  LP-pull rug is blocked at that position (§2.2). CIRC's problem is not "it's a rug"; it is
  "its value-accrual is narrated, front-runnable, and speculation-fed — none of it proven."

**dregg's flywheel (designed):**
- The **recycle contract is not built** (§4.3.5) — pieces exist, composition doesn't.
- The **on-chain proof does not bind the clearing price** (§4.3.1) — a NAMED weld;
  mitigated because the price is REPLAYABLE on-chain (corrupt binder can withhold, not
  misprice).
- **Model↔deployed ties are prose** (§4.3.2) — the Solidity/Rust ↔ Lean correspondences
  are asserted, not mechanized.
- **epoch-0 VK is a dev ceremony** (§4.3.4) — DEMO-TRUST until MPC.
- **dregg does not fix "a bad token is a bad token"** (`DREGG-LAUNCHPAD-DESIGN.md` §5.3): a
  fairly-recycled worthless token is still worthless; sybil *uniqueness* is out of scope
  (only the sybil *advantage* is neutralized, PROVEN); wash-trading-for-attention is
  detection, not prevention; free-holder pump-and-dump is a market, not a constructed
  abuse.
- **Latency/gas premium** is real (§6.3) — verification is not free.

The difference is not that dregg has no failure modes — it is that dregg's are **named,
graded, and mostly structural-or-scheduled**, while CIRC's are **invisible-until-audited
and reversible-by-the-team.** dregg turns "trust the team and watch the chain" into "run
the checker." That is the surpass, and §6 makes it measurable.

---

## 8. Sources

**CircuitLLM / $CIRC (cited; X/tweets unreachable, flagged inline):**
- Site: https://circuitllm.xyz/ ; live terminal https://circuitllm.xyz/data ;
  `/proof` https://circuitllm.xyz/proof
- Flywheel + wallet architecture (all §1.1, §5 quotes):
  https://circuitllm.xyz/articles/where-the-circ-lives
- GitHub org: https://github.com/Circuit-LLM ;
  https://raw.githubusercontent.com/Circuit-LLM/Circuit-LLM/main/README.md ;
  circuit-agent + circuit-node-client READMEs
- Contract `8fQgfsRnRkKSeNUhevT7wp8mhNvMSJdLn1fJi4oVpump`:
  https://solscan.io/token/8fQgfsRnRkKSeNUhevT7wp8mhNvMSJdLn1fJi4oVpump
- Market data (2026-07-17): https://www.geckoterminal.com/solana/pools/GTaHe1DbJab7kD7QVZnVxqxZDemasRyo5ApsH8SWgfTx
- pump.fun creator/dev fees: https://pump.fun/docs/fees ; x402: https://x402.org
- Founder @0xAlex_300, project @CircuitLLM (X) — ⚑ tweets could not be read (403 / nitter
  down); "not a burn" exact wording UNVERIFIED (substance confirmed via the article above).
- dregg launchpad: `chain/contracts/launchpad/DreggLaunchpad.sol`,
  `DreggSolventPool.sol`, `IClearingAttestor.sol`, `DreggProofAttestor.sol`;
  `chain/test/P0ParityLaunchLoop.t.sol`.
- dregg market metatheory (PROVEN-vs-named grading):
  `docs/reference/MARKET-METATHEORY-REVIEW.md`; `metatheory/Market/{Optimality,Priced,
  Fairness,CertF,Liquidity,GraduationPool}.lean`.
- dregg design + honest edges: `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` (§2 mechanism, §5
  gaps), `docs/RECEIPT-CONTRACT.md`, `docs/GAMES-AS-RECEIPTS.md`.
- Verifiable randomness: `pqvrf/src/lib.rs` (Esgin et al. FC 2021), `dice/src/lib.rs`.
</content>
</invoke>
