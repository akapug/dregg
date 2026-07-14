# The dregg launchpad — verify the sale yourself

*A provably-fair token launchpad. The three abuses that rug retail — sniping, hidden
supply, and the silent liquidity/mint drain — are **theorems you cannot route around**, not
settings a platform tunes. Every number a buyer sees is one they recompute from the chain
themselves. This is the BD-facing pitch; the mechanism design is `DREGG-LAUNCHPAD-DESIGN.md`,
the moment-and-scope census is `LAUNCHPAD-OPPORTUNITY.md`.*

---

## The moment

A launchpad billed as the "first DegenFi protocol" officially rugged; a major indexer
un-followed its account; the public reaction was "a generational fumble — who's the next
pump.fun on Robinhood?" This is not exotic. A 2025 Solidus Labs analysis found **~98.6%** of
pump.fun tokens exhibited rug / scam / pump-and-dump characteristics. The dominant failure is
a **trust failure**: the team drains, insiders pre-load, snipers win the first block, and the
retail buyer has no way to verify any of it *before* it happens.

The slot that just opened is not for a faster bonding curve. It is for a launchpad where
**fairness is checkable, not promised.** That is the one launchpad thesis dregg is uniquely
positioned to carry — its whole posture is *verify me, not trust me*.

---

## The one-line difference

> Every deployed launchpad's anti-abuse feature is, by the platforms' own admission, a
> **mitigation** — pump.fun says its guardrails "do not eliminate market risk," anti-snipe is
> "not a guarantee of fairness," "fair launch" is a label. On dregg the three dominant abuses
> are **theorems you can't route around**: sniping is unconstructable (one uniform price
> removes the value of ordering), hidden supply is unconstructable (the mint biconditional),
> and the silent LP/mint-drain rug has no door (pool solvency + disclosed mint) — and every
> number the buyer sees is one they can recompute from the chain themselves.

That last clause is the moat: a vaporware launchpad can copy a slogan, but it cannot copy a
receipt you verify against its own contract.

---

## The demo — a real fair launch, end to end, checkable

A launch is four verified turns: **disclosed-supply creation → sealed-bid batch raise cleared
at one uniform price → graduation into a provably-solvent pool → non-custodial settlement.**
The demo runs all four against the *real* deployed contract — no mock of the mechanism — and
produces a **verifiable receipt** where every field re-derives from chain state.

**What actually runs (reproducible locally today):**

- `chain/test/DreggLaunchpad.t.sol` — **16/16** on-chain adversarial tests pass
  (`forge test`): hidden-supply reverts, no-peek, no-late-switch, no-drop permutation,
  no-second-mint-door, seed-mismatch reverts, solvency-drain reverts, creator-lock enforced.
- `launchpad-web/gate/run-gate.sh` — **29/29** end-to-end checks pass against the deployed
  bytecode: a full honest launch (register → sealed commit → reveal → uniform clear → settle
  → graduate → live pool trade) **plus** the adversarial reverts, **plus** the backend REST
  layer reflecting every on-chain number. In the reference run the book clears at a **single
  uniform price of 3 gwei/token**, the full 1000-token sale tranche fills, the top bidder
  fills 400, the marginal bidder fills 200, the below-clearing bidder fills **0**, and the
  pool graduates solvent with a live buy — while a drain below the reserve floor **reverts**.
- `launchpad-web/gate/make-receipt.sh` → `launchpad-web/public/receipt.html` — a static,
  self-contained **verifiable receipt** generated from that real launch: the one clearing
  price, the sealed book and its fills, the disclosed schedule with its keccak commitment
  **recomputed and matched** on the page, and the solvent-pool reserves. Nothing is at stake;
  it is the shareable proof-of-fairness a buyer inspects.

The receipt is the product. Not "trust our fair launch" — **"here is the launch, verify it."**

---

## The abuse → antidote table (graded honestly)

| Abuse vector | dregg's answer | Grade |
|---|---|---|
| **Snipe / front-run** | One uniform price removes the value of ordering — no earliest block to win, no time-priority edge. `uniform_price_no_arbitrage`. Sealed commit→reveal hides bid content on top. | **PROVED** (lever) |
| **Hidden supply / insider mint** | No mint enters circulation except the disclosed, issuer-authorized creation turn; token mints once for the cap; no second-mint door. `execMintA_iff_spec`. | **PROVED** |
| **Silent LP / mint drain (the classic rug)** | Graduated liquidity is pool-owned and never-insolvent; no creator-withdrawal door; post-launch mint is a visible, recorded, bondable turn. `pool_solvent_forever`. | **PROVED** |
| **No late-switch / no peek** | A revealed bid is exactly the sealed one; a never-committed bid can never win. `reveal_binds_committed`, `uncommitted_cannot_win`. | **PROVED** |
| **Schedule-violating creator dump** | Cumulative creator sells beyond the disclosed vesting unlock = a slashing predicate; slashes compensate holders, never the platform. | **BONDED** (economic, not a theorem) |
| **Wash-trading for attention** | Uniform price kills *price*-motivated wash trades; volume-faking is caught by a replayable statistical screener, after the fact. | **detection, not prevention** |
| **A bad token / sybil uniqueness / organic pump-dump** | Named, not solved: mechanism design fixes the rigged wheel, not the casino; one human ≠ many wallets is an identity-layer problem. | **out of scope** |

The theorem names above are real and machine-checked; file:line citations are in
`DREGG-LAUNCHPAD-DESIGN.md` §2–3 and cited on the fairness panel of every launch page.

---

## Honest scope — what the proof does and does not cover

This is the honesty that *is* the product; it is stated plainly and it stays.

- **Mechanism-proven.** The on-chain surface a rug needs is closed by theorems: the sale
  clears fairly, the supply is real and disclosed, the LP is not drainable, the mint has no
  hidden door. This is what the gate and the receipt demonstrate.
- **Off-mechanism conduct — bonded, not proven.** The proof cannot make the team keep
  shipping, keep the domain up, or not abandon the project. A schedule-violating creator dump
  is disincentivized by a holder-compensating **conduct bond** (economic), and the
  launch-predicate wiring is designed-not-yet-written. A team can be a bad team off the
  mechanism; the honest claim is they cannot *rug via the mechanism*, and their on-chain
  conduct is publicly replayable.
- **Out of scope, named.** A bad token can still go to zero. Sybil uniqueness is an
  identity-layer problem (proof-of-personhood, not covered). Wash-for-attention is detection,
  not prevention. Regulatory / KYC / securities exposure is legal-and-BD work no Lean theorem
  touches.
- **Nothing deployed with value at stake.** The contracts pass their gate against local
  bytecode and dry-run cleanly against a public testnet fork; a public deploy carrying real
  funds is a separate, gated step with its own security review.

**Stated exactly:** dregg builds the launchpad where the *sale is provably fair and the supply
is provably real*. It cannot make a bad team good or a bad token valuable, and it says so.

---

## The live-testnet hook — one command from a public demo

The launchpad contract names **Robinhood Chain** (Arbitrum-Orbit L2, chainId 46630) in its
own header as a deploy **target** — a permissionless Orbit L2 anyone can deploy to. *This is a
target the contract names, not a confirmed partnership, listing, or co-marketing relationship;
"the next pump.fun on Robinhood" is a BD bet dregg does not control and does not narrate as
done.* Base-Sepolia (84532) is the equivalent standard-L2 target.

The deploy is **plumbed and dry-run-validated** against the real testnet (read-only fork,
chainId 46630 confirmed, ~4.79M gas / ~0.0001 ETH estimated) — it is one command from go, and
that command is ember's to fire:

```
# ⚠ EMBER RUNS THIS — the outward broadcast step. The agent prepared + dry-ran it; it is NOT fired.
export DEPLOYER_PRIVATE_KEY=0x<funded key>
export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \
    --rpc-url robinhood_testnet --broadcast -vvv
#   (Base-Sepolia instead: --rpc-url base_sepolia --broadcast --verify)
```

Post-deploy, registration is permissionless: anyone calls `registerLaunch` to run a real
launch, the commit/reveal windows elapse in real time, and the receipt page renders from the
live contract. The BD hook is concrete: **"here is the fair-launch contract live on a public
testnet; register a launch and verify the receipt yourself."**

---

## See also

- `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` — the deep mechanism design (four verified turns, the
  abuse→antidote table with file:line citations, the conduct bond).
- `docs/deos/LAUNCHPAD-OPPORTUNITY.md` — the moment + the buildable-now-vs-BD split, census-grade.
- `chain/contracts/launchpad/` — the deployed EVM realization; `chain/test/DreggLaunchpad.t.sol`
  (16 tests); `chain/script/DeployLaunchpad.s.sol` (the one-command deploy).
- `launchpad-web/` — the product layer driving the real contract; `gate/run-gate.sh` (the
  29-check e2e gate), `gate/make-receipt.sh` (the static verifiable receipt).
