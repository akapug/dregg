# The dregg launchpad — verify the sale yourself

*A provably-fair token launchpad. The three abuses that rug retail — sniping, hidden
supply, and the silent liquidity/mint drain — are **theorems you cannot route around**, not
settings a platform tunes. Every number a buyer sees is one they recompute from the chain
themselves. The anti-rug core is now backed three ways: the Lean mechanism theorems, a
**symbolic proof over the compiled contract bytecode**, and an **independent adversarial
audit that found — and we fixed — a real permanent-loss bug.** This is the BD-facing pitch;
the mechanism design is `DREGG-LAUNCHPAD-DESIGN.md`, the moment-and-scope census is
`LAUNCHPAD-OPPORTUNITY.md`, the rug-vector forensics is `RUG-FORENSICS-VS-DREGG.md`, and the
audit report is `LAUNCHPAD-CONTRACT-AUDIT.md`.*

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

## Why "verify me" is more than a slogan here — the assurance stack

The anti-rug claim rests on four independent layers of assurance, not one. Each grades
honestly, and the point of listing them is that they are *different kinds of evidence* that
converge:

1. **The Lean mechanism theorems (PROVED).** Uniform-price no-arbitrage, the supply-authority
   biconditional, pool solvency, and the sealed-bid binding are machine-checked in the
   metatheory (`uniform_price_no_arbitrage`, `execMintA_iff_spec`, `pool_solvent_forever`,
   `reveal_binds_committed`, `uncommitted_cannot_win`). This is what the *mechanism* proves.

2. **A symbolic proof over the compiled contract bytecode (PROVEN, symbolic-bounded).** The
   hand-written Solidity is the one surface the Lean proofs do not directly cover, so the two
   load-bearing anti-rug invariants are re-proven on the **real compiled bytecode** with
   Halmos (symbolic EVM, all inputs symbolic): `DreggLaunchToken` hard-cap / single-mint and
   `DreggSolventPool` never-drainable-below-floor, each the EVM twin of the corresponding Lean
   theorem. **7/7** symbolic checks pass; the negation yields a counterexample (mutation
   canary — the proof is non-vacuous). Honest bound: this is symbolic execution with **bounded
   call depth** and a bounded reserve band, not an unbounded inductive proof — the bound
   travels with the claim. (`chain/formal-verification/`; solc's CHC engine was *rejected as
   unsound* on these contracts — it mis-models `revert CustomError()` — and we refused to
   verify a `require`-rewritten mirror to fake a pass.)

3. **An independent adversarial audit that found a real bug (assurance, not theater).** The
   forge suite is *grading our own homework* — we wrote both the contracts and the tests. So
   the full contract source went to an independent hostile auditor (`codex`, GPT-5.6-class,
   reasoning xhigh), and every finding was triaged against source with a reproducing test. The
   audit **surfaced a real, confirmed, permanent-loss defect the green test suite missed**: a
   committed-but-unrevealed bidder's escrow was dead-locked once a launch cleared (the settle
   path required a reveal; the refund path refused a cleared launch — no third exit), and a
   permissionless force-clear could deliberately trap it. **Fixed** (settle now refunds any
   committed bidder at zero fill, CEI-safe, phase-disjoint), with an exploit test that fails
   pre-fix and passes post-fix. This is the proof point that "verify me" is not marketing: an
   outside adversary found what our own green tests couldn't, and the honest disclosure is the
   product. (`LAUNCHPAD-CONTRACT-AUDIT.md`.)

4. **Structural absence of the known rug doors (forensic).** We pulled the on-chain mechanism
   of documented launchpad rugs — Meerkat's `upgradeTo` proxy-swap, SQUID's owner/whitelist
   sell-blocking `transfer`, HypervaultFi's team-vault privileged withdrawal, the classic
   owner-`mint` inflation — and went vector-by-vector against our contracts. All **nine
   dissected rug doors are structurally absent in our source**: no owner/admin/governance
   role, no second-mint path, no proxy/upgrade slot, no honeypot transfer gate, no
   blacklist/pausable, no LP-pull, no owner-drain. (`RUG-FORENSICS-VS-DREGG.md`.)

---

## The demo — a real fair launch, end to end, checkable

A launch is four verified turns: **disclosed-supply creation → sealed-bid batch raise cleared
at one uniform price → graduation into a provably-solvent pool → non-custodial settlement.**
The demo runs all four against the *real* deployed contract — no mock of the mechanism — and
produces a **verifiable receipt** where every field re-derives from chain state.

**What actually runs (reproducible locally today):**

- `chain/test/DreggLaunchpad*.t.sol` — **42/42** on-chain adversarial tests pass across 4
  suites (`forge test`): hidden-supply reverts, no-peek, no-late-switch, no-drop permutation,
  no-second-mint-door, seed-mismatch reverts, solvency-drain reverts, creator-lock enforced,
  the timeout-refund disjoint-window, the committee-attestor signature discipline, the
  fraud-proof slash, **and the audit's permanent-loss exploit now recovering the escrow.** The
  broader chain suite (settlement + launchpad + backstops) runs green alongside it.
- `launchpad-web/gate/run-gate.sh` — an end-to-end gate runs a full honest launch (register →
  sealed commit → reveal → uniform clear → settle → graduate → live pool trade) **plus** the
  adversarial reverts against the deployed bytecode, **plus** the backend REST layer reflecting
  every on-chain number. In the reference run the book clears at a **single uniform price of 3
  gwei/token**, the full sale tranche fills, the top bidder fills 400, the marginal bidder
  fills 200, the below-clearing bidder fills **0**, and the pool graduates solvent with a live
  buy — while a drain below the reserve floor **reverts**.
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
| **Snipe / front-run** | One uniform price removes the value of ordering — no earliest block to win, no time-priority edge. `uniform_price_no_arbitrage`. Sealed commit→reveal hides bid content on top. | **PROVED** (Lean) |
| **Hidden supply / insider mint** | No mint enters circulation except the disclosed, issuer-authorized creation turn; token mints once for the cap; no second-mint door. `execMintA_iff_spec` — and re-proven on the compiled bytecode (Halmos, symbolic-bounded). | **PROVED + FV** |
| **Silent LP / mint drain (the classic rug)** | Graduated liquidity is pool-owned and never-insolvent; no creator-withdrawal door. `pool_solvent_forever` — and re-proven on the compiled bytecode (Halmos, symbolic-bounded). | **PROVED + FV** |
| **No late-switch / no peek** | A revealed bid is exactly the sealed one; a never-committed bid can never win. `reveal_binds_committed`, `uncommitted_cannot_win`. | **PROVED** (Lean) |
| **Funds-stuck-no-recovery (rug-via-liveness)** | Every committer gets a permissionless full refund once the clearing window elapses without a clearing; clearing and refund windows are disjoint, so worst case is stall-then-refund. The audit's escrow-lockup case is closed on the *cleared* path too. | **BUILT + TESTED** |
| **Schedule-violating creator dump** | Cumulative creator sells beyond the disclosed vesting unlock = a slashing predicate; slashes compensate holders, never the platform. | **BONDED** (economic, not a theorem) |
| **Corrupt clearing attestation** | A v1 k-of-n committee attests the clearing; a stateless on-chain fraud proof re-folds the book and replays the uniform walk, slashing a committee that signs a non-descending or wrong-price clearing. A corrupt quorum can misallocate *within bounds* but cannot over-mint, drain, or over-charge; a slash degrades the launch to the timeout-refund backstop (liveness fault, never theft). | **BUILT** (v1 trust-minimized; trustless-v2 = wrap-VK, named) |
| **Wash-trading for attention** | Uniform price kills *price*-motivated wash trades; volume-faking is caught by a replayable statistical screener, after the fact. | **detection, not prevention** |
| **A bad token / sybil uniqueness / organic pump-dump** | Named, not solved: mechanism design fixes the rigged wheel, not the casino; one human ≠ many wallets is an identity-layer problem. | **out of scope** |

The theorem names above are real and machine-checked; file:line citations are in
`DREGG-LAUNCHPAD-DESIGN.md` §2–3 and cited on the fairness panel of every launch page. The
committee-attestor, fraud-proof, and timeout-refund backstops are in
`chain/contracts/launchpad/` (`CommitteeAttestor.sol`, `DreggLaunchpad.sol`).

---

## Safe even while dregg itself is private and rotating

A launch does **not** depend on a stable dregg. The contracts hold no verifying key: the
launchpad consumes a clearing attestation as `address→bool` (`finalizeClearing` calls
`attestor.attestClearing(...)` over opaque bytes) — there is no VK, no verifier, no Groth16
point anywhere in the launchpad. A dregg devnet re-genesis or VK rotation **cannot break a
launch**, because the launch never references dregg's proving key. When a real wrapped clearing
proof is used instead of the committee signature, VK rotation is absorbed by an on-chain
epoch registry (a rotation is a single `advanceEpoch` transaction; old epochs stay verifiable)
— the consumer is unchanged. And custody is entirely on the stable chain: the escrow, the
hard-capped one-shot mint, and the un-drainable pool are enforced by contract code dregg
cannot alter. **dregg never holds a user asset**, so the strongest thing a compromised, dead,
or rotated dregg can do to those assets is *nothing*.

The practical consequence: **rung-1 needs zero dregg.** A launch can run permissionlessly with
the clearing recomputed on-chain (attestor set to zero), which means a public launch is
revenue with **no dependency on dregg's live state at all** — the private engine is an
*upgrade* (rung 2: real clearing attestation; rung 3: shielded bidding), not a prerequisite.
The architecture is in `PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`.

---

## Honest scope — what the proof does and does not cover

This is the honesty that *is* the product; it is stated plainly and it stays.

- **Mechanism-proven.** The on-chain surface a rug needs is closed by theorems and re-proven
  on the compiled bytecode: the sale clears fairly, the supply is real and disclosed, the LP
  is not drainable, the mint has no hidden door. This is what the gate, the FV, and the
  receipt demonstrate.
- **Off-mechanism conduct — bonded, not proven.** The proof cannot make the team keep
  shipping, keep the domain up, or not abandon the project. A schedule-violating creator dump
  is disincentivized by a holder-compensating **conduct bond** (economic), and the
  launch-predicate wiring is designed-not-yet-written. A team can raise fairly, take its
  fairly-earned proceeds, and walk — the "soft rug" — and the contract cannot stop that; it
  can only make the *launch mechanics* non-rug-pullable and the on-chain conduct publicly
  replayable.
- **Provably solvent means never-drains-to-zero, not price protection.** The pool floor is
  20% of the seed; up to 80% of a reserve can still exit through priced swaps (market
  activity, not a free drain). Solvency ≠ no-loss; a coordinated sell wave can still crater
  price toward the floor.
- **Deployment integrity is an operational assumption.** Every "no proxy / immutable" claim is
  about the source as written; a verifier must confirm the *deployed* launchpad bytecode
  matches this audited source and is not itself behind an upgradeable proxy. (Because the
  launchpad deploys the token and pool itself via `new`, this residual collapses to a single
  object: the launchpad's own deployment.)
- **Assurance bounds.** The Halmos proof is symbolic execution with bounded call depth and a
  bounded reserve band — strong evidence over all inputs within the bound, not an unbounded
  inductive proof. An unbounded proof needs Certora/Kontrol or a direct derivation from Lean
  (named next step). The independent audit found one real bug and confirmed no theft / rug /
  second-mint / pool-drain / reentrancy / signature vector; residuals are named-in-source or
  tested-by-design.
- **Out of scope, named.** A bad token can still go to zero. Sybil uniqueness is an
  identity-layer problem (proof-of-personhood, not covered). Wash-for-attention is detection,
  not prevention. Regulatory / KYC / securities exposure is legal-and-BD work no Lean theorem
  touches.
- **Nothing deployed with value at stake.** The contracts pass their gate and their FV against
  local bytecode and dry-run cleanly against a public testnet fork; a public deploy carrying
  real funds is a separate, gated step with its own security review and a production Groth16
  ceremony (the demo verifier rides a dev ceremony).

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
chainId confirmed, gas estimated) — it is one command from go, and that command is ember's to
fire:

```
# ⚠ EMBER RUNS THIS — the outward broadcast step. The agent prepared + dry-ran it; it is NOT fired.
export DEPLOYER_PRIVATE_KEY=0x<funded key>
export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \
    --rpc-url robinhood_testnet --broadcast -vvv
#   (Base-Sepolia instead: --rpc-url base_sepolia --broadcast --verify)
```

Post-deploy, registration is permissionless: anyone calls `registerLaunch` to run a real
launch (rung-1, clearing recomputed on-chain, no dregg dependency), the commit/reveal windows
elapse in real time, and the receipt page renders from the live contract. The BD hook is
concrete: **"here is the fair-launch contract live on a public testnet; register a launch and
verify the receipt yourself."**

---

## The same discipline, productized

The launchpad self-audit — the rug-forensics scrape, the Halmos formal verification, and the
codex adversarial pass — is packaged as a repeatable pipeline pointable at *any* contract
(`DREGG-AUDIT-SERVICE.md`): rug-door taxonomy scan → auto-generated Halmos proof where a
standard invariant applies → hostile codex pass → human triage. On a reconstructed rug sample,
three independent stages converge on the mintable-supply door, with Halmos supplying a
*machine counterexample* that the cap is breakable. Sold honestly, it is an assisted audit — it
**finds and proposes with a proof where one applies**, it is **not** a push-button
certification and it does **not** auto-rewrite to secure.

And a dregg clearing can be consumed by an external contract on another chain without migrating
to dregg: `OCIP-SECURITY-SOCKET.md` documents a socket where a third-party contract accepts a
trade only if a real dregg proof attests it (a tested demo, **11/11** both polarities over the
real BN254 pairing; a forged proof is refused). That is the "verify me, not trust me" posture
generalizing beyond the launchpad — dregg as a security *provider you plug into*, not a chain
you migrate to.

---

## See also

- `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` — the deep mechanism design (four verified turns, the
  abuse→antidote table with file:line citations, the conduct bond).
- `docs/deos/LAUNCHPAD-OPPORTUNITY.md` — the moment + the buildable-now-vs-BD split, census-grade.
- `docs/deos/RUG-FORENSICS-VS-DREGG.md` — the nine dissected rug doors vs our contracts.
- `docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` — the independent codex audit + the confirmed bug + the fix.
- `docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` — safe even while dregg rotates.
- `chain/contracts/launchpad/` — the EVM realization; `chain/test/DreggLaunchpad*.t.sol` (42 tests);
  `chain/formal-verification/` (the Halmos proofs); `chain/script/DeployLaunchpad.s.sol` (the one-command deploy).
- `launchpad-web/` — the product layer driving the real contract; `gate/run-gate.sh` (the e2e
  gate), `gate/make-receipt.sh` (the static verifiable receipt).
</content>
</invoke>
