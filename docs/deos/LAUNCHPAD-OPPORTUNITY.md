# The launchpad opportunity — a trustworthy slot the market just opened

*The moment: a "first DegenFi" launchpad rugged, its indexer un-followed it, and the
public asked "who's the next pump.fun on Robinhood?" The slot that opened is not for another
faster bonding curve — it is for a launchpad where **fairness is checkable, not promised.**
That is the exact thing dregg already builds. This doc states the opportunity, maps each
anti-rug claim to a **real verified primitive** (file + theorem), and separates cleanly what
is **buildable now on landed machinery** from what is **BD / partnership speculation**. What
is proven is cited; what is a gap is graded; what the proof does **not** cover is stated
plainly.*

**Grade of this document:** REPLAYABLE for the census (re-derivable by reading the cited
files); a **positioning + build-path** doc over the mechanism design in
`docs/deos/DREGG-LAUNCHPAD-DESIGN.md` and the landed code in `chain/contracts/launchpad/` +
`launchpad-web/`. Not a shipped, deployed product — §4 is the honest edge. Beyond the Lean
theorems, the anti-rug core carries three assurance layers — a **symbolic proof over the
compiled contract bytecode** (Halmos, `chain/formal-verification/`), an **independent
adversarial audit that found and fixed a real permanent-loss bug**
(`LAUNCHPAD-CONTRACT-AUDIT.md`), and **liveness/attestation backstops** (timeout-refund,
attestor ladder, fraud-proof) — summarized in §2 and detailed in the pitch
(`LAUNCHPAD-PITCH.md`).

---

## 1. The moment

A widely-followed post: a launchpad protocol billed as the "first DegenFi protocol"
officially rugged; a major indexer un-followed its account; the reaction was "a generational
fumble — who's gonna be the next pump.fun on Robinhood?" The DegenFi / launchpad space is
rug-ridden by construction: a 2025 Solidus Labs analysis found ~**98.6%** of pump.fun tokens
exhibited rug / scam / pump-and-dump characteristics (cited in `DREGG-LAUNCHPAD-DESIGN.md`
§1.2). The dominant failure mode is not exotic — it is a **trust failure**: the team drains,
the insiders pre-load, the snipers win the first block, and the retail buyer has no way to
verify any of it *before* it happens.

The slot that opened wants the opposite: a launchpad where the buyer does not have to trust
the team, the platform, or a screenshot — because the fairness of the sale and the reality
of the supply are **things you check**. dregg's whole posture is "verify me, not trust me."
This is the one launchpad thesis dregg is uniquely positioned to carry.

---

## 2. What we already discussed and built

This is not a cold start. The provably-fair launchpad has an existing design, deployed
contracts, a product layer, and a prior research pass (2026-07-13):

- **The mechanism design** — `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` ("the launchpad where
  fairness is a theorem"): a full landscape survey (pump.fun / LetsBONK / Meteora DBC /
  NOXA / Virtuals mechanisms + the abuse-vector taxonomy with $-scale), then the dregg
  mechanism as **four verified turns** (disclosed-supply creation → sealed-bid uniform-price
  raise → solvent-pool graduation → non-custodial settlement), an abuse→antidote table
  graded PROVED / bonded / not-solved, and a conduct-bond economic layer. This doc is the
  deep reference; the present doc is the *opportunity + moment* framing over it.
- **The deployed EVM contracts** — `chain/contracts/launchpad/`: `DreggLaunchpad.sol`
  (register → sealed commit → reveal → uniform-price clear → settle → graduate),
  `DreggLaunchToken.sol` (hard-capped, minted once, no second-mint door),
  `DreggSolventPool.sol` (the never-drainable graduation pool), `ILaunchEligibility.sol` +
  `IClearingAttestor.sol` + `CommitteeAttestor.sol` (a v1 k-of-n committee attestor with a
  stateless on-chain fraud proof) + `DreggProofAttestor.sol` (the trustless-v2 PROOF arm of
  `IClearingAttestor`: a clearing is attested iff a real Groth16(BN254) wrap proof verifies
  through the OCIP socket — no signatures, no committee; its one named trust point is the
  `bindLaunch` binder linking a launch to its proof, stated in the contract's own header) +
  `ConjunctiveAttestor.sol` (AND-composition of attestors). Explicitly targeted at Robinhood
  Chain (Arbitrum-Orbit L2, chainId 46630) in the contract's own header.
  `chain/test/DreggLaunchpad*.t.sol` carries **71** on-chain-enforced test functions across
  6 suites (core 16 · committee-attestor 16 · proof-attestor 20 · conjunctive 9 · refund 9 ·
  audit-fixes 1).
- **The product layer** — `launchpad-web/`: create / bid / token-page / replayable-discovery
  frontend + backend driving the *real* contract (no mock of the mechanism), with a gate
  (`gate/run-gate.sh` → `gate/e2e.mjs`) that spins anvil, deploys the real contract, and runs
  a full fair launch + adversarial checks (hidden-supply reverts, no-peek, no-late-switch,
  no-drop, dev-lock) against the deployed bytecode. There is also a node-driven mode where a
  launch is a real turn stream on a live dregg node.
- **The confidential-distribution framing** — `docs/deos/ECLIPSE-ZAMA-CONFIDENTIAL-FINANCE.md`
  §4.4 ("Confidential token distribution") and `docs/deos/DREGGFI-PRIVACY-TIERS.md`: the
  launchpad as the vehicle for *hidden distribution without hidden supply* — vesting/airdrop
  amounts private while the total supply stays provable — over the Dark/Shielded/Open dial.
- **The prior research pass (2026-07-13)** — a sub-agent swarm surveyed the launchpad
  landscape (NOXA, pump.fun, LetsBONK, Believe, Virtuals, Meteora DBC), reframed the
  anti-snipe narrative around uniform-price batch clearing as the robust lever, and turned
  the design into a deployable Robinhood-Chain MVP. That pass is what produced the contracts
  and the web layer above.

- **The assurance stack** — the hand-written Solidity is the one surface the Lean proofs do
  not directly cover, so three layers back the anti-rug core:
  (a) a **symbolic proof over the compiled bytecode** (Halmos, `chain/formal-verification/`) —
  `DreggLaunchToken` hard-cap/single-mint and `DreggSolventPool` never-drainable re-proven over
  all inputs (7/7, symbolic-bounded, the EVM twins of the Lean theorems); (b) an **independent
  codex adversarial audit** (`LAUNCHPAD-CONTRACT-AUDIT.md`) that surfaced a **real
  permanent-loss bug** the green forge suite missed (a committed-but-unrevealed bidder's escrow
  dead-locked once a launch cleared) — now fixed, with an exploit test that fails pre-fix; and
  (c) **liveness + attestation backstops** — a timeout-refund (stall→refund, never loss, with a
  disjoint clearing/refund window), a v1 committee attestor, and a stateless on-chain fraud
  proof that slashes a committee signing a non-descending or wrong-price clearing.

So the recall is concrete: **the anti-rug launchpad is designed, its contracts are written,
tested (71 forge tests across 6 suites), formally verified on the anti-rug core, independently
audited, and driven by a product surface.** What is new here is only the *moment* and the honest buildable-vs-BD split.

---

## 3. The anti-rug thesis, mapped to real verified primitives

A launchpad's core failure is the rug — a trust failure. dregg's move is to make the four
things a rug depends on either **unconstructable** (a theorem forbids the mechanism) or
**publicly checkable** (a replayable function over on-chain state). Each claim below is
mapped to a primitive that **exists in the tree today** (verified with the theorem names and
files confirmed):

| Anti-rug property | The claim | Real verified primitive |
|---|---|---|
| **No hidden supply** | The total is disclosed and provable; there is no undisclosed mint door. Circulating supply cannot exceed the schedule the sale committed. | The supply-authority biconditional `execMintA_iff_spec` (`metatheory/Dregg2/Circuit/Spec/supplycreation.lean:177`) — the executor commits a mint **iff** the independent `MintASpec` holds; non-vacuous (`execMintA_iff_spec_satisfiable`, `KeystoneAuditSupply.lean:83`). On the EVM realization: `DreggLaunchToken` mints exactly once for the whole cap, no second door. |
| **No snipe / no front-run** | The sale clears the whole book at **one uniform price**, so there is no earliest block to win and no ordering edge — the sniper advantage dies structurally, independent of the privacy layer. | `uniform_price_no_arbitrage` (`metatheory/Market/Optimality.lean:130`) + `uniform_price_optimal` (`:174`); the batch-clearing fold `clearedBatch_optimal` (`metatheory/Market/FhEggClearing.lean:358`). Sealed-bid privacy over the bids: `reveal_binds_committed` (no late-switch, `SealedAuction.lean:248`), `uncommitted_cannot_win` (`:415`). |
| **No insider pre-allocation** | No extra allocation can be silently inserted into the cleared book; the creator, if it buys, pays the same uniform price everyone pays. | The aggregation is permutation-faithful — `no_insert` / `no_drop` (`Market/Aggregation.lean`); undisclosed *supply* is blocked by `execMintA_iff_spec` above. Undisclosed *conduct* (a pre-buy off-schedule) is a bonded predicate, not a theorem — stated as such in §4.3 below. |
| **No silent LP / mint drain** | Graduated liquidity is pool-owned and never-insolvent; there is no creator withdrawal door and no thin-air funding. | `pool_solvent_forever` (`metatheory/Market/Liquidity.lean:145`) — starting solvent, under **any** valid fill schedule the pool reserve is never negative; the graduation pool is `DreggSolventPool.sol`, its seeding on-chain-verifiable (`GraduationSeedMismatch` reverts a hidden seeding). |
| **Conservation-locked value** | Every clearing is zero-sum through the real ledger measure; nothing is minted in the match. | Per-asset conservation `clearing_conserves_per_asset` + `mint_refused` (`Market/Clearing.lean`); the shielded no-mint `created_value_conservation` (`metatheory/Dregg2/Exec/ShieldedValue.lean:148`) for the private path. |
| **A verifiable receipt** | Every number a launch page shows is read back from the chain (or the node's own event stream), not a mirror — the fill, the one clearing price, the holder distribution, the disclosed schedule vs its on-chain commitment. | `launchpad-web` reads the real `DreggLaunchpad` contract / live node; the "why it's fair" panel grades each claim (PROVED Lean theorem / BUILT on-chain / REPLAYABLE) with `file:line` citations. The gate proves every displayed number is the contract's. |
| **The privacy dial** | The buyer/issuer picks the posture — fully **Open** (max transparency, every bid public and fair-by-proof) or **Shielded** (distribution amounts private, supply still provable) — over one verified kernel whose guarantee never changes. | The three-tier dial (`DREGGFI-PRIVACY-TIERS.md`): Open (Tier 2, now), Shielded (Tier 1, building — `shielded_ring_clears`, `ShieldedClearing.lean:182`). Same soundness kernel at every tier. |

**The sharpest anti-rug line:** *every deployed launchpad's anti-abuse feature is, by the
platforms' own admission, a mitigation — pump.fun says its guardrails "do not eliminate market
risk," anti-snipe is "not a guarantee of fairness," "fair launch" is a label. On dregg the
three dominant abuses are theorems you cannot route around: sniping is unconstructable (one
uniform price removes the value of ordering), hidden supply is unconstructable (the mint
biconditional), and the silent LP/mint-drain rug has no door (pool solvency + disclosed mint)
— and every number the buyer sees is one they can recompute from the chain themselves.*

---

## 4. Buildable now vs BD-speculative (kept honest and separate)

### 4.1 Buildable now — on machinery that has landed

The provably-fair launchpad **product** does not need new cryptography. It is a composition
over primitives that are proven and Lake-green, plus contracts and a web layer that already
exist and pass their gate:

- **The fair sale** — sealed-bid commit→reveal + uniform-price clearing. The theorems
  (`uniform_price_no_arbitrage`, `reveal_binds_committed`, `uncommitted_cannot_win`) are
  PROVED; the EVM realization (`DreggLaunchpad.sol`) is written and tested (71 on-chain tests
  across 6 suites; the e2e gate runs a full fair launch + adversarial checks against the
  deployed bytecode; the anti-rug core is additionally proven symbolically over the compiled
  bytecode via Halmos).
- **The supply-conservation proof** — `execMintA_iff_spec` PROVED; `DreggLaunchToken` is
  hard-capped and single-mint on the EVM side.
- **The solvent graduation** — `pool_solvent_forever` PROVED; `DreggSolventPool.sol` is the
  never-drainable pool.
- **The public verifiable receipt** — `launchpad-web` reads the real contract / node and
  grades every claim; replayable discovery ranks by a pure function over public fields (no
  pay-to-rank input).

**The concrete MVP path** (what to actually stand up):

1. **Deploy the real `DreggLaunchpad` to a public testnet** (Base-Sepolia today; Robinhood
   Chain / Arbitrum-Orbit as the BD target below) — the contracts are written; this is a
   forge deploy + a config point, not new work.
2. **Run one real, honest fair launch end-to-end** through `launchpad-web` — register a
   disclosed schedule, take sealed bids, clear at one uniform price, settle non-custodially,
   graduate into the solvent pool — with the "why it's fair" panel live and every number
   checkable on-chain.
3. **Publish the verifiable receipt** — the launch page where a buyer re-derives the
   clearing price, checks the disclosed supply against its on-chain commitment, and sees the
   holder distribution from Transfer logs. This *is* the differentiated product: not "trust
   our fair launch," but "here is the launch, verify it."
4. **Name the open welds honestly on the page** — the attestor ladder is BUILT at both rungs
   (launches run rung-1 REPLAYABLE today; the v1 k-of-n `CommitteeAttestor` + fraud proof and
   the trustless-v2 `DreggProofAttestor` — attestation iff a verified Groth16 wrap proof through
   the OCIP socket — both exist, with the proof attestor's one trust point being the `bindLaunch`
   binder that links a launch to its proof: the proof itself binds only the dregg state
   transition, no launch id or clearing price lane), the `x·y=k` pricing curve above the
   solvency floor (BUILT — `DreggSolventPool` keeps `x·y` non-decreasing under the fee,
   `ConstantProductViolated` guards it), the shielded-bidding upgrade (SPEC/MODEL), and the conduct-bond
   launch-predicate wiring (design, not yet written). These are labeled scheduled sharpening,
   not surprises.

### 4.2 BD / partnership-speculative (ember-gated, not a build claim)

- **"The next pump.fun on Robinhood"** — deploying to Robinhood Chain and any co-marketing /
  distribution relationship is a **business-development move**, not an engineering one. The
  contracts already target chainId 46630, but a partnership, a listing, or a "launch into
  Robinhood" is a relationship dregg does not control and should not narrate as done.
- **A live mainnet with real value at stake** — requires a live dregg devnet/testnet with
  settlement contracts (DREGGFI-PREREQS "live devnet"), and VK-epoch flip + re-genesis are
  ember-gated. The mechanism is buildable now; a *mainnet money-in* launch is gated on
  operator/deploy steps and a security posture decision.
- **The regulated / compliant-distribution pitch** — the confidential-distribution framing
  (`ECLIPSE-ZAMA-CONFIDENTIAL-FINANCE.md` §4.4) is substance dregg has and Zama has packaged
  as a pitch; turning it into a compliance-grade product is a positioning + legal effort, not
  a code effort.

The discipline: the **provably-fair launchpad product is buildable now on the verified
engine**; the **"launch into Robinhood" is a BD bet**. Never dress the second as the first.

---

## 5. Honest risks — what the proof does and does not cover

The fairness proof is precise, and its precision is the point. It covers the **on-chain,
mechanical surface of the sale** — and nothing beyond it.

- **A bad token is still a bad token.** The mechanism proves the *distribution and disclosure*
  are fair; it makes **no claim about the token's value or the team's competence.** A fairly
  launched, honestly disclosed, un-rugged token can still go to zero. Mechanism design fixes
  the rigged wheel, not the casino.
- **The proof cannot stop off-mechanism team behavior.** It proves the sale cleared fairly,
  the supply is real, and there is no hidden-mint or silent-LP-drain door. It **cannot prove
  the team will keep shipping, keep the domain up, or not abandon the project.** The anti-rug
  guarantee is about the *on-chain provable surface* (supply is real, the sale was fair, the
  LP is not drainable) — the schedule-violating creator dump is a **bonded** predicate
  (economic disincentive, holder-compensating slash), not a theorem, and the conduct-bond
  launch-predicate wiring is designed-not-yet-written. A team can still be a bad team off the
  mechanism; the honest claim is that they cannot *rug via the mechanism*, and that their
  on-chain conduct is publicly replayable.
- **Sybil uniqueness is an identity-layer problem.** Uniform-price clearing neutralizes the
  sybil *advantage* in the raise (many wallets buy no better price than one) — PROVED — but
  dregg cannot prove one human ≠ many wallets. Proof-of-personhood is out of scope.
- **Wash-trading for attention is detection, not prevention.** Uniform-price clearing kills
  *price*-motivated wash trades; volume-faking for attention is caught by a replayable
  statistical screener (after-the-fact), the same limit the whole industry faces.
- **Regulatory / compliance exposure.** A launchpad facilitates token sales; that carries
  real securities / KYC / jurisdictional questions that are legal-and-BD work, wholly outside
  what any Lean theorem covers. This is named, not solved.
- **Not yet deployed with value at stake.** The contracts pass their gate and the anti-rug
  formal verification against local bytecode; a public deploy carrying real funds is a
  separate, gated step with its own security review and a production Groth16 ceremony (the demo
  verifier rides a dev ceremony).
- **Formal-verification bound.** The Halmos proof is symbolic execution with bounded call depth
  and a bounded reserve band — strong evidence over all inputs *within the bound*, not an
  unbounded inductive proof (an unbounded proof needs Certora/Kontrol or a direct derivation
  from Lean, the named next step).

**The claim, stated exactly:** dregg can build the launchpad where the *sale is provably
fair and the supply is provably real* — the on-chain surface a rug needs, closed by theorems
and a public receipt. It cannot make a bad team good or a bad token valuable, and it says so.
That honesty is itself the product: in a space where 98.6% of launches are scams and the
latest "first DegenFi protocol" just rugged, "verify the sale yourself" is the one pitch a
vaporware launchpad cannot copy.

---

## See also

- `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` — the deep mechanism design (four verified turns,
  the abuse→antidote table, the conduct bond).
- `docs/deos/DREGGFI-PRIVACY-TIERS.md` — the Dark/Shielded/Open dial over one verified kernel.
- `docs/deos/ECLIPSE-ZAMA-CONFIDENTIAL-FINANCE.md` §4.4 — confidential distribution without
  hidden supply.
- `chain/contracts/launchpad/` — the deployed EVM realization (`DreggLaunchpad.sol` et al.).
- `launchpad-web/` — the product layer driving the real contract, with the fairness gate.
- `metatheory/Market/{Optimality,FhEggClearing,Liquidity,Clearing}.lean`,
  `metatheory/Dregg2/Intent/SealedAuction.lean`,
  `metatheory/Dregg2/Circuit/Spec/supplycreation.lean` — the verified cores.
