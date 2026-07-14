# p0, but dreggic — the create-launch-trade-lock stack where the rug doors are theorems

*People keep comparing dregg (and ember) to **p0**. This doc identifies p0 accurately (with
evidence and a confidence flag), maps its model honestly, and designs the dregg-native version —
the same job p0 does (create a token, launch it, trade it, lock/vest it), rebuilt on dregg's
verified-private-fair engine so the abuses p0 inherits from the launchpads it deploys to become
**unconstructable** rather than mitigated. Present tense, what-is. Every claim carries a trust
grade (the OCIP spine, `DREX-DESIGN.md` §0). The honest have-vs-build-vs-gated split is §5 and is
load-bearing — this is a design over real landed pieces, not a shipped product.*

Trust grades: **PROVED** (machine-checked Lean about the artifact) · **BUILT** (real code, both
polarities tested, not yet a theorem) · **ATTESTED** (HW/zkTLS provenance) · **REPLAYABLE** (a pure
function over public data anyone re-derives) · **UNBUILT** (named, designed, not written).

---

## 1. What "p0" is — the identification (evidence + confidence)

**Primary identification (confidence: MEDIUM-HIGH given ember's launchpad/degen context):
p0 Systems — `p0.systems`.** An AI-powered token-creation-and-trading stack on Solana. Its own
landing page bills it as *"AI-Powered Token Factory for Solana … Built for agents. Build meme
coins with AI. Deploy to Pump.fun or Bags.fm in 60 seconds."* Three products under one roof
(per the Bitrue explainer and the site):

- **AI Token Factory** — generate + configure a Solana SPL token with AI assistance, then
  one-click **deploy to an external launchpad** (Pump.fun, Bags.fm).
- **p0 Terminal** — a memecoin **trading terminal**: live charts, token swaps, portfolio.
- **p0 Locker** — token **locking, vesting schedules, and airdrop distribution via Merkle proofs**.

Token: `P0`, an SPL on Solana (~1B supply; contract ends `…EBAGS`), ~$3.3M market cap at survey,
thin/concentrated liquidity, only days old — a brand-new micro-cap. A hype-account tweet claims a
"real AI revenue → recurring buyback" token model and names a founder "Cory" — **both LOW
confidence** (single-source, promotional). The explainers themselves flag rug-pull risk from wallet
concentration.

**Why this is the most-likely p0 for ember's context.** ember builds `DREGG-LAUNCHPAD-DESIGN.md`
(a launchpad), DrEX (a trading terminal/exchange), and vesting/lock machinery — the *exact* three
surfaces p0 Systems bundles (factory + terminal + locker). The comparison people draw is
surface-for-surface. (Note: `DREGG-LAUNCHPAD-DESIGN.md` §1.1 previously logged "p0" as an
*unverified* NOXA-adjacent term; this doc resolves that open thread — p0 is **p0 Systems**, an
independent product, not a NOXA mechanic.)

**Secondary candidate (report honestly — genuinely plausible): Project 0 / "P0" by MacBrennan
(`@macbrennan_cc`).** A *"DeFi-Native Prime Broker"* — borrow against your entire DeFi portfolio
across venues. This is a different p0: a **cross-margin / prime-broker** product, not a launchpad.
It maps cleanly onto DrEX rung 7 (cross-margin via the capability mandate), so if the people
comparing ember to "p0" mean the prime broker, §4's row 6 (mandate cross-margin) is the direct
answer. It is the less-likely reading only because ember's dominant public surface is the
launchpad+terminal, which is p0 Systems' shape.

**Explicitly NOT fabricated / ruled lower:** "P0" also generically means "Priority-0" (an
engineering term, not a product), and there is an unrelated AI-infra `@p0` (Carra Wu / Parag
Agrawal). Neither fits the crypto-comparison framing.

**Net:** p0 = **p0 Systems** (`p0.systems`), an AI memecoin factory + terminal + locker on Solana —
MEDIUM-HIGH confidence; with **Project 0 the prime broker** as the honest secondary. The design
below is built primarily against p0 Systems and picks up the prime-broker reading in §4 row 6.

---

## 2. The p0 (Systems) model — features, value-prop, why people use it, its risks

**Model.** p0 is a *convenience layer over the pump.fun-class launch economy*. It does not run its
own settlement or clearing — the AI Factory **emits a token and hands it to an external launchpad**
(Pump.fun/Bags.fm) that runs the actual bonding-curve launch, and the Terminal **routes swaps
through public Solana DEXs**. p0's value is speed and packaging: AI-drafts the token, deploys in 60
seconds, gives you a terminal to trade it and a locker to vest it.

**Value-prop / why people use it:** (1) zero-friction creation — describe a coin, AI configures it,
ship in a minute; (2) one surface for the whole memecoin loop (make → launch → trade → lock);
(3) "built for agents" — an API surface aimed at automated/agent-driven launching and trading;
(4) a token with a buyback narrative.

**Weaknesses / risks — exactly the surface dregg's engine addresses:**

| p0 risk | Why it exists | The dregg-relevant gap |
|---|---|---|
| **Inherited rug economy** | p0 deploys to Pump.fun/Bags.fm, where a 2025 Solidus Labs report found ~**98.6%** of tokens showed rug/scam/pump-dump traits (`DREGG-LAUNCHPAD-DESIGN.md` §1.2) | p0 is a *deploy button*; the rug doors live in the target launchpad's contract and p0 does not close them |
| **Launch-block sniping / insider pre-allocation** | bonding-curve launches fill at time-priority; fresh coordinated wallets snipe the curve bottom (§1.2 B/C) | p0 offers no batch/sealed clearing — sniping is unmitigated |
| **Public-DEX MEV on the terminal** | swaps route through public Solana DEXs; visible in-flight | no execution proof, no privacy, sandwich-exposed |
| **Trusted-contract locker** | the Locker is an ordinary contract you trust to hold/release | a lock is a promise, not a proof; vesting-violation is off-chain judgment |
| **AI-emitted, unaudited contract** | the Factory ships a token contract; correctness is not verified | a mint/owner-drain door can sit in the emitted code |
| **Micro-cap / concentration / token risk** | thin liquidity, concentrated wallets | market risk mechanism design cannot fix (dregg does not claim to) |

The one-line reading: **p0 makes it *fast* to enter the memecoin loop, but it inherits every trust
and abuse property of the launchpads it deploys to and the public DEXs it routes through — it
packages the loop, it does not verify it.**

---

## 3. The dreggic thesis — same job, verified

> **p0 lets you mint a memecoin with AI and shove it onto pump.fun, where ~98.6% of tokens rug, then
> trade it on a public DEX where you get sandwiched. dregg does p0's exact job — create, launch,
> trade, lock — but on an engine where the rug doors are Lean theorems you cannot route around, the
> clearing is fair-by-proof instead of solver-trust, the whole loop runs private (reveal-nothing) or
> no-viewer (a `t`-of-`n` cryptographic bound), and it settles cross-chain by proof with no bridge
> honeypot. Same loop; the abuses are unconstructable instead of merely mitigated.**

dregg does not "compete with p0 on features" — it hosts the *identical* create-launch-trade-lock
loop on a substrate where p0's inherited risks are theorems-forbidden. The engine already exists;
the p0-parity product is a composition + a frontend over it (§5).

---

## 4. Feature-by-feature: p0 → p0-but-dreggic (grounded in real pieces)

Each row: the p0 feature, the dregg-native equivalent, the concrete advantage, and the grade of the
dregg piece it rests on (cited to real files).

### Row 1 — AI Token Factory → disclosed-supply creation turn + FV'd emit
- **p0:** AI drafts an SPL token; deploys an unaudited contract to an external launchpad.
- **dreggic:** the AI Factory emits a token whose creation is a **disclosed-supply mint turn** —
  `execMintA_iff_spec` (`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean`): the executor commits a
  mint **iff** the independent spec holds, requires a **live issuer cell**, and **no undisclosed
  supply door exists** in the ledger. The emitted contract is run through the **audit-service**
  before deploy (below).
- **Advantage:** on p0 a hidden-mint / owner-drain door can sit in the AI-emitted code. On dregg,
  **hidden supply is unconstructable** (PROVED) — the schedule (total supply, vesting, creator
  allocation) is a *public input of the proof*, so the launch page displays it and a re-executor
  checks it (REPLAYABLE).
- **Grade:** PROVED (the mint biconditional + live-issuer gate).

### Row 2 — "Deploy to Pump.fun/Bags.fm" → dregg IS the launchpad where fairness is a theorem
- **p0:** hands the token to a bonding-curve launchpad where sniping, insider pre-allocation, and
  LP-rug are mitigated-at-best.
- **dreggic:** the launch runs on dregg's own four-tower launchpad (`DREGG-LAUNCHPAD-DESIGN.md`):
  a **sealed-bid batch** cleared at a **single uniform price** (`SealedAuction.lean` +
  `Market/Optimality.lean` `uniform_price_no_arbitrage`/`uniform_price_optimal`), graduating into a
  **provably-solvent pool** (`Market/Liquidity.lean` `pool_solvent_forever`), with a
  **holder-compensating conduct bond** on the residual discretionary abuse.
- **Advantage — three abuses become UNCONSTRUCTABLE, not settings you tune:** sniping/time-priority
  (one uniform price removes the *value of ordering* — no earliest block to win, PROVED); hidden
  allocation (the mint biconditional + `no_insert`, PROVED); silent LP/mint-drain rug (pool solvency
  + disclosed mint — **no creator LP-withdrawal door**, PROVED). What a theorem can't forbid (a
  creator's schedule-violating dump) is a **REPLAYABLE bond predicate** (`dump_beyond_schedule`)
  whose slash **compensates holders, never the platform**.
- **Grade:** PROVED (uniform-price clearing + pool solvency + disclosed mint) / BONDED (conduct) —
  with named welds (the `x·y=k` curve above the solvency floor, and the launch-predicate/slash-leg
  wiring) in §5.

### Row 3 — p0 Terminal → DrEX with a privacy dial
- **p0:** a memecoin terminal that routes swaps through public Solana DEXs (MEV-exposed, no
  execution proof).
- **dreggic:** trades clear through **DrEX** — a proof-carrying exchange where the clearing *rules*
  are theorems (rung 1, `Market/{Clearing,Fairness}.lean`) and each fill **settles through the
  proved kernel** (`intent/src/verified_settle.rs` → `@[export] dregg_record_kernel_step` over
  `Exec.recKExec`). And it offers **three privacy tiers over one verified kernel**
  (`DREGGFI-PRIVACY-TIERS.md`): **Tier 2 OPEN** (public but fair-by-proof), **Tier 1 SHIELDED**
  (the transcript reveals nothing — `[nullifier, root, value_binding]` per leg, the solver sees),
  **Tier 0 DARK** (adversarial no-viewer — the crossing runs in output-boundary MPC revealing only
  `(p*, V*)`, a `t`-of-`n` cryptographic bound with no standing master key).
- **Advantage:** p0's terminal *is* the public-mempool sandwich surface. DrEX is **fair-by-proof**
  (an over-debiting/minting clearing is unconstructable), and its top tier is the **only DEX whose
  no-viewer is adversarial** — every competitor's "private" tier rests on a viewer or a policy
  (`DREX-NO-VIEWER-SURPASS.md`).
- **Grade:** PROVED (rung-1 clearing + settlement, ledger-realized) / model-PROVED (uniform-price,
  Tier-2) / BUILT (shielded pool, the fold+MPC-crossing PoC — measured sub-10ms fold, ~1–7ms
  crossing, reveal-only-`(p*,V*)`) / Frontier (Tier-0 production ladder).

### Row 4 — p0 Locker → committed-`Pred` vesting + bonded conduct
- **p0:** a locker contract you trust to hold and release on schedule; Merkle-proof airdrops.
- **dreggic:** vesting is a **committed monotone `Pred`** posted in the creation turn (a public
  input of the proof), and a schedule violation is the **REPLAYABLE** predicate
  `soldSoFar(creator) > unlocked(schedule, epoch)` — a **bonded slashing event** that routes to a
  holder-compensation pool through a conserving `settleRing` (`restitution + remainder == seized`,
  the relay-dispute primitive, PROVED).
- **Advantage:** p0's lock is a promise enforced by a trusted contract; dregg's vesting is a
  *public schedule anyone re-derives* and its violation is a *bonded, holder-compensating* event —
  the `DREGG-LAUNCHPAD-DESIGN.md` §1.3 failure ("unlocks are just scheduled dumps") becomes an
  economic tooth.
- **Grade:** PROVED (slash-conservation, relay-dispute primitive) / REPLAYABLE (the predicates) /
  UNBUILT (the *launch-predicate wiring* + slash-leg `_refines_` alignment — §5).

### Row 5 — Emit-then-hope → the assisted audit-service
- **p0:** ships an AI-emitted contract with no verification stage.
- **dreggic:** **every contract onboarded runs through the DREGG-kernel audit**
  (`DREGG-AUDIT-SERVICE.md`, tool at `tools/dregg-audit/`): (A) deterministic rug-forensics over a
  9-door taxonomy, (B) a **Halmos symbolic-EVM proof** of the supply-cap shape on real bytecode
  (the EVM twin of `execMintA_iff_spec`), (C) a `codex` adversarial pass, (D) human triage. On the
  hostile sample it flags 7/9 rug doors and returns a **machine-checked counterexample** that the
  cap is breakable.
- **Advantage:** p0 has no such gate; dregg makes "audited-by-construction" the default onboarding
  step. **Honest scope:** it is an *assisted audit* (finds + proposes, with a proof where a standard
  invariant applies) — **not** push-button certification and **not** an auto-secure-rewrite.
- **Grade:** BUILT (the tool + a sample run; Halmos proof machine-decided).

### Row 6 — "Built for agents" → the capability mandate (and the prime-broker reading)
- **p0:** an API for agents to launch/trade. (And the *secondary p0* — Project 0 — is a DeFi prime
  broker for cross-portfolio borrowing.)
- **dreggic:** an agent trades under an **attenuable capability mandate**
  (`metatheory/Dregg2/Agent/Mandate.lean`, `intent/src/agent_mandate.rs`): non-amplifying
  (`subtree_rights_le_root`), budget-conserved (`children_no_oversubscribe`), revocable-at-tip, and
  **materialized into committed executor effects**. This is exactly the prime-broker/cross-margin
  primitive (DrEX rung 7): "trade up to $X, venues {…}, no withdrawals," checked by the settling
  venue.
- **Advantage:** on p0 an agent holds a raw key (full authority; a compromised agent drains you).
  On dregg a **mandate breach is unconstructable, not monitored** — no prime broker offers
  cryptographically-scoped, provably-non-amplifying delegation. This is the direct answer if the
  "p0" people mean **Project 0 the prime broker**.
- **Grade:** PROVED (delegation/budget/revocation + materialization) / UNBUILT (per-trade
  caveat-admission in-circuit — the one open weld, §5).

### Row 7 — Single-chain, single-venue → OCIP cross-chain security socket
- **p0:** Solana-only; the token lives where it's deployed.
- **dreggic:** a dregg clearing/settlement **attests to any chain by proof** through the **OCIP
  socket** (`OCIP-SECURITY-SOCKET.md`, `chain/contracts/socket/`): an external contract accepts a
  trade/settlement/solvency claim only if a DREGG proof attests it, keeping its own custody. The EVM
  Groth16 wrap is done end-to-end on real data; Solana-inbound holdings proofs are REAL.
- **Advantage:** **dregg networks *proofs*, not tokens** — no bridge validators to corrupt, no
  convergence honeypot (a bridge's only verb is move-the-token; the vault is the honeypot).
- **Grade:** INTERFACE + tested DEMO (11 tests, real BN254 pairing; on a single-party dev Groth16
  ceremony — production MPC ceremony is §5/gated).

### Row 8 — Token = buyback narrative → $DREGG buys services, bonded-not-boosted
- **p0:** a P0 token with a revenue→buyback story; fees/premium features.
- **dreggic:** **$DREGG buys SERVICES** (the audit-service, elevated-assurance programs), **never
  features**; promotion is **bonded-not-boosted** and ranking is a **REPLAYABLE** pure function
  anyone re-derives (the OCIP §6 fee discipline — slashes compensate holders, the platform earns on
  volume/creation, never on slashing).
- **Advantage:** no boosted-listing pay-to-win; no incentive to manufacture misconduct.
- **Grade:** REPLAYABLE (ranking) / PROVED (fee-splitter money-paths) / designed (the bonded
  attention market as product — UNBUILT).

**The composition p0 structurally cannot copy.** Every economic fact above is a **recursion leaf**
(`note_spend_leaf_adapter`, `mpt_holding_leaf`, `bridge_leaf_adapter`, …) folded by
`joint_turn_recursive.rs` into one apex proof that shrinks BN254-native. A dreggic **structured
launch** is one proof folding {disclosed mint ⊕ uniform-price clear ⊕ pool solvency ⊕ cross-chain
holding ⊕ conduct bond} — verified once, on any chain, reusable as a leaf above it. p0 is a UI over
other people's contracts; dregg is a single verified object the whole loop composes into.

---

## 5. Honest state — HAVE vs BUILD vs GATED

**HAVE (real, landed — the engine p0-dreggic composes on):**
- DrEX rung 1 (clearing + settlement) **ledger-realized, PROVED**; rungs 4/5/6 (uniform-price /
  priced / pool-solvency) **model-PROVED, axiom-clean** (`Market/{Clearing,Fairness,Optimality,
  Priced,Liquidity}.lean`).
- Sealed-bid commit→reveal **PROVED** (no-peek/no-switch, over a real Blake3 kernel).
- Disclosed-supply mint **PROVED** (`KeystoneAuditSupply.lean`).
- The **audit-service** tool **BUILT** with a sample run (`tools/dregg-audit/`).
- The **OCIP socket** — INTERFACE + tested DEMO, real BN254 verification (`chain/contracts/socket/`).
- The **shielded pool** BUILT (identity privacy); the **FHE fold + output-boundary-MPC crossing**
  PoC **BUILT + measured** (`fhegg-fhe/`).
- The **capability mandate** PROVED + materialized (`Mandate.lean`).
- EVM Groth16 wrap end-to-end on real data; Solana-inbound holdings proofs REAL.

**BUILD (the p0-parity surface not yet built — real work, named):**
- The **AI Token Factory front** (AI-assist → FV'd template emitter feeding the audit-service +
  disclosed-schedule creation turn).
- The **DrEX trading-terminal frontend** (the p0-Terminal equivalent over Tier-2 DrEX).
- The **Locker** wired to the conduct-bond launch predicates + the `MarketRefinement` slash-leg
  `_refines_` alignment (the "design, not new science" weld).
- **Rung 5 ledger-realization** (priced/partial-fill off `DemoRes`) and **rung 3** (the shielded
  ring AIR: N-leg + partial-fill + the value-commitments-in-AIR weld + reveal-nothing theorem) for
  the private launch/terminal.
- The **`x·y=k` curve** above the pool-solvency floor.
- The **bonded attention market** as a product (the wash-trading detection lane, REPLAYABLE
  screener).

**GATED (ember / deploy — not a build gap, a launch decision):**
- A **live devnet/testnet** with settlement contracts you can point a tx at.
- **VK-epoch flip + re-genesis** (ember-gated per memory).
- **Mainnet MPC ceremony** replacing the single-party dev Groth16 (OCIP + EVM wrap production trust).
- Any **live-token launch** (per `reference-dregg-token-market.md` / `reference-public-surfaces`:
  $DREGG buys services, never features; product domain `dregg.net`).

**What dregg does NOT claim (no overclaim, matching p0's real limits):** a bad token is still a bad
token — dregg guarantees fair *distribution and disclosure*, not the coin's value; sybil-uniqueness
is an identity-layer problem (the advantage is neutralized in-raise, uniqueness is not proved);
wash-trading-for-attention is *detection*, not prevention; Tier-0 no-viewer is `t`-of-n, not
absolute.

---

## 6. The build plan — reaching "p0 but dreggic," phased

**Phase 0 — compose-now (NEAR; the pieces are Lean-green today).** Wire the sealed-bid →
uniform-price launchpad end-to-end (a Lean-tower composition on proven substrate) and ship the
**audit-service publicly** (the tool exists) + the **OCIP socket demo**. Deliverable: *"the
launchpad where fairness is a theorem, and audit any contract through the DREGG kernel."* This is
p0's launch+lock loop with the three abuses already unconstructable.

**Phase 1 — Tier-2 product surface (the p0 look-alike, verified).** Build (a) the **AI Token
Factory** front that emits an FV'd template (Halmos-proven cap) + disclosed-schedule creation turn,
(b) the **DrEX terminal frontend** over public Tier-2 clearing (fair-by-proof), (c) the **Locker**
as committed-`Pred` vesting bound to the conduct-bond predicates. Deliverable: *create → launch →
trade → lock, the whole p0 loop, every step a verified turn.*

**Phase 2 — Tier-1 SHIELDED (private launch + private terminal).** Ledger-realize rung 5
(priced/partial-fill), land the shielded ring AIR (N-leg + partial-fill + accumulator bind) and the
**reveal-nothing theorem** (the crux research item), weld shielded *bidding* into the launchpad
(rung 3). Deliverable: *the private version of the whole loop — the transcript reveals nothing.*

**Phase 3 — Tier-0 DARK (the no-viewer terminal p0 cannot build).** Production output-boundary MPC
(partial-decrypt-into-shares + malicious-secure online) + the PQ-commitment DLog→Poseidon2 cutover.
Deliverable: *adversarial no-viewer clearing — a `t`-of-n cryptographic bound, post-quantum.*

**Cross-cutting (ember-gated, runs alongside):** stand up the live devnet with settlement
contracts, run the mainnet MPC ceremony (retiring the dev Groth16 for OCIP + the EVM wrap), and
flip the VK epoch / re-genesis. These gate *deploy*, not *build* — the phases above land on the
tree first.

---

## See also
`DREGG-LAUNCHPAD-DESIGN.md` (the four-tower launch; the abuse→antidote table) ·
`DREX-DESIGN.md` (the proof-carrying exchange; trust grades §0) ·
`DREGGFI-PRIVACY-TIERS.md` + `DREX-NO-VIEWER-SURPASS.md` (the Open/Shielded/Dark dial; the
output-boundary-MPC no-viewer) · `DREGG-AUDIT-SERVICE.md` (`tools/dregg-audit/`) ·
`OCIP-SECURITY-SOCKET.md` (`chain/contracts/socket/`) · `RUG-FORENSICS-VS-DREGG.md` ·
`metatheory/Market/{Clearing,Fairness,Optimality,Priced,Liquidity}.lean` ·
`metatheory/Dregg2/{Intent/SealedAuction,Verify/KeystoneAuditSupply,Agent/Mandate}.lean` ·
`intent/src/{verified_settle,agent_mandate}.rs` · `fhegg-fhe/` ·
`reference-dregg-token-market.md` (the $DREGG-buys-services posture).

*p0 identification: `p0.systems` (primary, MEDIUM-HIGH confidence) + Project 0 / @macbrennan_cc
(secondary). Sources: p0.systems landing page; Bitrue "What is p0 Systems"; CoinGecko/LBank P0
market data; Kagi FastGPT (founder/model claims LOW confidence, single-source). Landscape stats
(Solidus 98.6%, abuse taxonomy) cited in `DREGG-LAUNCHPAD-DESIGN.md` §1.*
