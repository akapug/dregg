# Community brief — the dregg cloud, the forge, and the starbridge apps

*The three newest stories, in plain language, with every claim checkable and the honest status
labeled. Written for community explainers (articles, threads, series) — the register rule is the
product rule: never claim what a reader can't verify. Source-of-truth pointers are given per
section so a drafter can go deeper; the honest-status lines are NOT optional trimming — they are
the brand.*

---

## 1. The dreggnet cloud — a decentralized cloud where lying costs your stake

**The plain version.** dregg is growing a cloud: storage, compute, and code-checking are *jobs*
anyone can take on by posting a bond. Do the job honestly, keep your bond and earn the fee. Get
caught lying — and the system is built so lies *get caught by math, not by reputation* — and your
bond is slashed. In several configurations the person who catches you **gets paid from your bond**.

**Why it's different from every other "decentralized cloud":** the promises are not a whitepaper.
The storage market's end-to-end guarantee is a machine-checked theorem
(`metatheory/Dregg2/Storage/ClientProtocol.lean`): store a file erasure-coded across n providers,
and (1) the data survives as long as any k pass their audit, (2) an honest provider can never be
slashed, (3) a withholding provider always can be — and *cannot fake a passing audit*
(`por_refuses_substitution`). Derived, not asserted. The provider never learns what it stores
(ciphertext + commitment), and the client never trusts the provider (every served chunk is
verified against a root the client holds).

**The pieces, for the deep-enders:** Reed–Solomon k-of-n with a Lean uniqueness proof
(`Erasure.lean` — real algebra, no crypto assumption), rateless fountain codes (`Fountain.lean`),
proof-of-retrievability audits (`Retrievability.lean`), the bonded deal market as
executor-enforced cell programs (`ProviderMarket.lean`, `MarketAudit.lean`), light-client
sampling + reconstruction over untrusted sources (`storage/src/retrieval.rs`).

**Honest status:** the machinery and the proofs are in-tree and test-covered; a live public
provider mesh is not yet deployed. This is "built and proven, being wired to the running
federation" — not "rent your disk out today."

---

## 2. The forge — GitHub without git, secured like an optimistic rollup

**The plain version.** dregg has its own code forge. Not a git host with a review UI — the version
control *is* dregg's patch theory: a repo is a cell, a commit is a receipted verified turn, a merge
is a mathematical pushout (provably sound — conflicts are first-class objects that must be
resolved, never silently clobbered), and *who may push/merge/review* is a capability you hold,
not a checkbox an admin can flip.

**The headline for a crypto audience — CI with skin in the game.** When a pull request needs a CI
check ("do the tests pass?"), the forge doesn't trust the machine that ran them. The operator picks
a rung on an assurance dial (`dregg-doc/src/ci_assurance.rs`):

| rung | plain reading |
|---|---|
| `TrustedSigned` | "trust this host" — internal repos only |
| `ReExecuted{quorum}` | N independent machines re-run it; majority wins |
| `OptimisticChallenge{window}` | accepted fast — but anyone can re-run it in the window and prove a lie |
| `Proven{vk}` | the check result carries a STARK proof; trust nobody |
| `Staked{bond, inner}` | any of the above **plus a slashable bond** |

The recommended default is `Staked{ReExecuted{quorum:3}}` — the optimistic-plus-stake model, the
same economic shape as optimistic rollups, applied to code review. A lying CI host is convicted by
a real re-execution divergence (a `Conviction` is unforgeable — only genuine divergence mints one,
so an honest host is *never* slashed), and the slash beneficiary can be configured as
`Challenger` — **the watcher who proved the lie gets the liar's bond.** The CI runner itself is
confined (jailed) and *materializes the code from the committed patch history* — you cannot hand
it a doctored working tree (`forge-ci-runner`, refusal: `MaterializationMismatch`).

**Honest status** (per `docs/operator/forge-operations.md`): the assurance policy, governed
rotatable key sets, confined runner, bond post/slash/release, and challenge detection are operable
today on a single host or test federation, unit-covered. The cross-node transports (challenge
gossip, stake registry, federation HTTP wiring) are named seams — transport work over machinery
that already verifies, not soundness holes.

---

## 3. The starbridge apps — the arcade nobody knows exists

**The plain version.** There are working apps on this thing, and each one is a small demonstration
that *the system does the protecting* — the cheating move isn't against the rules, it's **refused
by the executor**. Ten are real today (Rust crate + tests + most with web surfaces, running against
the canonical executor with all gates firing — `starbridge-apps/README.md`):

- **privacy-voting** — one ballot cell per voter, write-once: a second vote is a refusal; a
  shrinking tally is a refusal.
- **bounty-board** — post → claim → submit → payout; first-claimer-wins because the claimant slot
  is write-once. A second claim doesn't lose a race — it *cannot commit*.
- **compute-exchange** — escrowed compute jobs: bids over budget refused, settlement must satisfy
  `paid + refunded == budget` (a value-conjuring settle is a refusal), lifecycle is one-way.
- **sealed-auction / gallery** — commit-reveal: a sealed submission is frozen the instant it
  commits; swapping it afterward is a refusal.
- **nameservice, identity, subscription, governed-namespace, compartment-workflow-mandate,
  storage-gateway-mandate** — registration, credentials with selective disclosure, pub/sub,
  threshold-governed registries, spend-policy workflows, volume-ceiling storage gateways.

A starbridge-app is *mostly data* — factory descriptors + turn templates over the one verified
kernel; the hard rule is "the answer is never `Effect::FooApp`" (no app-specific kernel code,
ever). They run three ways: an **in-browser node** (wasm — simulate, preview, time-travel locally),
the **browser-extension wallet** (`window.dregg` — real identity and signing), and a **live
federation node**. Twenty more are in various stages (escrow-market, execution-lease,
agent-orchestration, swarm-orchestration, polis, tool-access-delegation, supply-chain-provenance…).

**Honest status:** the ten are end-to-end tested in-process, two (voting, bounty) are seeded on
the devnet at genesis and drivable from the CLI today; the rest ride as the federation hardens.

---

## 4. Where $DREGG fits (and doesn't)

$DREGG buys **services, never features**: storage rent, compute jobs, CI assurance, bonds and
stakes for the roles above. It never buys a change to the rules — the rules are theorems. The
cloud sections above are what "services" concretely means: bonded work with slashing, where the
token is the skin in the game, not the product.

---

## 5. Suggested article angles (each one checkable end-to-end)

1. **"The cloud where catching a liar pays"** — the forge's `Staked{ReExecuted}` + `Challenger`
   beneficiary; the optimistic-rollup comparison lands instantly with CT.
2. **"A storage network whose promise is a theorem"** — walk `ClientProtocol.lean`'s three
   guarantees in plain words; the punchline is that the *marketing claim* is machine-checked.
3. **"Apps where cheating doesn't lose — it fails to exist"** — three refusal demos (double vote,
   over-budget bid, swapped auction submission), each a screenshot of the executor saying no.
4. **"GitHub without git"** — repos as cells, merges as pushouts, review as conflict-resolution,
   capabilities instead of admin checkboxes.

*Register rule for all of it: no "will," no "soon," no roadmap-as-fact. What runs, shown running;
what's proven, cited; what's a named seam, named. That honesty is not a limitation on the story —
it IS the story no other project can tell.*
