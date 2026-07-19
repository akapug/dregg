# THE DARK BAZAAR — the most private, most complex, most *unique* use of fhEgg, as a game

*A north-star design doc, 2026-07-18. The premise: use the game layer (`dreggnet-*`, the Descent, Seasons)
as the proving ground for the FULLEST fhEgg — including mechanisms nobody has built anywhere, at any scale,
web2 or web3 — with virtual stakes so the frontier can run rough and harden toward no-TODO while real players
put real load on it. Grades are honest (PROVED / WORKING / PROTOTYPE / FRONTIER-unbuilt), because grading is
the brand even for a dream. Companions: `FHEGG-MATURITY-ROADMAP.md`, `FHEGG-PRODUCT-ORDER-FRONTIER.md`,
`DREGGFI-VISION.md`.*

> **The image.** Figures walking luminous threads across a black field scattered with symbols and torn maps —
> each sees their own thread and the constellation of fixed lights where proofs anchor, and *nothing else*.
> That is the Dark Bazaar exactly: a market where you trace your own flow and verify the stars, but the book
> is dark to you, to every other player, **and to the house.**

---

## 0. The one unsayable sentence

Every game with hidden information asks you to **trust the operator** not to peek. Every private DEX is a
trusted mixer or leaks on-chain. The Dark Bazaar is the thing none of them can say:

> **The dealer cannot see the cards, the players cannot see each other, and every deal carries a proof it
> was fair.**

The house is *cryptographically* blind (FHE — it computes on ciphertext it can never open); the players are
blind to each other (Tier-0 DARK); and every clearing emits a `Cert-F` proof of optimality + conservation +
individual-rationality. No competitor, web2 or web3, can offer a market that is simultaneously **private to
all**, **operator-blind**, and **provably fair**. That trifecta is the flex.

---

## 1. The four halls — each a different maximal power of fhEgg

| hall | the mechanic | fhEgg primitive | grade | existing surface it upgrades |
|---|---|---|---|---|
| **The Sealed Exchange** | blind **combinatorial** bundle auction ("the Dragonslayer set: sword AND shield AND helm, all-or-nothing, ≤500g"), cleared welfare-optimally on encrypted valuations with a proof | private convex/**integer** clearing + verify-not-find (`Cert-F`) | **FRONTIER** (the LP is prototyped; discrete/combinatorial is the research reach — today on fhIR's reject-list) | `dreggnet-market` (sealed-bid, operator-held → cryptographically dark) |
| **The Dark Pool** | a resource AMM `x·y=k` whose **reserves are hidden** — no depth to snipe, but every swap provably priced by the invariant | ct×ct **multiply** (hidden reserves need private multiplication) | **PROTOTYPE** (multiply oracle-anchored `2376160a8`; hidden-reserve AMM is the next stone) | new — the liquid companion to the exchange |
| **The Oracle Pit** | a **confidential prediction market** on the game's own events ("does the boss fall this Season?"), positions hidden so no front-running, priced by a quadratic cost function | private **QP** + Fenchel–Young certificate | **FRONTIER** (the doc's `quadratic/PWL prediction AMM`, `Core` tier — needs the convex engine + quadratic pricing) | new — the speculation layer |
| **The Netting Vault** | guild members accrue **hidden IOUs** all Season; at settlement only the **net** flows are revealed + settled, the gross web staying encrypted | no-viewer **multilateral compression** (the frontier's item 4) + `settleRing` conservation | **FRONTIER** (compression is theorized; the ring settle + no-viewer decrypt are built/prototyped) | `dreggnet-trade` (bilateral → N-way), `dreggnet-guild` |

And wrapping all four: **cryptographic fog-of-war** — hidden inventories and hidden strategic state resolved
on encrypted data. Not "the server hides it" — *mathematically* hidden, from other players AND the house.
`FRONTIER` (general encrypted-state resolution is the deepest reach).

---

## 2. Why each hall is the *maximal* use of a different fhEgg capability

- **The Sealed Exchange** stresses **verify-not-find at its hardest**: a combinatorial allocation is
  NP-hard to *find*, but a valuation-revealing-free certificate *disposes* it. This is the crown jewel of
  market design — governments spend billions on spectrum auctions with trusted auctioneers who see every
  bid. A private, trustless, provably-optimal combinatorial exchange **does not exist anywhere**. Doing it
  first with virtual loot is how you prove it without a spectrum-license-sized mistake.
- **The Dark Pool** is the reason we built ct×ct multiply. `x·y=k` with *private* reserves is a genuine
  product of two secrets — the exact thing the additive fold could not do and the multiplicative frontier
  can. Dark liquidity that is provably honest.
- **The Oracle Pit** shows the **convex engine past `T=1`**: a quadratic cost-function market is an
  iterated convex program, priced privately, unmanipulable because the book is dark.
- **The Netting Vault** shows **no-viewer at social scale**: a whole guild's internal politics stay secret;
  only the *truth of who-owes-whom-net* becomes real. The gross graph is never decrypted by anyone.

---

## 3. The crawl-walk-run (honest sequencing — no faked frontier)

The genius of the game framing (ember's four reasons + a fifth): the FRONTIER halls can ship **rough** and
harden under real load, because a bug costs a virtual helm, not a spectrum license.

1. **CRAWL — The Sealed Exchange, single-unit first** (this Season): mount a distinct Dark Bazaar game over
   `dreggnet-market`'s real LIST → sealed BID → SETTLE executor path on web, Telegram, and Discord. The first
   playable cut is explicitly **operator-visible at settlement**: it commits bids during play, reveals them
   to settle, replays the winner and ledger conservation, and makes no Tier-0/ZK/source-bound claim. Next,
   weld the existing native Cert-F check-level clearing into that same session and receipt. In parallel,
   replace plaintext ingestion with the collective BFV → masked-boundary MPC path only when the exact order
   source → `(p*,V*)` → settlement integrity join is installed. Real players and load start at the honest
   low-resolution cut; the cryptographically dark carrier hardens underneath it without a fake badge.
2. **WALK — The Dark Pool** (multiply → hidden-reserve AMM) and **N-way trade** (`dreggnet-trade` →
   `settleRing`): both lean on prototyped machinery; harden the noise/perf under real swaps. The busy
   in-game AH is the realistic N that finally validates the **GPU-resident** thesis (histogram 11× at scale)
   the microbench couldn't reach.
3. **RUN — The combinatorial Sealed Exchange, the Oracle Pit, the Netting Vault, fog-of-war**: the true
   frontier. Prototype live with virtual stakes, learn from players, drive each toward no-TODO. The
   combinatorial reach means teaching fhIR *admissible discrete choice with a certificate* — a real research
   arc, which is exactly why it is the flex.

---

## 4. The honest ledger (grading is the brand)

- **PROVED/WORKING today:** the plaintext uniform-price rule/allocation/wire settlement; registered ring3 +
  market4 Cert-F integer optimality and a real hiding proof path; the LP convex linear step; ct×ct multiply
  (oracle-anchored); and `settleRing` conservation/atomicity. These are real components, not yet one Tier-0
  product execution.
- **PROTOTYPE (first cuts, named residuals):** local semi-honest no-viewer BFV → masked-boundary MPC; retained
  GPU additive fold; convex engine at `T>1`; and the broader fhIR family. One exact two-coordinate rebalance
  family is now Lean-authoritative end to end (typed plan + admission/no-wrap/noise proofs → canonical emitted
  artifact → strict Rust interpreter); the legacy Rust compiler still owns the other product families. The
  canonical runtime envelope now has a strict Ed25519 threshold-roster verifier and an opt-in certified-market
  co-endorsement weld. This authenticates who endorsed the exact combined claim, but does not prove the
  ciphertext-opening/source relation or malicious MPC correctness.
- **ENGINE INTEGRATION (working seam, not yet the live flagship route):** a settled Bazaar session now exposes
  the exact winning `DreggIdentity` and can cross an existing provenance-carrying `AssetId` for the winning
  `$DREGG` amount through `dreggnet-trade`'s sealed-escrow atomic swap. The end-to-end gate begins with a real
  fair-drawn Descent `LootVault` drop, adopts the exact same `AssetWorld` (no remint), and re-verifies the
  `mint → escrow → winner` lineage. An unfunded winner is refused and the loot returns to its seller. The
  auction-resolve turn and the asset/value cross are still two committed operations rather than one atomic
  multi-cell turn, and the dedicated Descent frontend has not yet passed its durable player world into the
  catalog Bazaar session.
- **FRONTIER (unbuilt, the reach — and the point):** combinatorial/integer clearing with a certificate,
  quadratic prediction pricing, no-viewer multilateral compression, general encrypted-state resolution.

The Dark Bazaar is not a demo of what is done — it is a **live crucible for the frontier**, run at real load
with virtual stakes, every mechanic carrying the grade of what it actually is.

Its player-facing acceptance gate is one offering key and one session protocol consumed by all surfaces:
`bazaar` must list, open, advance, render, and verify through the shared catalog on `arcade.dregg.net`, the
Telegram host, and Discord's generic `/play` adapter. A surface-specific reimplementation is not the game.

---

## 5. The private-game organ is larger than the market

The reusable primitive is not “an auction.” It is:

> evaluate a proved rule over hidden player state, reveal only the permitted outcome, and bind that outcome
> to the cells/receipts that enact it.

That organ belongs throughout the game engine:

- **guild and party governance:** private approval/ranked ballots, revealing only winner/quorum;
- **matchmaking and raid formation:** private rating, role, latency, blocklist, and preference inputs;
  reveal only the selected roster/partition, with a proof that the published compatibility and role rules held;
- **loot and encounter resolution:** sealed need/greed or DKP comparisons, private loot councils, and
  no-duplicate shuffled deals;
- **quests and shared-world predicates:** prove that a party satisfies a hidden inventory/reputation/history
  predicate without revealing which member or item witnesses it;
- **inter-party coordination:** private bargaining, coalition selection, and season-end netting that reveal
  only accepted terms or final net obligations.

Existing `dreggnet-party`, `collective-choice`, `starbridge-privacy-voting`, guild/tavern surfaces, asset
custody, cell predicates, and receipts are composition material—not automatically privacy-grade rule cores.
Where their semantics and leakage match, reuse them. Where an older crate is Rust-authored, operator-private,
or models the wrong rule, keep its identity/cell/surface organ and replace the decision relation with a fresh
Lean-authored descriptor. The first reusable instance is now built: fixed `N=4,K=4` private score aggregation,
scores in `0..3`, with only `(session, rule, ballot_root8, lowest-index aggregate winner)` public. It is
Lean-authored and byte-emitted; Rust supplies strict witness filling, `HidingFriPcs`, and a small
`VerifiedDecision` application seam. The emitted relation is now closed from actual `Satisfied2` descriptor
acceptance to semantic `Accepts`: exact score/total decoding, faithful packing, lowest-index argmax,
public-input identity, and all eight Poseidon output lanes are in the theorem. As with the private Bazaar
family, the hiding PCS shields inputs from proof consumers; a threshold FHE/MPC or distributed-prover producer
is still required before the house itself is blind.

The current reuse boundary is concrete:

- `dreggnet-party`, guild governance, council, and `starbridge-privacy-voting` already provide useful
  eligibility, custody signatures, single-use ballots, quorum, capabilities, and committed enactment. Their
  existing ballot/tally paths are public, however; the privacy-voting crate explicitly disclaims mixnet-style
  ballot secrecy. Reuse the electorate and enactment organs, not the leakage semantics.
- `dreggnet-game-board` already proves that a played card belonged to a hidden committed hand and was not
  replayed. The new fixed-N=8 private shuffle organ now supplies the missing exact-permutation half: eight
  independently blinded, per-seat leaves under a faithful root8, a Lean proof of no duplicates/no omissions,
  and depth-three selective openings. It still does not prove that the chosen permutation was unbiased or
  coordinator-independent; compose it with joint entropy or a threshold mix before claiming fairness.
- the custom-effect turn path already welds a sub-proof's public inputs to the exact pre/post cell roots, and
  its app-root binding can connect a published winner/root to the committed field that enacts it. The strongest
  retained recursion-fold path currently consumes the older circuit-DSL `CellProgram`, not an arbitrary
  Lean-emitted IR2 descriptor. A generic Lean-descriptor→custom-VK retained-witness adapter is therefore a real
  substrate weld, not something an app should paper over with a host-side `if proof.verify()`.

---

## 6. The pitch, one breath

**The Dark Bazaar: a game economy where the market is combinatorial, the book is cryptographically dark, the
house is blind, and every clearing carries a proof it was fair — the hardest, most-private market mechanisms
humans have designed, run trustlessly, stress-tested by real players for the price of pixels.** The dungeon
already has the Descent and its Seasons; this is the economy *inside the dark* — the threads of light across
the black field, each player tracing their own, verifying the stars, seeing no one else's hand.
