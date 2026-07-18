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

1. **CRAWL — The Sealed Exchange, single-unit first** (this Season): rewire `dreggnet-market`'s sealed-bid
   clearing to call fhEgg **Tier-0 uniform-price** (built + certified today) — bids FHE-encrypted, cleared
   dark, `Cert-F` receipt on the winner/price. This is the maturity-roadmap pillar #5 *deployed*, and it is
   buildable NOW. Real players, real load, zero fund risk.
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

- **PROVED/WORKING today:** Tier-0 uniform-price clearing + `Cert-F` (ring-3 → market4), the LP convex
  linear step, ct×ct multiply (oracle-anchored), the no-viewer keystone with a **proven smudging bound**,
  `settleRing` conservation/atomicity, non-inflatable reserves (`stripe_reserve_solvent_forever`).
- **PROTOTYPE (first cuts, named residuals):** the convex engine at `T>1`, the GPU-resident pipeline, fhIR.
- **FRONTIER (unbuilt, the reach — and the point):** combinatorial/integer clearing with a certificate,
  quadratic prediction pricing, no-viewer multilateral compression, general encrypted-state resolution.

The Dark Bazaar is not a demo of what is done — it is a **live crucible for the frontier**, run at real load
with virtual stakes, every mechanic carrying the grade of what it actually is.

---

## 5. The pitch, one breath

**The Dark Bazaar: a game economy where the market is combinatorial, the book is cryptographically dark, the
house is blind, and every clearing carries a proof it was fair — the hardest, most-private market mechanisms
humans have designed, run trustlessly, stress-tested by real players for the price of pixels.** The dungeon
already has the Descent and its Seasons; this is the economy *inside the dark* — the threads of light across
the black field, each player tracing their own, verifying the stars, seeing no one else's hand.
