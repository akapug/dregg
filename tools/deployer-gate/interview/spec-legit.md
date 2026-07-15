# Project spec (candidate A) — "Meridian Grid"

**One-liner.** An open-source metering + settlement layer for community solar
microgrids. Members contribute rooftop generation; the grid settles who owed
whom each month. The token is the settlement unit *inside* one grid's books.

**What exists today (verifiable).**
- Public monorepo (Apache-2.0), 3 years of commits, 6 named contributors on the
  CONTRIBUTORS file, CI green.
- A running testnet settling 4 pilot microgrids in Vermont (14, 9, 22, and 6
  households) since 8 months ago; monthly settlement reports are public.
- A hardware bill of materials and the open metering firmware (ESP32) that the
  pilots run.

**Team / accountability.**
- Two named co-founders (LinkedIn + prior grid-software employment), plus the
  contributor list. Willing to post a **50 ETH conduct bond**, slashable by the
  launchpad fraud-proof if the disclosed supply schedule is violated.
- Third-party audit of the settlement contract completed by a named firm;
  report hash published.

**Tokenomics (disclosed, closes).**
- Total supply 10,000,000, hard-capped, minted once. No further mint function.
- Sale 60%, team 15% (vesting-locked 24 months, cliff at 12), ecosystem/pool
  reserve 25% (disclosed, seeds the graduated liquidity pool).
- The token is the unit of account for intra-grid kWh settlement; it is *used*
  by the metering firmware, not bolted on. Members can redeem for the grid's
  fiat settlement account at the published monthly clearing rate.

**Use of funds (itemized).**
- 40% hardware subsidies for the next 6 pilot grids (BOM * quantity published).
- 30% two engineering salaries, 12 months, named roles.
- 20% the completed audit + a second audit pre-mainnet.
- 10% legal (utility-regulation counsel in the pilot states).

**Under-pressure answers.**
- "Who can drain the pool?" → Nobody; the pool floor is contract-enforced, and
  the team allocation is vesting-locked; here is the schedule.
- "Why does this need a token?" → It doesn't strictly need a *public-market*
  token; it needs an intra-grid unit. The public launch funds hardware; the
  redemption peg is the honest answer to 'why would anyone hold it'.
- "What if the pilots fail?" → Then the bond is slashable and the vesting means
  we can't dump; funds are itemized to hardware that has resale value.
