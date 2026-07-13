# launchpad-web — the dregg launchpad product layer

The product first-layer over the fair-launch engine in
`chain/contracts/launchpad/` (sealed-bid → uniform-price → disclosed-supply →
settle, on-chain-enforced). Toward pump.fun/four.meme feature-parity, but around
dregg's **differentiated fair-launch engine — no bonding curve**.

Every number the pages show is checkable on-chain; the frontend/backend only read
and drive the real `DreggLaunchpad` contract — there is no mirror of the mechanism.

## What it does

- **Create** (`/create.html`) — register a launch with a DISCLOSED supply/vesting
  schedule. The card proves no hidden supply: the schedule must close (sale +
  creator = total, else the contract reverts) and the token mints exactly once for
  the whole cap. After register, the raw schedule is submitted to the backend,
  which VERIFIES it against the on-chain `scheduleCommit` via `checkSchedule`.
- **Bid** (`/launch.html?id=N`) — the sealed commit → reveal → uniform-price clear
  flow, driven by the real wallet (injected `window.ethereum`, or an anvil dev
  signer for the local demo). A "why it's fair" panel grades every claim
  (PROVED Lean theorem / BUILT on-chain / REPLAYABLE recomputed) with `file:line`
  citations into `SealedAuction.lean` / `Market/Optimality.lean`.
- **Token page** (`/token.html?id=N`) — the honest pump.fun token page: disclosed
  supply/vesting (checkable vs the commitment), the one uniform clearing price
  everyone paid, the holder distribution (from Transfer logs), a chart placeholder.
- **Backend** (`server.mjs` + `indexer.mjs`) — an ethers event-listener over the
  contract (registered / committed / revealed / cleared / settled / transfer) →
  an authoritative store → a REST API:
  - `GET  /api/launches` — all launches, replayable-ranked (discovery)
  - `GET  /api/launches/:id` — disclosure + clearing + bids + holders
  - `POST /api/launches/:id/disclose` — submit + verify the disclosed schedule
  - `GET  /api/config` — { rpc, address, abi } the browser wires up
- **Discovery** (`/`) — launches ranked by a REPLAYABLE pure function over public
  on-chain fields only (fill, participation, cleared, disclosed, recency,
  attested). No boost/promote input anywhere — the OCIP anti-pay-to-rank spine.
  Composing the attested screener (wallet-cluster + Benford) is named-not-built.

## Reference material (studied, not lifted)

- **fiv3fingers/Token-Launchpad-Backend** (Solana/Node, `~/src/Token-Launchpad-Backend`,
  ISC) — the event-listener → DB → REST + socket shape (`AgentsLandListener.ts`
  `addEventListener`, `models/Coin.ts`, `routes/coin.ts` list/detail/king). We took
  the backend product shape and reshaped it onto the EVM fair-launch engine with a
  REPLAYABLE (not paid) ranking.
- **GurkanBozok/Meme-Launchpad-Platform** (EVM four.meme-style, `~/src/Meme-Launchpad-Platform`,
  commercial README) — the token-page shape (live clearing, holder distribution,
  trending bar, chart, wallet integration). We took the page layout; we did **not**
  take the bonding curve (ours is a sealed-bid uniform-price raise).

## Run it

```bash
cd launchpad-web && npm install

# Point at a deployed DreggLaunchpad (local anvil / Base-Sepolia / Robinhood Chain)
LAUNCHPAD_RPC=http://127.0.0.1:8545 LAUNCHPAD_ADDRESS=0x… node server.mjs
#   → http://localhost:8785   (discovery / · create · token page)
```

## Gate

```bash
bash gate/run-gate.sh
```

Spins a local anvil, deploys the real `DreggLaunchpad` (forge), starts the
backend, and runs `gate/e2e.mjs` — a full fair launch against the DEPLOYED
contract (register → sealed commit → reveal → uniform-price clear → settle) plus
adversarial checks (hidden-supply reverts, no-peek, no late-switch, no-drop
permutation, dev-lock) and REST-reflection checks. **21/21 pass.** No faked
launch — every number is the contract's.

## Honest scope — this is the FIRST product layer

Built: create / bid / token-page / backend / replayable discovery, driving the
real engine. Named-not-built: graduation to a liquid market (the `x·y=k` pricing
curve above the solvency floor), the social/comments layer, mobile, the conduct-
bond slashing UI, shielded participation, the attested-screener discovery, and a
concrete `IClearingAttestor` (rung-2 real Groth16 clearing proof — the named
weld; launches run rung-1 REPLAYABLE today).
