# USER-FACING-STACK-REALITY — the honest state of what a person actually touches

*Read-only scout (2026-07-14, revised against HEAD 2026-07-16). The
contracts/engine/soundness stack is deeply covered elsewhere; this maps the surface a REAL
user touches — the frontends, the wallet path, the browser extension, and the
dregg-interaction/RPC layer — and grades each layer REAL / DEMO / MISSING against the goal
in `docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`: a Robinhood-Chain user
connects a wallet, signs a sealed bid, submits it to a public RPC, dregg clears privately,
it settles on-chain, they see their allocation. Every claim is cited to the file it reads
from.*

**One-line summary.** The *crypto core is real* (the wasm cipherclerk signs, proves, and
verifies for real, in a real browser), and the *engine is real* (the matcher + fhEgg solver
clear for real). But the *product surface a real user would touch is a set of local dev
servers on the tailnet*, split across two disjoint wallets, driving no deployed public
contract and no hosted public RPC. The "public RPC signed-data" pipeline the architecture
doc argues from is **designed, not built**. Nothing targets Robinhood Chain (46630) from the
frontend today.

---

## 0. The layers at a glance

| Layer | Grade | One-liner |
|---|---|---|
| **Frontend infra** | DEMO (real engine behind it) | `drex-web` + `launchpad-web` + `offerings` are **local dev `node http` servers**, tailnet/LAN-only; they drive the REAL matcher / REAL contract, but there is **no production/hosted frontend** and no deployed contract. |
| **Wallet** | SPLIT: EVM real-but-unwired / dregg-native demo-keyed | Two different wallets. `launchpad-web` has a REAL `window.ethereum` (ethers) EVM path; `drex-web` uses the cipherclerk wasm with **demo deterministic keys**. Neither targets Robinhood Chain. The signed-order-to-public-RPC flow is **absent**. |
| **Extension** | REAL, both faces | A competent MV3 cipherclerk (named Ed25519 identities, authorization-first signing, ZK disclosure, receipt stream) **plus** an EVM signing leg (secp256k1 from the same sealed seed) and an fhEgg sealed-bid/DrEX page API. Remaining gap: the DrEX web surface **doesn't route through it** — `drex-web` loads the wasm standalone. |
| **Dregg-interaction / RPC** | REAL but LOCAL/solo | The node `/api/*` surface + `serve.mjs` `/clear` `/clear-shielded` `/prove-shielded` `/settle` are real against a **solo committee-of-one** node. **No `/bid`/`/reveal` RPC, no on-chain settle, no hosted endpoint.** |

---

## 1. Frontend infrastructure

### 1.1 `drex-web/` — the clickable DrEX (DEMO surface, REAL engine behind it)

`drex-web/serve.mjs` is a hand-rolled `node http` server (`serve.mjs:450`), **not** a
production frontend: no bundler, raw ESM served from disk, single process. `app.js` imports
its own wasm loader `drex-wallet.mjs` and a **baked demo book fixture** `demoBook` from
`drex-clearside.js` (`app.js:13-14`). It is REAL in exactly the way the README claims: the
`/clear` endpoint shells to the real `drex_clear` binary (`solver.rs` TTC ring match +
`verified_settle.rs` folded through the Lean `recKExecAsset` kernel), and `/settle` lands one
real turn on a live solo node. But the *product framing* is a demo: fixed demo orders, demo
trader keys, single-node, **no on-chain settle** (README `drex-web/README.md:40-51`).

- Endpoints (`serve.mjs`): `POST /clear` (real matcher, `:455`), `POST /clear-shielded`
  (real fhEgg solver, `:467`), `POST /prove-shielded` (real Cert-F STARK, seconds, `:484`),
  `GET /node/status` (`:538`), `POST /settle` (one real turn on the solo node, `:549`),
  `/wasm/` mount of the extension's wasm (`:568`).
- **No `/bid`, no `/reveal`.** The architecture doc's "signed sealed bid → `POST /bid` → RPC
  forwards the on-chain `commitBid`" flow (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`
  §2.2) has **no endpoint here**. It is designed, not built.
- **Live but private.** Per `DEVNET-DEPLOYMENT-REALITY.md` §1, `drex-web` is up on
  `:8781` but reachable on **LAN + tailnet only** behind hbox's firewall; nothing is on the
  public internet. (Note: the deploy comment flags it as bound to `0.0.0.0:8781` "wrongly" —
  `deploy/games/dregg-web-games.service` header — a hardening item, left untouched here.)

Siblings on their own ports (kept separate so they never clobber the live lane):
- `offerings.mjs` (`:8790`) — the "DreggFi Offerings" menu; runs the real `fhegg-solver`
  bins (`pricecert_clear`, `package_clear`, `fhegg_clear`). Its own header states it plainly:
  **"this is a devnet-DEMO surface … Actual PUBLIC devnet deployment … is the ember-gated
  step, not performed here"** (`offerings.mjs:22-26`).
- `drex-viz.{html,js}` — a visualization surface over fixture data (`drex-viz-data.js`).

### 1.2 `launchpad-web/` — the pump.fun-shaped product layer (DEMO deployment, REAL wiring)

This is the more product-shaped surface and the more real *wallet* story. `server.mjs`
serves a static product frontend (`public/`: discovery `index.html`, `create.html`,
`launch.html`, `token.html`, `receipt.html`) and vendors ethers so the browser drives the
**real** `DreggLaunchpad` contract with the user's own wallet (`server.mjs:9-11`). The
backend is a genuine ethers event-indexer → authoritative store → REST API
(`indexer.mjs`), with a node-driven alternative that reads launches as a real turn stream
off a live dregg node (`node-indexer.mjs`).

What makes it DEMO today, not production:
- **No deployed contract.** `LAUNCHPAD_ADDRESS` defaults to empty (`server.mjs:44`); with
  neither `DREGG_NODE` nor an address the API 503s (`server.mjs:129`). The gate deploys to a
  **local anvil, chainId 31337** (`public/receipt.html:42`), and the committed receipt keys
  are anvil's well-known public dev accounts (`gate/receipt.mjs:24-28`). There is no
  Base-Sepolia or Robinhood-Chain deployment — those are named only in comments/README
  (`server.mjs:4`, `README.md:79`).
- **Not live.** The only hosted public web surface serving traffic is the **games demo**
  (`deploy/games/dregg-web-games.service`, `dreggnet-web-server` over tailnet → Caddy
  gateway). The launchpad's deploy lane EXISTS in `deploy/launchpad/` —
  `dregg-launchpad-web.service` (a user unit binding `launchpad-web` to the hbox tailnet
  IP `:8785` behind the AWS gateway's Caddy, the games pattern), `deploy-launchpad.sh`
  (install/health-gate/rollback), `caddy/Caddyfile.launchpad`, `RUNBOOK.md`; `server.mjs`
  itself points at the unit (`server.mjs:41`). Go-live (DNS, env file, funded contract
  broadcast, gateway Caddy block) is ember-gated prep, so no launchpad URL serves the
  public. `drex-web` has no deploy lane at all — local `node server.mjs` only.

**Is there a production frontend? No.** Every user-facing web surface is a local dev server;
the surfaces wired to hosting/systemd are the standalone games demo (live) and the
launchpad (unit + runbook in place, not live). `DEVNET-DEPLOYMENT-
REALITY.md`'s own one-liner: *"the ENGINE is real and a solo node is genuinely LIVE; the
DEVNET is not … Nothing is on the public internet."*

---

## 2. Wallet integration

The two web surfaces carry **two separate wallets**. The unified thing the fhEgg user flow
needs — one identity holding both the EVM escrow key and the dregg-native signing/proving
faces — exists in the **extension** (§3), but neither web surface routes through it.

### 2.1 `launchpad-web` — a REAL EVM wallet path (but unwired to any real chain)

`public/js/app.js` is a genuine EVM connect/sign/submit path: if `window.ethereum` is
present (MetaMask / an injected EVM wallet) it builds an `ethers.BrowserProvider` and calls
`eth_requestAccounts` (`app.js:35-38`); off-injection on local anvil it falls back to an
anvil dev key (`app.js:41-45`), then builds the contract with the signer (`app.js:48`). This
is REAL wallet integration — but it drives only a local/undeployed contract, and there is
**no chainId-46630 (Robinhood) configuration anywhere in a frontend wallet path** (grep of
`drex-web/ launchpad-web/ extension/` for `46630`/`Robinhood` hits README/comment strings
plus one test fixture — `extension/test/launchpad.test.mjs:55` sets `CHAIN_ID = 46630`
against a placeholder address with no RPC and no deployed contract — never a wallet
config path). So: real EVM plumbing, aspirational target.

### 2.2 `drex-web` — the cipherclerk wasm wallet (dregg-native, DEMO-keyed)

`drex-wallet.mjs` loads the **same 50MB wasm the extension ships** and calls the real entry
points: `cipherclerk_make_action_turn` (Ed25519-signed dregg Turn), `assemble_signed_turn_
envelope` (hybrid ed25519 + ML-DSA-65), `prove_conservation`/`verify_conservation_proof`
(Bulletproofs solvency), `prove_anonymous_membership` (blinded ring membership). This
proving is REAL and runs in a real headless browser (README browser-check). **But**: this is
**not an EVM wallet** (no secp256k1, no `window.ethereum`), and it signs with **demo
deterministic keys** — `traderKey(seedByte)` synthesizes a key from a seed byte
(`drex-wallet.mjs:65-67`), explicitly "demo key material — a real wallet holds this in the
extension's sealed store." A real user's held key never enters this path today.

### 2.3 The Robinhood-Chain / public-RPC-signed-data flow — ASPIRATIONAL

The architecture doc's user surface is "two stable things: the launchpad contract + a stable
signed-data RPC" (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §2). In code:
- The **contract side** exists but is **undeployed** (§1.2 above).
- The **signed-data RPC side does not exist**: no `/bid`/`/reveal` endpoint forwards a
  signed order to `commitBid`; `serve.mjs` only exposes the dregg-native clear/settle
  endpoints. `chainId 46630` appears only in **backend** light-client / settlement crates
  (`eth-lightclient/tests/robinhood_holding.rs`, `cosmos-settlement/src/vk.rs`,
  `dregg-interchain-gov/tests/robinhood_inbound.rs`) — the *proving-a-holding / settling*
  side, never a user wallet path.

**What a real user needs:** one wallet that both (a) holds an EVM key to escrow on-chain
(`commitBid`) **and** (b) produces the dregg-native sealed-order signature +
solvency/eligibility proofs, plus a hosted RPC that carries (b) to dregg and binds it to (a).
The installed extension now holds (a) and (b) under one sealed seed (§3.1) — but the two web
surfaces do not use it (`launchpad-web` drives its own EVM path, `drex-web` loads the wasm
standalone), and the hosted RPC that would bind them does not exist.

---

## 3. `./extension` — the Dragon's Egg Cipherclerk

### 3.1 What it REALLY is (dregg-native, and genuinely good at that)

An MV3 extension (Chrome + Firefox) that is a citizen's cipherclerk for **dregg turns**:
- Named Ed25519 identity profiles; key derivation pinned to a golden vector across SDK/CLI
  (`README.md`, `src/background.ts` ~5800 lines).
- **Authorization-first** `signTurnV3` — never signs blind; renders a faithful reading of
  every action/effect (`src/explain.ts`), nonce-bound confirm popup, federation-domain
  binding (`src/federation-domain.ts`).
- Receipt SSE stream, capability tokens evaluated by a WASM datalog engine, ZK **selective
  disclosure** (Bulletproofs range proofs over Ristretto), stealth addresses, committed
  private transfers.
- Ships the identical `dregg_wasm.js` + `dregg_wasm_bg.wasm` crypto core that `drex-web`
  loads (`web_accessible_resources` in `manifest.json`).

### 3.2 The fhEgg legs it carries (code-verified)

- **An EVM signing leg.** `extension/src/evm.ts`; `background.ts` imports
  `personalSign`/`personalSignDigest`/`signTypedData` (`background.ts:19-22`). The page API
  is `window.dregg.evm.{getAddress, personalSign, signTypedData}` — EIP-191 and EIP-712
  signatures an on-chain launchpad escrow recovers, with the secp256k1 key derived from the
  same sealed wallet seed as the Ed25519 identity (`extension/README.md`). One recovery
  phrase restores both faces, so the EVM-escrow / dregg-native identity *binding* is
  intrinsic, not bolted on.
- **A DrEX / sealed-bid surface.** `extension/src/sealedbid.ts` + `launchpad.ts`;
  `background.ts` registers and handles the `dregg:sealedBidCommit`, `dregg:sealedBidReveal`,
  and `dregg:drexPlaceOrder` page-API messages (`background.ts:3466,4836,4879,5169`) — the
  fhEgg commit → reveal ceremony is in the installed extension.
- **Shielded STARK membership, enabled and sound.** The wasm crate proves Merkle-membership
  over the **real arity-4 Poseidon2 Merkle descriptor**
  (`merkle-membership::poseidon2-4ary-general-depthN`, via `prove_vm_descriptor2` / the
  deployed `verify_vm_descriptor2` — `wasm/src/lib.rs:265-282`); the toy linear
  `MerkleStarkAir` it replaces is retired. A genuine member proof verifies; a forged claim is
  rejected (`extension/README.md`).
- **Product-domain endpoint.** `host_permissions` points at `https://node.dregg.net/*` +
  `wss://node.dregg.net/*` (`manifest.json:18-21`), with localhost as optional permissions.
  `fg-goose.online` residue survives only as the Firefox add-on id
  (`manifest-firefox.json:75`) and in prose.

### 3.3 What still keeps the extension off the fhEgg path

**The DrEX flow bypasses the installed extension.** `drex-web/app.js` loads the wasm
standalone via `drex-wallet.mjs` (`app.js:13`), not via `window.dregg` — so the sealed-bid
ceremony and the EVM leg a user actually installs are not the surfaces the DrEX demo
exercises. Routing `drex-web` (and the launchpad flow) through the installed extension is the
remaining wiring, not a missing capability. And the ceremony has only been driven against
local/demo targets — the same no-deployed-contract / no-hosted-RPC gaps as every other layer
(§1, §4).

---

## 4. Dregg-interaction / RPC layer

- **The node HTTP surface (REAL, solo).** The extension speaks the gateway `/api/*` prefix:
  `/api/node/status`, `/api/cell/{id}`, `/api/turns/submit-signed`, `/api/events/stream`
  (SSE), `/api/receipts/{hash}/witnesses`, `/api/faucet`, `/api/turns/bearer-auth`,
  `/api/turns/peer-exchange` (extension README "Architecture"). These are real against a
  **committee-of-one** solo node (`DEVNET-DEPLOYMENT-REALITY.md` §1:
  `federation_mode:"solo"`, `peer_count:0`, but `full_turn_proving:true`, `state_producer:
  "lean"` — the proved effect-VM, not a mock).
- **The `serve.mjs` "RPC" (REAL, local).** `/clear` (real matcher), `/clear-shielded` (real
  fhEgg solver), `/prove-shielded` (real Cert-F STARK), `/settle` (`/cipherclerk/unlock` →
  `/turn/submit` → effect-VM → prove_pool, one real turn on the solo node). This is the
  strongest real integration — but LOCAL, solo, and dregg-native.
- **The in-browser prover (REAL, the crown jewel).** The wasm bindings prove/verify for real
  in a real browser (README browser-check). This is the most production-real piece of the
  whole user-facing stack.
- **Missing for a real user flow:** no hosted/public RPC (tailnet-only); **no on-chain
  settle** from a cleared batch; no `/bid`→`commitBid` forwarding; the shielded
  `finalizeClearing` where the attestor is the *sole* source of the result is DESIGNED-NOT-
  BUILT (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §5); and the concrete
  `IClearingAttestor` (the one seam dregg's verdict crosses onto the chain) is **interface +
  mock only** — no v1 committee attestor, no v2 proof attestor written (arch doc §3.3).
  Node-side, the `prove_pool` STARK does not yet attach for the SetField settlement shape
  (named node follow-up, `drex-web/README.md:44-49`).

---

## 5. The gap to a real Robinhood-Chain user clicking through an fhEgg launch

Step by step, for: *connect wallet → sign a sealed bid → submit to the public RPC → dregg
clears privately → settle on-chain → see allocation.*

| Step | Grade | Reality |
|---|---|---|
| 1. Connect wallet | **DEMO** | `launchpad-web` has a real `window.ethereum` connect (`app.js:35-48`), but only to local/undeployed anvil; `drex-web` uses **demo keys** (`drex-wallet.mjs:65`). No Robinhood-Chain (46630) config in any frontend. |
| 2. Sign a sealed bid | **CAPABLE / unwired as one flow** | Dregg-native sealed commit + Bulletproof solvency proof = **REAL** (wasm); the installed extension carries both the sealed-bid ceremony and the EVM escrow signature under one seed (§3.2). But the DrEX surface is demo-keyed and bypasses it, and the on-chain sealed `commitBid` escrow = **real contract, undeployed**. No shipped flow exercises both together. |
| 3. Submit to a public RPC | **MISSING** | No hosted RPC; `serve.mjs` is tailnet-solo; no `/bid`/`/reveal` endpoint. The architecture doc's signed-data RPC is **designed, not built**. |
| 4. dregg clears privately | **REAL (local/solo)** | `/clear-shielded` (fhEgg solver) + `/prove-shielded` (Cert-F STARK) are real, but solo/local; the shielded launchpad-effect binding is a named weld. |
| 5. Settle on-chain | **MISSING** | `drex-web` `/settle` lands a dregg-native turn on the solo node (real), but there is **no on-chain settle** and **no concrete `IClearingAttestor`** (interface + mock only). `DreggLaunchpad.settleBid` exists but nothing drives it from a cleared shielded batch. |
| 6. See allocation | **REAL (local/demo data)** | Fill panel + graded fairness ledger (`drex-web`) and the token page from on-chain logs (`launchpad-web`) are real, but tied to local/demo runs. |

### The single biggest gap

**There is no hosted, public, signed-data RPC that unifies EVM on-chain escrow custody with
dregg-native private clearing into ONE user action against a deployed contract + a real
public node.** Everything is a local dev server on the tailnet; the two wallet halves (EVM
escrow / dregg-native sealed order) live together only in the installed extension, which no
web surface routes through; no launchpad contract is deployed to any testnet, let alone
Robinhood Chain (46630); and the `IClearingAttestor` that would carry dregg's verdict
on-chain is interface + mock only. The whole "signed sealed bid → `commitBid`
→ private clear → attested settle" pipeline is argued on paper (`PRIVATE-DREGG-PUBLIC-
LAUNCHPAD-ARCHITECTURE.md`) but its two load-bearing pieces — the `/bid`+`/reveal` public RPC
and the concrete attestor contract — are unbuilt.

---

## 6. Highest-value next moves (Open-first, per the fhEgg codex)

The codex's own advice is monotone: `Tier0 DARK ⇒ Tier1 SHIELDED ⇒ Tier2 OPEN`, and the
shortest path to *a real user clicking through end-to-end* is the OPEN / rung-1 path — which
the architecture doc says is **deployable now** and for which **dregg is not even in the
loop** (`finalizeClearing` is permissionless on-chain, arch doc §2.3).

1. **Ship one faithful OPEN (Tier-2 / rung-1) launch a real user can click through.**
   Deploy `DreggLaunchpad` to a real public testnet (Base-Sepolia is the cheapest real EVM
   chain; Robinhood 46630 if that is the target), **go live on the prepared
   `deploy/launchpad/` lane** (unit + deploy script + runbook exist, §1.2; the frontend
   already has the real `window.ethereum` wallet path + real contract driver + real indexer),
   and run rung-1 REPLAYABLE: register → on-chain `commitBid` → `revealBid` → permissionless
   on-chain `finalizeClearing` → `settleBid`. This needs **no RPC, no attestor, no private
   dregg** — it is the fastest honest end-to-end a stranger can complete, and it exercises the
   real wallet + real contract + real fairness math.

2. **Build the public signed-data RPC** — the missing `/bid` + `/reveal` endpoints that
   forward a cipherclerk-signed order to the on-chain `commitBid` and carry the reveal to
   dregg. This is the seam the whole shielded story rests on and it is currently absent.

3. **Write the concrete v1 committee `IClearingAttestor`** (a small contract, arch doc §3.4)
   — unblocks the shielded settle-on-chain path with an honest, fraud-provable, trust-
   *minimized* posture, without waiting for the v2 clearing-proof pipeline.

4. **Route the surfaces through the installed extension.** The wallet identity IS unified
   there — the EVM leg and the sealed-bid ceremony live under one sealed seed (§3.2). What
   blocks the shielded fhEgg user flow now is wiring: `drex-web` should drive `window.dregg`
   (sealed-bid + EVM) rather than loading the wasm standalone, and `launchpad-web` should
   accept the extension's EVM signer alongside injected `window.ethereum` — so the surface a
   user installs is the surface the flow actually uses.

5. **Sweep the `fg-goose.online` residue** — the Firefox add-on id
   (`manifest-firefox.json:75`) and README/reviewer prose still carry the dead domain; the
   Chrome manifest already targets `node.dregg.net`.

---

## Sources (read-only, this session)

- `docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` — the intended user surface
  (§2 public RPC, §3 attestor, §5 residuals).
- `docs/deos/DEVNET-DEPLOYMENT-REALITY.md` — the honest infra grade (solo node live; devnet
  not; nothing public).
- `docs/deos/FHEGG-CODEX-ROUND4-BRIEF.md` — the three privacy tiers + Open-first monotonicity.
- `drex-web/serve.mjs` (`:450` server, `:455`/`:467`/`:484`/`:538`/`:549`/`:568` endpoints),
  `drex-web/drex-wallet.mjs` (`:65` demo key, `:74`/`:108` sign/prove), `drex-web/app.js`
  (`:13-14` demo book), `drex-web/offerings.mjs` (`:22-26` demo-scope), `drex-web/README.md`.
- `launchpad-web/server.mjs` (`:9-11` EVM wallet reuse, `:44` empty address default, `:129`
  503 guard), `launchpad-web/public/js/app.js` (`:35-48` real EVM connect),
  `launchpad-web/public/receipt.html:42` (anvil 31337), `launchpad-web/README.md`.
- `extension/manifest.json:18-21` (`node.dregg.net` host permissions), `extension/README.md`,
  `extension/src/{evm,sealedbid,launchpad}.ts`, `extension/src/background.ts`
  (`:19-22` EVM imports; `:3466,4836,4879,5169` sealed-bid/DrEX page API),
  `wasm/src/lib.rs:265-282` (Poseidon2 Merkle-membership path),
  `extension/manifest-firefox.json:75` (`fg-goose.online` id residue).
- `deploy/games/dregg-web-games.service` — the hosted web surface that is live (games demo,
  not DrEX); `deploy/launchpad/{dregg-launchpad-web.service,deploy-launchpad.sh,
  caddy/Caddyfile.launchpad,RUNBOOK.md}` — the launchpad's deploy lane (not live).
- Backend Robinhood-46630 refs (settlement/light-client side, not a user wallet path):
  `eth-lightclient/tests/robinhood_holding.rs`, `cosmos-settlement/src/vk.rs`,
  `dregg-interchain-gov/tests/robinhood_inbound.rs`.
</content>
</invoke>
