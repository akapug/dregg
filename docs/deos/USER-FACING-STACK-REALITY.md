# USER-FACING-STACK-REALITY — the honest state of what a person actually touches

*Read-only scout, 2026-07-14, HEAD `e97a2953a`. The contracts/engine/soundness stack
is deeply covered elsewhere; this maps the surface a REAL user touches — the frontends,
the wallet path, the browser extension, and the dregg-interaction/RPC layer — and grades
each layer REAL / DEMO / MISSING against the goal in
`docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`: a Robinhood-Chain user connects
a wallet, signs a sealed bid, submits it to a public RPC, dregg clears privately, it settles
on-chain, they see their allocation. Every claim is cited to the file read this session. No
code or service was changed; the live drex-web / node / games services were not disturbed.*

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
| **Extension** | REAL dregg-native clerk / MISSING for fhEgg | A competent MV3 cipherclerk (named Ed25519 identities, authorization-first signing, ZK disclosure, receipt stream). Has **zero EVM signing**, no sealed-bid/DrEX surface, and the DrEX flow **doesn't even use it**. Needs upgrading. |
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
- **No deployed contract.** `LAUNCHPAD_ADDRESS` defaults to empty (`server.mjs:38`); with
  neither `DREGG_NODE` nor an address the API 503s (`server.mjs:123`). The gate deploys to a
  **local anvil, chainId 31337** (`public/receipt.html:42`), and the committed receipt keys
  are anvil's well-known public dev accounts (`gate/receipt.mjs:24-28`). There is no
  Base-Sepolia or Robinhood-Chain deployment — those are named only in comments/README
  (`server.mjs:4`, `README.md:79`).
- **No hosting.** Like `drex-web`, it is a local `node server.mjs`; the only hosted public
  web surface in `deploy/` is the **games demo** (`deploy/games/dregg-web-games.service`,
  `dreggnet-web-server` over tailnet → Caddy gateway) — not DrEX and not the launchpad.

**Is there a production frontend? No.** Every user-facing web surface is a local dev server;
the only thing wired to hosting/systemd is the standalone games demo. `DEVNET-DEPLOYMENT-
REALITY.md`'s own one-liner: *"the ENGINE is real and a solo node is genuinely LIVE; the
DEVNET is not … Nothing is on the public internet."*

---

## 2. Wallet integration

There are **two separate wallets**, and neither is the unified thing the fhEgg user flow
needs.

### 2.1 `launchpad-web` — a REAL EVM wallet path (but unwired to any real chain)

`public/js/app.js` is a genuine EVM connect/sign/submit path: if `window.ethereum` is
present (MetaMask / an injected EVM wallet) it builds an `ethers.BrowserProvider` and calls
`eth_requestAccounts` (`app.js:35-38`); off-injection on local anvil it falls back to an
anvil dev key (`app.js:41-45`), then builds the contract with the signer (`app.js:48`). This
is REAL wallet integration — but it drives only a local/undeployed contract, and there is
**no chainId-46630 (Robinhood) configuration anywhere in the frontend** (grep of
`drex-web/ launchpad-web/ extension/` for `46630`/`Robinhood` hits only README/comment
strings). So: real EVM plumbing, aspirational target.

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

**What a real user needs that is missing:** one wallet that both (a) holds an EVM key to
escrow on-chain (`commitBid`) **and** (b) produces the dregg-native sealed-order signature +
solvency/eligibility proofs, plus a hosted RPC that carries (b) to dregg and binds it to (a).
Today (a) lives in `launchpad-web`'s EVM path and (b) lives in `drex-web`'s wasm path, and
they do not meet.

---

## 3. `./extension` — the Dragon's Egg Cipherclerk

### 3.1 What it REALLY is (dregg-native, and genuinely good at that)

An MV3 extension (Chrome + Firefox) that is a citizen's cipherclerk for **dregg turns**:
- Named Ed25519 identity profiles; key derivation pinned to a golden vector across SDK/CLI
  (`README.md`, `src/background.ts` 5168 lines).
- **Authorization-first** `signTurnV3` — never signs blind; renders a faithful reading of
  every action/effect (`src/explain.ts`), nonce-bound confirm popup, federation-domain
  binding (`src/federation-domain.ts`).
- Receipt SSE stream, capability tokens evaluated by a WASM datalog engine, ZK **selective
  disclosure** (Bulletproofs range proofs over Ristretto), stealth addresses, committed
  private transfers.
- Ships the identical `dregg_wasm.js` + `dregg_wasm_bg.wasm` crypto core that `drex-web`
  loads (`web_accessible_resources` in `manifest.json`).

### 3.2 What it is NOT — the fhEgg gap (grep-verified)

- **Zero EVM signing.** A grep of `extension/src/` for `window.ethereum`,
  `eth_requestAccounts`, `secp256k1`, `personalSign`, `chainId`, `ethers`, `evm`, `46630`
  returns **empty**. The extension cannot escrow on an EVM chain or talk to `DreggLaunchpad`.
- **No DrEX / sealed-bid surface.** No `commitBid`/`reveal`/`shielded-order` page API; grep
  for `drex`/`fhegg`/`sealed`/`bid` in `src/` is empty. The DrEX flow **bypasses the
  extension entirely** — `drex-web/app.js` loads the wasm standalone via `drex-wallet.mjs`,
  not via the installed extension's `window.dregg.signTurnV3`. So the extension's page API is
  not on the DrEX path at all.
- **Shielded STARK membership is DISABLED.** The extension's own README states STARK
  Merkle-*membership* proof composition is off because `MerkleStarkAir`'s hash is not
  collision-resistant (forgeable) until it moves to a Poseidon2 Merkle hash. The in-browser
  shielded-membership path fhEgg Tier-1 wants is therefore not shipped.
- **Stale default endpoint.** `host_permissions` points at
  `https://devnet.dregg.fg-goose.online` (`manifest.json`) — the devnet-era domain (per
  memory, `fg-goose.online` is superseded; product domain is now `dregg.net`).

### 3.3 Does the extension need upgrading for fhEgg? — **YES.**

Concretely, to let a citizen participate in a shielded fhEgg launch from the extension:
1. **An EVM-signing leg** — secp256k1 + an injected-provider (or a bound EVM companion) so
   the extension can drive the on-chain escrow `commitBid`. Today it is dregg-native only.
2. **A sealed-bid / DrEX order surface** in the page API + an fhEgg-shaped confirm UX for the
   **commit → reveal** two-phase flow (the current `confirm-intent` is a single-turn confirm,
   not a sealed-bid ceremony), and DrEX should actually *route through the installed
   extension* rather than the standalone wasm.
3. **The shielded-order wasm path re-enabled** — swap `MerkleStarkAir` to a Poseidon2 Merkle
   hash so STARK membership (Cert-F / Tier-1 shielded) is no longer forgeable-and-disabled.
4. **A fresh default endpoint** (retire `fg-goose.online`).

An alternative to (1)/(2) is to keep the extension dregg-native and pair it with a separate
EVM wallet — but then a *binding* between the two identities has to be built and confirmed by
the user; that binding does not exist today either.

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
| 2. Sign a sealed bid | **SPLIT / MISSING as one action** | Dregg-native sealed commit + Bulletproof solvency proof = **REAL** (wasm), but demo-keyed and off the installed extension. On-chain sealed `commitBid` escrow = **real contract, undeployed**. The single user action that does *both* does not exist. |
| 3. Submit to a public RPC | **MISSING** | No hosted RPC; `serve.mjs` is tailnet-solo; no `/bid`/`/reveal` endpoint. The architecture doc's signed-data RPC is **designed, not built**. |
| 4. dregg clears privately | **REAL (local/solo)** | `/clear-shielded` (fhEgg solver) + `/prove-shielded` (Cert-F STARK) are real, but solo/local; the shielded launchpad-effect binding is a named weld. |
| 5. Settle on-chain | **MISSING** | `drex-web` `/settle` lands a dregg-native turn on the solo node (real), but there is **no on-chain settle** and **no concrete `IClearingAttestor`** (interface + mock only). `DreggLaunchpad.settleBid` exists but nothing drives it from a cleared shielded batch. |
| 6. See allocation | **REAL (local/demo data)** | Fill panel + graded fairness ledger (`drex-web`) and the token page from on-chain logs (`launchpad-web`) are real, but tied to local/demo runs. |

### The single biggest gap

**There is no hosted, public, signed-data RPC that unifies EVM on-chain escrow custody with
dregg-native private clearing into ONE user action against a deployed contract + a real
public node.** Everything is a local dev server on the tailnet; the two wallet halves (EVM
escrow / dregg-native sealed order) are disjoint; no launchpad contract is deployed to any
testnet, let alone Robinhood Chain (46630); and the `IClearingAttestor` that would carry
dregg's verdict on-chain is interface + mock only. The whole "signed sealed bid → `commitBid`
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
   chain; Robinhood 46630 if that is the target), **host `launchpad-web` publicly** (it
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

4. **Unify the wallet identity** — either add an EVM-signing leg to the extension or build a
   confirmed binding between the cipherclerk identity and an EVM companion, so ONE user
   identity does both the escrow and the sealed order (§3.3). Until this exists the two-wallet
   split blocks any shielded fhEgg user flow.

5. **Refresh the extension** — retire the `fg-goose.online` default endpoint, and route
   `drex-web` through the *installed* extension (`window.dregg`) rather than loading the wasm
   standalone, so the surface a user installs is the surface the flow actually uses.

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
- `launchpad-web/server.mjs` (`:9-11` EVM wallet reuse, `:38` empty address default, `:123`
  503 guard), `launchpad-web/public/js/app.js` (`:35-48` real EVM connect),
  `launchpad-web/public/receipt.html:42` (anvil 31337), `launchpad-web/README.md`.
- `extension/manifest.json` (permissions, `fg-goose.online` host), `extension/README.md`,
  `extension/src/` (grep: zero EVM/DrEX signing).
- `deploy/games/dregg-web-games.service` — the only hosted web surface (games demo, not DrEX).
- Backend Robinhood-46630 refs (settlement/light-client side, not a user wallet path):
  `eth-lightclient/tests/robinhood_holding.rs`, `cosmos-settlement/src/vk.rs`,
  `dregg-interchain-gov/tests/robinhood_inbound.rs`.
</content>
</invoke>
