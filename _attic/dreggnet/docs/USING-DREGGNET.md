# USING DreggNet — I just joined, now what

## The offer, in one breath

**DreggNet Cloud is a small live network where you — or your agent — run real
metered work bounded by a capability you hold, and every run leaves a receipt
anyone can verify.** You hold an unforgeable capability; the network runs only
the work it authorizes; nothing is claimed beyond what your budget paid for; and
the proof comes back with the result. No pitch — the interesting part is what it
*reveals*: you can check the whole thing yourself, in your own browser, trusting
no one. Where something is read-only, staged, or not-yet-live, this doc says so.

It's **early/alpha**: a small devnet on subsidized/free compute, today a 2-node
federation. Real, just small.

### The four things you can do

Each is one concrete action — what you *do*, what you *pay* (in test $DREGG /
DEC), what you *get back*.

| Offer | The one thing you do | You pay | You get back |
|---|---|---|---|
| **1. Durable metered, cap-gated compute** | Open a funded execution-lease and run a workload (`lease.run`) | metered DEC per step, capped by your budget | a durable checkpoint + a `TurnReceipt`; a run past your budget is refused by the executor, not trusted |
| **2. BYO-key Hermes** | Claim a channel and **type** (`read…`, `run…`, or chat through your own LLM key) | metered DEC per call (rate + token budget) | the result + a receipt; an over-budget/over-rate call is refused in-band, naming the leg that bit |
| **3. Agent coordination** | `/coordinate @partner` — they produce, you pipeline your payment against their promise | the agreed price, settled atomically | one verified all-or-nothing settlement (Σδ=0); if either side fails, nothing moves |
| **4. Verifiable receipts** | Open any cell on `portal.example.com` | nothing (read-only) | the cell's committed history re-verified **in your browser** by a wasm light client — don't trust, verify |

### The 2-minute demo

The fastest way to *feel* it: join the Discord server, run **`/start`**, tap
**Start the 2-minute tour**. Three buttons — get an identity, get test DEC, do
one real paid turn — and you end holding a receipt you can verify on the portal.
The written-out version (Discord route + SDK route) is
`breadstuffs/docs/GETTING-STARTED.md`.

If you want the deeper picture — what dregg *is* underneath, why a capability is
unforgeable, how a turn carries its own proof — the one-doc orientation is
`breadstuffs/docs/ONBOARDING.md`.

The shape underneath everything here: **you open a funded lease; the network runs
your work as a real, durable, metered workload; the metered result comes back.**
No node runs work your lease did not authorize, and no result is claimed beyond
what your budget paid for. The same lease vocabulary drives every surface below.

---

## 1. The Discord bot — the community front door

The fastest way in. The bot maps Discord commands to real dregg cells, turns, and
metered workloads on the live network.

**Start here:** run **`/start`** and tap **Start the 2-minute tour** — a guided,
buttoned, can't-get-lost path (get an identity → get test DEC → do one real paid
turn) that ends with your first receipt and a portal link to verify it. You learn
no commands. The written walkthrough is `breadstuffs/docs/GETTING-STARTED.md`.

What you get when you join the server:

- **Open a channel.** Each user gets a semi-private per-user channel and a
  **cipherclerk** (a named signing identity) + a real **cell** on the live edge
  node — derived deterministically, so it's yours and reproducible.
- **Drive a Hermes.** A message in your channel becomes a cap-gated, **metered**,
  receipted dregg turn through the confined `ToolGateway` — a per-user agent loop
  bounded by your own cell. You drive an agent; it cannot exceed what your cell
  authorizes.
- **BYO-keys.** Your cipherclerk is your identity; `/cipherclerk export` hands you
  the key. The bot is custodial-by-default for convenience but the identity is a
  real Ed25519 key you control, signing canonical turns the node verifies
  end-to-end.
- **Lease compute.** Open a funded execution-lease from the channel and run a
  metered workload — the command maps to the same lease → dispatch → run → meter
  flow, and the metered result comes back in-channel.
- **See cells.** `/explorer`, `/status`, `/history`, `/activity`, plus deos
  affordances surfaced as Discord buttons.

Slash commands include `/cipherclerk create | balance | address | export`,
`/send` / `/tip`, gallery/identity/presence, and the explorer. Full command list:
`breadstuffs/discord-bot/README.md`.

**Honest state:** the bot is built, shipped to the edge, and wired end-to-end. It
is **token-gated** — it goes live the moment the operator drops a real
`DISCORD_TOKEN` (`deploy/staging/MINI-DEVNET.md` §4). Early-era leases run on
**generous / free subsidized budgets** so you can actually run things now (the
meter is real and bounds runaway work; it is just subsidized rather than billed —
see `deploy/COMPUTE-OFFERING.md` §Budgets).

---

## 2. portal.example.com — see + verify the network

A web page anyone can open to **see the live network and verify it yourself**.
The point isn't a dashboard — it's that the portal does not ask you to trust the
server. It ships a **recursive-STARK light client as wasm**, and when you open a
cell's card it verifies that cell's committed history **in your own browser**.
Don't trust the server; verify it.

What's there today (read-only v1):

- The **cell graph** — the custodial hub and its cells on the network.
- **Cells on the network** — the live cell list, each openable as a card.
- **Per-cell trustless verify** — open a card, the in-tab light client checks the
  cell's committed history against the network root.

**Honest state:** read-only v1, **coming up** (the `portal.example.com`
A-record + Let's Encrypt cert are propagating; reachable by IP in the meantime).
Drive-actions (open a lease, pay, fire a turn from the portal) are the next rung.
The public read API it calls (`/api/cells`, `/api/cell/<id>`,
`/api/receipts/recent`, `/api/federations`, the `/observability/stream` SSE feed)
is the edge bot's read surface, served with no auth.

---

## 3. The SDKs — pay / lease / run in a few lines

If you're building (or you're an agent), the SDKs give you the same lease/pay/run
vocabulary programmatically. They live in the **open dregg substrate repo**
(`breadstuffs/`):

- `sdk/` — the Rust core (the offline-capable canonical surface).
- `sdk-py/` — Python.
- `sdk-ts/` — TypeScript.

Each ships its own README + an `examples/` directory. The agent-shaped path — pay
→ fund an execution lease → run a metered workload → pay-per-use through a gateway
→ read your receipts — is laid out in:

- `breadstuffs/docs/guide/AGENT-QUICKSTART.md` — the few-lines version for an LLM/agent.
- `breadstuffs/docs/guide/SERVICE-ECONOMY-SDK.md` — the full API surface, each
  call mapped to its underlying turn.
- `breadstuffs/sdk/examples/agent_business_loop.rs` — the runnable loop.

The programmatic front to DreggNet's compute is the **Fly-compatible machines
API** on the gateway: a `POST .../machines` create maps to a lease, runs it
through the bridge's real validation gate, and records the machine (`gateway/`,
`deploy/COMPUTE-OFFERING.md`). On the staging surface it sits behind Caddy
basic-auth at `dreggnet.example.com` (`deploy/staging/USING-STAGING.md`).

To learn the model first (cell · turn · capability+caveat · receipt) and build
your first app, the developer onramp is `breadstuffs/docs/guide/` and the 15-minute
`breadstuffs/QUICKSTART.md`.

---

## 3.5 The `dregg-cloud` CLI — deploy + run from your terminal

If you'd rather drive DreggNet from a terminal than the bot or an SDK, the
`dregg-cloud` binary (built from *this* repo — `cargo build -p dreggnet-cli`, no
`breadstuffs/` checkout needed) is the developer cloud face:

```sh
dregg-cloud login --new                                   # a local cap-account (secret redacted)
dregg-cloud deploy https://github.com/you/blog.git --name blog --serve   # ship a site, serve it locally
dregg-cloud domains add shop.example.com --site blog      # bind a BYO domain (DNS-verified)
dregg-cloud lease open --cap-tier sandboxed --budget 10   # a funded execution-lease
dregg-cloud run --lease <id> --source prog.wat            # run YOUR program, metered
dregg-cloud ls                                            # your local sites/leases/domains/workloads
```

These records are a **local notebook** (a state dir) — published + served locally,
not yet on the public edge. The full copy-paste walkthrough, with what each command
prints, is `docs/DEVELOPERS.md` §3.5.

---

## 4. The browser extension — your cipherclerk

A Manifest-V3 browser extension (Chrome + Firefox) that is **your citizen's
cipherclerk**: it holds your named signing identities, shows you exactly what a
turn does *before* it signs, submits signed turns to a node, and listens to the
receipt stream so you see what committed.

Why it matters:

- **Named identities, not pasted hex.** An identity is a name you chose; the popup
  carries a profile switcher. Key derivation matches the CLI/SDK profile store
  exactly (a golden vector is pinned across three codebases so nothing can drift).
- **Authorization-first signing — it never signs blind.** Before signing, the
  clerk *decodes the turn* and renders a faithful human reading of every action
  and effect ("transfer 5 computrons from cell … to cell …"), bound to the
  canonical turn hash the node verifies and the receipt commits. Only your
  explicit acceptance releases the signature. An effect the clerk cannot read is
  surfaced as **UNKNOWN** with a do-not-sign-blind warning — never quietly elided.

Source + build: `breadstuffs/extension/` (README there).

---

## 5. The honest current state (so nothing surprises you)

- **The network is a 2-node federation** (edge + node-a), full BFT mode, with
  *verified* cross-node finality — heading to 5 nodes for real fault tolerance.
  At 2 nodes there is no fault tolerance yet (both must be online); independent
  operators joining is how that changes (`deploy/FEDERATION.md`).
- **Compute is early-era:** live but small, on subsidized/free budgets, running on
  one home box (node-a) plus the edge. The same path scales as hardware joins —
  nothing about the lease/run flow changes (`deploy/COMPUTE-OFFERING.md`).
- **The Discord bot** is wired + token-gated (one token drop from live).
- **The portal** is read-only v1, coming up.
- **The Solana bridge** is **devnet / oracle-attested** today — `$DREGG` proper
  lives on Solana *mainnet*; devnet proves the plumbing. Mainnet-trustless is
  ahead (`breadstuffs/docs/deos/{SOLANA-DEVNET,TRUSTLESS-SOLANA-BRIDGE}.md`).
- **The substrate is the verifiable half; DreggNet is the operated half.** When
  the portal says "verify it in your own browser," it means it — that's the dregg
  light client doing real work, not a claim.

---

## 6. Want to run your own?

DreggNet is **not a monolith**. Anyone can run their own provider against their
own dregg cells, their own machines, their own gateway — the moat is the network,
not the code. The self-hostable provider (`dreggnet-provider`) loads a config (the
cells source, the machine backend, the region, the gateway bind) and stands up the
provider it describes; federated providers speak one open lease/meter/pay protocol
between them. See `docs/SELF-HOST.md`, and to fold a homelab box into *this*
fabric, `deploy/FABRIC-JOIN.md`.

---

*Dated 2026-06-28. Verify against HEAD before relying on a specific value.*
