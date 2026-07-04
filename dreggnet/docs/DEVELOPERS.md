# Developing on DreggNet — the single entry point

This is the one page to read first. It tells you **what you can do** on DreggNet,
**how** to drive it (SDK / gateway / bot / your own provider), walks you through
**building your first app end-to-end against a local node**, and gives you the
**API + SDK reference**. Everything below cross-links the deeper guides rather
than repeating them.

> **The substrate vs. the cloud.** dregg (the verified substrate — cells, turns,
> capabilities, receipts) lives in the `breadstuffs/` repo; DreggNet (this repo)
> is the *operated* half: the provider, gateway, durable orchestration, and the
> compute fleet that runs metered workloads under dregg leases. The SDKs you call
> are published from `breadstuffs/` (`@dregg/sdk` on npm, `dregg` on pip). To
> learn the model itself (cell · turn · capability+caveat · receipt) read
> `breadstuffs/docs/guide/BUILD-WITH-DREGG.md`; to validate this repo run
> `make test` (see [TESTING.md](TESTING.md)).
>
> **Want to start with *only* this repo?** The `dregg-cloud` CLI flow (`login` →
> `deploy` → `run` → `domains` → `ls`) is fully self-contained — no `breadstuffs/`
> checkout needed. Jump to **§3.5**. Links prefixed `breadstuffs/` below point into
> the sibling substrate repo; clone it alongside DreggNet to follow those.

The shape underneath everything: **you hold an unforgeable capability; you open a
funded lease; the network runs your work as a real, durable, metered workload; the
metered result comes back with a receipt anyone can verify.** No node runs work
your lease did not authorize, and no result is claimed beyond what your budget
paid for.

---

## 1. What you can do

Six capabilities. Each is one concrete action — what you *do*, what you *pay* (in
test `$DREGG` / DEC), what you *get back*.

| Capability | The one thing you do | You pay | You get back |
|---|---|---|---|
| **Durable metered compute** | Open a funded execution-lease and run a workload on the owned wasmi sandbox | metered DEC per step, capped by your budget | a durable checkpoint + a `TurnReceipt`; a run past your budget is refused by the executor, not trusted |
| **BYO-key Hermes** | Claim a channel and drive an agent loop through your own LLM key | metered DEC per call (rate + token budget) | the result + a receipt; an over-budget/over-rate call is refused in-band, naming the leg that bit |
| **Agent coordination** | Post a service request / promise to the intent ring; pipeline your payment against their promise | the agreed price, settled atomically | one verified all-or-nothing settlement (per-asset Σδ=0); if either side fails, nothing moves |
| **Minisite hosting** | Publish a directory of static files under a name | a cap-gated publish turn | the site served at `<name>.dregg.works`, plus a `PublishReceipt` proving who published what at which content root |
| **Agent web APIs** | Declare HTTP routes bound to owned-sandbox handlers | metered DEC per request (1 unit/request when leased) | DreggNet routes each request to its handler, runs it on the sandbox, serves the response; an exhausted lease yields `402`, no work served |
| **Verifiable receipts** | Open any cell card on `portal.dregg.studio` | nothing (read-only) | the cell's committed history re-verified **in your own browser** by a wasm light client — don't trust, verify |

Where each one lives, and the honest "what's real vs. a later rung" line:

- **Durable metered compute** — `docs/COMPUTE-TIERS.md` (the cap-grade → sandbox
  tier → provider map: `Sandboxed` wasm is real on every platform via the owned,
  vendored pure-Rust `wasmi` engine — the `add(40,2)=42` dogfood genuinely runs here;
  every stronger tier — `JitSandboxed`/JIT, `Caged` native/python/node, `MicroVm`
  Firecracker, `Gpu` — is an honest fail-closed seam today (`ExecError::NotWired` /
  `TierNotServed`), never a fake run or silent downgrade; wiring an owned engine per
  tier is future work) and the SDK `ExecutionLease`
  (`breadstuffs/docs/guide/AGENT-QUICKSTART.md` §3).
- **BYO-key Hermes** — the Discord bot's per-user agent loop and the SDK
  `ToolGateway` (metered, rate-limited, charged invocation):
  `breadstuffs/docs/guide/AGENT-QUICKSTART.md` §4, `docs/USING-DREGGNET.md` §1.
- **Agent coordination** — the intent ring / service-promise exchange:
  `breadstuffs/docs/guide/SERVICE-ECONOMY-SDK.md` (the
  `dregg.intents.requestService` facade over `ServicePromiseExchange`).
- **Minisite hosting** — `docs/WEB-HOSTING.md` (a site is a dregg cell; publish is
  cap-gated + receipted; serve is read-only; the `dregg.works` Caddy/DNS wiring is
  the deploy lane's step).
- **Agent web APIs** — `docs/AGENT-WEB-APPS.md` (the `dreggnet-webapp` `Router`,
  the portable `dreggnet-serve`, the leased `402`-on-exhaustion path).
- **Verifiable receipts** — `docs/USING-DREGGNET.md` §2 (the portal's in-tab
  recursive-STARK light client) and `breadstuffs/QUICKSTART.md` §6.

---

## 2. How — the four routes

You drive DreggNet through one of four front doors. All four bottom out on the
same lease → dispatch → run → meter → settle flow.

### a. The SDK route (build it yourself)

`npm i @dregg/sdk` or `pip install dregg`, then: **identity → fund → pay / lease /
invoke → read the receipt.** This is the programmatic path and the subject of the
tutorial in §3.

```ts
import { AgentRuntime, profiles, NodeClient } from "@dregg/sdk";
const identity = profiles.loadActive() ?? (profiles.create("me"), profiles.load("me"));
const node = new NodeClient("http://localhost:8421");
const runtime = new AgentRuntime(identity, node);
await runtime.faucet(2000);                       // test DEC
await runtime.pay(provider, 1_000n, asset);       // one conserving Transfer
```

Full surface: `breadstuffs/docs/guide/SERVICE-ECONOMY-SDK.md`,
`breadstuffs/sdk-ts/README.md`, `breadstuffs/sdk-py/README.md`.

### b. The gateway machines API route (fly.io-compatible)

The `dreggnet-gateway` binary serves a fly.io-compatible **machines API**: a
`POST /v1/apps/{app}/machines` create maps to a dregg execution-lease, runs it
through the bridge's real validation gate, and records the machine. If you already
speak the fly machines API, you speak DreggNet's compute control plane. See §5 and
`docs/RUN-LOCALLY.md` ("The gateway").

### c. The bot route (no code)

The Discord bot maps slash commands to real dregg cells, turns, and metered
workloads. Run `/start` → **Start the 2-minute tour** (identity → test DEC → one
real paid turn → a receipt you verify on the portal). See `docs/USING-DREGGNET.md`
§1 and `breadstuffs/docs/GETTING-STARTED.md`.

### d. The provider route (run your own)

DreggNet is not a monolith — `dreggnet-provider` stands up your own provider
against your own cells, machines, and gateway. See `docs/SELF-HOST.md`.

### e. The `dregg-cloud` CLI route (this repo, no `breadstuffs/` needed)

The `dregg-cloud` binary (built from this repo, `cli/`) is the developer cloud face:
**connect an account → deploy a site → run a metered workload → bind a domain**, all
over the local/in-process path with **no `breadstuffs/` checkout required**. It is
the fastest way to *touch* the headline flows. Build it with
`cargo build -p dreggnet-cli` (the binary lands at `target/debug/dregg-cloud`); the
copy-paste walkthrough is **§3.5** below.

---

## 3. Build your first app — a copy-paste tutorial

A real end-to-end walkthrough, entirely local: run a node, get an identity, faucet
test DEC, lease compute and run a metered workload, then read and verify the
receipt. You need the `breadstuffs/` checkout and `cargo`; the SDK steps need
Node 22 **or** Python 3.

### Step 0 — run a local dregg node with the faucet on

From the `breadstuffs/` repo (the node is the verified Lean producer; see
`breadstuffs/QUICKSTART.md` §1):

```sh
cargo build -p dregg-node
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
curl -s http://localhost:8421/status        # state_producer:"lean", healthy:false on a solo node (expected)
```

`--enable-faucet` opens the genesis faucet for local dev (a production node leaves
it off). `healthy:false` / `consensus_live:false` is expected on a solo node — a
single node has no committee to finalize a block, but turns still commit and
witness on the verified path.

### Step 1 — identity, fund, and a metered lease (TypeScript)

```sh
cd breadstuffs/sdk-ts        # or: npm i @dregg/sdk in your own project
npm ci && npm run build      # a fresh clone needs ../wasm/pkg first — see sdk-ts/README.md
```

```ts
import { AgentRuntime, Identity, NodeClient, ReceiptFilter, profiles } from "@dregg/sdk";

// 1. A named identity — the same $DREGG_HOME/profiles store as `dregg id`.
const identity = profiles.loadActive() ?? (profiles.create("me"), profiles.load("me"));

// 2. Bind to your local dev node (its signed-turn ingress is open with --enable-faucet).
const node = new NodeClient("http://localhost:8421");
const runtime = new AgentRuntime(identity, node);

// 3. Materialize + fund the agent cell from the faucet (test DEC).
await runtime.faucet(2000);

// 4. Observe before acting.
const stream = node.events().subscribe(new ReceiptFilter().cell(identity.cellId()));

// 5. Open + fund + run a durable, metered execution lease.
const lease = runtime.execution.lease({ maxSteps: 8, asset: runtime.nativeAsset() });
await lease.fund(identity.cellId(), 5_000n);   // one conserving Transfer in
const step = await lease.run(workEffects);     // checkpoint += 1, metered on one turn
console.log(step.step, step.remaining);        // your durable progress + budget left

// 6. The receipt IS your proof — committed, chained, witnessed.
const receipt = step.receipt;
console.log(receipt.turnHash, receipt.computronsUsed);
```

A `run` past `maxSteps` is rejected by the executor's `FieldLte` meter (not an
in-memory check), and the monotone gate refuses any rewind — your durable progress
is bound into the committed transition.

### Step 1 (alternative) — the same in Python

```sh
pip install dregg          # the light, toolchain-free wheel (pure-Rust executor)
```

```python
import dregg
rt = dregg.ServiceRuntime()            # a real in-process runtime (self-funded agent cell)
funder = rt.spawn()
lease = rt.lease(8)                     # maxSteps = 8
lease.fund(funder, 5_000)              # one conserving Transfer in
lease.run()                            # advances the durable checkpoint; FieldLte∧Monotonic enforced
```

`dregg.kernel()` proves which executor actually ran your step (the Rust executor
in the default light wheel; the verified Lean kernel in `dregg[kernel]`).

### Step 1 (alternative) — publish a minisite instead

If you'd rather ship static content than run compute, publish a directory as a
site cell (cap-gated, receipted) and serve it (from this repo):

```sh
cargo run -p dreggnet-webapp --bin dreggnet-host -- \
  --dir ./site --name blog --owner agent:me --port 8080
curl -s -H 'Host: blog.dregg.works' http://localhost:8080/      # served by Host
curl -s http://localhost:8080/blog/                             # no-DNS local fallback
```

The publish returns a `PublishReceipt { seq, name, owner, content_root,
asset_count }` — the verifiable record of who published what. See
`docs/WEB-HOSTING.md`.

### Step 1 (alternative) — lease compute through the gateway machines API

If you speak fly's machines API, run the gateway and drive it with `curl` (see
`docs/RUN-LOCALLY.md` for the Docker compose path):

```sh
curl -s -X POST http://localhost:8080/v1/apps/demo/machines \
  -H 'content-type: application/json' \
  -d '{"name":"w1","config":{"guest":{"cpus":1,"memory_mb":256}}}'
# -> {"id":"...","name":"w1","state":"created",...}
```

A create maps onto a dregg execution-lease and runs through the bridge's real
validation gate **before** any machine is recorded — an unfunded / ill-formed /
grade-below-floor lease yields a 4xx and no machine record.

### Step 2 — see + verify the receipt

The receipt you got back (`receipt.turnHash`) is committed, chained, and
witnessed. Read it back and verify it trustlessly:

```sh
curl -s http://localhost:8421/api/receipts                 # the chain, newest first
curl -N "http://localhost:8421/api/events/stream"          # live SSE feed of every receipt
```

Then open it on the portal (`portal.dregg.studio`, read-only v1) or, locally, the
explorer (`breadstuffs/QUICKSTART.md` §6) — the in-tab wasm light client
re-verifies the cell's committed history against the network root. Don't trust the
server; verify it.

> The federation-attested artifacts a light client reads (committee-signed roots,
> finalized checkpoints, a standalone full-turn STARK) only exist once a committee
> finalizes blocks — empty/404 on a solo node by design. To see them populated,
> boot the local multi-node federation (`breadstuffs/QUICKSTART.md` §9,
> `demo/multi-node-devnet`).

That is the whole loop: **identity → fund → lease/publish/invoke → receipt →
verify.** The runnable Rust version of the economy loop is
`breadstuffs/sdk/examples/agent_business_loop.rs`
(`cargo run -p dregg-sdk --example agent_business_loop`).

---

## 3.5. The `dregg-cloud` CLI — the developer cloud flow (no `breadstuffs/` needed)

The §3 tutorial above drives the *substrate* (and needs the `breadstuffs/`
checkout). This section is entirely self-contained in **this repo**: the `dregg-cloud`
binary's developer cloud verbs — `login` / `deploy` / `domains` / `run` / `ls` /
`logs` / `destroy` — run over a local JSON notebook (a state dir), no node or
`breadstuffs/` required. It is the quickest way to walk the headline flows.

> Everything `dregg-cloud` records here is **local** (a `state.json` under the state
> dir) — `ls` says so in its header. The content is published + served locally; the
> public `<name>.dregg.works` edge is the gateway-mount step. Honest by design.

```sh
# Build the CLI (binary at target/debug/dregg-cloud).
cargo build -p dreggnet-cli
alias dregg-cloud=./target/debug/dregg-cloud

# 1. Connect an account. --new mints a fresh local cap-account. The dga1_ credential
#    is a BEARER SECRET: it is redacted in the output and stored 0600 in state.json.
dregg-cloud login --new
#   logged in as dregg:…
#   account dga1_…… (secret — hidden; rerun with --show-credential to reveal)
#   (a wallet-held credential instead: `dregg-cloud login --credential dga1_… --root <hex>`
#    — pass --root so the wallet login can also bind domains)

# 2. Deploy a git repo as a static site (clone → detect → build → publish), metered
#    + receipted, with the build commit folded into the cell's content_root.
dregg-cloud deploy https://github.com/you/blog.git --name blog
#   published locally (not yet served on the public edge):
#     site  blog  (will serve at https://blog.dregg.works/)
#     verify  the source-commitment manifest is at /.well-known/dregg-deploy.json

# 2b. Serve that deploy LOCALLY over HTTP (a real round-trip you can curl):
dregg-cloud deploy https://github.com/you/blog.git --name blog --serve --port 8080 &
curl -s -H 'Host: blog.dregg.works' http://127.0.0.1:8080/        # your index.html
curl -s -H 'Host: blog.dregg.works' http://127.0.0.1:8080/.well-known/dregg-deploy.json

# 3. Bind a custom domain (cap-gated). `verify` proves control via LIVE DNS — it
#    never trusts the value you pass, so it only goes green once you publish the TXT.
dregg-cloud domains add shop.example.com --site blog
#   then  dregg-cloud domains verify shop.example.com --txt dregg-verify-…
#   (publish that TXT at _dregg-verify.shop.example.com, then run the verify line)

# 4. Run a metered durable workload — YOUR program, not a demo. Open a funded lease,
#    then run a WAT file; the program you wrote is the program that runs.
echo '(module (func (export "run") (result i32) (i32.const 123)))' > prog.wat
LEASE=$(dregg-cloud lease open --cap-tier sandboxed --budget 10 | sed -n 's/^lease opened: //p')
dregg-cloud run --lease "$LEASE" --source prog.wat
#   output[0]  123
#   meter      1 units charged against budget 10

# 5. See + inspect your local records.
dregg-cloud ls                 # account, sites, leases, domains, workloads (+ state path)
dregg-cloud logs <id-prefix>   # a deploy's receipt or a workload's outputs
dregg-cloud destroy <id|domain>
```

That is the whole developer cloud loop, self-contained: **login → deploy (serve) →
domains → run your program → ls/logs**. Real e2e tests cover it
(`cli/tests/{e2e,deploy_e2e,cli_verbs_e2e}.rs`).

---

## 4. Validate your checkout — one command

```sh
make test          # the full offline-green gauntlet (all crates + e2e/integration)
make test-fast     # the quick unit subset
make lint          # fmt --check + clippy
make build         # cargo build --workspace
```

`make test` runs the default offline path green and skips the env-gated paths
(Postgres via `DATABASE_URL`, Solana devnet, the `dregg-verify` AGPL lane, a live
node) cleanly. To exercise a gated path, provide its env and run the matching
target — full breakdown in [TESTING.md](TESTING.md).

---

## 5. API / SDK reference

### The gateway machines API (`dreggnet-gateway`, fly.io-compatible)

Roots at `/v1/apps/{app}/machines`. Drive it with any HTTP client (`gateway/src/route.rs`).

| Method + path | Purpose |
|---|---|
| `POST /v1/apps/{app}/machines` | Create + admit a machine (body = fly create JSON; maps to a lease, runs the bridge gate before recording) |
| `GET /v1/apps/{app}/machines` | List machines for the app |
| `GET /v1/apps/{app}/machines/{id}` | Machine status |
| `POST /v1/apps/{app}/machines/{id}/stop` | Reap the workload |
| `POST /v1/apps/{app}/machines/{id}/start` | (Re)launch the workload |
| `DELETE /v1/apps/{app}/machines/{id}` | Destroy the record |
| `GET /` | Friendly landing page (HTML status) |
| `GET /status` (or `/v1`) | Gateway status as JSON |
| `GET /healthz` (or `/health`) | Minimal liveness JSON |

Create body shape (`gateway/src/types.rs::CreateMachineRequest`): `{"name": …,
"config": {"guest": {"cpus": N, "memory_mb": M}}}`. A body-less create makes a
default minimal shared-guest machine. Live now: create / list / status / stop /
start / delete. Deferred: the create→fulfill durable launch seam (the lifecycle
endpoints transition the record today) — `docs/RUN-LOCALLY.md` "What is live vs.
deferred".

The dynamic data plane (`dreggnet-serve` / the gateway's `WebAppHandler`) serves
an agent's declared routes (`GET /hello`, `GET /add?a=&b=`, …) bound to owned-sandbox
handlers — `docs/AGENT-WEB-APPS.md`. The static data plane (`dreggnet-host` / the
gateway's `SiteHostHandler`) serves published site cells by `Host` —
`docs/WEB-HOSTING.md`.

### The `@dregg/sdk` (npm) public surface

`Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt`. Full
table in `breadstuffs/sdk-ts/README.md`; the load-bearing exports:

| Export | Purpose |
|---|---|
| `Identity` / `profiles` | Ed25519 identity; the shared `$DREGG_HOME/profiles` named-identity store |
| `NodeClient` / `AgentRuntime` | A node's HTTP surface / an identity bound to it (`faucet`, `pay`, `services`, `execution`) |
| `TurnBuilder` / `AuthorizedTurn` | Typed verbs (`transfer` · `write`/`writeU64` · `grant` · `pay` · `effect`/`effects` · `.fee(n)`) → `.sign()` → `.submit()`; empty turns refused |
| `ServiceEconomy` (`runtime.pay` / `runtime.services.invoke` / `runtime.execution.lease`) | pay / invoke / durable metered lease, each desugaring to the verified turn the node executes |
| `Receipt` / `TurnProof` | Proof-of-execution noun; STARK lazily attached |
| `NodeEvents` / `ReceiptFilter` | `subscribe(filter)` → `AsyncIterable<Receipt>` (SSE, resume, reconnecting) |
| `AttestedQuery` | Light-client reads — `attestedRoots` / `checkpoint` / `turnProof` (no identity) |
| `TrustlineClient` / `ChannelsClient` / `MailboxClient` | The organs — credit lines / group-key channels / hosted inbox |
| `DeployChecker` | Static-check a DreggDL capability layout (conservation / non-amplification / well-formedness / ring-balance) before submitting |

### The `dregg` (pip) public surface

A PyO3 binding mirroring the same shape (`breadstuffs/sdk-py/README.md`):

```python
import dregg
ident = dregg.Identity.from_profile("me")          # ~/.dregg/profiles, shared with the CLI
receipt = ident.turn("http://localhost:8421").transfer("28c2cba0…", 100).sign().submit()
dregg.faucet(node, ident.cell_id, 2000, public_key=ident.public_key)   # --enable-faucet dev node
```

- `dregg.Identity` / `dregg.faucet` / `dregg.AttestedQuery`
- `dregg.ServiceRuntime` — `pay` / `invoke_service` / `lease` over the real
  in-process verified executor (`AGENT-QUICKSTART.md` §"What's real")
- `dregg.Trustline` / `dregg.Channels` / `dregg.Mailbox` — the organs
- `dregg.deploy` — `check` / `lower` (the real `dregg-deploy` crate)
- `dregg.pg` — drive pg-dregg from Python (`dregg[pg]`)
- `dregg.kernel()` — prove which executor ran a real transfer (`rust` light wheel
  vs. `lean` `dregg[kernel]` wheel)

The Rust SDK (`breadstuffs/sdk/`, the offline core every binding wraps) is
documented in `breadstuffs/docs/guide/SERVICE-ECONOMY-SDK.md` with each call
mapped to its underlying verified turn/effect.

---

## 6. The honest current state

- DreggNet is **early/alpha**: a small devnet on subsidized/free compute (a 2-node
  federation at time of writing, heading to 5 for real fault tolerance).
- Compute is **subsidized, not billed** in the early era — the meter is real and
  bounds runaway work; the budget is generous (`deploy/COMPUTE-OFFERING.md`).
- The portal is **read-only v1**; the Discord bot is **wired + token-gated**.
- The `dregg-verify` lane (reading funded leases from a live dregg node) is real
  behind an off-by-default feature — flipping it on makes the build a derivative
  of AGPL code, so it is the deliberate flip-on step (`docs/ORCHESTRATION-LOOP.md`,
  `docs/SELF-HOST.md`).
- The Solana bridge is **devnet / oracle-attested** today; mainnet-trustless is
  ahead.

Verify any specific value against HEAD before relying on it.

---

## Where next

- Run + demo this repo: `docs/RUN-LOCALLY.md` · validate it: [TESTING.md](TESTING.md).
- Operate your own provider: `docs/SELF-HOST.md`.
- Learn the substrate model: `breadstuffs/docs/guide/BUILD-WITH-DREGG.md` →
  `breadstuffs/QUICKSTART.md` (15-minute hands-on).
- The agent-shaped path: `breadstuffs/docs/guide/AGENT-QUICKSTART.md`.

*Verify against HEAD before relying on a specific value.*
