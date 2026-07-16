# Launchpad deploy runbook — the revenue rehearsal, public via Tailscale Funnel

The ordered go-live for the **dregg launchpad product layer** — the revenue rehearsal.
Two pieces: (1) the **launchpad-web** product surface (create / bid / token-page /
replayable-discovery, `launchpad-web/server.mjs`) served **publicly directly from hbox**
with `tailscale funnel` — **no AWS gateway, no gateway↔tailnet join, no DNS, no Caddy**
(the same pattern the games deploy verified live, `deploy/games/RUNBOOK-FUNNEL.md`); and
(2) the on-chain **DreggLaunchpad** contract deployed to a public testnet (Base-Sepolia
84532 or Robinhood Chain 46630) via `chain/script/DeployLaunchpad.s.sol`. This makes the
go-live a **small, safe flip** — `npm ci` → install → reload → health → the single
`tailscale funnel` command — not a new build.

> **Why funnel, not the gateway?** The earlier draft of this runbook fronted hbox with
> "the AWS gateway's Caddy over Tailscale". That topology is **false at the network layer**
> (verified 2026-07-15, `deploy/README.md`): the AWS edge is on `100.64.0.x` and hbox is on
> `skunk-emperor.ts.net` — **two tailnets that cannot reach each other** — and there is **no
> Caddy on the edge**. The only verified public path is `tailscale funnel` on hbox
> (`deploy/games/RUNBOOK-FUNNEL.md`, "THIS IS WHAT RUNS"). This runbook is now rebased onto
> it. The **contract-deploy half** (step c) was always sound and is unchanged.

**rung-1 needs ZERO dregg.** The launch runs OPEN / REPLAYABLE (attestor = `address(0)`,
permissionless on-chain finalize): the contract clears itself from the public revealed
book, dregg is not even in the settlement loop, and no private node / VK / attestor is
required. The launchpad-web + the on-chain contracts are the **whole thing** for rung-1
(`docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §2.3). This is the shortest
path to real (testnet) revenue.

**Two sources, one host.** The funnel unit serves `launchpad-web` bound to **loopback**
(`127.0.0.1:8785`); its data source is **env-selected**:
- **node-driven (default here)** — `DREGG_NODE=http://127.0.0.1:8420` reads launches as a
  real turn stream from the durable hbox solo node (`deploy/node/dregg-node.service`, the
  just-landed persistent-data-dir unit). Zero external dependency; the hbox-local rung.
- **EVM rung-1 contract** — `DREGG_NODE=` empty + `LAUNCHPAD_ADDRESS` + `LAUNCHPAD_RPC`
  points discovery at the on-chain contract from step (c). The browser drives that contract
  with the user's own wallet regardless; this only chooses what the discovery API indexes.

**Honest scope.** AUTOMATED by `deploy-launchpad.sh --funnel` (run on hbox): `npm ci`,
snapshot a rollback point, install the one user systemd unit (loopback:8785) + enable-linger,
reload, health-check `http://127.0.0.1:8785/api/config`, auto-revert on a failed gate; plus a
**keyless** `contract-dryrun` that SIMULATES the testnet deploy (no `--broadcast`). It **skips
the gateway/Caddy leg entirely** and, on a passing gate, **prints** the ember-gated
`tailscale funnel` flip — it does **not** run it. **EMBER-GATED** (this runbook's manual
steps): the durable node bring-up (or the funded-key contract broadcast), the env file, and
**the `tailscale funnel` command itself** (the public-exposure decision). Nothing here
broadcasts, exposes a surface, or places a secret.

---

## What is executable-on-hbox-today vs box-pending

| Step | Status |
|---|---|
| (a) durable `:8420` node up (node-driven source) | **executable on hbox today** (`deploy/node/RUNBOOK.md`) |
| (b) place `~/.config/dregg/launchpad-funnel.env` (loopback bind) | **executable on hbox today** |
| (c) contract dry-run (keyless sim) | **executable today** (anywhere); **broadcast** = ember + funded key |
| (d) `deploy-launchpad.sh --funnel` (npm ci + install unit + loopback health) | **executable on hbox today** |
| (e) **the `tailscale funnel --https=8443` public flip** | **box-pending** — needs hbox to confirm :8443 is free + Funnel allows a second port on this tailnet plan (see Topology) |
| (f) smoke test the public URL / take-down | **box-pending** (after the flip; on hbox) |

Every command below is run **on hbox** (`ssh hbox`) as the login user unless marked
otherwise.

---

## Topology (funnel — no gateway, no Caddy, no DNS)

> `<tailnet>` here is **`skunk-emperor.ts.net`** (Funnel is enabled on it; the games
> funnel + `nextop` already funnel), and `hbox-dregg` is `100.95.240.73`.

```
  https://hbox-dregg.<tailnet>.ts.net:8443     ← Tailscale Funnel (public, auto-TLS)
        │  Funnel proxies the PUBLIC :8443 → the LOCAL :8785
  ┌─────▼───────────────── hbox (tailnet node hbox-dregg, 100.95.240.73) ─────────┐
  │  tailscale funnel --https=8443 8785  ── public edge (TLS + hostname), no Caddy   │
  │  dregg-launchpad-web-funnel (user unit)  127.0.0.1:8785  ← create/bid/token/API  │
  │        │  DREGG_NODE=http://127.0.0.1:8420  (node-driven source, default)        │
  │  dregg-node (solo devnet)  127.0.0.1:8420  ← launches as a real turn stream       │
  └────────────────────────────────────────────────────────────────────────────────┘
        (EVM lane, in parallel:) browser drives the REAL DreggLaunchpad on a public
        testnet with the USER's own wallet — see step (c). DREGG_NODE= empty selects it.
```

- The web server binds **loopback** (`127.0.0.1:8785`) — Funnel serves a **local** port,
  reaching into localhost. (Contrast the gateway variant's tailnet-iface bind
  `100.95.240.73:8785`, which a separate gateway Caddy would reverse-proxy.) `8785` is FREE
  on hbox (`8790`/`8781`/`8787` are the games web / drex-web / dreggcloud).
- **Tailscale Funnel is the public edge** — it terminates TLS and owns the public hostname.
  No Caddy, no cert management, no DNS.

### ⚠ THE ONE PORT DECISION — launchpad takes the SECOND funnel port (:8443)

Tailscale Funnel exposes **only** the public ports `443` / `8443` / `10000`, and the **games
funnel already holds public :443** (`tailscale funnel 8790`). So the launchpad **cannot also
take :443** the same way. This runbook picks:

**(A) — rung-1, chosen: launchpad on the second funnel port `:8443`.**
```bash
tailscale funnel --bg --https=8443 8785     # → https://hbox-dregg.<tailnet>.ts.net:8443
```
One command, no new component, no disruption to the games funnel on :443. The cost is an
**ugly port in the URL** (`:8443`). This is the minimal rung.

**(B) — later consolidation: one local reverse-proxy path-splitting a single `:443`.**
A single loopback reverse-proxy (Caddy/nginx on hbox) that routes `/ → games:8790` and
`/launchpad → :8785`, fronted by ONE `tailscale funnel :443`. Cleaner URL (no port, path
prefix), but it **adds a proxy component** and **touches the games funnel** (the games unit
must move off its own `:443` funnel behind the proxy). Deferred — not needed for the rehearsal.

> **⚠ BOX-PENDING (confirm on hbox before the flip):** whether **`:8443`** (or `:10000`) is
> actually free on `hbox-dregg` and whether **Funnel permits a second public port** on this
> tailnet's plan. `tailscale funnel status` shows what is already served; if `--https=8443`
> is rejected, fall back to `--https=10000`, or adopt option (B). This is the single fact
> that cannot be verified off-box.

---

## Ordered go-live

Mark: ⟨EMBER⟩ = a human does it (includes every public-exposure step);
⟨SCRIPT⟩ = `deploy-launchpad.sh --funnel` does it.

### (a) SOURCE BRING-UP — the durable hbox `:8420` node (node-driven default)  ⟨EMBER⟩

The node-driven source reads launches as real turns from the durable solo node. Stand it up
per [`deploy/node/RUNBOOK.md`](../node/RUNBOOK.md) (a systemd **user** unit with a
**persistent** data dir + linger — the fix for the incident that lost the last ledger).
Confirm it is up on loopback:
```bash
# on hbox:
curl -fsS http://127.0.0.1:8420/status | jq '{healthy, federation_mode, state_producer}'
ss -tlnp | grep 8420    # LISTEN 127.0.0.1:8420 — NEVER 0.0.0.0
```
> **EVM-lane alternative:** if you are running the on-chain rung-1 rehearsal instead of the
> node-driven source, this step is the **contract deploy** in (c); leave `DREGG_NODE=` empty
> in the env file (b) and set `LAUNCHPAD_ADDRESS`. The two sources are mutually exclusive per
> unit — the env file selects one.

### (b) Place the funnel env on hbox  ⟨EMBER⟩
```bash
# on hbox:
mkdir -p ~/.config/dregg ~/.local/state/dregg-launchpad
cp ~/dev/breadstuffs/deploy/launchpad/.env.example ~/.config/dregg/launchpad-funnel.env
$EDITOR ~/.config/dregg/launchpad-funnel.env
#   LAUNCHPAD_HOST=127.0.0.1        ← LOOPBACK (Funnel serves the local port). NEVER the
#                                     tailnet iface here — that is the gateway variant's bind.
#   PORT=8785
#   # node-driven (default): read launches from the durable :8420 node
#   DREGG_NODE=http://127.0.0.1:8420
#   # OR the EVM lane instead: leave DREGG_NODE empty and set:
#   #   DREGG_NODE=
#   #   LAUNCHPAD_ADDRESS=0x<from step c>
#   #   LAUNCHPAD_RPC=https://sepolia.base.org
chmod 600 ~/.config/dregg/launchpad-funnel.env
```
This is a **separate** env file from the gateway variant's `launchpad.env`, so the two
topologies never share a bind line (a stale tailnet-iface bind would break Funnel). No prod
key is ever committed or placed by an agent — the launchpad-web holds **no key**: the browser
drives the contract with the user's own wallet; the backend only READS.

### (c) Deploy the contract to the testnet (the EVM lane)  ⟨DRY-RUN automated / BROADCAST ember⟩

Unchanged and sound. First rehearse keylessly (no key, no tx — compiles, deploys in-sim, runs
a full fair-launch demo, asserts the uniform clearing):
```bash
cd ~/dev/breadstuffs/deploy/launchpad
./deploy-launchpad.sh contract-dryrun                          # pure local simulation
DEPLOY_RPC=base_sepolia ./deploy-launchpad.sh contract-dryrun  # READ-ONLY vs the real RPC
```
Then the **ember-only** broadcast (a real tx; needs a funded testnet key):
```bash
# Base-Sepolia (84532):
export DEPLOYER_PRIVATE_KEY=0x<funded testnet key>       # EMBER input, NEVER committed
export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org
cd ~/dev/breadstuffs/chain
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad --rpc-url base_sepolia --broadcast --verify -vvv

# Robinhood Chain (46630) instead:
export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
forge script script/DeployLaunchpad.s.sol:DeployLaunchpad --rpc-url robinhood_testnet --broadcast -vvv
```
The broadcast deploys **one** contract (the launchpad); registration is permissionless. Put
the printed `DreggLaunchpad :` address into `~/.config/dregg/launchpad-funnel.env` as
`LAUNCHPAD_ADDRESS` (and set `DREGG_NODE=` empty) **only if** you are surfacing the EVM lane
through the funnel host; the node-driven default (a) does not need this.

### (d) Run the deploy — build + install the web unit on LOOPBACK  ⟨SCRIPT⟩
```bash
ssh hbox
cd ~/dev/breadstuffs/deploy/launchpad
./deploy-launchpad.sh --funnel --dry-run   # rehearse — prints every step, no side effects
./deploy-launchpad.sh --funnel             # npm ci -> snapshot -> install -> reload -> health
```
`--funnel` runs `npm ci` for `launchpad-web`, installs the **funnel** user unit
(`dregg-launchpad-web-funnel.service`, bound `127.0.0.1:8785`) with `loginctl enable-linger`
so it survives logout AND reboot, and **skips the gateway/Caddy leg entirely**. Its health
gate polls `http://127.0.0.1:8785/api/config`. On a passing gate it **prints** the ember-gated
`tailscale funnel` flip — it does **not** run it. Knobs: `AUTO_REVERT=0`, `HEALTH_TIMEOUT=180`.

### (e) Health-check localhost, then ⚠ THE PUBLIC-EXPOSURE FLIP  ⟨(d) SCRIPT gate · flip EMBER⟩

The script's gate already confirmed loopback health. By hand (still private):
```bash
curl -fsS http://127.0.0.1:8785/api/config     # 200 JSON {rpc,address,abi,source,...} — loopback, NOT public
```

**⚠ EMBER-GATED PUBLIC-EXPOSURE FLIP** — this single command makes the demo public
(**box-pending**: confirm `:8443` is free + Funnel allows a second port, see Topology):
```bash
tailscale funnel --bg --https=8443 8785        # serve 127.0.0.1:8785 publicly (public 8443 -> local 8785)
```
Confirm the public URL:
```bash
tailscale funnel status                        # shows https://hbox-dregg.<tailnet>.ts.net:8443 -> 127.0.0.1:8785
curl -fsS https://hbox-dregg.<tailnet>.ts.net:8443/api/config   # 200 through Funnel's TLS
```
If `--https=8443` is rejected on this tailnet plan, try `--https=10000`, or adopt option (B)
in Topology. Nothing is public until this runs; running it **is** the go-live decision.

### (f) Smoke test  ⟨EMBER⟩  ⟨box-pending⟩
Against the public URL `https://hbox-dregg.<tailnet>.ts.net:8443`:
- Open `/` — the discovery page + catalog load.
- **Connect a wallet** (`window.ethereum`, on the testnet chain — EVM lane) or observe the
  node-driven launch stream (default).
- **Run a launch end-to-end**: `create.html` register a launch with a disclosed schedule →
  sealed `commitBid` → `revealBid` → permissionless `finalizeClearing` (uniform price) →
  `settleBid` → token page shows the one clearing price everyone paid + the holder
  distribution. Every number is checkable (on-chain for the EVM lane; on the node's ledger
  for the node-driven source — `curl -fsS http://127.0.0.1:8420/api/receipts | jq '.[-3:]'`).

### (g) Take-down  ⟨EMBER⟩
Remove the public surface instantly (the loopback unit keeps running):
```bash
tailscale funnel --https=8443 off              # public URL gone; 127.0.0.1:8785 still serves locally
tailscale funnel status                         # confirm no launchpad funnel (games :443 unaffected)
```
Stop the web unit entirely / roll back:
```bash
systemctl --user stop dregg-launchpad-web-funnel
./deploy-launchpad.sh releases                  # list rollback snapshots
./deploy-launchpad.sh --funnel rollback         # restore the prior unit + restart
```

---

## What is automated vs ember-gated (the honest cut)

| Step | Who |
|---|---|
| `npm ci` the launchpad-web deps (on hbox) | **script** (`--funnel`) |
| snapshot a rollback point (unit + git rev) | **script** |
| install the funnel user unit (loopback:8785) + enable-linger | **script** |
| health-check `127.0.0.1:8785/api/config` + auto-revert on failure | **script** |
| **keyless** contract deploy DRY-RUN (`contract-dryrun`) | **script** |
| **(a)** durable `:8420` node up (node-driven source) | ember |
| place `~/.config/dregg/launchpad-funnel.env` (loopback bind) + chmod 600 | ember |
| **(c)** the contract testnet BROADCAST (funded key + `--broadcast`) — EVM lane | ember |
| **⚠ `tailscale funnel --https=8443 8785`** — the PUBLIC-EXPOSURE flip | ember |
| smoke test the public URL / take-down | ember |

## Caveats (named, once)
- **Funnel serves LOOPBACK.** The unit binds `127.0.0.1:8785`; Funnel proxies the local port.
  Never bind `0.0.0.0` / the tailnet iface for the funnel variant.
- **Public port is `:8443`, not `:443`.** Funnel supports only `443`/`8443`/`10000`; games
  holds `:443`, so the launchpad takes `:8443` (option A) — an ugly port in the URL. Whether
  `:8443` is free + a second funnel port is allowed on this tailnet plan is **box-pending**;
  option (B) (one path-splitting reverse-proxy on `:443`) is the later, prettier consolidation.
- **rung-1 only, needs ZERO dregg.** OPEN / REPLAYABLE launches (`attestor = address(0)`,
  permissionless finalize). rung-2 (a real Groth16 clearing attestor) and rung-3 (shielded,
  private-dregg clearing) are the named upgrades (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`
  §3) — NOT part of this rehearsal.
- **The launchpad-web holds no key.** The browser drives the contract with the user's own
  wallet; the backend only READS. The funded deployer key (step c) is ember's, used once for
  the contract broadcast, never placed on hbox.
- **Two sources, env-selected.** node-driven (`DREGG_NODE=:8420`, the default here) OR the EVM
  contract (`DREGG_NODE=` empty + `LAUNCHPAD_ADDRESS`). One unit serves one source; the env
  file picks. The unit lists `EnvironmentFile=` LAST so the env file overrides the fallbacks.
- **Testnet, dev ceremony.** This is a public *testnet* rehearsal (no mainnet, no real value).
  A concrete attestor + the production MPC VK ceremony are ember-gated future steps.
