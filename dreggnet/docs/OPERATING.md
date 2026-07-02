# OPERATING — run + operate the live DreggNet

This is the operator's doc: the live topology, how a node joins the fabric, how
to deploy/restart the stack, the cost model, and the runbook index. It is the
operate-it companion to `README.md` (the open-core split) and `ARCHITECTURE.md`
(the build ladder). For *what the network is and how it fits dregg*, start at the
substrate-side keystone: **`breadstuffs/docs/ONBOARDING.md`**. For *what users
can do*, see **`USING-DREGGNET.md`**.

Everything here is grounded to the real state as of 2026-06-28. Where a step is
staged or single-token-gated, it says so — no aspiration.

---

## 1. Topology

The fabric today is a **2-node federation** (target: **5**), a self-hosted
headscale mesh, and a home compute backend.

```
   community ── Discord ──► dreggnet-discord-bot ──► dregg-node (edge) ──► chain
                                  │                        ▲
                                  └── /admin (Caddy) ──────┘
   portal.dregg.studio ──► edge bot read API ──► live cells (trustless verify in-tab)
                          headscale overlay 100.64.0.0/10
   AWS edge box  ◄──────────────── mesh ────────────────►  persvati (compute backend)
   (stable IP, node-0 + gateway + bot)                     (node-1 + owned-sandbox exec + STARK proving)
```

| node | host | overlay | role |
|---|---|---|---|
| **edge** (node-0) | AWS `<EDGE_IP>` (t3.medium, EIP, `<EDGE_INSTANCE_ID>`, us-east-1c) | `100.64.0.1` | the public door: Caddy (TLS + basic-auth), gateway (Fly-machines API), control (lease dispatch), postgres, headscale + DERP relay, a `dregg-node`, the Discord bot |
| **persvati** (node-1) | ember's home Linux box (24c / 83 GiB / Ubuntu) | `100.64.0.2` | the engine room: the owned sandbox compute backend (`:8021/fulfill`), STARK turn proving, a `dregg-node` |
| homelab ×3 | pug (target) | `100.64.0.x` | additional independent consensus nodes + compute backends → the 5-quorum |

The economic shape: cloud spend is pinned to **one small always-on edge box**
(stable IP, TLS, mesh control, relay, orchestration front); everything that
scales with load — lease execution + STARK proving — runs on hardware already
owned, at ~free marginal cost. The edge is a thin door; persvati is the engine
room. Full detail: `deploy/PERSVATI-BACKEND.md`,
`deploy/ARCHITECTURE-COMPUTE-BACKEND.md`.

### Ports

- `:8420` (tcp) — node API (`/status`, `/health`, `/api/cell/{id}`,
  `/api/receipts`, faucet, turn submission).
- `:9420` (**udp**) — blocklace gossip (QUIC/quinn). It is UDP; a tcp-only port
  mapping silently fails to peer. On the edge (docker bridge) publish
  `"9420:9420/udp"`; persvati uses `network_mode: host`.
- `:8021` (tcp, overlay) — the compute backend's `/fulfill` + `/health`.
- `:80`/`:443` — Caddy, the only public HTTP surface on the edge.

### Consensus + what actually resists an attacker

Threshold is the strict blocklace supermajority `⌊2n/3⌋ + 1`; BFT is
`f = n − threshold`. At **n=2 → threshold 2, f=0**: a *real* federation (two
independent boxes, full BFT mode, signed quorum over the overlay), but **no fault
tolerance** — both must be online and honest for the chain to progress. At
**n=5 → threshold 4, f=1**: survives one down/Byzantine node. The load-bearing
fact for "resists attackers" is that the extra nodes are **independently
operated** (pug's homelab), not just the count. Full table + the verified
cross-node finality proof: `deploy/FEDERATION.md`.

Live federation id (committee = {edge, persvati}, epoch 0, threshold 2):
`4cf296834d87503f9bbe913c45dc7508a082473d4a15ffa5070e1a867d7b654c`.

---

## 2. Join the fabric (add a node)

Adding a node is **two** steps — the overlay (WireGuard mesh membership) and the
federation (consensus committee membership). The canonical operator spec is
**`deploy/FABRIC-JOIN.md`**; the consensus-committee re-roll is in
**`deploy/FEDERATION.md`**. The short form:

**1. Get on the overlay** (one command per machine):

```sh
# install tailscale if absent: curl -fsSL https://tailscale.com/install.sh | sh
sudo tailscale up \
  --login-server=https://headscale.dreggnet.fg-goose.online \
  --authkey=<reusable preauth key> \
  --hostname=<node-name>
```

Get a fresh reusable pre-auth key on the edge (the live keys are **not** committed
to the repo — regenerate, don't paste from history):

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_IP>
cd /opt/dreggnet
docker compose exec headscale headscale preauthkeys create --user 1 --reusable --expiration 720h
# (--user wants the numeric id; `headscale users list` shows ember = id 1)
```

`https://headscale.dreggnet.fg-goose.online/health` → `{"status":"pass"}`
confirms the control plane is up and the join works.

**2. Pick a role** (run either or both):

- **Compute backend** — run the owned-sandbox exec+prover agent (the `persvati-agent`
  pattern) as a systemd service bound to `0.0.0.0:8021`. It serves
  `:8021/fulfill` on the overlay and runs durable, metered workloads (the wasm
  tier genuinely runs; the python tier is a fail-closed seam today) + STARK proving. Scales with load. Smoke:
  `curl -s -X POST http://127.0.0.1:8021/fulfill -d '{}'` → a metered result.
  Concrete deploy + systemd unit: `deploy/PERSVATI-BACKEND.md`,
  `deploy/persvati-agent/`.
- **Consensus node** — run `dregg-node` (the `dregg-node:staging` image, or a
  native build). Modest resources. Joining the *committee* changes the
  `federation_id`, so growing the committee is a coordinated re-roll (the static
  5-node re-roll path is in `deploy/FEDERATION.md` §"How a new node joins").

---

## 3. Deploy + restart

### The staging stack (edge box)

The design principle: **the box just RUNS.** Heavy compilation happens off-box
(cross-build on a Mac, or natively on persvati); the box only pulls images and
runs `docker compose up`. A small box OOMs building the Rust closure — never
build Rust on the edge.

| piece | how it gets to the box | why |
|---|---|---|
| `dreggnet-gateway`, `dreggnet` (cli) | cross-build with `cargo zigbuild --target x86_64-unknown-linux-gnu`, rsync, wrap in debian-slim | pure cross-compilable Rust |
| postgres | `postgres:16-bookworm` (pulled) | stock |
| `dregg-node` | pre-built linux/amd64 image (`docker save`/`load`) | links a **host-native Lean archive** — **cannot** be cross-compiled |
| `dreggnet-discord-bot` | built native on persvati (`--features dregg-sdk/no-lean-link`), `docker save`/`load` to the edge | glibc binary; no Lean (signs+submits over HTTP, the node proves) |

Deploy from a dev Mac:

```sh
cp deploy/staging/.env.example deploy/staging/.env   # fill DREGG_NODE_IMAGE, secrets
BOX_HOST=<EDGE_IP> SSH_KEY=~/.ssh/dreggnet-staging.pem \
  deploy/staging/deploy.sh        # build (zigbuild) + ship (rsync) + up
# sub-commands: deploy.sh {build|ship|up|down|logs|build-node}
```

On the box:

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_IP>
cd /opt/dreggnet
docker compose ps                         # what's running
docker compose up -d <service>            # (re)start one service
docker compose logs -f --tail=100 gateway # follow
docker compose restart caddy              # after a DNS/cert change (clears ACME backoff)
```

The compose stack uses `restart: unless-stopped` + dockerd-on-boot, so every
service comes back after a box reboot. Full mechanics + the `.env` wiring:
`deploy/staging/README.md`, `deploy/staging/USING-STAGING.md`.

### The dregg-node — not cross-compilable (the recurring lesson)

`dregg-node` links `libdregg_lean.a` (the native objects the Lean compiler emits
for the verified kernel) **unconditionally**. That archive is host-architecture
and **cannot be cross-compiled** — build the node image where a Lean toolchain
lives (a linux/amd64 box with elan/lake + warm mathlib; persvati qualifies),
then `docker save | ssh … docker load` it onto the edge. See
`deploy/staging/README.md` §"The dregg node".

### The Caddy / cert lesson

Caddy is the only public door (TLS + basic-auth on the gated surface, no auth on
the public portal). Two faces (`deploy/staging/Caddyfile`):

- **`portal.dregg.studio`** — public, read-only: the static portal + its `/api/*`
  + `/observability/*` proxied to the edge bot's read surface.
- **`dreggnet.fg-goose.online`** — gated operator surface (gateway machines API +
  the bot's `/admin`), behind HTTP basic-auth.

The lesson baked into the Caddyfile: clients hitting the **raw IP** send no TLS
SNI, so set `default_sni localhost` and ship an internal-CA fallback cert so
`https://<EDGE_IP>/` handshakes *before* the real domain certs land.
Automatic Let's Encrypt (HTTP-01 over `:80`) issues once the A-record
propagates; **after the A-record lands, `docker compose restart caddy`** to clear
any ACME backoff so the real cert issues promptly. DNS: `dregg.net` stays
pristine for production; the live records hang off `fg-goose.online` /
`dregg.studio`.

### The Discord bot — the single token-drop

The bot is built, shipped to the edge, and wired into the staging compose; it is
**token-gated** and goes live the moment a real `DISCORD_TOKEN` (+ `DISCORD_APP_ID`,
`ADMIN_DISCORD_ID`) is set in `/opt/dreggnet/.env` and
`docker compose up -d dreggnet-discord-bot`. The full go-live runbook (OAuth
invite URL, `FEDERATION_ID` matching, the `/admin` portal): `deploy/staging/MINI-DEVNET.md`.

### Persvati compute agent restart

```sh
sudo systemctl status persvati-agent.service
sudo systemctl restart persvati-agent.service
journalctl -u persvati-agent.service -f
```

`Restart=on-failure` + `WantedBy=multi-user.target` → survives crashes + reboots.
Install + build steps: `deploy/PERSVATI-BACKEND.md`.

---

## 4. Cost model

| resource | running | idle / stopped |
|---|---|---|
| **edge** (t3.medium, AWS) | ~$0.0416/hr (~$30/mo) | ~$1.60/mo (EBS only) when stopped |
| Elastic IP | free while associated | ~$3.6/mo if allocated-but-unassociated — **keep it on the box** |
| **persvati** | ~free at the margin (home power, owned hardware) | — |
| **homelab** (later) | ~free at the margin (owned hardware) | — |

The edge is the **only recurring cloud spend, and it does not grow with load** —
all scale-with-load work (lease execution + proving) runs on owned hardware.
Stop the edge when idle (`aws ec2 stop-instances`); the EIP keeps the address
stable across stop/start so DNS does not break. Full numbers + the stop/start +
resize commands: `deploy/staging/USING-STAGING.md`, `deploy/staging/README.md`.

---

## 5. Runbook index

| topic | doc |
|---|---|
| Orient (the substrate-side keystone) | `breadstuffs/docs/ONBOARDING.md` |
| Open-core split + composition | `README.md` |
| Build ladder + bridge + mesh internals | `ARCHITECTURE.md` |
| Join the overlay (per-node) | `deploy/FABRIC-JOIN.md` |
| Consensus federation + committee re-roll + quorum | `deploy/FEDERATION.md` |
| The compute backend (architecture) | `deploy/ARCHITECTURE-COMPUTE-BACKEND.md` |
| The persvati deployment (concrete) | `deploy/PERSVATI-BACKEND.md` |
| Early-era compute (the offering) | `deploy/COMPUTE-OFFERING.md` |
| The persvati agent + systemd unit | `deploy/persvati-agent/` |
| Staging deploy mechanics | `deploy/staging/README.md` |
| Staging operate (logins, stop/start, cost) | `deploy/staging/USING-STAGING.md` |
| Discord bot go-live + mini-devnet | `deploy/staging/MINI-DEVNET.md` |
| Caddy config (the two faces) | `deploy/staging/Caddyfile` |
| Durable layer (postgres/billing) | `docs/DBOS-DURABLE-LAYER.md` |
| Self-host your own provider | `docs/SELF-HOST.md` |
| What users can do | `USING-DREGGNET.md` |

---

## 6. Reboot-survivability — honest state

- **Process layer: in place.** `restart: unless-stopped` + dockerd-on-boot
  (compose) and `Restart=on-failure`/`WantedBy=multi-user.target` (the systemd
  agent) bring services back after a reboot.
- **Durable-state recovery: self-healing on restart (fixed).** The
  genesis-first-then-overlay recovery (`1a61dc16d`) reconstructs the finalized
  ledger from (genesis baseline ⊕ durable overlay) in the sound order, and the
  SIGTERM-checkpoint handler (`node/src/main.rs::shutdown_signal`) flushes a clean
  checkpoint on `docker stop`/redeploy. So the previously-named caveat — a node
  that finalized turns but had not yet written its first checkpoint failing the
  recovery-convergence guard on restart — now **auto-recovers**: the
  `restart: unless-stopped` policy + `stop_grace_period: 45s` drive the
  crash → restart → recover → healthy loop without operator action. A node that
  hits **real corruption** still **fail-closes** (it exits rather than serve
  divergent state, so it crash-loops loudly under `unless-stopped` instead of
  serving wrong state — the ops dashboard pages `node_not_finalizing`). The
  manual fallback (wipe `dregg.redb`, keep `genesis.json` + `node.key`, restart to
  re-seed + replay from the quorum) remains valid for an unrecoverable local
  store. Full detail: `deploy/FEDERATION.md` §"Reboot-survivability",
  `docs/MONITORING.md` §"Auto-recovery".

---

*Dated 2026-06-28. Live keys/secrets are never committed — regenerate them on the
edge. Verify against HEAD before relying on a specific value.*
