# UPGRADE — safe rolling redeploy of a new build

How to ship a new build of the node / bot / gateway / compute backend without
taking the chain down or tripping the STORE-INTEGRITY event. The discipline:
**build off-box, ship as an image, swap one piece at a time, verify each before the
next.** Grounded in the real build/ship pipeline (`docker save`→ship→`docker load`)
and the node-a bounded-build pattern.

The order matters because the pieces depend on each other and because a careless
node swap (SIGKILL mid-checkpoint) is exactly what triggers the recovery event
(`INCIDENT-RESPONSE.md` §4). Take it in the order below.

## The shape: build off-box, ship pre-built

The edge box **never builds Rust** (a small box OOMs on the Lean/net closure —
`DEPLOY.md`). Each piece ships pre-built:

| piece | built where | shipped how |
|---|---|---|
| `dregg-node` | **node-a** (needs a Lean toolchain — links `libdregg_lean.a`, **not** cross-compilable) | `docker save | gzip` → scp → `docker load` |
| `dreggnet-discord-bot` | node-a native (`--features dregg-sdk/no-lean-link`) | `docker save | gzip` → scp → `docker load` |
| `gateway`, `dreggnet` (cli), `ops` | a dev Mac (`cargo zigbuild --target x86_64-unknown-linux-gnu`) | rsync binaries, wrap in debian-slim |
| `postgres` | n/a (`postgres:16-bookworm`) | pulled |

## 0. Build — the bounded, teed pattern (node-a)

The node + bot build on node-a, which runs `earlyoom` configured to **reap the
build toolchain** under memory pressure (`HARDWARE-NODE.md`). An unbounded
`-j$(nproc)` on the Lean/mathlib closure spikes memory + heat and earlyoom kills
the compiler mid-build — and if that build is rebuilding a *running* node, the
SIGKILL can cascade into a STORE-INTEGRITY event. **Bound it + tee the log:**

```sh
# on node-a, in the breadstuffs checkout — pin cores, bound jobs, tee the log:
cd ~/dev/breadstuffs
taskset -c 0-5 cargo build --release -j6 -p dregg-node 2>&1 \
  | tee /tmp/build-node.log | tail -n 50      # never re-run a build to read its log
```

For node/recovery work node-a keeps a **warm separate checkout**
(`~/dev/dregg-recovery`, warm `target/` + mathlib) so a rebuild doesn't cold-start
the whole closure under load (`NODE-OPS.md` §warm-worktree). Build the new image
there; do not churn `git stash`/`git worktree` on the shared tree.

Then build the image (the builder needs elan/lake for `build.rs` to splice the
x86_64 Lean archive — `NODE-OPS.md`):

```sh
docker buildx build --platform linux/amd64 --target node \
  -f docker/Dockerfile -t dregg-node:staging .
```

## 1. Ship — `docker save` → scp → `docker load`

```sh
docker save dregg-node:staging | gzip > /tmp/dregg-node.tgz
scp -i ~/.ssh/dreggnet-staging.pem /tmp/dregg-node.tgz ubuntu@<EDGE_HOST>:/tmp/
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST> \
  'gunzip -c /tmp/dregg-node.tgz | docker load'
# (the bot ships the same shape; gateway/cli/ops use deploy/staging/deploy.sh ship)
```

## 2. Swap — the safe order

Swap **one piece at a time**, verify, then the next. The dependency order:
**postgres → node → gateway → bot → ops** (downstream gates on upstream via compose
`depends_on: service_healthy`).

### The node — the careful one

A node swap MUST be a **graceful** stop so it flushes a clean checkpoint (SIGTERM →
`persist_on_shutdown`). Never `docker kill` a node mid-checkpoint.

```sh
cd /opt/dreggnet
sudo -e .env                                   # point DREGG_NODE_IMAGE at the new tag if changed
sudo docker compose up -d dregg-node           # compose stops (SIGTERM) + recreates with the new image
#   stop_grace_period: 45s gives the checkpoint room to flush

# VERIFY before moving on — it must come back HEALTHY (recovery replay can take a
# moment; the healthcheck has start_period: 90s):
sudo docker compose ps dregg-node              # → healthy
curl -s http://localhost:8420/status | jq '{federation_mode,peer_count,dag_height,healthy:.consensus_live}'
sudo docker compose logs --tail=80 dregg-node | grep -i "sigterm\|recover\|integrity\|self-advertisement"
```

> **If it comes back fail-closed** (STORE INTEGRITY), it is the recoverable
> order-bug or real corruption → `INCIDENT-RESPONSE.md` §4 / `DISASTER-RECOVERY.md`
> §B. A new image carrying `1a61dc16d` should NOT hit this on a graceful swap.

> **Coordinating a MULTI-NODE upgrade** (the whole committee gets a new node
> build): roll it **one node at a time**, never all at once. At n=2 (`f=0`) the
> chain pauses while a node is down — that is expected (quorum needs both); bring it
> back healthy before touching the next. At n≥4 (`f≥1`) the chain keeps finalizing
> through a single node's swap. **Critically: keep the Lean archive consistent
> across the committee** — a node on a newer archive than the others can trip a
> rust↔lean divergence (`INCIDENT-RESPONSE.md` §3). Upgrade the whole committee to
> the same build; don't leave it split.

### The bot

```sh
sudo docker compose up -d dreggnet-discord-bot
sudo docker compose logs -f dreggnet-discord-bot
#   db connected → node preflight (node OK: mode=…) → cell materialized →
#   "Bot connected as <name>" → commands registered
```

If the node's committee/key changed in this upgrade, update `FEDERATION_ID` first
(`SECRETS.md` / `COMMITTEE-CHANGE.md` §4) — a mismatch fails transfers with an
Ed25519 error.

### The gateway / cli / ops (cross-built)

```sh
# from a dev Mac — build (zigbuild) + ship (rsync) + up:
BOX_HOST=<EDGE_HOST> SSH_KEY=~/.ssh/dreggnet-staging.pem deploy/staging/deploy.sh
# or per-service on the box:
sudo docker compose up -d gateway   # then ops, then verify each /status, /healthz
```

### The compute backend (node-a)

```sh
# rebuild natively, then restart the systemd unit (Restart=on-failure):
cargo build --release -p dreggnet-node-agent
sudo systemctl restart node-agent.service
journalctl -u node-agent.service -f
curl -s -X POST http://127.0.0.1:8021/fulfill -d '{}'   # smoke the /fulfill contract
```

A compute-backend restart is low-risk (it holds no consensus state) but **in-flight
leases lapse** while it is down (`docs/MONITORING.md` `backend_down`) — do it in a
quiet window or expect a brief lapse blip.

## 3. Verify the whole stack recovered

```sh
sudo docker compose ps                                    # all Up/healthy
curl -fsS -u admin:<pw> https://ops.dreggnet.example.com/api/health | jq
curl -fsS -u admin:<pw> https://ops.dreggnet.example.com/api/alerts | jq  # → []
# end-to-end: a faucet transfer still finalizes cross-node (FEDERATION.md verify)
```

Confirm: no active alerts, `dag_height` advancing, `peer_count` restored, and a
test turn finalizes. Then prune the old image so disk doesn't creep
(`docs/MONITORING.md` §6): `sudo docker image prune -f`.

## Rollback

The previous image is still loaded until you prune it. To roll back: point
`DREGG_NODE_IMAGE` (or the service image) back at the prior tag and
`sudo docker compose up -d <service>`. Keep at least one prior image tag around
until the new one is proven (don't prune immediately after a node upgrade).

## See also

- NODE-OPS.md — the build pipeline, the bounded build, graceful shutdown, why a
  reaped build breaks a node.
- DEPLOY.md — how each image reaches the box, the compose stack, the deploy.sh
  sub-commands.
- INCIDENT-RESPONSE.md — what to do if a swap comes back fail-closed or diverges.
- COMMITTEE-CHANGE.md / SECRETS.md — when an upgrade also changes the committee /
  `FEDERATION_ID`.
- HARDWARE-NODE.md — earlyoom + the thermal ceiling the bounded build respects.
