# NODE-OPS — deploy, restart, recover, and build a dregg-node

The lifecycle of a `dregg-node`: how to deploy one, restart/shut it down
gracefully, recover from the STORE-INTEGRITY event we actually hit, the build
pipeline (and why the node can't be cross-compiled), and the bounded-build
discipline that keeps a laptop alive.

## The node, in one line

`dregg-node` gossips a blocklace DAG over `9420/udp`, serves an HTTP API on
`:8420`, and links `libdregg_lean.a` (the verified kernel) **unconditionally** —
so it is **not cross-compilable** and must be built where a Lean toolchain lives.

### Ports

- `:8420` (**tcp**) — node API: `/status`, `/health`, `/api/cell/{id}`,
  `/api/receipts`, `/api/node/identity`, faucet, turn submission.
- `:9420` (**udp**) — blocklace gossip (QUIC/quinn). It is **UDP** — a tcp-only
  port mapping **silently fails to peer**. On a docker bridge publish
  `"9420:9420/udp"`; with host networking it binds the overlay interface directly.

## Deploy a node

### node-a / a homelab box (host networking)

`~/dregg-node/docker-compose.yml`:

```yaml
services:
  dregg-node:
    image: dregg-node:staging
    container_name: dregg-node
    restart: unless-stopped
    network_mode: host
    command: >
      run --data-dir /data --bind 0.0.0.0 --port 8420 --gossip-port 9420
      --key-file node.key --node-index 1 --federation-size 2
      --federation-mode full --federation-peers 100.64.0.1:9420
    volumes:
      - /var/lib/dregg-node/data:/data   # holds genesis.json + node.key
```

`--node-index`/`--federation-size` are documentation only — the committee comes
from `genesis.json` (FEDERATION.md).

### The edge (compose bridge)

In `/opt/dreggnet/docker-compose.yml`, the `dregg-node` service runs with
`--federation-mode full --federation-peers 100.64.0.2:9420 --enable-faucet` and
the gossip port published as **`"9420:9420/udp"`** (the udp gotcha above).

Both deployments use `restart: unless-stopped` + dockerd-on-boot, so the node
comes back after a host reboot.

## Restart + graceful shutdown

```sh
docker compose ps                              # what's running
docker compose up -d dregg-node                # (re)start
docker compose logs -f --tail=100 dregg-node   # follow
curl -s http://localhost:8420/health           # {"healthy":true,...}
curl -s http://localhost:8420/status           # dag_height / block_count / latest_height / peer_count
```

**Graceful shutdown = SIGTERM → checkpoint.** The node writes a checkpoint on a
clean `SIGTERM`, so `docker compose stop dregg-node` (or `systemctl stop`) is the
safe way down. A **SIGKILL mid-checkpoint** (or `docker kill`, or an OOM-kill —
see the bounded-build section) is exactly what triggers the recovery event below.
Prefer `stop` over `kill`; give it the stop-timeout to flush.

## The STORE-INTEGRITY recovery runbook

**Symptom.** On restart the node fail-closes and refuses to start:

```
STORE INTEGRITY EVENT … reconstructed ledger root does not match the durably
recorded finalized root
```

**Cause.** A node that has **finalized ≥1 turn but not yet written its first
ledger checkpoint** (interval = `LEDGER_CHECKPOINT_INTERVAL = 100` finalized
heights, `node/src/blocklace_sync.rs`) hits a recovery-order bug: recovery rebuilt
the ledger from the last checkpoint (none yet → empty) + the per-turn commit-log
overlay, but the genesis cells were re-seeded **after** that check, so the
reconstructed root omitted the untouched genesis cells and the convergence guard
fail-closed. The two usual triggers: a **sub-checkpoint restart** (restarting
before height 100) or a **SIGKILL mid-checkpoint**.

This is **fail-CLOSED** — the node refuses to serve a divergent ledger; it does
**not** serve wrong state. It self-resolves once the chain passes height 100 (a
real checkpoint then contains the genesis cells and recovery converges).

**The fix** is in the node source: `breadstuffs` commit **`1a61dc16d`**
*"fix(node): recover in the sound order — genesis baseline first, overlay
second"* — recovery now seeds the genesis baseline **before** applying the
commit-log overlay, so the reconstructed root includes the genesis cells and the
guard passes. Once every deployed node image carries this commit, a sub-checkpoint
restart recovers cleanly without intervention.

**Recovery procedure (verified, the fallback until every image has the fix).**
The node rejoins by catch-up — it re-derives the exact finalized state from the
quorum (lace-merge, FEDERATION.md):

```sh
cd ~/dregg-node            # or /opt/dreggnet on the edge
docker compose stop dregg-node

# 1. BACK UP node-data first (never destroy before you have a copy):
cp -a data/dregg.redb data/dregg.redb.bak.$(date +%s)

# 2. clear ONLY the ledger db; KEEP genesis.json + node.key:
rm -f data/dregg.redb

# 3. restart — it re-seeds genesis, re-peers, and replays the finalized DAG
#    from the quorum, re-deriving the exact finalized state:
docker compose up -d dregg-node
docker compose logs -f dregg-node
curl -s http://localhost:8420/status     # converges to the quorum's dag_height
```

Verified end-to-end: node-a was wiped this way, rejoined, and re-finalized
`turn 42dea554…` with the recipient cell back at `balance 100` and the identical
state commitment. **Recovering to the recorded finalized root needs the quorum
live** — at n=2 (`f=0`) the other node must be up for catch-up to converge.

## Build + ship the node image (the pipeline)

`libdregg_lean.a` is host-architecture; an arm64 Mac cannot cross-build the
linux/amd64 node (it would link arm64 objects into an x86_64 ELF). So build the
image **where a Lean toolchain lives** (a linux/amd64 box with elan/lake + warm
mathlib — **node-a** qualifies), then ship it as a saved image:

```sh
# on the Lean-capable amd64 builder (node-a), in the breadstuffs checkout:
cd ~/dev/breadstuffs
docker buildx build --platform linux/amd64 --target node \
  -f docker/Dockerfile -t dregg-node:staging .
#   (NOTE: docker/Dockerfile installs rust+nightly but NOT elan/lake — add the
#    Lean toolchain to the builder so build.rs can splice the x86_64 archive.)

# ship: docker save | gzip → scp → docker load (the same shape the bot uses):
docker save dregg-node:staging | gzip > /tmp/dregg-node.tgz
scp -i ~/.ssh/dreggnet-staging.pem /tmp/dregg-node.tgz ubuntu@<EDGE_HOST>:/tmp/
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST> \
  'gunzip -c /tmp/dregg-node.tgz | docker load'
```

Then set `DREGG_NODE_IMAGE=dregg-node:staging` in `/opt/dreggnet/.env` and
`docker compose up -d dregg-node`. (The gateway + cli ship differently — they
cross-build with `cargo zigbuild --target x86_64-unknown-linux-gnu`; see DEPLOY.md.)

## The bounded build (keep the build box alive)

The build box runs `earlyoom` configured to **prefer killing `cargo`/`cc`/`ld`**
(HARDWARE-NODE.md). An unbounded `cargo build -j$(nproc)` on the Lean/mathlib
closure spikes memory + heat and earlyoom reaps the compiler mid-build — which on
a *node* can be the SIGKILL that triggers the STORE-INTEGRITY event above. So
**bound heavy builds**:

```sh
# pin the build to 6 cores so it stays under the earlyoom/thermal ceiling:
taskset -c 0-5 cargo build --release -j6 -p <pkg>
```

### The warm-worktree pattern

For node/recovery work node-a keeps a **separate warm checkout** at
`~/dev/dregg-recovery` (a second worktree/clone with a warm `target/` + warm
mathlib) so a rebuild doesn't cold-start the whole closure under load. Build the
recovery image there, ship it, without disturbing the primary `~/dev/breadstuffs`
checkout. (Note: avoid `git stash` / `git worktree` churn on the *shared* tree —
keep recovery work in its own checkout.)

## Tee build output — don't re-run to read it

Never re-run a build just to search its log. Tee it:

```sh
taskset -c 0-5 cargo build --release -j6 -p dregg-node 2>&1 \
  | tee /tmp/build-node.log | tail -n 50
```

## See also

- FEDERATION.md — the consensus model, the cross-node verify, the lace-merge that
  makes catch-up sound.
- DEPLOY.md — the edge compose stack, the gateway/cli cross-build, Caddy + DNS.
- HARDWARE-NODE.md — earlyoom, the thermal ceiling, why builds get reaped.
- `deploy/FEDERATION.md` §"Reboot-survivability" — the original write-up of this.
</content>
