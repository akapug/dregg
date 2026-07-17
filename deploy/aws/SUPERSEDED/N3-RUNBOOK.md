# N3 RUNBOOK — the 3-node federation on one graviton

Brings the devnet from `peer_count: 0` (solo gateway) to a live 3-member
federation on the same instance, then runs the FIRST PARTITION DRILL
(REFINEMENT-DESIGN §"The distributed reality: n=3, live").

Everything here runs **on the instance** (`ssh ubuntu@devnet.dregg.fg-goose.online`)
unless marked otherwise. No step writes a secret into the repo.

## 0. Topology and identity map

| Instance name | systemd unit    | validator key       | data dir            | HTTP (loopback) | QUIC gossip | public? |
|---------------|-----------------|---------------------|---------------------|-----------------|-------------|---------|
| node 1        | `dregg-gateway` | `node-0` (node-0.key) | `/opt/dregg-data`   | 127.0.0.1:8420  | 0.0.0.0:9420 | yes — behind Caddy |
| node 2        | `dregg-node@2`  | `node-1` (node-1.key) | `/opt/dregg-data-2` | 127.0.0.1:8421  | 0.0.0.0:9421 | no |
| node 3        | `dregg-node@3`  | `node-2` (node-2.key) | `/opt/dregg-data-3` | 127.0.0.1:8422  | 0.0.0.0:9422 | no |

Env files: `/etc/dregg/node.env` (gateway, unchanged), `/etc/dregg/node-2.env`,
`/etc/dregg/node-3.env` (from `deploy/aws/node-{2,3}.env.example`; same
`DEVNET_PASSWORD`/`DEVNET_API_TOKEN` convention, normally left empty on 2/3).

Peer lists are **IP:PORT literals** (`127.0.0.1:9420` etc.) — the node's peer
parser (`node/src/blocklace_sync.rs`, `SocketAddr::parse`) silently skips
hostnames, so the docker-style `node-0:9420` form must never be used here.

**Gateway/Caddy routing — unchanged.** Every Caddyfile route keeps pointing at
`localhost:8420` (node 1, the public face). Nodes 2/3 get **no** Caddy routes,
**no** new security-group rules (the gossip listener binds `0.0.0.0` —
hard-coded — so the security group is the only fence; 9421/9422 and 8421/8422
must stay closed). Reach nodes 2/3 only from the instance shell, or via
`ssh -L 8422:127.0.0.1:8422 ...` from a laptop.

**⚠ CHAIN RESET.** `federation_id` is a commitment to the committee pubkeys,
so minting the 3-member committee starts a fresh chain: the solo gateway's
explorer history does not carry forward (its data dir is archived, not
deleted). This is the devnet's documented regeneration path
(`deploy/genesis/README.md`), now run on-instance so keys never leave the box.

**Note — `.devnet` marker.** `federation-keygen.sh` installs the `.devnet`
marker into all three data dirs (the genesis generator's devnet convention).
That implicitly enables `auto-approve-joins` on every node (F-CRIT-2 gate,
logged loudly at boot) — correct for this devnet, never for production. The
previous solo data dir had no marker, so this is a (devnet-intended) behavior
delta.

**⚠ n=3 liveness math (read before the drill).** The blocklace ratification
supermajority is `(2n/3)+1` (`blocklace/src/ordering.rs:173`), which for n=3
is **3 — finality needs all three nodes**. With node 3 stopped, nodes 1+2
keep accepting and locally committing turns (the HTTP path executes
optimistically and queues the block for ordering), the DAG keeps growing, but
**the finalized/attested height freezes until node 3 returns**. That stall is
the drill's expected, correct-BFT observable — not a failure. If
stop-one-keep-finalizing is wanted, the federation needs n=4 (supermajority
3). See "node-code gaps" in the lane report.

## 1. Preflight

```bash
cd /opt/dregg
bash deploy/aws/update.sh   # or: git pull + cargo build --release -p dregg-node
ls deploy/aws/dregg-node@.service \
   deploy/aws/dregg-gateway-federation.conf \
   deploy/aws/node-2.env.example deploy/aws/node-3.env.example \
   deploy/aws/federation-keygen.sh deploy/aws/N3-RUNBOOK.md
```

Record the pre-federation state for the before/after diff:

```bash
curl -s http://127.0.0.1:8420/status | jq '{peer_count, federation_mode, latest_height, dag_height, block_count}'
# expect: peer_count 0, federation_mode "solo"
```

## 2. Stop and archive the solo chain

```bash
sudo systemctl stop dregg-gateway
sudo mv /opt/dregg-data /opt/dregg-data.pre-federation.$(date +%Y%m%d%H%M%S)
```

(`federation-keygen.sh` refuses to run while any target data dir still holds a
live `dregg.redb`, so this step is enforced, not just polite.)

## 3. Keygen — generate the committee ON the instance

```bash
sudo /opt/dregg/deploy/aws/federation-keygen.sh
```

This mints 3 Ed25519 validator keys + `genesis.json` into
`/etc/dregg/federation/` (root:dregg 0750; keys 0600; **never committed**),
validates the JSON with `python3 -c json.load`, and installs per the §0 table:
each data dir gets its `node.key`, the shared `genesis.json`, and the
`.devnet` marker. It prints the new `federation_id` — note it for step 6.

Sanity:

```bash
jq '{federation_id, threshold, validators: [.validators[].name]}' /etc/dregg/federation/genesis.json
sudo ls -l /opt/dregg-data /opt/dregg-data-2 /opt/dregg-data-3
```

## 4. Env files + systemd install

```bash
# Per-instance env (root:dregg 0640, same discipline as node.env):
sudo install -m 0640 -o root -g dregg /opt/dregg/deploy/aws/node-2.env.example /etc/dregg/node-2.env
sudo install -m 0640 -o root -g dregg /opt/dregg/deploy/aws/node-3.env.example /etc/dregg/node-3.env

# Template unit for the internal nodes:
sudo cp /opt/dregg/deploy/aws/dregg-node@.service /etc/systemd/system/

# Gateway drop-in (solo → federation member node-0; also retunes memory):
sudo mkdir -p /etc/systemd/system/dregg-gateway.service.d
sudo cp /opt/dregg/deploy/aws/dregg-gateway-federation.conf \
    /etc/systemd/system/dregg-gateway.service.d/federation.conf

sudo systemctl daemon-reload
sudo systemctl enable dregg-node@2 dregg-node@3
```

No secrets are needed in `node-2.env`/`node-3.env`; leave
`DEVNET_PASSWORD=`/`DEVNET_API_TOKEN=` empty (internal nodes run locked).
The gateway keeps its existing `/etc/dregg/node.env` and ExecStartPost unlock.

## 5. Start order

Internal peers first, public face last (the gateway then dials both on its
first topic join; late peers are also healed by the frontier-announce sweep,
so this order is a nicety, not a correctness requirement):

```bash
sudo systemctl start dregg-node@2
sudo systemctl start dregg-node@3
sudo systemctl start dregg-gateway
journalctl -u dregg-node@2 -u dregg-node@3 -u dregg-gateway -n 50 --no-pager
```

Healthy logs show `loaded federation keys from genesis.json (key_count=3)`,
`federation mode: full`, `blocklace PeerNode ready`, and
`initializing blocklace consensus participants=3 quorum_threshold=3`.

## 6. Verification gates (bring-up)

**Gate A — status truth on all three.** (`peer_count` reflects the
*configured* peer list — `node/src/api.rs` reports `s.peers.len()` — which is
why gates B/C below check *live* convergence, not just config.)

```bash
for p in 8420 8421 8422; do
  echo "── :$p"; curl -s http://127.0.0.1:$p/status \
    | jq '{healthy, peer_count, federation_mode, consensus_live, dag_height, latest_height, public_key}'
done
# expect on EVERY node: peer_count: 2, federation_mode: "full",
# consensus_live: true, healthy: true, and three DISTINCT public_key values
# matching genesis.json's validators.
```

**Gate B — DAG heights converge.** Repeat the loop above a few times (or
`watch`): `dag_height` on the three nodes must advance together and agree
within one heartbeat window (±1 during production).

**Gate C — a faucet turn on node 1 appears on node 3.** Recipients come from
the freshly generated genesis (`initial_cells[0]` is the faucet; 1–3 are
alice/bob/carol):

```bash
ALICE=$(jq -r '.initial_cells[1].id' /etc/dregg/federation/genesis.json)
TURN=$(curl -s -X POST http://127.0.0.1:8420/api/faucet \
  -H 'content-type: application/json' \
  -d "{\"recipient\":\"$ALICE\",\"amount\":100}" | jq -r '.turn_hash')
echo "turn: $TURN"

# Wait a few block cadences (~10 s), then confirm node 3 EXECUTED it
# (/api/receipts returns a bare array of the node's last 50 receipts):
curl -s http://127.0.0.1:8422/api/receipts | jq --arg t "$TURN" \
  'map(select(.turn_hash == $t)) | length'        # expect 1
curl -s http://127.0.0.1:8422/api/cells | jq --arg c "$ALICE" \
  '.[] | select(.id == $c) | .balance'            # alice credited
```

This is exactly what the public explorer renders (it reads the same
receipts/events surface through Caddy → node 1), so the same turn is also
visible at `https://devnet.dregg.fg-goose.online/explorer`.

**Gate D — the public face still works.**

```bash
curl -s https://devnet.dregg.fg-goose.online/status | jq '{healthy, peer_count, federation_mode}'
# served by node 1 through Caddy; peer_count: 2, federation_mode: "full"
```

## 7. Discord bot follows the new federation id

The bot pins `FEDERATION_ID` in its env; the keygen minted a new one:

```bash
sudo sed -i "s/^FEDERATION_ID=.*/FEDERATION_ID=$(jq -r .federation_id /etc/dregg/federation/genesis.json)/" \
  /etc/dregg/discord-bot.env
sudo systemctl restart dregg-discord-bot
```

## 8. FIRST PARTITION DRILL

This drill exercises tonight's soundness fix live: the **identity execution
cursor** (`node/src/execution_cursor.rs`) makes catch-up reorgs safe — a late
block sorting into the already-executed region is absorbed by identity
(no double-apply, no lost turn) and surfaces as the
`dregg_tau_prefix_shifts_total` counter (the machine-checked
`TauPrefixMonotone` counterexample, observed in production).

**8.1 Baselines** (note all values):

```bash
for p in 8420 8421 8422; do
  echo "── :$p"
  curl -s http://127.0.0.1:$p/status | jq '{latest_height, dag_height, block_count}'
  curl -s http://127.0.0.1:$p/metrics | grep -E '^dregg_tau_prefix_shifts_total' || echo "dregg_tau_prefix_shifts_total 0 (not yet emitted)"
done
```

**8.2 Partition — stop node 3:**

```bash
sudo systemctl stop dregg-node@3
```

**8.3 Faucet turns on nodes 1 AND 2** (distinct recipients dodge the
per-cell 60 s faucet limit):

```bash
BOB=$(jq -r '.initial_cells[2].id'   /etc/dregg/federation/genesis.json)
CAROL=$(jq -r '.initial_cells[3].id' /etc/dregg/federation/genesis.json)
T1=$(curl -s -X POST http://127.0.0.1:8420/api/faucet -H 'content-type: application/json' \
     -d "{\"recipient\":\"$BOB\",\"amount\":100}"   | jq -r '.turn_hash');  echo "node1 turn: $T1"
T2=$(curl -s -X POST http://127.0.0.1:8421/api/faucet -H 'content-type: application/json' \
     -d "{\"recipient\":\"$CAROL\",\"amount\":100}" | jq -r '.turn_hash');  echo "node2 turn: $T2"
```

**Gates during the partition (expected behavior at n=3):**

- Both faucet calls return `success: true` with a `turn_hash` — nodes 1+2
  **accept and locally commit** turns while partitioned (optimistic local
  execution; the block is queued for ordering).
- `dag_height`/`block_count` keep growing on 8420 and 8421 (the two-node DAG
  still produces and cross-acks blocks).
- `latest_height` **freezes** on both — finalization needs the n=3
  supermajority of 3 (see §0). A frozen attested height with a growing DAG is
  the drill's proof that finality is real (a node that kept "finalizing"
  alone here would be solo-committing, not federating).

**8.4 Heal — restart node 3 and verify convergence:**

```bash
sudo systemctl start dregg-node@3
# within a catch-up sweep or two (~10–30 s):
for p in 8420 8421 8422; do
  echo "── :$p"; curl -s http://127.0.0.1:$p/status | jq '{latest_height, dag_height}'
done
```

Convergence gates:

- `latest_height` **unfreezes and advances** on all three, to the same value
  (±1 while a wave is in flight) — the partition-era turns finalize.
- Both drill turns are now on **node 3** (which was down when they were
  submitted):

```bash
curl -s http://127.0.0.1:8422/api/receipts \
  | jq --arg a "$T1" --arg b "$T2" 'map(select(.turn_hash == $a or .turn_hash == $b)) | length'
# expect 2
```

- **No double-apply**: each turn hash appears exactly once per node
  (`map(...) | length` is 1 per hash per node), and bob/carol balances moved
  by exactly 100 each.

**8.5 The tau-prefix-shift metric:**

```bash
for p in 8420 8421 8422; do
  echo -n ":$p  "; curl -s http://127.0.0.1:$p/metrics \
    | grep -E '^dregg_tau_prefix_shifts_total' || echo "dregg_tau_prefix_shifts_total 0"
done
```

Read against the 8.1 baseline. **Any increment is the soundness fix firing
live**: an honest late block (node 3's, or one held back by the partition)
sorted into the already-executed region, and the identity cursor absorbed it —
the 8.4 no-double-apply gate passing *alongside* a nonzero counter is the
whole point. A counter that stays 0 is also a pass (this heal merely extended
the order); the drill's hard gates are 8.4's.

Also confirm the loud log form on any node that incremented:

```bash
journalctl -u dregg-gateway -u dregg-node@2 -u dregg-node@3 --since -30min --no-pager \
  | grep -i "PREFIX SHIFTED"
```

## 9. Rollback

```bash
sudo systemctl stop dregg-node@2 dregg-node@3 dregg-gateway
sudo systemctl disable dregg-node@2 dregg-node@3
sudo rm /etc/systemd/system/dregg-gateway.service.d/federation.conf
sudo systemctl daemon-reload
# restore the archived solo chain:
sudo mv /opt/dregg-data /opt/dregg-data.federation.$(date +%Y%m%d%H%M%S)
sudo mv /opt/dregg-data.pre-federation.<TIMESTAMP> /opt/dregg-data
sudo systemctl start dregg-gateway
# restore the old FEDERATION_ID in /etc/dregg/discord-bot.env + restart the bot
```

## Appendix — resource budget (8 GB t4g.large)

| unit            | MemoryHigh | MemoryMax |
|-----------------|-----------:|----------:|
| dregg-gateway   | 3G (drop-in) | 3584M   |
| dregg-node@2    | 1536M      | 2G        |
| dregg-node@3    | 1536M      | 2G        |

Worst-case node sum 7.5G is intentionally tight: it relies on MemoryHigh
reclaim and assumes no concurrent `cargo build` during the drill. Build
before starting the federation (step 1), or build on persvati.
