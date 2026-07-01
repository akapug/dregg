# DreggNet consensus federation

This is the consensus backbone: the set of `dregg-node` daemons that gossip a
shared blocklace (Cordial-Miners) DAG over the headscale overlay and finalize
turns by BFT quorum. The overlay join (getting a box onto the private WireGuard
mesh) is in `FABRIC-JOIN.md`; **this** file is the layer above it — how those
boxes form one *federation* with a shared identity and a quorum.

The one-line model: a federation is a fixed **committee** of validator public
keys. The `federation_id` is a commitment to that committee (`blake3_derive(len ||
sorted_pubkeys || epoch)`), every node derives it identically from its
`genesis.json`, and a turn is *final* only once a supermajority of the committee
has signed a finalization vote for the block that carries it.

## Topology (target: 5 nodes)

| role | host | overlay addr | api | gossip | node-index |
|------|------|--------------|-----|--------|------------|
| edge      | AWS `<EDGE_HOST>` | `100.64.0.1` | `:8420` | `9420/udp` | 0 |
| node-a    | the home compute node | `100.64.0.2` | `:8420` | `9420/udp` | 1 |
| node-b    | an operator | `100.64.0.x` | `:8420` | `9420/udp` | 2 |
| node-c    | an operator | `100.64.0.y` | `:8420` | `9420/udp` | 3 |
| node-d    | an operator | `100.64.0.z` | `:8420` | `9420/udp` | 4 |

- **API** `:8420` (tcp) — the localhost/overlay HTTP surface (`/status`,
  `/api/cell/{id}`, `/api/receipts`, faucet, turn submission).
- **Gossip** `:9420/**udp**` — the blocklace QUIC transport. It is **UDP** (quinn);
  a tcp-only port mapping will silently fail to peer. On the edge (docker bridge)
  the published port must be `"9420:9420/udp"`. On node-a the node runs with
  `network_mode: host`, so it binds the overlay interface directly.
- Nodes peer by **overlay address**: each is started with
  `--federation-peers <other-overlay-ip>:9420` (comma-separated for >1 peer). The
  gossip-of-peers exchange then shares the rest of the verified committee mesh, so
  a new node only needs *one* live bootstrap peer in its `--federation-peers`.

### Current live state (2 of 5)

**Federation id:** `<FEDERATION_ID>`
(committee = {edge, node-a}, epoch 0, threshold 2).

| node | public key |
|------|------------|
| edge (node-0)     | `<NODE0_PUBKEY>` |
| node-a (node-1)   | `<NODE1_PUBKEY>` |

Both run `--federation-mode full` (BFT quorum, not solo), peered over the overlay,
`consensus_live: true` with a real peer (`peer_count: 1` each, not solo). `/status`
on both reports the same `dag_height` / `block_count` / `latest_height`.

## Quorum and what actually resists an attacker

The threshold is the strict blocklace supermajority `⌊2n/3⌋ + 1`, and the
Byzantine fault tolerance is `f = n − threshold`:

| n | threshold (votes to finalize) | f (faulty nodes tolerated) |
|---|---|---|
| 1 | 1 | 0 — solo, no consensus |
| **2** | **2** | **0 — both must be online and honest** |
| 3 | 3 | 0 |
| 4 | 3 | 1 |
| **5** | **4** | **1 — survives one down/Byzantine node** |

**Honest state of the 2-node federation.** It is a *real* federation — two
independent boxes, full BFT mode, finalizing by signed quorum over the overlay —
but at n=2 the threshold is 2, so `f=0`: there is **no fault tolerance**. Both
nodes must be online for the chain to make progress (if one is down, the other
cannot reach quorum and no new turn finalizes), and it does not yet resist a
Byzantine member. That is exactly why the target is 5: n=5 gives threshold 4 and
`f=1`, so the chain keeps finalizing and stays correct even with one node down or
adversarial. "Resists attackers" begins at the point where independent operators
hold enough of the committee that no single party controls `n − f` keys — i.e.
an independent operator's 3 homelab nodes being **independently operated** is the
load-bearing fact, not just the node count.

## Proof of cross-node finality (verified 2026-06-28)

A turn submitted on **one** node finalizes and becomes visible on the **other**
over the overlay:

1. Submitted a faucet Transfer on the **edge** node (`POST :8420/api/faucet`,
   amount 100 → a fresh recipient cell). Edge returned
   `turn_hash = 42dea554c67818a919a173757be0faf9590bd6027a0adb563dbdeaf4bb57046a`.
2. The blocklace gossiped the turn-bearing block to node-a; both nodes signed
   finalization votes (threshold 2 — **both** were required), and the verified
   finality gate executed the turn.
3. The recipient cell `aaaa…aaaa` then read `balance: 100` on **both** nodes with
   the **identical** `state_commitment`
   `ea4321e41be41501af0deeab2988ed4b6733acd3862984e6b93e18bb2161ea70`, and
   node-a's `/api/receipts` carried the same `turn_hash` with `finality: "final"`
   and `post_state = 6e69f6ead1ce578c2e2a375dcb44495368a55bbea30641d05c569d532c584020`
   — matching the edge receipt for that turn. Both advanced to `latest_height: 1`
   (the attested-root height) in lockstep.

The recipient cell never existed before the turn and node-a never received the
faucet HTTP call: it was provisioned on node-a purely from the finalized turn
data by the same executor, which is the cross-node-deterministic-finality property
we wanted.

## How a new node (an operator's homelab) joins to reach the 5-quorum

Adding a node is **two** steps — the overlay (membership of the WireGuard mesh)
and the federation (membership of the consensus committee). The overlay step is
`FABRIC-JOIN.md`. The committee step is below.

Because `federation_id` is a commitment to the committee public keys, **adding
members changes the federation id** — so growing the committee is a coordinated
re-roll, not a unilateral act. For a devnet the simplest honest path is a
static committee re-roll:

1. **Overlay.** On each homelab box: `tailscale up --login-server=… --authkey=…`
   (FABRIC-JOIN.md). Note its overlay `100.64.0.x`.
2. **Key.** Generate a node keypair on each box (or generate all five centrally):
   `docker run --rm -v $PWD/out:/out dregg-node:staging genesis --validators 5
   --output /out` produces `node-0..4.key` + a `genesis.json` whose `validators[]`
   lists all five public keys, and prints the new 5-member `federation_id` with
   `threshold 4`. (Or collect each operator's `public_key` from
   `GET :8420/api/node/identity` and assemble the committee by hand.)
3. **Distribute.** Put the **same** `genesis.json` on every node's data dir, and
   give each node its own `node.key`. The committee (and thus `federation_id`) is
   now identical across all five.
4. **Peer + restart.** Start each node `--federation-mode full
   --federation-peers <edge>:9420[,<node-a>:9420]` (one live bootstrap peer is
   enough; gossip-of-peers fills in the rest). `--node-index`/`--federation-size`
   are documentation only — the committee comes entirely from `genesis.json`.
5. **Verify.** Each node's `/status` shows `federation_mode: full`,
   `peer_count ≥ 1`, the new 5-member `federation_id`, and they converge to the
   same `dag_height`. Quorum is now 4-of-5 (`f=1`).

The node also has a dynamic-join path (`MembershipAction::Join` over gossip +
committee-epoch rotation, gated by `--auto-approve-joins`), which lets a node be
admitted without a full re-roll; for a small devnet the static re-roll above is
simpler and auditable, and is the recommended path until the join-vote flow is
exercised end-to-end.

## Run / operate

Each node runs the prebuilt `dregg-node:staging` linux/amd64 image (it links a
host-native Lean archive and cannot be cross-compiled; ship it with `docker save |
ssh … docker load`). Both deployments use `restart: unless-stopped`, so dockerd
brings the node back when the daemon starts on boot.

**node-a** — `/var/lib/dregg-node/docker-compose.yml`, host networking:

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

The node-agent compute on `:8021` is a **separate** service and is untouched
by the node.

**edge** — `/opt/dreggnet/docker-compose.yml`, `dregg-node` service on the compose
bridge with `--federation-mode full --federation-peers 100.64.0.2:9420
--enable-faucet` and the gossip port published as `"9420:9420/udp"`.

## Reboot-survivability — honest state

- **Process / daemon layer: in place.** Both nodes use `restart: unless-stopped`
  and dockerd starts on boot, so a host reboot restarts the container.
- **Durable-state recovery: a node-source caveat before the first ledger
  checkpoint.** A node that has **finalized at least one turn but not yet written
  its first ledger checkpoint** (the ledger checkpoint interval is a hard-coded
  100 finalized heights — `node/src/blocklace_sync.rs::LEDGER_CHECKPOINT_INTERVAL`)
  fails its recovery-convergence guard on restart and refuses to start
  (`STORE INTEGRITY EVENT … reconstructed ledger root does not match the durably
  recorded finalized root`). Root cause: recovery rebuilds the ledger from the
  last checkpoint (none yet → empty) plus the per-turn commit-log overlay, but the
  genesis cells are re-seeded *after* that check (`node/src/state.rs` recovery vs
  the genesis-seed pass in `node/src/main.rs`), so the reconstructed root omits the
  untouched genesis cells and the guard fail-closes. This is fail-*closed* (it
  refuses to serve a divergent ledger; it does not serve wrong state) and it
  resolves on its own once the chain passes height 100 (a real checkpoint then
  contains the genesis cells and recovery converges).
- **Operational recovery today (verified):** a committee node rejoins by
  catch-up — clear its `dregg.redb` (keep `genesis.json` + `node.key`) and
  restart; it re-seeds genesis, re-peers, and replays the finalized DAG from the
  quorum, re-deriving the exact finalized state (confirmed: node-a was wiped,
  rejoined, and re-finalized `turn 42dea554…` with the recipient cell back at
  `balance 100`). The clean fix is in the node source (seed genesis before the
  convergence check, or make the ledger-checkpoint interval configurable so a
  devnet checkpoints at height 0/1); it is out of scope for this deploy lane.
