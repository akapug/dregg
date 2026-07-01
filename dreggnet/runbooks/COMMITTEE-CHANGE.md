# COMMITTEE-CHANGE — add / remove a validator (the re-roll dance)

Changing **who** is in the consensus committee changes the `federation_id` (it is a
commitment to the sorted member set), so it is a **coordinated act across every
node**, not a unilateral join. This runbook is the mechanism we actually use today
— the **static genesis re-roll** — with the exact steps from the n=4
`{edge, node-a, node-a-rust, node-b}` roll, an honest flag that it is
disruptive, and the future live-epoch path that would replace it.

Read `FEDERATION.md` first for the consensus model + the quorum table; this is the
operational procedure that sits under §"How to add an operator".

## Which mechanism — the honest state

There are two ways the committee *can* change. **Only the first is exercised on the
live nodes today.**

| mechanism | what it is | state |
|---|---|---|
| **static re-roll** (this runbook) | regenerate genesis with the new member set → new `federation_id` → a **fresh chain** → distribute + restart all | **the recommended, auditable path today** |
| **live epoch transition** (`federation/src/epoch.rs` + `dregg-node propose-epoch-transition` → `POST /epoch/propose-transition`) | `propose/verify/apply_epoch_transition` advance the epoch + swap the member set **without re-genesis**; the chain keeps its height | **in the source, but VERIFY it is in the DEPLOYED binary before choosing it** (see below) |

> **⚠ Verify the deployed binary before reaching for the live-epoch path.** The
> source has had `propose-epoch-transition` for a while, but a *deployed* image can
> predate it. Confirm on the running node, not from the source tree:
>
> ```sh
> # CLI subcommand present?
> sudo docker compose exec -T dregg-node dregg-node propose-epoch-transition --help
> # daemon route present? (404 ⇒ the binary predates the wiring ⇒ use the re-roll)
> curl -s -o /dev/null -w '%{http_code}\n' -X POST -H 'Content-Type: application/json' \
>   -d '{"add":[],"remove":[]}' http://localhost:8420/epoch/propose-transition
> ```
>
> As of the `dregg-node:n4` image both the subcommand is **absent** and the route
> **404s** — so on today's live nodes the static re-roll below is the only path
> until a redeploy.

The re-roll is disruptive (a fresh chain) but **completely auditable**: every node
derives the same `federation_id` from the same `genesis.json`, so there is no
trust in a transition QC. The genesis economy is preserved (the same faucet/initial
allocation is re-seeded); accumulated chain history is **not** carried over.

## The static re-roll — step by step

This is the path we ran for the n=4 `{edge, node-a, node-a-rust, node-b}`
committee. The shape generalizes to any member set.

### 0. Reconcile the LIVE committee first — descriptor vs who is actually voting

**Do not trust your memory of the committee — read it off the running edge.** The
deployed descriptor and the set of nodes *actually finalizing* can differ (a
placeholder member you forgot, or a member that is in the descriptor but running a
different/solo genesis so it never votes). Reconcile before you touch anything:

```sh
# the committee DESCRIPTOR (who is supposed to be a member) — read genesis.json
# out of the running node. NOTE: the edge node-data is a DOCKER VOLUME, not a host
# path; reach it through the container (the host /opt/dreggnet/node-data does NOT exist):
sudo docker exec dreggnet-dregg-node-1 cat /data/genesis.json | \
  python3 -c 'import sys,json;g=json.load(sys.stdin);print(g["federation_id"],g["threshold"]);[print(v["name"],v["public_key"]) for v in g["validators"]]'

# who is ACTUALLY voting (the live finalizers) — the per-voter last-seen gauge:
curl -s http://localhost:8420/metrics | grep dregg_validator_last_seen_timestamp_seconds
# a descriptor member with NO voter line (or a stale timestamp) is NOT finalizing —
# it is running solo / on an old genesis. That gap is the real state, not the descriptor.

# a single node's own pubkey: /status → public_key, or, on the box:
dregg-node gen-validator-key --data-dir <data-dir> --json   # → { "public_key": "<hex>", ... }
```

> There is **no** `/api/node/identity` endpoint on the deployed node — use `/status`
> (`public_key`), `/metrics` (the voter gauge), or `gen-validator-key` as above.
>
> **⚠ Not every deployed build serves `/status`.** The node-a instances run a
> `dregg-recovery` build that serves **`/metrics` only** — `/status`, `/health`, and
> `/api/status` all return nothing/404 on it. On such a node read the committee health
> entirely from `/metrics`: `dregg_federation_peers_connected` (the peer count),
> `dregg_validator_last_seen_timestamp_seconds{voter=…}` (who is finalizing),
> `dregg_consensus_attested_total` (advances per finalized turn — the height proxy when
> `/status.latest_height` is unavailable), and `dregg_consensus_differential_divergence_total`.
> Don't assume `/status` exists; probe `/metrics` first on a node whose build you don't control.

**Then decide the new member set + collect public keys.** A validator identity is an
Ed25519 public key (`blake3(pubkey)` is its gossip id). Collect the **public** key
of every intended member — never the private `node.key`. For a member that lives on
**another operator's box** you cannot scp to it; coordinate its pubkey + the genesis
hand-off **over the builders chat** (see §"Cross-operator coordination" below).

At n=4 the threshold is **3** (`⌊2·4/3⌋+1`) and `f=1` — the committee survives one
fault. (The first live n=4 ran `{edge, node-a, node-a-rust, node-b-lean}` with
**node-a-rust a placeholder** — a second node-a instance held threshold-3 quorum
while the incoming operator's box staged; firing the *genuine* multi-operator n=4
swaps that placeholder out for the incoming `node-b-rust` — see §"Swapping a member".)

### 1. Generate the fresh genesis (all keys → the new federation_id)

Either roll a whole fresh committee centrally:

```sh
# generates node-0..3.key + genesis.json (validators[] = all 4 pubkeys);
# prints the new 4-member federation_id with threshold 3:
docker run --rm -v "$PWD/out:/out" dregg-node:staging \
  genesis --validators 4 --output /out
```

…or, to **keep each operator's existing `node.key`** (so independently-operated
boxes keep their identity), assemble `genesis.json` by hand from the four collected
public keys. Either way the output is one `genesis.json` whose `validators[]` is the
sorted set of all four pubkeys, and it commits to the new `federation_id` =
`blake3_derive(len || sorted_pubkeys || epoch=0)`.

> **Record the new `federation_id`** — the bot and any tooling that pins it must be
> updated (step 4). The genesis emitter prints it.

#### Swapping a member (add one, drop one) — `add-validator` only ADDS

The deployed binary has `add-validator` but **no `remove-validator`**. To *swap* a
member (e.g. drop the `node-a-rust` placeholder, add `node-b-rust`), build the new
genesis from the keep-set, then fold the incoming key in — `add-validator` recomputes
`federation_id` + `threshold` canonically from `validators[]`, so the intermediate
stale id between the two edits is harmless:

```sh
# in a scratch data dir, start from the CURRENT genesis, hand-edit validators[] to the
# KEEP set (delete the departing member's entry — here drop f86b9c63 / node-a-rust):
jq '.validators |= map(select(.public_key != "<DEPARTING_PUBKEY>"))' genesis.json > g.keep.json
mv g.keep.json <scratch>/genesis.json
# fold in the incoming member — this recomputes federation_id + threshold over the result
# and writes a content-named genesis-<fedid8>.json sibling to distribute:
dregg-node add-validator --data-dir <scratch> --pubkey <INCOMING_PUBKEY> --json
```

(`add-validator` reads/writes only `genesis.json`; it does not need a `node.key` in the
scratch dir. Run it with the **deployed** binary — e.g.
`sudo docker exec dreggnet-dregg-node-1 dregg-node add-validator …` — so the derivation
is byte-identical to what the running nodes recompute.)

> **`add-validator` synthesizes each new member's `xmss_root` deterministically from
> its Ed25519 pubkey.** You hand it only the 64-hex public key, yet the emitted
> `validators[]` entry carries an `xmss_root` — it is a deterministic function of the
> pubkey (re-running `add-validator` on the same key yields the identical root). So a
> **cross-operator** member agrees on the full descriptor (and thus `federation_id`)
> from the pubkey alone — you do **not** exchange XMSS key material over the chat. The
> only reconcile point: if a deployed build XMSS-*checks* the genesis root against the
> node's own local XMSS material at boot, that node must hold the matching material;
> the n=4→C2 path treats `xmss_root` as a deterministic descriptor field (Ed25519 is the
> consensus signer) and the incoming nodes seed clean. Verify on the incoming node, not
> from assumption.

### 2. Distribute the SAME genesis to every node

Every node's data dir gets the **identical** `genesis.json`; each keeps (or gets)
its **own** `node.key`. The committee — and thus `federation_id` — is now identical
across all four.

```sh
# node-a runs TWO instances on one box — each has its OWN data dir; both get the
# identical genesis.json (binary: /opt/dregg-recovery/target/release/dregg-node):
scp genesis.json dregg@node-a:/var/lib/dregg-node/data/genesis.json        # node-a  :8420
scp genesis.json dregg@node-a:/var/lib/dregg-node-rust/data/genesis.json   # node-a-rust :8421
# edge — the node-data is a DOCKER VOLUME, reached through the container (NOT a host
# path; /opt/dreggnet/node-data does not exist):
scp -i ~/.ssh/dreggnet-staging.pem genesis.json ubuntu@<EDGE_HOST>:/tmp/genesis.json
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST> \
  'sudo docker cp /tmp/genesis.json dreggnet-dregg-node-1:/data/genesis.json'
# (or: sudo cp /tmp/genesis.json /var/lib/docker/volumes/dreggnet_node-data/_data/genesis.json)
# a member on ANOTHER operator's box (node-b) is not scp-reachable — hand it the
# genesis over the builders chat (§"Cross-operator coordination").
```

> **This replaces the chain.** Distributing a new genesis is the disruptive step —
> the old chain's `dregg.redb` is from the *old* committee and no longer matches.
> **Back up each old `dregg.redb` first** (`cp -a data/dregg.redb data/dregg.redb.bak.$(date +%s)`)
> and clear it so the node seeds the new genesis cleanly (`DISASTER-RECOVERY.md`).

### 3. Restart all in full mode, with a bootstrap peer

Start each node `--federation-mode full` with one live bootstrap peer; gossip-of-
peers + the self-forming mesh fill in the rest (`NETWORK-TROUBLESHOOTING.md`):

```sh
dregg-node run --data-dir /data --bind <overlay-ip> --port 8420 --gossip-port 9420 \
  --key-file node.key --federation-mode full \
  --federation-peers 100.64.0.1:9420        # the edge as bootstrap seed
```

`--node-index` / `--federation-size` are **documentation only** — the committee
comes entirely from `genesis.json`.

> **Two instances on one box** (the `node-a-rust` case): a second node on the
> same host needs a **distinct gossip port** — run it on `9421/udp` (and a distinct
> API port) alongside the first on `9420`. Bind both to the overlay IP, not
> `0.0.0.0`. See `NETWORK-TROUBLESHOOTING.md` §"two instances, one box".
>
> **Supervision reality — node-a's nodes are orphan processes, not systemd.** The
> two node-a `dregg-node run` instances are launched detached (`setsid`, so they
> reparent to PID 1) — **not** under a systemd unit (the only dregg-ish unit on the box
> is `node-agent.service`, the compute backend, a different thing). Consequences for
> a re-roll: there is **no supervisor that auto-restarts them**, so after you kill an
> instance it stays down until you relaunch it by hand with the step-3 command (cd into
> the data dir so `--key-file node.key` resolves; redirect with `setsid nohup … < /dev/null
> > run.log 2>&1 &` so it survives your SSH session). **Retiring a placeholder is just
> `kill <pid>`** — there is no unit to disable, and you simply do not relaunch it. By
> contrast the **edge** node is `docker compose`-managed (`docker compose restart dregg-node`
> picks up a new `/data/genesis.json`).

> **⚠ Quorum-stall sequencing when you SWAP a member.** The new chain cannot finalize
> until **≥ threshold** of the *new* committee are live on the new genesis. If the
> swap drops a member you currently rely on for quorum (e.g. retiring the
> node-a-rust placeholder leaves only edge+node-a = 2 < threshold 3), and you cut
> the nodes you control over to the new genesis **before** the incoming operator's
> nodes are up on it, the new chain **idles** until they join. Sequence it so the
> incoming members come up on the new genesis **first (or simultaneously)**: bring up
> the incoming `node-b-*` nodes on the new genesis, confirm they are seeding it, then
> cut edge+node-a over and retire the placeholder. Quorum is reached the instant
> edge+node-a+(≥1 incoming) are all on the new genesis.

### 4. Re-point the bot's FEDERATION_ID

`FEDERATION_ID` is the executor signing domain and **must match the committee** the
bot submits to. After the re-roll it is the new committee `federation_id` (step 1).
Update it and restart the bot:

```sh
sudo -e /opt/dreggnet/.env                  # set FEDERATION_ID=<new hex>
cd /opt/dreggnet && sudo docker compose up -d dreggnet-discord-bot
sudo docker compose logs -f dreggnet-discord-bot   # logs the value it derives
```

If it is wrong, transfers fail with an **Ed25519 error**; the bot logs
`Set FEDERATION_ID=<hex> to match` at startup (`SECRETS.md`).

### 5. Verify the new committee

```sh
for ip in 100.64.0.1 100.64.0.2 …; do
  curl -s http://$ip:8420/status | jq '{federation_mode,federation_id,peer_count,dag_height}'
done
```

Confirm: every node shows `federation_mode: full`, the **same new
`federation_id`**, `peer_count` = n−1 (every other member), and they converge to the
same `dag_height`. Then verify each member is actually **voting**, not just connected
— the descriptor lists a member, the voter gauge proves it finalizes:

```sh
# every committee pubkey should have a FRESH last-seen line (a member that only gossips
# but runs an old genesis shows no/stale line — the exact gap §0 catches):
curl -s http://localhost:8420/metrics | grep dregg_validator_last_seen_timestamp_seconds
# the rust↔lean differential (node-b-rust is the rust producer): present and FLAT under
# a new turn ⇒ the two implementations agree; a rising counter ⇒ a real divergence:
curl -s http://localhost:8420/metrics | grep dregg_consensus_differential_divergence_total
```

Then run the cross-node finality check (`FEDERATION.md` §"Verify cross-node
finality"): submit a faucet transfer on one node, watch `latest_height` advance on
**all** members, and read the recipient cell back on another with an identical
`state_commitment`. Quorum is now `threshold`-of-n.

## Cross-operator coordination (members on another homelab)

When a committee member lives on **another operator's box** (e.g. an operator's `node-b-lean`
+ `node-b-rust` on `100.64.0.3`), you cannot scp the genesis or restart their nodes —
only the gossip overlay (UDP 9420/9421) traverses; their SSH/HTTP is not reachable from
the edge/node-a. Coordinate the change over the **builders chat** (the
`builders-dogfood` project, `#general`):

1. **Collect their pubkeys over the chat** — ask the other operator's agent to run
   `dregg-node gen-validator-key --data-dir <dir> --json` and paste the full 64-hex.
   `federation_id` is a commitment to the exact bytes, so a truncated `027e299c…` is
   not enough.
2. **Post the built `genesis-<fedid8>.json` + the new `federation_id`** to the chat.
3. **They** drop it into each of their data dirs, back up + clear the old `dregg.redb`,
   and start their nodes `--federation-mode full --federation-peers 100.64.0.1:9420`.
4. **Sequence per the quorum-stall warning** — confirm their nodes are up on the new
   genesis *before* you retire any placeholder you depend on for quorum.
5. Note: the other operator's agent may be **idle / on a polling loop** and is
   **cross-team**, so a direct mention/nudge may not wake it — post clearly and expect
   asynchronous pickup. Reciprocal SSH (`ssh operator@100.64.0.3`) is wired for the human
   operators but is not a substitute for their agent placing the genesis.

## Removing a validator

Same dance, smaller set. There is no `remove-validator`, so drop the departing entry
with the `jq` filter from §"Swapping a member" (`.validators |= map(select(...))`),
**then re-derive** `federation_id` + `threshold` over the smaller set — fold a
no-op/already-present add, or regenerate centrally — redistribute, restart the
remaining nodes, re-point the bot. The departing box simply stops running its node.
The threshold drops accordingly (recompute from the quorum table in `FEDERATION.md`
— e.g. n=4→n=3 drops threshold 3→2, `f` stays 1).

## ⚠ Honestly: this is disruptive — and the wanted improvement

The static re-roll **starts a fresh chain**: accumulated history does not carry
across the boundary (the genesis economy is preserved, the ledger history is not).
For a devnet that is acceptable and maximally auditable, but it is not how a
production network should add a node.

**The future: live epoch transition.** `federation/src/epoch.rs` already implements
the sound mechanism — the chain continues **across** a committee change with **no
re-genesis**:

- `propose_epoch_transition(config, joins, leaves)` computes the new member set +
  threshold and builds an `EpochTransition` (`to_epoch = current+1`).
- `verify_epoch_transition` is **attestation-gated**: the QC must carry ≥ the *old*
  threshold of votes, each Ed25519-verified against an *old-epoch* member key, and
  the new threshold must be correct for the resulting set.
- `apply_epoch_transition` advances the epoch, swaps the member set + threshold +
  `epoch_start_height`, and the height keeps advancing.

So a validator would be admitted only with a supermajority attestation from the
*current* committee — no unilateral join. The dynamic join path
(`MembershipAction::Join` over gossip + `--auto-approve-joins`,
`node/src/main.rs`) wires into this. **It is NOT yet exercised end-to-end on the
live nodes** — wiring + exercising it is the named TODO that would retire the
re-roll. Until then, the re-roll above is the path.

## See also

- FEDERATION.md — the consensus model, the quorum table, lace-merge, the cross-node
  finality verify, the §"How to add an operator" overview.
- OPERATOR-ONBOARDING.md — getting a new operator's box onto the mesh + a node up
  *before* the committee step.
- SECRETS.md — `FEDERATION_ID` matching, `node.key` rotation triggers a re-roll.
- KEY-MANAGEMENT.md — the validator key lifecycle the re-roll consumes.
- NETWORK-TROUBLESHOOTING.md — bootstrap peers, two-instances-one-box gossip ports.
- DISASTER-RECOVERY.md — backing up + clearing the old chain's `dregg.redb`.
