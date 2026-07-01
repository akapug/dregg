# DISASTER-RECOVERY — lost keys, corruption, restore, re-sync

The worst-case runbook: a validator key is gone, a node's store is corrupt, a box
is lost, or a node's ledger has diverged from the committee. For each: what is
actually recoverable, what is not, and the exact procedure — grounded in the
recoveries we have run (the node-a wipe-and-re-sync, the genesis-baseline fix).

The load-bearing fact that makes recovery sound: the blocklace is a **proven CRDT**
(`FEDERATION.md` §lace-merge). A node rejoins by **pulling the finalized DAG from
the quorum and unioning it** — it re-derives the exact finalized state by replaying
the merged DAG. So as long as **quorum is live**, a single node's local store is
disposable: wipe it, restart, re-sync.

> **Golden rule: BACK UP before you destroy.** `cp -a` the store and the key dir
> before any `rm`. Never wipe node-data without a copy. Recovery is a re-derivation;
> a backup is your only undo if the re-derivation surprises you.

---

## A. Lost / compromised validator key (`node.key`)

`node.key` is a node's Ed25519 identity. Its **public** key is in `genesis.json`
and defines that validator's slot in the committee (and thus contributes to
`federation_id`). Losing or rotating it is **not** a local-only fix.

**If `node.key` is LOST (box died, dir wiped, no backup):**

1. The node's old identity is gone. You cannot resurrect *that* validator slot
   without the private key — the committee still expects signatures from the old
   public key.
2. **This forces a committee change.** Generate a fresh `node.key` for the box
   (`KEY-MANAGEMENT.md` §gen) and run the **static re-roll** (`COMMITTEE-CHANGE.md`)
   with the new public key in place of the old: new `genesis.json`, new
   `federation_id`, distribute, restart all, re-point the bot.
3. While the box is keyless it can still run as a **catch-up / compute**
   participant (it pulls + unions the finalized DAG) — it just is not a *voting*
   member until the re-roll lands its new key.

**If `node.key` is COMPROMISED (leaked / on a shared surface):**

Treat it as burned — scrubbing is not enough once it has left the box. Generate a
fresh key and run the re-roll to **evict the old public key** from the committee
(`COMMITTEE-CHANGE.md` §removing a validator, then re-add the new key). Rotating
`node.key` always changes the public key → changes `federation_id` → needs a
re-roll + a bot `FEDERATION_ID` update (`SECRETS.md`).

> **Have a backup?** If you backed up `node.key` (KEY-MANAGEMENT.md §backup), this
> is a non-event: restore the key file into the data dir and restart — the identity
> is intact, no re-roll needed. **This is why `node.key` backup matters.**

---

## B. Node-data corruption (the STORE INTEGRITY event)

**Symptom.** On restart the node fail-closes:
`STORE INTEGRITY EVENT … reconstructed ledger root does not match the durably
recorded finalized root`, and crash-loops under `restart: unless-stopped`.

This is **fail-CLOSED by design** — the node refuses to serve a divergent ledger;
it never serves wrong state. Two cases (full triage tree:
`INCIDENT-RESPONSE.md` §4):

- **Recoverable order-bug** (sub-checkpoint restart or a SIGKILL mid-checkpoint).
  Fixed in source by `breadstuffs` commit **`1a61dc16d`** (genesis baseline first,
  overlay second). On an image carrying it, a clean restart auto-recovers. On an
  older image, use the wipe-and-re-sync below.
- **Real corruption** (bad blocks / disk damage). Same re-sync path; the cause is
  the store, not the order.

**Procedure — wipe the local ledger, keep identity + genesis, re-sync:**

```sh
cd ~/dregg-node            # or /opt/dreggnet on the edge
docker compose stop dregg-node          # graceful SIGTERM — do NOT docker kill

cp -a data/dregg.redb data/dregg.redb.bak.$(date +%s)   # 1. BACK UP first
rm -f data/dregg.redb                                    # 2. clear ONLY the ledger db
#    KEEP genesis.json + node.key — they are identity + committee, not ledger

docker compose up -d dregg-node          # 3. re-seeds genesis, re-peers, replays
docker compose logs -f dregg-node        #    the finalized DAG from the quorum
curl -s http://localhost:8420/status     # → converges to the quorum's dag_height
```

This is exactly what we did to **node-a**: wiped, rejoined, re-finalized
`turn 42dea554…` with the recipient cell back at `balance 100` and the **identical
state commitment** — proof the re-derivation is exact.

> **Re-sync needs the quorum live.** At n=2 (`f=0`) the *other* node must be up for
> catch-up to converge. Bring the node with the good store up first. If both stores
> are bad, restore one from backup (§D) before re-syncing the other.

---

## C. A divergent-ledger node (the node-a re-sync)

**Symptom.** A node is up and serving, but its `dag_height` / `state_commitment`
**disagrees with the rest of the committee** and does not converge — it forked off
a different ledger (e.g. it ran solo, or against a stale/old genesis, and
accumulated state the committee never finalized).

**The fix is the same wipe-and-re-sync as §B** — but the trigger is divergence, not
a fail-closed store. **Discard the local ledger and re-sync from the committee:**

```sh
docker compose stop dregg-node
cp -a data/dregg.redb data/dregg.redb.bak.$(date +%s)   # back up the divergent ledger
rm -f data/dregg.redb                                    # discard it
docker compose up -d dregg-node                          # re-derive from the quorum
# verify it now AGREES — same federation_id, converging dag_height + state_commitment:
curl -s http://localhost:8420/status | jq '{federation_id,dag_height}'
```

This is sound because the committee's finalized DAG is authoritative and the
re-joining node **unions it in** rather than imposing its fork (lace-merge). The
node's divergent history is **dropped** — that is the point: the committee's
finalized order wins.

> **First confirm it is the LOCAL node that diverged**, not the committee. If a
> *majority* of nodes agree and one disagrees → wipe the one. If they **all**
> disagree pairwise, you have a deeper consensus problem (possibly a rust↔lean
> divergence — `INCIDENT-RESPONSE.md` §3) — do **not** start wiping; capture state
> and escalate. Also check it is not just the old-genesis case (a node carrying a
> *different* `federation_id` is on a different committee, not diverged within one).

---

## D. Restore a node from backup

If you have a backup of the data dir (KEY-MANAGEMENT.md recommends backing up
`node.key` + `genesis.json` at minimum):

```sh
docker compose stop dregg-node
# restore the identity + committee (always safe):
cp -a backup/node.key      data/node.key
cp -a backup/genesis.json  data/genesis.json
# the ledger db is OPTIONAL to restore — if quorum is live, skip it and let the
# node re-sync fresh (cleaner than trusting an old snapshot):
#   cp -a backup/dregg.redb data/dregg.redb     # only if quorum is NOT available
docker compose up -d dregg-node
curl -s http://localhost:8420/status
```

Prefer **restore identity, re-sync ledger** over restoring an old `dregg.redb` —
the re-sync gives you the *current* finalized state, an old snapshot gives you a
lagging one you'd have to catch up anyway.

---

## E. Genesis re-seed (whole-committee disaster)

If the **whole committee** is lost (every node's store gone, no good ledger
anywhere) but the **keys survive**, the chain restarts from genesis with the same
committee:

1. Restore (or regenerate) each node's `node.key`.
2. Put the **same** `genesis.json` on every node (back from backup, or
   re-assembled from the public keys — `COMMITTEE-CHANGE.md` §1; the same key set →
   the same `federation_id`).
3. Clear every `dregg.redb` (no good ledger exists) and start all
   `--federation-mode full` with a bootstrap peer.
4. The chain seeds the genesis economy and finalizes from height 0 again. Re-point
   the bot's `FEDERATION_ID` if the committee changed.

This is the genesis economy being preserved while accumulated history is lost — the
same property as a re-roll, applied to a total-loss recovery.

---

## What is NOT recoverable

- **A finalized turn's history after a re-seed/re-roll.** A fresh genesis is a fresh
  chain; pre-genesis history does not carry across. The genesis *economy* is
  preserved, accumulated ledger history is not (`COMMITTEE-CHANGE.md`).
- **A validator slot whose private `node.key` is lost with no backup** — that
  *specific* identity is gone; recovery is a re-roll with a new key (§A).
- **Money already lost to a real bridge conservation breach** — that is a security
  incident, not a recovery (`INCIDENT-RESPONSE.md` §5).

## See also

- INCIDENT-RESPONSE.md — the STORE-INTEGRITY triage tree + divergence diagnosis.
- NODE-OPS.md — the canonical wipe-and-re-sync recovery + graceful shutdown.
- COMMITTEE-CHANGE.md — the re-roll a lost/rotated key forces.
- KEY-MANAGEMENT.md — backing up `node.key`, what backup turns a disaster into a
  non-event.
- FEDERATION.md — lace-merge: why pulling + unioning the quorum's DAG is exact.
