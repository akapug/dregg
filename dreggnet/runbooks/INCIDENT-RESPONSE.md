# INCIDENT-RESPONSE — first-responder diagnostic trees

The page fired (or something looks wrong) and you are the first responder. This is
the **triage** runbook: symptom → the exact diagnostic commands → the likely cause
→ the fix → when to escalate. It is the doing-companion to `docs/MONITORING.md`
(what each alert *means* + the thresholds) — that doc defines the signals; this one
walks you from a red tile to a green one.

Every tree below is grounded in a failure we **actually hit or can hit on this
topology** (2-of-5 federation, edge + node-a over the headscale overlay). Read
the live state in `FEDERATION.md` before assuming counts.

## The 30-second orient

Before diving into a tree, take the whole-cloud snapshot — most incidents are
diagnosable from the rollup plus two `/status` reads:

```sh
# the ops rollup (the single pane — OPS-DASHBOARD.md):
curl -fsS -u admin:<pw> https://ops.dreggnet.example.com/api/health | jq
curl -fsS -u admin:<pw> https://ops.dreggnet.example.com/api/alerts | jq  # active alerts only

# each node's own view (over the overlay — no auth needed node-to-node):
curl -s http://100.64.0.1:8420/status | jq   # edge
curl -s http://100.64.0.2:8420/status | jq   # node-a
#   → { federation_mode, peer_count, dag_height, latest_height, block_count,
#       consensus_live, healthy, federation_id }
```

The four fields that resolve most incidents: **`peer_count`** (is the mesh
formed?), **`federation_mode`** (`full` vs `solo`), **`dag_height`** on each node
(do they agree?), and **`consensus_live`** (is quorum finalizing?).

> **No `dregg-node peers` CLI yet** (honest TODO). There is no command that prints
> the peer table; read **`peer_count`** from each `/status`, and
> `dregg_federation_peers_connected` from `:8420/metrics` (the one populated native
> gauge — `node/src/metrics.rs`). Per-peer detail comes from the node logs.

---

## 1. "The network won't finalize new turns"

**Symptom.** Turns submit but never reach `finality: "final"`; `dag_height` is
flat across refreshes; ops pages **`node_not_finalizing`** / **`NodeNotFinalizing`**
(`consensus_live == 0` or `node_finalizing == 0` for 5m).

**Diagnose — three checks, in order:**

```sh
# (a) is quorum even possible? read every committee member's mode + peers:
for ip in 100.64.0.1 100.64.0.2; do
  echo "== $ip =="; curl -s http://$ip:8420/status | jq '{federation_mode,peer_count,consensus_live,dag_height}'
done
```

- **(a) A member is DOWN → running below quorum.** At n=2 the threshold is **2**
  and `f=0` (`FEDERATION.md` quorum table): **both** nodes must be up to finalize.
  If one `/status` is unreachable or its `peer_count:0`, the live node **correctly
  refuses to finalize** — it cannot reach the supermajority. *This is not a bug; it
  is BFT safety.* The chain stalls rather than finalize without quorum.
  **Fix:** bring the missing member back up (`NODE-OPS.md` restart; if its store is
  wedged, the `DISASTER-RECOVERY.md` re-sync). Finalization resumes the moment
  quorum is reachable again.

- **(b) Both up but `peer_count:0` → the mesh did not form.** Each node is up and
  in `full` mode but they never connected, so neither sees the other's blocks or
  votes. Go to **tree 2** (peer won't mesh). The tell: both `dag_height` advance
  *independently* (each only sees its own turns) rather than converging.

- **(c) `federation_mode` is `solo` unexpectedly.** A node started without
  `--federation-mode full` runs as n=1 (no consensus). It "finalizes" alone, but it
  is **not** the committee. Restart it with `--federation-mode full` (`NODE-OPS.md`).

**Watch for `dag_height` DIVERGENCE.** If the two nodes show *different*
`dag_height` that do not converge, that is the mesh-not-formed case (b), or — if
they are peered — a finality disagreement (go to **tree 3**).

**Escalate** if quorum is reachable (both up, peered, `full`) and it still won't
finalize: capture `docker compose logs --tail=200 dregg-node` from both, check
`consensus_live` and the finality-latency panel (`dregg_consensus_finality_latency_seconds`),
and treat it as a consensus bug.

---

## 2. "A peer won't mesh / `peer_count` stuck at 0"

**Symptom.** A node is up and `--federation-mode full`, but `peer_count` stays `0`
(or `dregg_federation_peers_connected == 0`); it never sees the other members'
blocks.

**Cause (the self-mesh issue).** The gossip layer historically only formed links
on **outbound dials** — a node that was never given a peer to dial, and was never
dialed *by* a configured peer, sat alone even on a healthy overlay. A node booted
with no `--federation-peers` would not self-form the mesh.

**The fix (landed) — self-forming mesh.** `node/src/blocklace_sync.rs` now
self-advertises its reachable listen endpoint in the authenticated peer exchange:
a node booted with a **single** bootstrap peer signs + broadcasts its address, the
peer records the `identity → addr` binding and re-shares it via gossip-of-peers, so
the whole committee learns every member's endpoint from one seed. The log line to
confirm it is active:

```
gossip self-advertisement enabled (self-forming mesh)
```

**Diagnose:**

```sh
# is self-advertisement on? (it is OFF for a non-routable bind — see below)
docker compose logs dregg-node | grep -i "self-advertisement\|self-forming"

# is a bootstrap peer configured + resolvable? an unresolvable peer logs LOUDLY:
docker compose logs dregg-node | grep -iE "peer|bootstrap|resolve|gossip"
```

**The two real causes + fixes:**

1. **No bootstrap seed at all.** Give the node one live peer to dial — the
   `--federation-peers <edge>:9420` workaround. One peer is enough; gossip-of-peers
   fills in the rest. This is still the recommended explicit bootstrap even with the
   self-mesh fix (it makes the seed deterministic):

   ```sh
   # in the node's compose command:
   run … --federation-mode full --federation-peers 100.64.0.1:9420
   ```

2. **Bound to `0.0.0.0` or loopback → self-advertisement silently OFF.** A
   non-routable bind yields no advertisable address, so the node does not announce
   itself and peers cannot learn to dial it back. **Bind to the overlay IP**
   (`100.64.0.x`), not `0.0.0.0`/`127.0.0.1` — this is the MESH-2 scoping. See
   `NETWORK-TROUBLESHOOTING.md` for the full bind story.

**The other silent killer: the UDP gotcha.** Gossip is **`9420/udp`**
(QUIC/quinn). A **tcp-only** port mapping silently fails to peer — `peer_count`
stays 0 with no error. On a docker bridge publish `"9420:9420/udp"`; with host
networking it binds the interface directly (`NODE-OPS.md`). Verify reachability:

```sh
sudo tailscale ping 100.64.0.2          # overlay path works? (MESH.md)
# UDP/9420 reachability — nc -u is a coarse probe (no QUIC handshake), but a hard
# refusal here means the port/ACL is wrong:
nc -uvz 100.64.0.2 9420
```

**Escalate** if the overlay pings, the bind is the overlay IP, `9420/udp` is
published, a bootstrap peer is set + resolvable, and it still won't mesh — capture
both nodes' gossip logs.

---

## 3. "rust↔lean divergence alert fired"

**Symptom.** Ops pages **`consensus_divergence`** / **`ConsensusDivergence`** —
`dregg_consensus_differential_divergence_total > 0` (or the ops-reported
`dreggnet_ops_consensus_divergence > 0`). **This is a real consensus-bug signal —
treat it as page-now, never ignore.**

**What it means.** On a Lean-shadowed node the verified Lean rule
(`metatheory/Dregg2/Distributed/BlocklaceFinality.lean::tauOrder`) and the Rust
`ordering::tau` finalized **different** `(creator, seq)` sets for the same poll.
The finality gate (`node/src/finality_gate.rs`) **REFUSES** the disputed block (it
is not sliced to the executor) and records the divergence — **the verified Lean
rule wins, so safety holds** — but the two impls disagreeing is a bug:
either a Rust-side ordering bug or a **stale/mismatched Lean archive** in the
deployed image.

**Diagnose:**

```sh
# 1. WHICH node + how many divergences (the counter is monotonic):
curl -s http://100.64.0.1:8420/metrics | grep dregg_consensus_differential_divergence
curl -s http://100.64.0.2:8420/metrics | grep dregg_consensus_differential_divergence

# 2. capture the disagreeing finalization — the gate logs the (creator,seq) it
#    refused and the two orders. Grab a wide window around the first divergence:
docker compose logs --tail=500 dregg-node | grep -iE "diverg|finality|gate|refus|tau"
```

**Likely cause + fix:**

- **Stale Lean archive** (most likely): the deployed node image's `libdregg_lean.a`
  is from an older `breadstuffs` HEAD than the Rust `ordering::tau` it links
  against. **Fix:** rebuild the node image from a clean HEAD on the Lean builder and
  redeploy (`UPGRADE.md` — coordinate so the whole committee runs the same archive).
- **A genuine Rust ordering bug**: if the archive matches HEAD and they still
  disagree, capture the exact lace + the disagreeing order and file it against the
  substrate (`~/dev/breadstuffs`) — this is the cross-check doing its job.

**Note the fail-open case is the inverse risk.** A node built **without** the Lean
archive (rust-only) **fails OPEN** to the un-gated Rust order with a loud warning +
a divergence record — it keeps running but the verified gate is *not* active there.
Goal: every consensus member runs lean-shadowed so a divergence is caught
everywhere (`FEDERATION.md` §"the rust/lean finality mix"; an open TODO).

**Escalate:** any non-zero divergence that you cannot immediately attribute to a
known stale-archive redeploy — this must not sit unattended.

---

## 4. "STORE INTEGRITY EVENT on node restart"

**Symptom.** On restart a node fail-closes and refuses to start:

```
STORE INTEGRITY EVENT … reconstructed ledger root does not match the durably
recorded finalized root
```

Under `restart: unless-stopped` it then **crash-loops visibly** and ops pages
`node_down` / `node_not_finalizing`.

**This is fail-CLOSED, by design.** The node **refuses to serve a divergent
ledger** — it does **not** serve wrong state. So the worst case is a node that is
down loudly, never one that lies.

**First: is it the recoverable order-bug, or real corruption?**

- **Recoverable (the common case).** A node that finalized ≥1 turn but had not yet
  written its first ledger checkpoint (interval `LEDGER_CHECKPOINT_INTERVAL = 100`)
  hit a recovery-order bug: recovery rebuilt from an empty checkpoint + the commit
  overlay but re-seeded genesis cells *after* the convergence check, so the root
  omitted the untouched genesis cells. Two triggers: a **sub-checkpoint restart**
  (before height 100) or a **SIGKILL mid-checkpoint** (a `docker kill`, an OOM-kill
  — see `HARDWARE-NODE.md` earlyoom — or a redeploy that didn't grace the
  SIGTERM). **The fix** is `breadstuffs` commit **`1a61dc16d`** *"recover in the
  sound order — genesis baseline first, overlay second"*: once every deployed image
  carries it, a sub-checkpoint restart recovers cleanly with no intervention, and
  the chain self-resolves past height 100 regardless.

- **Real corruption.** A store that genuinely cannot be reconstructed (bad blocks,
  disk damage) also fail-closes here. The recovery is the same re-sync path — but
  the cause is the store, not the order bug.

**Recovery procedure (the fallback until every image has `1a61dc16d`):**

```sh
cd ~/dregg-node            # or /opt/dreggnet on the edge
docker compose stop dregg-node          # graceful SIGTERM (do NOT docker kill)

# 1. BACK UP node-data FIRST — never destroy before you have a copy:
cp -a data/dregg.redb data/dregg.redb.bak.$(date +%s)

# 2. clear ONLY the ledger db; KEEP genesis.json + node.key:
rm -f data/dregg.redb

# 3. restart — re-seeds genesis, re-peers, replays the finalized DAG from the
#    quorum (lace-merge, FEDERATION.md), re-deriving the exact finalized state:
docker compose up -d dregg-node
curl -s http://localhost:8420/status     # converges to the quorum's dag_height
```

> **Catch-up needs the quorum live.** At n=2 (`f=0`) the *other* node must be up
> for the wiped node to re-derive the recorded finalized root. If both are down,
> bring the one with the good store up first.

**Prevention.** Always stop with `docker compose stop` (clean SIGTERM →
checkpoint); the edge compose gives `stop_grace_period: 45s` to flush. Never
`docker kill`. Bound heavy builds so earlyoom does not SIGKILL a running node
(`NODE-OPS.md`, `HARDWARE-NODE.md`).

**Escalate:** if the re-synced node *still* fail-closes after a clean wipe + quorum
catch-up, the divergence is upstream (a bad finalized block in the quorum) — stop
and capture both nodes' state; do not keep wiping. Full recovery detail:
`DISASTER-RECOVERY.md`.

---

## 5. "Bridge conservation breach" (PAGE)

**Symptom.** Ops pages **`bridge_conservation_breach`** /
**`BridgeConservationBreach`** — `dreggnet_ops_bridge_conservation_ok == 0`: more
mirror asset (`live_supply`) circulates than is backed (`currently_locked` /
`total_verified_payments`). The conservation invariant is the bridge's **core
safety property**; a breach is a critical money bug. (`bridge_double_mint` — a
relayer reporting a *successful* double-mint — is equivalent by construction.)

> **Stripe rail deep dive:** the per-rail Stripe diagnostics (signature-fail,
> duplicate-mint, refund/dispute reconciliation, receiver-down) live in
> [STRIPE-OPS.md](STRIPE-OPS.md) §3. This tree is the cross-rail first-responder
> protocol; STRIPE-OPS is the Stripe-specific companion.

**Scope today (honest).** `dregg-bridge` is **library-only on `main`** — there is
no relayer daemon and `OPS_BRIDGE_URL` is unset, so `bridge_conservation_ok` reads
**null / un-observed**, never a false all-clear (`docs/MONITORING.md` §2b). This
alert can only fire once a relayer is wired. The red-team criticals BR-2/BR-3 (the
forgeable lock evidence + the once-vacuous conservation) are **fixed** in the
bridge crate (`docs/RED-TEAM-FINDINGS.md`); a breach firing on a real relayer would
mean a kernel/relayer bug, not a known-latent issue.

**Respond — STOP MINTING FIRST, then investigate:**

```sh
# 1. HALT the mint side. If a relayer daemon is running, stop it so no further
#    mint can draw against unbacked locks:
#    (relayer is operator-run; stop its process/unit — there is no bridge daemon
#     in the staging compose today.)

# 2. capture the evidence — the mint receipts vs the locked side. Bridge mints
#    land as real kernel effects on the node's committed-event feed:
curl -s http://100.64.0.1:8420/api/events | jq '[.[] | select(.kind|test("mint|bridgemint|burn"))]'
#    (honest gap: the events feed carries a mint's KIND but not its amount; burn
#     summaries DO carry amount+asset — docs/MONITORING.md §2b.)

# 3. if a relayer status surface exists, snapshot its MirrorState conservation
#    quantities (currently_locked / total_verified_payments vs live_supply):
curl -s "$OPS_BRIDGE_URL/status" | jq    # when OPS_BRIDGE_URL is configured
```

3. **Compare** the minted side against the on-chain locks (the Solana vault PDA /
   the Stripe verified payments). A genuine `live_supply > backing` confirms the
   breach. The committed `note_nullifiers` gate makes a double-mint *supposed to be*
   impossible — a real firing is a kernel/relayer bug.

**Escalate immediately** — a real conservation breach is money loss. Freeze the
relayer, preserve all receipts + on-chain state, and treat it as a CRITICAL
security incident (loop ember; see `docs/RED-TEAM-FINDINGS.md` for the bridge
threat model).

---

## Escalation summary

| Incident | First move | Page-worthy? | Escalate when |
|---|---|---|---|
| won't finalize | check quorum reachability | yes (`node_not_finalizing`) | quorum reachable but stalled |
| won't mesh | check bind + bootstrap + UDP | no (degraded) | all correct, still 0 peers |
| rust↔lean divergence | identify node + stale archive | **yes** | not a known redeploy |
| STORE INTEGRITY | recoverable vs corruption; re-sync | yes (`node_down`) | re-sync still fail-closes |
| bridge breach | **halt minting**, capture receipts | **yes** | always — money loss |

## See also

- `docs/MONITORING.md` — what every alert means + the thresholds (the signal doc).
- FEDERATION.md — the quorum table, the rust/lean finality mix, lace-merge catch-up.
- NODE-OPS.md — restart, graceful shutdown, the STORE-INTEGRITY runbook + build.
- DISASTER-RECOVERY.md — lost key, corruption, divergent-ledger re-sync.
- NETWORK-TROUBLESHOOTING.md — the bind / `--federation-peers` / UDP / ACL deep dive.
- OPS-DASHBOARD.md — the single-pane rollup + `/api/alerts`.
