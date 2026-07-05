# MONITORING — watch, alert, recover the live DreggNet

This is the operator's monitoring runbook: what to watch, the thresholds, what
each alert means, and the auto-recovery posture. It is the observe-it companion
to `OPERATING.md` (run + restart) and `deploy/FEDERATION.md` (the federation
state). Grounded to the deployed `deploy/staging/docker-compose.yml` + the
`dreggnet-ops` dashboard at HEAD.

The principle: **the orchestration lane owns the metrics** (the node emits its
own Prometheus series; this lane never adds metrics to the node/exec). Monitoring
here is *consumption* — the ops dashboard aggregates the existing read surfaces +
metrics and turns them into health signals, alerts, and a runbook.

---

## 1. The three layers

```
  process layer   docker compose   restart: unless-stopped + healthcheck + depends_on
                                    → a crashed service restarts; the stack starts in order
  signal layer    dreggnet-ops     aggregates node/gateway/bot/durable/backend + node /metrics
                                    → the whole-cloud health rollup + the alert set
  alert path      ops alerter      logs (always) + webhook (optional) + GET /api/alerts (pull)
                                    + the dashboard banner / header badge
```

- **Dashboard:** `https://ops.dreggnet.example.com` (separate admin password,
  user `admin`). Pre-DNS by raw IP:
  `curl -k --resolve ops.dreggnet.example.com:443:<EDGE_HOST> -u admin:<pw> https://ops.dreggnet.example.com/healthz`
- **Snapshot JSON:** `GET /api/snapshot` (everything), `GET /api/health` (the
  rollup), `GET /api/alerts` (the active alerts only).
- **History viewer:** the dashboard's **History** tab is the browsable,
  filterable "what happened" ledger over the receipt chain / turn log, the
  leases & machines, the compute runs, the $DREGG economy, and the bridge —
  sliceable by **category / who / effect / free-text / time window**. The JSON
  behind it: `GET /api/history?category=&who=&what=&q=&since=&until=&limit=`
  (`since`/`until` accept RFC3339, a bare epoch, or a relative window like
  `6h`/`7d`). It is the human "understand what's going on" surface; Grafana is the
  deep time-series — see **`GRAFANA-GUIDE.md`**, cross-linked from the dashboard
  header (set `OPS_GRAFANA_URL` to light the links up).
- **Auth (the `ops-admin` cap):** the dashboard is gated at the Caddy edge by
  `forward_auth webauth:8099 ?cap=ops-admin` — the operator presents a `dga1_…`
  dregg capability (held in their cipherclerk), verified offline by
  `dreggnet-webauth`. On admit, webauth copies `X-Dregg-Subject` / `X-Dregg-Cap`
  / `X-Dregg-Auth` onto the request; the dashboard header then shows **who is
  signed in** (subject · cap) with a **sign out** link. For defence-in-depth set
  `OPS_REQUIRE_CAP=ops-admin`: the app then **internalizes** the gate and refuses
  to serve (`403`) any request lacking the verified `X-Dregg-Cap` — so a Caddy
  misconfig that drops the forward-auth cannot expose the portal. A break-glass
  admit (`DREGG_WEBAUTH_BREAK_GLASS`) is always honored so the operator is never
  locked out. `GET /api/whoami` echoes the resolved identity.
- **Economy depth:** the **Durable / Economy** tab reads the `dreggnet_meter`
  outbox as a per-event ledger (every `(lease, period)` charge — when, units,
  running total) and splits spend **by resource**: compute leases vs the hosting
  bills (`bandwidth` / `uptime` / `publish` / `cert` / `build`, classified from
  the `host:<resource>:<key>` lease id). Each charge is a conserving
  `payer → beneficiary` move (per-asset Σδ=0).

---

## 2. What to watch (the health signals)

The ops dashboard surfaces these on the Overview tab (tiles + service dots) and
in the health rollup (`/api/health`):

| Signal | Source | Healthy | Watch |
|---|---|---|---|
| **node up** | node `/status` reachable | up | `node` dot red → chain down |
| **node finalizing** | node `/status` `healthy` (store ok + consensus live + ≥1 block) | yes | `no` → up but not making progress |
| **consensus live** | node `/status` `consensus_live` | live | `stalled` → quorum not finalizing |
| **rust↔lean divergence** | node `/metrics` `dregg_consensus_differential_divergence_total` | `0` | **any non-zero = consensus bug** |
| **reorg-by-catchup (τ shifts)** | node `/metrics` `dregg_tau_prefix_shifts_total` | any | informational — benign, the identity cursor absorbs it |
| **block height** | node `/status` `latest_height` | rising | flat across refreshes → not finalizing |
| **gateway up** | gateway `/status` reachable | up | `gateway` dot red → machines API down |
| **compute backend** | node-a `:8021/health` | up | down → dispatched leases lapse |
| **postgres / durable** | `dreggnet_meter` connect | up | down → metering stalls, leases lapse |
| **PG connections** | `pg_stat_activity` vs `max_connections` | < 85% | ≥ 85% → connection pressure |
| **discord bot** | bot read API reachable (if configured) | up | down → community front door down |
| **durable jobs in flight** | meter outbox recent window | ≥ 0 | a sudden drop with backend down = lapses |
| **bridge conservation** | relayer status `live ≤ locked` (per asset) | OK / un-observed | **BREACH = critical bridge bug** |
| **bridge mints / redeems** | node `/api/events` (`mint`/`bridgemint`/`burn`) | rising with use | last-mint staleness |
| **bridge relayer / solana / stripe** | reachability probes (if configured) | up / not-configured | down → that bridge leg degraded |

---

## 2b. The coin-bridge panel (Solana / Stripe mirror)

The **Bridge** tab observes the Solana/Stripe mirror bridge (`breadstuffs/bridge/`)
read-only — it changes no bridge logic. Three honest tiers of evidence:

1. **Live on the node (grounded today).** Every bridge mint/redeem lands as a real
   kernel effect, so the node's committed-event feed carries it: `mint` /
   `bridgemint` is a lock→mint (oracle / trustless respectively), `burn` is a
   redeem. The panel counts these, timestamps the last mint, and feeds the
   activity. *Honest gap:* the events feed carries a mint's KIND but not its
   amount (burn summaries do carry amount+asset).
2. **The relayer status endpoint (optional, `OPS_BRIDGE_URL`).** A relayer that
   serializes its `MirrorState` / `StripeMirrorState` (the conservation quantities
   `currently_locked` / `total_verified_payments` vs `live_supply`, plus the
   consumed-lock count) is what lets the panel surface AND alert on the
   **conservation invariant** + **double-mint**. Absent (the staging default) →
   conservation is reported **un-observed** (never a false all-clear).
3. **External reachability (optional, plaintext only).** The Solana devnet RPC
   (`OPS_SOLANA_RPC_URL`, `getHealth`) and the Stripe webhook receiver
   (`OPS_STRIPE_RECEIVER_URL`). The ops binary carries no TLS closure by design,
   so an `https` Solana RPC is recorded **unreachable** from here — point these at
   a plaintext-proxied health, or read reachability from the relayer status
   (tier 2). **The mainnet gap:** the trustless geyser inclusion-proof path is
   verified in the bridge crate but not yet wired to a live mainnet relayer the
   dashboard reads; today's reachable path is devnet/oracle.

---

## 3. The alerts (thresholds + meaning)

The ops alerter computes these every `OPS_ALERT_INTERVAL_SECS` (default 30s) and
on every dashboard refresh. Severity drives the response.

### PAGE — wake someone

- **`consensus_divergence`** — `dregg_consensus_differential_divergence_total > 0`.
  On a Lean-shadowed node the verified Lean `dregg_tau_order` and the Rust
  `ordering::tau` finalized **different** `(creator, seq)` sets for a poll. The
  verified Lean order is authoritative for that poll (safety holds), but the two
  implementations disagreeing is a real bug — a Rust-side ordering bug or a
  stale/mismatched Lean archive. **Action:** capture node logs around the
  divergence, compare the deployed node image's Lean archive against HEAD, file it.
  This must never sit non-zero unattended.
- **`node_down`** — the node's `/status` is unreachable. The chain is down.
  **Action:** `docker compose ps` / `logs dregg-node`; the `unless-stopped` policy
  is already restarting it (see §4). If it crash-loops, it is fail-closing on a
  store it cannot recover — see §4 unrecoverable path.
- **`node_not_finalizing`** — the node is up but reports `healthy:false`
  (`consensus_live:false`, store unreachable, or no blocks). **Action:** check
  `consensus_live` + peers; on a solo edge a stalled consensus task or a wedged
  store is the usual cause; restart picks up the recovery path.
- **`bridge_conservation_breach`** — a mirror's `live_supply > currently_locked`
  (Solana) / `> total_verified_payments` (Stripe): more mirror asset is
  circulating than is backed. The conservation invariant is the bridge's core
  safety property; a breach is a critical bridge bug. **Action:** freeze the
  relayer, capture the mint receipts vs the locked side, compare against the
  on-chain locks. Requires `OPS_BRIDGE_URL` to be observed.
- **`bridge_double_mint`** — the relayer reports a successful double-mint (the
  consume-once lock nullifier was bypassed). Equivalent to a breach by
  construction. **Action:** as above; the committed `note_nullifiers` gate should
  make this impossible, so a firing here is a kernel/relayer bug, not a misconfig.

### WARN — degraded, look soon

- **`gateway_down`** — gateway `/status` unreachable. The Fly-machines API is
  down; the node/chain may still be fine. Restart is automatic.
- **`postgres_down`** — the durable/billing Postgres is configured but
  unreachable. The meter outbox cannot record charges → the lease economy stalls
  and leases lapse. **Action:** `logs postgres`; check disk (§ below).
- **`postgres_conn_pressure`** — `≥ 85%` of `max_connections` in use. A
  connection leak or a load spike; risks new connections being refused.
- **`backend_down`** — the compute backend (`:8021/health`) is unreachable. A
  refused/undeliverable lease maps to a **lapse**, so a down backend is the
  dominant lease-lapse cause — this is the grounded lease-lapse-rate signal.
  Expected while node-a is offline (hardware surgery); unset `OPS_BACKEND_URL`
  to silence it then.
- **`bot_down`** — the Discord bot read API is configured but unreachable. The
  community front door is down (the bot also exits without its go-live secrets —
  see `MINI-DEVNET.md`).
- **`bridge_relayer_down`** — `OPS_BRIDGE_URL` is configured but its status
  endpoint is unreachable. Conservation/double-mint can no longer be observed
  (the panel reports un-observed, not all-clear). **Action:** check the relayer
  process / its host.
- **`bridge_solana_down`** — `OPS_SOLANA_RPC_URL` is configured but the cluster's
  `getHealth` is unreachable (recall: `https` RPCs are not probeable from the
  no-TLS ops binary — use a plaintext proxy or the relayer's report). Inbound
  locks cannot be observed/verified while down.
- **`bridge_stripe_down`** — `OPS_STRIPE_RECEIVER_URL` is configured but the
  webhook receiver health is unreachable. USD-credit mints stall while down.

### INFO — FYI (dashboard tiles, not pushed)

- **reorg-by-catchup / τ prefix shifts** — `dregg_tau_prefix_shifts_total`
  rising. An honest late block sorted into an already-executed region; the
  identity execution cursor absorbs it correctly. A rising rate is worth a glance
  (network churn) but is **not** a bug and does not page.
- **bridge double-mints REJECTED** — the relayer's count of double-mint attempts
  the nullifier gate refused. This is the gate **working as intended** (a tile on
  the Bridge tab), not a fault. Only a *successful* double-mint (`bridge_double_mint`)
  pages.

---

## 4. Auto-recovery posture

The recoverable case is self-healing; the unrecoverable case fail-closes loudly.

**The loop (recoverable):** `crash → restart → recover → healthy`.
- `restart: unless-stopped` (every service) + dockerd-on-boot restart a crashed
  process or reboot the box back into the stack.
- On node restart, the **genesis-first-then-overlay** recovery (`1a61dc16d`)
  reconstructs the finalized ledger from (genesis baseline ⊕ durable overlay) in
  the sound order — no manual `dregg.redb` wipe needed for the recoverable case.
- Graceful shutdown: the node catches **SIGTERM** (`docker stop`/redeploy) and
  flushes a clean checkpoint before exit (`node/src/main.rs::shutdown_signal` →
  `persist_on_shutdown`). `stop_grace_period: 45s` gives that flush room so the
  redeploy does not SIGKILL mid-checkpoint (the original cause of the restart
  STORE-INTEGRITY event).
- The node healthcheck does a real HTTP `/health` probe over `/dev/tcp` (the node
  image has no curl), with `start_period: 90s` to cover boot + recovery replay, so
  a hung-but-listening node is caught (a bare TCP probe would miss it). Dependents
  (`dreggnet-discord-bot`, etc.) gate on `service_healthy`, so they only start
  once the node is genuinely serving.

**Fail-closed (unrecoverable):** a node that hits **real corruption** it cannot
reconstruct **exits rather than serve divergent state**. Under `unless-stopped`
it then crash-loops visibly (rather than serving wrong state), and the ops layer
pages `node_down` / `node_not_finalizing`. The operator fallback for an
unrecoverable local store: wipe the node's `dregg.redb` (keep `genesis.json` +
`node.key`), restart; it re-seeds genesis, re-peers, and replays the finalized
DAG from the quorum, re-deriving the exact state. This is the *manual* path; the
recoverable case above needs no intervention.

**Confirming the loop holds:**
```bash
# recoverable: a clean restart auto-recovers to healthy (no wipe)
docker compose -f deploy/staging/docker-compose.yml restart dregg-node
docker compose -f deploy/staging/docker-compose.yml ps           # → dregg-node healthy
# graceful stop flushes a checkpoint (look for the SIGTERM log line)
docker compose -f deploy/staging/docker-compose.yml logs --tail=50 dregg-node | grep -i sigterm
```

---

## 5. The alert path (how an operator notices)

Three independent surfaces, no extra infrastructure required:

1. **Dashboard banner + header badge** — every page/warn alert renders as a
   banner on all tabs, with a red `⚠ N PAGE` / amber `N warn` badge in the header
   and the overall pill pulled to `degraded` when a page is active.
2. **Log path (always on)** — the alerter writes every page/warn alert to the ops
   container log: `dreggnet-ops ALERT [page] consensus_divergence: …`. Tail it
   from the dashboard Logs tab (pick `ops`) or
   `docker compose logs -f ops`. De-duplicated by key: a steady-state condition
   fires once and re-fires at most every 10 min; a resolved condition clears so a
   recurrence re-alerts.
3. **Webhook (optional)** — set `OPS_ALERT_WEBHOOK` to a **plain-HTTP** sink; the
   alerter POSTs `{"text":..,"content":..}` (Slack- and Discord-shaped). The ops
   binary carries no TLS closure by design, so for an **https** destination
   (Slack/Discord directly) poll `GET /api/alerts` from a cron and forward, e.g.:
   ```bash
   # cron: page Discord on any active alert (https sink reached by curl, not ops)
   alerts=$(curl -fsS -u admin:<pw> https://ops.dreggnet.example.com/api/alerts)
   [ "$alerts" != "[]" ] && curl -fsS -X POST -H 'content-type: application/json' \
     -d "{\"content\": $(printf %s "$alerts" | jq -Rs .)}" "$DISCORD_WEBHOOK_URL"
   ```

---

## 6. Disk pressure (host-level)

The ops binary monitors the *durable database* size (`pg_db_size_bytes`) and
connection pressure, but **host disk** is below the container and is watched at
the host. The node's `node-data` volume + Postgres `pgdata` are the growers. A
ready cron on the edge box:
```bash
# /etc/cron.d/dreggnet-disk — warn to the journal when the box is ≥ 85% full
*/10 * * * * root use=$(df --output=pcent / | tail -1 | tr -dc 0-9); \
  [ "$use" -ge 85 ] && logger -t dreggnet-disk "disk ${use}% — prune docker / grow volume"
```
`docker system df` shows Docker's share; `docker volume ls` + the `node-data` /
`pgdata` volumes are the ones to grow or prune (old images:
`docker image prune -f`).

---

## 7. Config reference (ops env)

| Env | Default | Meaning |
|---|---|---|
| `OPS_NODE_URL` | `http://dregg-node:8420` | node read surface (status/metrics) |
| `OPS_GATEWAY_URL` | `http://gateway:8080` | gateway read surface |
| `OPS_BOT_URL` | `http://dreggnet-discord-bot:8080` | bot read API (alerts if down) |
| `DATABASE_URL` | (compose) | durable meter outbox (pressure + economy) |
| `OPS_BACKEND_URL` | node-a `:8021/health` | compute backend probe; unset to silence |
| `OPS_BRIDGE_URL` | (unset) | coin-bridge relayer status (conservation/double-mint source) |
| `OPS_SOLANA_RPC_URL` | (unset) | Solana cluster `getHealth` probe (PLAINTEXT only — no TLS) |
| `OPS_STRIPE_RECEIVER_URL` | (unset) | Stripe webhook receiver health (plain GET) |
| `OPS_ALERT_WEBHOOK` | (unset) | plain-HTTP alert sink (Slack/Discord-shaped) |
| `OPS_ALERT_INTERVAL_SECS` | `30` | alerter re-evaluation period (min 5) |
| `OPS_GRAFANA_URL` | (unset) | public Grafana base URL → lights up the dashboard's `Grafana ↗` header + per-viewer deep-links (`<url>/d/<uid>`) |
| `OPS_REQUIRE_CAP` | (unset) | require this dregg cap (`ops-admin`) on every request (`X-Dregg-Cap` from the webauth forward-auth) — fails closed if the edge gate is removed; break-glass always honored |
| `OPS_LOGIN_BASE` | `/.dregg-auth` | where webauth serves `/login` + `/logout` (the dashboard's "signed in as … · sign out" control) |
| `OPS_ADMIN_TOKEN` | (unset) | optional app-layer Bearer/`?token=` gate under Caddy |
| `OPS_DOCKER_SOCKET` | `/var/run/docker.sock` | log tailing (read-only) |

---

*Dated 2026-06-29. Verify against HEAD before relying on a specific value;
metrics are owned by the node/orchestration lane and consumed read-only here.*
