# GRAFANA-GUIDE — how to read the DreggNet dashboards

This is the "what am I looking at" guide for the provisioned Grafana. It is the
deep-metrics companion to the **ops/admin portal** (`MONITORING.md`): the ops
portal answers *what's going on right now and what
happened* in human terms; Grafana answers *how has each number moved over time*.

> **Two surfaces, cross-linked.** The ops portal (`https://ops.dreggnet.<domain>`)
> has a **History** tab — the browsable, filterable "what happened" ledger — and a
> **Grafana ↗** link in its header that opens the board below. Each History viewer
> (Turns, Compute, Economy, Bridge) deep-links to the matching board. Set
> `OPS_GRAFANA_URL=https://grafana.dreggnet.<domain>` on the ops service to light
> those links up.

---

## Getting in (the part that's usually the blocker)

Grafana is provisioned **dashboards-as-code** — you do **not** build panels by
hand; they ship in `deploy/observability/grafana/dashboards/*.json` and load
automatically. "Configuring" Grafana here means three things, all already done:

1. **The datasource** is wired (Prometheus, `uid: dreggnet-prometheus`,
   `provisioning/datasources/datasource.yml`). You never pick a datasource.
2. **The dashboards** are provisioned into the **DreggNet** folder
   (`provisioning/dashboards/dashboards.yml`). Edits to the JSON files reload
   within 30s; UI edits are allowed but are **not** persisted across a redeploy
   (the files are the source of truth — change those to keep a change).
3. **The landing page** is set to **Cloud Health** (`GF_DASHBOARDS_DEFAULT_HOME_DASHBOARD_PATH`),
   so logging in drops you straight onto the rollup instead of a blank welcome.

**Reach it.** Grafana is bound to host loopback (`127.0.0.1:3000`); tunnel:

```sh
ssh -i ~/.ssh/dreggnet-staging.pem -L 3000:127.0.0.1:3000 ubuntu@<edge-ip>
# then open http://localhost:3000  (user `admin`, GF_SECURITY_ADMIN_PASSWORD)
```

Or, once the public vhost is added (`deploy/observability/README.md`), open
`https://grafana.dreggnet.<domain>` and log in with the same admin credential.

**Every board's defaults** are saved: top-right shows **last 6h**, auto-refresh
**30s**. To zoom: drag-select on any time-series, or use the time picker
(top-right) — try `last 24h` after an incident, `last 5m` while you watch a fix
land. Hover any panel title → the **ⓘ** shows that panel's one-line description.

---

## Which board do I open?

| You want to know… | Open | uid |
|---|---|---|
| Is the cloud working at all? | **Cloud Health** | `dreggnet-cloud-health` |
| Is-it-working **and** how busy (one board) | **Cloud** | `dreggnet-cloud` |
| Chain correctness / finality / validators | **Consensus** | `dreggnet-consensus` |
| Throughput, turns, receipts, mempool, DAG | **Protocol** | `dreggnet-protocol` |
| Compute backend + machines + node-a thermals | **Compute** | `dreggnet-compute` |
| $DREGG flows, lease spend, jobs | **Economy** | `dreggnet-economy` |
| Solana/Stripe bridge + conservation | **Bridge** | `dreggnet-bridge` |
| Anything safety/abuse-shaped | **Security** | `dreggnet-security` |
| CPU/RAM/disk/network on the boxes | **Host Overview** | `dreggnet-hosts` |

Deep-link any board directly: `<grafana-url>/d/<uid>`.

---

## The boards, panel by panel

### Cloud Health — *"is the cloud working?"* (the landing page)
The single-pane rollup. **Stat tiles up top are the headline:** `Node`,
`Gateway`, `Ops`, `Bot`, `Backend` each read **1 = up / 0 = down** (blackbox HTTP
probes). `Finalizing` = the node's own readiness (store ok + consensus live + ≥1
block). **`Node` or `Finalizing` at 0 is the page** — the chain is down or
stalled. **Service availability** plots those probes over time, so you can see
*when* something dropped. Lower row: `Block height` (must rise), `Peers` (0 on a
solo edge is fine), `Units spent` (cumulative lease economy), `PG conns` +
**Postgres connections (active vs max)** (watch ≥85% = pressure), **Postgres DB
size** (a grower — watch host disk).
**Read it when:** anything feels wrong. Start here, then dive to the specific board.

### Cloud — *"is it working AND how busy?"*
Cloud Health plus the activity numbers on one board: `Machines`, `Total leases`,
`Durable jobs in flight`, `Lease economy — units spent`, `Bridge conservation`,
`Bridge mints observed`, `Postgres pressure`, `DB size`, plus `Dispatch enabled`
(is the orchestrator placing work?) and `node-a compute thermals`. The
everyday "glance at the whole cloud" board.

### Consensus — *"is the chain correct and finalizing?"*
`Node up` / `Consensus live` / `Finalizing` (the safety headline), `Peers` /
`Federation peers`, `Block height`, **`rust↔lean differential divergence`**
(**must be 0** — any non-zero means the Rust and verified-Lean finalizers
disagreed on an ordering; investigate now), `tau-prefix shifts` (benign
reorg-by-catchup; informational), **`Finality latency`** (how long to finalize),
**`Validator liveness (age of last vote)`** (a validator whose last-vote age
climbs is going quiet).
**Read it when:** finality feels slow, or the ops portal pages `consensus_divergence`.

### Protocol — *"throughput and the protocol internals."*
`Turns / sec`, `Turn execution latency`, `Finality latency`, `Consensus attested
rate`, `Mempool pending`, `Receipt chain length`, `Proofs`, `Ledger cells`,
`DAG / blocklace` depth/frontier, `Validator vote-share %` (is one validator
dominating?), plus the divergence/tau pair. The board for "is the node keeping up
and what is it doing".

### Compute — *"is there somewhere to run work, and is it healthy?"*
`Backend (node-a) up`, `Gateway up`, `Dispatch enabled`, `Machines`, `Backend
probe latency`, `Durable workload jobs in flight`, and the node-a thermals
(`CPU package temperature`, `CPU frequency`, `fan level`). **Backend down is the
dominant lease-lapse cause** — a refused lease becomes a lapse, so when leases
lapse, check `Backend up` here first.

### Economy — *"where is $DREGG flowing?"*
`Total units spent` + `Lease spend (total metered units)` (the **spent** side of
the economy — cumulative meter units charged), `Jobs in flight` / `Durable jobs
in flight` (active metered runs), `Machines` / `Gateway machines`, and `$DREGG
bridge mints observed`. **Honest scope:** this is the *spent* side (the durable
meter outbox); *minted/conserved* live per-cell in the dregg lease-cell ledger on
the node, and per-asset mint/transfer/burn rate breakdowns need the bridge-relayer
metrics (light up when `OPS_BRIDGE_URL` is configured).

### Bridge — *"is the mirror bridge conserving?"*
`Conservation OK` (**1 = conserved, 0 = BREACH** — circulating mirror asset must
never exceed what is locked/cleared; **a 0 here is critical**), `Mints observed`,
`Bridge mints observed` over time, and `Double-mint breaches` (the consume-once
nullifier being bypassed — should stay 0). Conservation/double-mint are only
*observed* when a relayer status endpoint is configured (`OPS_BRIDGE_URL`);
absent, they read **un-observed**, never a false all-clear.

### Security — *"is anything being abused or refused?"*
`Revocations`, **`rust↔lean divergence (security-critical)`** (the same
must-be-0 series, framed as the safety signal), `Rejected turns`, `Auth
failures`, `Cap refusals`, `Sandbox denials`. Spikes here are the abuse/attack
surface. The 15m-window tiles (`Revocations (15m)`, `Auth failures (15m)`) are the
quick "anything happening right now" read.

### Host Overview — *"are the boxes healthy?"*
Standard node_exporter host metrics for the edge + node-a + node-b: `Hosts up`,
`CPU usage %`, `Memory used %`/`(bytes)`, `Disk used % per mount`, `Disk IO`,
`Network throughput`, `Load average`, `Uptime`. The board *below* the protocol —
when a service is flaky, check whether its **box** is out of CPU/RAM/disk here.

---

## Reading-the-numbers cheatsheet

- **`probe_success` / `*_up` = 1 is good, 0 is down.** The stat tiles are colored
  green/red on that threshold.
- **`rust↔lean divergence` must be 0** on every board it appears (Consensus,
  Protocol, Security). Non-zero = a real consensus-implementation bug — page.
- **Counters rise; don't read the raw height of a counter, read its slope.** A
  flat `Turns / sec` over a period of expected load is the signal, not the number.
- **`tau-prefix shifts` rising is benign** (honest late block, absorbed by the
  identity cursor) — informational, never a page.
- **PG connections ≥ 85% of max** = pressure; **DB size** climbing = watch host
  disk on the edge box.
- **Conservation `0`/BREACH and Double-mint `> 0`** on the Bridge board are
  critical — they mean more mirror asset circulates than is backed.
- **"No data" on a panel** usually means that series isn't being emitted yet
  (e.g. bridge-relayer metrics with no relayer configured, or node-a offline) —
  it is not necessarily a fault. Cross-check the matching service tile on Cloud
  Health.

---

## Keeping a change (the source-of-truth rule)

UI edits to a provisioned dashboard are allowed but **revert on redeploy**. To
make a change stick, edit the JSON in
`deploy/observability/grafana/dashboards/<uid>.json` and commit it — the
provisioner reloads it within 30s. Use Grafana's **Dashboard settings → JSON
Model** to copy your UI tweak back into the file. The panel `description` fields
are what drive the hover-help **ⓘ**; keep them filled when you add a panel.

---

*Companion docs: `MONITORING.md` (the admin portal + alerts + thresholds + the
auto-recovery posture), `deploy/observability/README.md` (the stack + how it's
brought up). Verify panel names against the JSON at HEAD before relying on a
specific title.*
