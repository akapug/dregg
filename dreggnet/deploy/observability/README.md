# DreggNet Observability — Prometheus + Grafana + Alertmanager

A real time-series + dashboards + alerting foundation for the DreggNet edge,
deployed as a **separate compose project** that scrapes the running main stack.
It does NOT edit the main `docker-compose.yml` or `Caddyfile` (the redeploy lane
owns those).

## Layout

```
deploy/staging/docker-compose.observability.yml   # the stack (name: dreggnet-obs)
deploy/observability/
  prometheus/prometheus.yml                        # scrape config
  prometheus/rules/dreggnet.rules.yml              # alert rules (page/warn)
  alertmanager/alertmanager.yml                    # routing → alert-sink (swap for real sink)
  json-exporter/config.yml                         # ops /api/health + gateway /status → metrics
  blackbox-exporter/config.yml                     # http_2xx up/down probes
  grafana/provisioning/                            # datasource + dashboard providers
  grafana/dashboards/                              # 6 dashboards-as-code
```

## Bring it up (on the edge box, main stack already running)

```sh
cd /opt/dreggnet
docker compose -f docker-compose.observability.yml up -d
```

It attaches to the main stack's `dreggnet_default` network (external) so it can
scrape `dregg-node:8420`, `ops:8090`, `gateway:8080`, `dreggnet-discord-bot:8080`
by name, and node-a over the overlay (`100.64.0.2:8021`).

## Access

- **Grafana** — admin login. User `admin`, password from `GRAFANA_ADMIN_PASSWORD`
  (the baked default is handed over out of band). Bound to host loopback
  (`127.0.0.1:3000`); reach it during ops via an SSH tunnel:
  `ssh -i ~/.ssh/dreggnet-staging.pem -L 3000:127.0.0.1:3000 ubuntu@<EDGE_HOST>`
  then open http://localhost:3000 . Nine dashboards under the **DreggNet** folder:
  Consensus, Economy, Compute, Bridge, Security, Cloud Health, **Host Overview**
  (CPU/RAM/disk/network/load/uptime for edge+node-a+node-b via node_exporter),
  **Cloud** (is-the-cloud-working + how-busy: services up/down, machines, leases,
  lease economy, bridge, pg pressure), and **Protocol** (consensus, turns/sec,
  finality, per-validator vote-share, blocklace depth/frontier, mempool, receipts).
  Public: **grafana.dreggnet.example.com** (the main Caddy vhost; admin login).
- **Prometheus** (`127.0.0.1:9090`) and **Alertmanager** (`127.0.0.1:9093`) are
  loopback-only (NOT publicly exposed) — tunnel the same way to inspect targets/rules.

## Publishing Grafana on the public web (a one-line MAIN-Caddyfile addition)

This stack does NOT touch the main Caddyfile. To put Grafana behind the existing
Caddy TLS + on a real hostname, the main loop adds this vhost to
`deploy/staging/Caddyfile` (Grafana is reachable in-cluster as `grafana:3000`
because both Caddy and Grafana sit on `dreggnet_default`):

```caddyfile
# --- the OBSERVABILITY Grafana (admin-login gated) -------------------------
# grafana.dreggnet.example.com — provisioned dashboards over Prometheus.
# Grafana's own admin login is the gate (no Caddy basic-auth needed, but you may
# add the admin block for defence in depth). tls internal until the
# A-record propagates, then drop it for Let's Encrypt.
grafana.dreggnet.example.com {
	tls internal
	reverse_proxy grafana:3000
}
```

(Add an A-record `grafana.dreggnet.example.com -> <EDGE_HOST>`, or test by
raw IP with `--resolve`.) Prometheus/Alertmanager intentionally get NO public
vhost; keep them loopback + tunnel.

## Host metrics — prometheus node_exporter (the host-level gap)

The `dregg_*` protocol metrics and the node-thermal sidecar don't cover host
resources, so all three boxes run the standard **node_exporter** (`:9100`):

- **edge** — a container in `docker-compose.observability.yml` (`pid:host` + `/:/host:ro`),
  scraped by compose DNS (`node-exporter:9100`), relabelled `instance=edge`.
- **node-a** / **node-b** — a systemd service (`deploy/observability/node-exporter/`),
  scraped over the headscale overlay (`100.64.0.2:9100` / `100.64.0.3:9100`). The
  ACL (`deploy/staging/headscale/acls.hujson`) opens `9100` on `tag:compute` and
  names `node-b` (an untagged node) for the edge — the `:8022` thermal lesson.

Install on node-a/node-b: `sudo bash install-node-exporter.sh` (see
`node-exporter/README.md`). The **Host Overview** dashboard's `$host` variable
groups the three. node-b's target is UP once its SSH is reachable and the
installer has run (until then it shows DOWN / connection-refused).

## What is scraped — live vs the metric-enrichment follow-up

**Live today:**
- `dregg-node:8420/metrics` — native Prometheus. `dregg_federation_peers_connected`
  is populated now; the other `dregg_*` families (block height, divergence, tau,
  revocations, turns/proofs) are registered and emit as the node touches them.
- `ops:8090/api/health` via **json-exporter** — the rich live source: block height,
  peers, federation members, consensus-live/finalizing, machines, durable jobs in
  flight, total units spent, pg active/max/size, bridge mints observed,
  bridge conservation (when a relayer is configured), and divergence/tau (when
  ops reports them non-null).
- `gateway:8080/status` via json-exporter — machines count, dispatch enabled.
- **blackbox** http_2xx up/down for node, gateway, ops, bot, and node-a (overlay).
- **security counters (native node)** — `dregg_turns_rejected_total` (every
  `TurnResult::Rejected`), `dregg_auth_failures_total` (credential/authorization-gate
  refusals), `dregg_cap_refusals_total` (the CAP path), classified from the
  `TurnError` at the real reject sites. The Security dashboard is now a live
  exploitation-attempt detector. (`dregg_sandbox_denials_total` is registered but
  stays 0 on the node — see below.)
- **consensus signals (native node)** — `dregg_consensus_finality_latency_seconds`
  (first local finalization vote → consensus-wide quorum) and per-validator
  `dregg_validator_last_seen_timestamp_seconds`, emitted on every recorded
  finalization vote. The Consensus dashboard's finality-latency + validator-liveness
  panels.
- **node-a thermals** via the `node-a-thermal` job → `node_a_cpu_temp_celsius`
  / `node_a_cpu_freq_mhz` / `node_a_fan_level` / `node_a_load1`. UP once the
  `node-thermal-exporter` sidecar's systemd unit is enabled on node-a (see
  `node-thermal-exporter/README.md`). The Compute dashboard's thermal panels.

**Enrichment follow-up (named, not wired here):**
- **sandbox denials** — `dregg_sandbox_denials_total` is registered on the node but
  the exec deny-by-default lives in the DreggNet `exec` plane (a separate process
  with no Prometheus surface), so it stays 0 until exec exports its own metrics.
- **bridge** per-mirror locks / live_supply vs backing / `double_mint` counter —
  need the bridge-relayer status surface (`OPS_BRIDGE_URL`, currently
  `not-configured`).

## Alerting

`prometheus/rules/dreggnet.rules.yml` mirrors the ops page/warn model:
- **page** — ConsensusDivergence (rust↔lean), NodeDown, NodeNotFinalizing,
  BridgeConservationBreach.
- **warn** — BackendDown (lease-lapse cause), GatewayDown, PostgresConnectionPressure,
  TauPrefixShifts, RevocationSpike.

Alertmanager routes by severity to the **alert-sink** request-logger
(`docker logs dreggnet-obs-alert-sink-1`). For a real page, replace the webhook
`url` in `alertmanager/alertmanager.yml` with ember's Slack/Discord/email sink
(Discord: append `/slack` to a Discord webhook for Slack-compatible payloads).
