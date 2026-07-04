# node_exporter — DreggNet host metrics

The standard Prometheus **host** exporter (CPU / RAM / disk usage+IO / network /
load / uptime) for all three DreggNet machines. It fills the host-level gap the
`dregg_*` protocol metrics and the node-thermal sidecar don't cover. Feeds the
**DreggNet · Host Overview** Grafana dashboard.

## Topology

| host     | overlay IP    | how node_exporter runs                                  | Prometheus instance |
|----------|---------------|---------------------------------------------------------|---------------------|
| edge     | (compose DNS) | a container in `docker-compose.observability.yml` with `pid:host` + `/:/host:ro` | `edge` |
| node-a   | 100.64.0.2    | a systemd service (`node_exporter.service`) on the box  | `node-a` |
| node-b   | 100.64.0.3    | a systemd service (`node_exporter.service`) on the box  | `node-b` |

All three serve `/metrics` on `:9100`. The edge one is scraped by compose DNS
(`node-exporter:9100`); node-a and node-b are scraped over the headscale overlay
(`100.64.0.x:9100`). The ACL (`deploy/staging/headscale/acls.hujson`) opens `9100`
on `tag:compute` from `tag:edge`, the same lesson as the `:8022` thermal exporter.

## Install on node-a / node-b

```sh
scp deploy/observability/node-exporter/{node_exporter.service,install-node-exporter.sh} node-a:/tmp/
ssh node-a 'sudo bash /tmp/install-node-exporter.sh'
# and node-b (when reachable):
scp deploy/observability/node-exporter/{node_exporter.service,install-node-exporter.sh} dregg@100.64.0.3:/tmp/
ssh dregg@100.64.0.3 'sudo bash /tmp/install-node-exporter.sh'
```

The installer is idempotent (pinned to node_exporter v1.8.2): it creates the
unprivileged `node_exporter` user, drops the binary in `/usr/local/bin`, installs
the systemd unit, and `enable --now`s it.

## Edge

The edge runs node_exporter as a container in the observability compose project —
no host install needed. `pid: host` + the read-only `/:/host` bind mount let it
read the BOX's `/proc`, `/sys` and filesystems rather than the container's.

```sh
cd /opt/dreggnet
docker compose -f docker-compose.observability.yml up -d node-exporter
```

## Verify

```sh
# on the edge:
docker compose -f docker-compose.observability.yml exec prometheus \
  wget -qO- 'http://node-exporter:9100/metrics' | head
curl -s http://100.64.0.2:9100/metrics | head   # node-a over the overlay
curl -s http://100.64.0.3:9100/metrics | head   # node-b over the overlay
```

Then in Prometheus (`127.0.0.1:9090/targets`) the `node-exporter` job should show
`edge`, `node-a`, `node-b` all **UP**.
