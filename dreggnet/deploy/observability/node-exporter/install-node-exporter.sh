#!/usr/bin/env bash
# Install prometheus node_exporter on a DreggNet compute box (node-a, node-b).
#
# Idempotent: downloads the node_exporter binary (pinned VERSION below) to
# /usr/local/bin, creates a system `node_exporter` user, installs the systemd
# unit (node_exporter.service, copied next to this script), and enables it so it
# serves /metrics on 0.0.0.0:9100 over the overlay for the edge Prometheus.
#
#   # from the repo, push the two files and run:
#   scp deploy/observability/node-exporter/{node_exporter.service,install-node-exporter.sh} node-a:/tmp/
#   ssh node-a 'sudo bash /tmp/install-node-exporter.sh'
#
# Verify (from the edge, over the overlay):
#   curl -s http://100.64.0.2:9100/metrics | head   # node-a
#   curl -s http://100.64.0.3:9100/metrics | head   # node-b
set -euo pipefail

VERSION="1.8.2"
ARCH="$(uname -m)"
case "$ARCH" in
  x86_64)  GOARCH="amd64" ;;
  aarch64|arm64) GOARCH="arm64" ;;
  *) echo "unsupported arch: $ARCH" >&2; exit 1 ;;
esac

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARBALL="node_exporter-${VERSION}.linux-${GOARCH}.tar.gz"
URL="https://github.com/prometheus/node_exporter/releases/download/v${VERSION}/${TARBALL}"

echo "==> installing node_exporter ${VERSION} (${GOARCH})"

# 1. system user (no login, no home)
if ! id node_exporter >/dev/null 2>&1; then
  useradd --system --no-create-home --shell /usr/sbin/nologin node_exporter
fi

# 2. binary
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
curl -fsSL "$URL" -o "$tmp/$TARBALL"
tar -xzf "$tmp/$TARBALL" -C "$tmp"
install -m 0755 "$tmp/node_exporter-${VERSION}.linux-${GOARCH}/node_exporter" /usr/local/bin/node_exporter

# 3. systemd unit (use the copy that shipped next to this script)
if [ -f "$SCRIPT_DIR/node_exporter.service" ]; then
  install -m 0644 "$SCRIPT_DIR/node_exporter.service" /etc/systemd/system/node_exporter.service
else
  echo "node_exporter.service not found next to this script ($SCRIPT_DIR)" >&2
  exit 1
fi

# 4. enable + (re)start
systemctl daemon-reload
systemctl enable --now node_exporter
sleep 1
systemctl --no-pager --full status node_exporter | head -n 12 || true

echo "==> node_exporter up on $(hostname): http://0.0.0.0:9100/metrics"
echo "    verify from the edge over the overlay (curl http://<overlay-ip>:9100/metrics | head)"
