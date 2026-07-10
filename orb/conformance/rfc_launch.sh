#!/usr/bin/env bash
# Launch the deployed serve for the RFC 7230/7231 conformance probe.
#
#   conformance/rfc_launch.sh [io]      # io = uring (default) | blocking | kqueue
#
# Starts the leanc-compiled proven serve behind the Rust reactor with the same
# deployment env the base conformance suite uses (DRORB_EFFECT_SEAM=1) plus the
# real Rust gzip seam (DRORB_RUST_GZIP=1). Detaches, waits for the listen socket,
# prints the startup line. Stop with: pkill -f 'release/dataplane'.
#
# NOTE: no DRORB_SPAN is set — the DEPLOYED DEFAULT serve is now RFC-conformant.
# Every metered serve path crosses its `drorb_serve_metered*_conformant` twin (the
# proven `conformantServe` wrapper composed WITH the IP-filter/rate gates), so the
# probe drives the real default to 17/17 with no A/B env. (DRORB_SPAN=19 remains the
# non-metered conformant serve, kept for A/B; it is NOT needed here.)
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

IO="${1:-uring}"
PORT="${CONF_HTTP_PORT:-8391}"
export HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
export LD_LIBRARY_PATH="${HACL_DIST}:${LD_LIBRARY_PATH:-}"

pkill -f "release/dataplane" 2>/dev/null || true
sleep 0.5
DRORB_RUST_GZIP=1 DRORB_EFFECT_SEAM=1 HACL_DIST="$HACL_DIST" \
  setsid ./target/release/dataplane --bind "127.0.0.1:${PORT}" --no-udp --io "$IO" \
  >/tmp/dp-rfc.log 2>&1 < /dev/null &
for _ in $(seq 1 40); do
  if ss -ltn 2>/dev/null | grep -q ":${PORT} "; then break; fi
  sleep 0.1
done
cat /tmp/dp-rfc.log
ss -ltn 2>/dev/null | grep -q ":${PORT} " && echo "listening on 127.0.0.1:${PORT} (io=${IO})" || { echo "FAILED to listen"; exit 1; }
