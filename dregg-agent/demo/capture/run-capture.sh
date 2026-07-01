#!/usr/bin/env bash
# Capture ALL the DreggNet browser surfaces for the demo film.
#
# Launches the real server binaries locally (dreggnet-attach / -console / -status
# / -landing) + a hermetic node/webauth stub, drives each surface with Playwright
# (headless chromium; the extension in a headed persistent context), and writes
# the raw clips to out/. Then run ./stitch.sh to composite the film.
#
# Prereqs: the DreggNet binaries built (see below), `npm install` in this dir,
# and the Playwright chromium cached (~/Library/Caches/ms-playwright).
#
#   (cd ~/dev/DreggNet && cargo build -p dreggnet-attach -p dreggnet-console \
#        -p dreggnet-status -p dreggnet-landing)
#   npm install            # in this dir
#   ./run-capture.sh
#
# All data is LOCAL fixtures / a dev subject / a stub node — nothing here is a
# live-cloud claim. Media is gitignored; regenerate any time.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DREGGNET="${DREGGNET_DIR:-$HOME/dev/DreggNet}"
EXT_DIR="${EXT_DIR:-$HOME/dev/breadstuffs/extension}"
BIN="$DREGGNET/target/debug"
SUBJECT="dregg:demo0001demo0001"   # the subject the console fixtures are owned by
export OUT_DIR="$HERE/out"
mkdir -p "$OUT_DIR"

pids=()
cleanup() {
  for p in "${pids[@]:-}"; do kill "$p" 2>/dev/null || true; done
  pkill -f "$BIN/dreggnet-" 2>/dev/null || true
  pkill -f 'capture/mock-node.mjs' 2>/dev/null || true
}
trap cleanup EXIT

for b in dreggnet-attach dreggnet-console dreggnet-status dreggnet-landing; do
  [ -x "$BIN/$b" ] || { echo "missing $BIN/$b — build the DreggNet binaries first (see header)"; exit 1; }
done

echo "── launching the surfaces locally ──────────────────────────────────────"
ATTACH_BIND=127.0.0.1:8100 ATTACH_DEV_SUBJECT="$SUBJECT" ATTACH_DEFAULT_BUDGET=50 \
  ATTACH_LOGIN_BASE=/.dregg-auth "$BIN/dreggnet-attach"  >/tmp/cap-attach.log  2>&1 & pids+=($!)
CONSOLE_BIND=127.0.0.1:8101 CONSOLE_DEV_SUBJECT="$SUBJECT" \
  CONSOLE_LOGIN_BASE=/.dregg-auth "$BIN/dreggnet-console" >/tmp/cap-console.log 2>&1 & pids+=($!)
STATUS_DEMO=1 STATUS_BIND=127.0.0.1:8102 STATUS_FEDERATION_SIZE=5 \
  "$BIN/dreggnet-status"  >/tmp/cap-status.log  2>&1 & pids+=($!)
LANDING_BIND=127.0.0.1:8103 LANDING_STATUS_URL=http://127.0.0.1:8102 \
  LANDING_CONSOLE_URL=http://127.0.0.1:8101 "$BIN/dreggnet-landing" >/tmp/cap-landing.log 2>&1 & pids+=($!)
node "$HERE/mock-node.mjs" 8420 >/tmp/cap-mock.log 2>&1 & pids+=($!)

sleep 2
for u in 8100/api/whoami 8101/healthz 8102/healthz 8103/healthz; do
  curl -sf "http://127.0.0.1:$u" >/dev/null || echo "WARN: http://127.0.0.1:$u not ready"
done
curl -sf http://127.0.0.1:8420/status >/dev/null || echo "WARN: mock-node not ready"

echo "── 1/3  cockpit (dreggnet-attach): goal → stream → verify → tamper ──────"
ATTACH_URL=http://127.0.0.1:8100 node "$HERE/capture-cockpit.mjs"

echo "── 2/3  panes (console / status / landing) ─────────────────────────────"
CONSOLE_URL=http://127.0.0.1:8101 STATUS_URL=http://127.0.0.1:8102 \
  LANDING_URL=http://127.0.0.1:8103 node "$HERE/capture-panes.mjs"

echo "── 3/3  extension (cipherclerk): onboard → login → powerbox ────────────"
EXT_DIR="$EXT_DIR" MOCK_NODE_URL=http://localhost:8420 node "$HERE/capture-extension.mjs"

# drop the raw Playwright-named originals (saveAs left deterministic copies).
rm -f "$OUT_DIR"/page@*.webm
echo "── done. clips in $OUT_DIR ─────────────────────────────────────────────"
ls -la "$OUT_DIR"/*.webm
