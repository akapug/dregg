#!/bin/bash
# Generate the 3-member devnet federation identity ON THE INSTANCE and install
# each validator's key + the shared genesis into the three per-node data dirs.
#
#   validator node-0  →  /opt/dregg-data    (dregg-gateway, the public face)
#   validator node-1  →  /opt/dregg-data-2  (dregg-node@2, internal)
#   validator node-2  →  /opt/dregg-data-3  (dregg-node@3, internal)
#
# Master copies land in /etc/dregg/federation (root-owned, mode 0750). Keys
# are generated HERE and are NEVER committed to the repo.
#
# ⚠ CHAIN RESET: a fresh genesis derives a NEW federation_id (it is a
# commitment to the committee pubkeys), so the existing solo-gateway chain
# state cannot be carried forward. This script REFUSES to touch a data dir
# that contains a live store (dregg.redb); archive it first — the runbook's
# step 2 (deploy/aws/N3-RUNBOOK.md) is:
#   sudo systemctl stop dregg-gateway
#   sudo mv /opt/dregg-data /opt/dregg-data.pre-federation.$(date +%Y%m%d%H%M%S)
#
# Usage (as root on the instance):
#   sudo /opt/dregg/deploy/aws/federation-keygen.sh [--force]
#
# --force regenerates the master copies in /etc/dregg/federation (a brand-new
# committee). It still refuses to overwrite a live dregg.redb.
set -euo pipefail

REPO_DIR="${REPO_DIR:-/opt/dregg}"
BIN="$REPO_DIR/target/release/dregg-node"
OUT="${OUT:-/etc/dregg/federation}"

GW_DATA=/opt/dregg-data
N2_DATA=/opt/dregg-data-2
N3_DATA=/opt/dregg-data-3

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
  FORCE=1
elif [[ $# -gt 0 ]]; then
  echo "usage: $0 [--force]" >&2
  exit 2
fi

if [[ "$(id -u)" -ne 0 ]]; then
  echo "ERROR: run as root (sudo $0)" >&2
  exit 1
fi

if [[ ! -x "$BIN" ]]; then
  echo "ERROR: $BIN not found. Build it first:" >&2
  echo "  cd $REPO_DIR && cargo build --release -p dregg-node" >&2
  exit 1
fi

if ! id dregg &>/dev/null; then
  echo "ERROR: the 'dregg' system user does not exist (run deploy/aws/setup.sh first)" >&2
  exit 1
fi

# Never install over a live chain store, --force or not.
for d in "$GW_DATA" "$N2_DATA" "$N3_DATA"; do
  if [[ -e "$d/dregg.redb" ]]; then
    echo "ERROR: $d contains a live store ($d/dregg.redb)." >&2
    echo "Stop the service and archive the directory first, e.g.:" >&2
    echo "  sudo systemctl stop dregg-gateway dregg-node@2 dregg-node@3" >&2
    echo "  sudo mv $d $d.pre-federation.\$(date +%Y%m%d%H%M%S)" >&2
    exit 1
  fi
done

if [[ -e "$OUT/genesis.json" && $FORCE -eq 0 ]]; then
  echo "ERROR: $OUT/genesis.json already exists. Re-run with --force to mint a" >&2
  echo "brand-new committee (chain reset), or install the existing one by hand." >&2
  exit 1
fi

# ── Generate ─────────────────────────────────────────────────────────────────
install -d -m 0750 -o root -g dregg "$OUT"
if [[ $FORCE -eq 1 ]]; then
  rm -f "$OUT"/genesis.json "$OUT"/.devnet "$OUT"/node-*.key "$OUT"/node-*.env \
        "$OUT"/agent-*.key "$OUT"/faucet.key
fi

echo "=== Generating 3-validator federation genesis in $OUT ==="
"$BIN" genesis \
  --validators 3 \
  --epoch-length 100 \
  --checkpoint-interval 10 \
  --output "$OUT"

# The generated node-*.env files use docker-compose style hostname peers
# (node-0:9420) which this host's peer parser does NOT accept; the real env
# files come from deploy/aws/node-{2,3}.env.example. Remove them so nobody
# installs them by mistake.
rm -f "$OUT"/node-*.env

# Validate the genesis JSON parses before installing anywhere.
python3 -c "import json,sys; json.load(open('$OUT/genesis.json'))" \
  || { echo "ERROR: generated genesis.json does not parse" >&2; exit 1; }

# ── Install per instance ─────────────────────────────────────────────────────
install_node() {
  local validator_idx="$1" data_dir="$2"
  install -d -o dregg -g dregg "$data_dir"
  install -m 600 -o dregg -g dregg "$OUT/node-$validator_idx.key" "$data_dir/node.key"
  install -m 640 -o dregg -g dregg "$OUT/genesis.json" "$data_dir/genesis.json"
  install -m 640 -o dregg -g dregg "$OUT/.devnet" "$data_dir/.devnet"
  echo "  validator node-$validator_idx → $data_dir"
}

echo "=== Installing validator identities ==="
install_node 0 "$GW_DATA"
install_node 1 "$N2_DATA"
install_node 2 "$N3_DATA"

FEDERATION_ID="$(jq -r '.federation_id' "$OUT/genesis.json")"

echo ""
echo "=== Federation identity generated ==="
echo "  federation_id: $FEDERATION_ID"
echo "  threshold:     $(jq -r '.threshold' "$OUT/genesis.json")"
jq -r '.validators[] | "  \(.name): \(.public_key)"' "$OUT/genesis.json"
echo ""
echo "Next steps (full order in deploy/aws/N3-RUNBOOK.md):"
echo "  1. install /etc/dregg/node-2.env and node-3.env from the .example files"
echo "  2. install dregg-node@.service + the dregg-gateway federation drop-in"
echo "  3. update FEDERATION_ID=$FEDERATION_ID in /etc/dregg/discord-bot.env"
echo "  4. systemctl daemon-reload && start node@2, node@3, then dregg-gateway"
