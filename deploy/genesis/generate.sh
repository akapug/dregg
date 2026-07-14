#!/bin/bash
# Generate a testnet genesis state using the canonical dregg-node genesis command.
#
# THE RE-GENESIS (2026-07): a fresh committee for the dregg games/beacon testnet.
# Every validator enrolls BOTH an ed25519 AND an ML-DSA-65 (FIPS 204) key
# (node/src/genesis.rs), so the committee can furnish the HYBRID (ed25519 ∧
# ML-DSA-65) finalization quorum the beacon's PQ finalized-root half consumes.
# Default committee size is 4 (n>=4 gives one-fault slack; n=3 is unanimity-fragile).
#
# Usage:
#   cd deploy/genesis
#   ./generate.sh            # generate (refuses if a genesis already exists)
#   ./generate.sh --force    # regenerate from scratch (invalidates existing state)
#
# Config (env overridable):
#   FED_VALIDATORS   committee size            (default 4; use 4+)
#   FED_EPOCH_LENGTH epoch length              (default 100)
#   FED_CHECKPOINT   checkpoint interval       (default 10)
#   GENESIS_KEYS_DIR where PRIVATE keys land   (default ./secrets — GITIGNORED)
#                    Point this at an out-of-tree path (e.g. ~/dregg-secrets) to
#                    keep private keys entirely outside the repo.
#   DREGG_DEPLOY_HOST demo/testnet host        (default demo.dregg.net)
#
# KEY PLACEMENT: only the PUBLIC genesis.json is written into this tracked
# directory (deploy/genesis/genesis.json — the committee's public keys, the
# enrolled ML-DSA roster, the threshold, the config). Every PRIVATE key
# (node-*.key, issuer/fee/faucet/agent-*.key) is written to GENESIS_KEYS_DIR and
# is NEVER committed (deploy/genesis/secrets/ + deploy/genesis/*.key are
# gitignored). Do NOT move private keys into the tracked tree.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

FED_VALIDATORS="${FED_VALIDATORS:-4}"
FED_EPOCH_LENGTH="${FED_EPOCH_LENGTH:-100}"
FED_CHECKPOINT="${FED_CHECKPOINT:-10}"
GENESIS_KEYS_DIR="${GENESIS_KEYS_DIR:-$SCRIPT_DIR/secrets}"
DREGG_DEPLOY_HOST="${DREGG_DEPLOY_HOST:-demo.dregg.net}"

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
  FORCE=1
elif [[ $# -gt 0 ]]; then
  echo "usage: $0 [--force]" >&2
  exit 2
fi

cd "$SCRIPT_DIR"

if [[ -e "genesis.json" && $FORCE -eq 0 ]]; then
  echo "ERROR: deploy/genesis/genesis.json already exists."
  echo "Use --force to regenerate (this will invalidate existing testnet state)."
  exit 1
fi

if [[ $FORCE -eq 1 ]]; then
  rm -f genesis.json .devnet node-*.key node-*.env
  rm -rf keys "$GENESIS_KEYS_DIR"
fi

mkdir -p "$GENESIS_KEYS_DIR"

echo "=== Generating testnet genesis state (n=$FED_VALIDATORS, HYBRID ML-DSA roster) ==="
echo "Private keys -> $GENESIS_KEYS_DIR  (NEVER committed)"

cd "$REPO_DIR"
cargo run --release -p dregg-node -- genesis \
  --validators "$FED_VALIDATORS" \
  --epoch-length "$FED_EPOCH_LENGTH" \
  --checkpoint-interval "$FED_CHECKPOINT" \
  --output "$GENESIS_KEYS_DIR"

# Publish ONLY the public manifest into the tracked directory.
cp "$GENESIS_KEYS_DIR/genesis.json" "$SCRIPT_DIR/genesis.json"

echo ""
echo "=== Genesis state generated ==="
echo ""
echo "Public manifest (tracked):"
echo "  deploy/genesis/genesis.json      committee public keys + ML-DSA roster + threshold"
echo ""
echo "Private material (in $GENESIS_KEYS_DIR — GITIGNORED, do NOT commit):"
echo "  node-*.key    validator private keys (each derives its ed25519 + ML-DSA-65 key)"
echo "  *-well.key / agent-*.key  seed cell keys"
echo "  node-*.env    per-validator environment files"
echo ""
echo "Deploy the PUBLIC manifest to the demo/testnet host:"
echo "  scp deploy/genesis/genesis.json ${DREGG_DEPLOY_HOST}:/opt/dregg-data/"
echo "  ssh ${DREGG_DEPLOY_HOST} sudo systemctl restart dregg-gateway"
echo ""
echo "WARNING: These keys are for TESTNET use only. Do NOT use in production."
