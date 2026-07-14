#!/usr/bin/env bash
# make-receipt.sh — produce the STATIC verifiable-receipt page from a REAL local
# launch. Spins a local anvil, deploys the real DreggLaunchpad (forge), drives a
# full fair launch through it, reads every number back from the chain, and writes
# launchpad-web/public/receipt.html — a shareable artifact whose every field a
# reader can recompute from the chain. Zero external exposure; nothing broadcast.
#
#   bash gate/make-receipt.sh
set -uo pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
CHAIN="$REPO/chain"
RPC="http://127.0.0.1:8545"
KEY="0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80" # anvil #0

ANVIL_PID=""
cleanup() { [ -n "$ANVIL_PID" ] && kill "$ANVIL_PID" 2>/dev/null; }
trap cleanup EXIT

echo "== anvil =="
pkill -f "anvil.*8545" 2>/dev/null; sleep 0.5
anvil --silent --port 8545 & ANVIL_PID=$!
for i in $(seq 1 40); do cast block-number --rpc-url "$RPC" >/dev/null 2>&1 && break; sleep 0.25; done

echo "== deploy DreggLaunchpad =="
cd "$CHAIN"
OUT="$(forge create contracts/launchpad/DreggLaunchpad.sol:DreggLaunchpad \
        --rpc-url "$RPC" --private-key "$KEY" --broadcast --json 2>err.log)"
ADDRESS="$(printf '%s' "$OUT" | node -e 'let s="";process.stdin.on("data",d=>s+=d).on("end",()=>{const m=s.match(/"deployedTo"\s*:\s*"(0x[0-9a-fA-F]+)"/);console.log(m?m[1]:"")})')"
if [ -z "$ADDRESS" ]; then echo "   deploy FAILED"; cat err.log; exit 2; fi
echo "   DreggLaunchpad @ $ADDRESS"

echo "== drive launch + emit receipt =="
cd "$HERE"
RPC="$RPC" ADDRESS="$ADDRESS" node gate/receipt.mjs
echo "== done → launchpad-web/public/receipt.html =="
