#!/usr/bin/env bash
# run-gate.sh — the launchpad-web GATE.
#
# Spins a local anvil, deploys the REAL DreggLaunchpad (forge — solc compile is
# local; no cargo), starts the backend indexer/API against it, then runs the e2e
# driver that puts the deployed contract through a full fair launch and checks the
# REST API. Reports PASS/FAIL and tears everything down.
#
#   bash gate/run-gate.sh
set -uo pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
CHAIN="$REPO/chain"
RPC="http://127.0.0.1:8545"
PORT="${PORT:-8785}"
KEY="0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80" # anvil #0

ANVIL_PID=""; SERVER_PID=""
cleanup() { [ -n "$SERVER_PID" ] && kill "$SERVER_PID" 2>/dev/null; [ -n "$ANVIL_PID" ] && kill "$ANVIL_PID" 2>/dev/null; }
trap cleanup EXIT

echo "== 1. anvil =="
pkill -f "anvil.*8545" 2>/dev/null; sleep 0.5
anvil --silent --port 8545 & ANVIL_PID=$!
for i in $(seq 1 40); do cast block-number --rpc-url "$RPC" >/dev/null 2>&1 && break; sleep 0.25; done
echo "   anvil up (pid $ANVIL_PID)"

echo "== 2. deploy DreggLaunchpad (forge create) =="
cd "$CHAIN"
OUT="$(forge create contracts/launchpad/DreggLaunchpad.sol:DreggLaunchpad \
        --rpc-url "$RPC" --private-key "$KEY" --broadcast --json 2>err.log)"
ADDRESS="$(printf '%s' "$OUT" | node -e 'let s="";process.stdin.on("data",d=>s+=d).on("end",()=>{const m=s.match(/"deployedTo"\s*:\s*"(0x[0-9a-fA-F]+)"/);console.log(m?m[1]:"")})')"
if [ -z "$ADDRESS" ] || [ "$ADDRESS" = "undefined" ]; then echo "   deploy FAILED"; cat err.log; exit 2; fi
echo "   DreggLaunchpad @ $ADDRESS"

echo "== 3. backend indexer + API =="
cd "$HERE"
LAUNCHPAD_RPC="$RPC" LAUNCHPAD_ADDRESS="$ADDRESS" PORT="$PORT" node server.mjs & SERVER_PID=$!
for i in $(seq 1 40); do curl -s "http://localhost:$PORT/api/config" >/dev/null 2>&1 && break; sleep 0.25; done
echo "   server up (pid $SERVER_PID) → http://localhost:$PORT"

echo "== 4. e2e driver (real contract lifecycle + REST checks) =="
RPC="$RPC" ADDRESS="$ADDRESS" SERVER="http://localhost:$PORT" node "$HERE/gate/e2e.mjs"
RC=$?

echo "== gate exit $RC =="
exit $RC
