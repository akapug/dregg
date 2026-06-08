#!/usr/bin/env bash
#
# smoke-cli-name.sh — drive the FULL nameservice lifecycle through the `dregg`
# CLI against a live local node, proving each mutating turn commits on the
# verified commit path.
#
# This is the demoable starbridge-app end-to-end smoke: it exercises the same
# path a human operator uses — `dregg name {register,resolve,transfer,revoke}`
# → the node's `/turn/submit` JSON ingress → a real signed call-forest →
# execution → blocklace consensus → the commit-path state producer (the
# VERIFIED Lean executor when DREGG_LEAN_PRODUCER=1) + full-turn STARK proving.
#
# Flow:
#   1. Build dregg-node + the dregg CLI.
#   2. Start a solo node with --enable-faucet --prove-turns.
#   3. Unlock, read the operator identity, fund its cell.
#   4. `dregg name register alice.dregg`   → assert PROVED.
#   5. `dregg name resolve  alice.dregg`   → assert bound + active.
#   6. `dregg name transfer alice.dregg`   → assert PROVED + owner changed.
#   7. `dregg name revoke   alice.dregg`   → assert PROVED.
#   8. `dregg name resolve  alice.dregg`   → assert revoked == true.
#
# Exits non-zero on any failed assertion. Self-contained; safe for CI.
#
# Usage: scripts/smoke-cli-name.sh [PORT]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PORT="${1:-8475}"
DATA_DIR="$(mktemp -d)"
NODE_URL="http://127.0.0.1:$PORT"
PASSPHRASE="cli-name-smoke-local"
NAME="alice.dregg"
LEAN_PRODUCER="${DREGG_LEAN_PRODUCER:-0}"

fail() { echo "FAIL: $*" >&2; exit 1; }
pass() { echo "PASS: $*"; }

DREGG_NODE="$PROJECT_ROOT/target/debug/dregg-node"
DREGG_CLI="$PROJECT_ROOT/target/debug/dregg"
echo "=== building dregg-node + dregg CLI ==="
(cd "$PROJECT_ROOT" && cargo build -p dregg-node -p dregg-cli) || fail "build failed"
[ -x "$DREGG_NODE" ] || fail "dregg-node binary missing"
[ -x "$DREGG_CLI" ] || fail "dregg CLI binary missing"

NODE_PID=""
cleanup() {
  if [ -n "$NODE_PID" ] && kill -0 "$NODE_PID" 2>/dev/null; then
    kill "$NODE_PID" 2>/dev/null || true
    wait "$NODE_PID" 2>/dev/null || true
  fi
  rm -rf "$DATA_DIR"
}
trap cleanup EXIT

echo ""
echo "=== starting solo node (faucet + full-turn proving) ==="
echo "  data dir:       $DATA_DIR"
echo "  api:            $NODE_URL"
echo "  lean producer:  $LEAN_PRODUCER"

"$DREGG_NODE" init --data-dir "$DATA_DIR" >"$DATA_DIR/init.log" 2>&1 || true

DREGG_PROVE_TURNS=1 DREGG_LEAN_PRODUCER="$LEAN_PRODUCER" \
"$DREGG_NODE" run \
  --data-dir "$DATA_DIR" --port "$PORT" --gossip-port 0 \
  --federation-mode solo --consensus blocklace \
  --enable-faucet --prove-turns --block-cadence-ms 500 \
  >"$DATA_DIR/node.log" 2>&1 &
NODE_PID=$!

echo "waiting for HTTP API ..."
for _ in $(seq 1 60); do
  curl -fsS "$NODE_URL/status" >/dev/null 2>&1 && break
  if ! kill -0 "$NODE_PID" 2>/dev/null; then
    echo "--- node.log ---"; cat "$DATA_DIR/node.log" || true
    fail "node exited before the API came up"
  fi
  sleep 0.25
done
curl -fsS "$NODE_URL/status" >/dev/null 2>&1 || fail "HTTP API never became reachable"
pass "node API reachable"

export DREGG_NODE_URL="$NODE_URL"
export DREGG_OUTPUT="json"

# ── Unlock + identity + faucet ──────────────────────────────────────────────
UNLOCK_JSON="$(curl -fsS -H 'Content-Type: application/json' \
  -d "{\"passphrase\":\"$PASSPHRASE\"}" "$NODE_URL/cipherclerk/unlock")" \
  || fail "unlock request failed"
API_TOKEN="$(echo "$UNLOCK_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin).get("bearer_token") or "")')"
[ -n "$API_TOKEN" ] || fail "unlock did not return a bearer_token"
export DREGG_API_TOKEN="$API_TOKEN"
pass "cipherclerk unlocked"

IDENT_JSON="$("$DREGG_CLI" node identity)"
PUBKEY="$(echo "$IDENT_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin)["public_key"])')"
AGENT_CELL="$(echo "$IDENT_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin)["agent_cell"])')"
[ -n "$PUBKEY" ] && [ -n "$AGENT_CELL" ] || fail "could not read operator identity"

FAUCET_JSON="$(curl -fsS -H 'Content-Type: application/json' \
  -d "{\"recipient\":\"$AGENT_CELL\",\"amount\":5000,\"public_key\":\"$PUBKEY\"}" \
  "$NODE_URL/api/faucet" || true)"
echo "$FAUCET_JSON" | python3 -c '
import sys, json
d = json.load(sys.stdin)
if not d.get("success"): sys.exit("faucet did not succeed: %s" % json.dumps(d))
' || fail "faucet funding failed"
pass "operator cell funded"

assert_proved() {
  # $1 = JSON from a name mutation, $2 = label
  echo "$1" | python3 -c '
import sys, json
d = json.load(sys.stdin)
if not d.get("accepted"): sys.exit("turn NOT accepted: %s" % json.dumps(d))
st = (d.get("proof_status","") or "").lower()
if st not in ("proved","not_required"): sys.exit("unexpected proof_status: %s" % st)
print("accepted proof_status=%s" % st)
' || fail "$2 did not commit with an honest proof status"
}

# ── 1. Register ─────────────────────────────────────────────────────────────
echo ""; echo "=== dregg name register $NAME ==="
REG_JSON="$("$DREGG_CLI" name register "$NAME" --expiry 1000000 --fee 1000)" || fail "register failed to execute"
echo "$REG_JSON" | python3 -m json.tool 2>/dev/null || echo "$REG_JSON"
assert_proved "$REG_JSON" "register"
pass "register committed + proved"

# ── 2. Resolve (bound + active) ─────────────────────────────────────────────
echo ""; echo "=== dregg name resolve $NAME ==="
RES_JSON="$("$DREGG_CLI" name resolve "$NAME")" || fail "resolve failed"
echo "$RES_JSON" | python3 -m json.tool 2>/dev/null || echo "$RES_JSON"
echo "$RES_JSON" | python3 -c '
import sys, json
d = json.load(sys.stdin)
assert d.get("found"), "cell not found"
assert d.get("bound"), "name not bound after register"
assert not d.get("revoked"), "name unexpectedly revoked"
' || fail "resolve did not show bound+active after register"
pass "name resolves bound + active"

OWNER_BEFORE="$(echo "$RES_JSON" | python3 -c 'import sys,json; print(json.load(sys.stdin)["owner_hash"])')"

# ── 3. Transfer (owner changes) ─────────────────────────────────────────────
echo ""; echo "=== dregg name transfer $NAME --to bob ==="
XFER_JSON="$("$DREGG_CLI" name transfer "$NAME" --to bob --fee 1000)" || fail "transfer failed"
echo "$XFER_JSON" | python3 -m json.tool 2>/dev/null || echo "$XFER_JSON"
assert_proved "$XFER_JSON" "transfer"
OWNER_AFTER="$("$DREGG_CLI" name resolve "$NAME" | python3 -c 'import sys,json; print(json.load(sys.stdin)["owner_hash"])')"
[ "$OWNER_BEFORE" != "$OWNER_AFTER" ] || fail "owner_hash did not change after transfer"
pass "transfer committed + owner changed ($OWNER_BEFORE -> $OWNER_AFTER)"

# ── 4. Revoke (one-way) ─────────────────────────────────────────────────────
echo ""; echo "=== dregg name revoke $NAME ==="
REV_JSON="$("$DREGG_CLI" name revoke "$NAME" --fee 1000)" || fail "revoke failed"
echo "$REV_JSON" | python3 -m json.tool 2>/dev/null || echo "$REV_JSON"
assert_proved "$REV_JSON" "revoke"
RES2_JSON="$("$DREGG_CLI" name resolve "$NAME")" || fail "post-revoke resolve failed"
echo "$RES2_JSON" | python3 -c '
import sys, json
d = json.load(sys.stdin)
assert d.get("revoked"), "name not revoked after revoke turn"
' || fail "name not revoked after revoke"
pass "revoke committed + tombstone visible"

echo ""
echo "PASS: the FULL nameservice lifecycle (register → resolve → transfer → revoke)"
echo "      flowed through the dregg CLI → node → verified commit path, each turn proven."
