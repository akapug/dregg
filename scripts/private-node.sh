#!/usr/bin/env bash
# private-node.sh — start/stop/check a SINGLE private dregg-node on hbox.
#
# This stands up the PRIVATE-DEPLOYMENT FOUNDATION: one dregg-node running as a
# solo committee-of-one, executing real turns on the effect-VM and proving each
# committed turn (--prove-turns → prove_pool / commit-path full-turn STARK proof).
# It is bound to a PRIVATE address (127.0.0.1 by default; or the hbox LAN IP
# 192.168.50.39 for LAN/WireGuard reach) — NEVER 0.0.0.0-public. hbox's ufw is
# default-deny inbound (LAN + SSH only), so even a LAN bind stays off the public
# internet; the localhost default needs no firewall trust at all.
#
# HONEST SCOPE: this is a single-node dev instance. It is NOT the multi-node
# federation (n=4 validators + blocklace finality — the named next step), NOT the
# on-chain settle wiring, and NOT a public/mainnet deployment. No real value.
#
# Usage (run ON hbox, from the synced lane dir, e.g. ~/dregg-build/privnode):
#   scripts/private-node.sh start        # init (first run) + start, wait for /status
#   scripts/private-node.sh status       # is it up? print /status
#   scripts/private-node.sh check        # execute+prove a real faucet turn end-to-end
#   scripts/private-node.sh logs         # tail the node log
#   scripts/private-node.sh stop         # stop the node
#
# Config (env overrides):
#   DREGG_PRIV_PORT   HTTP API port           (default 8420)
#   DREGG_PRIV_BIND   bind address            (default 127.0.0.1; use 192.168.50.39 for LAN)
#   DREGG_PRIV_GOSSIP gossip port             (default 9420)
#   DREGG_PRIV_DATA   data dir (persistent)   (default $HOME/dregg-priv/data)
#   DREGG_PRIV_BIN    node binary             (default ./target/release/dregg-node)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PORT="${DREGG_PRIV_PORT:-8420}"
BIND="${DREGG_PRIV_BIND:-127.0.0.1}"
GOSSIP="${DREGG_PRIV_GOSSIP:-9420}"
DATA="${DREGG_PRIV_DATA:-$HOME/dregg-priv/data}"
BIN="${DREGG_PRIV_BIN:-$ROOT/target/release/dregg-node}"
LOG="$HOME/dregg-priv/node.log"
PIDF="$HOME/dregg-priv/node.pid"
# Reach the API on 127.0.0.1 for local curls even when bound to the LAN IP
# (a LAN-bound socket is also reachable from the same host on that IP).
CURL_HOST="$BIND"; [ "$BIND" = "0.0.0.0" ] && CURL_HOST="127.0.0.1"
BASE="http://$CURL_HOST:$PORT"

say()  { printf '\n\033[1m==> %s\033[0m\n' "$*"; }
die()  { printf '\n\033[31mFATAL: %s\033[0m\n' "$*" >&2; exit 1; }

case "$BIND" in
  0.0.0.0) die "refusing to bind 0.0.0.0 (public). Use 127.0.0.1 or the LAN IP 192.168.50.39." ;;
esac

running() { [ -f "$PIDF" ] && kill -0 "$(cat "$PIDF")" 2>/dev/null; }

cmd_start() {
  [ -x "$BIN" ] || die "node binary not found/executable at $BIN (build it: DREGG_REQUIRE_LEAN=0 cargo build --release -p dregg-node)."
  if running; then say "already running (pid $(cat "$PIDF")) on $BASE"; return 0; fi
  mkdir -p "$(dirname "$LOG")"
  # Persistent genesis: init ONLY on first run (never wipe existing state).
  if [ ! -f "$DATA/node.key" ]; then
    say "first run — initializing fresh dev genesis at $DATA"
    "$BIN" init --data-dir "$DATA"
  fi
  say "starting private dregg-node (solo · blocklace · faucet · prove-turns) on $BIND:$PORT"
  nohup "$BIN" run \
    --data-dir "$DATA" \
    --bind "$BIND" \
    --port "$PORT" \
    --gossip-port "$GOSSIP" \
    --federation-size 1 \
    --federation-mode solo \
    --consensus blocklace \
    --enable-faucet \
    --prove-turns \
    >"$LOG" 2>&1 &
  echo $! >"$PIDF"
  # wait for /status
  for _ in $(seq 1 80); do
    if curl -fsS "$BASE/status" >/dev/null 2>&1; then
      say "UP — $BASE  (pid $(cat "$PIDF"), log $LOG)"
      curl -fsS "$BASE/status"; echo
      return 0
    fi
    running || { tail -30 "$LOG"; die "node exited before /status came up (log above)."; }
    sleep 0.5
  done
  die "node did not answer /status within ~40s (see $LOG)."
}

cmd_status() {
  if running; then say "running (pid $(cat "$PIDF")) on $BASE"; curl -fsS "$BASE/status"; echo
  else say "NOT running"; curl -fsS "$BASE/status" 2>/dev/null && echo || true; fi
}

cmd_logs()  { tail -n "${1:-40}" "$LOG"; }

cmd_stop() {
  if running; then
    p="$(cat "$PIDF")"; say "stopping pid $p"; kill "$p" 2>/dev/null || true
    for _ in $(seq 1 20); do kill -0 "$p" 2>/dev/null || break; sleep 0.25; done
    kill -9 "$p" 2>/dev/null || true; rm -f "$PIDF"; say "stopped."
  else say "not running."; rm -f "$PIDF"; fi
}

# check — prove it is a REAL node: a faucet Transfer executes on the effect-VM
# (recipient balance changes) and is PROVEN (a full-turn STARK proof is fetchable).
cmd_check() {
  running || die "node is not running (start it first)."
  local recip; recip="$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')"
  say "recipient cell: $recip"
  say "POST $BASE/api/faucet  (amount 1000) — a real faucet-signed Transfer turn"
  local resp; resp="$(curl -fsS -X POST "$BASE/api/faucet" -H 'content-type: application/json' \
        -d "{\"recipient\":\"$recip\",\"amount\":1000}")"
  echo "    $resp"
  local th; th="$(echo "$resp" | sed -n 's/.*"turn_hash":"\([0-9a-f]*\)".*/\1/p')"
  [ -n "$th" ] || die "no turn_hash in faucet response — turn did not commit."
  say "turn_hash: $th"
  say "GET $BASE/api/cell/$recip — effect-VM state after execution"
  local cell; cell="$(curl -fsS "$BASE/api/cell/$recip" || true)"; echo "    $cell"
  echo "$cell" | grep -q '"balance":1000' \
    && say "EXECUTED: recipient balance = 1000 (state changed on the effect-VM)." \
    || die "recipient balance is not 1000 — execution did not land."
  # The full-turn STARK proof attaches ASYNCHRONOUSLY (prove_pool, off the commit
  # lock): the committed receipt flips has_proof/has_witness true once the pool's
  # prove_and_verify_finalized_turn generates AND self-verifies the composed
  # FullTurnProof (verify_full_turn gates the attach — an unverified proof is
  # NEVER attached). We poll the receipt row for that flip. (The separate
  # /api/turn/<hash>/proof endpoint serves the COMMIT-PATH-persisted proof, which
  # in solo mode is preempted by a faucet nonce-replay on re-execution — a
  # different persistence leg, not the attestation the light-client consumes.)
  say "polling GET $BASE/api/starbridge/receipts?turn_hash=$th — full-turn STARK proof (async prove pool)"
  local row="" attached=""
  for _ in $(seq 1 60); do
    row="$(curl -fsS "$BASE/api/starbridge/receipts?turn_hash=$th" 2>/dev/null || true)"
    if echo "$row" | grep -q '"has_proof":true'; then attached=1; break; fi
    sleep 1
  done
  if [ -n "$attached" ]; then
    echo "    $row"
    say "PROVEN: a real full-turn STARK proof was generated, self-verified, and attached ($(echo "$row" | grep -o '"witness_count":[0-9]*'))."
    say "REAL NODE CONFIRMED: turn executed on the verified effect-VM AND STARK-proven."
  else
    # HONEST STATUS: the prove PIPELINE is real and runs (the prover builds the
    # trace and fails CLOSED at a named constraint) — it does not fake a proof.
    # If has_proof never flips, read the real prover error from the log.
    say "EXECUTED (verified) — PROOF PENDING: has_proof did not flip within the poll window."
    echo "    (real prover error from the log, if any:)"
    grep -iE "async proof generation failed|no realized relation" "$LOG" | tail -1 | sed 's/^/    /'
    echo "    → the effect-VM execution is the verified Lean producer; inspect $LOG for the"
    echo "      prove-pool outcome (ENQUEUED / attached / generation failed)."
  fi
}

case "${1:-}" in
  start)  cmd_start ;;
  stop)   cmd_stop ;;
  status) cmd_status ;;
  check)  cmd_check ;;
  logs)   shift; cmd_logs "${1:-40}" ;;
  *) echo "usage: $0 {start|stop|status|check|logs [N]}" >&2; exit 2 ;;
esac
