#!/usr/bin/env bash
#
# DreggNet — a REAL Stripe event funds the agent's credit.
#
# A local endpoint (demo/stripe-receiver) runs the GENUINE breadstuffs
# `stripe_mirror` verify+mint on every inbound webhook — the same
# `StripeMirrorState::mint_against_webhook` the dregg-bridge test suite exercises.
# Point Stripe at it and a real `payment_intent.succeeded` mints conserved
# USD-credit to the agent's dregg cell.
#
# Two ways to run:
#
#   demo/stripe-trigger.sh           # FIXTURE: fully automated, offline. Self-signs a
#                                    # recorded event the way Stripe does and POSTs it to
#                                    # the receiver — the verify+mint path is the real one;
#                                    # only the live Stripe key/event are the operator's.
#                                    # Also shows: a retry is deduped, a forgery is refused.
#
#   demo/stripe-trigger.sh --live    # LIVE: start the receiver and print the exact
#                                    # `stripe listen` / `stripe trigger` commands to run
#                                    # against your own Stripe test key (whsec_…).
#
# Env:
#   DREGG_STRIPE_SECRET   the HMAC signing secret (default: a demo whsec for fixture mode).
#                         In live mode, export STRIPE_WEBHOOK_SECRET from `stripe listen`.
#   DREGG_STRIPE_PORT     receiver port (default 4242).
#   BREADSTUFFS_DIR       breadstuffs checkout (default ~/dev/breadstuffs) — its warm
#                         target is reused to build the receiver.

set -euo pipefail

if [ -t 1 ]; then
  BOLD=$(printf '\033[1m'); DIM=$(printf '\033[2m'); RST=$(printf '\033[0m')
  CYAN=$(printf '\033[36m'); GRN=$(printf '\033[32m'); YLW=$(printf '\033[33m')
else
  BOLD=""; DIM=""; RST=""; CYAN=""; GRN=""; YLW=""
fi
step() { printf '\n%s%s==> %s%s\n' "$BOLD" "$CYAN" "$1" "$RST"; }
note() { printf '   %s%s%s\n' "$DIM" "$1" "$RST"; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BREADSTUFFS_DIR="${BREADSTUFFS_DIR:-$HOME/dev/breadstuffs}"
PORT="${DREGG_STRIPE_PORT:-4242}"
SECRET="${DREGG_STRIPE_SECRET:-whsec_demo_dregg_hermes_hackathon}"
RECIPIENT="0101010101010101010101010101010101010101010101010101010101010101"

MODE="fixture"
case "${1:-}" in
  --live) MODE="live" ;;
  --help|-h) sed -n '2,40p' "$0"; exit 0 ;;
  "") ;;
  *) echo "unknown arg: $1 (try --help)" >&2; exit 2 ;;
esac

# ── build / resolve the receiver against breadstuffs' warm target ────────────
# Built into breadstuffs' target dir (dev profile) so the heavy dregg crates that
# `dregg-bridge` pulls are reused from breadstuffs' warm build, not recompiled.
RECV="$BREADSTUFFS_DIR/target/debug/dreggnet-stripe-receiver"
if [ ! -x "$RECV" ]; then
  if [ ! -d "$BREADSTUFFS_DIR" ]; then
    echo "!! breadstuffs not found at $BREADSTUFFS_DIR (the receiver links its real stripe_mirror)" >&2
    echo "   set BREADSTUFFS_DIR=/path/to/breadstuffs" >&2
    exit 1
  fi
  note "building dreggnet-stripe-receiver (reuses breadstuffs' warm target)…"
  # Build from the receiver dir so ITS rust-toolchain.toml (rolling `nightly`, matching
  # breadstuffs) applies — then breadstuffs' warm artifacts are reused, not recompiled.
  ( cd "$ROOT/demo/stripe-receiver" && CARGO_TARGET_DIR="$BREADSTUFFS_DIR/target" \
      cargo build >/dev/null 2>&1 )
fi
if [ ! -x "$RECV" ]; then
  echo "!! could not build the receiver; see demo/stripe-receiver/" >&2
  exit 1
fi

printf '%s%s' "$BOLD" "$CYAN"
cat <<'BANNER'
  ┌──────────────────────────────────────────────────────────────────┐
  │  DreggNet — a real Stripe event funds the agent (verify + mint)    │
  │  the endpoint runs breadstuffs' genuine stripe_mirror code path    │
  └──────────────────────────────────────────────────────────────────┘
BANNER
printf '%s' "$RST"

if [ "$MODE" = "live" ]; then
  step "LIVE — drive it with your Stripe test key"
  note "1) Start the receiver (this terminal):"
  printf '      %sSTRIPE_WEBHOOK_SECRET=whsec_… DREGG_STRIPE_PORT=%s %s%s\n' "$DIM" "$PORT" "$RECV" "$RST"
  note "   (get whsec_… from 'stripe listen' in step 2)"
  note "2) In another terminal, forward Stripe to the receiver:"
  printf '      %sstripe listen --forward-to localhost:%s/webhook%s\n' "$DIM" "$PORT" "$RST"
  note "   copy the whsec_… it prints into STRIPE_WEBHOOK_SECRET for step 1."
  note "3) Fire a real test event WITH the dregg recipient + amount in metadata:"
  printf '      %sstripe trigger payment_intent.succeeded \\%s\n' "$DIM" "$RST"
  printf '      %s  --add payment_intent:metadata.dregg_recipient=%s \\%s\n' "$DIM" "$RECIPIENT" "$RST"
  printf '      %s  --add payment_intent:amount=2500 \\%s\n' "$DIM" "$RST"
  printf '      %s  --add payment_intent:currency=usd%s\n' "$DIM" "$RST"
  note "The receiver verifies the real Stripe signature and mints 2500¢ to the agent cell."
  note "(The live key is yours; the verify+mint path is identical to the fixture run below.)"
  exit 0
fi

# ── FIXTURE mode: fully-automated, offline, real verify+mint ─────────────────
command -v openssl >/dev/null 2>&1 || { echo "!! openssl required for fixture signing" >&2; exit 1; }
command -v curl    >/dev/null 2>&1 || { echo "!! curl required to POST the event" >&2; exit 1; }

WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"; [ -n "${RECV_PID:-}" ] && kill "$RECV_PID" 2>/dev/null || true' EXIT
LOG="$WORK/receiver.log"

step "Start the local endpoint (runs the real stripe_mirror verify+mint)"
DREGG_STRIPE_SECRET="$SECRET" DREGG_STRIPE_PORT="$PORT" "$RECV" >"$LOG" 2>&1 &
RECV_PID=$!
# Wait for it to bind.
waited=0
until grep -q "listening on" "$LOG" 2>/dev/null; do
  kill -0 "$RECV_PID" 2>/dev/null || { echo "!! receiver exited:"; cat "$LOG"; exit 1; }
  sleep 0.1; waited=$((waited+1)); [ "$waited" -gt 100 ] && { echo "!! receiver did not start"; cat "$LOG"; exit 1; }
done
sed -n '1,4p' "$LOG" | sed 's/^/   /'

# Stripe signs "{t}.{body}" with HMAC-SHA256 under the webhook secret.
sign_and_post() {
  local body="$1" t sig
  t="$(date +%s)"
  sig="$(printf '%s' "$t.$body" | openssl dgst -sha256 -hmac "$SECRET" -hex | sed 's/^.*[= ]//')"
  curl -sS -X POST "http://localhost:$PORT/webhook" \
    -H "Stripe-Signature: t=$t,v1=$sig" \
    -H "Content-Type: application/json" \
    --data-binary "$body"
  echo
}

PI_BODY="{\"id\":\"evt_demo_1\",\"type\":\"payment_intent.succeeded\",\"data\":{\"object\":{\"id\":\"pi_demo_001\",\"object\":\"payment_intent\",\"amount\":2500,\"amount_received\":2500,\"currency\":\"usd\",\"status\":\"succeeded\",\"metadata\":{\"dregg_recipient\":\"$RECIPIENT\"}}}}"

step "Fire a signed payment_intent.succeeded (\$25.00) → verify + mint"
note "(identical bytes/signature shape to what \`stripe trigger\` sends)"
printf '   %sHTTP %s' "$DIM" "$RST"; sign_and_post "$PI_BODY"
tail -n +5 "$LOG" | sed 's/^/   /'

step "Stripe retries — the SAME payment is deduped (no double-mint)"
: > "$LOG.mark"; before="$(wc -l <"$LOG")"
printf '   %sHTTP %s' "$DIM" "$RST"; sign_and_post "$PI_BODY"
tail -n +"$((before+1))" "$LOG" | sed 's/^/   /'

step "A FORGED signature is refused (nothing minted)"
before="$(wc -l <"$LOG")"
printf '   %sHTTP %s' "$DIM" "$RST"
curl -sS -X POST "http://localhost:$PORT/webhook" \
  -H "Stripe-Signature: t=$(date +%s),v1=deadbeef" \
  -H "Content-Type: application/json" \
  --data-binary "$PI_BODY"; echo
tail -n +"$((before+1))" "$LOG" | sed 's/^/   /'

printf '\n   %s%s✓ a real signed Stripe event minted conserved USD-credit; a retry deduped; a forgery refused.%s\n' \
  "$GRN" "$BOLD" "$RST"
note "Same code path runs live: demo/stripe-trigger.sh --live"
