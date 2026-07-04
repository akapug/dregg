#!/usr/bin/env bash
# run-node-10min.sh — from a fresh checkout to a running, health-checked dregg-node in ~10 minutes.
#
# The honest one-script path referenced by QUICKSTART.md. It:
#   1. tries to link the VERIFIED Lean executor via the seed release artifact (minutes), and
#      cleanly falls back to (or lets you choose) a MARSHAL-ONLY build when no seed is available;
#   2. builds dregg-node;
#   3. inits a data dir + starts the node with the faucet on;
#   4. curls /status and REPORTS whether the running node is verified (state_producer:lean) or
#      marshal-only, plus a faucet round-trip to prove a real turn lands.
#
# Usage:
#   scripts/run-node-10min.sh                 # verified if a seed is fetchable, else prompt
#   DREGG_SEED_MODE=marshal scripts/run-node-10min.sh   # skip the seed; marshal-only on purpose
#   DREGG_SEED_MODE=verified scripts/run-node-10min.sh  # require verified; fail if no seed
#   DREGG_NODE_PORT=8421 DREGG_DATA_DIR=/tmp/my-dregg scripts/run-node-10min.sh
#
# It leaves the node RUNNING in the background and prints how to stop it.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
PORT="${DREGG_NODE_PORT:-8421}"
DATA="${DREGG_DATA_DIR:-/tmp/dregg-10min}"
MODE="${DREGG_SEED_MODE:-auto}"     # auto | verified | marshal
PROFILE_DIR=debug
CARGO_FLAGS=()

say()  { printf '\n\033[1m==> %s\033[0m\n' "$*"; }
warn() { printf '\033[33m    %s\033[0m\n' "$*"; }
die()  { printf '\n\033[31mFATAL: %s\033[0m\n' "$*" >&2; exit 1; }

command -v cargo >/dev/null 2>&1 || die "cargo not on PATH — install Rust (https://rustup.rs)."
command -v curl  >/dev/null 2>&1 || die "curl not on PATH."

# ── 1. seed (verified path) ───────────────────────────────────────────────────
seed_present() { [ -f dregg-lean-ffi/libdregg_lean.a ]; }
have_lean_toolchain() { command -v lake >/dev/null 2>&1; }

want_verified=0
case "$MODE" in
  verified) want_verified=1 ;;
  marshal)  want_verified=0 ;;
  auto)     want_verified=1 ;;   # try; degrade gracefully
  *) die "DREGG_SEED_MODE must be auto|verified|marshal (got '$MODE')" ;;
esac

if [ "$want_verified" -eq 1 ]; then
  say "Verified path: ensuring the Lean seed is present"
  if seed_present; then
    warn "seed already present ($(du -h dregg-lean-ffi/libdregg_lean.a | cut -f1 | tr -d ' '))."
  elif scripts/fetch-lean-seed.sh; then
    :
  else
    if [ "$MODE" = "verified" ]; then
      die "could not fetch a verified seed and DREGG_SEED_MODE=verified. Cut a seed release (see
  docs/LEAN-SEED-ARTIFACT.md) or run ./scripts/bootstrap.sh (slow), then re-run."
    fi
    warn "no seed available — falling back to a MARSHAL-ONLY (un-verified) build."
    warn "to get a verified node: cut a seed release (docs/LEAN-SEED-ARTIFACT.md) or ./scripts/bootstrap.sh."
    want_verified=0
  fi
fi

if [ "$want_verified" -eq 1 ]; then
  if ! have_lean_toolchain; then
    if [ "$MODE" = "verified" ]; then
      die "the seed is present but elan/lake is not on PATH — the seed links against the Lean
  toolchain runtime. Install elan: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh"
    fi
    warn "elan/lake not on PATH — the seed can't link without the toolchain; building marshal-only."
    warn "install elan (minutes, no mathlib compile) for the verified node: https://elan.lean-lang.org"
    want_verified=0
  else
    # Make the sysroot explicit so the build never falls back to marshal-only for a lookup miss.
    if [ -z "${DREGG_LEAN_SYSROOT:-}" ]; then
      sr="$(cd metatheory && lake env printenv LEAN_SYSROOT 2>/dev/null || true)"
      [ -n "$sr" ] && export DREGG_LEAN_SYSROOT="$sr" && warn "DREGG_LEAN_SYSROOT=$sr"
    fi
    export DREGG_REQUIRE_LEAN=1    # fail loud rather than silently degrade
  fi
fi

# ── 2. build ──────────────────────────────────────────────────────────────────
say "Building dregg-node (first build links the Lean archive — a few minutes)"
if [ "$want_verified" -eq 1 ]; then
  cargo build -p dregg-node || die "verified build failed — read the panic above (usually a stale
  seed vs Lean HEAD, or a missing toolchain). See docs/BUILD-LEAN-LINKED-NODE.md."
else
  DREGG_REQUIRE_LEAN=0 cargo build -p dregg-node || die "marshal-only build failed."
fi
BIN="target/$PROFILE_DIR/dregg-node"
[ -x "$BIN" ] || die "node binary not found at $BIN"

# ── 3. run ────────────────────────────────────────────────────────────────────
say "Starting the node (data dir $DATA, port $PORT, faucet on)"
rm -rf "$DATA"; "$BIN" init --data-dir "$DATA" >/dev/null
"$BIN" run --data-dir "$DATA" --enable-faucet --port "$PORT" >"$DATA/node.log" 2>&1 &
NODE_PID=$!
# wait for /status to answer (up to ~30s).
ok=0
for _ in $(seq 1 60); do
  if curl -fs "http://localhost:$PORT/status" >/dev/null 2>&1; then ok=1; break; fi
  sleep 0.5
done
[ "$ok" -eq 1 ] || { cat "$DATA/node.log" | tail -20; die "node did not answer /status (pid $NODE_PID). Log above."; }

# ── 4. verify ─────────────────────────────────────────────────────────────────
say "Node is up — /status:"
STATUS="$(curl -fs "http://localhost:$PORT/status")"
echo "    $STATUS"
# NB: extract with POSIX BRE only ([a-z]* — NOT \|, which BSD/macOS sed does not support).
producer="$(echo "$STATUS" | sed -n 's/.*"state_producer":"\([^"]*\)".*/\1/p')"
leanp="$(echo "$STATUS" | sed -n 's/.*"lean_producer":\([a-z][a-z]*\).*/\1/p')"

say "Faucet round-trip (a real verified turn lands)"
CID="$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')"
FR="$(curl -fs -X POST "http://localhost:$PORT/api/faucet" -H 'content-type: application/json' \
      -d "{\"recipient\":\"$CID\",\"amount\":1000}" || true)"
echo "    $FR"

echo
if [ "$producer" = "lean" ] && [ "$leanp" = "true" ]; then
  printf '\033[32m==> VERIFIED node running: state_producer=lean (the proved Lean executor).\033[0m\n'
else
  printf '\033[33m==> MARSHAL-ONLY node running: state_producer=%s (un-verified Rust executor).\033[0m\n' "${producer:-?}"
  printf '    For a verified node: fetch a seed (scripts/fetch-lean-seed.sh) + elan, then re-run.\n'
fi
cat <<EOF

  Node PID: $NODE_PID   ·   log: $DATA/node.log   ·   http://localhost:$PORT
  Try:   curl -s http://localhost:$PORT/status
         curl -s http://localhost:$PORT/api/cell/$CID
  Stop:  kill $NODE_PID
  Next:  QUICKSTART.md (§2 the CLI, §4 the guided demo, §9 the federation read surface)
EOF
