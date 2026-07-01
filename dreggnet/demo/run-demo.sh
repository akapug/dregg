#!/usr/bin/env bash
#
# DreggNet — the agent-business loop, end to end.
#
#   "An agent earns/holds value → pays via Stripe → spends it on a dregg
#    execution-lease → runs real, durable, metered compute on DreggNet."
#
# This is a TWO-REPO demo by design:
#
#   * dregg (AGPL, public — ~/dev/breadstuffs): the verified payment + lease RAIL.
#       Stripe webhook → conserving USD-credit mint → resolve_pay → execution-lease.
#   * DreggNet (AGPL, here): the thing that actually RUNS the workload —
#       a metered, crash-resumable durable polyana job in a wasm sandbox.
#
# The two halves are licensed apart and live in separate repos, so this is a
# scripted narrative that drives BOTH. Every step below is labelled:
#
#       [REAL]      a genuine code path executes (a passing test / a real binary).
#       [NARRATED]  the autonomous-agent framing around those real steps.
#
# Nothing here claims more than runs. The Stripe→mint→pay-lease rail is exercised
# as the dregg crates' own tests; the durable metered exec is the dreggnet binary
# genuinely running the workload. The "fully autonomous agent" is the wrapper.
#
# Usage:
#   demo/run-demo.sh                 # both halves
#   demo/run-demo.sh --dregg-only    # only the dregg payment-rail half
#   demo/run-demo.sh --dreggnet-only # only the DreggNet durable-exec half
#
# Env:
#   BREADSTUFFS_DIR   path to the dregg (breadstuffs) checkout
#                     (default: $HOME/dev/breadstuffs)
#   DREGGNET_BIN      path to a prebuilt `dreggnet` binary
#                     (default: target/release/dreggnet, else built, else docker)

set -euo pipefail

# ── presentation ────────────────────────────────────────────────────────────
if [ -t 1 ]; then
  BOLD=$(printf '\033[1m'); DIM=$(printf '\033[2m'); RST=$(printf '\033[0m')
  CYAN=$(printf '\033[36m'); GRN=$(printf '\033[32m'); YLW=$(printf '\033[33m')
else
  BOLD=""; DIM=""; RST=""; CYAN=""; GRN=""; YLW=""
fi

step()     { printf '\n%s%s==> %s%s\n' "$BOLD" "$CYAN" "$1" "$RST"; }
real()     { printf '   %s[REAL]%s %s\n' "$GRN" "$RST" "$1"; }
narrated() { printf '   %s[NARRATED]%s %s\n' "$YLW" "$RST" "$1"; }
note()     { printf '   %s%s%s\n' "$DIM" "$1" "$RST"; }
run()      { printf '   %s$ %s%s\n' "$DIM" "$*" "$RST"; "$@"; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BREADSTUFFS_DIR="${BREADSTUFFS_DIR:-$HOME/dev/breadstuffs}"

DO_DREGG=1
DO_DREGGNET=1
case "${1:-}" in
  --dregg-only)    DO_DREGGNET=0 ;;
  --dreggnet-only) DO_DREGG=0 ;;
  --help|-h)       sed -n '2,40p' "$0"; exit 0 ;;
  "" )             ;;
  * ) echo "unknown arg: $1 (try --help)" >&2; exit 2 ;;
esac

printf '%s%s' "$BOLD" "$CYAN"
cat <<'BANNER'
  ┌──────────────────────────────────────────────────────────────────┐
  │  DreggNet — earn · spend · run                                     │
  │  an agent pays Stripe and gets verifiable, durable, metered compute│
  │  boundaries are theorems · every spend is a receipt                │
  └──────────────────────────────────────────────────────────────────┘
BANNER
printf '%s' "$RST"

# ── ACT I — the dregg payment + lease RAIL (breadstuffs, AGPL) ────────────────
if [ "$DO_DREGG" = 1 ]; then
  step "ACT I — the agent earns value and pays for compute (dregg rail, verified)"
  narrated "An agent needs durable compute. It holds value and pays with Stripe."
  note "Repo: $BREADSTUFFS_DIR  (dregg, AGPL-3.0 — the open, verified substrate)"

  if [ ! -d "$BREADSTUFFS_DIR" ]; then
    echo "   !! breadstuffs not found at $BREADSTUFFS_DIR" >&2
    echo "      set BREADSTUFFS_DIR=/path/to/breadstuffs (or run --dreggnet-only)" >&2
    exit 1
  fi

  real "Stripe webhook → conserving USD-credit mint → pay an execution-lease."
  note "Each line below is a real code path in dregg, run as its own test."
  note "  · a signed Stripe webhook mints exactly the paid USD-credit (Σδ=0, conserving)"
  note "  · a forged/tampered webhook is refused — nothing minted"
  note "  · a retried/duplicated webhook never double-mints (idempotent on payment-intent id)"
  note "  · that minted USD-credit pays an execution-lease via the SAME resolve_pay rail \$DREGG uses"

  run cargo test --manifest-path "$BREADSTUFFS_DIR/Cargo.toml" \
      -p dregg-bridge --lib stripe -- --nocapture

  real "The lease itself: open → fund → metered run, executor-enforced ceiling."
  note "  · open+fund a lease, run a metered step, the durable checkpoint advances"
  note "  · a run past the funded ceiling is refused by the kernel executor"

  run cargo test --manifest-path "$BREADSTUFFS_DIR/Cargo.toml" \
      -p dregg-sdk --lib service_economy -- --nocapture

  printf '   %s%s✓ dregg rail: payment verified, credit conserved, lease funded.%s\n' \
      "$GRN" "$BOLD" "$RST"
fi

# ── ACT II — DreggNet runs the durable, metered workload (here, AGPL) ──
if [ "$DO_DREGGNET" = 1 ]; then
  step "ACT II — DreggNet runs the durable, metered workload (the operated reality)"
  narrated "The funded lease authorizes work. DreggNet schedules + runs it."
  note "Repo: $ROOT  (DreggNet, AGPL — the moat that runs the workload)"

  # Resolve a `dreggnet` binary: prebuilt → build → docker fallback.
  BIN="${DREGGNET_BIN:-}"
  USE_DOCKER=0
  if [ -z "$BIN" ] && [ -x "$ROOT/target/release/dreggnet" ]; then
    BIN="$ROOT/target/release/dreggnet"
  fi
  if [ -z "$BIN" ]; then
    if command -v cargo >/dev/null 2>&1; then
      note "building the dreggnet CLI (first build compiles polyana/wasmtime — heavy)…"
      ( cd "$ROOT" && cargo build -p dreggnet-cli --release >/dev/null 2>&1 ) \
        && BIN="$ROOT/target/release/dreggnet" || true
    fi
  fi
  if [ -z "$BIN" ]; then
    if command -v docker >/dev/null 2>&1; then
      USE_DOCKER=1
      note "no native binary; using docker compose (the Linux serving image)."
    else
      echo "   !! no dreggnet binary and no docker — build with: cargo build -p dreggnet-cli --release" >&2
      exit 1
    fi
  fi

  if [ "$USE_DOCKER" = 1 ]; then
    real "docker compose run --rm dreggnet dreggnet-demo (lease → run → status)"
    run docker compose -f "$ROOT/docker-compose.yml" run --rm dreggnet dreggnet-demo
  else
    STATE="$(mktemp -d)"
    trap 'rm -rf "$STATE"' EXIT
    WAT="$STATE/workload.wat"
    printf '(module (func (export "run") (result i32) (i32.const 42)))\n' > "$WAT"

    real "open + fund an execution-lease (sandboxed grade, budget 100, 1/step)"
    OUT="$("$BIN" --state-dir "$STATE" lease open --cap-tier sandboxed --budget 100 --lessee stripe-agent)"
    printf '%s\n' "$OUT" | sed 's/^/      /'
    LEASE="$(printf '%s\n' "$OUT" | sed -n 's/^lease opened: //p')"

    real "run the workload — a durable, metered polyana job in the wasm sandbox"
    note "control → bridge → durable → exec → polyana. add(40,2)=42, then *2=84."
    note "each durable step charges the meter; an over-budget tick lapses → reap."
    printf '   %s$ dreggnet run --lease %s --lang wat --source workload.wat%s\n' \
      "$DIM" "${LEASE:0:8}…" "$RST"
    # The in-memory durable store logs retryable contention WARNs to stderr; they
    # auto-retry to success and only clutter the demo, so drop just those lines.
    "$BIN" --state-dir "$STATE" run --lease "$LEASE" --lang wat --source "$WAT" 2>&1 \
      | grep -vE 'duroxide|retryable|deadlock|backing off' \
      | sed 's/^/      /'

    real "status — the lifecycle + the meter you can read back"
    printf '   %s$ dreggnet status%s\n' "$DIM" "$RST"
    "$BIN" --state-dir "$STATE" status | sed 's/^/      /'

    note "(the durable workflow is crash-resumable: a crash resumes within the SAME"
    note " budget — exactly-once metering, charge ⟺ checkpoint. proved in the durable"
    note " crate's pg-backed resume test; see docs/DBOS-DURABLE-LAYER.md.)"
  fi

  printf '   %s%s✓ DreggNet: durable workload ran, metered against the lease.%s\n' \
      "$GRN" "$BOLD" "$RST"
fi

# ── the payoff ────────────────────────────────────────────────────────────────
step "THE LOOP"
cat <<EOF
   earn/hold  →  pay via Stripe  →  spend on a dregg lease  →  run durable metered compute
   ${DIM}(value)        (real webhook→mint)   (resolve_pay, Σδ=0)     (polyana, crash-resumable)${RST}

   The agent paid Stripe and got verifiable, durable, metered compute —
   on a formally-verified rail. Boundaries are theorems; every spend a receipt.
EOF
