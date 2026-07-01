#!/usr/bin/env bash
#
# DreggNet — the on-camera crash-resume proof.
#
#   A durable, metered workload runs. We SIGKILL it mid-flight — a genuine crash of
#   a real OS process, after step 1's checkpoint but before step 2. Then a BRAND-NEW
#   process resumes over the same on-disk SQLite store and proves exactly-once:
#
#       step 1 is REPLAYED from the checkpoint — never re-executed
#       step 2 runs exactly once
#       the meter is charged exactly twice — never doubled by the crash
#
# This is the differentiated claim, made visceral: most "durable" demos never show
# the kill. This one does — `kill -9` on camera, then the work resumes correct.
#
# It uses the bundled SQLite durable store (no Postgres, no network) so it runs
# anywhere, offline, in ~10 seconds.
#
# Usage:   demo/crash-resume.sh
# Env:     DREGGNET_BIN   path to a prebuilt `dreggnet-crash-resume` binary.

set -euo pipefail

# Quiet duroxide's retryable "database is locked" backoff WARNs (they auto-retry to
# success and only clutter the demo). Override by exporting RUST_LOG before running.
export RUST_LOG="${RUST_LOG:-error}"

if [ -t 1 ]; then
  BOLD=$(printf '\033[1m'); DIM=$(printf '\033[2m'); RST=$(printf '\033[0m')
  CYAN=$(printf '\033[36m'); GRN=$(printf '\033[32m'); RED=$(printf '\033[31m'); YLW=$(printf '\033[33m')
else
  BOLD=""; DIM=""; RST=""; CYAN=""; GRN=""; RED=""; YLW=""
fi
step() { printf '\n%s%s==> %s%s\n' "$BOLD" "$CYAN" "$1" "$RST"; }
note() { printf '   %s%s%s\n' "$DIM" "$1" "$RST"; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# ── resolve the binary: env → prebuilt → build ───────────────────────────────
BIN="${DREGGNET_BIN:-}"
if [ -z "$BIN" ]; then
  for cand in "$ROOT/target/release/dreggnet-crash-resume" "$ROOT/target/debug/dreggnet-crash-resume"; do
    [ -x "$cand" ] && BIN="$cand" && break
  done
fi
if [ -z "$BIN" ]; then
  note "building dreggnet-crash-resume (first build compiles polyana — heavy)…"
  ( cd "$ROOT" && cargo build -p dreggnet-cli --bin dreggnet-crash-resume >/dev/null 2>&1 ) \
    && BIN="$ROOT/target/debug/dreggnet-crash-resume"
fi
if [ -z "$BIN" ] || [ ! -x "$BIN" ]; then
  echo "!! could not find or build dreggnet-crash-resume" >&2
  echo "   build it with: cargo build -p dreggnet-cli --bin dreggnet-crash-resume" >&2
  exit 1
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
DB="$WORK/durable.db"
SNAP="$WORK/snapshot.json"
READY="$WORK/ready"
INSTANCE="lease-crash-demo"

printf '%s%s' "$BOLD" "$CYAN"
cat <<'BANNER'
  ┌──────────────────────────────────────────────────────────────────┐
  │  DreggNet — crash-resume: kill it mid-flight, resume exactly-once  │
  │  on-disk SQLite durable store · charge ⟺ checkpoint · no double-pay│
  └──────────────────────────────────────────────────────────────────┘
BANNER
printf '%s' "$RST"

# ── phase 1: run to the checkpoint, then get SIGKILL-ed ──────────────────────
step "Run the durable workload — checkpoint after step 1, then CRASH it"
note "store: $DB"

"$BIN" --phase 1 --db "$DB" --snapshot "$SNAP" --ready "$READY" --instance "$INSTANCE" &
PHASE1_PID=$!

# Wait until phase 1 reports the post-step1 checkpoint is durable on disk.
waited=0
until [ -f "$READY" ]; do
  if ! kill -0 "$PHASE1_PID" 2>/dev/null; then
    echo "!! phase 1 exited before reaching the checkpoint" >&2
    wait "$PHASE1_PID" || true
    exit 1
  fi
  sleep 0.2
  waited=$((waited + 1))
  if [ "$waited" -gt 150 ]; then
    echo "!! timed out waiting for the checkpoint" >&2
    kill -9 "$PHASE1_PID" 2>/dev/null || true
    exit 1
  fi
done

# 💥 The genuine crash — a real SIGKILL of a live, mid-workflow process.
printf '\n   %s%s💥 kill -9 %s%s  %s(SIGKILL — the process dies mid-workflow, no cleanup)%s\n' \
  "$BOLD" "$RED" "$PHASE1_PID" "$RST" "$DIM" "$RST"
kill -9 "$PHASE1_PID" 2>/dev/null || true
wait "$PHASE1_PID" 2>/dev/null || true
note "process $PHASE1_PID is gone. The on-disk checkpoint is all that survives."

# ── phase 2: a fresh process resumes over the same store ─────────────────────
step "Resume — a brand-new process picks up from the checkpoint"
if "$BIN" --phase 2 --db "$DB" --snapshot "$SNAP" --instance "$INSTANCE"; then
  printf '\n   %s%s✓ crash-resume: exactly-once held across a real SIGKILL.%s\n' "$GRN" "$BOLD" "$RST"
else
  printf '\n   %s%s✗ crash-resume proof FAILED%s\n' "$RED" "$BOLD" "$RST"
  exit 1
fi
