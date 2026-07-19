#!/usr/bin/env bash
# Regenerate the Rust-consumed clearing plan from the proved Lean compiler.
#
#   fhegg-fhe/plans/regen.sh          overwrite the checked-in cache
#   fhegg-fhe/plans/regen.sh --check  fail iff Lean and the cache differ
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ARTIFACT="$ROOT/fhegg-fhe/plans/rebalance-v1.json"

if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "regen: FATAL — 'lake' not on PATH (Lean toolchain required)." >&2
  exit 2
fi

( cd "$ROOT/metatheory" && lake build Market.FhIRClearingPlan >/dev/null )
TMP="$(mktemp -t fhir-clearing-plan.XXXXXX.json)"
trap 'rm -f "$TMP"' EXIT
( cd "$ROOT/metatheory" && lake env lean --run EmitFhIRClearingPlan.lean ) > "$TMP"

if [ "${1:-}" = "--check" ]; then
  if diff -u "$ARTIFACT" "$TMP"; then
    echo "regen --check: PASS — Lean emission matches rebalance-v1.json."
    exit 0
  fi
  echo "FHIR CLEARING PLAN DRIFT: run fhegg-fhe/plans/regen.sh and commit the result." >&2
  exit 1
fi

cp "$TMP" "$ARTIFACT"
echo "regen: wrote $ARTIFACT from Market.FhIRClearingPlan."
