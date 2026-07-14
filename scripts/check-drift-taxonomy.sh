#!/usr/bin/env bash
# check-drift-taxonomy.sh — THE DRIFT-TAXONOMY CI GATE.
#
# Classifies the descriptor delta between a BASE git ref (what trunk ships today)
# and the WORKING TREE (what this change proposes), and REFUSES a GEOMETRY-WIDEN
# (a re-genesis flag-day) unless an eyes-open re-genesis flag is set. Mechanizes
# "does this upgrade need a wipe?" — a TAIL-APPEND passes cleanly; a change that
# moves an existing cohort member's trace_width / shared-PI-prefix / fingerprint
# cannot ship silently.
#
# Unlike check-descriptor-drift.sh (Lean<->JSON freshness — needs a Lean build),
# this gate is a pure diff of two committed/working descriptor sets: no toolchain
# required, cheap to run on every PR.
#
# Config (env):
#   DRIFT_TAXONOMY_BASE_REF  base ref to diff against (default: first of
#                            origin/main, main, HEAD that resolves)
#   DREGG_ALLOW_REGENESIS=1  acknowledge an eyes-open re-genesis (passes a
#                            GEOMETRY-WIDEN). The ember-gated flag.
#   DRIFT_DESCRIPTORS_SUBPATH  descriptor subpath (default circuit/descriptors)
#
# Exit: 0 = UNCHANGED / TAIL-APPEND (or GEOMETRY-WIDEN + DREGG_ALLOW_REGENESIS=1);
#       4 = GEOMETRY-WIDEN refused (no re-genesis flag); 2 = setup error.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SUBPATH="${DRIFT_DESCRIPTORS_SUBPATH:-circuit/descriptors}"
NEW="$ROOT/$SUBPATH"

resolve_base() {
  if [ -n "${DRIFT_TAXONOMY_BASE_REF:-}" ]; then
    echo "$DRIFT_TAXONOMY_BASE_REF"; return 0
  fi
  for cand in origin/main main HEAD; do
    if git -C "$ROOT" rev-parse --verify --quiet "$cand^{commit}" >/dev/null; then
      echo "$cand"; return 0
    fi
  done
  return 1
}

if ! BASE="$(resolve_base)"; then
  echo "check-drift-taxonomy: no base ref resolvable (set DRIFT_TAXONOMY_BASE_REF); skipping." >&2
  exit 0
fi

# Does the base ref even carry the descriptor subpath? (A fresh repo / a ref before
# the descriptors existed → nothing to diff against; treat as a clean skip.)
if ! git -C "$ROOT" cat-file -e "$BASE:$SUBPATH" 2>/dev/null; then
  echo "check-drift-taxonomy: $BASE has no $SUBPATH (nothing to diff); skipping." >&2
  exit 0
fi

echo "check-drift-taxonomy: classifying $SUBPATH delta  ($BASE -> working tree)..."

FLAGS=()
if [ "${DREGG_ALLOW_REGENESIS:-}" = "1" ]; then
  FLAGS+=(--allow-regenesis)
  echo "check-drift-taxonomy: DREGG_ALLOW_REGENESIS=1 — a GEOMETRY-WIDEN will be permitted (eyes-open)."
fi

exec python3 "$ROOT/scripts/classify_descriptor_drift.py" \
  --old-ref "$BASE" --descriptors-subpath "$SUBPATH" \
  --new "$NEW" "${FLAGS[@]}"
