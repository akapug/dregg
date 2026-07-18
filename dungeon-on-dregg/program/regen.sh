#!/usr/bin/env bash
# regen.sh — regenerate dungeon_program.json from the VERIFIED Lean source of truth.
#
# The checked-in `dungeon_program.json` is a CACHE of the Lean emission
# (`metatheory/Dregg2/Games/DungeonProgram.lean :: dungeonProgram`, rendered by
# `metatheory/EmitDungeonProgram.lean`). Lean is the source of truth; the deployed
# descent program (`dungeon-on-dregg/src/descent.rs::Deployment::program()`) LOADS this
# artifact and resolves the symbolic slot/method names against the translation-validated
# dregg-schema allocator. There is NO hand-rolled Rust `CellProgram` in the descent's
# path.
#
# Usage:
#   dungeon-on-dregg/program/regen.sh          # regenerate + overwrite the artifact
#   dungeon-on-dregg/program/regen.sh --check  # DRIFT GATE: regenerate to a temp file and
#                                              # diff; nonzero exit iff Lean and the
#                                              # checked-in artifact disagree.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ARTIFACT="$ROOT/dungeon-on-dregg/program/dungeon_program.json"

if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "regen: FATAL — 'lake' not on PATH (Lean toolchain required)." >&2
  exit 2
fi

# Build what we run (the emit imports the compiled olean, not the source).
( cd "$ROOT/metatheory" && lake build Dregg2.Games.DungeonProgram >/dev/null )

TMP="$(mktemp -t dungeon_program.XXXXXX.json)"
trap 'rm -f "$TMP"' EXIT
( cd "$ROOT/metatheory" && lake env lean --run EmitDungeonProgram.lean ) > "$TMP"

if [ "${1:-}" = "--check" ]; then
  if diff -u "$ARTIFACT" "$TMP"; then
    echo "regen --check: PASS — the Lean emission matches the checked-in artifact."
    exit 0
  else
    echo "" >&2
    echo "DUNGEON PROGRAM DRIFT: the Lean emission and the checked-in JSON disagree." >&2
    echo "  Run dungeon-on-dregg/program/regen.sh (no --check) and commit the result." >&2
    exit 1
  fi
fi

cp "$TMP" "$ARTIFACT"
echo "regen: wrote $ARTIFACT ($(wc -c < "$ARTIFACT") bytes) from the Lean source of truth."
