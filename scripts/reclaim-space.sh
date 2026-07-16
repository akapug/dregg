#!/usr/bin/env bash
# reclaim-space.sh — find and reclaim agent build-sprawl on this dev machine.
#
# The recurring problem (2026-07-16): a `cargo clean` at a workspace root only
# cleans that ONE workspace's target/. A tree like breadstuffs has ~11 EXCLUDED
# sub-workspaces (sdk-py, discord-bot, dregg-tui, pg-dregg, wasm, solana-lock,
# deos-homeserver, forge-ci-runner, dregg-interchain-gov, dreggnet-gear,
# host-gateway, …), each with its OWN target/ that the root clean never touches;
# and agents building across ~20 repos under ~/dev leave a target/ (and Lean
# .lake) in each. It adds up to hundreds of GB with no single smoking gun.
#
# This script REPORTS by default (safe, read-only) and only deletes with --clean.
#
#   ./scripts/reclaim-space.sh                 # dry-run report, ranked, with total
#   ./scripts/reclaim-space.sh --clean         # remove every target/ (KEEPS .lake)
#   ./scripts/reclaim-space.sh --clean --lake  # also remove .lake (Lean rebuilds are slow)
#   ./scripts/reclaim-space.sh --clean --worktrees   # also `git worktree prune` + drop .claude/worktrees
#   ./scripts/reclaim-space.sh --roots "$HOME/dev $HOME/dreggnet-local"   # override scan roots
#
# ⚠ --clean is destructive and RACES ACTIVE BUILDS: deleting a target/ under a
#   running cargo/lake will break that build. Run it when the swarms are quiet.

set -euo pipefail

ROOTS="${HOME}/dev ${HOME}/dreggnet-local"
DO_CLEAN=0
DO_LAKE=0
DO_WORKTREES=0

while [ $# -gt 0 ]; do
  case "$1" in
    --clean)     DO_CLEAN=1 ;;
    --lake)      DO_LAKE=1 ;;
    --worktrees) DO_WORKTREES=1 ;;
    --roots)     shift; ROOTS="$1" ;;
    -h|--help)   sed -n '2,25p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1 (see --help)" >&2; exit 2 ;;
  esac
  shift
done

# Build the name filter: always target/, plus .lake when asked (report shows both).
if [ "$DO_LAKE" = 1 ] || [ "$DO_CLEAN" = 0 ]; then
  NAME_EXPR=( \( -name target -o -name .lake \) )
else
  NAME_EXPR=( -name target )
fi

echo "── scanning: ${ROOTS} ──"
# -prune so we do not descend INTO a target/ (fast); NUL-safe for weird repo names.
mapfile -d '' -t DIRS < <(
  # shellcheck disable=SC2086
  find ${ROOTS} -type d "${NAME_EXPR[@]}" -prune -print0 2>/dev/null
)

if [ "${#DIRS[@]}" -eq 0 ]; then echo "nothing found."; exit 0; fi

echo "── ranked (largest first) ──"
# du each once; reuse for report + total. macOS du -k = KiB blocks (portable).
TOTAL_KB=0
declare -a ROWS=()
for d in "${DIRS[@]}"; do
  kb=$(du -sk "$d" 2>/dev/null | awk '{print $1}')
  [ -z "$kb" ] && continue
  TOTAL_KB=$(( TOTAL_KB + kb ))
  ROWS+=("$kb	$d")
done
printf '%s\n' "${ROWS[@]}" | sort -rn | head -40 | awk '{
  kb=$1; $1=""; unit="KiB"; v=kb;
  if (v>=1048576){v=v/1048576; unit="GiB"} else if (v>=1024){v=v/1024; unit="MiB"}
  printf "  %7.1f %s\t%s\n", v, unit, substr($0,2)
}'

printf '── total reclaimable: %.1f GiB across %d dirs ──\n' "$(echo "$TOTAL_KB/1048576" | bc -l)" "${#DIRS[@]}"
df -h / 2>/dev/null | awk 'NR==1||/\/$/{print "  "$0}'

if [ "$DO_CLEAN" = 0 ]; then
  echo
  echo "report only. re-run with --clean to delete the target/ dirs above"
  echo "(add --lake to include Lean builds, --worktrees to prune agent worktrees)."
  exit 0
fi

echo
echo "⚠ --clean: deleting the dirs above. This BREAKS any build currently running in them."
for d in "${DIRS[@]}"; do
  echo "  rm -rf $d"
  rm -rf "$d"
done

if [ "$DO_WORKTREES" = 1 ]; then
  echo "── pruning stale agent worktrees ──"
  for wt in "${HOME}"/dev/*/.claude/worktrees "${HOME}"/dev/*-worktrees; do
    [ -d "$wt" ] || continue
    repo="${wt%/.claude/worktrees}"; repo="${repo%-worktrees}"
    if [ -d "$repo/.git" ] || [ -f "$repo/.git" ]; then
      git -C "$repo" worktree prune 2>/dev/null || true
    fi
    echo "  rm -rf $wt"
    rm -rf "$wt"
  done
fi

echo "── done. new free space: ──"
df -h / 2>/dev/null | awk 'NR==1||/\/$/{print "  "$0}'
