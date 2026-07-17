#!/usr/bin/env bash
# ship-readiness-smoke.sh — run every shipped cockpit feature surface and report
# SOLID / PARTIAL / STUB / BUSTED. The companion to .docs-history-noclaude/deos/SHIP-READINESS.md.
#
# This RUNS the real harnesses (render bakes + per-crate tests), it does not assert
# from code-reading. Each surface prints its evidence (the test-result line and/or
# the baked artifact). Pass `--fast` to skip the heavy embedded-executor suites
# (apps/membrane/live-node, ~10-20 min compile+run) and only do the render bakes
# (which reuse the prebuilt release binary).
#
# Prereqs:
#   - a release binary at starbridge-v2/target/release/starbridge-v2 (the bakes reuse it)
#   - a dregg node on :8775 for the unified-boot / node-attach surfaces
#     (start one with the node crate; the bake degrades honestly if absent)
#
# Usage:  scripts/ship-readiness-smoke.sh [--fast] [OUTDIR]
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FAST=0
OUT="${TMPDIR:-/tmp}/ship-readiness-$$"
for a in "$@"; do
  case "$a" in
    --fast) FAST=1 ;;
    *) OUT="$a" ;;
  esac
done
mkdir -p "$OUT"
BIN="starbridge-v2/target/release/starbridge-v2"
NODE="${DREGG_NODE:-http://127.0.0.1:8775}"

pass=0; fail=0
say() { printf '\n=== %s ===\n' "$1"; }
ok()  { printf '  SOLID   %s\n' "$1"; pass=$((pass+1)); }
part(){ printf '  PARTIAL %s\n' "$1"; pass=$((pass+1)); }
bad() { printf '  BUSTED  %s\n' "$1"; fail=$((fail+1)); }

# ---- render bakes (reuse the prebuilt release binary) ----------------------
if [[ -x "$BIN" ]]; then
  say "self-hosting-full (editor-save=turn -> disk mirror -> terminal rustc)"
  if "$BIN" --render-self-hosting-full "$OUT/self-hosting-full.png" 2>&1 | tee "$OUT/self-hosting-full.log" | grep -q "THE FULL SINGLE LOOP RAN"; then
    ok "self-hosting-full bake ($(ls -1 "$OUT"/self-hosting-full.png* 2>/dev/null | head -1))"
  else bad "self-hosting-full bake — see $OUT/self-hosting-full.log"; fi

  say "unified-boot (live node pane + editor + terminal)  [node: $NODE]"
  if "$BIN" --render-unified-boot "$OUT/unified-boot.png" --node "$NODE" 2>&1 | tee "$OUT/unified-boot.log" | grep -q "PANE (live node): attached"; then
    if grep -q "did NOT reach the node ledger" "$OUT/unified-boot.log"; then
      part "unified-boot bake — SEAM: editor save is LOCAL-only; node attach is READ-ONLY-synced (write-back unrouted)"
    else ok "unified-boot bake"; fi
  else bad "unified-boot bake (node up on $NODE?) — see $OUT/unified-boot.log"; fi
else
  bad "no release binary at $BIN — build with: cargo build --release --features native-full --bin starbridge-v2"
fi

# ---- per-crate harnesses ---------------------------------------------------
run_crate() { # name dir testargs... ; PASS if a `test result: ok` and no `FAILED`
  local name="$1" dir="$2"; shift 2
  say "$name  ($dir cargo test $*)"
  ( cd "$dir" && cargo test "$@" ) 2>&1 | tee "$OUT/$name.log" | tail -4
  if grep -q "test result: ok" "$OUT/$name.log" && ! grep -q "test result: FAILED" "$OUT/$name.log"; then
    ok "$name — $(grep 'test result: ok' "$OUT/$name.log" | tail -1 | sed 's/^[[:space:]]*//')"
  else bad "$name — see $OUT/$name.log"; fi
}

run_crate "servo-web-shell"  "servo-render" test --features libservo
run_crate "editor-firmament" "deos-zed"     test --features firmament
run_crate "hermes-agent"     "deos-hermes"  test
run_crate "chat-matrix"      "deos-matrix"  test
run_crate "terminal-pty"     "deos-terminal" test
run_crate "inspectors"       "deos-reflect" test

if [[ "$FAST" -eq 0 ]]; then
  # the heavy embedded-executor suites (long compile + run)
  say "apps (19 apps launch on World + fire turns)"
  ( cd starbridge-v2 && cargo test --no-default-features --features app-registry --lib ) 2>&1 | tee "$OUT/apps.log" | tail -4
  if grep -q "test result: ok" "$OUT/apps.log" && ! grep -q "test result: FAILED" "$OUT/apps.log"; then ok "apps"; else bad "apps — see $OUT/apps.log"; fi

  say "membrane (shared_fork — a message = a cap-bounded world-fork)"
  ( cd starbridge-v2 && cargo test --no-default-features --features embedded-executor --lib shared_fork ) 2>&1 | tee "$OUT/membrane.log" | tail -4
  if grep -q "test result: ok" "$OUT/membrane.log" && ! grep -q "test result: FAILED" "$OUT/membrane.log"; then ok "membrane"; else bad "membrane — see $OUT/membrane.log"; fi

  say "node-attach (LiveNode HTTP+SSE sync)"
  ( cd starbridge-v2 && cargo test --no-default-features --features embedded-executor,live-node --lib live_node ) 2>&1 | tee "$OUT/live-node.log" | tail -4
  if grep -q "test result: ok" "$OUT/live-node.log" && ! grep -q "test result: FAILED" "$OUT/live-node.log"; then ok "node-attach"; else bad "node-attach — see $OUT/live-node.log"; fi
fi

printf '\n=== SHIP-READINESS SUMMARY ===\n  surfaces green: %d   busted: %d\n  logs + bakes: %s\n' "$pass" "$fail" "$OUT"
[[ "$fail" -eq 0 ]]
