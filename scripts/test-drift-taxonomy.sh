#!/usr/bin/env bash
# test-drift-taxonomy.sh — DRIVE the drift-taxonomy classifier on synthetic fixtures.
#
# Non-vacuity gate: a tail-append fixture must CLASSIFY tail-append AND PASS; a
# geometry-widen fixture must CLASSIFY geometry-widen AND be REFUSED without the
# re-genesis flag AND PASS with it; an unchanged fixture must classify UNCHANGED.
# (i.e. the gate lets the cheap change through and CATCHES the wipe-requiring one.)
#
# Exit: 0 = all cases behaved as required; nonzero = a case regressed.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CLS="$ROOT/scripts/classify_descriptor_drift.py"
FIX="$ROOT/scripts/fixtures/drift-taxonomy"
OLD="$FIX/old"

fails=0
pass() { echo "  PASS — $1"; }
fail() { echo "  FAIL — $1" >&2; fails=$((fails + 1)); }

# run_case <label> <new-dir> <expect-class> <expect-exit> [extra-flags...]
run_case() {
  local label="$1" new="$2" expect_class="$3" expect_exit="$4"; shift 4
  local out rc
  out="$(python3 "$CLS" --old "$OLD" --new "$new" "$@" 2>/dev/null)"; rc=$?
  local got_class
  got_class="$(printf '%s\n' "$out" | sed -n 's/^drift-taxonomy: CLASS = //p' | head -1)"
  if [ "$got_class" = "$expect_class" ] && [ "$rc" -eq "$expect_exit" ]; then
    pass "$label -> $got_class (exit $rc)"
  else
    fail "$label: got class=$got_class exit=$rc; want class=$expect_class exit=$expect_exit"
    printf '%s\n' "$out" | sed 's/^/      /'
  fi
}

echo "drift-taxonomy driver: exercising the fixtures under $FIX"

# 1. UNCHANGED: identical set -> UNCHANGED, passes.
run_case "unchanged set"            "$FIX/unchanged"      UNCHANGED       0

# 2. TAIL-APPEND: new tail row + additive tail PI -> TAIL-APPEND, passes cleanly.
run_case "tail-append set"          "$FIX/tail-append"    TAIL-APPEND     0

# 3. GEOMETRY-WIDEN without the flag -> classified geometry-widen AND REFUSED (exit 4).
run_case "geometry-widen (no flag)" "$FIX/geometry-widen" GEOMETRY-WIDEN  4

# 4. GEOMETRY-WIDEN WITH --allow-regenesis -> classified geometry-widen AND PASSES.
run_case "geometry-widen (--allow-regenesis)" "$FIX/geometry-widen" GEOMETRY-WIDEN 0 --allow-regenesis

# 5. Cross-check the two poles are genuinely distinct (non-vacuity): the tail-append
#    fixture must NOT be refused, and the geometry-widen fixture MUST be refused.
if python3 "$CLS" --old "$OLD" --new "$FIX/tail-append" >/dev/null 2>&1; then
  pass "non-vacuity: tail-append is NOT refused"
else
  fail "non-vacuity: tail-append was refused (should pass)"
fi
if python3 "$CLS" --old "$OLD" --new "$FIX/geometry-widen" >/dev/null 2>&1; then
  fail "non-vacuity: geometry-widen was NOT refused (should be caught)"
else
  pass "non-vacuity: geometry-widen IS refused without the flag"
fi

echo
if [ "$fails" -eq 0 ]; then
  echo "drift-taxonomy driver: ALL CASES PASS"
  exit 0
else
  echo "drift-taxonomy driver: $fails case(s) FAILED" >&2
  exit 1
fi
