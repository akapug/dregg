#!/usr/bin/env bash
# check-turn-valid-until.sh — THE UNBOUNDED-DEADLINE gate (local-gates.sh rows).
#
# Tripwires a production `Turn { .., valid_until: None, .. }` literal in the five crates whose
# turn builders PRs #78 / #81 / #82 / #83 / #84 bounded (sdk, node, intent, starbridge-v2,
# coord). `valid_until` is a block height (issue #46, 2026-09-29); `None` never expires, and
# the verified Lean producer's wire marshal refuses it, so the turn silently falls back to the
# Rust producer. The rule is `.ast-grep/rules/turn-valid-until-none.yml`; it replaces the
# `include_str!` text ratchets those PRs carried, which `None }`, `Option::None`, a new file or
# a formatter would all have evaded.
#
# Usage:  scripts/check-turn-valid-until.sh [--self-test]
# Exit:   0 = clean; 1 = an unsuppressed `valid_until: None` Turn literal in production
#         source (or, with --self-test, the rule failed to fire / fired where it must not);
#         2 = environment problem.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [ "${1:-}" = "--self-test" ]; then
  printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
    'does the rule, copied verbatim into a scratch project, flag exactly the four forbidden shapes in a fixture (bare Turn, path-qualified Turn, Option::None, a Turn built in a non-test mod named tests) and none of the three permitted ones (a Some deadline, a #[cfg(test)] module, an ast-grep-ignore suppression)?' \
    'anything about the real tree. This mode never scans production source.'
else
  printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
    'does ast-grep find a Turn struct literal with valid_until: None (or Option::None), outside #[cfg(test)] modules and not suppressed by an ast-grep-ignore line, in sdk/src, node/src, intent/src, starbridge-v2/src or coord/src?' \
    'whether any turn carries a SENSIBLE deadline. A Turn built by a helper or a builder (TurnBuilder, TurnComposer, make_turn) whose deadline is never set is not a literal and is not seen; neither is any crate outside the five; and a stamped deadline may still be a Unix-seconds value, which only the executor refuses (DeadlineBeyondHorizon).'
fi

SG=""
for c in ast-grep sg; do
  if command -v "$c" >/dev/null 2>&1; then SG="$c"; break; fi
done
if [ -z "$SG" ]; then
  echo "check-turn-valid-until: FATAL — ast-grep ('sg') not on PATH." >&2
  exit 2
fi

RULE=".ast-grep/rules/turn-valid-until-none.yml"
[ -f "$RULE" ] || { echo "check-turn-valid-until: FATAL — missing $RULE" >&2; exit 2; }

count_hits() {
  # $1 = project root holding sgconfig.yml; rest = paths. Prints the number of diagnostics.
  local proj="$1"; shift
  # `scan` exits 1 when it finds error-severity matches, which is the point here; the count,
  # not the exit status, is the verdict (an unparsable output still fails in python).
  { (cd "$proj" && "$SG" scan --config sgconfig.yml --filter turn-valid-until-none --json=compact "$@" 2>/dev/null) || true; } \
    | python3 -c 'import json,sys; print(len(json.load(sys.stdin)))'
}

if [ "${1:-}" = "--self-test" ]; then
  TMP="$(mktemp -d -t turn-valid-until-selftest.XXXXXX)"
  trap 'rm -rf "$TMP"' EXIT
  mkdir -p "$TMP/.ast-grep/rules" "$TMP/sdk/src"
  cp "$RULE" "$TMP/.ast-grep/rules/"
  printf 'ruleDirs:\n  - .ast-grep/rules\n' > "$TMP/sgconfig.yml"
  cat > "$TMP/sdk/src/fixture.rs" <<'RS'
fn forbidden_bare() -> Turn {
    Turn { agent: a, nonce: 0, valid_until: None, fee: 0 }
}
fn forbidden_qualified() -> dregg_turn::Turn {
    dregg_turn::Turn { agent: a, valid_until: None }
}
fn forbidden_option_none() -> Turn {
    Turn { valid_until: Option::None, agent: a }
}
mod tests {
    fn a_mod_named_tests_without_the_attribute_is_production() -> Turn {
        Turn { valid_until: None }
    }
}
fn permitted_some() -> Turn {
    Turn { valid_until: Some(dregg_turn::valid_until_at(h, 1800)) }
}
fn permitted_suppressed() -> Turn {
    Turn {
        // Never executed: hashed only.
        // ast-grep-ignore: turn-valid-until-none
        valid_until: None,
    }
}
#[cfg(test)]
mod real_tests {
    fn permitted_in_cfg_test() -> Turn {
        Turn { valid_until: None }
    }
}
RS
  got="$(count_hits "$TMP" sdk/src)"
  if [ "$got" = "4" ]; then
    echo "check-turn-valid-until: SELF-TEST PASS — 4 forbidden shapes flagged, 3 permitted shapes not."
    exit 0
  fi
  echo "check-turn-valid-until: SELF-TEST FAILED — expected 4 diagnostics on the fixture, got '$got'." >&2
  exit 1
fi

# A path that does not exist scans as clean; refuse rather than pass on nothing.
SCOPED=(sdk/src node/src intent/src starbridge-v2/src coord/src)
for d in "${SCOPED[@]}"; do
  [ -d "$d" ] || { echo "check-turn-valid-until: FATAL — '$d' does not exist; re-point SCOPED here and 'files:' in $RULE." >&2; exit 2; }
done

echo "check-turn-valid-until: scanning ${SCOPED[*]} with $SG ..."
if "$SG" scan --config sgconfig.yml --filter turn-valid-until-none "${SCOPED[@]}"; then
  echo "check-turn-valid-until: PASS — no production Turn literal leaves valid_until unset."
  exit 0
fi
echo "" >&2
echo "UNBOUNDED DEADLINE: a production Turn literal sets valid_until: None. The turn never" >&2
echo "expires and the verified Lean producer's wire marshal refuses it. Stamp a block height:" >&2
echo "  dregg_turn::valid_until_at(height, dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS)" >&2
echo "(inside a node: executor_setup::default_valid_until(s))." >&2
exit 1
