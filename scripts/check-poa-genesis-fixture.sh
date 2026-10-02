#!/usr/bin/env bash
# check-poa-genesis-fixture.sh — the frozen PoA network-genesis fixtures ARE Lean's render.
#
# ANSWERS:         do dregg-lean-ffi/tests/fixtures/poa-network-genesis-{input,output,config,canon}-v1.json
#                  equal, byte for byte, what Lean renders from `NetworkGenesis.fixtureInput`
#                  (and does Lean accept that fixture)?
# DOES NOT ANSWER: whether the fixture is the LIVE deployment's tuple. It is a pinned test vector
#                  (the counter-12 POAG1 bundle as of 2026-10-01). The live tuple is exercised by
#                  dregg-node's `poa_signal_genesis` tests, which run the node's ceremony encoder
#                  over `poa/deployments/epoch-1` + the signed bundle through the linked Lean
#                  evaluator — no frozen file in between.
#
# ⚑ WHY (2026-10-01): the frozen input sat at content counter 2 for eight weeks while Lean's
# `FIXTURE_*` constants and the signed bundle moved to 12. Nothing tied the JSON to Lean's
# `fixtureInputBytes`; one lane checked it once with a hand-run `#eval`.
#
# The renderer is `metatheory/Dregg2/Games/PathOfAngels/NetworkGenesisFixtureEmitMain.lean` (no
# second encoder here). Re-emit: `cd metatheory && lake env lean --run <that file>`.
#
#   scripts/check-poa-genesis-fixture.sh              # check the checked-in fixtures
#   scripts/check-poa-genesis-fixture.sh --self-test  # plant a one-byte edit in a scratch copy:
#                                                     # it MUST refuse; the untouched copy MUST pass
#
# Needs the `NetworkGenesisFixtures` olean (`lake build Dregg2.Games.PathOfAngels.NetworkGenesisFixtures`).
# Exit 3 (BLOCKED) when that prerequisite is absent, 1 on drift, 0 when byte-exact.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
META="$ROOT/metatheory"
DRIVER="Dregg2/Games/PathOfAngels/NetworkGenesisFixtureEmitMain.lean"
FIXTURES="$ROOT/dregg-lean-ffi/tests/fixtures"
STEMS=(input output config canon)

olean="$META/.lake/build/lib/lean/Dregg2/Games/PathOfAngels/NetworkGenesisFixtures.olean"
if [ ! -f "$olean" ]; then
  echo "BLOCKED: $olean is absent — run \`lake build Dregg2.Games.PathOfAngels.NetworkGenesisFixtures\` in metatheory/" >&2
  exit 3
fi

run_check() {  # $1 = fixture dir; prints the driver's output, returns its exit code
  (cd "$META" && POA_GENESIS_FIXTURE_MODE=check POA_GENESIS_FIXTURE_DIR="$1" \
     lake env lean --run "$DRIVER") 2>&1
}

if [ "${1:-}" != "--self-test" ]; then
  run_check "$FIXTURES"
  exit $?
fi

# ── SELF-TEST ── the headline is "no drift", a NEGATIVE assertion, which a broken reader passes
# just as happily. So: a scratch copy, untouched, must PASS (the reader can say yes), and each of
# the four files with ONE byte changed must FAIL naming that file (the reader can say no, and the
# comparison covers every file). The checked-in fixtures are never touched.
tmp="$(mktemp -d "${TMPDIR:-/tmp}/poa-genesis-fixture-selftest.XXXXXX")" || exit 2
trap 'rm -rf "$tmp"' EXIT
for s in "${STEMS[@]}"; do cp "$FIXTURES/poa-network-genesis-$s-v1.json" "$tmp/" || exit 2; done

out="$(run_check "$tmp")"; rc=$?
if [ $rc -ne 0 ]; then
  echo "SELF-TEST FAIL: the untouched copy did not pass (rc=$rc) — the checker cannot say yes:"; echo "$out"; exit 1
fi
echo "control: untouched copy passes"

fails=0
for s in "${STEMS[@]}"; do
  f="$tmp/poa-network-genesis-$s-v1.json"
  cp "$f" "$f.orig"
  # Flip ONE byte: the first lowercase hex digit after the 40th byte becomes a different digit
  # (stays valid-looking JSON, so a reader that only parses would not notice).
  python3 - "$f" <<'PY' || exit 2
import sys
p = sys.argv[1]; b = bytearray(open(p, "rb").read())
for i in range(40, len(b)):
    if chr(b[i]) in "0123456789abcdef":
        b[i] = ord("1") if chr(b[i]) != "1" else ord("2"); break
else:
    sys.exit("no hex digit to flip in " + p)
open(p, "wb").write(bytes(b))
PY
  cmp -s "$f" "$f.orig" && { echo "SELF-TEST FAIL: the plant did not change $s"; exit 1; }
  out="$(run_check "$tmp")"; rc=$?
  if [ $rc -eq 0 ] || ! printf '%s' "$out" | grep -q "DRIFT .*poa-network-genesis-$s-v1.json"; then
    echo "SELF-TEST FAIL: a one-byte edit to $s was NOT refused by name (rc=$rc):"; echo "$out"; fails=$((fails+1))
  else
    echo "red: one-byte edit to $s refused (rc=$rc)"
  fi
  mv "$f.orig" "$f"
done
[ $fails -eq 0 ] || exit 1
echo "self-test: control passes, ${#STEMS[@]}/${#STEMS[@]} planted one-byte edits refused"
