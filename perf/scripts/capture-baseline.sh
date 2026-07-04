#!/usr/bin/env bash
# capture-baseline.sh — run the FULL dregg perf suite and save a criterion
# baseline + a summary JSON. Idempotent: re-running overwrites the named
# baseline and the summary. Intended for the PERSVATI capture run once the code
# stabilizes — NOT for laptops (the FULL prove benches are minutes-scale).
#
#   Usage:  perf/scripts/capture-baseline.sh [BASELINE_NAME]
#   e.g.    perf/scripts/capture-baseline.sh main-2026-06-13
#
# What it does:
#   1. PERF_FULL=1 cargo bench -p dregg-perf -- --save-baseline <name>
#      (criterion writes per-bench estimates under target/criterion/.../<name>/)
#   2. cargo run --release -p dregg-perf --bin proof-sizes -- --json
#      -> perf/baselines/<name>/proof-sizes.json   (regression-tracked sizes)
#   3. cargo run --release -p dregg-perf --bin perf-report
#      -> perf/baselines/<name>/perf-report.txt     (the human-readable map)
#
# Compare a later run against this baseline with:
#   PERF_FULL=1 cargo bench -p dregg-perf -- --baseline <name>
set -euo pipefail

BASELINE="${1:-baseline-$(date +%Y%m%d)}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT="${ROOT}/perf/baselines/${BASELINE}"
mkdir -p "${OUT}"

echo "== dregg perf baseline capture: ${BASELINE} =="
echo "   repo: ${ROOT}"
echo "   out:  ${OUT}"
echo

# 1. Full criterion suite, FULL inputs, save the named baseline.
echo "-- [1/3] criterion suite (PERF_FULL=1, --save-baseline ${BASELINE})"
( cd "${ROOT}" && PERF_FULL=1 cargo bench -p dregg-perf -- --save-baseline "${BASELINE}" )

# 2. Proof-size microbench -> JSON (the wire-byte regression tracker).
echo "-- [2/3] proof-size microbench -> proof-sizes.json"
( cd "${ROOT}" && cargo run --release -q -p dregg-perf --bin proof-sizes -- --json ) \
    > "${OUT}/proof-sizes.json"
cat "${OUT}/proof-sizes.json"; echo

# 3. Full human-readable perf report -> txt.
echo "-- [3/3] perf-report -> perf-report.txt"
( cd "${ROOT}" && cargo run --release -q -p dregg-perf --bin perf-report ) \
    | tee "${OUT}/perf-report.txt" > /dev/null

# Stamp the run.
{
    echo "baseline: ${BASELINE}"
    echo "captured: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "host:     $(uname -srm)"
    echo "git:      $(cd "${ROOT}" && git rev-parse --short HEAD 2>/dev/null || echo '?')"
} > "${OUT}/META.txt"

echo
echo "== done. baseline '${BASELINE}' saved =="
echo "   criterion estimates: ${ROOT}/target/criterion/*/${BASELINE}/"
echo "   proof sizes:         ${OUT}/proof-sizes.json"
echo "   perf report:         ${OUT}/perf-report.txt"
echo "   meta:                ${OUT}/META.txt"
echo
echo "   compare a later run:  PERF_FULL=1 cargo bench -p dregg-perf -- --baseline ${BASELINE}"
