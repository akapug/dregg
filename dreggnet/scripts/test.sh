#!/usr/bin/env bash
#
# The DreggNet test gauntlet — one command to validate the repo.
#
#   scripts/test.sh                 the default offline-green path (service stack)
#                                   plus any gated lane whose env is present
#
# The default path needs no network, no Postgres, no live node. The env-gated
# lanes (Postgres, a live dregg node) run only when their env var is set, and are
# reported as SKIPPED — never failed — when it is absent. See docs/TESTING.md.
#
# This is the driver behind `make test`.

set -u
cd "$(dirname "$0")/.."

# The macOS/Linux-portable service stack — the always-green offline path. These
# are exactly the crates CI tests on the macOS service-stack job; their tests
# include the e2e / integration suites (cli e2e, the orchestration loop, durable
# resume, the site publish/serve round-trip, the lease→durable workflow).
SERVICE_CRATES="-p dreggnet-cli -p dreggnet-durable -p dreggnet-exec -p dreggnet-bridge -p dreggnet-control -p dreggnet-webapp -p dreggnet-ops"

fail=0
declare -a skipped=()

run() {
  # run "<label>" <cmd...>
  local label="$1"; shift
  echo
  echo "==> ${label}"
  echo "    \$ $*"
  if "$@"; then
    echo "    OK: ${label}"
  else
    echo "    FAIL: ${label}"
    fail=1
  fi
}

echo "================================================================"
echo " DreggNet test gauntlet"
echo "   platform : $(uname -s) $(uname -m)"
echo "   toolchain: $(rustc --version 2>/dev/null || echo '??')"
echo "================================================================"

# 1. The offline-green default — the service stack (unit + integration + e2e).
run "service stack (offline-green)" \
  cargo test ${SERVICE_CRATES}

# 2. Postgres durable lane (opt-in: DATABASE_URL).
if [ "${DATABASE_URL:-}" != "" ]; then
  run "durable Postgres lane (DATABASE_URL present)" \
    cargo test -p dreggnet-durable --features pg --test durable_resume_pg -- --ignored --test-threads=1
else
  skipped+=("durable Postgres lane — set DATABASE_URL=postgres://user:pass@host/db (and run \`make test-pg\`)")
fi

# 3. Verified on-chain read lane (opt-in: DREGGNET_LIVE_NODE + the AGPL dregg-verify feature).
if [ "${DREGGNET_LIVE_NODE:-}" != "" ]; then
  run "verified read lane (DREGGNET_LIVE_NODE present)" \
    cargo test -p dreggnet-bridge --features dregg-verify --test verified_read_live -- --ignored --nocapture
else
  skipped+=("verified read lane — needs a live dregg node + the AGPL dregg-verify feature: set DREGGNET_LIVE_NODE=host:port (and run \`make test-verify\`)")
fi

# 4. The Linux network/gateway lane — only meaningful on Linux (io_uring/epoll, the
#    Elide net/ closure). Documented, not auto-run here; cross-build from macOS with
#    `cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-gateway`.
if [ "$(uname -s)" != "Linux" ]; then
  skipped+=("Linux gateway/net lane — the httpe gateway + net/ stack are Linux-only (io_uring/epoll); build via \`make build-gateway\` or run \`make test-net\` on Linux")
fi

echo
echo "================================================================"
if [ ${#skipped[@]} -gt 0 ]; then
  echo " SKIPPED (env/platform-gated — not failures):"
  for s in "${skipped[@]}"; do echo "   - ${s}"; done
fi
if [ "${fail}" -eq 0 ]; then
  echo " RESULT: GREEN (default offline path passed)"
else
  echo " RESULT: FAILURES above"
fi
echo "================================================================"
exit "${fail}"
