#!/usr/bin/env bash
# confined-boot.sh — de-risk the homeserver-grain's confinement (GRAIN-HOMESERVER.md
# step 3). Boots the heavy rocksdb+tokio continuwuity homeserver under a
# deny-default macOS Seatbelt profile (sandbox/homeserver.sb) — the faithful proxy
# for the firmament confined-spawn door spec — and proves it SERVES the CS API
# (GET /_matrix/client/versions -> 200) while confined.
#
# macOS sandbox-exec speaks the SAME SBPL language firmament emits, so the minimal
# allow-set that boots+serves here IS the spec for grant_read_write(db_dir) +
# grant_listen(port).
#
#   usage:  bash deos-homeserver/scripts/confined-boot.sh
#           KEEP=1 ...   # leave the confined server up afterward
#           DENIALS=1 ...# (default on failure) dump Sandbox denials from the log
set -uo pipefail

HS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # deos-homeserver/
PROFILE="$HS_DIR/sandbox/homeserver.sb"
BIN="$HS_DIR/target/debug/deos-homeserver"
SERVER_NAME="${SERVER_NAME:-localhost}"

# System rocksdb link env (skip the C++ build; the bin is prebuilt anyway).
export ROCKSDB_LIB_DIR="$(brew --prefix rocksdb)/lib"
export ROCKSDB_INCLUDE_DIR="$(brew --prefix rocksdb)/include"
HOMEBREW="$(brew --prefix)"

# FIXED db root (temp). std::env::temp_dir() honours $TMPDIR, so pinning TMPDIR
# pins the RocksDB dir under a dir we control -> the ONE write subpath (DB_DIR).
# (The bin still appends deos-homeserver-<pid>-<n>/db; DB_DIR is the parent the
# firmament door canonicalises to.)
# Resolve symlinks (/var -> /private/var) so the -D DB_DIR literal matches the
# canonical path the sandbox kernel checks writes against.
RUN_ROOT="$(cd "$(mktemp -d -t deos-hs-confined.XXXXXX)" && pwd -P)"
export TMPDIR="$RUN_ROOT"
DB_DIR="$RUN_ROOT"

if [[ ! -x "$BIN" ]]; then
  echo "!! missing $BIN — build it first:" >&2
  echo "   ( cd $HS_DIR && ROCKSDB_LIB_DIR=$ROCKSDB_LIB_DIR ROCKSDB_INCLUDE_DIR=$ROCKSDB_INCLUDE_DIR cargo build --bin deos-homeserver )" >&2
  exit 1
fi

OUT="$(mktemp -t deos-hs-out.XXXXXX)"
ERR="$(mktemp -t deos-hs-err.XXXXXX)"
HS_PID=""
START_TS="$(date '+%Y-%m-%d %H:%M:%S')"

cleanup() {
  if [[ -n "$HS_PID" ]] && kill -0 "$HS_PID" 2>/dev/null; then
    if [[ "${KEEP:-0}" == "1" ]]; then
      echo "==> KEEP=1 — leaving confined homeserver up (pid $HS_PID)"
      return
    fi
    kill -TERM "$HS_PID" 2>/dev/null || true
    wait "$HS_PID" 2>/dev/null || true
  fi
  [[ "${KEEP:-0}" == "1" ]] || rm -rf "$RUN_ROOT" "$OUT" "$ERR"
}
trap cleanup EXIT

echo "==> profile : $PROFILE"
echo "==> bin     : $BIN"
echo "==> DB_DIR  : $DB_DIR"
echo "==> booting under deny-default sandbox-exec ..."

/usr/bin/sandbox-exec \
  -f "$PROFILE" \
  -D SELF="$BIN" \
  -D DB_DIR="$DB_DIR" \
  -D HOMEBREW="$HOMEBREW" \
  "$BIN" "$SERVER_NAME" >"$OUT" 2>"$ERR" &
HS_PID=$!

URL=""
for i in $(seq 1 90); do
  if ! kill -0 "$HS_PID" 2>/dev/null; then
    echo "!! confined homeserver exited early (after ${i}s). stderr:" >&2
    tail -20 "$ERR" >&2
    break
  fi
  line="$(grep -m1 '^READY ' "$OUT" 2>/dev/null || true)"
  if [[ -n "$line" ]]; then
    URL="${line#READY }"; URL="${URL%$'\r'}"
    echo "==> READY (after ${i}s): $URL"
    break
  fi
  sleep 1
done

RC=1
if [[ -n "$URL" ]]; then
  CODE="$(curl -s -o /dev/null -w '%{http_code}' "$URL/_matrix/client/versions" || echo 000)"
  echo "==> GET /_matrix/client/versions -> HTTP $CODE"
  if [[ "$CODE" == "200" ]]; then
    echo "==> PASS: continuwuity boots + serves 200 under deny-default confinement."
    RC=0
  else
    echo "!! server up but CS API did not answer 200"
  fi
else
  echo "!! never reached READY under confinement"
fi

# On failure (or DENIALS=1) surface the kernel's Sandbox denials — these name the
# exact operation/path to add to the profile.
if [[ "$RC" != "0" || "${DENIALS:-0}" == "1" ]]; then
  echo "==> Sandbox denials since boot (operation + path to grant):"
  log show --style syslog --start "$START_TS" \
    --predicate 'process == "deos-homeserver" AND (eventMessage CONTAINS "deny" OR senderImagePath CONTAINS[c] "Sandbox")' \
    2>/dev/null | grep -iE 'deny|sandbox' | sed 's/^/    /' | tail -60 || true
fi

echo "==> stderr tail:"; tail -8 "$ERR" | sed 's/^/    /'
exit $RC
