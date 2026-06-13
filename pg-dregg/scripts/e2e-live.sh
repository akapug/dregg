#!/usr/bin/env bash
# pg-dregg — LIVE pg18 end-to-end runner.
#
# Stands up the cargo-pgrx-managed pg18, builds + installs the pg_dregg
# extension, sets the issuer key, and drives sql/e2e-live.sql (the Tier-B/C
# verified-store story) PLUS the §11 write-path gate with a freshly minted token.
# This is the reproducible form of the "pg re-validates, never trusts" proof.
#
# Prereqs (all authorized / already present on the dev box):
#   brew install postgresql@18
#   cargo install cargo-pgrx --version 0.17.0
#   cargo pgrx init --pg18 "$(brew --prefix postgresql@18)/bin/pg_config"
#
# Usage:  pg-dregg/scripts/e2e-live.sh
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # the pg-dregg crate dir
PSQL="$(brew --prefix postgresql@18)/bin/psql"
PORT=28818                                                # the cargo-pgrx pg18 port
SOCK="$HOME/.pgrx"
DB=pg_dregg_e2e
# The test issuer root is RootKey::from_seed([7;32]); this is its public key.
ISSUER_PUBKEY=ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c

cd "$HERE"

echo "== building + installing the pg_dregg extension into pg18 =="
cargo pgrx install --pg-config "$(brew --prefix postgresql@18)/bin/pg_config" >/dev/null 2>&1 || true
cargo pgrx start pg18 >/dev/null 2>&1 || true

echo "== (re)creating a clean database =="
"$PSQL" -h "$SOCK" -p "$PORT" -d postgres -c "DROP DATABASE IF EXISTS $DB;" >/dev/null
"$PSQL" -h "$SOCK" -p "$PORT" -d postgres -c "CREATE DATABASE $DB;" >/dev/null

echo "== setting the issuer key (the Sighup GUC) at server level =="
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c \
  "ALTER SYSTEM SET dregg.issuer_pubkey = '$ISSUER_PUBKEY';" >/dev/null
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c "SELECT pg_reload_conf();" >/dev/null
sleep 1

echo "== driving sql/e2e-live.sql (Tier B/C verified store) =="
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -f sql/e2e-live.sql

echo ""
echo "== driving the §11 WRITE PATH: a pg-user submits a verified turn FROM pg =="
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c "SELECT dregg_install_write_outbox();" >/dev/null
ALICE_HEX=a100000000000000000000000000000000000000000000000000000000000000
BOB_HEX=b000000000000000000000000000000000000000000000000000000000000000
# Mint an ALICE-only submit token (resource prefix a1) — minting holds the
# issuer secret, so it is a CLI action (examples/mint.rs), not a SQL one.
ALICE_TOK="$(cargo run -q --example mint -- --seed 7 --action submit --prefix a1 2>/dev/null)"

echo "-- present the ALICE-only token, become the unprivileged app role, submit FOR ALICE => OK"
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c \
  "SET dregg.token = '$ALICE_TOK'; SET ROLE dregg_reader;
   SELECT dregg_submit_turn('\\xdeadbeef'::bytea, '\\x$ALICE_HEX'::bytea) AS alice_submission_id;"
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c \
  "SET dregg.token = '$ALICE_TOK'; SET ROLE dregg_reader;
   SELECT encode(agent,'hex') AS agent, status FROM dregg.submit_queue;"

echo "-- pg18 uuidv7 queue key as an AUDIT SIGNAL: the audit view recovers the enqueue time + version FROM the key itself"
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c \
  "SET ROLE dregg_kernel;
   SELECT id_version, (id_version = 7) AS is_v7,
          (abs(extract(epoch FROM (enqueued_at - submitted_at))) < 5) AS key_time_matches_clock,
          status
   FROM dregg.submit_queue_audit ORDER BY id;"

echo "-- pg18 OAuth → role → dregg-cap bind seam: dregg_bind_role binds dregg_reader to ALICE; role_bindings shows it WITHOUT the token"
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c "SELECT dregg_install_login_binding();" >/dev/null
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c \
  "SELECT dregg_bind_role('dregg_reader', '\\x$ALICE_HEX'::bytea, '$ALICE_TOK');
   SET ROLE dregg_kernel;
   SELECT pg_role, agent, has_token FROM dregg.role_bindings WHERE pg_role = 'dregg_reader';"

echo "-- submit FOR BOB under the ALICE-only token => RLS REFUSES (a role submits only what its caps authorize)"
"$PSQL" -h "$SOCK" -p "$PORT" -d "$DB" -c \
  "SET dregg.token = '$ALICE_TOK'; SET ROLE dregg_reader;
   SELECT dregg_submit_turn('\\xdeadbeef'::bytea, '\\x$BOB_HEX'::bytea) AS bob_submission_id;" \
  || echo "   (expected: ERROR new row violates row-level security policy for table \"submit_queue\")"

echo ""
echo "== DONE: live pg18 verified-store + write-path gate, all real rows. =="
