#!/usr/bin/env bash
# pg-dregg demo — the ONE command a newcomer runs.
#
# It builds and runs the postgres-free three-pillars example, which SHOWS, on this
# host, with no postgres and no node:
#
#   1. cap-secure RLS   — a capability predicate compiles to jsonpath and filters rows
#   2. the verified store — a tampered / reordered history is REFUSED by the engine
#   3. proof-attested ranges — the Tier-C range-attest seam (fail-closed by default)
#
# No postgres, no cargo-pgrx, no node required: it runs the cores that `cargo test`
# proves. The same arc runs through real SQL on pg18 (see the notes printed at the end).
set -euo pipefail

cd "$(dirname "$0")/.."

echo "==> cargo run --example three_pillars   (postgres-free; the cores cargo test proves)"
echo
cargo run --quiet --example three_pillars

cat <<'EOF'

────────────────────────────────────────────────────────────────────────────
WANT TO SEE IT THROUGH REAL SQL?  (a live psql session on PostgreSQL 18)

  cargo install cargo-pgrx --version 0.17.0
  cargo pgrx init --pg18 $(brew --prefix postgresql@18)/bin/pg_config
  cargo pgrx run pg18           # opens psql with the extension loaded
  cargo pgrx test pg18          # the #[pg_test]s — the SAME arc, through SQL

Then follow docs/QUICKSTART-pg-user.md (10 minutes from a plain table to cap-gated RLS).

WANT THE REAL PROOF ADMIT (Tier-C, ~minutes, needs the circuit verifier)?

  cargo test --features tier-c --test tier_c_real_proof -- --ignored --nocapture
────────────────────────────────────────────────────────────────────────────
EOF
