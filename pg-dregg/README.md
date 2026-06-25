# pg-dregg

dregg's verified object-capability authorization, as a PostgreSQL extension.

`pg-dregg` lets an ordinary postgres application gate rows with **capability
tokens** instead of hand-rolled Row-Level-Security predicates over a JWT. One
signed, attenuable, offline-verifiable token decides what a session can see and
touch — and the same token works against the dregg kernel if you ever talk to
one. The decision is the same one dregg's kernel makes, from the same token; its
semantics are machine-checked in Lean (`metatheory/Dregg2/Authority/`) and
embodied, dependency-light and offline, in `dregg-auth`.

## What it is

Three things added to a database, in one extension:

- **cap-secure RLS** — a capability's authority (a predicate tree of `AttrEq`,
  `AttrPrefix`, temporal gates, and an `AllOf`/`AnyOf`/`Not` algebra) becomes a
  policy. A token attenuated to a narrower scope sees a **strict subset** of what
  its grantor saw — the no-amplification property, enforced, not hoped for. A
  predicate also compiles to a SQL/JSON `jsonpath` (`src/jsonpath.rs`) so reads
  and audits run as plain, index-eligible SQL over the mirrored state.
- **the verified store** — the mirror of committed turns is a hash chain: each
  turn's post-state root is the next turn's pre-state root. The engine itself
  runs that step gate (`dregg_verify_turn`, lifted from `mirror::verify_chain_step`,
  on the `dregg.commit_log` path), so a **tampered, reordered, or replayed batch
  is refused by the database** — no prover re-run, the head never moves on a
  refusal.
- **proof-attested ranges (Tier-C)** — a whole-chain IVC proof rides in as a
  versioned `bytea` transport and `dregg_attest_range` verifies it, attesting a
  receipt window against a pinned VK anchor. It is **fail-closed by default**: the
  heavyweight verifier is a build feature; absent it, the seam attests *nothing*
  rather than a forged anything.

## Play with it

No postgres, no node, no cargo-pgrx needed for the core. One command:

```bash
./scripts/demo.sh
# or directly:
cargo run --example three_pillars
```

It runs the three pillars on the postgres-free cores (the ones `cargo test`
proves) and narrates each, asserting the load-bearing property so the run is a
real artifact, not a print job. You will see a capability predicate compile to
jsonpath; an attenuated token narrow the visible rows (and a foreign-issuer
token see nothing); a tampered and a reordered batch each refused; and the
range-attest seam fail closed.

Verify the cores yourself:

```bash
cargo test            # the postgres-free cores (authz, jsonpath, mirror, attest)
```

Through real SQL, on a live psql session (PostgreSQL 18):

```bash
cargo install cargo-pgrx --version 0.17.0
cargo pgrx init --pg18 $(brew --prefix postgresql@18)/bin/pg_config
cargo pgrx run  pg18      # opens psql with the extension loaded
cargo pgrx test pg18      # the #[pg_test]s — the same arc, through SQL
```

Then `docs/QUICKSTART-pg-user.md` walks the 10-minute path from a plain table to
cap-gated RLS. The real Tier-C proof ADMIT (a genuine whole-chain proof accepted,
plus tamper-refusal) is a slow, circuit-backed test:

```bash
cargo test --features tier-c --test tier_c_real_proof -- --ignored --nocapture
```

## What it does, in SQL

```sql
CREATE EXTENSION pg_dregg;
ALTER SYSTEM SET dregg.issuer_pubkey = 'ea4a6c63…';  -- the trust root (public key)

ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
ALTER TABLE documents FORCE ROW LEVEL SECURITY;

-- a reader sees a row iff their presented token admits `read` on the row's id
CREATE POLICY cap_read ON documents FOR SELECT
  USING (dregg_admits('read', id::text));
```

```sql
SELECT set_config('dregg.token', 'dga1_…attenuated-to-public…', true);
SELECT id FROM documents;   -- the rows narrow to what the token admits
```

A malformed or absent issuer key makes every decision deny (fail-closed —
`SELECT dregg_issuer_status();` reports it). Revocation is instant and
per-credential (`dregg_revoke`); a filtered row's reason is nameable
(`dregg_cap_explain`).

## What it enables

- **Delegation without a round-trip.** Hand a sub-agent less by attenuating a
  token offline; the database enforces the narrowing. A flat JWT claim in a GUC
  structurally cannot guarantee child ⊆ grantor.
- **A store that re-validates instead of trusting.** The mirror is a projection
  of an artifact that already exists; the chain tooth means a read-only replica
  rejects forged history on its own.
- **One token, two enforcers.** The same `dga1_…` string a component carries to
  call a dregg tool is the string a postgres policy checks a `SELECT` against.

## Build modes

The default feature set is **empty** — `cargo test` builds only the
postgres-independent cores (`src/authz.rs`, `src/jsonpath.rs`, `src/mirror.rs`,
`src/attest.rs`) and needs no postgres or cargo-pgrx. The `#[pg_extern]` wrappers
are gated behind a `pgNN` feature (primary: `pg18`; pg13–pg17 available) and are
a cargo-pgrx job. `tier-c` links the Lean-free circuit verifier for the real
range-attest ADMIT; `tier-d` (a feasibility spike, `docs/PG-DREGG-TIER-D-SPIKE.md`)
covers the executor-in-backend endgame.

## Where things are

| | |
|---|---|
| the one-command demo | `scripts/demo.sh`, `examples/three_pillars.rs` |
| the postgres-user 10-minute path | `docs/QUICKSTART-pg-user.md` |
| the dregg-developer view (postgres as the dregg store) | `docs/QUICKSTART-dregg-dev.md` |
| recipes | `docs/COOKBOOK.md`, `sql/cookbook.sql` |
| cap-secured store (postgres-free) | `tests/cap_secured_store.rs` |
| the real Tier-C proof admit/refuse | `tests/tier_c_real_proof.rs` |
| the executor-in-postgres spike | `docs/PG-DREGG-TIER-D-SPIKE.md` |
