# pg-dregg quickstart — for the dregg developer

You are building on dregg. `pg-dregg` makes **postgres a native dregg surface**:
your node's state is queryable SQL, authorization is caps, and the mirror is the
store. "Your node IS your postgres." You reach for pg as naturally as for the
SDK — `SELECT`s replace bespoke query endpoints, and the same cap token that
authorizes a tool call gates the rows.

This is the path from committed turns to a queryable, cap-gated state surface.
Every query below runs against the **synthetic-demo data** — a hand-built chain
of committed turns (genesis → transfer → grant → organ op) that stands in for
the node's live commit log until the M2 writer lands. Run the whole arc:

```bash
cd pg-dregg
cargo run --example end_to_end     # the postgres-free cores, end to end
cargo pgrx test pg14               # the SAME arc through real pg14 RLS
```

---

## 1. The model: state is a projection of verified turns

The spine invariant (`docs/PG-DREGG.md` §8):

> **Reads are free SQL; state mutates ONLY through verified turns.**

Every row in the `dregg.*` schema is the post-image of a turn the kernel already
verified (the commit log's `CommitRecord`). Applications `SELECT` freely; a bare
`INSERT/UPDATE/DELETE` by an app role is forbidden at the privilege layer. The
only writer is `dregg_kernel` (the `BYPASSRLS` SECURITY-DEFINER writer); in Tier
C even its writes pass the `dregg_verify_turn` CHECK.

The projection is owned in Rust, postgres-free and `cargo test`-proven, in
`src/mirror.rs`:

- `Domain` + `MemCell` — the universal-memory model (`docs/UNIVERSAL-MEMORY.md`):
  ONE multiset over `Domain × κ`. A new state component is a new domain *value*,
  never a new table.
- `CellRow` / `TurnRow` / `CapRow` — typed query-sugar projections of
  `dregg_cell::Cell`, the commit log, and `CapabilityRef`.
- `MirrorBatch` — one verified turn's rows, the serde wire unit the node ships
  into postgres (the M2 writer; see §6).
- `RootChain` — the anti-substitution tooth: turn *N*'s post-root is turn
  *N+1*'s pre-root, so `dregg.turns` is a hash chain a light client walks.

The schema is **emitted from that same Rust** (`mirror::ddl::tier_b()`), so the
tables can't drift from the row types — pinned by the
`emitted_ddl_agrees_with_committed_sql_file` test.

---

## 2. Install the store

```sql
CREATE EXTENSION pg_dregg;
-- install the Tier-B schema (tables + the query-surface views + read-side RLS +
-- the write-lockdown role model). This is mirror::ddl::tier_b() — also the file
-- sql/schema-tierB.sql.
SELECT dregg_install_schema();   -- (or run sql/schema-tierB.sql)
```

The M2 writer tails the node's commit log and, per committed turn, ships a
`MirrorBatch` that the mirror writes after the `RootChain` tooth accepts it.
Until M2 lands, the synthetic story (`src/synth.rs`) populates the same tables.

---

## 3. Query cells, balances, the ledger

The "show me the money" view, `dregg.cell_balances` (hex-keyed, balance-first):

```sql
SELECT cell, balance, nonce, lifecycle
FROM dregg.cell_balances
ORDER BY balance DESC;
--  c011…   999500   1   Active     ← TREASURY after paying out
--  a111…      400   2   Active     ← ALICE (grant + organ op bumped the nonce)
--  b011…      100   0   Active     ← BOB
```

Conservation, as a query — sum the touched-cell balances of a turn:

```sql
SELECT sum(balance) FROM dregg.cells;     -- = the genesis total, value conserved
```

Time-travel / per-turn history is the `cell_history` projection (a cell by
`(id, ordinal)`); the latest post-image is `dregg.cells`.

---

## 4. Query the delegation graph (caps)

The grant turn installed an `ALICE → BOB` edge. The `dregg.cap_edges` view is
the delegation graph; `WITH RECURSIVE` over it walks reachability — the
no-amplification audit surface (a child's `allowed_effects ⊆ its grantor's`):

```sql
SELECT src, dst, slot, permissions, expires_at FROM dregg.cap_edges;
--  a111…   b011…   0   {"transfer":"delegated"}   10000

-- the delegation tree rooted at one cell:
WITH RECURSIVE reach(src, dst, depth) AS (
    SELECT src, dst, 1 FROM dregg.cap_edges WHERE src = '\xa111…'
  UNION ALL
    SELECT e.src, e.dst, r.depth + 1
    FROM dregg.cap_edges e JOIN reach r ON e.src = r.dst
    WHERE r.depth < 32)
SELECT * FROM reach;
```

---

## 5. Query the receipt chain (the light client, in SQL)

`dregg.receipt_chain` is the turn hash chain — each row's `prev_root` is the
prior row's `ledger_root`. A consumer walks it to verify non-omission:

```sql
SELECT ordinal, creator, prev_root, ledger_root FROM dregg.receipt_chain;
--  0   c011…   0000…   3488…       ← genesis (prev_root pinned)
--  1   c011…   3488…   1063…       ← transfer  (chains onto turn 0)
--  2   a111…   1063…   5770…       ← grant
--  3   a111…   5770…   203e…       ← organ op
```

That each `prev_root` equals the prior `ledger_root` is the `RootChain` tooth.
A batch that doesn't chain is **refused** — proven by
`root_chain_gate_refuses_a_tampered_batch` (`cargo pgrx test pg14`) and the
`examples/end_to_end.rs` anti-substitution step.

---

## 6. The universal-memory table (the honest model)

The typed tables (§3–5) are derived boundary views over one Blum multiset,
`dregg.memory`, over `Domain × κ` (`docs/UNIVERSAL-MEMORY.md`):

```sql
SELECT domain, encode(collection,'hex') AS cell, encode(key,'hex') AS k,
       encode(value,'hex') AS v, last_ordinal
FROM dregg.memory WHERE domain = 'registers';
```

The map roots (cap / nullifier / heap / index) are `SELECT`s over the present
cells of a domain — derived boundary roots, exactly as in the kernel.

---

## 7. Authorization is caps — the explorer IS your capabilities

Every state table is RLS-gated by the same Tier-A cap layer the pg-user
quickstart uses: a reader sees only the cells/turns/caps their token admits.
"The explorer is your capabilities, expressed as the rows you may `SELECT`."

```sql
SELECT set_config('dregg.token', 'dga1_…', true);
SELECT * FROM dregg.cell_balances;   -- only your admitted cells
```

An attenuated token narrows the visible rows to a strict subset — proven on the
mirror tables by `tier_b_mirror_rls_narrows_cell_visibility` (operator sees 3
cells, an ALICE-only token sees 1). Your SDKs and explorer query through pg with
the bearer token they already hold; no separate authorization surface.

---

## 8. Submit a verified turn FROM postgres (the write path)

The bidirectional half: a pg-user submits a SIGNED turn from postgres, gated to
exactly the agents their capability authorizes. Install the outbox, then submit.

```sql
SELECT dregg_install_write_outbox();   -- dregg.submit_queue + the submit_gate RLS

-- present a token that admits `submit` on your agent (minted with the issuer
-- secret out of band: cargo run --example mint -- --action submit --prefix <hex>)
SELECT set_config('dregg.token', 'dga1_…', true);
SET ROLE dregg_reader;                 -- so the submit_gate policy bites
SELECT dregg_submit_turn(:signed_turn_bytes, :agent_id_bytes);  -- returns a uuid
```

The enqueue is RLS-gated by `dregg_admits('submit', encode(agent,'hex'))`: submit
a turn for an agent your token does not authorize and Row-Level Security refuses
it. **Postgres never executes** — the turn is queued for the node, which drains
it through the real verified executor; only verified post-state lands. Reads stay
free SQL; writes stay verified-only. (Proven: `write_path_submit_turn_enqueues_
under_an_authorized_token` + `write_path_rls_refuses_submitting_for_an_
unauthorized_agent`, `cargo pgrx test pg18`.)

---

## 9. The roadmap from here

| Tier | What | Status |
|---|---|---|
| **A** | caps as RLS (the M1 functions) | **landed**, proven (`cargo test`, `cargo pgrx test pg18`) |
| **B** | dregg state as queryable tables (this doc) | **LANDED + live on pg18**: the node→pg writer (`node/src/pg_mirror.rs` `pg_live::PgSink`) ships each verified turn's `MirrorBatch` over `tokio-postgres`; the `RootChain` tooth gates it |
| **C** | the verified-store gate (`dregg_verify_turn` + `dregg.commit_log`) | **LANDED + live**: the trigger runs the REAL anti-substitution chain re-validator + materializes via MERGE; a tampered batch is refused by the engine (`dregg_install_tier_c()`). The per-turn *proof* gate (whole-chain IVC) is the orthogonal M3 item |
| **C-write** | submit a verified turn FROM pg (`dregg_submit_turn` + the outbox) | **LANDED** (§8): RLS-gated enqueue; the node-side drainer is M3 |
| **D** | the executor as a pg function (in-process) | the north star — one transaction mutates dregg state AND your app data atomically |

The whole arc runs live: `cargo pgrx test pg18`, or `scripts/e2e-live.sh` for a
standalone `psql` walk-through (rows land, the chain verifies, a tampered batch
is refused, the write-path gate narrows submission).

Tier D is where it gets awesome: `SELECT dregg_submit_turn_inproc(envelope)`
inside a transaction that also `UPDATE`s your app tables — kernel state and app
state commit together or not at all. No separate node can offer that cross-domain
atomicity. See `docs/PG-DREGG.md` §11.
