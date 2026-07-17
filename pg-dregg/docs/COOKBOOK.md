# pg-dregg — the cap-gated query cookbook

*A capability **is** a database view. The rows you may read **are** your
authority, and the kernel's guarantees — no-amplification, conservation,
non-omission, anti-substitution — are all ordinary SQL over the materialized
state.*

This cookbook is a small library of copy-paste SQL recipes over the pg-dregg
mirror schema (Tier B/C, `.docs-history-noclaude/PG-DREGG.md` §8–§10). Each recipe is a real tool
**and** a teaching artifact, and every one **runs** against the live mirror.
Pair it with the browser glass — `site/explorer/caps-as-rows.html` — which is
the same "a cap is a view" insight rendered as a page: present a token, watch
the rows narrow.

- **The runnable file:** `pg-dregg/sql/cookbook.sql` (parameterized via psql
  `\set`; runs top-to-bottom against a mirror DB).
- **The seed:** `pg-dregg/sql/cookbook-seed.sql` (installs a demo delegation
  graph + per-cell history so the recipes have data; idempotent).

```sh
# against the cargo-pgrx-managed pg18 (the prior pg lanes' dev box):
psql -h ~/.pgrx -p 28818 -d pg_dregg_mirror -f sql/cookbook-seed.sql   # once
psql -h ~/.pgrx -p 28818 -d pg_dregg_mirror -f sql/cookbook.sql        # the recipes
```

## The spine invariant (why reads can be this free)

> **Reads are free SQL; state mutates ONLY through verified turns.**

Every row in `dregg.*` is the post-image of a turn the kernel already verified.
A `SELECT` cannot violate conservation / no-amplification / nullifier-uniqueness
— it only observes — so the full power of SQL (joins, window functions,
recursive CTEs) is sound by construction over the mirror. Recipes 1–6 are all
reads. Recipe 7 is the other half of the invariant: the database engine refusing
a tampered write.

---

## Recipe 1 — the delegation tree (`WITH RECURSIVE`)

The capability delegation graph is `holder → target` edges, surfaced as the
shipped view `dregg.cap_edges` (over `dregg.capabilities`). A `WITH RECURSIVE`
walks it from one root cell to the whole reachable subtree: *who can this
authority ultimately reach, and by what chain?* The `NOT dst = ANY(path)` cycle
guard keeps a back-edge from looping; `depth < 32` bounds pathological graphs.

```sql
WITH RECURSIVE reach(src, dst, depth, path) AS (
    SELECT src, dst, 1, ARRAY[src, dst]
    FROM dregg.cap_edges
    WHERE src = '\xaa00…'::bytea                 -- the root cell
  UNION ALL
    SELECT e.src, e.dst, r.depth + 1, r.path || e.dst
    FROM dregg.cap_edges e
    JOIN reach r ON e.src = r.dst
    WHERE r.depth < 32 AND NOT e.dst = ANY(r.path)
)
SELECT depth, src AS grantor, dst AS delegate, path AS chain FROM reach;
```

Live output (the seeded `org → alice → bob → carol` chain):

```
 depth | grantor | delegate |                chain
-------+---------+----------+--------------------------------------
     1 | aa0000  | bb0000   | aa0000 -> bb0000
     2 | bb0000  | cc0000   | aa0000 -> bb0000 -> cc0000
     3 | cc0000  | dd0000   | aa0000 -> bb0000 -> cc0000 -> dd0000
```

---

## Recipe 2 — the no-amplification audit (child effects ⊆ grantor's)

The capability invariant: **a delegate may grant downstream only effects it was
itself granted.** `dregg.capabilities.allowed_effects` is the attenuation set (a
jsonb array of effect strings). This recipe explodes every edge's effects,
compares each holder's outgoing grants against the effects that holder was
*itself* granted (the union over its inbound edges), and **flags any effect a
holder grants but never held** — an amplification that must never exist.

A *genesis root* — a holder that is never a delegation target, minted by the
kernel rather than delegated — legitimately holds effects with no inbound edge,
so the audit marks it `is_genesis_root` and does not count it as a violation.

```sql
WITH edge_effect AS (
  SELECT encode(holder,'hex') AS holder, encode(target,'hex') AS target, slot,
         eff.effect
  FROM dregg.capabilities c,
       LATERAL jsonb_array_elements_text(c.allowed_effects) AS eff(effect)
),
held  AS (SELECT target AS who, effect FROM edge_effect GROUP BY target, effect),
roots AS (SELECT holder FROM edge_effect EXCEPT SELECT target FROM edge_effect)
SELECT e.holder AS delegate, e.target, e.slot,
       (e.holder IN (SELECT holder FROM roots)) AS is_genesis_root,
       array_agg(e.effect) FILTER (WHERE h.who IS NULL) AS over_granted,
       (bool_or(h.who IS NULL)
        AND e.holder NOT IN (SELECT holder FROM roots)) AS violation
FROM edge_effect e
LEFT JOIN held h ON h.who = e.holder AND h.effect = e.effect
GROUP BY e.holder, e.target, e.slot
ORDER BY violation DESC;
```

Live output — the seed plants one deliberate amplification (`bob → alice
{admin}`: bob was only ever granted `{read,transfer}`), and the audit catches
exactly it:

```
 delegate | target | slot | is_genesis_root |   over_granted   | violation
----------+--------+------+-----------------+------------------+-----------
 cc0000   | bb0000 |    1 | f               | {admin}          | t          ← caught
 aa0000   | bb0000 |    0 | t               | {…}              | f          ← genesis root, fine
 bb0000   | cc0000 |    0 | f               | (none)           | f
 cc0000   | dd0000 |    0 | f               | (none)           | f
```

The same audit collapses to **one boolean** for a CI gate or a `CHECK`:

```sql
... SELECT NOT bool_or(h.who IS NULL
                       AND e.holder NOT IN (SELECT holder FROM roots))
             AS no_amplification ...
```

(`f` on the seeded graph — because of the planted violation; on a sound graph it
is `t`.) The shipped view `dregg.cap_attenuations` (a `JSON_TABLE` explosion) is
the flat one-row-per-effect surface if you only want the list.

---

## Recipe 3 — the conservation check (`sum(balance) = genesis`)

Value is neither created nor destroyed. Across the whole live ledger, the sum of
every cell's balance equals the supply minted at genesis (add mint/burn cells to
the genesis term if your deployment has them).

```sql
WITH genesis(total) AS (VALUES (1885::bigint))
SELECT g.total AS genesis_supply, sum(c.balance) AS live_supply,
       sum(c.balance) - g.total AS drift, (sum(c.balance) = g.total) AS conserved
FROM dregg.cells c, genesis g GROUP BY g.total;
```

```
 genesis_supply | live_supply | drift | conserved
----------------+-------------+-------+-----------
           1885 |        1885 |     0 | t
```

Per-turn conservation surfaces the touched-cell post-balances per ordinal from
`dregg.cell_history` (a transfer's touched-set deltas sum to zero).

---

## Recipe 4 — the receipt-chain walk (in-SQL non-omission)

`dregg.turns` is a hash chain: turn *N*'s post-state root (`ledger_root`) is turn
*N+1*'s pre-state root (`prev_root`). A `lag` window function walks the chain and
asserts each link **in SQL** — a light client, no node. A broken link
(`chains_ok = f`) or an ordinal gap (`gap <> 1`) is an omitted or substituted
turn.

```sql
SELECT ordinal,
       prev_root,
       lag(ledger_root) OVER w AS expected_prev_root,
       (prev_root = lag(ledger_root) OVER w) AS chains_ok,
       (ordinal - lag(ordinal) OVER w)       AS ordinal_gap
FROM dregg.receipt_chain
WINDOW w AS (ORDER BY ordinal) ORDER BY ordinal;
```

```
 ordinal | prev_root | expected_prev_root | chains_ok | ordinal_gap
---------+-----------+--------------------+-----------+-------------
       0 | 00000000  |                    |           |
       1 | 01010101  | 01010101           | t         |           1
       2 | 02020202  | 02020202           | t         |           1
```

As one assertion (`chain_intact = t`), and the **tamper-detection** demo — the
same walk over a CTE that simulates corrupting turn 1's roots makes both adjacent
links light up `chains_ok = f` (we never mutate the table; writes are
verified-only):

```
-- tamper detection (CTE corrupts turn 1):
 ordinal | prev_root | expected_prev_root | chains_ok
---------+-----------+--------------------+-----------
       1 | deadbeef  | 01010101           | f          ← caught
       2 | 02020202  | deadbeef           | f          ← caught
```

*An auditor needs no node — just `psql` and the published chain.*

---

## Recipe 5 — per-cell time-travel

`dregg.cell_history` keeps every post-image (the cell-by-`(id, ordinal)` index of
the commit log). This walks one cell's balance / nonce / commitment across the
turns that touched it, with the per-step delta from a window function.

```sql
SELECT h.ordinal, t.height, h.balance,
       h.balance - lag(h.balance) OVER w AS balance_delta,
       encode(h.cell_root,'hex') AS cell_root_commitment
FROM dregg.cell_history h JOIN dregg.turns t ON t.ordinal = h.ordinal
WHERE h.cell_id = '\x5eff…'::bytea
WINDOW w AS (ORDER BY h.ordinal) ORDER BY h.ordinal;
```

```
 ordinal | height | balance | balance_delta | cell_root_commitment
---------+--------+---------+---------------+----------------------
       0 |      1 |       0 |               | 5e00
       1 |      2 |      20 |            20 | 5e01
```

The node serves historical *commitments* (the canonical objects a verifier
checks), so the cell_root column is the per-step authenticated commitment, not a
re-derivable convenience.

---

## Recipe 6 — caps-as-rows (the gate respected, and made legible)

The thesis recipe, and the SQL twin of the browser explorer: *your capabilities,
expressed as the rows you may `SELECT`.* Two faces.

**(6a) The gate respected.** Become the unprivileged reader role, present the
token, `SELECT`: RLS returns **only** the admitted rows — never a bypass. The
token is **transaction-local** (`set_config(..., true)`, the safe pooled-conn
default), so the `SET` and the `SELECT` must share a transaction:

```sql
BEGIN;
  SET LOCAL ROLE dregg_reader;                    -- the unprivileged app role
  SELECT set_config('dregg.token', 'dga1_…', true);  -- present the bearer token
  SELECT encode(cell_id,'hex'), balance FROM dregg.cells ORDER BY cell_id;
COMMIT;
```

Live, the narrowing is observed (not asserted) — mint with
`cargo run --example mint -- --seed 7 --action read --prefix <p>`:

```
 token presented (read, prefix …) | rows the reader sees
----------------------------------+----------------------------------
 prefix "5e"                      | 1   (only the 5eff… cell)
 prefix ""  (everything)          | 6   (all cells)
 no token                         | 0   (fail-closed)
```

That is the no-amplification property made physical: a token attenuated to a
narrower prefix sees a **strict subset** of the rows, with no policy or data
changed.

**(6b) The gate explained.** `dregg_cap_explain` takes the token as an *argument*
(so it does not depend on the session role/GUC) and names, per row, **why** it is
admitted or filtered — the miserable vanished-row problem, solved:

```sql
SELECT encode(cell_id,'hex') AS cell,
       dregg_cap_admits (:'tok','read',encode(cell_id,'hex'),
                         extract(epoch from now())::bigint) AS admitted,
       dregg_cap_explain(:'tok','read',encode(cell_id,'hex'),
                         extract(epoch from now())::bigint) AS reason
FROM dregg.cells ORDER BY cell_id;
```

```
  cell  | admitted |                       reason
--------+----------+-----------------------------------------------------------------
 5c9456 | f        | refused: block 0 requires attribute `resource` starts with `5e`
 5eff91 | t        | allowed
 aa0000 | f        | refused: block 0 requires attribute `resource` starts with `5e`
 …
```

This is the pair the browser explorer renders: the admitted set as a list, and
the per-row verdict + reason on demand.

---

## Recipe 7 — the write gate (the engine refuses a tampered turn)

The spine invariant's other half. Run against the Tier-C store
(`pg_dregg_e2e`), the database **engine** — not a `SELECT`-side check — refuses a
turn whose `prev_root` does not chain onto the head root. This is
`dregg_verify_turn` inside the `dregg.commit_log` `BEFORE INSERT` trigger
(`schema-tierC.sql`):

```sql
INSERT INTO dregg.commit_log
  (ordinal,height,block_id,block_executed_up_to,turn_hash,creator,
   receipt_hash,ledger_root,prev_root,cells)
VALUES (2, 2, '\xbb'::bytea, 2, '\xcafe'::bytea, '\xc0'::bytea,
        '\xab'::bytea, '\x333333'::bytea, '\xdeadbeef'::bytea, '[]'::jsonb);
-- ERROR: dregg: turn 2 does not chain onto the head root — refused
--        (anti-substitution)
```

A correctly-chaining turn (`prev_root` = the current head `ledger_root`) is
accepted and materializes its cells in the same transaction. Reads stay free;
writes stay verified-only.

---

## What is tested-against-live-pg vs parse-only

Everything in this cookbook was run against a **live PostgreSQL 18** (the
cargo-pgrx-managed instance, port 28818) with the `pg_dregg` extension installed:

- **Recipes 1–6 — tested against live pg** on `pg_dregg_mirror` (the Tier-B query
  surface), against the seeded graph (`cookbook-seed.sql`). The full
  `cookbook.sql` runs top-to-bottom with **zero errors**.
- **Recipe 6 narrowing (6a) — tested against live pg** with real minted tokens
  (`dga1_…`): the reader sees 1 / 6 / 0 rows for prefix-`5e` / `""` / no-token,
  and `dregg_cap_explain` (6b) names the per-row reason.
- **Recipe 7 — tested against live pg** on `pg_dregg_e2e` (the Tier-C store): the
  non-chaining `INSERT` is refused by the engine with the anti-substitution
  error verbatim.

The recipes respect the RLS gate (they read as `dregg_reader` with a presented
token, never bypass it). The write recipe demonstrates the engine-level gate
rather than circumventing it.
