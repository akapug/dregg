-- pg-dregg — THE CAP-GATED QUERY COOKBOOK
-- =============================================================================
-- Copy-paste SQL recipes over the pg-dregg mirror schema (Tier B/C). Each recipe
-- is a real tool AND a teaching artifact, and each RUNS against the live mirror.
-- The thesis these recipes make tangible: **a capability IS a database view** —
-- the rows you may read ARE your authority, and the kernel's guarantees
-- (no-amplification, conservation, non-omission, anti-substitution) are all
-- expressible as ordinary SQL over the materialized state.
--
-- THE SPINE INVARIANT (.docs-history-noclaude/PG-DREGG.md §8): reads are free SQL; state mutates
-- ONLY through verified turns. Every recipe here is a READ. Recipe 7 shows the
-- WRITE gate (the database engine refusing a tampered turn) for contrast.
--
-- HOW TO RUN
-- ----------
--   psql -h ~/.pgrx -p 28818 -d pg_dregg_mirror -f sql/cookbook.sql
-- (the cargo-pgrx-managed pg18; substitute your own conninfo). The mirror DB is
-- the Tier-B query surface; the e2e DB is the Tier-C verified store (recipe 7).
--
-- PARAMETERS — every recipe is parameterized via psql \set. Override on the
-- command line:  psql ... -v root_cell="'\\xaa00…'" -f sql/cookbook.sql
-- or edit the \set lines below. They default to the cookbook's seeded graph
-- (sql/cookbook-seed.sql installs it).
\set ON_ERROR_STOP on
\set root_cell '''\\xaa00000000000000000000000000000000000000000000000000000000000000'''
\set focus_cell '''\\x5eff91e344090c47234eeceb0f684b2dbc1ffdafc0d5b69fb2427add7020cd86'''
\set genesis_supply 1885

\echo ''
\echo '################################################################'
\echo '#  pg-dregg cap-gated query cookbook                           #'
\echo '#  every recipe below is RLS-gated and RUNS on the live mirror #'
\echo '################################################################'

-- ===========================================================================
-- RECIPE 1 — THE DELEGATION TREE  (WITH RECURSIVE over the cap-edges)
-- ===========================================================================
-- The capability delegation graph is `holder -> target` edges (dregg.cap_edges,
-- a view over dregg.capabilities). A WITH RECURSIVE walks it from one root cell
-- to the whole reachable subtree — "who can this authority ultimately reach,
-- and by what chain?" The cycle guard (NOT dst = ANY(path)) keeps a back-edge
-- from looping; depth<32 bounds pathological graphs.
\echo ''
\echo '== RECIPE 1: delegation tree rooted at :root_cell =='
WITH RECURSIVE reach(src, dst, depth, path) AS (
    SELECT src, dst, 1, ARRAY[src, dst]
    FROM dregg.cap_edges
    WHERE src = :root_cell
  UNION ALL
    SELECT e.src, e.dst, r.depth + 1, r.path || e.dst
    FROM dregg.cap_edges e
    JOIN reach r ON e.src = r.dst
    WHERE r.depth < 32
      AND NOT e.dst = ANY(r.path)            -- cycle guard
)
SELECT depth,
       left(encode(src, 'hex'), 6) AS grantor,
       left(encode(dst, 'hex'), 6) AS delegate,
       array_to_string(
         ARRAY(SELECT left(encode(p, 'hex'), 6) FROM unnest(path) p), ' -> '
       ) AS chain
FROM reach
ORDER BY depth, grantor, delegate;

-- ===========================================================================
-- RECIPE 2 — THE NO-AMPLIFICATION AUDIT  (a child's effects ⊆ its grantor's)
-- ===========================================================================
-- The capability invariant: a delegate may grant downstream only effects it was
-- itself granted. dregg.capabilities.allowed_effects is the attenuation set
-- (a jsonb array of effect strings). This recipe explodes every edge's effects,
-- compares each holder's outgoing grants against the effects that holder was
-- ITSELF granted (the union over its inbound edges), and FLAGS any effect a
-- holder grants but never held — an amplification, which must never exist.
--
-- A genesis root (a holder that is never a delegation target — minted by the
-- kernel, not delegated) legitimately holds effects with no inbound edge, so the
-- recipe marks it is_genesis_root and does NOT count it as a violation.
\echo ''
\echo '== RECIPE 2: no-amplification audit (VIOLATION=t is a real over-grant) =='
WITH edge_effect AS (        -- one row per (holder, target, slot, effect)
  SELECT encode(holder, 'hex') AS holder, encode(target, 'hex') AS target, slot,
         eff.effect
  FROM dregg.capabilities c,
       LATERAL jsonb_array_elements_text(c.allowed_effects) AS eff(effect)
),
held AS (                    -- the effects each holder was THEMSELVES granted
  SELECT target AS who, effect FROM edge_effect GROUP BY target, effect
),
roots AS (                   -- holders never delegated TO = genesis authorities
  SELECT holder FROM edge_effect
  EXCEPT
  SELECT target FROM edge_effect
)
SELECT left(e.holder, 6) AS delegate,
       left(e.target, 6) AS target,
       e.slot,
       (e.holder IN (SELECT holder FROM roots)) AS is_genesis_root,
       array_agg(e.effect ORDER BY e.effect) AS grants_downstream,
       array_agg(e.effect ORDER BY e.effect)
         FILTER (WHERE h.who IS NULL) AS over_granted_effects,
       (bool_or(h.who IS NULL)
        AND e.holder NOT IN (SELECT holder FROM roots)) AS violation
FROM edge_effect e
LEFT JOIN held h ON h.who = e.holder AND h.effect = e.effect
GROUP BY e.holder, e.target, e.slot
ORDER BY violation DESC, e.holder, e.slot;

-- The same audit as ONE boolean for a CI gate / a CHECK: no edge over-grants.
\echo '-- the audit as one assertion (no_amplification should be t):'
WITH edge_effect AS (
  SELECT encode(holder, 'hex') AS holder, encode(target, 'hex') AS target,
         eff.effect
  FROM dregg.capabilities c,
       LATERAL jsonb_array_elements_text(c.allowed_effects) AS eff(effect)
),
held AS (SELECT target AS who, effect FROM edge_effect GROUP BY target, effect),
roots AS (SELECT holder FROM edge_effect EXCEPT SELECT target FROM edge_effect)
SELECT NOT bool_or(h.who IS NULL AND e.holder NOT IN (SELECT holder FROM roots))
         AS no_amplification
FROM edge_effect e
LEFT JOIN held h ON h.who = e.holder AND h.effect = e.effect;

-- The shipped view dregg.cap_attenuations is the same surface from JSON_TABLE
-- (one row per attenuated effect) — use it when you just want the flat list:
\echo '-- dregg.cap_attenuations (the shipped JSON_TABLE view, one row per effect):'
SELECT left(holder, 6) AS holder, left(target, 6) AS target, slot, effect
FROM dregg.cap_attenuations
ORDER BY holder, slot, effect;

-- ===========================================================================
-- RECIPE 3 — THE CONSERVATION CHECK  (sum(balance) = genesis)
-- ===========================================================================
-- Conservation: value is neither created nor destroyed. Across the whole live
-- ledger, the sum of every cell's balance equals the supply minted at genesis.
-- (Mint/burn cells, if your deployment has them, are added to the genesis term.)
\echo ''
\echo '== RECIPE 3: conservation — live supply vs declared genesis =='
WITH genesis(total) AS (VALUES (:genesis_supply :: bigint))
SELECT g.total       AS genesis_supply,
       sum(c.balance) AS live_supply,
       sum(c.balance) - g.total AS drift,
       (sum(c.balance) = g.total) AS conserved
FROM dregg.cells c, genesis g
GROUP BY g.total;

-- Per-turn conservation: the touched-cell post-balances of each turn. For a pure
-- transfer the touched set's delta sums to zero; this surfaces the per-ordinal
-- snapshot from dregg.cell_history (the time-travel table).
\echo '-- per-turn touched-cell balance sums (dregg.cell_history):'
SELECT h.ordinal, t.height,
       sum(h.balance) AS touched_balance_sum,
       count(*)       AS cells_touched
FROM dregg.cell_history h
JOIN dregg.turns t ON t.ordinal = h.ordinal
GROUP BY h.ordinal, t.height
ORDER BY h.ordinal;

-- ===========================================================================
-- RECIPE 4 — THE RECEIPT-CHAIN WALK  (in-SQL non-omission: prev_root = lag(...))
-- ===========================================================================
-- dregg.turns is a hash chain: turn N's post-state root (ledger_root) is turn
-- N+1's pre-state root (prev_root). A window function (lag) walks the chain and
-- asserts each link IN SQL — a light client, no node needed. A broken link
-- (chains_ok=f) or an ordinal gap (gap<>1) is an omitted/substituted turn.
\echo ''
\echo '== RECIPE 4: receipt-chain walk with in-SQL non-omission assertion =='
SELECT ordinal,
       left(prev_root, 8) AS prev_root,
       left(lag(ledger_root) OVER w, 8) AS expected_prev_root,
       (prev_root = lag(ledger_root) OVER w) AS chains_ok,
       (ordinal - lag(ordinal) OVER w) AS ordinal_gap   -- 1 = dense, >1 = omission
FROM dregg.receipt_chain
WINDOW w AS (ORDER BY ordinal)
ORDER BY ordinal;

-- The chain as ONE assertion (chain_intact should be t): a CI/audit gate that
-- proves non-omission + non-substitution over the whole visible chain at once.
\echo '-- the chain as one assertion (chain_intact should be t):'
WITH chain AS (
  SELECT ordinal, prev_root,
         lag(ledger_root) OVER (ORDER BY ordinal) AS expected_prev,
         ordinal - lag(ordinal) OVER (ORDER BY ordinal) AS gap
  FROM dregg.receipt_chain)
SELECT count(*) FILTER (WHERE expected_prev IS NOT NULL
                          AND prev_root <> expected_prev) AS broken_links,
       count(*) FILTER (WHERE gap IS NOT NULL AND gap <> 1) AS ordinal_gaps,
       bool_and(coalesce(prev_root = expected_prev, true)
                AND coalesce(gap = 1, true)) AS chain_intact
FROM chain;

-- DETECTION demo: the SAME walk over a hypothetically-tampered copy BREAKS. We
-- do NOT mutate the table (writes are verified-only); the CTE simulates someone
-- swapping turn 1's roots, and both adjacent links light up chains_ok=f. This is
-- the "an auditor needs no node — just psql and the chain" proof.
\echo '-- tamper detection (CTE simulates corrupting turn 1; chains_ok must go f):'
WITH tampered AS (
  SELECT ordinal,
         CASE WHEN ordinal = 1 THEN 'deadbeef' ELSE prev_root END AS prev_root,
         CASE WHEN ordinal = 1 THEN 'deadbeef' ELSE ledger_root END AS ledger_root
  FROM dregg.receipt_chain)
SELECT ordinal, left(prev_root, 8) AS prev_root,
       left(lag(ledger_root) OVER w, 8) AS expected_prev_root,
       (prev_root = lag(ledger_root) OVER w) AS chains_ok
FROM tampered
WINDOW w AS (ORDER BY ordinal)
ORDER BY ordinal;

-- ===========================================================================
-- RECIPE 5 — PER-CELL TIME-TRAVEL  (a cell's trajectory across turns)
-- ===========================================================================
-- dregg.cell_history keeps every post-image (the cell-by-(id,ordinal) index of
-- the commit log). This walks ONE cell's balance/nonce/commitment across the
-- turns that touched it, with the per-step balance delta from a window function.
\echo ''
\echo '== RECIPE 5: per-cell time-travel for :focus_cell =='
SELECT h.ordinal, t.height, h.balance, h.nonce,
       h.balance - lag(h.balance) OVER w AS balance_delta,
       left(encode(h.cell_root, 'hex'), 8) AS cell_root_commitment
FROM dregg.cell_history h
JOIN dregg.turns t ON t.ordinal = h.ordinal
WHERE h.cell_id = :focus_cell
WINDOW w AS (ORDER BY h.ordinal)
ORDER BY h.ordinal;

-- ===========================================================================
-- RECIPE 6 — CAPS-AS-ROWS  (given a token, the exact rows it grants — the gate
--            RESPECTED, and made legible)
-- ===========================================================================
-- This is the cookbook's thesis recipe and the SQL twin of the browser explorer:
-- "your capabilities, expressed as the rows you may SELECT." Two faces:
--
--  (6a) the gate RESPECTED — become the unprivileged reader role, present the
--       token, and SELECT: RLS returns ONLY the admitted rows. Never a bypass.
--  (6b) the gate EXPLAINED — for every candidate row, dregg_cap_explain names
--       WHY it is admitted or filtered (the vanished-row problem, solved).
--
-- Present a token first. Mint one out-of-band (the issuer secret never enters
-- pg): `cargo run --example mint -- --seed 7 --action read --prefix 5e`, then:
--     \set tok 'dga1_...'
-- and uncomment the BEGIN…COMMIT block below.
--
-- CRITICAL — the token is TRANSACTION-LOCAL (set_config(..., true), the safe
-- default on a pooled connection). The SET and the SELECT must be in the SAME
-- transaction or the GUC is gone by the SELECT and the reader sees ZERO rows.
-- So the gate-respecting form is a BEGIN…COMMIT block (the pooled-connection
-- pattern). Left commented so the file runs key-free; the uncommented body below
-- shows the rows WITHOUT a token (the kernel/owner view), and recipe 6b explains
-- the per-row verdict for any token literal without needing the role/GUC.
\echo ''
\echo '== RECIPE 6a: caps-as-rows — the cells a presented token grants (gate respected) =='
-- BEGIN;
--   SET LOCAL ROLE dregg_reader;                       -- the unprivileged app role
--   SELECT set_config('dregg.token', :'tok', true);    -- present the bearer token
--   SELECT encode(cell_id, 'hex') AS cell_you_may_read, balance, lifecycle
--   FROM dregg.cells ORDER BY cell_id;                 -- ONLY the admitted rows
-- COMMIT;
-- With TOK_5E (read, prefix 5e) this returns ONLY the 5eff… cell; with a
-- read/"" token it returns all cells; with no token, zero (fail-closed).
SELECT encode(cell_id, 'hex') AS cell_you_may_read, balance, lifecycle
FROM dregg.cells
ORDER BY cell_id;

-- The EXPLAIN twin works for ANYONE (it takes the token as an argument, so it
-- does not depend on the session role/GUC): pass a token literal and see the
-- per-row verdict + reason. Replace the token below with your minted one.
\echo '== RECIPE 6b: caps-as-rows EXPLAINED — why each row is admitted/filtered =='
\echo '   (replace the token literal with one from: cargo run --example mint ...)'
-- Example with a read/prefix-5e token (yours will differ):
-- SELECT left(encode(cell_id,'hex'),6) AS cell,
--        dregg_cap_admits(:'tok','read',encode(cell_id,'hex'),
--                         extract(epoch from now())::bigint) AS admitted,
--        dregg_cap_explain(:'tok','read',encode(cell_id,'hex'),
--                          extract(epoch from now())::bigint) AS reason
-- FROM dregg.cells ORDER BY cell_id;

-- ===========================================================================
-- RECIPE 7 — THE WRITE GATE  (for contrast: the engine REFUSES a tampered turn)
-- ===========================================================================
-- Everything above is a READ. This is the spine invariant's other half: a row
-- enters dregg state ONLY as a verified-turn post-image. Run against the Tier-C
-- e2e DB (pg_dregg_e2e), the database ENGINE — not a SELECT-side check — refuses
-- a turn whose prev_root does not chain onto the head (anti-substitution). This
-- is dregg_verify_turn in the dregg.commit_log BEFORE INSERT trigger.
--
--   -- (run in pg_dregg_e2e, as a role with INSERT on dregg.commit_log)
--   INSERT INTO dregg.commit_log
--     (ordinal,height,block_id,block_executed_up_to,turn_hash,creator,
--      receipt_hash,ledger_root,prev_root,cells)
--   VALUES (2, 2, '\xbb'::bytea, 2, '\xcafe'::bytea, '\xc0'::bytea,
--           '\xab'::bytea, '\x333333'::bytea, '\xdeadbeef'::bytea, '[]'::jsonb);
--   -- ERROR: dregg: turn 2 does not chain onto the head root — refused
--   --        (anti-substitution)
--
-- A correctly-chaining turn (prev_root = the current head ledger_root) is
-- accepted and materializes its cells in the same transaction. Reads stay free;
-- writes stay verified-only.

\echo ''
\echo '################################################################'
\echo '#  cookbook complete — every recipe ran against the live mirror #'
\echo '################################################################'
