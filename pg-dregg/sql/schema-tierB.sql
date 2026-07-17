-- pg-dregg — Tier B schema sketch: dregg state AS queryable postgres tables.
--
-- =============================================================================
-- ⚠ DESIGN SKETCH — NOT A MIGRATION. See .docs-history-noclaude/PG-DREGG.md §8 (Tier B/C/D).
-- =============================================================================
-- This file is the concrete artifact for the Tier B proposal: it shows the
-- shape of the cells / receipts / blocklace / capability tables, the
-- universal-memory single table, and the RLS policies that compose with the
-- LANDED M1 authz layer (dregg_admits / dregg_cap_admits, see src/authz.rs).
--
-- The Rust mirror core (src/mirror.rs) is the postgres-free, cargo-test-proven
-- backbone of this schema: it owns the row types, the universal-memory Domain
-- model, the DDL emitter (`mirror::ddl::tier_b()` regenerates these tables), and
-- the RootChain anti-substitution tooth. Tier C (the verify gate) is the sibling
-- file schema-tierC.sql.
--
-- THE LOAD-BEARING INVARIANT (the spine of the whole design):
--
--     Reads are free SQL; state mutates ONLY through verified turns.
--
-- Every table below is a MATERIALIZED VIEW of state the dregg kernel produced.
-- A row appears here ONLY as the post-image of a verified turn (the commit
-- log's CommitRecord — persist/src/commit_log.rs). Ordinary `SELECT` queries
-- this freely. A bare SQL `INSERT/UPDATE/DELETE` by an application role is
-- FORBIDDEN — it would bypass the executor and break conservation /
-- no-amplification / nullifier-uniqueness. Tier C (the dregg_verify_turn CHECK
-- tooth, §9) is what mechanically enforces that forbiddance; this file sets up
-- the tables and the read-side RLS, and marks the write-lockdown that Tier C
-- fills in.
--
-- Provenance of every column is named against the real Rust types so the
-- mirror is a faithful projection, not an invention:
--   * persist/src/commit_log.rs  :: CommitRecord
--   * persist/src/ledger_store.rs :: LedgerCheckpoint
--   * cell/src/cell.rs            :: Cell / CellState / Permissions
--   * cell/src/capability.rs      :: CapabilitySet / CapabilityRef
--   * .docs-history-noclaude/UNIVERSAL-MEMORY.md    :: the (domain,key)->value Blum multiset

CREATE EXTENSION IF NOT EXISTS pg_dregg;
CREATE SCHEMA IF NOT EXISTS dregg;

-- ===========================================================================
-- 0.  The write-lockdown role model (Tier C precondition).
-- ===========================================================================
-- Two roles, sharply separated:
--   * dregg_kernel  — the ONLY role permitted to INSERT/UPDATE dregg.* state.
--                     In Tier C/D this is the role the verifier/executor
--                     function runs as (SECURITY DEFINER). NOTHING ELSE writes.
--   * dregg_reader  — applications. SELECT only. RLS-gated by the M1 caps.
-- A bare application connection is dregg_reader: it can never mutate state.
-- The kernel is the VERIFIED writer: it materializes verified-turn post-images
-- wholesale, so it is BYPASSRLS (the read-side RLS gates APPLICATIONS, not the
-- writer that produced the rows). In Tier C even the kernel's writes still pass
-- the dregg_verify_turn CHECK (schema-tierC.sql) — the verifier gates writes,
-- RLS gates reads.
CREATE ROLE dregg_kernel  NOLOGIN BYPASSRLS;   -- the verified writer (SECURITY DEFINER target)
CREATE ROLE dregg_reader  NOLOGIN;             -- applications: reads only

-- ===========================================================================
-- 1.  RECEIPTS / TURNS — the spine. A direct projection of CommitRecord.
-- ===========================================================================
-- This table is the authority for "what verified turns happened". Every other
-- state table (cells, memory, caps) is reconcilable to it: a cell row at
-- ordinal N is the touched_cells post-image of the turn at ordinal N.
CREATE TABLE dregg.turns (
    ordinal              bigint PRIMARY KEY,            -- CommitRecord.ordinal (dense, gap-free)
    height               bigint NOT NULL,               -- CommitRecord.height (attested-root height)
    block_id             bytea  NOT NULL,               -- CommitRecord.block_id (consensus anchor)
    block_executed_up_to bigint NOT NULL,               -- CommitRecord.block_executed_up_to
    turn_hash            bytea  NOT NULL UNIQUE,         -- CommitRecord.turn_hash
    creator              bytea  NOT NULL,               -- CommitRecord.creator (agent CellId)
    receipt_hash         bytea  NOT NULL,               -- CommitRecord.receipt_hash
    ledger_root          bytea  NOT NULL,               -- CommitRecord.ledger_root (post-state commitment)
    prev_root            bytea  NOT NULL,               -- the prior turn's ledger_root (the RootChain link)
    committed_at         timestamptz NOT NULL DEFAULT now()  -- wall-clock mirror time (NOT consensus time)
);
CREATE INDEX turns_by_height  ON dregg.turns (height);
CREATE INDEX turns_by_creator ON dregg.turns (creator, ordinal);
-- The mirror's own integrity tooth: ordinals are dense. (Tier C strengthens
-- this to "ledger_root chains": each row's ledger_root is the verified
-- post-state of applying turn_hash to the prior row's ledger_root.)

-- ===========================================================================
-- 2.  CELLS — the live ledger, one row per cell, AS OF the latest turn.
-- ===========================================================================
-- A projection of dregg_cell::Cell (cell/src/cell.rs) + LedgerCheckpoint.cells.
-- `last_ordinal` ties each cell row to the turn that produced its post-image,
-- so a join `cells ⋈ turns ON last_ordinal = ordinal` is fully reconcilable.
CREATE TABLE dregg.cells (
    cell_id        bytea PRIMARY KEY,         -- Cell.id() (CellId, 32 bytes)
    mode           text  NOT NULL,            -- CellMode (Hosted | Sovereign | ...)
    balance        bigint NOT NULL,           -- CellState balance
    nonce          bigint NOT NULL,           -- CellState nonce (monotone)
    -- State payload kept BOTH as raw bytes (faithful) and as jsonb (queryable).
    -- The bytea is canonical; the jsonb is a decoded convenience the mirror
    -- writer fills. Queries use jsonb; integrity reconciles on bytea.
    fields         bytea NOT NULL,            -- CellState.fields (FieldElement slots), canonical
    fields_json    jsonb,                     -- decoded slot array, for `fields_json->>'0'` queries
    heap           bytea,                     -- CellState heap (openable sorted map), canonical
    program        bytea,                     -- CellProgram (predicate / verification key bound)
    verification_key bytea,                   -- Cell.verification_key (Option)
    permissions    jsonb,                     -- Cell.permissions (Permissions), decoded
    delegate       bytea,                     -- Cell.delegate (Option<CellId>)
    lifecycle      text  NOT NULL,            -- CellLifecycle (Active | Sealed | ...)
    last_ordinal   bigint NOT NULL REFERENCES dregg.turns(ordinal),  -- the turn that produced this row
    cell_root      bytea NOT NULL,            -- this cell's commitment (recStateCommit); part of ledger_root
    -- GENERATED COLUMNS: pg-maintained canonical projections that cannot drift
    -- from the canonical bytea. pg18 makes VIRTUAL (read-time, no storage) the
    -- DEFAULT; we choose per column by whether it must be indexed:
    --   * cell_hex STORED — it backs the cells_by_canonical index (a VIRTUAL
    --     column cannot be indexed). Typed with the pg17 builtin C collation
    --     pg_c_utf8 so its byte order matches the node's canonical
    --     lexicographic-on-bytes order — no ICU/locale drift. (PG18 §3,§4.)
    --   * cell_root_hex / balance_field VIRTUAL (the pg18 default, explicit) —
    --     read-side projections that need no index; pg18 computes them on read,
    --     identically and drift-free, with zero stored bytes.
    cell_hex       text COLLATE pg_c_utf8
                   GENERATED ALWAYS AS (encode(cell_id, 'hex')) STORED,
    cell_root_hex  text COLLATE pg_c_utf8
                   GENERATED ALWAYS AS (encode(cell_root, 'hex')) VIRTUAL,
    balance_field  bigint
                   GENERATED ALWAYS AS ((fields_json->>'balance')::bigint) VIRTUAL
);
-- One composite index serves BOTH "cells in this mode" AND "cells by balance,
-- any mode" — the latter via pg18's B-tree SKIP SCAN. The leading column `mode`
-- has tiny cardinality (Hosted | Sovereign), which is exactly skip scan's sweet
-- spot: a query constraining only `balance` makes the planner skip through the
-- few distinct `mode` prefixes and range-scan `balance` within each, instead of
-- the pre-18 fallback (a full index scan / seq scan). So one index covers the two
-- hot analytics paths (`WHERE mode=…` and `WHERE balance>=…` / `ORDER BY balance`)
-- with no separate balance index to maintain on the write path. (PG18 §8.)
CREATE INDEX cells_by_mode_balance ON dregg.cells (mode, balance);
CREATE INDEX cells_fields_gin   ON dregg.cells USING gin (fields_json);
CREATE INDEX cells_perms_gin    ON dregg.cells USING gin (permissions);
-- The canonical-order index: byte-order on the hex id under the builtin C
-- provider, the deterministic order the node's canonical roots use (no drift).
CREATE INDEX cells_by_canonical ON dregg.cells (cell_hex);

-- Optional: full history (every post-image, not just latest) for time-travel.
-- This is the cell-by-(id,ordinal) index of the commit log, surfaced as SQL.
CREATE TABLE dregg.cell_history (
    cell_id     bytea  NOT NULL,
    ordinal     bigint NOT NULL REFERENCES dregg.turns(ordinal),
    balance     bigint NOT NULL,
    nonce       bigint NOT NULL,
    fields_json jsonb,
    cell_root   bytea  NOT NULL,
    PRIMARY KEY (cell_id, ordinal)
);
CREATE INDEX cell_history_by_ordinal ON dregg.cell_history (ordinal);

-- ===========================================================================
-- 3.  CAPABILITIES + the delegation graph (cell/src/capability.rs).
-- ===========================================================================
-- One row per CapabilityRef in a cell's CapabilitySet. (holder, slot) is the
-- c-list address; `target` is the cell the capability reaches. The graph is
-- holder -> target edges; recursive queries walk the delegation tree.
CREATE TABLE dregg.capabilities (
    holder       bytea  NOT NULL REFERENCES dregg.cells(cell_id),  -- the cell that HOLDS the cap
    slot         int    NOT NULL,                                  -- CapabilityRef.slot (c-list position)
    target       bytea  NOT NULL,                                  -- CapabilityRef.target (cell reached)
    permissions  jsonb  NOT NULL,                                  -- CapabilityRef.permissions (AuthRequired)
    breadstuff   bytea,                                            -- CapabilityRef.breadstuff (token hash)
    expires_at   bigint,                                           -- CapabilityRef.expires_at (Option<height>)
    allowed_effects jsonb,                                         -- CapabilityRef.allowed_effects (attenuation)
    stored_epoch bigint,                                           -- CapabilityRef.stored_epoch (group-key epoch)
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (holder, slot)
);
CREATE INDEX caps_by_target ON dregg.capabilities (target);

-- ===========================================================================
-- 4.  BLOCKLACE DAG (persist/src/blocklace_store.rs) — the consensus layer.
-- ===========================================================================
CREATE TABLE dregg.blocks (
    block_id   bytea PRIMARY KEY,        -- block hash
    creator    bytea NOT NULL,           -- block creator (validator CellId)
    seq        bigint NOT NULL,          -- creator-local sequence number
    payload_kind text NOT NULL,          -- 'turn' | 'heartbeat' | 'membership' | 'checkpoint'
    turn_ordinal bigint REFERENCES dregg.turns(ordinal)  -- the turn this block carried, if any
);
-- The DAG edges (a block ACKNOWLEDGES its predecessors — the blocklace pointers).
CREATE TABLE dregg.block_edges (
    child  bytea NOT NULL REFERENCES dregg.blocks(block_id),  -- the acknowledging block
    parent bytea NOT NULL REFERENCES dregg.blocks(block_id),  -- the acknowledged predecessor
    PRIMARY KEY (child, parent)
);
CREATE INDEX block_edges_parent ON dregg.block_edges (parent);

-- ===========================================================================
-- 5.  UNIVERSAL MEMORY — the elegant collapse (.docs-history-noclaude/UNIVERSAL-MEMORY.md).
-- ===========================================================================
-- The Blum multiset over Domain × κ maps to ONE table. Domain ∈ {registers,
-- heap, caps, nullifiers, index}; a future state component is a NEW DOMAIN
-- VALUE, never a new table — so this single relation is the whole memory.
-- (Tables 2-4 above are then DERIVED BOUNDARY VIEWS over this one table, exactly
-- as the four map roots are derived boundary views over the final memory cells.
-- Whether to keep tables 2-4 as real tables or as VIEWS over dregg.memory is an
-- ember decision, §8: the typed tables are nicer to query; the single table is
-- the honest model.)
CREATE TABLE dregg.memory (
    domain       text  NOT NULL,         -- 'registers'|'heap'|'caps'|'nullifiers'|'index'
    collection   bytea NOT NULL,         -- collection_id (e.g. the cell, the map)
    key          bytea NOT NULL,         -- κ within the domain
    value        bytea,                  -- Option ν: NULL = absent cell, non-null = present
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (domain, collection, key)
);
CREATE INDEX memory_by_domain ON dregg.memory (domain);
-- The boundary roots (cap_root / nullifier_root / heap_root / index root) are
-- `SELECT dregg_domain_root('caps', collection)` over the present cells — a
-- derived view, matching boundary_root_derived. Equality of that derived root
-- with the committed map root is the Lean-proved boundary reconciliation.

-- ===========================================================================
-- 5a. THE MIRROR WRITE PATH — a PostgreSQL 18 MERGE upsert (one atomic stmt).
-- ===========================================================================
-- The kernel writer materializes each touched cell's post-image with a single
-- pg18 MERGE: a first-seen cell INSERTs, a re-touched cell UPDATEs in place,
-- `merge_action()` (pg17) RETURNS which arm fired, and pg18's
-- `RETURNING WITH (OLD AS o, NEW AS n)` binds the PRE-image in the SAME statement
-- — so the function returns the action AND the exact balance delta
-- ('INSERT +1000000' / 'UPDATE -500'), an audit signal impossible pre-18 without
-- a separate pre-read. The explicit `RETURNING WITH (OLD/NEW)` alias is the
-- spec-standard pg18 form (strictly better than the bare `old.`/`new.`
-- pseudo-aliases, which only resolve when no column is named old/new). Shipped as
-- a function (the same one the mirror::ddl emitter generates) so the node invokes
-- it as `SELECT dregg.merge_cell(...)`. (.docs-history-noclaude/PG-DREGG-PG18.md §7; the Tier-C
-- trigger materializes the same way, schema-tierC.sql §3.)
CREATE OR REPLACE FUNCTION dregg.merge_cell(
    p_cell_id bytea, p_mode text, p_balance bigint, p_nonce bigint,
    p_fields bytea, p_fields_json jsonb, p_lifecycle text,
    p_last_ordinal bigint, p_cell_root bytea) RETURNS text
LANGUAGE plpgsql AS $$
DECLARE v_action text; v_dbal bigint;
BEGIN
    MERGE INTO dregg.cells AS t
    USING (SELECT p_cell_id AS cell_id) AS s
      ON t.cell_id = s.cell_id
    WHEN MATCHED THEN UPDATE SET balance=p_balance, nonce=p_nonce,
        fields_json=p_fields_json, last_ordinal=p_last_ordinal, cell_root=p_cell_root
    WHEN NOT MATCHED THEN INSERT
        (cell_id,mode,balance,nonce,fields,fields_json,lifecycle,last_ordinal,cell_root)
        VALUES (p_cell_id,p_mode,p_balance,p_nonce,p_fields,p_fields_json,
                p_lifecycle,p_last_ordinal,p_cell_root)
    -- pg17 merge_action() = 'INSERT'|'UPDATE'; pg18 RETURNING WITH binds o (the
    -- pre-image, o.balance NULL on insert) ⇒ n.balance - coalesce(o.balance,0).
    RETURNING WITH (OLD AS o, NEW AS n)
        merge_action(), n.balance - coalesce(o.balance, 0)
        INTO v_action, v_dbal;
    RETURN v_action || ' ' || (CASE WHEN v_dbal >= 0 THEN '+' ELSE '' END) || v_dbal::text;
END $$;

-- The richer audit applicator: the SAME atomic MERGE, returning the typed delta
-- tuple (action, signed balance delta, signed nonce delta) the pg18 RETURNING
-- WITH (OLD/NEW) reads from the pre-image. The string `dregg.merge_cell` stays the
-- materialization path; this twin is the analytics face when a caller wants the
-- numbers typed — e.g. asserting conservation (the per-cell balance deltas of a
-- transfer sum to zero) directly off the applicator. (.docs-history-noclaude/PG-DREGG-PG18.md §7.)
CREATE OR REPLACE FUNCTION dregg.merge_cell_delta(
    p_cell_id bytea, p_mode text, p_balance bigint, p_nonce bigint,
    p_fields bytea, p_fields_json jsonb, p_lifecycle text,
    p_last_ordinal bigint, p_cell_root bytea,
    OUT action text, OUT balance_delta bigint, OUT nonce_delta bigint)
LANGUAGE plpgsql AS $$
BEGIN
    MERGE INTO dregg.cells AS t
    USING (SELECT p_cell_id AS cell_id) AS s
      ON t.cell_id = s.cell_id
    WHEN MATCHED THEN UPDATE SET balance=p_balance, nonce=p_nonce,
        fields_json=p_fields_json, last_ordinal=p_last_ordinal, cell_root=p_cell_root
    WHEN NOT MATCHED THEN INSERT
        (cell_id,mode,balance,nonce,fields,fields_json,lifecycle,last_ordinal,cell_root)
        VALUES (p_cell_id,p_mode,p_balance,p_nonce,p_fields,p_fields_json,
                p_lifecycle,p_last_ordinal,p_cell_root)
    RETURNING WITH (OLD AS o, NEW AS n)
        merge_action(),
        n.balance - coalesce(o.balance, 0),
        n.nonce   - coalesce(o.nonce, 0)
        INTO action, balance_delta, nonce_delta;
END $$;

-- ===========================================================================
-- 5b. THE DREGG-DEVELOPER QUERY SURFACE — views over the Tier-B tables.
-- ===========================================================================
-- These are the views the `mirror::ddl::tier_b()` emitter ships (kept in step
-- with this file by the `emitted_ddl_agrees_with_committed_sql_file` test in
-- src/mirror.rs). Each is created WITH (security_invoker = true) (pg15), so RLS on
-- the base tables is evaluated as the INVOKING reader THROUGH the view — the
-- capability gate is enforced by declaration, not incidentally (.docs-history-noclaude/PG-DREGG.md
-- §14.3). See docs/QUICKSTART-dregg-dev.md for worked queries.

-- The delegation graph; WITH RECURSIVE over it gives reachability / the
-- no-amplification audit (a child's allowed_effects ⊆ its grantor's).
CREATE OR REPLACE VIEW dregg.cap_edges WITH (security_invoker = true) AS
    SELECT holder AS src, target AS dst, slot, permissions, expires_at
    FROM dregg.capabilities;

-- The ledger, hex-keyed and balance-first: the "show me the money" view.
CREATE OR REPLACE VIEW dregg.cell_balances WITH (security_invoker = true) AS
    SELECT encode(cell_id, 'hex') AS cell, balance, nonce, lifecycle, last_ordinal
    FROM dregg.cells;

-- The receipt/turn hash chain a light client walks: each row's prev_root is the
-- prior row's ledger_root (the RootChain tooth, surfaced as SQL).
CREATE OR REPLACE VIEW dregg.receipt_chain WITH (security_invoker = true) AS
    SELECT ordinal, height, encode(creator, 'hex') AS creator,
           encode(prev_root, 'hex') AS prev_root,
           encode(ledger_root, 'hex') AS ledger_root, committed_at
    FROM dregg.turns ORDER BY ordinal;

-- PostgreSQL 17 SQL/JSON projections (JSON_TABLE) — the embedded jsonb state,
-- surfaced as flat relational rows so a developer JOINs/aggregates it without
-- hand-rolled jsonb operators (.docs-history-noclaude/PG-DREGG.md "PostgreSQL 17 leverage").

-- One row per attenuated effect in a capability's allowed_effects array: the
-- no-amplification audit surface, exploded from the jsonb array into rows.
CREATE OR REPLACE VIEW dregg.cap_attenuations WITH (security_invoker = true) AS
    SELECT encode(c.holder, 'hex') AS holder, c.slot,
           encode(c.target, 'hex') AS target, jt.effect, c.expires_at,
           c.last_ordinal
    FROM dregg.capabilities c,
         JSON_TABLE(c.allowed_effects, '$[*]'
             COLUMNS (effect text PATH '$')) AS jt;

-- The decoded cell field slots (balance/nonce) projected out of fields_json: a
-- typed face over the canonical jsonb the mirror writer fills.
CREATE OR REPLACE VIEW dregg.cell_fields WITH (security_invoker = true) AS
    SELECT encode(cell_id, 'hex') AS cell, jt.balance, jt.nonce, last_ordinal
    FROM dregg.cells,
         JSON_TABLE(fields_json, '$'
             COLUMNS (balance bigint PATH '$.balance',
                      nonce    bigint PATH '$.nonce')) AS jt;

-- The canonical ledger view: cells in the deterministic byte-order the node's
-- canonical roots use, via the pg17 builtin C collation (pg_c_utf8) on the
-- generated cell_hex column. ORDER BY here matches the kernel's sorted-leaf
-- ordering exactly (no ICU/locale drift), so a pg-side fold over this view sees
-- leaves in the same order the ledger root commits them.
CREATE OR REPLACE VIEW dregg.canonical_cells WITH (security_invoker = true) AS
    SELECT cell_hex, balance, nonce, lifecycle, cell_root_hex, last_ordinal
    FROM dregg.cells
    ORDER BY cell_hex COLLATE pg_c_utf8;

-- pg18 AIO observability (.docs-history-noclaude/PG-DREGG-PG18.md §8, .docs-history-noclaude/PG-DREGG.md §14.2): the
-- read/write/verify I/O mix made legible. pg18's asynchronous I/O subsystem feeds
-- pg_stat_io; this projects the read-path-relevant relation contexts (normal,
-- vacuum, bulkread/bulkwrite) into a compact mirror-facing surface with the
-- AIO-specific reads/read_bytes and the cache hit ratio the read-heavy mirror
-- watches as the ledger grows. A thin SELECT over the system view (no row data).
CREATE OR REPLACE VIEW dregg.mirror_io_stats AS
    SELECT backend_type, object, context,
           reads, read_bytes, writes, write_bytes, extends, hits, evictions,
           CASE WHEN coalesce(hits,0) + coalesce(reads,0) > 0
                THEN round(coalesce(hits,0)::numeric
                           / (coalesce(hits,0) + coalesce(reads,0)), 4)
                ELSE NULL END AS cache_hit_ratio
    FROM pg_stat_io
    WHERE object IN ('relation')
      AND context IN ('normal','vacuum','bulkread','bulkwrite');

-- pg18 AIO IN-FLIGHT (.docs-history-noclaude/PG-DREGG-PG18.md §8): pg_stat_io is the cumulative
-- counter; pg18 ALSO ships `pg_aios`, the live view of the async-I/O handles a
-- backend currently has outstanding. For a read-heavy mirror issuing batched
-- async reads, the in-flight depth shows whether AIO is actually queueing reads
-- vs falling back to synchronous. SELECT * so it inherits pg_aios's columns
-- verbatim (a system view, no row data). pg18-only: pg_aios does not exist pre-18.
CREATE OR REPLACE VIEW dregg.mirror_aio_inflight AS
    SELECT * FROM pg_aios;

-- pg18 DATA-INTEGRITY status (.docs-history-noclaude/PG-DREGG-PG18.md §11): dregg's thesis is
-- integrity-down-to-the-bytes; the STORAGE floor under the kernel root + chain
-- tooth + IVC light client is page-level integrity, and pg18 makes `initdb`
-- enable data checksums BY DEFAULT (every page carries a checksum verified on
-- read, so silent on-disk corruption surfaces as a loud error, never a wrong byte
-- fed to the mirror). This view makes that floor legible: `data_checksums` is the
-- read-only GUC pg sets from the control file ('on' when active). A thin SELECT
-- over GUCs (no row data) — an operator/setup-assertion confirms the mirror sits
-- on a checksummed cluster, the page integrity the higher tiers assume.
CREATE OR REPLACE VIEW dregg.integrity_status AS
    SELECT current_setting('data_checksums')           AS data_checksums,
           (current_setting('data_checksums') = 'on')   AS checksums_enabled,
           current_setting('block_size')                AS block_size;

-- ===========================================================================
-- 6.  READ-SIDE RLS — every state table composes with the M1 cap layer.
-- ===========================================================================
-- The reader sees ONLY the cells/turns/caps its presented dregg token admits.
-- This is the M1 dregg_admits gate (src/authz.rs) applied to the mirror: the
-- explorer is "your capabilities, expressed as the rows you may SELECT".
ALTER TABLE dregg.cells        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       ENABLE ROW LEVEL SECURITY;

-- A token admits a cell row iff it admits `read` on that cell id.
CREATE POLICY cells_read ON dregg.cells FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(cell_id, 'hex')));

-- A token admits a turn row iff it admits `read` on the turn's creator cell
-- (you can see the turns of agents you can read). Public-explorer deployments
-- relax this to USING (true) for the turns table while keeping cells gated.
CREATE POLICY turns_read ON dregg.turns FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(creator, 'hex')));

CREATE POLICY caps_read ON dregg.capabilities FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(holder, 'hex')));

CREATE POLICY memory_read ON dregg.memory FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(collection, 'hex')));

-- ===========================================================================
-- 7.  WRITE LOCKDOWN — the spine, mechanically (Tier C fills the CHECK).
-- ===========================================================================
-- Applications (dregg_reader) get SELECT only. NO write grants. The ONLY writer
-- is dregg_kernel, and in Tier C even dregg_kernel's writes pass through the
-- dregg_verify_turn CHECK (see .docs-history-noclaude/PG-DREGG.md §9 and schema-tierC.sql).
GRANT USAGE  ON SCHEMA dregg TO dregg_reader, dregg_kernel;
GRANT SELECT ON ALL TABLES IN SCHEMA dregg TO dregg_reader;
GRANT INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg TO dregg_kernel;

-- Belt-and-braces: FORCE RLS so even the table owner is filtered, and REVOKE
-- any default write from PUBLIC. A bare SQL INSERT by an app is rejected at the
-- privilege layer BEFORE any trigger; Tier C's trigger then guarantees that
-- even dregg_kernel cannot write a row that is not a verified-turn post-image.
ALTER TABLE dregg.cells        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       FORCE ROW LEVEL SECURITY;
REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC;

-- ===========================================================================
-- 8.  Worked queries — the payoff. The explorer, expressed as SQL.
-- ===========================================================================
-- (illustrative; each is RLS-gated by §6, so it returns only admitted rows.)

-- Richest cells you can see:
--   SELECT encode(cell_id,'hex'), balance FROM dregg.cells ORDER BY balance DESC LIMIT 10;

-- Conservation check over a turn (sum of touched-cell balances unchanged):
--   SELECT t.ordinal, sum(ch.balance) FROM dregg.cell_history ch
--   JOIN dregg.turns t ON t.ordinal = ch.ordinal GROUP BY t.ordinal;

-- The delegation tree rooted at one cell (no-amplification audit surface):
--   WITH RECURSIVE reach(src,dst,depth) AS (
--     SELECT src,dst,1 FROM dregg.cap_edges WHERE src = $root
--     UNION ALL
--     SELECT e.src,e.dst,r.depth+1 FROM dregg.cap_edges e
--     JOIN reach r ON e.src = r.dst WHERE r.depth < 32)
--   SELECT * FROM reach;

-- Turns by an agent, newest first, joined to their post-state root:
--   SELECT ordinal, height, encode(ledger_root,'hex')
--   FROM dregg.turns WHERE creator = $agent ORDER BY ordinal DESC;
