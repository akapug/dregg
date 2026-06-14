-- pg-dregg — cookbook SEED data.
-- =============================================================================
-- Installs a small but meaningful delegation graph + per-cell history into a
-- pg-dregg mirror DB so sql/cookbook.sql has data to run against. These are
-- KERNEL-EQUIVALENT mirror rows (the post-images a verified turn would produce);
-- on a real node they arrive from node/src/pg_mirror.rs, never by hand. This
-- file is for demos / the cookbook walk-through only.
--
-- Run AFTER the schema is installed (SELECT dregg_install_schema()):
--   psql -h ~/.pgrx -p 28818 -d pg_dregg_mirror -f sql/cookbook-seed.sql
--
-- It assumes the base mirror already has at least turns 0..2 and the two cells
-- 5eff…/5c94… (the live mirror's seed). It is idempotent (ON CONFLICT DO NOTHING)
-- and additive: it adds four agent cells (org/alice/bob/carol = aa/bb/cc/dd), a
-- delegation graph with one DELIBERATE amplification (cc->bb {admin}) for the
-- audit to catch, and a per-cell history for time-travel.
\set ON_ERROR_STOP on

-- The cookbook references the genesis supply 1885 = the seeded total:
--   5eff=20 + 5c94=15 + aa=1000 + bb=500 + cc=250 + dd=100 = 1885.

-- ---- agent cells (org / alice / bob / carol) -------------------------------
INSERT INTO dregg.cells
  (cell_id, mode, balance, nonce, fields, fields_json, lifecycle, last_ordinal, cell_root)
VALUES
 ('\xaa00000000000000000000000000000000000000000000000000000000000000','Hosted',1000,0,'\x00','{"balance":1000,"nonce":0}','Live',2,'\xaaaa'),
 ('\xbb00000000000000000000000000000000000000000000000000000000000000','Hosted', 500,0,'\x00','{"balance":500,"nonce":0}', 'Live',2,'\xbbbb'),
 ('\xcc00000000000000000000000000000000000000000000000000000000000000','Hosted', 250,0,'\x00','{"balance":250,"nonce":0}', 'Live',2,'\xcccc'),
 ('\xdd00000000000000000000000000000000000000000000000000000000000000','Hosted', 100,0,'\x00','{"balance":100,"nonce":0}', 'Live',2,'\xdddd')
ON CONFLICT (cell_id) DO NOTHING;

-- ---- the delegation graph (cap-edges with attenuation) ---------------------
--   org(aa) --{read,transfer,grant,admin}-> alice(bb)   (genesis grant)
--   alice(bb) --{read,transfer}--> bob(cc)               (attenuated subset)
--   bob(cc)  --{read}-----------> carol(dd)              (further attenuated)
--   bob(cc)  --{admin}----------> alice(bb)  slot 1      (AMPLIFICATION — bob
--                                                          never held admin; the
--                                                          no-amplification audit
--                                                          must flag this)
INSERT INTO dregg.capabilities
  (holder, slot, target, permissions, allowed_effects, expires_at, last_ordinal)
VALUES
 ('\xaa00000000000000000000000000000000000000000000000000000000000000', 0,
  '\xbb00000000000000000000000000000000000000000000000000000000000000',
  '{"auth":"owner"}'::jsonb,  '["read","transfer","grant","admin"]'::jsonb, NULL, 2),
 ('\xbb00000000000000000000000000000000000000000000000000000000000000', 0,
  '\xcc00000000000000000000000000000000000000000000000000000000000000',
  '{"auth":"holder"}'::jsonb, '["read","transfer"]'::jsonb, 9999, 2),
 ('\xcc00000000000000000000000000000000000000000000000000000000000000', 0,
  '\xdd00000000000000000000000000000000000000000000000000000000000000',
  '{"auth":"holder"}'::jsonb, '["read"]'::jsonb, 9999, 2),
 ('\xcc00000000000000000000000000000000000000000000000000000000000000', 1,
  '\xbb00000000000000000000000000000000000000000000000000000000000000',
  '{"auth":"holder"}'::jsonb, '["admin"]'::jsonb, NULL, 2)
ON CONFLICT (holder, slot) DO NOTHING;

-- ---- the time-travel table (cell_history) ----------------------------------
-- The shipped DDL emitter materializes the latest-image dregg.cells; the cookbook
-- installs the cell-by-(id,ordinal) history projection from schema-tierB.sql §2.
CREATE TABLE IF NOT EXISTS dregg.cell_history (
    cell_id     bytea  NOT NULL,
    ordinal     bigint NOT NULL REFERENCES dregg.turns(ordinal),
    balance     bigint NOT NULL,
    nonce       bigint NOT NULL,
    fields_json jsonb,
    cell_root   bytea  NOT NULL,
    PRIMARY KEY (cell_id, ordinal)
);
CREATE INDEX IF NOT EXISTS cell_history_by_ordinal ON dregg.cell_history (ordinal);
ALTER TABLE dregg.cell_history ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.cell_history FORCE ROW LEVEL SECURITY;
DROP POLICY IF EXISTS cell_history_read ON dregg.cell_history;
-- A reader sees a cell's history iff its token admits read on that cell —
-- the SAME M1 gate as dregg.cells (so time-travel is cap-gated too).
CREATE POLICY cell_history_read ON dregg.cell_history FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(cell_id, 'hex')));
GRANT SELECT ON dregg.cell_history TO dregg_reader;
GRANT INSERT, UPDATE, DELETE ON dregg.cell_history TO dregg_kernel;
REVOKE INSERT, UPDATE, DELETE ON dregg.cell_history FROM PUBLIC;

INSERT INTO dregg.cell_history (cell_id, ordinal, balance, nonce, fields_json, cell_root)
VALUES
 ('\x5eff91e344090c47234eeceb0f684b2dbc1ffdafc0d5b69fb2427add7020cd86', 0,  0, 0, '{"balance":0,"nonce":0}',  '\x5e00'),
 ('\x5eff91e344090c47234eeceb0f684b2dbc1ffdafc0d5b69fb2427add7020cd86', 1, 20, 0, '{"balance":20,"nonce":0}', '\x5e01'),
 ('\x5c94568eff15b01d2580e2cce5b739612d9672f0248645fe973c0595847c319e', 1,  0, 0, '{"balance":0,"nonce":0}',  '\x5c01'),
 ('\x5c94568eff15b01d2580e2cce5b739612d9672f0248645fe973c0595847c319e', 2, 15, 0, '{"balance":15,"nonce":0}', '\x5c02')
ON CONFLICT (cell_id, ordinal) DO NOTHING;

\echo 'cookbook seed installed:'
SELECT (SELECT count(*) FROM dregg.cells)         AS cells,
       (SELECT count(*) FROM dregg.capabilities)  AS cap_edges,
       (SELECT count(*) FROM dregg.cell_history)  AS history_rows;
