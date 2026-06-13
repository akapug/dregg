-- pg-dregg — LIVE pg18 end-to-end driver (the M2/M2.5 "pg re-validates" proof).
--
-- Run it against a pg18 with the pg_dregg extension installed (see
-- scripts/e2e-live.sh, which stands up the cluster, sets the issuer key, and
-- pipes this file through psql). It drives the REAL path on a live database:
--
--   * Tier B/C schema installed from the Rust DDL emitter (the exact SQL the
--     extension ships).
--   * A turn's verified post-image lands as ACTUAL rows through dregg.commit_log
--     — its trigger runs the REAL chain re-validator (dregg_verify_turn) and the
--     pg18 dregg.merge_cell upsert (MERGE + RETURNING old/new delta).
--   * The turns table chains (each prev_root is the prior ledger_root).
--   * A TAMPERED / reordered batch is REFUSED by the pg-side chain (the trigger
--     RAISEs the anti-substitution error) — and the store is left intact.
--   * The §11 write outbox gates submission: a role submits only the turns its
--     capability admits `submit` on (driven from scripts/e2e-live.sh, which has
--     the minted token).
--
-- This is the human-runnable twin of the #[pg_test]s in src/lib.rs.

\set ON_ERROR_STOP off
\echo '== installing the extension + Tier B + Tier C =='
CREATE EXTENSION IF NOT EXISTS pg_dregg;
SELECT dregg_install_schema();
SELECT dregg_install_tier_c();

\echo ''
\echo '== 1. dregg_verify_turn at genesis (ord 0, no head yet) => TRUE =='
SELECT dregg_verify_turn(
    '\x0000000000000000000000000000000000000000000000000000000000000000'::bytea,
    '\x1111111111111111111111111111111111111111111111111111111111111111'::bytea,
    0) AS genesis_chains;

\echo ''
\echo '== 2. submit GENESIS (ord 0) through the commit_log door — TREASURY funded =='
INSERT INTO dregg.commit_log(ordinal,height,block_id,block_executed_up_to,turn_hash,creator,receipt_hash,ledger_root,prev_root,cells)
VALUES (0,0,'\x22'::bytea,0,'\x33'::bytea,'\xc0'::bytea,'\x44'::bytea,
        '\x1111111111111111111111111111111111111111111111111111111111111111'::bytea,
        '\x0000000000000000000000000000000000000000000000000000000000000000'::bytea,
        '[{"cell_id":"c000000000000000000000000000000000000000000000000000000000000000","mode":"Hosted","balance":1000000,"nonce":0,"fields":"","fields_json":{"balance":1000000,"nonce":0},"lifecycle":"Active","cell_root":"c000000000000000000000000000000000000000000000000000000000000000"}]'::jsonb);

\echo '== 3. submit TRANSFER (ord 1, prev_root = genesis post-root) — chains => admitted =='
INSERT INTO dregg.commit_log(ordinal,height,block_id,block_executed_up_to,turn_hash,creator,receipt_hash,ledger_root,prev_root,cells)
VALUES (1,1,'\x22'::bytea,1,'\x3301'::bytea,'\xc0'::bytea,'\x4401'::bytea,
        '\x2222222222222222222222222222222222222222222222222222222222222222'::bytea,
        '\x1111111111111111111111111111111111111111111111111111111111111111'::bytea,
        '[{"cell_id":"c000000000000000000000000000000000000000000000000000000000000000","mode":"Hosted","balance":999500,"nonce":1,"fields":"","fields_json":{"balance":999500,"nonce":1},"lifecycle":"Active","cell_root":"c000000000000000000000000000000000000000000000000000000000000000"},{"cell_id":"a100000000000000000000000000000000000000000000000000000000000000","mode":"Hosted","balance":400,"nonce":0,"fields":"","fields_json":{"balance":400,"nonce":0},"lifecycle":"Active","cell_root":"a100000000000000000000000000000000000000000000000000000000000000"}]'::jsonb);

\echo ''
\echo '== 4. THE ROWS LANDED: the verified hash chain + the materialized cells =='
SELECT ordinal, encode(prev_root,'hex') AS prev_root, encode(ledger_root,'hex') AS ledger_root FROM dregg.turns ORDER BY ordinal;
SELECT encode(cell_id,'hex') AS cell, balance, nonce, last_ordinal FROM dregg.cells ORDER BY cell_id;

\echo ''
\echo '== 4b. pg18 MERGE + RETURNING old/new: dregg.merge_cell returns <ACTION> <DELTA> =='
\echo '--      on a throwaway demo cell (ee..): INSERT then UPDATE; the delta is read from the pre-image in ONE statement'
SET ROLE dregg_kernel;
SELECT dregg.merge_cell('\xee00000000000000000000000000000000000000000000000000000000000000'::bytea,
    'Hosted',1000,0,'\x'::bytea,'{"balance":1000,"nonce":0}'::jsonb,'Active',1,
    '\xee00000000000000000000000000000000000000000000000000000000000000'::bytea) AS insert_arm;   -- 'INSERT +1000'
SELECT dregg.merge_cell('\xee00000000000000000000000000000000000000000000000000000000000000'::bytea,
    'Hosted',700,1,'\x'::bytea,'{"balance":700,"nonce":1}'::jsonb,'Active',1,
    '\xee00000000000000000000000000000000000000000000000000000000000000'::bytea) AS update_arm;   -- 'UPDATE -300'
\echo '--      pg18 VIRTUAL generated columns (cell_root_hex / balance_field) equal their canonical source on READ'
SELECT balance, balance_field, (cell_root_hex = encode(cell_root,'hex')) AS root_hex_ok
FROM dregg.cells WHERE cell_id='\xee00000000000000000000000000000000000000000000000000000000000000'::bytea;
\echo '--      pg18 generated-column kinds: cell_hex STORED (indexed), cell_root_hex / balance_field VIRTUAL (s/v)'
SELECT attname, attgenerated FROM pg_attribute
WHERE attrelid='dregg.cells'::regclass AND attname IN ('cell_hex','cell_root_hex','balance_field') ORDER BY attname;
DELETE FROM dregg.cells WHERE cell_id='\xee00000000000000000000000000000000000000000000000000000000000000'::bytea;  -- leave the story untouched
RESET ROLE;

\echo ''
\echo '== 5. dregg_verify_turn on a TAMPERED ord-2 (prev_root substituted) => FALSE =='
SELECT dregg_verify_turn(
    '\x9999999999999999999999999999999999999999999999999999999999999999'::bytea,
    '\xdeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeadde'::bytea,
    2) AS tampered_chains;

\echo '== 5b. SUBMIT the tampered ord-2 through the gate — the trigger RAISEs (REFUSED) =='
INSERT INTO dregg.commit_log(ordinal,height,block_id,block_executed_up_to,turn_hash,creator,receipt_hash,ledger_root,prev_root,cells)
VALUES (2,2,'\x22'::bytea,2,'\x3302'::bytea,'\xa1'::bytea,'\x4402'::bytea,
        '\xdeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeaddeadde'::bytea,
        '\x9999999999999999999999999999999999999999999999999999999999999999'::bytea,
        '[{"cell_id":"a100000000000000000000000000000000000000000000000000000000000000","mode":"Hosted","balance":999999,"nonce":9,"fields":"","fields_json":{"balance":999999,"nonce":9},"lifecycle":"Active","cell_root":"a100000000000000000000000000000000000000000000000000000000000000"}]'::jsonb);

\echo '== 5c. a REPLAYED ord-0 (ordinal gap) is also REFUSED =='
INSERT INTO dregg.commit_log(ordinal,height,block_id,block_executed_up_to,turn_hash,creator,receipt_hash,ledger_root,prev_root,cells)
VALUES (0,0,'\x22'::bytea,0,'\x3399'::bytea,'\xc0'::bytea,'\x4499'::bytea,
        '\x5555555555555555555555555555555555555555555555555555555555555555'::bytea,
        '\x0000000000000000000000000000000000000000000000000000000000000000'::bytea,'[]'::jsonb);

\echo ''
\echo '== 6. THE STORE IS INTACT: still 2 turns, ALICE still 400 (forged 999999 never landed) =='
SELECT (SELECT count(*) FROM dregg.turns) AS turns_recorded,
       (SELECT count(*) FROM dregg.cells) AS cells_materialized,
       (SELECT balance FROM dregg.cells WHERE cell_id='\xa100000000000000000000000000000000000000000000000000000000000000'::bytea) AS alice_balance,
       (SELECT encode(ledger_root,'hex') FROM dregg.turns ORDER BY ordinal DESC LIMIT 1) AS head_root;

\echo ''
\echo '== 7. the privilege lockdown: an app role gets ZERO write on state; only the kernel submits =='
DO $$ BEGIN CREATE ROLE dregg_app NOLOGIN; EXCEPTION WHEN duplicate_object THEN NULL; END $$;
SELECT has_table_privilege('dregg_app','dregg.cells','INSERT')       AS app_insert_cells,
       has_table_privilege('dregg_app','dregg.commit_log','INSERT')  AS app_submit_turn,
       has_table_privilege('dregg_kernel','dregg.commit_log','INSERT') AS kernel_submit_turn;

\echo ''
\echo '== LIVE pg18 E2E complete: rows landed, chain verified, tamper refused, lockdown enforced. =='
