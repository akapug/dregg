-- pg-dregg — Tier C schema: writes through the verifier (the CHECK tooth).
--
-- =============================================================================
-- This is the human-readable mirror of the Rust DDL emitter
-- `pg_dregg::mirror::ddl::tier_c()` (the SQL the extension actually ships via
-- `SELECT dregg_install_tier_c()`). See docs/PG-DREGG.md §10 (Tier C).
-- =============================================================================
-- Tier C makes the database engine — not a trusted writer — gate dregg state:
-- a row reaches dregg.cells/memory/capabilities ONLY through dregg.commit_log,
-- whose BEFORE INSERT trigger re-validates the turn and only then materializes
-- the post-image. This is the spine invariant (docs/PG-DREGG.md §8) enforced in
-- SQL:
--
--     Reads are free SQL; state mutates ONLY through verified turns.
--
-- Builds on schema-tierB.sql (the tables + the dregg.merge_cell upsert + the
-- role model). Requires SELECT dregg_install_schema() to have run first.
--
-- WHAT `dregg_verify_turn` DOES (and does NOT) — the honest boundary
-- (docs/PG-DREGG.md §10.2/§10.3):
--   * It RE-VALIDATES THE CHAIN: the turn's ordinal is the next expected one AND
--     its prev_root equals the database's current head root (the post-state of
--     turn N is the pre-state of turn N+1). This is the REAL anti-substitution
--     tooth — the exact gate the in-process mirror runs
--     (pg_dregg::mirror::verify_chain_step, which RootChain::extend also calls),
--     so a tampered / reordered / forged batch is refused by postgres itself.
--   * It does NOT re-prove a per-turn STARK. A CommitRecord carries no per-turn
--     proof; proof soundness is the whole-chain IVC light client's job
--     (circuit::ivc_turn_chain::verify_turn_chain_recursive), not a per-row pg
--     check. The realizable per-row gate is the structural chain re-validation.
--   * It is NOT stubbed to TRUE — the forbidden failure mode (§10.3): a labeled
--     gate that does not gate. It fails closed on any deviation, and the
--     materialization is downstream of it (no chain ⇒ no rows).

CREATE EXTENSION IF NOT EXISTS pg_dregg;

-- ===========================================================================
-- 1.  The chain re-validator (provided by the extension).
-- ===========================================================================
-- TRUE iff a turn with pre-state `prev_root` and `ordinal` chains onto the
-- database's current head (read from dregg.turns): `ordinal` is the next
-- expected one AND `prev_root` equals the head root. `ledger_root` is the
-- post-state the row claims to produce (recorded by the trigger). STABLE
-- (depends on the current head, constant within a statement); STRICT +
-- fail-closed (a malformed/short root ⇒ FALSE).
--
--   CREATE FUNCTION dregg_verify_turn(prev_root bytea, ledger_root bytea,
--                                     ordinal bigint)
--     RETURNS boolean STABLE PARALLEL SAFE STRICT;   -- (extension-provided)

-- ===========================================================================
-- 2.  The commit log — the ONE door to state.
-- ===========================================================================
-- A verified-turn post-image is submitted here (the turn metadata + its
-- touched-cell post-images as a jsonb array — the realizable payload). An
-- application NEVER writes the state tables directly (the Tier-B privilege
-- lockdown forbids it); the only door is this INSERT, and this INSERT runs the
-- verifier. Even dregg_kernel writes go through the trigger.
CREATE TABLE IF NOT EXISTS dregg.commit_log (
    ordinal      bigint PRIMARY KEY,
    height       bigint NOT NULL,
    block_id     bytea  NOT NULL,
    block_executed_up_to bigint NOT NULL,
    turn_hash    bytea  NOT NULL,
    creator      bytea  NOT NULL,
    receipt_hash bytea  NOT NULL,
    ledger_root  bytea  NOT NULL,   -- the verified post-state root of this turn
    prev_root    bytea  NOT NULL,   -- the pre-state root it claims to chain onto
    cells        jsonb  NOT NULL DEFAULT '[]'::jsonb,  -- touched-cell post-images
    submitted_at timestamptz NOT NULL DEFAULT now());

-- ===========================================================================
-- 3.  The gate — verify (chain) + record + materialize, atomically.
-- ===========================================================================
-- A row reaches dregg.cells/memory/capabilities ONLY through this trigger, and
-- ONLY after dregg_verify_turn admits the chain. The materialize step upserts
-- the post-images via the pg17 dregg.merge_cell MERGE in the SAME transaction —
-- so the cells and the turns row commit together or not at all. SECURITY
-- DEFINER so the least-privileged submitter (who holds only INSERT on
-- commit_log) never touches the locked-down state tables directly.
CREATE OR REPLACE FUNCTION dregg.apply_verified_turn() RETURNS trigger
LANGUAGE plpgsql SECURITY DEFINER AS $$
DECLARE c jsonb;
BEGIN
    -- (1) The chain MUST re-validate (anti-substitution). Fail-closed: RAISE.
    IF NOT dregg_verify_turn(NEW.prev_root, NEW.ledger_root, NEW.ordinal) THEN
        RAISE EXCEPTION 'dregg: turn % does not chain onto the head root — refused (anti-substitution)', NEW.ordinal;
    END IF;

    -- (2) Record the verified turn row.
    INSERT INTO dregg.turns(ordinal, height, block_id, block_executed_up_to,
                            turn_hash, creator, receipt_hash, ledger_root, prev_root)
        VALUES (NEW.ordinal, NEW.height, NEW.block_id, NEW.block_executed_up_to,
                NEW.turn_hash, NEW.creator, NEW.receipt_hash, NEW.ledger_root, NEW.prev_root);

    -- (3) Materialize the post-image cells, same txn, via the pg17 MERGE upsert.
    FOR c IN SELECT * FROM jsonb_array_elements(NEW.cells) LOOP
        PERFORM dregg.merge_cell(
            decode(c->>'cell_id', 'hex'),
            c->>'mode',
            (c->>'balance')::bigint,
            (c->>'nonce')::bigint,
            decode(coalesce(c->>'fields',''), 'hex'),
            (c->'fields_json'),
            c->>'lifecycle',
            NEW.ordinal,
            decode(c->>'cell_root', 'hex'));
    END LOOP;
    RETURN NEW;
END $$;

DROP TRIGGER IF EXISTS verify_before_apply ON dregg.commit_log;
CREATE TRIGGER verify_before_apply BEFORE INSERT ON dregg.commit_log
    FOR EACH ROW EXECUTE FUNCTION dregg.apply_verified_turn();

-- ===========================================================================
-- 4.  Submitting a turn IS the only write. The kernel writer gets INSERT +
--     SELECT on commit_log (it submits AND audits the verified-store door) —
--     and even the INSERT runs the verifier. The turn-effects JSON_TABLE view
--     (a turn's touched cells exploded into rows) is granted to it too. PUBLIC
--     gets nothing.
-- ===========================================================================
GRANT INSERT, SELECT ON dregg.commit_log TO dregg_kernel;
GRANT SELECT ON dregg.turn_effects TO dregg_kernel;
REVOKE INSERT, UPDATE, DELETE ON dregg.commit_log FROM PUBLIC;

-- The light client, in SQL: dregg.turns is now a hash chain (each row's
-- prev_root is the prior row's ledger_root, enforced by the gate). A consumer
-- can walk dregg.receipt_chain and re-verify it itself — reads are not only
-- free, they can be ATTESTED free.

-- ===========================================================================
-- 5.  The WRITE-path outbox (docs/PG-DREGG.md §11) — submit a turn FROM pg.
-- ===========================================================================
-- The mirror of pg_dregg::mirror::ddl::write_outbox() (SELECT
-- dregg_install_write_outbox()). A pg-user submits a SIGNED turn FROM postgres
-- via dregg_submit_turn(signed_turn, agent), which enqueues it here; the node
-- drains the queue, executes through the REAL verified executor, and the
-- post-image flows back via the mirror. Postgres NEVER executes — it enqueues an
-- intent the verifier must accept. RLS gates submission on the dregg cap layer:
-- a role submits ONLY the turns its capability admits `submit` on.
--
--   CREATE TABLE dregg.submit_queue (
--       id uuid PRIMARY KEY DEFAULT uuidv7(),   -- pg18: temporally-sortable drain key
--       agent bytea NOT NULL,            -- the turn's agent cell (the RLS key)
--       signed_turn bytea NOT NULL,      -- postcard SignedTurn bytes
--       submitter text NOT NULL DEFAULT current_user,
--       status text NOT NULL DEFAULT 'pending'
--              CHECK (status IN ('pending','executed','refused')),
--       receipt_hash bytea, error text,  -- set by the node on resolution
--       submitted_at timestamptz NOT NULL DEFAULT now(), resolved_at timestamptz);
--
--   CREATE POLICY submit_gate ON dregg.submit_queue FOR INSERT TO dregg_reader
--       WITH CHECK (dregg_admits('submit', encode(agent, 'hex')));
--   CREATE POLICY submit_read ON dregg.submit_queue FOR SELECT TO dregg_reader
--       USING (dregg_admits('submit', encode(agent, 'hex')));
--   GRANT INSERT, SELECT ON dregg.submit_queue TO dregg_reader;  -- the submitter
--   GRANT SELECT, UPDATE ON dregg.submit_queue TO dregg_kernel;  -- the node drainer

-- ===========================================================================
-- 6.  Tier D preview (docs/PG-DREGG.md §11) — the executor as a pg function.
-- ===========================================================================
-- With the `tier-d` feature (the embedded executor, gated on the pg/Lean
-- process-model spike), submission collapses to EXECUTION inside the backend:
--
--   SELECT dregg_submit_turn_inproc(envelope);   -- runs the kernel, returns the receipt
--
-- and the post-state lands atomically. At that point postgres IS a dregg node:
--   BEGIN;
--     SELECT dregg_submit_turn_inproc(pay_invoice_envelope);  -- dregg state changes
--     UPDATE invoices SET paid = true WHERE id = 7;           -- app state changes
--   COMMIT;                                                    -- both, or neither.
-- That cross-domain atomicity (kernel + app data in one transaction) is the
-- unique Tier-D payoff no separate node can offer. The §11 outbox above is the
-- realizable slice today (the node executes out-of-process); Tier D is the
-- north-star where postgres executes in-process.
