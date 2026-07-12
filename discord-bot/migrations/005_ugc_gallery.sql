-- The UGC GALLERY — durable published universes + their no-cheat leaderboards.
--
-- The `/gallery` registry was in-memory + per-process: a bot restart dropped every
-- published universe and every verified completion back to the built-in dungeon. These
-- two tables close that gap. What is stored is the MINIMAL, REPRODUCIBLE public source:
--
--   * a universe's SEED-EPOCH (for a procgen `daily` world) or its spween SOURCE (for an
--     `authored` world) — NOT a cached world shape. On boot the world is regenerated
--     through the same public `ugc-dregg` constructor and its content address recomputed.
--   * a completion's MOVE SEQUENCE + player + claimed turns — NOT a trusted receipt blob.
--     On boot the receipt chain is deterministically re-recorded on a fresh, identically
--     seeded world and re-verified through `Registry::submit` (the no-cheat gate).
--
-- Because reload REPLAYS through the real verifier, a TAMPERED ROW CANNOT RESURRECT A
-- CHEAT: edited moves that no longer win are rejected (`DidNotWin` / a refused move); an
-- edited `claimed_turns` is rejected (`ResultMismatch`); an edited universe source/author/
-- epoch recomputes to a different content address than its stored `id_hex` and the row is
-- dropped. None of these land on the board. See discord-bot/src/commands/gallery.rs
-- (`GalleryStore`, `load_registry`) and its driven persist→reload→reverify tests.
--
-- NOTE: `Database::connect` also creates these tables inline (CREATE TABLE IF NOT EXISTS),
-- matching the bot's schema-in-code pattern; this file documents the schema for the
-- migrations dir. The main loop adds the matching `Database` methods + a `SqliteGalleryStore`
-- (mirroring `pay::SqliteCreditStore`) and calls `gallery::install_store(...)` once at boot.

-- A published universe's public source. Content-addressed: `id_hex` is the address the
-- world hashed to at publish time; reload recomputes it and DROPS the row on a mismatch.
CREATE TABLE IF NOT EXISTS ugc_universes (
    id_hex     TEXT PRIMARY KEY,              -- universe content address (hex) + tamper check
    kind       TEXT NOT NULL,                 -- 'daily' (procgen seed-epoch) | 'authored' (spween source)
    name       TEXT NOT NULL,                 -- display name (derived for daily; authoritative for authored)
    author     TEXT NOT NULL,                 -- author label (binds into the content address)
    source     TEXT NOT NULL DEFAULT '',      -- spween source (authored); '' for daily (regenerated from epoch)
    epoch_hex  TEXT,                          -- daily only: hex of the 32-byte epoch commitment (blake3(seed_text))
    win_json   TEXT NOT NULL DEFAULT '[]',    -- WinCondition vars [[name, value], ...] as JSON
    created_at INTEGER NOT NULL
);

-- A verified completion, stored as its reproducible input. `key_hex` is the idempotency PK
-- (blake3(universe_id_hex || player || moves_json)) so a re-submit / a double-load never
-- duplicates a board entry. `claimed_turns` is stored INDEPENDENTLY of the moves, so a
-- tampered value trips `ResultMismatch` when replayed.
CREATE TABLE IF NOT EXISTS ugc_completions (
    key_hex         TEXT PRIMARY KEY,         -- blake3(universe_id_hex || player || moves_json)
    universe_id_hex TEXT NOT NULL,            -- the universe this completion is for
    player          TEXT NOT NULL,
    moves_json      TEXT NOT NULL,            -- choice indices as a JSON array
    claimed_turns   INTEGER NOT NULL,         -- claimed turns-to-win (re-checked against the verified move count)
    created_at      INTEGER NOT NULL
);

-- Rebuild a universe's board in one scan on boot.
CREATE INDEX IF NOT EXISTS idx_ugc_completions_universe
    ON ugc_completions (universe_id_hex);
