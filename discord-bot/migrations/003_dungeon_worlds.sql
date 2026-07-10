-- The community DUNGEON LIBRARY — authored `.dungeon` worlds published from Discord.
--
-- The SOURCE text is authoritative: `/dungeon start <name>` re-parses it fail-closed on every
-- load (never a cached binary shape). Provenance is an AUTHOR LABEL — the publisher's Discord id
-- and their derived cipherclerk Ed25519 public key hex. It records WHO published; it is NOT a
-- signature over the source (see discord-bot/src/commands/fiction.rs).
--
-- NOTE: `Database::connect` also creates this table inline (CREATE TABLE IF NOT EXISTS), matching
-- the bot's existing schema-in-code pattern; this file documents the schema for the migrations dir.
CREATE TABLE IF NOT EXISTS dungeon_worlds (
    name              TEXT PRIMARY KEY,
    display_name      TEXT NOT NULL,
    source            TEXT NOT NULL,
    author_discord_id TEXT NOT NULL,
    author_pubkey     TEXT NOT NULL,
    validates_clean   INTEGER NOT NULL,
    room_count        INTEGER NOT NULL,
    created_at        INTEGER NOT NULL
);
