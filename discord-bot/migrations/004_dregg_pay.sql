-- $DREGG payment credits — the sqlite backing for dregg-pay's `CreditStore` + the
-- user→deposit-index map (the "B" custodial HD-deposit model). Credits survive restart.
--
-- A user PAYS $DREGG to their deterministic per-user deposit address (dregg-pay's
-- `HdDeposit::deposit_address(discord_user_id)`); a Watcher observes the payment and
-- `CreditLedger::credit` mints run-credits at `price_per_run`, idempotent by the payment
-- reference. A paid /dungeon run `CreditLedger::debit`s one credit and routes to real Bedrock
-- under a per-run USD budget; an empty balance falls back to the free ollama/scripted tier.
--
-- NOTE: `Database::connect` also creates these tables inline (CREATE TABLE IF NOT EXISTS),
-- matching the bot's schema-in-code pattern; this file documents the schema for the migrations dir.

-- Per-user run-credit balance (the spendable "one run's worth of budget" count).
CREATE TABLE IF NOT EXISTS pay_credits (
    user     TEXT PRIMARY KEY,   -- the dregg-pay UserId == the Discord snowflake string
    credits  INTEGER NOT NULL DEFAULT 0
);

-- The idempotency ledger: every credited payment reference, so re-observing the same
-- on-chain payment never double-credits (belt-and-suspenders with the watcher's own dedup).
CREATE TABLE IF NOT EXISTS pay_processed (
    reference TEXT PRIMARY KEY   -- PaymentReceived::reference (mock:… / sol:…:slot:…)
);

-- The user→deposit-index map. The zero-config default derives the index from the user id
-- (a 2^31 hash, negligible-but-nonzero collision), but persisting an explicit assignment here
-- lets an operator move to collision-free monotonic indices without changing a user's address.
-- `deposit_address` caches the base58 address for display + re-derivation cross-checks.
CREATE TABLE IF NOT EXISTS pay_deposit_index (
    user            TEXT PRIMARY KEY,
    deposit_index   INTEGER NOT NULL,
    deposit_address TEXT NOT NULL,
    assigned_at     INTEGER NOT NULL
);
