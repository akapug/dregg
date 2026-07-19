//! # `dreggnet-discord-identity` — the ONE Discord custodial-seed derivation.
//!
//! The single source of truth for the deterministic per-Discord-user custodial seed:
//!
//! ```text
//! seed = BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret ‖ discord_user_id_le)   // seed_for
//! ```
//!
//! This seed IS the Ed25519 secret both callers feed into their signer construction
//! (`AgentCipherclerk::from_key_bytes` in the bot, `TurnSigner::from_seed` on the web Activity
//! surface), so a Discord user always re-derives the SAME dregg identity — reproducible custodial
//! keys, byte-for-byte identical across the two processes.
//!
//! ## Why this crate exists (the extraction, [`docs/DISCORD-ACTIVITIES-DESIGN.md`] §3)
//!
//! `dreggnet-web` serves the Discord **Activity** (`/da`) surface and must attribute the Activity
//! player the EXACT identity the in-chat bot does. It cannot depend on `dregg-discord-bot` (an
//! EXCLUDED workspace — an sqlx `libsqlite3-sys` `links = "sqlite3"` conflict), and re-implementing
//! `seed_for` there is the identity-drift class the frontends were explicitly built to avoid. So
//! the derivation lives HERE — CALLED by both, never mirrored:
//!
//! - `discord-bot/src/cipherclerk.rs` re-exports [`seed_for`] + [`op_token`] (behaviour unchanged;
//!   `UserCipherclerk::derive` calls this crate's [`seed_for`]);
//! - `dreggnet-web`'s Activity surface calls [`seed_for`] to build the custodial [`TurnSigner`] for
//!   a ticket-verified uid.
//!
//! The mirror of the `dreggnet-telegram::cipherclerk` extraction, minus any transport. Deliberately
//! light (`blake3` + `hex` only): it pulls none of the heavy signing/prover graph into a caller.

/// The BLAKE3 derive-key domain for Discord custodial seeds. **Pinned** — a changed domain (or a
/// changed byte layout in [`seed_for`]) rotates EVERY custodial identity the bot ever derived and
/// forks the web Activity surface off the in-chat player. Distinct from the Telegram frontend's
/// `"dregg-telegram-bot-v1"` so a Discord uid and a Telegram uid never collide onto one identity.
pub const DISCORD_SEED_DOMAIN: &str = "dregg-discord-bot-v1";

/// The BLAKE3 derive-key domain for the per-user **op token** — domain-separated from
/// [`DISCORD_SEED_DOMAIN`] (`-op-token-v1` vs `-v1`) so the token is NOT the signing key: leaking
/// it lets a holder drive ops as that one user, never recover their Ed25519 secret.
pub const DISCORD_OP_TOKEN_DOMAIN: &str = "dregg-discord-bot-op-token-v1";

/// The deterministic 32-byte custodial seed for a Discord user — the SINGLE source of truth for
/// `seed = BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret ‖ discord_user_id_le)`. This seed
/// IS the Ed25519 secret fed to `AgentCipherclerk::from_key_bytes` (bot) / `TurnSigner::from_seed`
/// (web Activity surface), so reconstructing the same user's cipherclerk uses this exact value —
/// the identity is reproducible.
///
/// Moved byte-for-byte from `discord-bot/src/cipherclerk.rs`: the same `to_le_bytes` uid layout,
/// the same `bot_secret ‖ uid_le` concatenation order, the same [`DISCORD_SEED_DOMAIN`] context.
pub fn seed_for(bot_secret: &[u8; 32], discord_user_id: u64) -> [u8; 32] {
    let user_id_bytes = discord_user_id.to_le_bytes();
    let mut input = Vec::with_capacity(32 + 8);
    input.extend_from_slice(bot_secret);
    input.extend_from_slice(&user_id_bytes);
    blake3::derive_key(DISCORD_SEED_DOMAIN, &input)
}

/// Derive the **per-user op token** — the capability that proves a caller controls a given Discord
/// user when driving a custodial op over HTTP (`POST /api/op`). Keyed by the bot's master secret,
/// so it is unforgeable without that secret yet deterministically reproducible for a
/// Discord-AUTHENTICATED user. Domain-separated from the signing seed (see
/// [`DISCORD_OP_TOKEN_DOMAIN`]) so leaking it never recovers the Ed25519 secret.
///
/// Moved byte-for-byte from `discord-bot/src/cipherclerk.rs`.
pub fn op_token(bot_secret: &[u8; 32], discord_user_id: u64) -> String {
    let mut input = Vec::with_capacity(32 + 8);
    input.extend_from_slice(bot_secret);
    input.extend_from_slice(&discord_user_id.to_le_bytes());
    hex::encode(blake3::derive_key(DISCORD_OP_TOKEN_DOMAIN, &input))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **The canonical pin** — the derivation is recomputed inline from the LITERAL domain string
    /// and byte layout, so any drift in [`seed_for`] (a changed domain, a changed uid byte order,
    /// a changed concatenation) diverges from this and fails. The two callers each carry the same
    /// pin against their own construction path (`discord-bot/src/cipherclerk.rs` and
    /// `dreggnet-web/src/discord_activity.rs`) — one seed, three pins.
    #[test]
    fn seed_for_is_pinned_byte_for_byte() {
        let secret = [7u8; 32];
        let uid = 42_424_242u64;
        let mut input = Vec::new();
        input.extend_from_slice(&secret);
        input.extend_from_slice(&uid.to_le_bytes());
        let expected = blake3::derive_key("dregg-discord-bot-v1", &input);
        assert_eq!(
            seed_for(&secret, uid),
            expected,
            "seed_for must be BLAKE3_derive_key(\"dregg-discord-bot-v1\", secret ‖ uid_le)"
        );
        assert_eq!(DISCORD_SEED_DOMAIN, "dregg-discord-bot-v1");
    }

    /// Deterministic + per-user + secret-bound: the same inputs always yield the same seed;
    /// different uids and different secrets diverge.
    #[test]
    fn seed_for_is_deterministic_per_user_and_per_secret() {
        let s = [3u8; 32];
        assert_eq!(seed_for(&s, 1), seed_for(&s, 1));
        assert_ne!(seed_for(&s, 1), seed_for(&s, 2));
        assert_ne!(seed_for(&s, 1), seed_for(&[9u8; 32], 1));
    }

    /// The op token is domain-separated from the signing seed — its bytes never equal the seed for
    /// the same `(secret, uid)`, so a leaked token can never be the Ed25519 secret. Deterministic
    /// + per-user, as `http_server.rs`'s gate requires.
    #[test]
    fn op_token_is_domain_separated_and_deterministic() {
        let secret = [5u8; 32];
        assert_eq!(op_token(&secret, 1), op_token(&secret, 1));
        assert_ne!(op_token(&secret, 1), op_token(&secret, 2));
        assert_ne!(op_token(&secret, 1), op_token(&[8u8; 32], 1));
        // NOT the signing seed (different BLAKE3 domain over the same input).
        assert_ne!(
            hex::decode(op_token(&secret, 1)).unwrap().as_slice(),
            seed_for(&secret, 1).as_slice()
        );
        assert_eq!(DISCORD_OP_TOKEN_DOMAIN, "dregg-discord-bot-op-token-v1");
    }
}
