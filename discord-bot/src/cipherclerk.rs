//! Custodial cclerk: deterministic per-user cipherclerks backed by the canonical
//! `dregg_app_framework::AppCipherclerk` (and underneath, `dregg_sdk::AgentCipherclerk`).
//!
//! Each Discord user maps to a deterministic 32-byte seed:
//!
//! ```text
//! seed = BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret || discord_user_id)
//! ```
//!
//! The seed is fed into `AgentCipherclerk::from_key_bytes` to produce a real
//! Ed25519 signing identity. The Discord user's `CellId` is then
//! `AppCipherclerk::cell_id()` — the canonical dregg derivation (public_key +
//! BLAKE3(domain)). No bespoke key derivation, no parallel cell-id
//! derivation: the bot is a peer of the SDK rather than a separate
//! implementation.
//!
//! # Wire-signature transition gap
//!
//! Some legacy devnet endpoints (`/api/gallery/auctions/<id>/bid`,
//! `/api/identity/credentials/issue`, etc.)
//! expects a hex-encoded `signature` field defined as
//! `blake3(action_bytes || raw_secret)`. That scheme is *not* Ed25519, and
//! `AppCipherclerk` deliberately hides the raw secret to keep apps from
//! reaching past the framework. Transfer commands now use canonical
//! `SignedTurn` ingress, but this cclerk still retains the raw 32-byte seed
//! for the remaining explicitly legacy BLAKE3-MAC paths. Once those endpoints
//! move to canonical actions, this field and its accessor should be deleted in
//! favor of `AppCipherclerk::sign_action`.

use dregg_app_framework::AppCipherclerk;
use dregg_sdk::AgentCipherclerk;
use zeroize::Zeroizing;

/// A deterministic per-user cclerk handle.
///
/// Wraps a canonical [`AppCipherclerk`] derived from the bot secret + Discord
/// user id. The raw seed is retained for the legacy BLAKE3-MAC wire
/// signature path (see module docs).
pub struct UserCipherclerk {
    /// Canonical app-level cipherclerk handle (Ed25519, framework-bound).
    pub app: AppCipherclerk,
    /// Raw 32-byte seed (== Ed25519 secret key). Held only for the
    /// legacy BLAKE3-MAC wire signature; do not use for new signing
    /// paths — call `app.sign_action(...)` / `app.make_action(...)`.
    legacy_secret: [u8; 32],
    /// Cached hex-encoded ed25519 public key.
    public_key_hex_cached: String,
    /// Cached cell-id bytes.
    cell_id_bytes_cached: [u8; 32],
    /// Cached cell-id hex.
    cell_id_hex_cached: String,
}

impl UserCipherclerk {
    /// Derive a cclerk for the given Discord user.
    ///
    /// * `bot_secret` — the bot's master secret (32 bytes from env).
    /// * `discord_user_id` — the Discord snowflake id.
    /// * `federation_id` — the federation this bot binds signed
    ///   actions to (the bot's configured dregg node group). Used by
    ///   `AppCipherclerk` to bind action signatures against cross-federation
    ///   replay.
    pub fn derive(bot_secret: &[u8; 32], discord_user_id: u64, federation_id: [u8; 32]) -> Self {
        // Step 1: derive the deterministic 32-byte seed (matches the
        // legacy scheme so existing user→cell mappings persist).
        let seed = seed_for(bot_secret, discord_user_id);

        // Step 2: build a canonical AgentCipherclerk from the seed. Wrapping
        // the secret in `Zeroizing` here ensures the temporary copy
        // we hand to `from_key_bytes` is wiped after construction.
        let secret = Zeroizing::new(seed);
        let agent = AgentCipherclerk::from_key_bytes(secret);

        // Step 3: wrap in an AppCipherclerk bound to this bot's federation.
        // The default domain ("default") is what AgentCipherclerk::cell_id
        // uses for its identity-cell derivation; we use that same
        // domain here so callers can call `cclerk.cell_id()` without
        // threading a domain string.
        let public_key_hex_cached = hex::encode(agent.public_key().0);
        let app = AppCipherclerk::new(agent, federation_id);
        let cell_id = app.cell_id();
        let cell_id_bytes_cached = cell_id.0;
        let cell_id_hex_cached = hex::encode(cell_id_bytes_cached);

        Self {
            app,
            legacy_secret: seed,
            public_key_hex_cached,
            cell_id_bytes_cached,
            cell_id_hex_cached,
        }
    }

    /// The user's cell id (32 bytes).
    pub fn cell_id_bytes(&self) -> [u8; 32] {
        self.cell_id_bytes_cached
    }

    /// The user's cell id as lowercase hex.
    pub fn cell_id_hex(&self) -> &str {
        &self.cell_id_hex_cached
    }

    /// Short cell-id display (first 8 bytes / 16 hex chars).
    pub fn cell_id_short(&self) -> String {
        hex::encode(&self.cell_id_bytes_cached[..8])
    }

    /// The user's Ed25519 public key as lowercase hex.
    pub fn public_key_hex(&self) -> &str {
        &self.public_key_hex_cached
    }

    /// The raw secret bytes (== Ed25519 secret) — exposed only for the
    /// legacy BLAKE3-MAC wire signature path used by old devnet endpoints.
    /// See module docs.
    pub fn legacy_secret(&self) -> &[u8; 32] {
        &self.legacy_secret
    }

    /// Hex-encode the legacy secret for `/cipherclerk export`.
    ///
    /// Discord users see this as their "private key"; it is the
    /// Ed25519 secret. Once the wire format migration completes, this
    /// continues to be a valid export (matches `AgentCipherclerk::from_key_bytes`).
    pub fn private_key_hex(&self) -> String {
        hex::encode(self.legacy_secret)
    }
}

// THE ONE DERIVATION, EXTRACTED. `seed_for` (the custodial seed) and `op_token` (the
// per-user op capability) moved byte-for-byte into the light root-workspace crate
// `dreggnet-discord-identity` so `dreggnet-web`'s Discord Activity surface can derive the SAME
// identity WITHOUT depending on this excluded workspace and WITHOUT mirroring the derivation
// (the drift class). Re-exported here so every existing caller (`crate::cipherclerk::seed_for`,
// `crate::cipherclerk::op_token`, `UserCipherclerk::derive` above) is unchanged: one impl, two
// callers, zero identity drift. See docs/DISCORD-ACTIVITIES-DESIGN.md §3.
pub use dreggnet_discord_identity::{
    DISCORD_OP_TOKEN_DOMAIN, DISCORD_SEED_DOMAIN, op_token, seed_for,
};

/// Sign a string action using the legacy BLAKE3-MAC scheme accepted by
/// old devnet endpoints. Returns a hex-encoded 32-byte MAC.
///
/// This is the wire signature path described in the module docs — it
/// will be deleted once the devnet endpoints accept canonical signed
/// `Action`s (built via `cclerk.app.make_action(...)`).
pub fn sign_legacy(cclerk: &UserCipherclerk, action_bytes: &[u8]) -> String {
    let mut msg = Vec::with_capacity(action_bytes.len() + 32);
    msg.extend_from_slice(action_bytes);
    msg.extend_from_slice(cclerk.legacy_secret());
    let sig = blake3::hash(&msg);
    hex::encode(sig.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::TurnSigner;

    /// **The parity pin — bot side.** The extracted [`seed_for`] must remain the historical
    /// `BLAKE3_derive_key("dregg-discord-bot-v1", secret ‖ uid_le)`; the pinned algorithm is
    /// recomputed inline, so a drift in the shared crate (domain string or byte layout) diverges
    /// from this literal and fails HERE (the in-chat side). Its twin lives in
    /// `dreggnet-web/src/discord_activity.rs`, hardcoding the same literal on the web side.
    #[test]
    fn seed_for_is_pinned_byte_for_byte() {
        let secret = [7u8; 32];
        let uid = 42_424_242u64;
        let mut input = Vec::new();
        input.extend_from_slice(&secret);
        input.extend_from_slice(&uid.to_le_bytes());
        let expected = blake3::derive_key("dregg-discord-bot-v1", &input);
        assert_eq!(seed_for(&secret, uid), expected);
        assert_eq!(DISCORD_SEED_DOMAIN, "dregg-discord-bot-v1");
    }

    /// **The identity parity.** The pubkey the bot attributes (`UserCipherclerk`, via
    /// `AgentCipherclerk::from_key_bytes`) is byte-for-byte the pubkey the web Activity surface
    /// signs turns under (`TurnSigner::from_seed`), because BOTH construct an Ed25519 identity from
    /// the SAME [`seed_for`] output — one human, one key, two callers. (The `UserCipherclerk`
    /// public key is derived before federation binding, so the `federation_id` argument does not
    /// affect it.)
    #[test]
    fn the_cipherclerk_pubkey_equals_the_seed_signer_identity() {
        let secret = [42u8; 32];
        let uid = 555_000_111u64;
        let bot_pubkey = UserCipherclerk::derive(&secret, uid, [0u8; 32])
            .public_key_hex()
            .to_string();
        let web_pubkey = TurnSigner::from_seed(seed_for(&secret, uid)).identity().0;
        assert_eq!(
            bot_pubkey, web_pubkey,
            "the in-chat cipherclerk and the Activity signer are ONE identity"
        );
    }

    /// The op token stays deterministic, per-user, and domain-separated from the signing seed
    /// after the extraction (the `http_server.rs` GW-4a gate depends on all three).
    #[test]
    fn op_token_is_deterministic_and_domain_separated() {
        let secret = [5u8; 32];
        assert_eq!(op_token(&secret, 1), op_token(&secret, 1));
        assert_ne!(op_token(&secret, 1), op_token(&secret, 2));
        assert_ne!(op_token(&secret, 1), op_token(&[8u8; 32], 1));
        assert_ne!(
            hex::decode(op_token(&secret, 1)).unwrap().as_slice(),
            seed_for(&secret, 1).as_slice()
        );
    }
}
