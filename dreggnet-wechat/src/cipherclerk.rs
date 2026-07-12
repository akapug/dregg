//! **Per-WeChat-user derived dregg identity** — the faithful mirror of
//! `dreggnet-telegram/src/cipherclerk.rs` (itself the mirror of the discord bot's
//! `UserCipherclerk::derive`). A WeChat **OpenID** (the per-Official-Account opaque user handle)
//! becomes a deterministic 32-byte seed, fed to the canonical `AgentCipherclerk::from_key_bytes`
//! to produce a REAL Ed25519 signing identity; the [`dreggnet_offerings::DreggIdentity`] a
//! [`crate::WeChatFrontend`] attributes moves to is that key's public-key hex — the SAME kind of
//! handle every other frontend derives, just under a WeChat-scoped BLAKE3 domain:
//!
//! ```text
//! seed = BLAKE3_derive_key("dregg-wechat-v1", bot_secret || openid_utf8_bytes)
//! ```
//!
//! Cross-platform, by construction: the SAME primitive on every frontend, a per-platform domain so
//! a Discord user, a Telegram user, and a WeChat user never collide onto one dregg identity, and a
//! WeChat OpenID always re-derives the SAME dregg identity (reproducible custodial keys). Nothing
//! here is WeChat-transport-specific — it needs no access-token and no network.
//!
//! NOTE on the key material: a WeChat OpenID is a variable-length UTF-8 string (per-OA unique,
//! e.g. `"oGZUI0egBJY1zhBYw2KaXT;..."`), where the Telegram user id was a `u64`. We hash the raw
//! UTF-8 bytes, so any OpenID length is supported and two distinct OpenIDs never seed the same key.

use dregg_sdk::AgentCipherclerk;
use dreggnet_offerings::DreggIdentity;
use zeroize::Zeroizing;

/// The BLAKE3 derive-key domain for WeChat custodial seeds — the WeChat analogue of the telegram
/// frontend's `"dregg-telegram-bot-v1"` and the discord bot's `"dregg-discord-bot-v1"`. A distinct
/// domain per frontend keeps the platforms' user-id spaces from ever colliding onto one identity.
pub const WECHAT_SEED_DOMAIN: &str = "dregg-wechat-v1";

/// The deterministic 32-byte custodial seed for a WeChat OpenID — `seed =
/// BLAKE3_derive_key("dregg-wechat-v1", bot_secret || openid_utf8_bytes)`. This seed IS the Ed25519
/// secret handed to `AgentCipherclerk::from_key_bytes`, so the identity is reproducible (the same
/// shape as the telegram `seed_for`, a WeChat OpenID string in place of the Telegram u64).
pub fn seed_for(bot_secret: &[u8; 32], openid: &str) -> [u8; 32] {
    let mut input = Vec::with_capacity(32 + openid.len());
    input.extend_from_slice(bot_secret);
    input.extend_from_slice(openid.as_bytes());
    blake3::derive_key(WECHAT_SEED_DOMAIN, &input)
}

/// A deterministic per-WeChat-user cipherclerk handle — a real Ed25519 identity derived from the
/// bot secret + the WeChat OpenID. The mirror of the telegram `TelegramCipherclerk`.
pub struct WeChatCipherclerk {
    /// The canonical agent cipherclerk (Ed25519, deterministic from the seed).
    agent: AgentCipherclerk,
    /// Cached hex-encoded Ed25519 public key — the [`DreggIdentity`] handle.
    public_key_hex_cached: String,
}

impl WeChatCipherclerk {
    /// Derive the cclerk for `openid` under `bot_secret`. Deterministic and reproducible: the same
    /// inputs always yield the same Ed25519 identity.
    pub fn derive(bot_secret: &[u8; 32], openid: &str) -> Self {
        // The transient seed copy handed to `from_key_bytes` is wiped after construction (as the
        // telegram cclerk does).
        let secret = Zeroizing::new(seed_for(bot_secret, openid));
        let agent = AgentCipherclerk::from_key_bytes(secret);
        let public_key_hex_cached = hex::encode(agent.public_key().0);
        WeChatCipherclerk {
            agent,
            public_key_hex_cached,
        }
    }

    /// The user's Ed25519 public key as lowercase hex.
    pub fn public_key_hex(&self) -> &str {
        &self.public_key_hex_cached
    }

    /// The user's frontend-agnostic [`DreggIdentity`] (the public-key hex handle the core
    /// attributes moves to). The SAME actor → the SAME identity, on every frontend.
    pub fn identity(&self) -> DreggIdentity {
        DreggIdentity(self.public_key_hex_cached.clone())
    }

    /// The underlying agent cipherclerk — for a real deploy to actually SIGN a turn on the user's
    /// behalf (this crate only needs the public identity for attribution).
    pub fn agent(&self) -> &AgentCipherclerk {
        &self.agent
    }
}
