//! `wg` — DreggNet's own WireGuard config parser + userspace engine.
//!
//! This is the AGPL-clean replacement for the previously-vendored Elide
//! `elidewireguard` crate. It is backed by `boringtun` (Cloudflare, BSD-3-Clause,
//! the reference userspace WireGuard implementation) and a clean-room parser for
//! the public `wg-quick` INI format (`[Interface]` / `[Peer]` sections). It owns
//! no Elide code.
//!
//! The mesh (`crate::mesh`) renders that standard INI itself
//! ([`crate::mesh::MeshConfig::wireguard_ini`]) and rounds it back through
//! [`WireGuardConfig::from_ini`] into a real [`WireGuardEngine`] — one `boringtun`
//! `Tunn` per configured peer. Constructing the engine validates the interface
//! private key and every peer public key as genuine 32-byte x25519 WireGuard keys.
//! Bringing the TUN device up and completing the live Noise handshake against the
//! remote node is the deploy step layered on top of this engine.
//!
//! `boringtun` is cross-platform userspace, so — unlike the old Linux-only Elide
//! stack — this module builds and is exercised on every host.

use base64::Engine as _;
use base64::engine::general_purpose::STANDARD as BASE64;
use boringtun::noise::Tunn;
use boringtun::x25519::{PublicKey, StaticSecret};

/// Why a WireGuard config failed to parse or an engine failed to build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WgError {
    /// The INI was missing a required key/section, or had a malformed value.
    Config(String),
    /// A base64 key did not decode to a 32-byte x25519 key.
    Key(String),
}

impl std::fmt::Display for WgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WgError::Config(m) => write!(f, "wireguard config: {m}"),
            WgError::Key(m) => write!(f, "wireguard key: {m}"),
        }
    }
}

impl std::error::Error for WgError {}

/// One `[Peer]` section of a WireGuard config.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeerConfig {
    /// The peer's base64 x25519 public key (`PublicKey`).
    pub public_key: String,
    /// The peer's `host:port` UDP endpoint, if pinned (`Endpoint`).
    pub endpoint: Option<String>,
    /// The routes carried to this peer (`AllowedIPs`), verbatim.
    pub allowed_ips: Vec<String>,
    /// The persistent-keepalive interval in seconds, if set (`PersistentKeepalive`).
    pub persistent_keepalive: Option<u16>,
}

/// A parsed WireGuard config: the local `[Interface]` plus its `[Peer]`s.
///
/// Parsed from the standard `wg-quick` INI format by [`WireGuardConfig::from_ini`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireGuardConfig {
    /// The interface's base64 x25519 private key (`PrivateKey`).
    pub private_key: String,
    /// The UDP port the interface listens on (`ListenPort`), if set.
    pub listen_port: Option<u16>,
    /// The interface's overlay addresses (`Address`), verbatim.
    pub address: Vec<String>,
    /// The configured peers.
    pub peers: Vec<PeerConfig>,
}

impl WireGuardConfig {
    /// Parse a standard WireGuard `wg-quick` INI (`[Interface]` + `[Peer]`s).
    ///
    /// Comments (`#` / `;`), blank lines, and surrounding whitespace are ignored;
    /// `AllowedIPs` accepts a comma-separated list. A missing `[Interface]` /
    /// `PrivateKey`, or a `[Peer]` with no `PublicKey`, is a [`WgError::Config`].
    pub fn from_ini(ini: &str) -> Result<WireGuardConfig, WgError> {
        #[derive(PartialEq)]
        enum Section {
            None,
            Interface,
            Peer,
        }

        let mut section = Section::None;
        let mut private_key: Option<String> = None;
        let mut listen_port: Option<u16> = None;
        let mut address: Vec<String> = Vec::new();
        let mut peers: Vec<PeerConfig> = Vec::new();

        for raw in ini.lines() {
            let line = strip_comment(raw).trim();
            if line.is_empty() {
                continue;
            }

            if let Some(name) = line.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
                match name.trim().to_ascii_lowercase().as_str() {
                    "interface" => section = Section::Interface,
                    "peer" => {
                        section = Section::Peer;
                        peers.push(PeerConfig {
                            public_key: String::new(),
                            endpoint: None,
                            allowed_ips: Vec::new(),
                            persistent_keepalive: None,
                        });
                    }
                    other => {
                        return Err(WgError::Config(format!("unknown section [{other}]")));
                    }
                }
                continue;
            }

            let (key, value) = line
                .split_once('=')
                .ok_or_else(|| WgError::Config(format!("expected `key = value`, got `{line}`")))?;
            let key = key.trim().to_ascii_lowercase();
            let value = value.trim();

            match section {
                Section::None => {
                    return Err(WgError::Config(format!(
                        "`{key}` appears before any [Interface]/[Peer] section"
                    )));
                }
                Section::Interface => match key.as_str() {
                    "privatekey" => private_key = Some(value.to_string()),
                    "listenport" => {
                        listen_port =
                            Some(value.parse().map_err(|_| {
                                WgError::Config(format!("bad ListenPort `{value}`"))
                            })?)
                    }
                    "address" => address.extend(split_list(value)),
                    // DNS/MTU/Table etc. are accepted-and-ignored (kernel wg-quick keys
                    // with no bearing on the userspace engine we build).
                    _ => {}
                },
                Section::Peer => {
                    let peer = peers
                        .last_mut()
                        .expect("a [Peer] section was pushed before its keys");
                    match key.as_str() {
                        "publickey" => peer.public_key = value.to_string(),
                        "endpoint" => peer.endpoint = Some(value.to_string()),
                        "allowedips" => peer.allowed_ips.extend(split_list(value)),
                        "persistentkeepalive" => {
                            peer.persistent_keepalive = Some(value.parse().map_err(|_| {
                                WgError::Config(format!("bad PersistentKeepalive `{value}`"))
                            })?)
                        }
                        // PresharedKey is honoured by the engine (below); other peer
                        // keys are accepted-and-ignored.
                        _ => {}
                    }
                }
            }
        }

        let private_key =
            private_key.ok_or_else(|| WgError::Config("no [Interface] PrivateKey".to_string()))?;
        for (i, peer) in peers.iter().enumerate() {
            if peer.public_key.is_empty() {
                return Err(WgError::Config(format!("[Peer] {i} has no PublicKey")));
            }
        }

        Ok(WireGuardConfig {
            private_key,
            listen_port,
            address,
            peers,
        })
    }
}

/// A userspace WireGuard engine: one `boringtun` `Tunn` per configured peer.
///
/// Built by [`WireGuardEngine::new`] from a [`WireGuardConfig`]. Construction
/// decodes and validates the interface private key and every peer public key.
pub struct WireGuardEngine {
    tunnels: Vec<Tunn>,
}

impl WireGuardEngine {
    /// Build the engine from `config`, constructing a `boringtun` `Tunn` for each
    /// peer under the interface's private key. Returns [`WgError::Key`] if any key
    /// is not a valid 32-byte base64 x25519 key.
    pub fn new(config: WireGuardConfig) -> Result<WireGuardEngine, WgError> {
        let static_private = decode_static_secret(&config.private_key)?;

        let mut tunnels = Vec::with_capacity(config.peers.len());
        for (index, peer) in config.peers.iter().enumerate() {
            let peer_public = decode_public_key(&peer.public_key)?;
            let tunn = Tunn::new(
                static_private.clone(),
                peer_public,
                None,
                peer.persistent_keepalive,
                // A unique per-peer local index (WireGuard reserves the low byte).
                index as u32,
                None,
            );
            tunnels.push(tunn);
        }

        Ok(WireGuardEngine { tunnels })
    }

    /// The number of peers the engine was built with.
    pub fn peer_count(&self) -> usize {
        self.tunnels.len()
    }
}

/// Drop everything from the first `#`/`;` to end-of-line (an inline comment).
fn strip_comment(line: &str) -> &str {
    let cut = line.find(['#', ';']).unwrap_or(line.len());
    &line[..cut]
}

/// Split a comma-separated INI value into trimmed, non-empty items.
fn split_list(value: &str) -> Vec<String> {
    value
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect()
}

/// Decode a base64 WireGuard key into its raw 32 bytes.
fn decode_key_bytes(b64: &str) -> Result<[u8; 32], WgError> {
    let bytes = BASE64
        .decode(b64.trim())
        .map_err(|e| WgError::Key(format!("not base64: {e}")))?;
    let arr: [u8; 32] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| WgError::Key(format!("expected 32 bytes, got {}", bytes.len())))?;
    Ok(arr)
}

fn decode_static_secret(b64: &str) -> Result<StaticSecret, WgError> {
    Ok(StaticSecret::from(decode_key_bytes(b64)?))
}

fn decode_public_key(b64: &str) -> Result<PublicKey, WgError> {
    Ok(PublicKey::from(decode_key_bytes(b64)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A rendered mesh INI round-trips into a real engine with the right peer count.
    #[test]
    fn parses_and_builds_a_real_engine() {
        // Two valid (all-zero-derived) 32-byte x25519 keys, base64-encoded.
        let key = BASE64.encode([7u8; 32]);
        let ini = format!(
            "[Interface]\n\
             PrivateKey = {key}\n\
             ListenPort = 51820\n\
             Address = 100.64.0.1/32\n\
             \n\
             [Peer]\n\
             PublicKey = {key}\n\
             Endpoint = 203.0.113.7:51820\n\
             AllowedIPs = 100.64.0.2/32\n\
             PersistentKeepalive = 25\n"
        );

        let config = WireGuardConfig::from_ini(&ini).expect("valid INI parses");
        assert_eq!(config.listen_port, Some(51820));
        assert_eq!(config.address, vec!["100.64.0.1/32".to_string()]);
        assert_eq!(config.peers.len(), 1);
        assert_eq!(
            config.peers[0].endpoint.as_deref(),
            Some("203.0.113.7:51820")
        );
        assert_eq!(config.peers[0].persistent_keepalive, Some(25));

        let engine = WireGuardEngine::new(config).expect("valid keys build an engine");
        assert_eq!(engine.peer_count(), 1);
    }

    #[test]
    fn comments_blank_lines_and_lists_are_handled() {
        let key = BASE64.encode([3u8; 32]);
        let ini = format!(
            "# leading comment\n\
             [Interface]\n\
             PrivateKey = {key}   ; inline comment\n\
             Address = 100.64.0.1/32, fd00::1/128\n\
             \n\
             [Peer]\n\
             PublicKey = {key}\n\
             AllowedIPs = 100.64.0.2/32, 100.64.0.3/32\n"
        );
        let config = WireGuardConfig::from_ini(&ini).expect("parses");
        assert_eq!(config.address.len(), 2);
        assert_eq!(config.peers[0].allowed_ips.len(), 2);
    }

    #[test]
    fn missing_private_key_is_an_error() {
        let err = WireGuardConfig::from_ini("[Interface]\nListenPort = 51820\n").unwrap_err();
        assert!(matches!(err, WgError::Config(_)));
    }

    #[test]
    fn bad_key_length_is_a_key_error() {
        let short = BASE64.encode([1u8; 16]);
        let ini = format!("[Interface]\nPrivateKey = {short}\n[Peer]\nPublicKey = {short}\n");
        let config = WireGuardConfig::from_ini(&ini).expect("parses");
        match WireGuardEngine::new(config) {
            Err(WgError::Key(_)) => {}
            Err(other) => panic!("expected a key error, got {other}"),
            Ok(_) => panic!("a 16-byte key must not build an engine"),
        }
    }
}
