//! Parsing a Sandstorm app manifest → a [`GrainSpec`](crate::grain::GrainSpec).
//!
//! A Sandstorm app ships as a `.spk` package: an Ed25519-signed, xz-compressed
//! archive whose root holds the app's read-only files plus a Cap'n Proto-serialized
//! `Manifest` (schema: `sandstorm-io/sandstorm/src/sandstorm/package.capnp`). The
//! **app id** is the Crockford-base32 encoding of the package's signing public key,
//! so "which key signed this app" is intrinsic to its identity — a property dregg
//! reuses directly (see the plan, §App-catalog).
//!
//! ## Two real decode paths
//!
//! [`SpkManifest::from_spk`] reads the manifest the way the package actually carries
//! it. A real catalog `.spk` stores `sandstorm-manifest` as a Cap'n Proto `Manifest`
//! message; [`SpkManifest::from_capnp`] decodes that genuine wire (via
//! [`crate::capnp_wire`] against the `package.capnp` layout) — `appTitle`,
//! `appVersion`, `appMarketingVersion`, the `actions`, and the `continueCommand` argv.
//! A synthetic test package may instead store an equivalent JSON projection of the
//! same fields ([`SpkManifest::from_json`]); `from_spk` detects which and uses the
//! matching decoder. Either way the field shapes mirror `package.capnp`.
//!
//! `sandstorm-http-bridge` apps declare their bridge in one of two real forms: a
//! `bridgeConfig` block (carried in the JSON projection), or — the convention a real
//! catalog package uses — the `/sandstorm-http-bridge <port>` invocation in the
//! `continueCommand` argv plus a separate `sandstorm-http-bridge-config` file. The
//! capnp decoder recognizes the latter, recovering the ingress port from the argv.

use serde::{Deserialize, Serialize};

use crate::capnp_wire::{self, Message, Struct};
use crate::grain::{GrainSpec, SandboxTier};
use crate::spk::Spk;

/// A Sandstorm app id — the Crockford-base32 of the package's Ed25519 signing key.
///
/// In Sandstorm this is intrinsic (the key *is* the identity). On dregg it doubles
/// as the **issuer** of the app's asset-well / publisher identity: "this grain runs
/// app signed by key K" is a provable fact, not a registry claim.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AppId(pub String);

/// A Cap'n Proto `Command` — how the supervisor launches a process inside the grain
/// sandbox (`package.capnp:Manifest.Command`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Command {
    /// `argv[0]` and friends — the executable + args run as PID 1 in the grain's
    /// PID namespace. (Sandstorm's `argv`; `deprecatedExecutablePath` folded in.)
    #[serde(default)]
    pub argv: Vec<String>,
    /// Environment variables set for the process.
    #[serde(default)]
    pub environ: Vec<(String, String)>,
}

/// A Sandstorm `Action` — a way to *create* a fresh grain (`Manifest.actions`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Action {
    /// The human "New <noun>" label (Sandstorm's `nounPhrase`).
    #[serde(default)]
    pub noun_phrase: String,
    /// The command run to initialize a new grain.
    pub command: Command,
}

/// The `bridgeConfig` of an `sandstorm-http-bridge` app — the legacy-HTTP apps
/// (Etherpad, Wekan, …) that speak plain HTTP, which the bridge translates to/from
/// the `WebSession` Cap'n Proto API. Carries the app's permission/role model and
/// its powerbox API surface.
#[derive(Clone, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct BridgeConfig {
    /// The localhost port the app's HTTP server listens on inside the sandbox; the
    /// bridge proxies the grain session to it. On dregg this is the workload's
    /// ingress port the gateway routes to (see the plan, §Verifiable-serving).
    #[serde(default)]
    pub api_port: Option<u16>,
    /// The app's declared permissions (the `viewInfo.permissions`) — the named
    /// rights a sharing role may carry. These become the **effect facets** a dregg
    /// cap can be attenuated to (see [`crate::webauth_rail`]).
    #[serde(default)]
    pub permissions: Vec<String>,
    /// The sharing roles (`viewInfo.roles`), each a named bundle of `permissions`.
    #[serde(default)]
    pub roles: Vec<Role>,
}

/// A Sandstorm sharing role — a named subset of the app's permissions (e.g.
/// "editor" = {edit, view}, "viewer" = {view}). Maps to a *named attenuation* of
/// the grain's root cap.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Role {
    pub title: String,
    /// Which of [`BridgeConfig::permissions`] this role grants.
    #[serde(default)]
    pub permissions: Vec<String>,
}

/// The app metadata block (`Manifest.metadata`) — catalog-facing fields.
#[derive(Clone, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct Metadata {
    #[serde(default)]
    pub author: String,
    #[serde(default)]
    pub website: String,
    /// The app market categories (productivity, communication, …).
    #[serde(default)]
    pub categories: Vec<String>,
    #[serde(default)]
    pub short_description: String,
}

/// A parsed Sandstorm app manifest — the fields the dregg integration consumes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpkManifest {
    /// The signing-key-derived app id.
    pub app_id: AppId,
    /// `Manifest.appTitle` (the default-locale text).
    pub app_title: String,
    /// `Manifest.appVersion` — a monotone integer the package signs.
    pub app_version: u32,
    /// `Manifest.appMarketingVersion` — the human "1.4.2" string.
    #[serde(default)]
    pub marketing_version: String,
    /// `Manifest.actions` — how to create a new grain.
    #[serde(default)]
    pub actions: Vec<Action>,
    /// `Manifest.continueCommand` — how to restart (wake) an existing grain.
    pub continue_command: Command,
    /// Present iff this is an `sandstorm-http-bridge` (legacy-HTTP) app.
    #[serde(default)]
    pub bridge_config: Option<BridgeConfig>,
    #[serde(default)]
    pub metadata: Metadata,
}

/// Failure to parse a manifest projection.
#[derive(Debug)]
pub struct ParseError(pub String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "manifest parse error: {}", self.0)
    }
}
impl std::error::Error for ParseError {}

impl SpkManifest {
    /// Parse the JSON projection of a Sandstorm `Manifest`. (Production: decode the
    /// real Cap'n Proto `Manifest` out of the `.spk`; the field shapes match.)
    pub fn from_json(s: &str) -> Result<Self, ParseError> {
        serde_json::from_str(s).map_err(|e| ParseError(e.to_string()))
    }

    /// Decode the manifest out of a parsed, signature-verified [`Spk`]: read the
    /// `sandstorm-manifest` file from the archive and parse it (the real capnp
    /// `Manifest` message a catalog package carries, or a JSON projection a synthetic
    /// package may use — detected from the bytes), **overriding the app id with the
    /// package's signing key** (the App ID is intrinsic to the signature — the manifest
    /// body never gets to assert its own identity).
    pub fn from_spk(spk: &Spk) -> Result<Self, ParseError> {
        let bytes = spk
            .manifest_bytes()
            .ok_or_else(|| ParseError("no sandstorm-manifest in package archive".into()))?;
        let mut m = if looks_like_json(bytes) {
            let json = std::str::from_utf8(bytes)
                .map_err(|_| ParseError("manifest is not utf-8".into()))?;
            Self::from_json(json)?
        } else {
            Self::from_capnp(bytes)?
        };
        m.app_id = spk.app_id();
        Ok(m)
    }

    /// Decode a real Cap'n Proto `Manifest` message (`package.capnp:Manifest`). The
    /// `app_id` is left empty — [`from_spk`](Self::from_spk) overrides it with the
    /// intrinsic signing-key identity.
    pub fn from_capnp(bytes: &[u8]) -> Result<Self, ParseError> {
        let (msg, _) = Message::parse_prefix(bytes).map_err(|e| ParseError(e.to_string()))?;
        let root = msg.root().map_err(|e| ParseError(e.to_string()))?;
        // Manifest layout (ordinal-allocated): data — minApiVersion@0(b0),
        // maxApiVersion@1(b4), appVersion@4(b8), minUpgradableAppVersion@5(b12);
        // pointers — actions@2=slot0, continueCommand@3=slot1, appMarketingVersion@6=2,
        // appTitle@7=3, metadata@8=4.
        let app_version = root.get_u32(8);
        let app_title = read_localized(&root, 3).map_err(|e| ParseError(e.to_string()))?;
        let marketing_version = read_localized(&root, 2).map_err(|e| ParseError(e.to_string()))?;
        let continue_command =
            read_command(root.get_struct(1).map_err(|e| ParseError(e.to_string()))?)
                .map_err(|e| ParseError(e.to_string()))?;
        let actions = read_actions(&root).map_err(|e| ParseError(e.to_string()))?;
        // A catalog http-bridge app declares its bridge via the `/sandstorm-http-bridge
        // <port>` invocation (the bridgeConfig itself lives in a separate file, default
        // here → no declared permissions); recover the ingress port from the argv.
        let bridge_config = bridge_config_from_argv(&continue_command.argv);
        Ok(SpkManifest {
            app_id: AppId(String::new()),
            app_title,
            app_version,
            marketing_version,
            actions,
            continue_command,
            bridge_config,
            metadata: Metadata::default(),
        })
    }

    /// Whether the app speaks legacy HTTP through `sandstorm-http-bridge`.
    pub fn is_http_bridge(&self) -> bool {
        self.bridge_config.is_some()
    }

    /// The full set of named permissions this app declares (the universe a sharing
    /// role — and thus a dregg cap — can be attenuated within). Empty for a raw
    /// Cap'n Proto app with no `bridgeConfig`.
    pub fn declared_permissions(&self) -> Vec<String> {
        self.bridge_config
            .as_ref()
            .map(|b| b.permissions.clone())
            .unwrap_or_default()
    }

    /// Derive the [`GrainSpec`] this manifest implies: the wake command, the ingress
    /// port (for http-bridge apps), and the **sandbox tier** the grain demands.
    ///
    /// A Sandstorm grain *always* runs untrusted third-party code under the
    /// supervisor's namespaces+seccomp jail. dregg's faithful analog is the
    /// strong-isolation path: an http-bridge web app routes to [`SandboxTier::Caged`]
    /// (native + seccomp-bpf + Landlock — the closest match to the Sandstorm
    /// supervisor), and a raw/arbitrary-binary app to [`SandboxTier::MicroVm`]
    /// (a per-grain microVM — strictly stronger than the shared-kernel supervisor).
    /// We never route a grain to an in-process wasm tier: that would *downgrade* the
    /// isolation Sandstorm assumes.
    pub fn grain_spec(&self) -> GrainSpec {
        let tier = if self.is_http_bridge() {
            SandboxTier::Caged
        } else {
            SandboxTier::MicroVm
        };
        let argv = self.continue_command.argv.clone();
        let ingress_port = self.bridge_config.as_ref().and_then(|b| b.api_port);
        GrainSpec {
            app_id: self.app_id.clone(),
            app_version: self.app_version,
            wake_argv: argv,
            ingress_port,
            tier,
            declared_permissions: self.declared_permissions(),
        }
    }
}

/// Heuristic: a JSON manifest projection begins (after whitespace) with `{`; a real
/// capnp `Manifest` message begins with a little-endian segment table (a small count).
fn looks_like_json(bytes: &[u8]) -> bool {
    bytes
        .iter()
        .find(|b| !b.is_ascii_whitespace())
        .map(|b| *b == b'{')
        .unwrap_or(false)
}

/// Read a `Util.LocalizedText` at pointer `slot`, returning its `defaultText` (`""`
/// if the field is absent).
fn read_localized(s: &Struct<'_, '_>, slot: usize) -> Result<String, capnp_wire::CapnpError> {
    match s.get_struct(slot)? {
        Some(lt) => lt.get_text(0),
        None => Ok(String::new()),
    }
}

/// Read a `Manifest.Command` (or `None` → an empty command). In `package.capnp`,
/// `deprecatedExecutablePath`, `argv`, and `environ` occupy pointer slots 0, 1,
/// and 2 respectively; each `Util.KeyValue` in `environ` has `key` and `value`
/// in pointer slots 0 and 1. The deprecated path, when present, is prepended
/// to `argv`, as the upstream schema specifies.
fn read_command(cmd: Option<Struct<'_, '_>>) -> Result<Command, capnp_wire::CapnpError> {
    let Some(cmd) = cmd else {
        return Ok(Command {
            argv: Vec::new(),
            environ: Vec::new(),
        });
    };
    let mut argv = match cmd.get_list(1)? {
        Some(list) => list.text_list()?,
        None => Vec::new(),
    };
    let deprecated_executable_path = cmd.get_text(0)?;
    if !deprecated_executable_path.is_empty() {
        argv.insert(0, deprecated_executable_path);
    }
    let environ = match cmd.get_list(2)? {
        Some(list) => list
            .structs()?
            .into_iter()
            .map(|entry| Ok((entry.get_text(0)?, entry.get_text(1)?)))
            .collect::<Result<Vec<_>, capnp_wire::CapnpError>>()?,
        None => Vec::new(),
    };
    Ok(Command { argv, environ })
}

/// Read `Manifest.actions` (pointer slot 0). Each `Action`'s `command` is pointer slot
/// 1 and its `nounPhrase` (`LocalizedText`) pointer slot 4.
fn read_actions(root: &Struct<'_, '_>) -> Result<Vec<Action>, capnp_wire::CapnpError> {
    let list = match root.get_list(0)? {
        Some(l) => l,
        None => return Ok(Vec::new()),
    };
    let mut out = Vec::new();
    for a in list.structs()? {
        let command = read_command(a.get_struct(1)?)?;
        let noun_phrase = read_localized(&a, 4)?;
        out.push(Action {
            noun_phrase,
            command,
        });
    }
    Ok(out)
}

/// Recover a `BridgeConfig` from a `continueCommand` argv: an app launched via
/// `/sandstorm-http-bridge <port> -- …` is an http-bridge app whose ingress port is the
/// argument after the bridge binary. (The bridge's permission/role model lives in the
/// separate `sandstorm-http-bridge-config` file; recovered as empty here.) `None` for a
/// raw Cap'n Proto app.
fn bridge_config_from_argv(argv: &[String]) -> Option<BridgeConfig> {
    let idx = argv
        .iter()
        .position(|a| a == "/sandstorm-http-bridge" || a.ends_with("/sandstorm-http-bridge"))?;
    let api_port = argv.get(idx + 1).and_then(|p| p.parse::<u16>().ok());
    Some(BridgeConfig {
        api_port,
        permissions: Vec::new(),
        roles: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_real_schema_command_environment_and_deprecated_executable() {
        // capnp encode against Sandstorm package.capnp and util.capnp at
        // a97cf3ee19d3bf2761cd597583ca5d998de425d8 generated this framed
        // Manifest message. It carries both action and continue commands;
        // the latter has all three Command pointer fields populated.
        let hex = concat!(
            "000000003e00000000000000020005000000000000000000070000000000000011000000370000006800000000000300",
            "0000000000000000cc000000000002000000000000000000040000000100050000000000000000000000000000000000",
            "0c0000000000030000000000000000000000000000000000340000000000020000000000000000000500000016000000",
            "11000000170000000500000042000000050000002a0000002f616374696f6e00696e6974000000000400000000000200",
            "050000005a0000000900000022000000414354494f4e5f454e560000000000006e657700000000000500000032000000",
            "00000000000000007468696e67000000090000006a0000000d0000002600000035000000270000002f6c65676163792d",
            "65786563000000000d000000ba000000150000002a000000150000001a00000015000000520000002f73616e6473746f",
            "726d2d687474702d627269646765000038303030000000002d2d0000000000002f73746172742e736800000000000000",
            "08000000000002000d0000002a0000000d00000072000000110000004a00000015000000420000005041544800000000",
            "2f7573722f62696e3a2f62696e0000004150505f4d4f4445000000000000000073746167696e6700050000006a000000",
            "0000000000000000436f6d6d616e64205769726500000000",
        );
        let bytes = hex
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect::<Vec<_>>();
        let manifest = SpkManifest::from_capnp(&bytes).unwrap();
        assert_eq!(manifest.app_title, "Command Wire");
        assert_eq!(manifest.app_version, 7);
        assert_eq!(
            manifest.continue_command.argv,
            [
                "/legacy-exec",
                "/sandstorm-http-bridge",
                "8000",
                "--",
                "/start.sh"
            ]
        );
        assert_eq!(
            manifest.continue_command.environ,
            [
                ("PATH".into(), "/usr/bin:/bin".into()),
                ("APP_MODE".into(), "staging".into())
            ]
        );
        assert_eq!(manifest.actions.len(), 1);
        assert_eq!(manifest.actions[0].command.argv, ["/action", "init"]);
        assert_eq!(
            manifest.actions[0].command.environ,
            [("ACTION_ENV".into(), "new".into())]
        );
    }

    /// A trimmed Etherpad-shaped manifest (an http-bridge app with an editor/viewer
    /// role model) — the kind of `.spk` the catalog is full of.
    fn etherpad_json() -> &'static str {
        r#"{
          "app_id": "vfnwptfn02ty21w715snyyczw0nqxkv3jvawcsk4180s",
          "app_title": "Etherpad",
          "app_version": 33,
          "marketing_version": "1.8.18",
          "actions": [
            { "noun_phrase": "pad", "command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] } }
          ],
          "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
          "bridge_config": {
            "api_port": 8000,
            "permissions": ["view", "edit"],
            "roles": [
              { "title": "editor", "permissions": ["view", "edit"] },
              { "title": "viewer", "permissions": ["view"] }
            ]
          },
          "metadata": {
            "author": "The Etherpad Foundation",
            "categories": ["office", "productivity"],
            "short_description": "Collaborative document editor"
          }
        }"#
    }

    #[test]
    fn parses_an_http_bridge_app() {
        let m = SpkManifest::from_json(etherpad_json()).unwrap();
        assert_eq!(m.app_title, "Etherpad");
        assert_eq!(m.app_version, 33);
        assert!(m.is_http_bridge());
        assert_eq!(m.declared_permissions(), vec!["view", "edit"]);
    }

    #[test]
    fn http_bridge_app_routes_to_caged_with_ingress() {
        let spec = SpkManifest::from_json(etherpad_json())
            .unwrap()
            .grain_spec();
        // A web app under the supervisor's jail → the Caged (seccomp+landlock) tier.
        assert_eq!(spec.tier, SandboxTier::Caged);
        assert_eq!(spec.ingress_port, Some(8000));
        assert_eq!(spec.declared_permissions, vec!["view", "edit"]);
    }

    #[test]
    fn raw_capnp_app_routes_to_microvm() {
        // No bridge_config => a raw Cap'n Proto app => the strongest tier.
        let json = r#"{
          "app_id": "z9q6whrf",
          "app_title": "RawApp",
          "app_version": 1,
          "continue_command": { "argv": ["/app/server"] }
        }"#;
        let spec = SpkManifest::from_json(json).unwrap().grain_spec();
        assert_eq!(spec.tier, SandboxTier::MicroVm);
        assert_eq!(spec.ingress_port, None);
        assert!(spec.declared_permissions.is_empty());
    }
}
