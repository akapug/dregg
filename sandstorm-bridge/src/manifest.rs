//! Bread's hosting policy over the standalone signed SPK manifest parser.
//!
//! Format decoding and signature binding live in sandstorm-package. This
//! facade preserves Bread's existing SpkManifest::grain_spec() API while
//! keeping its Caged/MicroVm choice out of the package format crate.

use std::ops::{Deref, DerefMut};

use serde::{Deserialize, Serialize};

use crate::grain::{GrainSpec, SandboxTier};
use crate::spk::Spk;

pub use sandstorm_package::manifest::{
    Action, AppId, BridgeConfig, Command, Metadata, ParseError, Role,
};

/// A parsed signed package manifest with Bread's grain hosting conversion.
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct SpkManifest(pub sandstorm_package::manifest::SpkManifest);

impl std::fmt::Debug for SpkManifest {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, formatter)
    }
}

impl SpkManifest {
    pub fn from_json(json: &str) -> Result<Self, ParseError> {
        sandstorm_package::manifest::SpkManifest::from_json(json).map(Self)
    }

    pub fn from_spk(spk: &Spk) -> Result<Self, ParseError> {
        sandstorm_package::manifest::SpkManifest::from_spk(spk).map(Self)
    }

    pub fn from_capnp(bytes: &[u8]) -> Result<Self, ParseError> {
        sandstorm_package::manifest::SpkManifest::from_capnp(bytes).map(Self)
    }

    /// Convert signed package metadata into Bread's grain launch policy.
    pub fn grain_spec(&self) -> GrainSpec {
        let tier = if self.is_http_bridge() {
            SandboxTier::Caged
        } else {
            SandboxTier::MicroVm
        };
        GrainSpec {
            app_id: self.app_id.clone(),
            app_version: self.app_version,
            wake_argv: self.continue_command.argv.clone(),
            ingress_port: self.bridge_config.as_ref().and_then(|b| b.api_port),
            tier,
            declared_permissions: self.declared_permissions(),
        }
    }
}

impl Deref for SpkManifest {
    type Target = sandstorm_package::manifest::SpkManifest;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SpkManifest {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn http_bridge_manifest_routes_to_caged() {
        let manifest = SpkManifest::from_json(
            r#"{"app_id":"signed","app_title":"Web","app_version":1,
                 "continue_command":{"argv":["/sandstorm-http-bridge","8000","--","/start.sh"]},
                 "bridge_config":{"api_port":8000,"permissions":["view","edit"]}}"#,
        )
        .unwrap();
        let spec = manifest.grain_spec();
        assert_eq!(spec.tier, SandboxTier::Caged);
        assert_eq!(spec.ingress_port, Some(8000));
        assert_eq!(spec.declared_permissions, vec!["view", "edit"]);
    }

    #[test]
    fn raw_capnp_manifest_routes_to_microvm() {
        let manifest = SpkManifest::from_json(
            r#"{"app_id":"signed","app_title":"Raw","app_version":1,
                 "continue_command":{"argv":["/app/server"]}}"#,
        )
        .unwrap();
        let spec = manifest.grain_spec();
        assert_eq!(spec.tier, SandboxTier::MicroVm);
        assert_eq!(spec.ingress_port, None);
        assert!(spec.declared_permissions.is_empty());
    }

    #[test]
    fn facade_preserves_manifest_wire_and_debug_shape() {
        let json = r#"{"app_id":"signed","app_title":"Web","app_version":1,
                      "continue_command":{"argv":["/app/server"],"environ":[["PATH","/bin"]]}}"#;
        let manifest = SpkManifest::from_json(json).unwrap();
        let leaf = sandstorm_package::manifest::SpkManifest::from_json(json).unwrap();
        assert_eq!(
            serde_json::to_value(&manifest).unwrap(),
            serde_json::to_value(&leaf).unwrap()
        );
        assert_eq!(format!("{manifest:?}"), format!("{leaf:?}"));
        assert_eq!(manifest.continue_command.environ[0].1, "/bin");
    }
}
