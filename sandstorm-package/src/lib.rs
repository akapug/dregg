//! Signed Sandstorm package format, independent of the hosting substrate.
//!
//! Parse and signature-verify an SPK before decoding its manifest. The parser
//! also retains the full typed archive tree for an executor to materialize.

pub mod capnp_wire;
pub mod manifest;
pub mod spk;

pub use manifest::{AppId, SpkManifest};
pub use spk::{Archive, File, FileContent, Spk, SpkBuilder, SpkError};
