//! The production loader. This file is the artifact's ONLY consumer path.

/// The deployed descriptor, loaded from the emitted artifact — one author, on disk.
pub const DEPLOYED_JSON: &str = include_str!("../descriptors/by-name/canary.json");

pub fn descriptor_by_name(_n: &str) -> Option<&'static str> {
    Some(DEPLOYED_JSON)
}
