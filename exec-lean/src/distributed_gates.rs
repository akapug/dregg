//! The verified-Lean gate IMPLEMENTATIONS for the distributed coordination crates.
//!
//! `dregg-coord`, `dregg-captp`, `dregg-federation`, and `dregg-intent` are FFI-free: each defines a
//! `verified_gate` SEAM trait and routes its verified decisions through it. This module is the single
//! FFI boundary that implements those seams over `dregg-lean-ffi`. A native node calls
//! [`register_distributed_gates`] once at startup to install all four; an FFI-free target
//! (wasm / verifier-PD / pg) never depends on this crate, so the seams stay unregistered and the
//! native-Rust differential siblings decide — the structural replacement for the deleted
//! `no-lean-link` feature.

use dregg_captp::verified_gate::CaptpVerifiedGate;
use dregg_coord::verified_gate::{CoordVerifiedGate, Verdict2pc};
use dregg_federation::verified_gate::FederationVerifiedGate;
use dregg_intent::verified_gate::IntentVerifiedGate;

/// The Lean-backed implementation of every distributed coordination seam. A single zero-sized type
/// that delegates each gate method to its `dregg-lean-ffi` export.
#[derive(Clone, Copy, Debug, Default)]
pub struct LeanDistributedGate;

impl CoordVerifiedGate for LeanDistributedGate {
    fn distributed_exports_available(&self) -> bool {
        dregg_lean_ffi::distributed_exports_available()
    }
    fn happened_before(&self, wire: &str) -> Option<bool> {
        dregg_lean_ffi::verified_happened_before(wire).ok()
    }
    fn decide_2pc(&self, wire: &str) -> Option<Verdict2pc> {
        match dregg_lean_ffi::verified_2pc_decide(wire) {
            Ok(dregg_lean_ffi::Decision2pc::Commit) => Some(Verdict2pc::Commit),
            Ok(dregg_lean_ffi::Decision2pc::Abort) => Some(Verdict2pc::Abort),
            Ok(dregg_lean_ffi::Decision2pc::Pending) => Some(Verdict2pc::Pending),
            Err(_) => None,
        }
    }
    fn shared_budget(&self, wire: &str) -> Option<String> {
        dregg_lean_ffi::shadow_coord_shared_budget(wire).ok()
    }
}

impl CaptpVerifiedGate for LeanDistributedGate {
    fn distributed_exports_available(&self) -> bool {
        dregg_lean_ffi::distributed_exports_available()
    }
    fn handoff_non_amplifying(&self, wire: &str) -> Option<bool> {
        dregg_lean_ffi::verified_handoff_non_amplifying(wire).ok()
    }
    fn process_drop(&self, wire: &str) -> Option<String> {
        dregg_lean_ffi::shadow_captp_process_drop(wire).ok()
    }
    fn pipeline_resolve(&self, wire: &str) -> Option<String> {
        dregg_lean_ffi::shadow_captp_pipeline_resolve(wire).ok()
    }
}

impl FederationVerifiedGate for LeanDistributedGate {
    fn strand_admit_available(&self) -> bool {
        dregg_lean_ffi::strand_admit_available()
    }
    fn admits(&self, wire: &str) -> Option<bool> {
        dregg_lean_ffi::verified_admits(wire).ok()
    }
}

impl IntentVerifiedGate for LeanDistributedGate {
    fn record_kernel_step(&self, input: &str) -> Result<String, String> {
        dregg_lean_ffi::shadow_record_kernel_step(input)
    }
}

/// Install the verified-Lean gate into all four distributed coordination seams (call once at native
/// node startup). After this, `dregg-coord` / `dregg-captp` / `dregg-federation` / `dregg-intent`
/// route their verified decisions through the linked Lean archive; before it (and on every FFI-free
/// target) they use their native-Rust differential siblings.
pub fn register_distributed_gates() {
    dregg_coord::register_coord_verified_gate(Box::new(LeanDistributedGate));
    dregg_captp::register_captp_verified_gate(Box::new(LeanDistributedGate));
    dregg_federation::register_federation_verified_gate(Box::new(LeanDistributedGate));
    dregg_intent::register_intent_verified_gate(Box::new(LeanDistributedGate));
}
