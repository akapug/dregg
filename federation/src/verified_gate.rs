//! The verified-Lean gate SEAM for `dregg-federation`.
//!
//! `dregg-federation` is FFI-free: the F-4 hybrid strand-admission gate builds its wire encoding
//! (`StrandAdmission.encodeAdmitWire`) and routes it through this seam, never calling
//! `dregg-lean-ffi` directly. A native node installs the Lean-backed implementation once at startup
//! (`dregg-exec-lean` provides it); a wasm / verifier-PD / pg build never registers one, so the
//! query returns `None` and the pure-Rust `admitted_rust` differential sibling decides — exactly the
//! behavior the deleted `no-lean-link` feature used to compile in.

use std::sync::OnceLock;

/// The verified-Lean federation gate. Implemented by `dregg-exec-lean` (the single FFI boundary)
/// and injected on a native node; absent (⇒ `gate()` is `None`) on FFI-free targets.
pub trait FederationVerifiedGate: Send + Sync {
    /// Whether the verified `dregg_strand_admit` export is linked and queryable.
    fn strand_admit_available(&self) -> bool;
    /// Decide F-4 strand admission over the wire (`"N=…;m=…;S=…;V=…;Bo=…;q=…"`). Returns
    /// `Some(verdict)` (a malformed wire decodes fail-closed to `Some(false)` inside the impl), or
    /// `None` if the archive lacks the export (⇒ caller falls back to `admitted_rust`).
    fn admits(&self, wire: &str) -> Option<bool>;
}

static GATE: OnceLock<Box<dyn FederationVerifiedGate>> = OnceLock::new();

/// Install the verified-Lean federation gate (call once at node startup). A second call is a no-op.
pub fn register_federation_verified_gate(gate: Box<dyn FederationVerifiedGate>) {
    let _ = GATE.set(gate);
}

/// The installed gate, or `None` when none is registered (every FFI-free target / pre-registration).
pub(crate) fn gate() -> Option<&'static dyn FederationVerifiedGate> {
    GATE.get().map(|b| b.as_ref())
}
