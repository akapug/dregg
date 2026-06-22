//! The verified-Lean gate SEAM for `dregg-captp`.
//!
//! `dregg-captp` is FFI-free: it builds the wire encodings for its three verified decisions
//! (handoff non-amplification, process-drop GC verdict, pipeline FIFO resolve) and routes them
//! through this seam, never calling `dregg-lean-ffi` directly. A native node installs the
//! Lean-backed implementation once at startup (`dregg-exec-lean` provides it); a wasm / verifier-PD
//! / pg build never registers one, so every gate query returns `None` and the native-Rust lattice /
//! FIFO sibling decides — exactly the behavior the deleted `no-lean-link` feature used to compile in.

use std::sync::OnceLock;

/// The verified-Lean CapTP gate. Implemented by `dregg-exec-lean` (the single FFI boundary) and
/// injected on a native node; absent (⇒ `gate()` is `None`) on FFI-free targets.
///
/// Each method returns `None` when the verified gate is unavailable (archive not linked / export
/// absent / wire error), so the caller falls back to the native Rust decision.
pub trait CaptpVerifiedGate: Send + Sync {
    /// Whether the verified distributed-exports module is linked and queryable.
    fn distributed_exports_available(&self) -> bool;
    /// Decide §6 handoff non-amplification over the wire (`"h=…;g=…;he=…;ge=…"`).
    fn handoff_non_amplifying(&self, wire: &str) -> Option<bool>;
    /// Decide a `process_drop` GC verdict; returns the reply wire (`"S=<tag>;t=…"`) for the caller
    /// to parse, or `None` if unavailable.
    fn process_drop(&self, wire: &str) -> Option<String>;
    /// Resolve a pipeline drain order; returns the reply wire (`"D=…;q=…"`) for the caller to
    /// parse, or `None` if unavailable.
    fn pipeline_resolve(&self, wire: &str) -> Option<String>;
}

static GATE: OnceLock<Box<dyn CaptpVerifiedGate>> = OnceLock::new();

/// Install the verified-Lean CapTP gate (call once at node startup). A second call is a no-op.
pub fn register_captp_verified_gate(gate: Box<dyn CaptpVerifiedGate>) {
    let _ = GATE.set(gate);
}

/// The installed gate, or `None` when none is registered (every FFI-free target / pre-registration).
pub(crate) fn gate() -> Option<&'static dyn CaptpVerifiedGate> {
    GATE.get().map(|b| b.as_ref())
}
