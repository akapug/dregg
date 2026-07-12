//! THE HONEST BODY SEAM.
//!
//! This crate serves a grain's `WebSession` surface; it does NOT execute the
//! packaged app binary. The compute-tier `exec_workload` weld (running the
//! `.spk` `continue_command` inside a `Caged`/`MicroVm` jail — grain-jail /
//! TEE) is a separate future lane, exactly as `sandstorm-bridge`'s own crate
//! header names it. Rather than simulate that weld, the serving surface takes
//! a pluggable [`GrainBody`]:
//!
//! * [`NoBody`] — the fail-closed default. Every request that survives the
//!   capability gate is answered with a typed `503` refusal that NAMES the
//!   missing exec weld. Nothing is pretended.
//! * [`DemoNotesBody`] — an honest in-process body implementing the `WebSession`
//!   contract against the grain's REAL cell heap (it wraps the upstream
//!   [`NotesApp`] permission-gated notes store and adds a `/whoami` echo of
//!   the derived `X-Sandstorm-*` headers), so the whole
//!   serving + auth + custody + checkpoint loop is real end-to-end with a
//!   body that says what it is.
//!
//! A body only ever sees the [`BridgedRequest`] (identity/permission headers
//! already derived from the presented `dga1_` cap) and the grain's `/var`
//! [`Umem`]; the capability gate has already run in `HttpBridge::serve`.

use sandstorm_bridge::bridge::{BridgedRequest, GrainWorkload, HttpResponse, Method, NotesApp};
use sandstorm_bridge::cell::Umem;

/// Which body is mounted behind the serving surface — reported honestly in the
/// daemon status and the assurance ledger.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrainBodyKind {
    /// No execution body: every request refuses with [`NO_BODY_REFUSAL`].
    NoBody,
    /// The in-process demo body ([`DemoNotesBody`]) — real `WebSession` +
    /// `/var` semantics, NOT the packaged app.
    InProcessDemo,
}

impl GrainBodyKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            GrainBodyKind::NoBody => "no-body-fail-closed",
            GrainBodyKind::InProcessDemo => "in-process-demo",
        }
    }
}

/// The pluggable execution seam. A body is a [`GrainWorkload`] (the upstream
/// `WebSession` app contract) that also declares what it is. The future exec
/// weld mounts an OS-process body here without touching the serving surface.
pub trait GrainBody: GrainWorkload + Send + Sync {
    fn kind(&self) -> GrainBodyKind;
}

/// The typed refusal body [`NoBody`] answers every request with (HTTP 503).
pub const NO_BODY_REFUSAL: &str = concat!(
    "{\"refusal\":\"grain-serve.exec-weld-unavailable\",",
    "\"detail\":\"no execution body is mounted: the packaged app binary is never run by this daemon; ",
    "the compute-tier exec_workload weld (grain-jail / microVM) is a separate named lane\",",
    "\"app_executed\":false}"
);

/// Fail-closed default body: the exec weld is absent, so say so — with a
/// typed, machine-readable refusal — instead of serving anything.
pub struct NoBody;

impl GrainWorkload for NoBody {
    fn serve(&self, _req: &BridgedRequest, _var: &mut Umem) -> HttpResponse {
        HttpResponse {
            status: 503,
            body: NO_BODY_REFUSAL.as_bytes().to_vec(),
        }
    }
}

impl GrainBody for NoBody {
    fn kind(&self) -> GrainBodyKind {
        GrainBodyKind::NoBody
    }
}

/// The in-process demo body: the upstream permission-gated [`NotesApp`]
/// (GET needs `view`, POST/PUT/DELETE need `edit`, state persists in the real
/// `/var` umem) plus `GET /whoami`, which echoes the cap-derived
/// `X-Sandstorm-*` identity headers back as JSON so a caller can SEE the
/// identity/permission derivation this weld exists to carry.
pub struct DemoNotesBody;

impl GrainWorkload for DemoNotesBody {
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
        if req.method == Method::Get && req.path == "/whoami" {
            if !req.permissions().iter().any(|p| p == "view") {
                return HttpResponse::forbidden();
            }
            let header = |name: &str| req.headers.get(name).cloned().unwrap_or_default();
            let echo = serde_json::json!({
                "user_id": header("X-Sandstorm-User-Id"),
                "username": header("X-Sandstorm-Username"),
                "session_id": header("X-Sandstorm-Session-Id"),
                "permissions": req.permissions(),
            });
            return HttpResponse::ok(echo.to_string().into_bytes());
        }
        NotesApp.serve(req, var)
    }
}

impl GrainBody for DemoNotesBody {
    fn kind(&self) -> GrainBodyKind {
        GrainBodyKind::InProcessDemo
    }
}
