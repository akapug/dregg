//! HTTP surface for an [`AffordanceSurface`] — the deos app's cap-gated
//! verified-turn affordances, served + fired over HTTP.
//!
//! `docs/deos/DEOS-APPS.md` (§"the deos app model"): the affordance-fire gate is
//! the SAME proof/cap check, pointed at the affordance's `required ⊆ held`
//! ([`dregg_cell::is_attenuation`]); per-viewer projection means an agent sees only
//! its authorized affordances. This module mounts that, composing the framework's
//! OWN pieces:
//!
//! - `GET {prefix}/descriptor` — the anti-drift [`crate::affordance::SurfaceDescriptor`]
//!   (the full surface; what [`crate::webgen`] also renders to JS).
//! - `GET {prefix}/projected` — the **per-viewer projection**: only the affordances
//!   the requester's held authority authorizes (`required ⊆ held`). Two viewers with
//!   different held rights get DIFFERENT element sets over the SAME surface.
//! - `POST {prefix}/fire/{name}` — **fire** the named affordance: the cap gate runs
//!   FIRST (`is_attenuation`); on pass, the real effect is executed as a verified
//!   turn through the framework's [`EmbeddedExecutor`] and the executor's OWN
//!   [`dregg_turn::TurnReceipt`] is returned. Unauthorized ⇒ 403, NOTHING submitted
//!   (anti-ghost).
//!
//! ## The held-rights resolver (the proof/cap boundary)
//!
//! The held authority a request carries is resolved by a [`HeldRightsResolver`].
//! The gate itself is unconditional and REAL — `is_attenuation(held, required)`,
//! the proven lattice — but WHERE `held` comes from is the deployment's boundary:
//!
//! - In production, the resolver is backed by the verified presentation /
//!   capability check (the [`crate::middleware`] `StrictPresentation` extractor +
//!   [`crate::authorizer`]'s `CapabilityAuthorizer`): the held authority is what the
//!   requester PROVED it holds. A resolver that returns `None` ⇒ 401 (no authority
//!   presented), exactly as the strict presentation extractor rejects a missing
//!   proof.
//! - The default [`HeaderHeldRights`] resolves the held tier from a header — the
//!   in-band hook the example app + tests use to drive the loop end-to-end. It is
//!   the SAME `AuthRequired` the production resolver yields; only the *source*
//!   differs. The gate ([`crate::affordance::CellAffordance::authorized_for`]) does
//!   not change.

use std::sync::Arc;

use axum::{
    extract::{Path, State},
    http::{HeaderMap, StatusCode},
    routing::{get, post},
    Json, Router,
};
use serde_json::json;

use dregg_cell::AuthRequired;

use crate::affordance::{AffordanceSurface, FireError, FireExecuteError};
use crate::cipherclerk::{AppCipherclerk, EmbeddedExecutor};
use crate::server::{api_error, ErrorResponse};

/// Resolves the **held authority** a request carries — the `held` side of the
/// affordance gate `required ⊆ held`.
///
/// This is the proof/cap boundary: an implementation inspects the request (its
/// verified presentation, a capability header, a bearer token) and returns the
/// [`AuthRequired`] the requester is entitled to. Returning `None` means "no
/// authority presented" → the endpoint answers 401 (the same posture
/// [`crate::middleware::StrictPresentation`] takes for a missing proof). The gate
/// applied to the returned value is the REAL [`dregg_cell::is_attenuation`] — this
/// trait only chooses the *source* of `held`, never weakens the gate.
pub trait HeldRightsResolver: Send + Sync {
    /// Resolve the held authority for a request from its headers. `None` ⇒ no
    /// authority presented (the endpoint rejects with 401).
    fn held(&self, headers: &HeaderMap) -> Option<AuthRequired>;
}

/// Header name carrying the held authority tier for [`HeaderHeldRights`].
pub const HELD_RIGHTS_HEADER: &str = "x-dregg-held-rights";

/// The default [`HeldRightsResolver`]: reads the held tier from the
/// [`HELD_RIGHTS_HEADER`] header (case-insensitive value).
///
/// Accepted values map to the real [`AuthRequired`] tiers: `none` / `root`
/// (`AuthRequired::None`), `either` (`AuthRequired::Either`), `signature` /
/// `sig` (`AuthRequired::Signature`), `proof` (`AuthRequired::Proof`),
/// `impossible` (`AuthRequired::Impossible`). An absent or unrecognized header ⇒
/// `None` (401). This is the in-band hook the example app + integration tests use;
/// a production deployment swaps in a resolver backed by the verified presentation.
#[derive(Clone, Debug, Default)]
pub struct HeaderHeldRights;

impl HeldRightsResolver for HeaderHeldRights {
    fn held(&self, headers: &HeaderMap) -> Option<AuthRequired> {
        let raw = headers.get(HELD_RIGHTS_HEADER)?.to_str().ok()?;
        parse_auth_required(raw)
    }
}

/// Parse an [`AuthRequired`] tier from a (case-insensitive) string label. Shared by
/// the header resolver; returns `None` for unrecognized labels.
pub fn parse_auth_required(raw: &str) -> Option<AuthRequired> {
    match raw.trim().to_ascii_lowercase().as_str() {
        "none" | "root" => Some(AuthRequired::None),
        "either" => Some(AuthRequired::Either),
        "signature" | "sig" => Some(AuthRequired::Signature),
        "proof" => Some(AuthRequired::Proof),
        "impossible" => Some(AuthRequired::Impossible),
        _ => None,
    }
}

/// An HTTP endpoint over one [`AffordanceSurface`] — serves the descriptor + the
/// per-viewer projection, and fires affordances as verified turns through the
/// embedded executor.
///
/// Construct with [`AffordanceEndpoint::new`] (surface + cipherclerk + executor),
/// optionally swap the held-rights resolver with [`AffordanceEndpoint::with_resolver`],
/// then mount with [`AffordanceEndpoint::router`] under a path prefix:
///
/// ```ignore
/// let endpoint = AffordanceEndpoint::new(surface, cipherclerk, executor);
/// AppServer::new(config)
///     .nest("/doc-affordances", endpoint.router("/doc-affordances"))
///     .serve()
///     .await
/// ```
#[derive(Clone)]
pub struct AffordanceEndpoint {
    surface: AffordanceSurface,
    cipherclerk: AppCipherclerk,
    executor: EmbeddedExecutor,
    resolver: Arc<dyn HeldRightsResolver>,
}

impl AffordanceEndpoint {
    /// Build an endpoint over `surface`, firing through `cipherclerk` + `executor`,
    /// with the default header-based held-rights resolver.
    pub fn new(
        surface: AffordanceSurface,
        cipherclerk: AppCipherclerk,
        executor: EmbeddedExecutor,
    ) -> Self {
        Self {
            surface,
            cipherclerk,
            executor,
            resolver: Arc::new(HeaderHeldRights),
        }
    }

    /// Swap the held-rights resolver (e.g. one backed by the verified presentation
    /// in production). The gate applied to the resolved value is unchanged.
    pub fn with_resolver(mut self, resolver: Arc<dyn HeldRightsResolver>) -> Self {
        self.resolver = resolver;
        self
    }

    /// Build the `axum::Router` mounting the three routes. `route_prefix` is the
    /// path this router will be nested at (used to compute the descriptor's
    /// endpoint paths so they match where it is actually mounted).
    pub fn router(self, route_prefix: &str) -> Router {
        let state = EndpointState {
            route_prefix: route_prefix.trim_end_matches('/').to_string(),
            surface: Arc::new(self.surface),
            cipherclerk: self.cipherclerk,
            executor: self.executor,
            resolver: self.resolver,
        };
        Router::new()
            .route("/descriptor", get(handle_descriptor))
            .route("/projected", get(handle_projected))
            .route("/fire/{name}", post(handle_fire))
            .with_state(state)
    }
}

#[derive(Clone)]
struct EndpointState {
    route_prefix: String,
    surface: Arc<AffordanceSurface>,
    cipherclerk: AppCipherclerk,
    executor: EmbeddedExecutor,
    resolver: Arc<dyn HeldRightsResolver>,
}

/// `GET {prefix}/descriptor` — the full anti-drift surface descriptor (every
/// affordance, regardless of viewer). The same payload [`crate::webgen`] renders
/// to JS; a client may fetch it to learn the endpoints + required rights.
async fn handle_descriptor(State(state): State<EndpointState>) -> Json<serde_json::Value> {
    let desc = state.surface.descriptor(&state.route_prefix);
    Json(json!(desc))
}

/// `GET {prefix}/projected` — the PER-VIEWER projection: only the affordances the
/// requester's held authority authorizes (`required ⊆ held`). Missing/invalid
/// held-rights ⇒ 401.
async fn handle_projected(
    State(state): State<EndpointState>,
    headers: HeaderMap,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let held = state.resolver.held(&headers).ok_or_else(|| {
        api_error(
            StatusCode::UNAUTHORIZED,
            "no held authority presented (missing/invalid held-rights)",
        )
    })?;
    // The REAL gate: only the affordances `required ⊆ held` admits.
    let visible = state.surface.project_for(&held);
    let elements: Vec<serde_json::Value> = visible
        .iter()
        .map(|a| {
            json!({
                "name": a.name,
                "requiredRights": format!("{:?}", a.required_rights),
                "effectKind": a.effect_summary().variant_tag(),
                "fireEndpoint": format!("{}/fire/{}", state.route_prefix, a.name),
            })
        })
        .collect();
    Ok(Json(json!({
        "held": format!("{held:?}"),
        "visible": state.surface.visible_names(&held),
        "elements": elements,
    })))
}

/// `POST {prefix}/fire/{name}` — fire the named affordance as a verified turn.
///
/// The cap gate runs FIRST. On pass, the real effect is executed through the
/// embedded executor and the executor's OWN receipt is returned. Refusals:
/// - missing/invalid held authority ⇒ 401 (nothing submitted),
/// - `required ⊄ held` ⇒ 403 (anti-ghost: nothing submitted),
/// - no such affordance ⇒ 404,
/// - executor rejected the (authorized) turn ⇒ 422.
async fn handle_fire(
    State(state): State<EndpointState>,
    Path(name): Path<String>,
    headers: HeaderMap,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let held = state.resolver.held(&headers).ok_or_else(|| {
        api_error(
            StatusCode::UNAUTHORIZED,
            "no held authority presented (missing/invalid held-rights)",
        )
    })?;

    match state
        .surface
        .fire_through_executor(&name, &held, &state.cipherclerk, &state.executor)
    {
        Ok(receipt) => Ok(Json(json!({
            "fired": name,
            "surface_cell": hex_full(&state.surface.cell),
            "actor": hex_full(&receipt.agent),
            "turn_hash": hex_full_arr(&receipt.turn_hash),
            "post_state_hash": hex_full_arr(&receipt.post_state_hash),
            "action_count": receipt.action_count,
        }))),
        Err(FireExecuteError::Gate(FireError::NoSuchAffordance)) => Err(api_error(
            StatusCode::NOT_FOUND,
            format!("no affordance named `{name}` on this surface"),
        )),
        Err(FireExecuteError::Gate(FireError::Unauthorized {
            affordance,
            required,
            held,
        })) => Err(api_error(
            StatusCode::FORBIDDEN,
            format!(
                "unauthorized: firing `{affordance}` requires {required:?} but holder has {held:?}"
            ),
        )),
        Err(FireExecuteError::Executor(e)) => Err(api_error(
            StatusCode::UNPROCESSABLE_ENTITY,
            format!("executor rejected the authorized turn: {e}"),
        )),
    }
}

fn hex_full(cell: &dregg_types::CellId) -> String {
    hex_full_arr(cell.as_bytes())
}

fn hex_full_arr(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affordance::CellAffordance;
    use axum::body::Body;
    use axum::http::Request;
    use dregg_sdk::AgentCipherclerk;
    use dregg_turn::action::{Effect, Event};
    use tower::ServiceExt; // for `oneshot`

    fn cid(b: u8) -> dregg_types::CellId {
        dregg_types::CellId::from_bytes([b; 32])
    }

    fn emit_event(cell: dregg_types::CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: Event { topic: [1u8; 32], data: vec![] },
        }
    }

    /// A doc surface backed by the cipherclerk's OWN cell (so the embedded ledger
    /// has it — fires actually execute). {view@Signature, comment@Either,
    /// admin@None}.
    fn fixture() -> (AppCipherclerk, EmbeddedExecutor, AffordanceSurface) {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let doc = cclerk.cell_id();
        let surface = AffordanceSurface::named(doc, "doc")
            .declare(CellAffordance::new("view", AuthRequired::Signature, emit_event(doc)))
            .declare(CellAffordance::new("comment", AuthRequired::Either, emit_event(doc)))
            .declare(CellAffordance::new("admin", AuthRequired::None, emit_event(doc)));
        (cclerk, executor, surface)
    }

    fn app() -> Router {
        // Mount the endpoint router the way an app would: nested under its prefix.
        // The `router(prefix)` arg makes the descriptor's endpoint labels match
        // this mount point.
        let (cclerk, executor, surface) = fixture();
        let endpoint = AffordanceEndpoint::new(surface, cclerk, executor);
        Router::new().nest("/doc-affordances", endpoint.router("/doc-affordances"))
    }

    async fn body_json(resp: axum::response::Response) -> serde_json::Value {
        let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
            .await
            .unwrap();
        serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null)
    }

    #[tokio::test]
    async fn projected_diverges_per_viewer() {
        // A viewer (Signature) sees only {view}; an editor (Either) sees
        // {comment, view}; over the SAME surface — the deos per-viewer property,
        // served over HTTP, gated by the REAL is_attenuation.
        let viewer = app()
            .oneshot(
                Request::get("/doc-affordances/projected")
                    .header(HELD_RIGHTS_HEADER, "signature")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(viewer.status(), StatusCode::OK);
        let v = body_json(viewer).await;
        assert_eq!(v["visible"], json!(["view"]));

        let editor = app()
            .oneshot(
                Request::get("/doc-affordances/projected")
                    .header(HELD_RIGHTS_HEADER, "either")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        let e = body_json(editor).await;
        assert_eq!(e["visible"], json!(["comment", "view"]));
        // DIVERGENCE over the same surface.
        assert_ne!(v["visible"], e["visible"]);
    }

    #[tokio::test]
    async fn projected_without_held_rights_is_401() {
        let resp = app()
            .oneshot(
                Request::get("/doc-affordances/projected")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::UNAUTHORIZED);
    }

    #[tokio::test]
    async fn fire_authorized_executes_a_real_verified_turn() {
        // An admin (root) fires `admin`: the gate passes, the turn executes through
        // the embedded executor, and the response carries the executor's OWN receipt
        // (non-zero turn_hash).
        let resp = app()
            .oneshot(
                Request::post("/doc-affordances/fire/admin")
                    .header(HELD_RIGHTS_HEADER, "root")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let v = body_json(resp).await;
        assert_eq!(v["fired"], "admin");
        assert_eq!(v["action_count"], 1);
        // The receipt's turn_hash is non-zero (a real executed turn).
        let th = v["turn_hash"].as_str().unwrap();
        assert_ne!(th, "0".repeat(64), "turn_hash must be non-zero");
    }

    #[tokio::test]
    async fn fire_unauthorized_is_403_anti_ghost() {
        // A viewer (Signature) tries to fire `admin` (req None / root): 403, REFUSED
        // by the real gate — nothing executed.
        let resp = app()
            .oneshot(
                Request::post("/doc-affordances/fire/admin")
                    .header(HELD_RIGHTS_HEADER, "signature")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::FORBIDDEN);
    }

    #[tokio::test]
    async fn fire_missing_affordance_is_404() {
        let resp = app()
            .oneshot(
                Request::post("/doc-affordances/fire/nonexistent")
                    .header(HELD_RIGHTS_HEADER, "root")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn descriptor_endpoint_serves_the_anti_drift_surface() {
        let resp = app()
            .oneshot(
                Request::get("/doc-affordances/descriptor")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let v = body_json(resp).await;
        assert_eq!(v["surface"], "doc");
        assert_eq!(v["route_prefix"], "/doc-affordances");
        let els = v["elements"].as_array().unwrap();
        assert_eq!(els.len(), 3);
        let admin = els.iter().find(|e| e["name"] == "admin").unwrap();
        assert_eq!(admin["fire_endpoint"], "/doc-affordances/fire/admin");
    }
}
