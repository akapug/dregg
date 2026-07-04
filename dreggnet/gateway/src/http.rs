//! The `Handler` that serves the fly-machines API.
//!
//! [`MachinesHandler`] implements [`dreggnet_http::handler::Handler`] (so it is
//! the handler for the `/v1/apps/` prefix). It does its own path routing via
//! [`crate::route`] — a generic exact-match router can't express the `{app}` /
//! `{id}` path params.
//!
//! ## Routing + the body
//!
//! All routing flows through one method, [`MachinesHandler::dispatch`], which
//! takes the request method, path, and body bytes. Read-only and lifecycle
//! routes (list, status, stop, start, delete) need no body. Create
//! (`POST .../machines`) carries a JSON body, decoded by [`parse_create_request`].
//!
//! The body reaches `dispatch` two ways:
//!
//! - The serving binary (`main.rs`) reads the request body off the socket and
//!   passes it straight in, so a real `curl -d '{...}'` create is decoded for
//!   real. This is the production path.
//! - The [`Handler`] trait surface ([`dreggnet_http::Request`]) is the zero-copy,
//!   body-less request view, so [`Handler::handle`] calls `dispatch` with an
//!   **empty** body. An empty body means "minimal shared-guest machine" (a
//!   body-less create, which fly permits), so the handler-mounted path still
//!   creates a default machine.

use std::sync::Arc;

use dreggnet_http::handler::{Handler, HandlerResult};
use dreggnet_http::response::{StatusCode, content_type};
use dreggnet_http::{Method, Request, ResponseWriter};

use crate::gateway::{GatewayError, MachineGateway};
use crate::route::{self, Route};
use crate::status::{GatewayInfo, GatewayStatus};
use crate::types::{ApiError, CreateMachineRequest, OkBody};
use dreggnet_guard::GuardRefusal;

/// Parse a fly create body (`POST .../machines`) from raw JSON bytes.
///
/// Real + tested; the body-bearing seam (`ParsedRequest::body_bytes()`) feeds
/// this once the gateway is mounted there.
pub fn parse_create_request(body: &[u8]) -> Result<CreateMachineRequest, serde_json::Error> {
    serde_json::from_slice(body)
}

/// The fly-machines API handler over a [`MachineGateway`].
///
/// The gateway HTTP handler for the `/v1/apps/` prefix.
pub struct MachinesHandler {
    gateway: Arc<MachineGateway>,
    /// Operator-set facts for the friendly root (name / portal / node health URL).
    info: Arc<GatewayInfo>,
}

impl MachinesHandler {
    /// Build a handler over an existing (shared) gateway, with default landing info.
    pub fn new(gateway: Arc<MachineGateway>) -> Self {
        MachinesHandler {
            gateway,
            info: Arc::new(GatewayInfo::default()),
        }
    }

    /// Build a handler over a gateway with explicit landing-page info.
    pub fn with_info(gateway: Arc<MachineGateway>, info: GatewayInfo) -> Self {
        MachinesHandler {
            gateway,
            info: Arc::new(info),
        }
    }

    /// Build a handler over a fresh gateway.
    pub fn fresh() -> Self {
        MachinesHandler::new(Arc::new(MachineGateway::new()))
    }

    /// The gateway this handler serves (for the control loop that drives
    /// [`MachineGateway::fulfill`]).
    pub fn gateway(&self) -> &Arc<MachineGateway> {
        &self.gateway
    }

    /// The landing-page info this handler renders the root with.
    pub fn info(&self) -> &Arc<GatewayInfo> {
        &self.info
    }

    /// Route + serve one request, decoding `body` for the create endpoint.
    ///
    /// This is the single routing path. The serving binary passes the request
    /// body it read off the socket; the [`Handler::handle`] trait surface passes
    /// an empty body (see the module docs).
    pub fn dispatch(
        &self,
        method: Method,
        path: &str,
        body: &[u8],
        response: &mut ResponseWriter,
    ) -> HandlerResult {
        let route = route::parse(method, path);
        match route {
            Route::Root => {
                let status = GatewayStatus::assemble(&self.gateway, &self.info);
                html(response, StatusCode::Ok, &status.render_html())
            }
            Route::Status => {
                let status = GatewayStatus::assemble(&self.gateway, &self.info);
                json(response, StatusCode::Ok, &status)
            }
            Route::Health => {
                let body = serde_json::json!({ "ok": true, "service": self.info.name });
                json(response, StatusCode::Ok, &body)
            }
            Route::CreateMachine { app } => {
                // A present body is decoded for real; an empty/whitespace body
                // means a minimal shared-guest machine (a body-less create).
                let req = match decode_create_body(body) {
                    Ok(req) => req,
                    Err(e) => {
                        return json(
                            response,
                            StatusCode::BadRequest,
                            &ApiError::new(format!("invalid create body: {e}")),
                        );
                    }
                };
                match self.gateway.create(app, &req) {
                    Ok(machine) => json(response, StatusCode::Ok, &machine),
                    Err(GatewayError::LeaseRefused(e)) => json(
                        response,
                        // 422: the request was well-formed but the lease does
                        // not authorize the work (fly returns 4xx for these).
                        StatusCode::BadRequest,
                        &ApiError::new(format!("lease refused: {e}")),
                    ),
                    // The per-account abuse guard's in-band refusal: 402 (quota) /
                    // 429 (deploy rate) / 403 (suspended), per the refusal kind.
                    Err(GatewayError::Refused(r)) => {
                        json(response, guard_status(&r), &ApiError::new(r.to_string()))
                    }
                    Err(e) => json(
                        response,
                        StatusCode::InternalServerError,
                        &ApiError::new(e.to_string()),
                    ),
                }
            }
            Route::ListMachines { app } => {
                let machines = self.gateway.list(app);
                json(response, StatusCode::Ok, &machines)
            }
            Route::GetMachine { id, .. } => match self.gateway.get(id) {
                Some(machine) => json(response, StatusCode::Ok, &machine),
                None => not_found(response),
            },
            Route::StopMachine { id, .. } => match self.gateway.stop(id) {
                Some(machine) => json(response, StatusCode::Ok, &machine),
                None => not_found(response),
            },
            Route::StartMachine { id, .. } => match self.gateway.start(id) {
                Some(machine) => json(response, StatusCode::Ok, &machine),
                None => not_found(response),
            },
            Route::DeleteMachine { id, .. } => {
                if self.gateway.delete(id) {
                    json(response, StatusCode::Ok, &OkBody::accepted())
                } else {
                    not_found(response)
                }
            }
            Route::NotFound => not_found(response),
        }
    }

    /// Route + serve one request, **driving a real dispatch** for create when the
    /// gateway is dispatch-configured.
    ///
    /// This is the serving binary's entry point (the gateway connection loop blocks
    /// on it). For every route except create it is identical to [`dispatch`]. For
    /// `POST .../machines` against a dispatch-configured gateway
    /// ([`MachineGateway::dispatches`]) it does the full create→run in one call:
    /// it admits the lease (records the machine), then dispatches the lease's
    /// workload over the overlay to the compute node ([`MachineGateway::fulfill`])
    /// and returns the machine record already reflecting the **real metered result**
    /// (or the lapse/failure). Without a dispatch backend it falls back to the
    /// synchronous create (records the machine as `created`, the fly create→start
    /// split — `start` then drives the launch).
    ///
    /// [`dispatch`]: MachinesHandler::dispatch
    pub async fn dispatch_async(
        &self,
        method: Method,
        path: &str,
        body: &[u8],
        response: &mut ResponseWriter<'_>,
    ) -> HandlerResult {
        // Only create against a dispatch-configured gateway needs the async path;
        // everything else is the synchronous route table.
        match route::parse(method, path) {
            Route::CreateMachine { app } if self.gateway.dispatches() => {
                let req = match decode_create_body(body) {
                    Ok(req) => req,
                    Err(e) => {
                        return json(
                            response,
                            StatusCode::BadRequest,
                            &ApiError::new(format!("invalid create body: {e}")),
                        );
                    }
                };
                // Admit the lease (records the machine); a refused lease never runs.
                let machine = match self.gateway.create(app, &req) {
                    Ok(m) => m,
                    Err(GatewayError::LeaseRefused(e)) => {
                        return json(
                            response,
                            StatusCode::BadRequest,
                            &ApiError::new(format!("lease refused: {e}")),
                        );
                    }
                    Err(GatewayError::Refused(r)) => {
                        return json(response, guard_status(&r), &ApiError::new(r.to_string()));
                    }
                    Err(e) => {
                        return json(
                            response,
                            StatusCode::InternalServerError,
                            &ApiError::new(e.to_string()),
                        );
                    }
                };
                // Dispatch the workload to the compute node; the machine record then
                // reflects the real metered outcome (or the lapse/failure reason).
                let id = machine.id.clone();
                match self.gateway.fulfill(&id).await {
                    // Ran, or lapsed honestly: return the machine record (its `state`
                    // + `dregg` report tell the story). A lapse is a 200 because the
                    // lease WAS processed — no work was claimed past its budget.
                    Ok(_) | Err(GatewayError::Lapsed(_)) => {
                        let m = self.gateway.get(&id).unwrap_or(machine);
                        json(response, StatusCode::Ok, &m)
                    }
                    // The node could not be reached / the workflow faulted: a 502,
                    // with the machine left recording the failure for a later GET.
                    Err(e) => json(
                        response,
                        StatusCode::BadGateway,
                        &ApiError::new(e.to_string()),
                    ),
                }
            }
            // Start against a dispatch-configured gateway (re)launches the workload —
            // the fly create→start split, honored.
            Route::StartMachine { id, .. } if self.gateway.dispatches() => {
                match self.gateway.fulfill(id).await {
                    Ok(_) | Err(GatewayError::Lapsed(_)) => match self.gateway.get(id) {
                        Some(m) => json(response, StatusCode::Ok, &m),
                        None => not_found(response),
                    },
                    Err(GatewayError::NotFound) => not_found(response),
                    Err(e) => json(
                        response,
                        StatusCode::BadGateway,
                        &ApiError::new(e.to_string()),
                    ),
                }
            }
            _ => self.dispatch(method, path, body, response),
        }
    }
}

impl Handler for MachinesHandler {
    fn handle(&self, request: &Request, response: &mut ResponseWriter) -> HandlerResult {
        // The body-less `dreggnet_http::Request` surface carries no body; the serving
        // binary uses `dispatch` directly with the socket body. See module docs.
        self.dispatch(request.method(), request.path(), &[], response)
    }
}

/// Decode a fly create body, treating an empty/whitespace body as a default
/// (minimal shared-guest) machine — a body-less create, which fly permits.
fn decode_create_body(body: &[u8]) -> Result<CreateMachineRequest, serde_json::Error> {
    if body.iter().all(|b| b.is_ascii_whitespace()) {
        Ok(CreateMachineRequest::default())
    } else {
        parse_create_request(body)
    }
}

/// Write a JSON body with a status code; returns the bytes written.
/// Map a per-account abuse-guard refusal onto the in-band HTTP status: a quota
/// ceiling is `402 Payment Required` (raise the quota / pay), a rate ceiling is
/// `429 Too Many Requests`, a suspension is `403 Forbidden`.
fn guard_status(r: &GuardRefusal) -> StatusCode {
    match r {
        GuardRefusal::Quota(_) => StatusCode::PaymentRequired,
        GuardRefusal::Rate(_) => StatusCode::TooManyRequests,
        GuardRefusal::Suspended { .. } => StatusCode::Forbidden,
    }
}

fn json<T: serde::Serialize>(
    response: &mut ResponseWriter,
    status: StatusCode,
    value: &T,
) -> HandlerResult {
    let body = match serde_json::to_vec(value) {
        Ok(b) => b,
        Err(e) => {
            // Serialization failure — emit a 500 with a plain message.
            let msg = format!("{{\"error\":\"serialize: {e}\"}}");
            response
                .status(StatusCode::InternalServerError)
                .header_line(content_type::APPLICATION_JSON)
                .content_length(msg.len())
                .body(msg.as_bytes());
            return HandlerResult::Written(response.position());
        }
    };
    response
        .status(status)
        .header_line(content_type::APPLICATION_JSON)
        .content_length(body.len())
        .body(&body);
    HandlerResult::Written(response.position())
}

/// Write an HTML body with a status code (the friendly landing page).
fn html(response: &mut ResponseWriter, status: StatusCode, body: &str) -> HandlerResult {
    response
        .status(status)
        .header_line(content_type::TEXT_HTML)
        .content_length(body.len())
        .body(body.as_bytes());
    HandlerResult::Written(response.position())
}

/// A fly-shaped 404 with a JSON error body.
fn not_found(response: &mut ResponseWriter) -> HandlerResult {
    json(
        response,
        StatusCode::NotFound,
        &ApiError::new("machine not found"),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::funding::{FundingError, FundingSource};
    use dreggnet_bridge::{CapGrade, Lease};
    use dreggnet_http::Method;

    /// A test funding source standing in for the chain's verified attestation: it
    /// funds any app generously (a real on-chain reserve), so the create-path
    /// tests exercise the admit path. The funded-vs-not gate itself is proven in
    /// [`funding`](crate::funding) + `tests/no_free_compute`.
    struct FundsAnyApp;
    impl FundingSource for FundsAnyApp {
        fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError> {
            Ok(vec![Lease::funded(
                app,
                CapGrade::MicroVm,
                "computrons",
                1_000_000,
                1,
            )])
        }
    }

    /// A handler over a gateway whose funding source attests a generous funded
    /// lease for any app — the live binary attaches one via `funded_by`, so the
    /// create-path tests do the same instead of failing closed on no funding.
    fn funded_handler() -> MachinesHandler {
        MachinesHandler::new(Arc::new(
            MachineGateway::new().funded_by(Arc::new(FundsAnyApp)),
        ))
    }

    fn run(handler: &MachinesHandler, method: Method, path: &str) -> (String, String) {
        let req = Request::new(method, path, path.as_bytes());
        let mut buf = vec![0u8; 16 * 1024];
        let mut writer = ResponseWriter::new(&mut buf);
        let res = handler.handle(&req, &mut writer);
        let n = res.bytes_written();
        let raw = String::from_utf8_lossy(&buf[..n]).to_string();
        // Split status line from the rest for convenient assertions.
        let status = raw.lines().next().unwrap_or("").to_string();
        (status, raw)
    }

    #[test]
    fn create_then_get_then_list() {
        let handler = funded_handler();

        let (status, body) = run(&handler, Method::Post, "/v1/apps/my-app/machines");
        assert!(status.contains("200 OK"), "status was: {status}");
        assert!(body.contains("application/json"));
        assert!(body.contains("\"state\":\"created\""));

        // The created id is listable.
        let listed = handler.gateway().list("my-app");
        assert_eq!(listed.len(), 1);
        let id = &listed[0].id;

        let (status, body) = run(
            &handler,
            Method::Get,
            &format!("/v1/apps/my-app/machines/{id}"),
        );
        assert!(status.contains("200 OK"));
        assert!(body.contains(id));

        let (status, body) = run(&handler, Method::Get, "/v1/apps/my-app/machines");
        assert!(status.contains("200 OK"));
        assert!(body.contains(id));
    }

    #[test]
    fn get_unknown_is_404() {
        let handler = MachinesHandler::fresh();
        let (status, body) = run(&handler, Method::Get, "/v1/apps/a/machines/nope");
        assert!(status.contains("404 Not Found"), "status was: {status}");
        assert!(body.contains("machine not found"));
    }

    #[test]
    fn stop_start_delete_lifecycle() {
        let handler = funded_handler();
        run(&handler, Method::Post, "/v1/apps/a/machines");
        let id = handler.gateway().list("a")[0].id.clone();

        let (status, body) = run(
            &handler,
            Method::Post,
            &format!("/v1/apps/a/machines/{id}/stop"),
        );
        assert!(status.contains("200 OK"));
        assert!(body.contains("\"state\":\"stopped\""));

        let (status, body) = run(
            &handler,
            Method::Post,
            &format!("/v1/apps/a/machines/{id}/start"),
        );
        assert!(status.contains("200 OK"));
        assert!(body.contains("\"state\":\"started\""));

        let (status, _) = run(
            &handler,
            Method::Delete,
            &format!("/v1/apps/a/machines/{id}"),
        );
        assert!(status.contains("200 OK"));
        assert!(handler.gateway().get(&id).is_none());
    }

    #[test]
    fn unknown_route_is_404() {
        let handler = MachinesHandler::fresh();
        let (status, _) = run(&handler, Method::Get, "/nope");
        assert!(status.contains("404 Not Found"));
    }

    #[test]
    fn root_is_a_friendly_landing_page_not_a_404() {
        let handler = MachinesHandler::fresh();
        let (status, body) = run(&handler, Method::Get, "/");
        assert!(status.contains("200 OK"), "status was: {status}");
        assert!(body.contains("text/html"), "body was: {body}");
        assert!(body.contains("DreggNet gateway"));
        assert!(body.contains("alive"));
        assert!(body.contains("portal.example.com"));
        // It is NOT the old fly 404.
        assert!(!body.contains("machine not found"));
    }

    #[test]
    fn status_endpoint_is_json() {
        let handler = MachinesHandler::fresh();
        let (status, body) = run(&handler, Method::Get, "/status");
        assert!(status.contains("200 OK"));
        assert!(body.contains("application/json"));
        assert!(body.contains("\"status\":\"alive\""));
        assert!(body.contains("\"machines\":0"));
    }

    #[test]
    fn health_endpoint_is_ok() {
        let handler = MachinesHandler::fresh();
        let (status, body) = run(&handler, Method::Get, "/healthz");
        assert!(status.contains("200 OK"));
        assert!(body.contains("\"ok\":true"));
    }

    #[test]
    fn create_body_decode_is_real() {
        let body = br#"{"name":"m1","config":{"guest":{"cpu_kind":"performance","cpus":2,"memory_mb":1024}}}"#;
        let req = parse_create_request(body).expect("valid body");
        assert_eq!(req.name.as_deref(), Some("m1"));
        assert_eq!(req.config.guest.cpu_kind, "performance");
    }

    /// The serving binary's path: `dispatch` with a real body decodes it and the
    /// created machine reflects the request (the body seam, closed).
    #[test]
    fn dispatch_decodes_a_create_body() {
        let handler = funded_handler();
        let body = br#"{"name":"w1","config":{"guest":{"cpu_kind":"performance","cpus":2,"memory_mb":1024}}}"#;
        let mut buf = vec![0u8; 16 * 1024];
        let mut writer = ResponseWriter::new(&mut buf);
        let res = handler.dispatch(Method::Post, "/v1/apps/demo/machines", body, &mut writer);
        let raw = String::from_utf8_lossy(&buf[..res.bytes_written()]).to_string();
        assert!(raw.contains("200 OK"), "status was: {raw}");
        assert!(raw.contains("\"name\":\"w1\""), "body was: {raw}");

        let listed = handler.gateway().list("demo");
        assert_eq!(listed.len(), 1);
        assert_eq!(listed[0].name, "w1");
    }

    /// A malformed create body is a 400 (and provisions no machine).
    #[test]
    fn dispatch_rejects_a_malformed_create_body() {
        let handler = MachinesHandler::fresh();
        let mut buf = vec![0u8; 4096];
        let mut writer = ResponseWriter::new(&mut buf);
        let res = handler.dispatch(
            Method::Post,
            "/v1/apps/demo/machines",
            b"{not json",
            &mut writer,
        );
        let raw = String::from_utf8_lossy(&buf[..res.bytes_written()]).to_string();
        assert!(raw.contains("400 Bad Request"), "status was: {raw}");
        assert_eq!(handler.gateway().list("demo").len(), 0);
    }
}
