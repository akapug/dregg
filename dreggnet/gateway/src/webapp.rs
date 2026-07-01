//! Serve an agent-assembled web app through the gateway.
//!
//! This is the gateway-side adoption of [`dreggnet_webapp`]: where
//! [`crate::MachinesHandler`] is the fly *control* plane (create/inspect/reap
//! machines), [`WebAppHandler`] is the *data* plane — it routes inbound HTTP for
//! a served app to that app's polyana handlers, the realization of "the gateway
//! routes inbound HTTP to a leased polyana workload."
//!
//! ```text
//!   inbound HTTP  ──▶  WebAppHandler::dispatch
//!                        │  dreggnet_webapp::Router::serve  (match the route)
//!                        ▼
//!                      dreggnet_exec::run_workload          (the handler runs on polyana)
//!                        │
//!                        ▼
//!                      fly-shaped HTTP response written back
//! ```
//!
//! It serves a single [`dreggnet_webapp::WebApp`] (the app's own ingress, like a
//! `*.fly.dev` host). Per-app multiplexing by `Host`/path is a later rung; the
//! portable `dreggnet-serve` binary in the `webapp` crate is the any-host serving
//! path. Like [`crate::MachinesHandler`], the body-bearing path is `dispatch`
//! (the serving binary reads the body off the socket); the body-less
//! [`Handler::handle`] trait surface dispatches with an empty body.

use std::sync::Arc;

use dreggnet_http::handler::{Handler, HandlerResult};
use dreggnet_http::{Method, Request, ResponseWriter};

use std::time::{SystemTime, UNIX_EPOCH};

use dreggnet_guard::{Guard, GuardRefusal};
use dreggnet_webapp::{Router, WebApp, WebRequest, WebResponse};

use crate::webresp::{map_method, write};

/// The per-account abuse gate on the SERVING path: the guard, plus the owning
/// account subject + this site's id, so each inbound request is charged against
/// the per-site + per-account request rate and refused if the site/account is
/// suspended. Optional — without it the handler serves unbounded (the dev posture).
#[derive(Clone)]
struct ServeGuard {
    guard: Arc<Guard>,
    subject: String,
    site_id: String,
}

/// The gateway HTTP handler that serves one agent-assembled [`WebApp`] over polyana.
pub struct WebAppHandler {
    router: Arc<Router>,
    serve_guard: Option<ServeGuard>,
}

impl WebAppHandler {
    /// Serve `app`'s routes (unmetered, unguarded). For a lease-metered served app,
    /// drive [`dreggnet_webapp::LeasedRouter`] from the portable serving path; the
    /// gateway adopts the plain [`Router`] here.
    pub fn new(app: WebApp) -> WebAppHandler {
        WebAppHandler {
            router: Arc::new(Router::new(app)),
            serve_guard: None,
        }
    }

    /// Serve `app` under the per-account abuse [`Guard`]: each request is charged
    /// against the per-site (`site_id`) and per-account (`subject`) request rate
    /// (over ⇒ `429`), and a suspended site/account stops serving (⇒ `403`) with the
    /// owner-readable takedown reason. The `subject` is the owning account's
    /// `dga1_`-derived id; `site_id` identifies this served resource.
    pub fn guarded(
        app: WebApp,
        guard: Arc<Guard>,
        subject: impl Into<String>,
        site_id: impl Into<String>,
    ) -> WebAppHandler {
        WebAppHandler {
            router: Arc::new(Router::new(app)),
            serve_guard: Some(ServeGuard {
                guard,
                subject: subject.into(),
                site_id: site_id.into(),
            }),
        }
    }

    /// The app this handler serves.
    pub fn app(&self) -> &WebApp {
        self.router.app()
    }

    /// Route + serve one request, decoding `body` for the matched handler.
    ///
    /// The serving binary passes the request body it read off the socket; the
    /// [`Handler::handle`] trait surface passes an empty body.
    ///
    /// When [`guarded`](Self::guarded), the per-account abuse gate runs FIRST: a
    /// suspended site/account is refused `403` (stops serving) and a request over
    /// the per-site/per-account rate is refused `429` — before any handler runs.
    pub fn dispatch(
        &self,
        method: Method,
        target: &str,
        body: &[u8],
        response: &mut ResponseWriter,
    ) -> HandlerResult {
        // The serving-path abuse gate (suspension + per-site/per-account request rate).
        if let Some(sg) = &self.serve_guard {
            if let Err(refusal) = sg
                .guard
                .admit_request(&sg.subject, &sg.site_id, now_unix_secs())
            {
                let (status, msg) = match &refusal {
                    GuardRefusal::Suspended { reason } => {
                        (403u16, format!("resource suspended: {reason}"))
                    }
                    GuardRefusal::Rate(e) => (429u16, e.to_string()),
                    GuardRefusal::Quota(e) => (402u16, e.to_string()),
                };
                return write(response, &WebResponse::error(status, msg));
            }
        }
        let Some(m) = map_method(method) else {
            return write(response, &WebResponse::error(405, "unsupported method"));
        };
        let req = WebRequest::new(m, target, body.to_vec());
        let resp = self.router.serve(&req);
        write(response, &resp)
    }
}

/// Wall-clock unix seconds — the sliding-window rate-limiter's block clock.
fn now_unix_secs() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

impl Handler for WebAppHandler {
    fn handle(&self, request: &Request, response: &mut ResponseWriter) -> HandlerResult {
        // The body-less `dreggnet_http::Request` surface carries no body; the serving
        // binary uses `dispatch` directly with the socket body.
        self.dispatch(request.method(), request.path(), &[], response)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_webapp::assemble;

    fn run(handler: &WebAppHandler, method: Method, target: &str) -> String {
        let mut buf = vec![0u8; 64 * 1024];
        let mut writer = ResponseWriter::new(&mut buf);
        let res = handler.dispatch(method, target, &[], &mut writer);
        let n = res.bytes_written();
        String::from_utf8_lossy(&buf[..n]).to_string()
    }

    #[test]
    fn serves_add_route_over_polyana() {
        let handler = WebAppHandler::new(assemble::demo_app("demo"));
        let raw = run(&handler, Method::Get, "/add?a=40&b=2");
        assert!(raw.contains("200 OK"), "raw: {raw}");
        assert!(raw.contains("\"result\":42"), "raw: {raw}");
    }

    #[test]
    fn unknown_route_is_404() {
        let handler = WebAppHandler::new(assemble::demo_app("demo"));
        let raw = run(&handler, Method::Get, "/nope");
        assert!(raw.contains("404 Not Found"), "raw: {raw}");
    }

    #[test]
    fn a_suspended_site_stops_serving_403() {
        use dreggnet_guard::Guard;
        let guard = Arc::new(Guard::new([21u8; 32]));
        let handler = WebAppHandler::guarded(
            assemble::demo_app("demo"),
            guard.clone(),
            "acct-a",
            "site_demo",
        );
        // serves fine before takedown.
        assert!(run(&handler, Method::Get, "/add?a=1&b=2").contains("200 OK"));
        // operator suspends the site → it stops serving (403), reason readable.
        guard.suspend_resource("acct-a", "site_demo", "phishing", "dregg:op", 1000);
        let raw = run(&handler, Method::Get, "/add?a=1&b=2");
        assert!(raw.contains("403"), "raw: {raw}");
        assert!(raw.contains("phishing"), "owner-readable reason: {raw}");
    }

    #[test]
    fn request_rate_429s_a_hammered_site() {
        use dreggnet_guard::{Guard, QuotaPolicy, RateLimit, RatePolicy};
        // a tiny per-site request rate so a small burst trips 429.
        let guard = Arc::new(Guard::with_policy(
            QuotaPolicy::default(),
            RatePolicy {
                site_requests: RateLimit::new(2, 60),
                ..RatePolicy::default()
            },
            [22u8; 32],
        ));
        let handler = WebAppHandler::guarded(
            assemble::demo_app("demo"),
            guard.clone(),
            "acct-b",
            "site_hot",
        );
        assert!(run(&handler, Method::Get, "/add?a=1&b=2").contains("200 OK"));
        assert!(run(&handler, Method::Get, "/add?a=1&b=2").contains("200 OK"));
        // the third request within the window is rate-limited.
        let raw = run(&handler, Method::Get, "/add?a=1&b=2");
        assert!(raw.contains("429"), "raw: {raw}");
    }
}
