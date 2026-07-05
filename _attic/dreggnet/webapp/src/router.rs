//! The router: turn an inbound [`WebRequest`] into a [`WebResponse`] by running
//! the matched route's owned-sandbox handler.
//!
//! ```text
//!   WebRequest ─▶ WebApp::match_route ─▶ Handler::build_source (fill the template)
//!                                          │
//!                                          ▼
//!                       dreggnet_exec::run_workload  (the handler RUNS on the owned sandbox)
//!                                          │  Output { values }
//!                                          ▼
//!                       ResponseSpec::render ─▶ WebResponse
//! ```
//!
//! Two entry points:
//! - [`Router`] — serve a request directly (the handler runs on the owned sandbox; no
//!   metering). This is the path that proves request→handler→response.
//! - [`LeasedRouter`] — the same, but **metered against a funded dregg
//!   execution-lease**: each served request charges `per_period_units` against the
//!   lease budget, and a request that would exceed the budget is refused with
//!   `402 Payment Required` *before the handler runs* (no unpaid work). The lease
//!   is validated through the bridge's real gate
//!   ([`dreggnet_bridge::workflow_input_for_lease`]) when the router is built.

use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use dreggnet_bridge::{BridgeError, Lease};
use dreggnet_durable::{WorkloadRun, WorkloadSpec, run_workflow_on_disk_blocking};

use crate::http::{WebRequest, WebResponse};
use crate::spec::{Handler, HandlerError, Route, WebApp};

/// Serve an agent-assembled [`WebApp`] by running its handlers on the owned sandbox.
pub struct Router {
    app: WebApp,
}

impl Router {
    /// Build a router over an app.
    pub fn new(app: WebApp) -> Router {
        Router { app }
    }

    /// The app this router serves.
    pub fn app(&self) -> &WebApp {
        &self.app
    }

    /// Route + serve one request. A matched route's handler runs on the owned sandbox and
    /// its result is rendered; an unmatched route is a `404`, a handler build
    /// error a `4xx`, and a the owned sandbox execution failure a `502`.
    pub fn serve(&self, req: &WebRequest) -> WebResponse {
        let Some(route) = self.app.match_route(req.method, &req.path) else {
            return WebResponse::error(404, format!("no route for {} {}", req.method, req.path));
        };
        run_handler(route, req)
    }
}

/// Build the durable [`WorkloadSpec`] for one request to a handler: the concrete
/// (templated, integer-validated) source + the declared lang/cap-tier, labelled
/// `handler`. This is the unit a [`LeasedRouter`] runs as one durable step, and the
/// same spec the crash-resume proof drives.
pub fn handler_workload_spec(
    handler: &Handler,
    query: &std::collections::BTreeMap<String, String>,
) -> Result<WorkloadSpec, HandlerError> {
    let source = handler.build_source(query)?;
    Ok(WorkloadSpec {
        label: "handler".to_string(),
        lang: handler.lang.clone(),
        source,
        cap_tier: handler.cap_tier.clone(),
    })
}

/// Run one matched route's handler on the owned sandbox and render the response. Shared by
/// [`Router`] and [`LeasedRouter`].
fn run_handler(route: &crate::spec::Route, req: &WebRequest) -> WebResponse {
    let source = match route.handler.build_source(&req.query) {
        Ok(s) => s,
        Err(e) => return WebResponse::error(e.status(), e.to_string()),
    };
    let tier = match route.handler.cap_tier() {
        Ok(t) => t,
        Err(e) => return WebResponse::error(e.status(), e.to_string()),
    };

    match dreggnet_exec::run_workload(&route.handler.lang, &source, tier) {
        Ok(out) => route.response.render(&out.values),
        // The handler ran (or failed to assemble/run) inside the owned sandbox — a 502 is
        // the honest "the served upstream (the sandboxed handler) erred" code.
        Err(e) => WebResponse::error(502, format!("handler execution failed: {e}")),
    }
}

/// Remove a completed request's on-disk SQLite store and its WAL sidecars. Best-effort:
/// a leftover file only costs disk, never correctness (a stale completed instance is inert).
fn cleanup_store_file(db_path: &std::path::Path) {
    let _ = std::fs::remove_file(db_path);
    for suffix in ["-wal", "-shm"] {
        let mut sidecar = db_path.as_os_str().to_owned();
        sidecar.push(suffix);
        let _ = std::fs::remove_file(std::path::PathBuf::from(sidecar));
    }
}

/// A snapshot of a lease's metering after a request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MeterSnapshot {
    /// Units charged so far across all served requests.
    pub charged: i64,
    /// The lease's total budget.
    pub budget: i64,
    /// Requests served (charged) so far.
    pub requests: i64,
}

impl MeterSnapshot {
    /// Units of budget still available.
    pub fn remaining(&self) -> i64 {
        self.budget - self.charged
    }
}

/// A [`Router`] whose every served request runs as a **durable, exactly-once-metered
/// workflow** against a funded dregg execution-lease.
///
/// Each request is gated against the lease budget (`lease.per_period_units` against
/// `lease.budget_units`) and refused with `402` **before any handler runs** if it would
/// exceed the budget. A request that clears the gate is then run THROUGH the durable layer:
/// the handler is wrapped as a one-step [`WorkflowInput`] and executed by
/// [`dreggnet_durable`] — the handler runs on the owned sandbox, its result is durably checkpointed,
/// and the `MeterTick` charges the step exactly-once. So a served request gets the bridge's
/// full durability guarantee: a crash mid-request resumes exactly-once (no double-charge, no
/// re-run of a completed step), the same invariant the durable bridge enforces per step.
///
/// Durability scope (honest): the durable store on the request path is an **on-disk** SQLite
/// store under [`store_dir`](LeasedRouter::store_dir) — one DB file per request instance. The
/// store therefore *persists across a process restart*: a request that crashes mid-workflow
/// survives on disk, and a fresh process resumes it from its last checkpoint exactly-once (the
/// completed step is replayed, never re-run; the meter is never double-charged). A request that
/// completes deletes its (now finished) DB file, so `store_dir` holds exactly the in-flight /
/// crash-recoverable instances. On-disk SQLite is single-host, WAL-durable — it survives crash
/// and restart on the **same host**; replicated/multi-host durability is the Postgres store's
/// boundary (`dreggnet_durable`'s `pg` feature). Swapping the store changes no workflow code.
///
/// The cross-process crash-resume guarantee is proved over this on-disk store — across a
/// **real** process restart, not just a runtime teardown — in the crate's integration test,
/// driving the same one-step workflow this router builds (via [`handler_workload_spec`]).
pub struct LeasedRouter {
    router: Router,
    lease: Lease,
    meter: Mutex<Meter>,
    /// The directory holding this router's per-request on-disk durable stores. Persists
    /// across a process restart so an in-flight request survives a serving-process crash.
    store_dir: PathBuf,
    /// A per-router nonce mixed into each instance id so instance ids are unique across
    /// router constructions / process runs sharing the same `store_dir` (no collision with
    /// an already-recorded instance).
    nonce: u64,
    /// Per-request durable-workflow instance counter, so each request runs as its own
    /// uniquely-identified durable instance (the exactly-once unit).
    next_instance: AtomicU64,
}

#[derive(Default)]
struct Meter {
    charged: i64,
    requests: i64,
}

impl LeasedRouter {
    /// Build a metered router over `app`, authorized by `lease`, with its per-request durable
    /// stores under the default persistent directory
    /// (`std::env::temp_dir()/dreggnet-webapp/<app>`). Returns the bridge's refusal if the
    /// lease does not authorize work (unfunded / ill-formed / grade-below-floor) — no app is
    /// served under a bad lease.
    ///
    /// Use [`with_store_dir`](LeasedRouter::with_store_dir) to place the durable stores at an
    /// explicit, deployment-chosen location (e.g. a persistent data volume so requests survive
    /// a serving-process restart across reboots).
    pub fn new(app: WebApp, lease: Lease) -> Result<LeasedRouter, BridgeError> {
        let dir = std::env::temp_dir().join("dreggnet-webapp").join(&app.name);
        LeasedRouter::with_store_dir(app, lease, dir)
    }

    /// Build a metered router over `app`, authorized by `lease`, whose per-request durable
    /// stores live under `store_dir`. The directory persists across process restarts: a
    /// request that crashes mid-workflow survives on disk there and is resumed exactly-once by
    /// a fresh process. The directory is created on first use.
    pub fn with_store_dir(
        app: WebApp,
        lease: Lease,
        store_dir: PathBuf,
    ) -> Result<LeasedRouter, BridgeError> {
        // The bridge's REAL gate decides whether this lease authorizes work.
        dreggnet_bridge::workflow_input_for_lease(&lease, None)?;
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0);
        Ok(LeasedRouter {
            router: Router::new(app),
            lease,
            meter: Mutex::new(Meter::default()),
            store_dir,
            nonce,
            next_instance: AtomicU64::new(0),
        })
    }

    /// The directory holding this router's per-request on-disk durable stores.
    pub fn store_dir(&self) -> &std::path::Path {
        &self.store_dir
    }

    /// The app this router serves.
    pub fn app(&self) -> &WebApp {
        self.router.app()
    }

    /// The lease this router runs under.
    pub fn lease(&self) -> &Lease {
        &self.lease
    }

    /// The current meter snapshot.
    pub fn meter(&self) -> MeterSnapshot {
        let m = self.meter.lock().expect("meter poisoned");
        MeterSnapshot {
            charged: m.charged,
            budget: self.lease.budget_units,
            requests: m.requests,
        }
    }

    /// Serve a request as a durable, exactly-once-metered workflow. Charges the
    /// per-request cost against the lease budget *before* running the handler; an
    /// over-budget request is refused with `402` and the handler never runs. A
    /// request that clears the gate runs THROUGH [`dreggnet_durable`] (the handler
    /// executes on the owned sandbox, checkpointed, metered exactly-once). Returns the
    /// response and the meter snapshot after this request.
    pub fn serve(&self, req: &WebRequest) -> (WebResponse, MeterSnapshot) {
        // Match first: an unmatched route is a 404 and is NOT charged (no work).
        let Some(route) = self.router.app.match_route(req.method, &req.path) else {
            return (
                WebResponse::error(404, format!("no route for {} {}", req.method, req.path)),
                self.meter(),
            );
        };

        // Gate the charge BEFORE the handler runs (the bridge's per-step rule, at
        // request granularity): refuse if this request would exceed the budget.
        {
            let mut m = self.meter.lock().expect("meter poisoned");
            let projected = m.charged + self.lease.per_period_units;
            if projected > self.lease.budget_units {
                let snap = MeterSnapshot {
                    charged: m.charged,
                    budget: self.lease.budget_units,
                    requests: m.requests,
                };
                return (
                    WebResponse::error(
                        402,
                        format!(
                            "execution-lease exhausted: request charge {} would reach {} > budget {}",
                            self.lease.per_period_units, projected, self.lease.budget_units
                        ),
                    ),
                    snap,
                );
            }
            // Reserve the charge now so a concurrent request can't double-spend
            // the last unit; the handler runs after the lock is released.
            m.charged = projected;
            m.requests += 1;
        }

        let resp = self.run_route_durably(route, req);
        (resp, self.meter())
    }

    /// Run one matched route's handler as a one-step durable workflow over this router's
    /// **on-disk** durable store and render the response. The handler runs on the owned sandbox inside
    /// [`dreggnet_durable`], checkpointed to disk and metered exactly-once; the within-workflow
    /// budget is exactly one step's cost, so the durable `MeterTick` mirrors the lease's
    /// per-request charge. Because the store is on disk, a request that crashes mid-workflow
    /// survives the serving process and is resumed exactly-once by a fresh process; a request
    /// that completes deletes its (finished) store file.
    fn run_route_durably(&self, route: &Route, req: &WebRequest) -> WebResponse {
        let spec = match handler_workload_spec(&route.handler, &req.query) {
            Ok(s) => s,
            Err(e) => return WebResponse::error(e.status(), e.to_string()),
        };
        let cost = self.lease.per_period_units;
        let input = WorkloadRun::new(cost, cost, vec![spec]);
        let n = self.next_instance.fetch_add(1, Ordering::Relaxed);
        let instance = format!("{}-{}-req-{n}", self.router.app().name, self.nonce);
        let db_path = self.store_dir.join(format!("{instance}.db"));

        let resp = match run_workflow_on_disk_blocking(&input, &instance, &db_path) {
            Ok(out) => route.response.render(&out.outputs),
            // The handler ran (or failed) inside the durable workflow on the owned sandbox — a
            // 502 is the honest "the served upstream handler erred" code.
            Err(e) => WebResponse::error(502, format!("durable handler workflow failed: {e}")),
        };
        // The request finished durably; its on-disk store is no longer needed for recovery.
        // (A crash before this point leaves the file behind for a fresh process to resume.)
        cleanup_store_file(&db_path);
        resp
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assemble;
    use crate::http::WebRequest;
    use dreggnet_bridge::CapGrade;

    #[test]
    fn unmatched_route_is_404() {
        let router = Router::new(assemble::demo_app("demo"));
        let resp = router.serve(&WebRequest::get("/nope"));
        assert_eq!(resp.status, 404);
    }

    #[test]
    fn leased_router_refuses_a_bad_lease() {
        let unfunded = Lease {
            lessee: "a".into(),
            cap_grade: CapGrade::Sandboxed,
            asset: "USD".into(),
            budget_units: 100,
            per_period_units: 1,
            funded: false,
        };
        assert!(LeasedRouter::new(assemble::demo_app("a"), unfunded).is_err());
    }

    #[test]
    fn leased_router_meters_and_exhausts() {
        // Budget for exactly 2 requests at 1 unit each.
        let lease = Lease::funded("a", CapGrade::Sandboxed, "USD", 2, 1);
        let router = LeasedRouter::new(assemble::demo_app("a"), lease).unwrap();

        let (r1, m1) = router.serve(&WebRequest::get("/hello"));
        assert_eq!(r1.status, 200, "first request served: {}", r1.body_str());
        assert_eq!(m1.charged, 1);

        let (r2, m2) = router.serve(&WebRequest::get("/hello"));
        assert_eq!(r2.status, 200);
        assert_eq!(m2.charged, 2);

        // The third request would exceed the budget → 402, handler never runs.
        let (r3, m3) = router.serve(&WebRequest::get("/hello"));
        assert_eq!(r3.status, 402, "exhausted: {}", r3.body_str());
        assert_eq!(m3.charged, 2, "no charge on a refused request");
    }
}
