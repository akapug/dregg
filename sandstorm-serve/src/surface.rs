//! The weld onto the substrate's site-serving surface (`http-serve`).
//!
//! `http-serve` owns the HTTP/1.1 plumbing ONCE — the hardened parse
//! (slow-loris `408`, header cap `431`, body cap `413`, bounded chunked
//! decode, the `ConnGate` connection ceiling) — and hands a handler one
//! [`ServeRequest`]. This module is the weld: it builds the
//! `Fn(&ServeRequest) -> WebResponse` handler that routes an authenticated
//! request into [`GrainServer::serve`], plus a small operable daemon (spawn /
//! `local_addr` / shutdown) that drives `http-serve`'s hardened
//! single-connection path on an accept loop a test or operator can stop.
//!
//! ## The request contract
//!
//! * `Authorization` — checked by the pluggable [`TransportGate`] FIRST (an
//!   operated deployment gates non-loopback binds on a bearer capability; the
//!   permissive [`OpenGate`] is for loopback/dev). A refusal is `401` with a
//!   typed JSON body, before any grain state is touched.
//! * `GET /__grain/status` — the operator surface: grain/app identity, the
//!   honest body kind, lifecycle state, live `DataRoot`, custody generation.
//! * everything else — the grain's `WebSession` surface. Requires:
//!   - `x-dregg-grain-cap`: the `dga1_…` grain capability token,
//!   - `x-dregg-presenter`: the presenting subject,
//!   - optional `x-dregg-user-id` / `x-dregg-username` /
//!     `x-dregg-session-id` display identity (defaulting to the presenter).
//!
//!   The permission set is derived from the cap on the real rail inside
//!   [`GrainServer::serve`]; a cap that admits nothing is `403` with no
//!   effect. Identity headers are read with [`ServeRequest::header`], which
//!   refuses smuggled duplicates fail-closed.
//!
//! NOTE the honest residuals (also on the serving core): the presenter
//! subject is transport-asserted (forward-auth is a separate seam), and the
//! upstream `HttpResponse` carries no content-type, so grain bodies are served
//! as `application/octet-stream`.

use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::{SystemTime, UNIX_EPOCH};

use http_serve::{serve_http_connection_limited, HttpMethod, Limits, ServeRequest, WebResponse};
use sandstorm_bridge::bridge::{HttpRequest, Method};

use crate::custody::GrainCustodyAnchorV1;
use crate::serve::{GrainServeError, GrainServer, PresentedSession};

/// The transport-boundary gate a deployment plugs in ahead of the grain
/// surface. This is NOT the grain capability (the `dga1_` cap gates the grain
/// inside the serving core); it is the operator boundary — e.g. a bearer
/// capability required on a non-loopback bind.
pub trait TransportGate: Send + Sync {
    /// Admit or refuse a request given its `Authorization` header value
    /// (already read duplicate-safe). Refusals are answered `401`.
    fn admits(&self, authorization: Option<&str>) -> bool;
    /// Whether this gate actually enforces anything. An operated wrapper uses
    /// this to refuse dangerous bind/gate combinations fail-closed.
    fn is_enforcing(&self) -> bool;
}

/// The permissive gate — loopback/dev only. An operated deployment must not
/// expose it beyond loopback (`is_enforcing` says so, honestly).
pub struct OpenGate;

impl TransportGate for OpenGate {
    fn admits(&self, _authorization: Option<&str>) -> bool {
        true
    }
    fn is_enforcing(&self) -> bool {
        false
    }
}

fn refusal(status: u16, code: &str, detail: &str) -> WebResponse {
    WebResponse {
        status,
        content_type: "application/json".to_string(),
        body: serde_json::json!({ "refusal": code, "detail": detail })
            .to_string()
            .into_bytes(),
    }
}

fn now_unix_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|elapsed| elapsed.as_secs())
        .unwrap_or(0)
}

/// Build the `http-serve` handler for one grain server behind one transport
/// gate — the pure weld, usable under [`http_serve::serve_http`] /
/// [`http_serve::serve_on`] directly or via [`GrainServeDaemon`].
pub fn grain_handler(
    server: Arc<Mutex<GrainServer>>,
    gate: Arc<dyn TransportGate>,
) -> impl Fn(&ServeRequest) -> WebResponse + Send + Sync + 'static {
    move |request: &ServeRequest| handle(request, &server, gate.as_ref())
}

fn handle(
    request: &ServeRequest,
    server: &Mutex<GrainServer>,
    gate: &dyn TransportGate,
) -> WebResponse {
    // 1. The operator transport boundary.
    if !gate.admits(request.header("authorization")) {
        return refusal(
            401,
            "grain-serve.operator-capability-refused",
            "the operator bearer capability is missing or invalid",
        );
    }

    // 2. The operator status surface (reads only).
    if request.method == HttpMethod::Get && request.target == "/__grain/status" {
        let guard = match server.lock() {
            Ok(guard) => guard,
            Err(_) => return refusal(500, "grain-serve.poisoned", "server lock poisoned"),
        };
        let status = serde_json::json!({
            "grain_cell_id": guard.grain_cell_id(),
            "app_id": guard.app_id(),
            "body": guard.body_kind().as_str(),
            "grain_state": format!("{:?}", guard.grain_state()),
            "data_root": guard.data_root().0,
            "custody_generation": guard.anchor().generation,
        });
        return WebResponse::json(status.to_string().into_bytes());
    }

    // 3. The grain surface: capability headers, then the real rail decides.
    let Some(cap_token) = request.header("x-dregg-grain-cap") else {
        return refusal(
            401,
            "grain-serve.capability-required",
            "x-dregg-grain-cap (a dga1_ grain capability) is required",
        );
    };
    let Some(presenter) = request.header("x-dregg-presenter") else {
        return refusal(
            401,
            "grain-serve.presenter-required",
            "x-dregg-presenter (the presenting subject) is required",
        );
    };
    let session_identity = PresentedSession {
        user_id: request
            .header("x-dregg-user-id")
            .unwrap_or(presenter)
            .to_string(),
        username: request
            .header("x-dregg-username")
            .unwrap_or(presenter)
            .to_string(),
        session_id: request
            .header("x-dregg-session-id")
            .unwrap_or("s:unlabeled")
            .to_string(),
        cap_token: cap_token.to_string(),
        presenter_subject: presenter.to_string(),
    };

    // The WebSession surface carries the four verbs the bridge models.
    let method = match request.method {
        HttpMethod::Get => Method::Get,
        HttpMethod::Post => Method::Post,
        HttpMethod::Put => Method::Put,
        HttpMethod::Delete => Method::Delete,
        HttpMethod::Patch | HttpMethod::Head | HttpMethod::Options => {
            return refusal(
                405,
                "grain-serve.method-not-supported",
                "the WebSession surface carries GET/POST/PUT/DELETE",
            );
        }
    };
    // Route on the path only (the grain's WebSession paths carry no query).
    let path = request
        .target
        .split_once('?')
        .map(|(path, _)| path)
        .unwrap_or(&request.target)
        .to_string();
    let grain_request = HttpRequest {
        method,
        path,
        body: request.body.clone(),
    };

    let serve_result = {
        let mut guard = match server.lock() {
            Ok(guard) => guard,
            Err(_) => return refusal(500, "grain-serve.poisoned", "server lock poisoned"),
        };
        guard.serve(&session_identity, &grain_request, now_unix_secs())
    };
    match serve_result {
        Ok(outcome) => WebResponse {
            status: outcome.response.status,
            // The upstream WebSession HttpResponse carries no content-type; the
            // body is served verbatim (a named residual).
            content_type: "application/octet-stream".to_string(),
            body: outcome.response.body,
        },
        // Durability failed AFTER the workload ran: custody is poisoned and the
        // response is withheld (archive-first means no un-checkpointed acks).
        Err(error) => refusal(500, "grain-serve.custody-refused", &error.to_string()),
    }
}

/// An operable serving daemon over the weld: every connection is served by
/// `http-serve`'s hardened single-connection path
/// ([`serve_http_connection_limited`] — the same `Limits` bounds as
/// [`http_serve::serve_on`]) on an accept loop that can be STOPPED, which the
/// forever-serving `serve_on` cannot. Shutdown sleeps the grain (a durable
/// final checkpoint) and returns the custody anchor the operator persists.
pub struct GrainServeDaemon {
    local_addr: SocketAddr,
    server: Arc<Mutex<GrainServer>>,
    stop: Arc<AtomicBool>,
    accept_thread: Option<JoinHandle<()>>,
}

impl GrainServeDaemon {
    /// Serve `server` behind `gate` on an already-bound listener. Bind policy
    /// (loopback vs gated public exposure) belongs to the operated caller; the
    /// mechanism here serves whatever listener it is handed.
    pub fn spawn_on(
        listener: TcpListener,
        gate: Arc<dyn TransportGate>,
        server: GrainServer,
        limits: Limits,
    ) -> Result<Self, GrainServeError> {
        let local_addr = listener
            .local_addr()
            .map_err(|error| GrainServeError::Transport(error.to_string()))?;
        let server = Arc::new(Mutex::new(server));
        let stop = Arc::new(AtomicBool::new(false));
        let handler = Arc::new(grain_handler(Arc::clone(&server), gate));
        let accept_stop = Arc::clone(&stop);
        let accept_thread = std::thread::spawn(move || {
            for stream in listener.incoming() {
                if accept_stop.load(Ordering::SeqCst) {
                    break;
                }
                let Ok(stream) = stream else { continue };
                let handler = Arc::clone(&handler);
                let limits = limits.clone();
                std::thread::spawn(move || {
                    let _ = serve_http_connection_limited(stream, handler.as_ref(), &limits);
                });
            }
        });
        Ok(Self {
            local_addr,
            server,
            stop,
            accept_thread: Some(accept_thread),
        })
    }

    /// Bind `addr` and serve. See [`spawn_on`](Self::spawn_on) for the policy
    /// note: the operated caller decides WHAT address is safe to bind.
    pub fn spawn(
        addr: SocketAddr,
        gate: Arc<dyn TransportGate>,
        server: GrainServer,
        limits: Limits,
    ) -> Result<Self, GrainServeError> {
        let listener = TcpListener::bind(addr)
            .map_err(|error| GrainServeError::Transport(error.to_string()))?;
        Self::spawn_on(listener, gate, server, limits)
    }

    pub fn local_addr(&self) -> SocketAddr {
        self.local_addr
    }

    /// Stop accepting, join the accept loop, sleep the grain (durably
    /// checkpointing its `/var`), and return the final custody anchor.
    pub fn shutdown(mut self) -> Result<GrainCustodyAnchorV1, GrainServeError> {
        self.stop.store(true, Ordering::SeqCst);
        // Unblock the accept loop with a throwaway connection.
        let _ = TcpStream::connect(self.local_addr);
        if let Some(thread) = self.accept_thread.take() {
            let _ = thread.join();
        }
        let mut server = self
            .server
            .lock()
            .map_err(|_| GrainServeError::Transport("server lock poisoned".to_string()))?;
        server.sleep()
    }
}
