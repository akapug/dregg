//! The dregg **http-bridge shim** — run an `.spk` grain as a served workload.
//!
//! The key fact the integration turns on (plan §1.5): the vast majority of catalog
//! apps are *not* native Cap'n Proto — they are an ordinary HTTP server on
//! `localhost:8000` inside the chroot, fronted by `sandstorm-http-bridge`. The bridge
//! owns the grain's single outside socket, implements the `WebSession` capnp
//! interface, and proxies HTTP-over-RPC to that local server — injecting the
//! identity/permission headers (`X-Sandstorm-User-Id`, `-Username`, `-Permissions`,
//! `-Session-Id`) the app reads to know who is calling and what they may do.
//!
//! The dregg shim is that bridge, with the permission headers **derived from the
//! holder's dregg cap**: the facets of the cap a session presents *become* the
//! `X-Sandstorm-Permissions` value. So the app's permission model is enforced by the
//! cap lattice (and is witnessed), not by an ambient identity the host asserts.
//!
//! This module is the `WebSession`→HTTP surface + the cap→headers derivation + the
//! grain `/var` ↔ cell umem wiring, exercised in-process. A real grain runs the
//! `.spk` chroot in a `Caged`/`MicroVm` tier (that execution is REVIEWED-GO — see the
//! plan); here a [`GrainWorkload`] stands in for the app's `:8000` server so the
//! shim contract (verbs, headers, persistence) is proven without executing untrusted
//! code. The contract is exactly what a real workload sees.

use std::collections::BTreeMap;

use crate::cell::{DataRoot, Umem};
use crate::limits::ResourceLease;
use crate::net::{EgressDecision, NetworkPolicy};
use crate::powerbox::{DreggCapRef, RestoreError, SealKey, SturdyRef};

/// Percent-encode a string exactly as `sandstorm-http-bridge` does for the
/// `X-Sandstorm-Username` header — `kj::encodeUriComponent`, which is JavaScript's
/// `encodeURIComponent`. Every byte outside the unreserved set `A-Za-z0-9-_.!~*'()`
/// is emitted as `%XX` (uppercase hex of the UTF-8 byte). Confirmed verbatim
/// against `capnproto/c++/src/kj/encoding.c++`. A display name with a space or any
/// non-ASCII character must arrive at the app encoded this way, or our header bytes
/// diverge from the real bridge's.
pub(crate) fn uri_encode_component(s: &str) -> String {
    fn unreserved(b: u8) -> bool {
        b.is_ascii_alphanumeric()
            || matches!(
                b,
                b'-' | b'_' | b'.' | b'!' | b'~' | b'*' | b'\'' | b'(' | b')'
            )
    }
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        if unreserved(b) {
            out.push(b as char);
        } else {
            out.push('%');
            out.push(
                char::from_digit((b >> 4) as u32, 16)
                    .unwrap()
                    .to_ascii_uppercase(),
            );
            out.push(
                char::from_digit((b & 0x0f) as u32, 16)
                    .unwrap()
                    .to_ascii_uppercase(),
            );
        }
    }
    out
}

/// An HTTP method the `WebSession` surface carries (`web-session.capnp`: get / post /
/// put / delete / …). The non-GET verbs matter for apps like Davros (WebDAV).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Method {
    Get,
    Post,
    Put,
    Delete,
}

/// An HTTP request entering the grain (after the gateway routes the session to it).
#[derive(Clone, Debug)]
pub struct HttpRequest {
    pub method: Method,
    /// The path within the grain (`/`, `/pad/x`, …).
    pub path: String,
    pub body: Vec<u8>,
}

impl HttpRequest {
    pub fn get(path: impl Into<String>) -> Self {
        HttpRequest {
            method: Method::Get,
            path: path.into(),
            body: Vec::new(),
        }
    }
    pub fn post(path: impl Into<String>, body: impl Into<Vec<u8>>) -> Self {
        HttpRequest {
            method: Method::Post,
            path: path.into(),
            body: body.into(),
        }
    }
}

/// The grain's HTTP response (`web-session.capnp:WebSession.Response`, simplified).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HttpResponse {
    pub status: u16,
    pub body: Vec<u8>,
}

impl HttpResponse {
    pub fn ok(body: impl Into<Vec<u8>>) -> Self {
        HttpResponse {
            status: 200,
            body: body.into(),
        }
    }
    pub fn forbidden() -> Self {
        HttpResponse {
            status: 403,
            body: b"forbidden".to_vec(),
        }
    }
}

/// The request as it reaches the app's `:8000` server — the bridge has injected the
/// `X-Sandstorm-*` headers derived from the session's dregg cap. The app reads these
/// to learn the caller and their permissions, never raw identities.
#[derive(Clone, Debug)]
pub struct BridgedRequest {
    pub method: Method,
    pub path: String,
    pub body: Vec<u8>,
    /// `X-Sandstorm-User-Id` / `-Username` / `-Permissions` / `-Session-Id`.
    pub headers: BTreeMap<String, String>,
}

impl BridgedRequest {
    /// The permission set the bridge handed the app (`X-Sandstorm-Permissions`),
    /// parsed back into the facet list — what the app is allowed to do this request.
    pub fn permissions(&self) -> Vec<String> {
        self.headers
            .get("X-Sandstorm-Permissions")
            .filter(|s| !s.is_empty())
            .map(|s| s.split(',').map(|p| p.to_string()).collect())
            .unwrap_or_default()
    }

    fn has(&self, facet: &str) -> bool {
        self.permissions().iter().any(|p| p == facet)
    }
}

/// The grain's in-sandbox HTTP app — the `:8000` server the bridge proxies to. Its
/// `/var` is the cell umem heap, passed in so writes persist into the committed cell.
pub trait GrainWorkload {
    /// Serve one request. `var` is the grain's `/var` (the cell umem heap); mutate it
    /// to persist state. The request carries the cap-derived permission headers.
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse;
}

/// The dregg http-bridge: derive identity/permission headers from a session's cap,
/// hand the request to the grain workload over its `/var`, and commit the resulting
/// umem state to a `data_root` (the witnessed checkpoint of what the request changed).
pub struct HttpBridge;

/// The principal a session presents to a grain: who they are + the **host-sealed
/// cap token** they present over this grain. The cap is NOT trusted as a bare struct
/// (a caller can fabricate any `DreggCapRef`); it is the [`SturdyRef`] the host sealed
/// under its [`SealKey`], and its authenticity is re-verified at [`HttpBridge::serve`]
/// before any facet is honored (red-team #H-1). The restored cap's facets become the
/// app's permissions.
#[derive(Clone, Debug)]
pub struct Session {
    pub user_id: String,
    pub username: String,
    pub session_id: String,
    /// The persisted, host-sealed cap token this session presents (`dga1_…`).
    pub sturdyref: SturdyRef,
    /// The key the presenter claims — must be the owner the token is sealed to.
    pub presenter_key: String,
}

impl Session {
    /// Build a session from a host-sealed cap, sealing `cap` to `presenter` under the
    /// host [`SealKey`]. This is the only honest way to obtain a session: the cap's
    /// authority is the host's seal, not a self-asserted struct.
    pub fn sealed(
        user_id: impl Into<String>,
        username: impl Into<String>,
        session_id: impl Into<String>,
        cap: &DreggCapRef,
        presenter: impl Into<String>,
        seal: &SealKey,
    ) -> Session {
        let presenter = presenter.into();
        let sturdyref = cap.seal_for(presenter.clone(), seal);
        Session {
            user_id: user_id.into(),
            username: username.into(),
            session_id: session_id.into(),
            sturdyref,
            presenter_key: presenter,
        }
    }

    /// The **authentic** cap this session carries: restore its SturdyRef under the host
    /// [`SealKey`] and the claimed presenter. A token this host did not seal (forged),
    /// one tampered, or one presented by a non-owner returns an error — there is no way
    /// to derive authority from a bare struct.
    pub fn authentic_cap(&self, seal: &SealKey) -> Result<DreggCapRef, RestoreError> {
        self.sturdyref.restore(&self.presenter_key, seal)
    }
}

/// The result of serving one request through the bridge: the app's response plus the
/// new committed `data_root` (so the caller can record the witnessed state change).
#[derive(Clone, Debug)]
pub struct Served {
    pub response: HttpResponse,
    pub new_data_root: DataRoot,
}

impl HttpBridge {
    /// Build the bridged request: inject the `X-Sandstorm-*` headers from the session
    /// and its cap (the cap facets → `X-Sandstorm-Permissions`). This is the core of
    /// the bridge's identity contract — the app never sees a raw identity, only these.
    ///
    /// The four headers here are the identity+authority core of the real
    /// `sandstorm-http-bridge` contract, confirmed verbatim against
    /// `sandstorm-http-bridge.c++`: `X-Sandstorm-Permissions` is a comma-separated
    /// list of permission *names* (not indices), and `X-Sandstorm-Username` is
    /// `encodeUriComponent`-encoded (so a display name with a space or non-ASCII
    /// arrives identically to the real bridge). The real bridge additionally sets
    /// optional context headers (`-Tab-Id`, `-Preferred-Handle`, `-User-Picture`,
    /// `-User-Pronouns`, `-Session-Type`, `-Base-Path`, `-Api`); a dregg session
    /// carries no analog for those, so the shim omits them — an app reads only the
    /// headers it needs, and our identity/authority bytes match the real contract.
    /// Derive the `X-Sandstorm-*` headers for an **already-authenticated** cap. The
    /// permission header reflects the restored cap's facets — never a caller-supplied
    /// struct. Callers obtain the authentic cap via [`Session::authentic_cap`].
    fn headers_for(req: &HttpRequest, session: &Session, cap: &DreggCapRef) -> BridgedRequest {
        let mut facets = cap.facets.clone();
        facets.sort();
        let mut headers = BTreeMap::new();
        headers.insert("X-Sandstorm-User-Id".into(), session.user_id.clone());
        headers.insert(
            "X-Sandstorm-Username".into(),
            uri_encode_component(&session.username),
        );
        headers.insert("X-Sandstorm-Session-Id".into(), session.session_id.clone());
        headers.insert("X-Sandstorm-Permissions".into(), facets.join(","));
        BridgedRequest {
            method: req.method,
            path: req.path.clone(),
            body: req.body.clone(),
            headers,
        }
    }

    /// Build the bridged request from a session's **host-sealed** cap: re-verify the
    /// cap's authenticity under the host [`SealKey`] (a forged/tampered/foreign token
    /// is refused), then inject the `X-Sandstorm-*` headers from the *restored* facets.
    /// This is the core of the bridge's identity+authority contract — the app's
    /// permissions are the host seal's, not an ambient identity the host asserts or a
    /// struct the caller fabricated.
    pub fn bridge_request(
        req: &HttpRequest,
        session: &Session,
        seal: &SealKey,
    ) -> Result<BridgedRequest, RestoreError> {
        let cap = session.authentic_cap(seal)?;
        Ok(Self::headers_for(req, session, &cap))
    }

    /// Serve one request end-to-end: **authenticate the presented cap** under the host
    /// [`SealKey`], bridge the headers from its restored facets, run the workload over
    /// the grain's `/var` umem, and commit the new `data_root`. Two gates, both
    /// fail-closed: (1) the cap token must be genuinely host-sealed for its presenter
    /// (a forged/foreign/tampered token confers nothing — red-team #H-1); (2) the
    /// restored cap must name this grain (target = the grain cell id). Either failure
    /// is answered `403` with no effect.
    pub fn serve(
        workload: &dyn GrainWorkload,
        grain_cell_id: &str,
        session: &Session,
        seal: &SealKey,
        var: &mut Umem,
        req: &HttpRequest,
    ) -> Served {
        // (1) Authenticity: only a host-sealed cap carries authority here.
        let cap = match session.authentic_cap(seal) {
            Ok(c) => c,
            Err(_) => {
                return Served {
                    response: HttpResponse::forbidden(),
                    new_data_root: var.commit(),
                };
            }
        };
        // (2) A cap over a different grain confers nothing here (no ambient authority).
        if cap.target != grain_cell_id {
            return Served {
                response: HttpResponse::forbidden(),
                new_data_root: var.commit(),
            };
        }
        let bridged = Self::headers_for(req, session, &cap);
        let response = workload.serve(&bridged, var);
        Served {
            new_data_root: var.commit(),
            response,
        }
    }

    /// **L4 + L7** — serve a request bounded by the grain's funded lease. Identical to
    /// [`serve`](Self::serve) but, after the workload mutates `/var`, the new total
    /// storage is admitted against the lease; a write that would exceed the storage
    /// quota is **rolled back** (fail-closed) and answered `507`. A hostile grain
    /// cannot fill the host disk through the only ingress it has.
    pub fn serve_bounded(
        workload: &dyn GrainWorkload,
        grain_cell_id: &str,
        session: &Session,
        seal: &SealKey,
        var: &mut Umem,
        lease: &mut ResourceLease,
        req: &HttpRequest,
    ) -> Served {
        let cap = match session.authentic_cap(seal) {
            Ok(c) => c,
            Err(_) => {
                return Served {
                    response: HttpResponse::forbidden(),
                    new_data_root: var.commit(),
                };
            }
        };
        if cap.target != grain_cell_id {
            return Served {
                response: HttpResponse::forbidden(),
                new_data_root: var.commit(),
            };
        }
        let snapshot = var.clone();
        let bridged = Self::headers_for(req, session, &cap);
        let response = workload.serve(&bridged, var);
        if lease.admit_storage(var.stored_bytes() as u64).is_err() {
            // Over the storage quota — roll the write back and refuse it.
            *var = snapshot;
            return Served {
                response: HttpResponse {
                    status: 507,
                    body: b"insufficient storage: grain over lease quota".to_vec(),
                },
                new_data_root: var.commit(),
            };
        }
        Served {
            new_data_root: var.commit(),
            response,
        }
    }

    /// **L2 + L7** — the bridge is the grain's *only* egress path. Any outbound the
    /// grain attempts is routed through here and checked against its [`NetworkPolicy`].
    /// A grain with no powerbox-granted [`crate::net::OutboundCap`] for `host:port` is
    /// denied (deny-default, no ambient network). There is no other egress surface: a
    /// grain that cannot route through the bridge cannot reach the network at all.
    pub fn egress(policy: &NetworkPolicy, host: &str, port: u16) -> EgressDecision {
        policy.check_outbound(host, port)
    }
}

/// A representative http-bridge app: a permissioned notes store (the shape of
/// Etherpad/Davros — read needs `view`, write needs `edit`). It reads its permissions
/// from the bridge headers and persists notes into `/var` (the cell umem), so the
/// catalog-app contract (verbs + permission gating + persistence) is exercised.
pub struct NotesApp;

impl GrainWorkload for NotesApp {
    fn serve(&self, req: &BridgedRequest, var: &mut Umem) -> HttpResponse {
        let key = format!("notes{}", req.path);
        match req.method {
            Method::Get => {
                if !req.has("view") {
                    return HttpResponse::forbidden();
                }
                match var.get(&key) {
                    Some(b) => HttpResponse::ok(b.to_vec()),
                    None => HttpResponse {
                        status: 404,
                        body: b"not found".to_vec(),
                    },
                }
            }
            Method::Post | Method::Put => {
                if !req.has("edit") {
                    return HttpResponse::forbidden();
                }
                var.put(key, req.body.clone());
                HttpResponse::ok(b"stored".to_vec())
            }
            Method::Delete => {
                if !req.has("edit") {
                    return HttpResponse::forbidden();
                }
                let existed = var.remove(&key);
                HttpResponse::ok(if existed {
                    b"deleted".to_vec()
                } else {
                    b"absent".to_vec()
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::powerbox::SealKey;

    fn host_seal() -> SealKey {
        SealKey::from_secret(b"test-host-secret")
    }

    fn editor_session(grain: &str, seal: &SealKey) -> Session {
        Session::sealed(
            "u:alice",
            "alice",
            "sess:1",
            &DreggCapRef::new(grain, &["view", "edit"]),
            "u:alice",
            seal,
        )
    }
    fn viewer_session(grain: &str, seal: &SealKey) -> Session {
        Session::sealed(
            "u:bob",
            "bob",
            "sess:2",
            &DreggCapRef::new(grain, &["view"]),
            "u:bob",
            seal,
        )
    }

    #[test]
    fn headers_are_derived_from_the_cap_facets() {
        let seal = host_seal();
        let s = editor_session("cell:grain1", &seal);
        let b = HttpBridge::bridge_request(&HttpRequest::get("/x"), &s, &seal).unwrap();
        assert_eq!(b.headers.get("X-Sandstorm-User-Id").unwrap(), "u:alice");
        assert_eq!(
            b.headers.get("X-Sandstorm-Permissions").unwrap(),
            "edit,view"
        );
        assert_eq!(b.permissions(), vec!["edit", "view"]);
    }

    /// The `X-Sandstorm-Username` header is `encodeUriComponent`-encoded, matching
    /// the real `sandstorm-http-bridge` (`kj::encodeUriComponent`). A display name
    /// with a space and a non-ASCII character must arrive percent-encoded exactly as
    /// the real bridge emits it — pinned so the shim's bytes match real WebSession
    /// traffic. Unreserved `A-Za-z0-9-_.!~*'()` pass through untouched.
    #[test]
    fn username_header_is_uri_encoded_like_the_real_bridge() {
        let seal = host_seal();
        let s = Session::sealed(
            "u:zoë",
            "Zoë Smith",
            "sess:1",
            &DreggCapRef::new("cell:grain1", &["view"]),
            "u:zoë",
            &seal,
        );
        let b = HttpBridge::bridge_request(&HttpRequest::get("/x"), &s, &seal).unwrap();
        // 'Z','o' unreserved; 'ë' = UTF-8 C3 AB; ' ' = %20; 'S','m','i','t','h' pass.
        assert_eq!(
            b.headers.get("X-Sandstorm-Username").unwrap(),
            "Zo%C3%AB%20Smith"
        );
        // The User-Id is an opaque id, not URI-encoded (the real bridge leaves it raw).
        assert_eq!(b.headers.get("X-Sandstorm-User-Id").unwrap(), "u:zoë");
        // Unreserved punctuation survives intact.
        let s2 = Session {
            username: "a-b_c.d!e~f*g'h(i)".into(),
            ..s
        };
        let b2 = HttpBridge::bridge_request(&HttpRequest::get("/x"), &s2, &seal).unwrap();
        assert_eq!(
            b2.headers.get("X-Sandstorm-Username").unwrap(),
            "a-b_c.d!e~f*g'h(i)"
        );
    }

    #[test]
    fn a_request_round_trips_through_the_shim() {
        let seal = host_seal();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        // An editor POSTs a note...
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &editor_session(grain, &seal),
            &seal,
            &mut var,
            &HttpRequest::post("/hello", b"hi there".to_vec()),
        );
        assert_eq!(r.response.status, 200);
        // ...and a viewer reads it back through the bridge.
        let r2 = HttpBridge::serve(
            &NotesApp,
            grain,
            &viewer_session(grain, &seal),
            &seal,
            &mut var,
            &HttpRequest::get("/hello"),
        );
        assert_eq!(r2.response.status, 200);
        assert_eq!(r2.response.body, b"hi there");
    }

    #[test]
    fn the_permission_header_gates_the_app() {
        let seal = host_seal();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        // A viewer (no `edit` facet) cannot write — the app reads the header and 403s.
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &viewer_session(grain, &seal),
            &seal,
            &mut var,
            &HttpRequest::post("/x", b"nope".to_vec()),
        );
        assert_eq!(r.response.status, 403);
        // Nothing persisted.
        assert!(var.is_empty());
    }

    #[test]
    fn a_cap_for_another_grain_is_inert() {
        let seal = host_seal();
        let mut var = Umem::new();
        // The session holds a (genuinely host-sealed) cap over a *different* grain —
        // confers nothing here (target mismatch).
        let session = editor_session("cell:OTHER", &seal);
        let r = HttpBridge::serve(
            &NotesApp,
            "cell:grain1",
            &session,
            &seal,
            &mut var,
            &HttpRequest::post("/x", b"x".to_vec()),
        );
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }

    /// **Red-team #H-1 PoC (cap-auth at serve).** A caller fabricates a cap over the
    /// grain with `edit`, but seals it without the host secret (under their own key).
    /// The bridge restores under the HOST seal, the MAC fails, and the request is
    /// refused `403` — the per-grain `target` gate is no longer the only obstacle.
    /// Under the old code (trusting `session.cap` verbatim) this forged cap would have
    /// yielded `X-Sandstorm-Permissions: edit,view` over the named grain.
    #[test]
    fn a_forged_cap_at_the_l7_bridge_is_refused() {
        let host = host_seal();
        let grain = "cell:grain1";
        // The attacker does not hold the host secret.
        let attacker = SealKey::from_secret(b"mallory-guess");
        let forged = DreggCapRef::new(grain, &["view", "edit"]).seal_for("u:mallory", &attacker);
        let session = Session {
            user_id: "u:mallory".into(),
            username: "mallory".into(),
            session_id: "s:x".into(),
            sturdyref: forged,
            presenter_key: "u:mallory".into(),
        };
        let mut var = Umem::new();
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &session,
            &host,
            &mut var,
            &HttpRequest::post("/pwn", b"owned".to_vec()),
        );
        // Not host-sealed → refused, nothing persisted.
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }

    /// A presenter who does not own the (genuinely host-sealed) token cannot use it —
    /// a stolen/leaked token is inert at the bridge.
    #[test]
    fn a_leaked_token_presented_by_a_non_owner_is_refused() {
        let host = host_seal();
        let grain = "cell:grain1";
        // Host seals a cap to alice; mallory steals the token and claims to be its owner.
        let token = DreggCapRef::new(grain, &["view", "edit"]).seal_for("u:alice", &host);
        let session = Session {
            user_id: "u:mallory".into(),
            username: "mallory".into(),
            session_id: "s:y".into(),
            sturdyref: token,
            presenter_key: "u:mallory".into(),
        };
        let mut var = Umem::new();
        let r = HttpBridge::serve(
            &NotesApp,
            grain,
            &session,
            &host,
            &mut var,
            &HttpRequest::get("/secret"),
        );
        assert_eq!(r.response.status, 403);
        assert!(var.is_empty());
    }

    #[test]
    fn grain_state_persists_in_the_cell_data_root() {
        let seal = host_seal();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        let empty_root = var.commit();
        let served = HttpBridge::serve(
            &NotesApp,
            grain,
            &editor_session(grain, &seal),
            &seal,
            &mut var,
            &HttpRequest::post("/doc", b"v1".to_vec()),
        );
        // The write moved the committed data_root (the witnessed state change).
        assert_ne!(served.new_data_root, empty_root);

        // Simulate sleep→wake: a fresh umem restored from the same contents commits
        // to the same root, and the note is still there.
        let mut restored = var.clone();
        assert_eq!(restored.commit(), served.new_data_root);
        let read = HttpBridge::serve(
            &NotesApp,
            grain,
            &viewer_session(grain, &seal),
            &seal,
            &mut restored,
            &HttpRequest::get("/doc"),
        );
        assert_eq!(read.response.body, b"v1");
    }

    #[test]
    fn a_grain_with_no_outbound_cap_cannot_egress() {
        use crate::net::NetworkPolicy;
        // L2/L7: the bridge is the only egress path, and a confined grain has no cap.
        let policy = NetworkPolicy::confined();
        assert!(!HttpBridge::egress(&policy, "evil.example.com", 443).is_allowed());
        assert!(!HttpBridge::egress(&policy, "169.254.169.254", 80).is_allowed());
    }

    #[test]
    fn egress_is_allowed_only_through_a_granted_cap() {
        use crate::net::{NetworkPolicy, OutboundCap};
        let mut policy = NetworkPolicy::confined();
        policy.grant_outbound(OutboundCap::to("api.weather.test", 443));
        // The granted service is reachable through the bridge...
        assert!(HttpBridge::egress(&policy, "api.weather.test", 443).is_allowed());
        // ...but nothing else is.
        assert!(!HttpBridge::egress(&policy, "evil.example.com", 443).is_allowed());
    }

    #[test]
    fn a_storage_bomb_is_refused_and_rolled_back() {
        use crate::limits::ResourceLease;
        let seal = host_seal();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        // A lease that funds only 16 bytes of /var.
        let mut lease = ResourceLease::bounded(u64::MAX, u64::MAX, u64::MAX, 16);
        // A hostile grain tries to write 1 KiB — over its storage quota.
        let big = vec![0u8; 1024];
        let served = HttpBridge::serve_bounded(
            &NotesApp,
            grain,
            &editor_session(grain, &seal),
            &seal,
            &mut var,
            &mut lease,
            &HttpRequest::post("/huge", big),
        );
        // Refused (507) and nothing persisted — the host disk is protected.
        assert_eq!(served.response.status, 507);
        assert!(var.is_empty());
        assert_eq!(lease.storage_bytes_now(), 0);
    }

    #[test]
    fn a_within_quota_write_through_serve_bounded_persists() {
        use crate::limits::ResourceLease;
        let seal = host_seal();
        let grain = "cell:grain1";
        let mut var = Umem::new();
        let mut lease = ResourceLease::bounded(u64::MAX, u64::MAX, u64::MAX, 4096);
        let served = HttpBridge::serve_bounded(
            &NotesApp,
            grain,
            &editor_session(grain, &seal),
            &seal,
            &mut var,
            &mut lease,
            &HttpRequest::post("/ok", b"small".to_vec()),
        );
        assert_eq!(served.response.status, 200);
        assert!(!var.is_empty());
    }
}
