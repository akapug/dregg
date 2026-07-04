//! **Grain serving, welded onto the real `dreggnet-webapp` site surface.**
//!
//! A grain is served as a **hosted cell** through the real DreggNet serving surface —
//! [`dreggnet_webapp::WebRequest`] / [`dreggnet_webapp::WebResponse`] /
//! [`dreggnet_webapp::SiteRegistry`], the *exact* surface the httpe
//! `dreggnet-gateway` `SiteHostHandler` adopts (the gateway reads the `Host` header
//! off the socket and calls `SiteRegistry::resolve`/`serve_site`; on Linux it fronts
//! this same surface — the macOS dev build can't compile the httpe net stack, so the
//! weld is expressed against the server-agnostic `dreggnet-webapp` surface the gateway
//! shares). Routing is by the real [`dreggnet_webapp::site_name_from_host`] (the
//! `<name>.example.com` wildcard), and the grain's identity headers
//! (`X-Sandstorm-*`) are derived from the holder's **real** `dga1_` capability via
//! [`crate::webauth_rail`].
//!
//! Two serving shapes, both real:
//!
//! 1. [`serve_grain`] — a live grain request: route by host → derive permissions from
//!    the presented `dga1_` cap → run the handler on the real `dreggnet-exec` tier →
//!    a [`WebResponse`]. This is the dynamic, authenticated serving path.
//! 2. [`publish_grain_snapshot`] — the **verifiable-serving** differentiator: publish
//!    the grain's served bytes as a [`dreggnet_webapp::SiteCell`] through the real,
//!    cap-gated, receipted [`SiteRegistry::publish`] turn, so a visitor re-witnesses
//!    that what they were served binds to a committed cell (the host cannot lie about
//!    what it served).

use dreggnet_webapp::{
    site_name_from_host, HttpMethod, PublishCap, PublishError, PublishReceipt, SiteContent,
    SiteRegistry, WebRequest, WebResponse,
};
use dreggnet_webauth::cred::PublicKey;

use crate::bridge::{uri_encode_component, BridgedRequest, Method};
use crate::cell::Umem;
use crate::exec_workload::ExecGrainWorkload;
use crate::webauth_rail::derive_permissions;

/// The grain `<name>.example.com` a `Host` header routes to, if any — the real
/// wildcard routing the gateway uses (`<name>.example.com`, bare-label local
/// testing, apex/`www`/multi-label rejected). `None` ⇒ the host does not name a grain.
pub fn grain_name_for_host(host: &str) -> Option<String> {
    site_name_from_host(host)
}

fn to_bridge_method(m: HttpMethod) -> Option<Method> {
    match m {
        HttpMethod::Get | HttpMethod::Head => Some(Method::Get),
        HttpMethod::Post => Some(Method::Post),
        HttpMethod::Put => Some(Method::Put),
        HttpMethod::Delete => Some(Method::Delete),
        // The grain http-bridge `WebSession` surface carries get/post/put/delete;
        // PATCH/OPTIONS are not part of it.
        HttpMethod::Patch | HttpMethod::Options => None,
    }
}

/// Who is presenting, and what they hold — the real-rail session for a served grain
/// request. The capability is a real `dga1_` token; its authority is the host root's
/// signature, never a struct the caller fabricated.
pub struct GrainSession<'a> {
    pub user_id: &'a str,
    pub username: &'a str,
    pub session_id: &'a str,
    /// The presenter's subject the cap is sealed to (the `subject` caveat).
    pub presenter_subject: &'a str,
    /// The presented `dga1_…` grain capability.
    pub token: &'a str,
}

/// **Serve one live grain request** through the real surface. Routes by `host` to the
/// grain, derives the `X-Sandstorm-Permissions` from the presented `dga1_` cap on the
/// real `webauth` rail, injects the `X-Sandstorm-*` identity headers, runs the grain
/// handler on the real `dreggnet-exec` tier, commits the new `/var` `data_root`, and
/// returns a real [`WebResponse`]. Fail-closed: a host that does not name this grain,
/// or a cap that grants no facet (forged / wrong-grain / non-owner / expired), is
/// answered with no grain effect.
#[allow(clippy::too_many_arguments)]
pub fn serve_grain(
    host: &str,
    req: &WebRequest,
    grain_cell_id: &str,
    declared_permissions: &[String],
    session: &GrainSession<'_>,
    host_pub: &PublicKey,
    workload: &ExecGrainWorkload,
    var: &mut Umem,
    now: u64,
) -> WebResponse {
    // Route: the Host header must name this grain (the wildcard routing).
    match grain_name_for_host(host) {
        Some(name) if grain_matches(&name, grain_cell_id) => {}
        _ => return WebResponse::error(404, "no such grain"),
    }

    let method = match to_bridge_method(req.method) {
        Some(m) => m,
        None => return WebResponse::error(405, "method not supported by the grain session"),
    };

    // The cap lattice (real rail) decides the permission set — derived, not asserted.
    let permissions = derive_permissions(
        session.token,
        host_pub,
        grain_cell_id,
        session.presenter_subject,
        declared_permissions,
        now,
    );
    if permissions.is_empty() {
        // No facet granted: forged / wrong-grain / non-owner / expired / unauthorized.
        return WebResponse::error(403, "forbidden");
    }

    let bridged = bridged_request(method, &req.path, &req.body, session, &permissions);
    let run = workload.run(&bridged, var);
    let _committed = var.commit();
    let content_type = "text/plain; charset=utf-8".to_string();
    WebResponse {
        status: run.response.status,
        content_type,
        body: run.response.body,
    }
}

/// The grain's served bytes published as a hosted cell — the verifiable-serving step.
/// Publishes through the real, cap-gated, receipted [`SiteRegistry::publish`] turn, so
/// the served snapshot is a committed [`dreggnet_webapp::SiteCell`] a visitor can
/// re-witness. Returns the publish receipt (the witnessed turn artifact).
pub fn publish_grain_snapshot(
    registry: &SiteRegistry,
    owner: &str,
    name: &str,
    path: &str,
    body: impl Into<Vec<u8>>,
) -> Result<PublishReceipt, PublishError> {
    let cap = PublishCap::for_site(owner, name);
    let content = SiteContent::new().with(path, body);
    registry.publish(&cap, name, content)
}

/// Build the bridged request with the cap-derived `X-Sandstorm-*` headers (the
/// identity contract: the app reads who is calling + what they may do from these,
/// never an ambient identity the host asserts).
fn bridged_request(
    method: Method,
    path: &str,
    body: &[u8],
    session: &GrainSession<'_>,
    permissions: &[String],
) -> BridgedRequest {
    let mut facets = permissions.to_vec();
    facets.sort();
    let mut headers = std::collections::BTreeMap::new();
    headers.insert("X-Sandstorm-User-Id".into(), session.user_id.to_string());
    headers.insert(
        "X-Sandstorm-Username".into(),
        uri_encode_component(session.username),
    );
    headers.insert(
        "X-Sandstorm-Session-Id".into(),
        session.session_id.to_string(),
    );
    headers.insert("X-Sandstorm-Permissions".into(), facets.join(","));
    BridgedRequest {
        method,
        path: path.to_string(),
        body: body.to_vec(),
        headers,
    }
}

/// Whether a routed `<name>` names this grain cell. The wildcard label is the grain's
/// short name; the cell id is `cell:<name>` or carries the name as its tail label.
fn grain_matches(name: &str, grain_cell_id: &str) -> bool {
    grain_cell_id == name
        || grain_cell_id == format!("cell:{name}")
        || grain_cell_id
            .rsplit([':', '/'])
            .next()
            .map(|tail| tail == name)
            .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grain::SandboxTier;
    use crate::webauth_rail::HostAuthority;

    fn python3_available() -> bool {
        std::process::Command::new("python3")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    fn declared() -> Vec<String> {
        vec!["view".into(), "edit".into()]
    }

    #[test]
    fn routing_is_the_real_wildcard() {
        assert_eq!(
            grain_name_for_host("etherpad.example.com"),
            Some("etherpad".to_string())
        );
        assert_eq!(grain_name_for_host("example.com"), None);
        assert_eq!(grain_name_for_host("www.example.com"), None);
    }

    #[test]
    fn serve_a_grain_request_over_the_real_surface() {
        if !python3_available() {
            eprintln!("skip: no python3 on PATH");
            return;
        }
        let host = HostAuthority::from_seed([21u8; 32]);
        let grain = "cell:etherpad";
        let token = host
            .mint_grain_cap(grain, "u:alice", &["view", "edit"], None)
            .encode();
        let session = GrainSession {
            user_id: "u:alice",
            username: "Alice",
            session_id: "s:1",
            presenter_subject: "u:alice",
            token: &token,
        };
        let workload = ExecGrainWorkload::notes(SandboxTier::Caged);
        let mut var = Umem::new();

        // POST a note through the real serving surface (real WebRequest → real exec).
        let post = serve_grain(
            "etherpad.example.com",
            &WebRequest::new(HttpMethod::Post, "/pad/welcome", b"hello dregg".to_vec()),
            grain,
            &declared(),
            &session,
            &host.public(),
            &workload,
            &mut var,
            1000,
        );
        assert_eq!(post.status, 200);

        // GET it back.
        let get = serve_grain(
            "etherpad.example.com",
            &WebRequest::new(HttpMethod::Get, "/pad/welcome", Vec::new()),
            grain,
            &declared(),
            &session,
            &host.public(),
            &workload,
            &mut var,
            1000,
        );
        assert_eq!(get.status, 200);
        assert_eq!(get.body, b"hello dregg");
    }

    #[test]
    fn a_request_to_an_unrouted_host_is_404() {
        let host = HostAuthority::from_seed([22u8; 32]);
        let token = host
            .mint_grain_cap("cell:etherpad", "u:alice", &["view"], None)
            .encode();
        let session = GrainSession {
            user_id: "u:alice",
            username: "Alice",
            session_id: "s:1",
            presenter_subject: "u:alice",
            token: &token,
        };
        let workload = ExecGrainWorkload::notes(SandboxTier::Caged);
        let mut var = Umem::new();
        let r = serve_grain(
            "example.com", // the apex names no grain
            &WebRequest::new(HttpMethod::Get, "/", Vec::new()),
            "cell:etherpad",
            &declared(),
            &session,
            &host.public(),
            &workload,
            &mut var,
            1000,
        );
        assert_eq!(r.status, 404);
    }

    #[test]
    fn a_forged_cap_is_403_at_the_serving_surface() {
        let host = HostAuthority::from_seed([23u8; 32]);
        let attacker = HostAuthority::from_seed([200u8; 32]);
        let forged = attacker
            .mint_grain_cap("cell:etherpad", "u:mallory", &["view", "edit"], None)
            .encode();
        let session = GrainSession {
            user_id: "u:mallory",
            username: "mallory",
            session_id: "s:x",
            presenter_subject: "u:mallory",
            token: &forged,
        };
        let workload = ExecGrainWorkload::notes(SandboxTier::Caged);
        let mut var = Umem::new();
        let r = serve_grain(
            "etherpad.example.com",
            &WebRequest::new(HttpMethod::Post, "/pwn", b"x".to_vec()),
            "cell:etherpad",
            &declared(),
            &session,
            &host.public(),
            &workload,
            &mut var,
            1000,
        );
        // The forged cap (not host-rooted) grants nothing → 403, nothing persisted.
        assert_eq!(r.status, 403);
        assert!(var.is_empty());
    }

    #[test]
    fn the_served_snapshot_is_published_and_re_witnessable() {
        let registry = SiteRegistry::new();
        let receipt = publish_grain_snapshot(
            &registry,
            "u:alice",
            "etherpad",
            "/index.html",
            b"<h1>served from a grain</h1>".to_vec(),
        )
        .expect("publish the grain snapshot");
        assert_eq!(receipt.name, "etherpad");
        assert_eq!(receipt.owner, "u:alice");
        // And it serves back through the real registry serving path.
        let resp = registry.serve_site(
            "etherpad",
            &WebRequest::new(HttpMethod::Get, "/index.html", Vec::new()),
        );
        assert_eq!(resp.status, 200);
        assert_eq!(resp.body, b"<h1>served from a grain</h1>");
    }
}
