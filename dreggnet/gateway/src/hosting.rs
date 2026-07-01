//! Serve published minisite cells through the gateway — static hosting on
//! `example.com`.
//!
//! This is the gateway-side adoption of [`dreggnet_webapp::hosting`]: where
//! [`crate::WebAppHandler`] is the *dynamic* data plane (routes → polyana
//! handlers), [`SiteHostHandler`] is the *static* data plane — it resolves an
//! inbound request's `Host` (`<name>.example.com`) to a published
//! [`SiteCell`](dreggnet_webapp::hosting::SiteCell) and serves the cell's content,
//! the realization of "a minisite published as a dregg cell, served on example.com."
//!
//! ```text
//!   GET https://<name>.example.com/path
//!        │  Host: <name>.example.com
//!        ▼
//!   SiteHostHandler::dispatch
//!        │  dreggnet_webapp::SiteRegistry::resolve   (host → site cell → asset)
//!        ▼
//!   the asset bytes + content-type written back
//! ```
//!
//! Read-only, public, unauthenticated — a published public site is served to
//! anyone (the publish was the cap-gated, receipted step; reads are free). The
//! registry is shared (`Arc`), so a publish (the control side) becomes visible to
//! the data plane immediately. Like [`crate::WebAppHandler`], the body-bearing
//! entry is [`SiteHostHandler::dispatch`] (the serving loop reads the `Host` line
//! off the socket); the [`Handler::handle`] trait surface reads the `Host` header
//! off the parsed request.
//!
//! ## One data plane, two serving engines (why this loop stays separate)
//!
//! All three static-hosting front-ends share ONE data plane — the
//! [`SiteRegistry`] (resolve `Host` → site cell → asset, metered + lapse-gated in
//! [`SiteRegistry::serve_site`]). What differs is only the serving *entry point*
//! wrapped around it, so they keep distinct loops rather than being force-merged:
//!
//! - **This `SiteHostHandler`** is the GATEWAY edge handler: it implements
//!   [`dreggnet_http::Handler`], the same handler surface the gateway's
//!   machines/storage/webapp handlers register on, and is driven by the gateway
//!   binary's hand-rolled `std::net::TcpListener` loop (`gateway/src/main.rs`),
//!   which calls [`SiteHostHandler::dispatch`] directly with the `Host`/body it
//!   read off the socket.
//! - **`dreggnet_webapp::serve_http`** is the PORTABLE-BINARY loop: its own
//!   cross-platform std `TcpListener` loop, shared (after the de-duplication) by
//!   BOTH portable binaries — `dreggnet-host` (static, over a [`SiteRegistry`])
//!   and `dreggnet-serve` (dynamic, over a polyana `Router`).
//!
//! Both are now plain-`std` loops (the gateway no longer links any third-party
//! HTTP engine); the duplication that was collapsed is the portable std-TCP loop
//! (once copied between the static and dynamic binaries, now one `serve_http`).
//! The gateway's edge handler is a separate entry point over the same registry,
//! not a fourth copy.

use std::sync::Arc;

use dreggnet_http::handler::{Handler, HandlerResult};
use dreggnet_http::{Method, Request, ResponseWriter};

use dregg_domains::{DomainRegistry, LiveDns};
use dreggnet_webapp::hosting::site_name_from_host;
use dreggnet_webapp::{SiteRegistry, WebRequest, WebResponse};

use crate::webresp::{map_method, write};

/// The gateway HTTP handler that serves published minisite cells by `Host` — both the
/// `<name>.example.com` wildcard path and **verified BYO custom domains**.
///
/// It holds the [`SiteRegistry`] (the wildcard data plane) and the
/// [`DomainRegistry`] (the custom-domain control plane). A verified custom `Host`
/// resolves to its bound site cell; everything else falls through to the
/// `<name>.example.com` resolution. Both registries are shared (`Arc`) so a publish
/// or a bind elsewhere is served here without a rebuild.
pub struct SiteHostHandler {
    registry: Arc<SiteRegistry>,
    domains: Arc<DomainRegistry>,
    /// The live DNS resolver the on-demand-TLS `ask` re-confirms a custom domain's
    /// control through. `None` = no live resolver (tests / wildcard-only) → the
    /// `ask` reads only already-proven bindings. Present in production so a cert is
    /// minted only when REAL DNS currently proves control (never a client-asserted
    /// flag). `LiveDns` is cheap to share (a channel to its worker thread).
    resolver: Option<Arc<LiveDns>>,
}

impl SiteHostHandler {
    /// Serve sites published into `registry`, with no custom-domain bindings (an
    /// empty [`DomainRegistry`]). The wildcard-only constructor.
    pub fn new(registry: Arc<SiteRegistry>) -> SiteHostHandler {
        SiteHostHandler::with_domains(registry, Arc::new(DomainRegistry::new()))
    }

    /// Serve sites published into `registry`, routing verified custom domains in
    /// `domains` to their bound site cells. No live resolver — the cert `ask` reads
    /// only already-proven bindings (the test / offline constructor).
    pub fn with_domains(
        registry: Arc<SiteRegistry>,
        domains: Arc<DomainRegistry>,
    ) -> SiteHostHandler {
        SiteHostHandler {
            registry,
            domains,
            resolver: None,
        }
    }

    /// As [`with_domains`](Self::with_domains), but the on-demand-TLS `ask` re-checks
    /// an unproven custom domain against LIVE DNS through `resolver` before minting a
    /// cert — the production constructor.
    pub fn with_domains_and_resolver(
        registry: Arc<SiteRegistry>,
        domains: Arc<DomainRegistry>,
        resolver: Arc<LiveDns>,
    ) -> SiteHostHandler {
        SiteHostHandler {
            registry,
            domains,
            resolver: Some(resolver),
        }
    }

    /// The site registry this handler serves.
    pub fn registry(&self) -> &Arc<SiteRegistry> {
        &self.registry
    }

    /// The custom-domain registry this handler routes verified bindings from.
    pub fn domains(&self) -> &Arc<DomainRegistry> {
        &self.domains
    }

    /// Whether this handler serves `host` — a published `<name>.example.com` site or
    /// a *verified* custom domain. (Routing decision for the serving loop: a host
    /// this returns `true` for goes to the static data plane, not the machines API.)
    pub fn serves_host(&self, host: &str) -> bool {
        let bare = host.split(':').next().unwrap_or(host).trim();
        (bare.ends_with(".example.com") && site_name_from_host(host).is_some())
            || self.domains.site_for_host(host).is_some()
    }

    /// Whether a per-domain certificate should be minted for `host` — the Caddy
    /// on-demand-TLS `ask` decision: a published `<name>.example.com` site OR a
    /// custom domain whose control is **proven against live DNS** (never an
    /// unverified / squatted domain).
    ///
    /// For a custom domain that is not yet proven, this re-queries LIVE DNS through
    /// the configured [`LiveDns`] resolver (the `_dregg-verify.<domain>` TXT / the
    /// `<domain>` CNAME) and mints a cert only if the real record is present — so a
    /// stale or fabricated `Verified` flag, or a domain a tenant does not control,
    /// earns no certificate. (Caddy caches the issued cert, so this on-demand query
    /// runs at most once per cert lifetime.)
    pub fn cert_ok(&self, host: &str) -> bool {
        let wildcard = site_name_from_host(host)
            .map(|name| self.registry.get(&name).is_some())
            .unwrap_or(false);
        if wildcard {
            return true;
        }
        if self.domains.is_verified(host) {
            return true;
        }
        // A bound-but-unproven custom domain: confirm control against live DNS now.
        if let Some(resolver) = &self.resolver {
            // `verify` lowercases/keys the domain; strip any `:port` first.
            let bare = host.split(':').next().unwrap_or(host).trim();
            return self
                .domains
                .verify(bare, resolver.as_ref())
                .map(|b| b.is_verified())
                .unwrap_or(false);
        }
        false
    }

    /// Resolve `host` to a published site and serve `target` against its content.
    ///
    /// A verified custom domain resolves to its bound site cell; otherwise the
    /// `<name>.example.com` path. The serving binary passes the `Host` it read off
    /// the socket; the [`Handler::handle`] trait surface reads it from the request.
    pub fn dispatch(
        &self,
        method: Method,
        host: &str,
        target: &str,
        body: &[u8],
        response: &mut ResponseWriter,
    ) -> HandlerResult {
        let Some(m) = map_method(method) else {
            return write(response, &WebResponse::error(405, "unsupported method"));
        };
        let req = WebRequest::new(m, target, body.to_vec());
        // A verified custom domain serves its bound site; else the wildcard path.
        // Both funnel through `SiteRegistry::serve_site`, so bandwidth is counted
        // (and a lapsed site refused) exactly once regardless of which Host routed.
        let resp = match self.domains.site_for_host(host) {
            Some(name) => self.registry.serve_site(&name, &req),
            None => self.registry.resolve(host, &req),
        };
        write(response, &resp)
    }
}

impl Handler for SiteHostHandler {
    fn handle(&self, request: &Request, response: &mut ResponseWriter) -> HandlerResult {
        let host = request.header("host").unwrap_or("");
        self.dispatch(request.method(), host, request.path(), &[], response)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};

    fn registry_with_blog() -> Arc<SiteRegistry> {
        let reg = SiteRegistry::new();
        let content = SiteContent::new()
            .with("/index.html", "<h1>served on example.com</h1>")
            .with("/style.css", "h1{color:teal}");
        reg.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            content,
        )
        .expect("publish");
        Arc::new(reg)
    }

    fn run(handler: &SiteHostHandler, host: &str, target: &str) -> String {
        let mut buf = vec![0u8; 64 * 1024];
        let mut writer = ResponseWriter::new(&mut buf);
        let res = handler.dispatch(Method::Get, host, target, &[], &mut writer);
        let n = res.bytes_written();
        String::from_utf8_lossy(&buf[..n]).to_string()
    }

    #[test]
    fn serves_the_published_index_by_host() {
        let handler = SiteHostHandler::new(registry_with_blog());
        let raw = run(&handler, "blog.example.com", "/");
        assert!(raw.contains("200 OK"), "raw: {raw}");
        assert!(raw.contains("text/html"), "raw: {raw}");
        assert!(raw.contains("served on example.com"), "raw: {raw}");
    }

    #[test]
    fn serves_css_with_correct_content_type() {
        let handler = SiteHostHandler::new(registry_with_blog());
        let raw = run(&handler, "blog.example.com", "/style.css");
        assert!(raw.contains("200 OK"), "raw: {raw}");
        assert!(raw.contains("text/css"), "raw: {raw}");
    }

    #[test]
    fn unknown_host_is_404() {
        let handler = SiteHostHandler::new(registry_with_blog());
        let raw = run(&handler, "nope.example.com", "/");
        assert!(raw.contains("404 Not Found"), "raw: {raw}");
    }

    #[test]
    fn verified_custom_domain_routes_to_its_bound_site() {
        use dregg_domains::{ChallengeMethod, DOMAINS_CAP, DomainCap, DomainRegistry, MockDns};
        use dreggnet_webauth::cred::RootKey;
        use dreggnet_webauth::grant::mint_caps;

        let registry = registry_with_blog();
        let root = RootKey::from_seed([5u8; 32]);
        let domains = Arc::new(DomainRegistry::with_authority(root.public()));
        let cred = mint_caps(&root, [DOMAINS_CAP], None).encode();
        let r = domains
            .bind(
                &DomainCap::new(cred, "blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .expect("bind");
        let handler = SiteHostHandler::with_domains(registry, Arc::clone(&domains));

        // Unverified: the handler does not serve the custom host (falls through →
        // example.com path, which 404s the unknown host), and no cert is minted.
        assert!(!handler.serves_host("blog.example.com"));
        assert!(!handler.cert_ok("blog.example.com"));
        assert!(run(&handler, "blog.example.com", "/").contains("404"));

        // Verify it (mock DNS), then the custom host serves the bound site cell.
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        domains.verify("blog.example.com", &dns).expect("verify");
        assert!(handler.serves_host("blog.example.com"));
        assert!(handler.cert_ok("blog.example.com"));
        let raw = run(&handler, "blog.example.com", "/");
        assert!(raw.contains("200 OK"), "raw: {raw}");
        assert!(raw.contains("served on example.com"), "raw: {raw}");
    }
}
