//! Runtime configuration for the console server, read from the environment.

use std::time::Duration;

/// The console server configuration.
#[derive(Clone, Debug)]
pub struct ConsoleConfig {
    /// Address to bind (`CONSOLE_BIND`, default `0.0.0.0:8095`).
    pub bind: String,
    /// The PUBLIC path the webauth login/logout flow is reachable at, as the
    /// browser sees it through Caddy (`CONSOLE_LOGIN_BASE`, e.g. `/.dregg-auth`).
    /// Used for the sign-out link + the deny message.
    pub login_base: String,
    /// When set (`CONSOLE_REQUIRE_CAP`, e.g. `console-user`), every non-liveness
    /// request must arrive carrying the `X-Dregg-Cap` the `dreggnet-webauth`
    /// forward-auth verified AND an `X-Dregg-Subject` (the cap holder) — the
    /// production fail-closed posture (internalizes the edge gate). A break-glass
    /// admit is always honored. Unset (default) trusts the edge.
    pub require_cap: Option<String>,
    /// A fallback subject for LOCAL DEV ONLY (`CONSOLE_DEV_SUBJECT`): when
    /// `require_cap` is UNSET and no `X-Dregg-Subject` header is present, the
    /// console scopes to this subject so the page is browsable without the live
    /// webauth edge. Ignored entirely once `require_cap` is set (production never
    /// trusts a configured/spoofable subject — only the verified header).
    pub dev_subject: Option<String>,
    /// The live read-API config. When [`ReadApi::is_live`], the console serves
    /// from a [`crate::source::LiveSource`] that aggregates the real resource
    /// surfaces; otherwise it serves the deterministic fixtures.
    pub read_api: ReadApi,
}

/// Where the console reads the live resource surfaces FROM (the reviewed-go
/// deploy step). Each surface is an HTTP `GET` returning the resource records;
/// the base is typically the gateway/aggregator that exposes the registry list
/// endpoints. A surface left `None` (unset / unreachable) contributes nothing —
/// honest, never fabricated, and the cap-scope still drops everyone else's cells.
#[derive(Clone, Debug, Default)]
pub struct ReadApi {
    /// Turn on the live source (`CONSOLE_LIVE=1`, or any surface URL set).
    pub live: bool,
    /// Base URL whose list endpoints are read when a per-surface URL is unset
    /// (`CONSOLE_READ_API`, e.g. `http://gateway:8080`).
    pub base: Option<String>,
    /// `GET → [SiteCell]` (`CONSOLE_SITES_URL`, default `{base}/api/sites`).
    pub sites_url: Option<String>,
    /// `GET → [ServerRecord]` (`CONSOLE_SERVERS_URL`, default `{base}/api/servers`).
    pub servers_url: Option<String>,
    /// `GET → [AgentView]` (`CONSOLE_AGENTS_URL`, default `{base}/api/agents`).
    pub agents_url: Option<String>,
    /// `GET → [DomainBinding]` (`CONSOLE_DOMAINS_URL`, default `{base}/api/domains`).
    pub domains_url: Option<String>,
    /// `GET → [BucketCell]` (`CONSOLE_BUCKETS_URL`, default `{base}/api/buckets`).
    pub buckets_url: Option<String>,
    /// `GET → [SpendEntry]` (`CONSOLE_SPEND_URL`, default `{base}/api/billing/spend`).
    pub spend_url: Option<String>,
    /// `GET → {subject: balance}` (`CONSOLE_BALANCES_URL`, default
    /// `{base}/api/billing/balances`).
    pub balances_url: Option<String>,
    /// An optional bearer the console presents to cap-gated read surfaces
    /// (`CONSOLE_READ_BEARER`).
    pub bearer: Option<String>,
    /// Per-surface request timeout.
    pub timeout: Duration,
}

impl ReadApi {
    /// Whether the console should serve from the live source.
    pub fn is_live(&self) -> bool {
        self.live
            && (self.base.is_some()
                || self.sites_url.is_some()
                || self.servers_url.is_some()
                || self.agents_url.is_some()
                || self.domains_url.is_some()
                || self.buckets_url.is_some()
                || self.spend_url.is_some()
                || self.balances_url.is_some())
    }

    /// Resolve a surface URL: the explicit override, else `{base}{path}`.
    pub fn surface(&self, explicit: &Option<String>, path: &str) -> Option<String> {
        explicit.clone().or_else(|| {
            self.base
                .as_ref()
                .map(|b| format!("{}{}", b.trim_end_matches('/'), path))
        })
    }
}

impl Default for ConsoleConfig {
    fn default() -> Self {
        Self {
            bind: "0.0.0.0:8095".to_string(),
            login_base: String::new(),
            require_cap: None,
            dev_subject: None,
            read_api: ReadApi {
                timeout: Duration::from_millis(2000),
                ..ReadApi::default()
            },
        }
    }
}

impl ConsoleConfig {
    /// Read configuration from the environment.
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Some(b) = non_empty("CONSOLE_BIND") {
            cfg.bind = b;
        }
        if let Some(lb) = non_empty("CONSOLE_LOGIN_BASE") {
            cfg.login_base = lb.trim_end_matches('/').to_string();
        }
        cfg.require_cap = non_empty("CONSOLE_REQUIRE_CAP");
        cfg.dev_subject = non_empty("CONSOLE_DEV_SUBJECT");

        let api = &mut cfg.read_api;
        api.base = non_empty("CONSOLE_READ_API");
        api.sites_url = non_empty("CONSOLE_SITES_URL");
        api.servers_url = non_empty("CONSOLE_SERVERS_URL");
        api.agents_url = non_empty("CONSOLE_AGENTS_URL");
        api.domains_url = non_empty("CONSOLE_DOMAINS_URL");
        api.buckets_url = non_empty("CONSOLE_BUCKETS_URL");
        api.spend_url = non_empty("CONSOLE_SPEND_URL");
        api.balances_url = non_empty("CONSOLE_BALANCES_URL");
        api.bearer = non_empty("CONSOLE_READ_BEARER");
        if let Some(ms) = non_empty("CONSOLE_READ_TIMEOUT_MS").and_then(|s| s.parse::<u64>().ok()) {
            api.timeout = Duration::from_millis(ms);
        }
        // Live when explicitly enabled, or implicitly when any surface is wired.
        api.live = std::env::var("CONSOLE_LIVE")
            .map(|v| v == "1")
            .unwrap_or(false)
            || api.base.is_some();

        cfg
    }
}

fn non_empty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|v| !v.trim().is_empty())
}
