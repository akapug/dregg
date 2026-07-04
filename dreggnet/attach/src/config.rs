//! Runtime configuration for the web-attach server, read from the environment.

/// The web-attach server configuration.
#[derive(Clone, Debug)]
pub struct AttachConfig {
    /// Address to bind (`ATTACH_BIND`, default `0.0.0.0:8100`).
    pub bind: String,
    /// The PUBLIC path the webauth login/logout flow is reachable at, as the
    /// browser sees it through Caddy (`ATTACH_LOGIN_BASE`, e.g. `/.dregg-auth`).
    /// Used for the sign-out link + the deny message.
    pub login_base: String,
    /// When set (`ATTACH_REQUIRE_CAP`, e.g. `attach-user`), every non-liveness
    /// request must arrive carrying the `X-Dregg-Cap` the `dreggnet-webauth`
    /// forward-auth verified AND an `X-Dregg-Subject` (the cap holder) — the
    /// production fail-closed posture (internalizes the edge gate). A break-glass
    /// admit is always honored. Unset (default) trusts the edge.
    pub require_cap: Option<String>,
    /// A fallback subject for LOCAL DEV ONLY (`ATTACH_DEV_SUBJECT`): when
    /// `require_cap` is UNSET and no `X-Dregg-Subject` header is present, the
    /// attach scopes to this subject so the page is drivable without the live
    /// webauth edge. Ignored entirely once `require_cap` is set (production never
    /// trusts a configured/spoofable subject — only the verified header).
    pub dev_subject: Option<String>,
    /// The default budget the goal box is pre-filled with (`ATTACH_DEFAULT_BUDGET`).
    pub default_budget: i64,
    /// The break-glass shared secret (`ATTACH_BREAK_GLASS`). When set, a request may
    /// skip the `require_cap` gate ONLY if it carries `X-Dregg-Break-Glass: <this
    /// exact secret>` — an operator escape hatch that a tenant cannot forge. When
    /// UNSET (default) break-glass is DISABLED entirely (fail-closed): there is NO
    /// header value a caller can send to bypass the cap gate. (Closes the prior
    /// `X-Dregg-Auth: break-glass` self-admit, which any client could set.)
    pub break_glass: Option<String>,
    /// The live hosted-session backend (the reviewed-go deploy step). When set
    /// (`ATTACH_LIVE_BACKEND`), the server would drive sessions through the live
    /// Hermes/Kimi brain over a real confined workdir instead of the demo planner.
    /// NAMED, not wired here — the demo driver is the shipped, green path.
    pub live_backend: Option<String>,
}

impl Default for AttachConfig {
    fn default() -> Self {
        Self {
            bind: "0.0.0.0:8100".to_string(),
            login_base: String::new(),
            require_cap: None,
            dev_subject: None,
            default_budget: 50,
            break_glass: None,
            live_backend: None,
        }
    }
}

impl AttachConfig {
    /// Read configuration from the environment.
    pub fn from_env() -> Self {
        let mut cfg = Self::default();
        if let Some(b) = non_empty("ATTACH_BIND") {
            cfg.bind = b;
        }
        if let Some(lb) = non_empty("ATTACH_LOGIN_BASE") {
            cfg.login_base = lb.trim_end_matches('/').to_string();
        }
        cfg.require_cap = non_empty("ATTACH_REQUIRE_CAP");
        cfg.dev_subject = non_empty("ATTACH_DEV_SUBJECT");
        cfg.break_glass = non_empty("ATTACH_BREAK_GLASS");
        if let Some(n) = non_empty("ATTACH_DEFAULT_BUDGET").and_then(|s| s.parse::<i64>().ok()) {
            cfg.default_budget = n.max(1);
        }
        cfg.live_backend = non_empty("ATTACH_LIVE_BACKEND");
        cfg
    }
}

fn non_empty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|v| !v.trim().is_empty())
}
