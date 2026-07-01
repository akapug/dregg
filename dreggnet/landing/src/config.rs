//! Runtime config for the landing server, from `LANDING_*` env.
//!
//! Everything has a sensible public default so an unconfigured deploy renders a
//! correct page out of the box; the live-edge deploy overrides the public URLs to
//! the real hosts.

/// Where the landing page links/points, plus its own bind.
#[derive(Debug, Clone)]
pub struct LandingConfig {
    /// The `host:port` the server binds (default `0.0.0.0:8096`).
    pub bind: String,
    /// The PUBLIC URL of the status page (the live banner is fetched from its
    /// `/status.json`, and the "live status" link points here).
    pub status_url: String,
    /// The PUBLIC URL of the signed-in customer console (the "sign in" link).
    pub console_url: String,
    /// The docs / quickstart base URL (the "read the docs" link).
    pub docs_url: String,
    /// The public git repository URL (the "verify it yourself / source" link).
    pub repo_url: String,
}

impl Default for LandingConfig {
    fn default() -> Self {
        LandingConfig {
            bind: "0.0.0.0:8096".to_string(),
            status_url: "https://status.example.com".to_string(),
            console_url: "https://console.example.com".to_string(),
            docs_url: "https://example.com/docs".to_string(),
            repo_url: "https://github.com/cmrx64/DreggNet".to_string(),
        }
    }
}

impl LandingConfig {
    /// Build from `LANDING_*` env, falling back to [`LandingConfig::default`].
    pub fn from_env() -> Self {
        let mut c = LandingConfig::default();
        if let Some(v) = env_nonempty("LANDING_BIND") {
            c.bind = v;
        }
        if let Some(v) = env_nonempty("LANDING_STATUS_URL") {
            c.status_url = v;
        }
        if let Some(v) = env_nonempty("LANDING_CONSOLE_URL") {
            c.console_url = v;
        }
        if let Some(v) = env_nonempty("LANDING_DOCS_URL") {
            c.docs_url = v;
        }
        if let Some(v) = env_nonempty("LANDING_REPO_URL") {
            c.repo_url = v;
        }
        c
    }
}

/// A non-empty environment variable, or `None`.
fn env_nonempty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|s| !s.is_empty())
}
