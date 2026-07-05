//! Runtime config for the status server, from `STATUS_*` env.
//!
//! Defaults target the compose-internal DreggNet staging stack (the same service
//! DNS names + ports the ops dashboard aggregates), so an unconfigured deploy on
//! the edge box probes the right things out of the box. Everything is optional —
//! an unset surface is simply NOT probed (NotConfigured), never falsely green.

use std::time::Duration;

/// Where the status page reaches each health surface, plus its own bind.
#[derive(Debug, Clone)]
pub struct StatusConfig {
    /// The `host:port` the server binds (default `0.0.0.0:8095`).
    pub bind: String,
    /// The dregg node base URL (`/status` + `/api/federations` + `/metrics`).
    pub node_url: String,
    /// The gateway base URL (`/status`). `None` → not probed.
    pub gateway_url: Option<String>,
    /// The control / orchestrator base URL (`/healthz`). `None` → not probed.
    pub control_url: Option<String>,
    /// The bridge relayer status URL. `None` → conservation reported un-observed.
    pub bridge_url: Option<String>,
    /// The economy conservation URL (a JSON `{"delta_sum": N}` surface). `None` →
    /// conservation derived from the node when possible, else Unknown.
    pub economy_url: Option<String>,
    /// The expected federation committee size (n). Default 5 (the live n=5
    /// federation); overridden by the real `member_count` from `/api/federations`
    /// when reachable.
    pub federation_size: usize,
    /// The serving source: `true` = live HTTP, `false` = a fixture (for demo/embed).
    pub live: bool,
    /// Per-upstream request timeout.
    pub timeout: Duration,
}

impl Default for StatusConfig {
    fn default() -> Self {
        StatusConfig {
            bind: "0.0.0.0:8095".to_string(),
            node_url: "http://dregg-node:8420".to_string(),
            gateway_url: Some("http://gateway:8080".to_string()),
            control_url: None,
            bridge_url: None,
            economy_url: None,
            federation_size: 5,
            live: true,
            timeout: Duration::from_millis(1500),
        }
    }
}

impl StatusConfig {
    /// Build from `STATUS_*` env, falling back to [`StatusConfig::default`].
    pub fn from_env() -> Self {
        let mut c = StatusConfig::default();
        if let Some(v) = env_nonempty("STATUS_BIND") {
            c.bind = v;
        }
        if let Some(v) = env_nonempty("STATUS_NODE_URL") {
            c.node_url = v;
        }
        c.gateway_url = env_nonempty("STATUS_GATEWAY_URL").or(c.gateway_url);
        c.control_url = env_nonempty("STATUS_CONTROL_URL");
        c.bridge_url = env_nonempty("STATUS_BRIDGE_URL");
        c.economy_url = env_nonempty("STATUS_ECONOMY_URL");
        if let Some(n) = env_nonempty("STATUS_FEDERATION_SIZE").and_then(|s| s.parse().ok()) {
            c.federation_size = n;
        }
        if let Some(ms) = env_nonempty("STATUS_TIMEOUT_MS").and_then(|s| s.parse::<u64>().ok()) {
            c.timeout = Duration::from_millis(ms);
        }
        // STATUS_DEMO=1 serves the deterministic healthy fixture (no live surfaces).
        if std::env::var("STATUS_DEMO")
            .map(|v| v == "1")
            .unwrap_or(false)
        {
            c.live = false;
        }
        c
    }
}

/// A non-empty environment variable, or `None`.
fn env_nonempty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|s| !s.is_empty())
}
