//! Operator-set configuration for the ops dashboard, from `OPS_*` env.
//!
//! Sensible defaults target the compose-internal DreggNet staging stack (the
//! service DNS names + ports the edge compose wires), so an unconfigured deploy on
//! the edge box aggregates the right things out of the box.

use std::time::Duration;

/// Where the ops dashboard reaches each aggregated surface, plus its own gates.
#[derive(Debug, Clone)]
pub struct OpsConfig {
    /// The `host:port` the dashboard binds (default `0.0.0.0:8090`).
    pub bind: String,
    /// The dregg node base URL (federation/consensus/cells/turns/receipts/metrics).
    pub node_url: String,
    /// The gateway base URL (machines + compute + status).
    pub gateway_url: String,
    /// The discord bot's READ API base URL, if deployed. `None` → not aggregated.
    pub bot_url: Option<String>,
    /// The bot's `ADMIN_TOKEN`, to pull its `/admin/api/*` (hermes/users/channels).
    /// `None` → only the bot's public `/api/*` is aggregated.
    pub bot_admin_token: Option<String>,
    /// The Postgres URL the durable `dreggnet_meter` outbox lives in. `None` → the
    /// lease-economy / durable-job view is reported as "not configured".
    pub database_url: Option<String>,
    /// The Docker Engine API unix socket, for log tailing. `None` → logs panel is
    /// reported as "not available" (no socket mounted).
    pub docker_socket: Option<String>,
    /// An OPTIONAL app-level admin token (Bearer or `?token=`), defence-in-depth
    /// UNDER the Caddy admin-password gate. `None` (default) → the app layer is
    /// open and Caddy is the sole gate (the normal browser-behind-Caddy flow).
    pub admin_token: Option<String>,
    /// The gateway apps whose machines are listed (the gateway lists machines
    /// per-app; there is no global list). Default `["demo"]`.
    pub gateway_apps: Vec<String>,
    /// The compute backend's `/health` URL (the node-a agent on
    /// `:8021`, reached over the headscale overlay). `None` → the backend is not
    /// probed and reports "not-configured" (no alert). Reachability is a WARN-level
    /// signal (the backend is a secondary compute path; a refused lease maps to a
    /// lapse, so backend-down is the dominant lease-lapse cause).
    pub backend_url: Option<String>,
    /// The coin-BRIDGE relayer's status endpoint (a JSON serialization of its
    /// `MirrorState`/`StripeMirrorState` — the conservation source of truth).
    /// `None` (default) → the conservation/double-mint signal is reported
    /// un-observed (never a false all-clear); the node-derived mint/burn activity
    /// is aggregated regardless. See `bridge.rs` for the expected shape.
    pub bridge_url: Option<String>,
    /// The Solana cluster RPC for a `getHealth` reachability probe (the
    /// devnet/oracle path). PLAINTEXT only — the ops binary has no TLS closure, so
    /// an `https` RPC is recorded unreachable; point this at a plaintext-proxied
    /// health or rely on the relayer's `solana_reachable`. `None` → not probed.
    pub solana_rpc_url: Option<String>,
    /// The Stripe webhook receiver's health URL (a plain GET). `None` → not probed.
    pub stripe_receiver_url: Option<String>,
    /// An OPTIONAL alert webhook. When set, the background alerter POSTs page/warn
    /// alerts here as JSON `{"text":..,"content":..}` (Slack/Discord-shaped). Plain
    /// HTTP only (the ops binary carries no TLS closure by design) — point it at an
    /// internal http sink, or poll `/api/alerts` for an https destination.
    pub alert_webhook: Option<String>,
    /// How often the background alerter re-evaluates health + (re)fires alerts.
    pub alert_interval: Duration,
    /// The public base URL of the provisioned Grafana (e.g.
    /// `https://grafana.dreggnet.example.com`). `None` → the dashboard's
    /// "deep metrics" cross-links are hidden. The admin portal is the human
    /// "what's going on" view; Grafana is the time-series companion. Deep-links to
    /// a specific board use `<grafana_url>/d/<uid>` (the dashboard uids are stable:
    /// `dreggnet-cloud-health`, `dreggnet-economy`, `dreggnet-compute`, …).
    pub grafana_url: Option<String>,
    /// When set (e.g. `ops-admin`), the app **requires** the dregg capability the
    /// `dreggnet-webauth` forward-auth verified — it fails closed for any request
    /// that does not arrive with a matching `X-Dregg-Cap` header (or a break-glass
    /// `X-Dregg-Auth`). This is defence-in-depth that **internalizes** the gate:
    /// the Caddy `forward_auth webauth:8099 ?cap=ops-admin` is the primary gate,
    /// but with this set the dashboard refuses to serve even if that edge gate is
    /// ever misconfigured away. `None` (default) → trust the edge gate alone.
    /// From `OPS_REQUIRE_CAP`.
    pub require_cap: Option<String>,
    /// The webauth login base (where `/login` + `/logout` live, as Caddy maps it),
    /// for the dashboard's "signed in as … · sign out" control. From
    /// `OPS_LOGIN_BASE`, default `/.dregg-auth` (matches the staging Caddyfile).
    pub login_base: String,
    /// Per-upstream request timeout.
    pub timeout: Duration,
}

impl Default for OpsConfig {
    fn default() -> Self {
        OpsConfig {
            bind: "0.0.0.0:8090".to_string(),
            node_url: "http://dregg-node:8420".to_string(),
            gateway_url: "http://gateway:8080".to_string(),
            bot_url: None,
            bot_admin_token: None,
            database_url: None,
            docker_socket: Some("/var/run/docker.sock".to_string()),
            admin_token: None,
            gateway_apps: vec!["demo".to_string()],
            backend_url: None,
            bridge_url: None,
            solana_rpc_url: None,
            stripe_receiver_url: None,
            alert_webhook: None,
            grafana_url: None,
            require_cap: None,
            login_base: "/.dregg-auth".to_string(),
            alert_interval: Duration::from_secs(30),
            timeout: Duration::from_millis(1500),
        }
    }
}

impl OpsConfig {
    /// Build the config from `OPS_*` (and `DATABASE_URL`) environment variables,
    /// falling back to [`OpsConfig::default`] for anything unset.
    pub fn from_env() -> Self {
        let mut c = OpsConfig::default();
        if let Some(v) = env_nonempty("OPS_NODE_URL") {
            c.node_url = v;
        }
        if let Some(v) = env_nonempty("OPS_GATEWAY_URL") {
            c.gateway_url = v;
        }
        c.bot_url = env_nonempty("OPS_BOT_URL");
        c.bot_admin_token = env_nonempty("OPS_BOT_ADMIN_TOKEN");
        // The durable meter outbox shares the staging Postgres (`DATABASE_URL`).
        c.database_url = env_nonempty("OPS_DATABASE_URL").or_else(|| env_nonempty("DATABASE_URL"));
        if let Some(v) = env_nonempty("OPS_DOCKER_SOCKET") {
            c.docker_socket = Some(v);
        }
        if std::env::var("OPS_NO_DOCKER").is_ok() {
            c.docker_socket = None;
        }
        c.admin_token = env_nonempty("OPS_ADMIN_TOKEN");
        if let Some(v) = env_nonempty("OPS_GATEWAY_APPS") {
            c.gateway_apps = v
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
        }
        if let Some(ms) = env_nonempty("OPS_TIMEOUT_MS").and_then(|s| s.parse::<u64>().ok()) {
            c.timeout = Duration::from_millis(ms);
        }
        c.backend_url = env_nonempty("OPS_BACKEND_URL");
        c.bridge_url = env_nonempty("OPS_BRIDGE_URL");
        c.solana_rpc_url = env_nonempty("OPS_SOLANA_RPC_URL");
        c.stripe_receiver_url = env_nonempty("OPS_STRIPE_RECEIVER_URL");
        c.alert_webhook = env_nonempty("OPS_ALERT_WEBHOOK");
        c.grafana_url =
            env_nonempty("OPS_GRAFANA_URL").map(|u| u.trim_end_matches('/').to_string());
        c.require_cap = env_nonempty("OPS_REQUIRE_CAP");
        if let Some(b) = env_nonempty("OPS_LOGIN_BASE") {
            c.login_base = b.trim_end_matches('/').to_string();
        }
        if let Some(s) = env_nonempty("OPS_ALERT_INTERVAL_SECS").and_then(|s| s.parse::<u64>().ok())
        {
            c.alert_interval = Duration::from_secs(s.max(5));
        }
        c
    }
}

/// A non-empty environment variable, or `None`.
fn env_nonempty(key: &str) -> Option<String> {
    std::env::var(key).ok().filter(|s| !s.is_empty())
}
