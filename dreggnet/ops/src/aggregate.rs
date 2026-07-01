//! Assemble the whole-cloud snapshot by fetching every live read surface.
//!
//! This is the heart of the dashboard: it fetches the dregg node, the gateway, the
//! discord bot's read API, and the durable meter outbox **concurrently-ish but
//! defensively** — each source's reachability is recorded as a [`SourceStatus`],
//! and an unreachable source degrades to `None` data rather than failing the
//! snapshot. The result is one [`CloudSnapshot`] the dashboard renders and the
//! `/api/snapshot` endpoint serves verbatim.

use serde::Serialize;
use serde_json::Value;

use crate::bridge::{self, BridgeView};
use crate::client::http_get;
use crate::config::OpsConfig;
use crate::pg::DurableView;

/// One aggregated upstream's reachability + timing.
#[derive(Debug, Clone, Serialize)]
pub struct SourceStatus {
    /// A human label ("dregg node", "gateway", "discord bot", "postgres").
    pub name: String,
    /// The kind of source ("http" / "postgres").
    pub kind: String,
    /// The target (URL / db host).
    pub target: String,
    /// Whether the source answered.
    pub reachable: bool,
    /// The HTTP status, when applicable.
    pub http_status: Option<u16>,
    /// Round-trip time in milliseconds.
    pub latency_ms: u128,
    /// The error, when unreachable.
    pub error: Option<String>,
}

/// A handful of summary numbers parsed from the node's Prometheus `/metrics`.
#[derive(Debug, Clone, Serialize, Default)]
pub struct MetricsSummary {
    pub turns_submitted: Option<f64>,
    pub turns_executed: Option<f64>,
    pub proofs_verified: Option<f64>,
    pub block_height: Option<f64>,
    pub peers_connected: Option<f64>,
    pub cell_count: Option<f64>,
    /// `dregg_consensus_differential_divergence_total` — the rust↔lean finalized-
    /// order DISAGREEMENT counter. ANY non-zero value is a real consensus-bug
    /// signal (a Rust-side bug or a stale/mismatched Lean archive) and pages.
    pub consensus_divergence: Option<f64>,
    /// `dregg_tau_prefix_shifts_total` — reorg-by-catchup count. EXPECTED/benign
    /// (the identity cursor absorbs it); surfaced as info, never an alert.
    pub tau_prefix_shifts: Option<f64>,
    /// `dregg_gossip_messages_total` — federation gossip volume (all directions
    /// summed). The healthy baseline; the denominator for the rejection ratio.
    pub gossip_messages: Option<f64>,
    /// `dregg_gossip_stream_rejected_total` — inbound gossip streams DROPPED at
    /// the edge (conn-limit / slow-loris / unknown-sender / bad-sig / decode).
    /// 0 in healthy operation; a climbing value is the live edge-gossip-storm
    /// signature (the incident that was invisible until edge fell over). The RATE
    /// is the early warning — Grafana/Prometheus own `rate(...)`; here we carry the
    /// cumulative so the single-pane shows it climb live.
    pub gossip_stream_rejected: Option<f64>,
    /// `dregg_consensus_attested_total` — blocks that reached a quorum of signed
    /// finalization votes (the cross-node AGREEMENT step). A flat rate = a stall.
    pub consensus_attested: Option<f64>,
    /// Mean finality latency (first-vote→quorum) in seconds, derived from the
    /// `dregg_consensus_finality_latency_seconds` summary as `sum / count`. A
    /// climbing mean is a finality slowdown; `None` until the node finalizes once.
    pub finality_latency_avg: Option<f64>,
}

/// One operator-facing alert derived from the snapshot.
#[derive(Debug, Clone, Serialize)]
pub struct Alert {
    /// "page" (wake someone), "warn" (degraded, look soon), or "info" (FYI).
    pub severity: String,
    /// A stable key for de-duplication / suppression (e.g. "consensus_divergence").
    pub key: String,
    /// A human-readable message.
    pub message: String,
}

/// The dregg node's aggregated view.
#[derive(Debug, Clone, Serialize, Default)]
pub struct NodeView {
    pub status: Option<Value>,
    pub federations: Option<Value>,
    pub recent_receipts: Option<Value>,
    pub recent_events: Option<Value>,
    pub metrics: Option<MetricsSummary>,
}

/// The gateway's aggregated view.
#[derive(Debug, Clone, Serialize, Default)]
pub struct GatewayView {
    pub status: Option<Value>,
    /// Machines listed across the configured apps; each carries an injected `app`.
    pub machines: Vec<Value>,
}

/// The discord bot's aggregated view (read API).
#[derive(Debug, Clone, Serialize, Default)]
pub struct BotView {
    pub configured: bool,
    pub reachable: bool,
    pub activity: Option<Value>,
    pub cells: Option<Value>,
    pub receipts: Option<Value>,
    pub hermes: Option<Value>,
}

/// The top-level whole-cloud health rollup (the at-a-glance verdict).
#[derive(Debug, Clone, Serialize)]
pub struct CloudHealth {
    /// "healthy" / "degraded" / "down".
    pub overall: String,
    pub node: String,
    pub gateway: String,
    pub bot: String,
    pub postgres: String,
    /// The compute backend (node-a `:8021/health`): "up"/"down"/"not-configured".
    pub backend: String,
    pub federation_members: Option<u64>,
    pub consensus_live: Option<bool>,
    /// Whether the node reports itself finalizing (its own `healthy` field: store
    /// reachable + consensus live + at least one block). `None` if the node is down.
    pub node_finalizing: Option<bool>,
    /// The rust↔lean differential divergence counter (paging when > 0).
    pub consensus_divergence: Option<f64>,
    /// The tau prefix-shift counter (benign reorg-by-catchup; informational).
    pub tau_prefix_shifts: Option<f64>,
    /// Cumulative federation gossip volume (`dregg_gossip_messages_total`).
    pub gossip_messages: Option<f64>,
    /// Cumulative inbound gossip streams rejected at the edge
    /// (`dregg_gossip_stream_rejected_total`). Climbs during a gossip storm — the
    /// signal that was missing when the edge fell over. WARN when > 0 (the RATE
    /// early-warning + page lives in the Grafana/Prometheus rule).
    pub gossip_stream_rejected: Option<f64>,
    /// Mean finality latency in seconds (first-vote→quorum), `None` until the node
    /// finalizes at least once.
    pub finality_latency_avg: Option<f64>,
    pub machines: Option<u64>,
    pub durable_jobs_in_flight: i64,
    pub total_units_spent: i64,
    pub block_height: Option<u64>,
    pub peers: Option<u64>,
    /// Postgres backend connections in use vs the server ceiling (pressure).
    pub pg_active_connections: Option<i64>,
    pub pg_max_connections: Option<i64>,
    /// The durable database's on-disk size in bytes (disk pressure).
    pub pg_db_size_bytes: Option<i64>,
    /// The coin-bridge relayer status: "up"/"down"/"not-configured".
    pub bridge_relayer: String,
    /// The Solana cluster (devnet) reachability: "up"/"down"/"not-configured".
    pub bridge_solana: String,
    /// The Stripe webhook receiver reachability: "up"/"down"/"not-configured".
    pub bridge_stripe: String,
    /// Whether the bridge conservation invariant was observed AND holds. `None`
    /// when un-observed (no relayer status endpoint) — never a false all-clear.
    pub bridge_conservation_ok: Option<bool>,
    /// Count of bridge mints (`mint`/`bridgemint`) observed in the node event window.
    pub bridge_mints_observed: u64,
    /// The active alerts derived from this snapshot (newest evaluation each build).
    pub alerts: Vec<Alert>,
}

/// The full snapshot the dashboard renders.
#[derive(Debug, Clone, Serialize)]
pub struct CloudSnapshot {
    pub generated_at: String,
    pub health: CloudHealth,
    pub sources: Vec<SourceStatus>,
    pub node: NodeView,
    pub gateway: GatewayView,
    pub bot: BotView,
    pub durable: DurableView,
    pub bridge: BridgeView,
}

impl CloudSnapshot {
    /// Fetch every surface and assemble the snapshot. The `runtime` drives the
    /// (async) Postgres read from this synchronous call.
    pub fn build(cfg: &OpsConfig, runtime: &tokio::runtime::Runtime) -> CloudSnapshot {
        let mut sources = Vec::new();
        let node = fetch_node(cfg, &mut sources);
        let gateway = fetch_gateway(cfg, &mut sources);
        let bot = fetch_bot(cfg, &mut sources);
        let durable = fetch_durable_view(cfg, runtime, &mut sources);
        let backend = fetch_backend(cfg, &mut sources);
        let bridge = bridge::fetch_bridge(cfg, &node, &mut sources);
        let health = roll_up(&node, &gateway, &bot, &durable, backend, &bridge, &sources);

        CloudSnapshot {
            generated_at: now_rfc3339(),
            health,
            sources,
            node,
            gateway,
            bot,
            durable,
            bridge,
        }
    }
}

/// Fetch a JSON endpoint, recording a [`SourceStatus`] and returning the parsed
/// value on a 2xx.
fn get_json(
    name: &str,
    base: &str,
    path: &str,
    cfg: &OpsConfig,
    bearer: Option<&str>,
    sources: &mut Vec<SourceStatus>,
) -> Option<Value> {
    let url = format!("{}{}", base.trim_end_matches('/'), path);
    match http_get(&url, cfg.timeout, bearer) {
        Ok(resp) => {
            let ok = (200..300).contains(&resp.status);
            let val = if ok { resp.json().ok() } else { None };
            sources.push(SourceStatus {
                name: format!("{name} {path}"),
                kind: "http".into(),
                target: url,
                reachable: ok,
                http_status: Some(resp.status),
                latency_ms: resp.elapsed.as_millis(),
                error: if ok {
                    None
                } else {
                    Some(format!("HTTP {}", resp.status))
                },
            });
            val
        }
        Err(e) => {
            sources.push(SourceStatus {
                name: format!("{name} {path}"),
                kind: "http".into(),
                target: url,
                reachable: false,
                http_status: None,
                latency_ms: 0,
                error: Some(e),
            });
            None
        }
    }
}

fn fetch_node(cfg: &OpsConfig, sources: &mut Vec<SourceStatus>) -> NodeView {
    let base = &cfg.node_url;
    let status = get_json("node", base, "/status", cfg, None, sources);
    let federations = get_json("node", base, "/api/federations", cfg, None, sources);
    // Pull a wide window so the historical-log viewer has real history to browse
    // (unknown `limit=` params are ignored by an older node, so this is safe).
    let recent_receipts = get_json("node", base, "/api/receipts?limit=200", cfg, None, sources);
    let recent_events = get_json("node", base, "/api/events?limit=200", cfg, None, sources);

    // /metrics is Prometheus text, not JSON — parse a few summary series.
    let metrics = {
        let url = format!("{}/metrics", base.trim_end_matches('/'));
        match http_get(&url, cfg.timeout, None) {
            Ok(resp) if (200..300).contains(&resp.status) => {
                sources.push(SourceStatus {
                    name: "node /metrics".into(),
                    kind: "http".into(),
                    target: url,
                    reachable: true,
                    http_status: Some(resp.status),
                    latency_ms: resp.elapsed.as_millis(),
                    error: None,
                });
                Some(parse_metrics(&resp.text()))
            }
            Ok(resp) => {
                sources.push(SourceStatus {
                    name: "node /metrics".into(),
                    kind: "http".into(),
                    target: url,
                    reachable: false,
                    http_status: Some(resp.status),
                    latency_ms: resp.elapsed.as_millis(),
                    error: Some(format!("HTTP {}", resp.status)),
                });
                None
            }
            Err(e) => {
                sources.push(SourceStatus {
                    name: "node /metrics".into(),
                    kind: "http".into(),
                    target: url,
                    reachable: false,
                    http_status: None,
                    latency_ms: 0,
                    error: Some(e),
                });
                None
            }
        }
    };

    NodeView {
        status,
        federations,
        recent_receipts,
        recent_events,
        metrics,
    }
}

fn fetch_gateway(cfg: &OpsConfig, sources: &mut Vec<SourceStatus>) -> GatewayView {
    let base = &cfg.gateway_url;
    let status = get_json("gateway", base, "/status", cfg, None, sources);
    // The gateway lists machines per-app; aggregate the configured apps.
    let mut machines = Vec::new();
    for app in &cfg.gateway_apps {
        let path = format!("/v1/apps/{app}/machines");
        if let Some(Value::Array(arr)) = get_json("gateway", base, &path, cfg, None, sources) {
            for mut m in arr {
                if let Some(obj) = m.as_object_mut() {
                    obj.insert("app".into(), Value::String(app.clone()));
                }
                machines.push(m);
            }
        }
    }
    GatewayView { status, machines }
}

fn fetch_bot(cfg: &OpsConfig, sources: &mut Vec<SourceStatus>) -> BotView {
    let Some(base) = cfg.bot_url.clone() else {
        return BotView {
            configured: false,
            ..Default::default()
        };
    };
    let activity = get_json("bot", &base, "/api/apps/activity", cfg, None, sources);
    let cells = get_json("bot", &base, "/api/cells", cfg, None, sources);
    let receipts = get_json("bot", &base, "/api/receipts/recent", cfg, None, sources);
    // Hermes activity is admin-token-gated on the bot (Bearer).
    let hermes = cfg
        .bot_admin_token
        .as_deref()
        .and_then(|tok| get_json("bot", &base, "/admin/api/hermes", cfg, Some(tok), sources));
    let reachable = activity.is_some() || cells.is_some() || receipts.is_some();
    BotView {
        configured: true,
        reachable,
        activity,
        cells,
        receipts,
        hermes,
    }
}

fn fetch_durable_view(
    cfg: &OpsConfig,
    runtime: &tokio::runtime::Runtime,
    sources: &mut Vec<SourceStatus>,
) -> DurableView {
    let Some(url) = cfg.database_url.clone() else {
        sources.push(SourceStatus {
            name: "durable (postgres)".into(),
            kind: "postgres".into(),
            target: "(unset)".into(),
            reachable: false,
            http_status: None,
            latency_ms: 0,
            error: Some("DATABASE_URL not configured".into()),
        });
        return DurableView::default();
    };
    let view = runtime.block_on(crate::pg::fetch_durable(&url, cfg.timeout));
    sources.push(SourceStatus {
        name: "durable (postgres)".into(),
        kind: "postgres".into(),
        target: redact_db(&url),
        reachable: view.reachable,
        http_status: None,
        latency_ms: 0,
        error: view.error.clone(),
    });
    view
}

/// Probe the compute backend's `/health` (node-a agent on `:8021`,
/// reached over the headscale overlay). Returns `None` when no backend URL is
/// configured (not probed, no alert), or `Some(reachable)` otherwise.
fn fetch_backend(cfg: &OpsConfig, sources: &mut Vec<SourceStatus>) -> Option<bool> {
    let url = cfg.backend_url.clone()?;
    let (reachable, http_status, latency_ms, error) = match http_get(&url, cfg.timeout, None) {
        Ok(resp) => {
            let ok = (200..300).contains(&resp.status);
            (
                ok,
                Some(resp.status),
                resp.elapsed.as_millis(),
                if ok {
                    None
                } else {
                    Some(format!("HTTP {}", resp.status))
                },
            )
        }
        Err(e) => (false, None, 0, Some(e)),
    };
    sources.push(SourceStatus {
        name: "compute backend /health".into(),
        kind: "http".into(),
        target: url,
        reachable,
        http_status,
        latency_ms,
        error,
    });
    Some(reachable)
}

/// Roll the fetched views up into the top-level health verdict.
#[allow(clippy::too_many_arguments)]
fn roll_up(
    node: &NodeView,
    gateway: &GatewayView,
    bot: &BotView,
    durable: &DurableView,
    backend: Option<bool>,
    bridge: &BridgeView,
    sources: &[SourceStatus],
) -> CloudHealth {
    let node_up = node.status.is_some();
    let gateway_up = gateway.status.is_some();

    let federation_members = node
        .status
        .as_ref()
        .and_then(|s| s.get("peer_count"))
        .and_then(|v| v.as_u64())
        .map(|p| p + 1) // peers + self
        .or_else(|| {
            node.federations
                .as_ref()
                .and_then(|f| f.as_array())
                .and_then(|a| a.first())
                .and_then(|f| f.get("member_count"))
                .and_then(|v| v.as_u64())
        });
    let consensus_live = node
        .status
        .as_ref()
        .and_then(|s| s.get("consensus_live"))
        .and_then(|v| v.as_bool());
    let block_height = node
        .status
        .as_ref()
        .and_then(|s| s.get("latest_height"))
        .and_then(|v| v.as_u64());
    let peers = node
        .status
        .as_ref()
        .and_then(|s| s.get("peer_count"))
        .and_then(|v| v.as_u64());
    let machines = gateway
        .status
        .as_ref()
        .and_then(|s| s.get("machines"))
        .and_then(|v| v.as_u64())
        .or(Some(gateway.machines.len() as u64));

    // The node's own readiness verdict (store ok + consensus live + ≥1 block).
    let node_finalizing = node
        .status
        .as_ref()
        .and_then(|s| s.get("healthy"))
        .and_then(|v| v.as_bool());
    let consensus_divergence = node.metrics.as_ref().and_then(|m| m.consensus_divergence);
    let tau_prefix_shifts = node.metrics.as_ref().and_then(|m| m.tau_prefix_shifts);
    let gossip_messages = node.metrics.as_ref().and_then(|m| m.gossip_messages);
    let gossip_stream_rejected = node.metrics.as_ref().and_then(|m| m.gossip_stream_rejected);
    let finality_latency_avg = node.metrics.as_ref().and_then(|m| m.finality_latency_avg);

    let node_s = if node_up { "up" } else { "down" };
    let gateway_s = if gateway_up { "up" } else { "down" };
    let bot_s = if !bot.configured {
        "not-deployed"
    } else if bot.reachable {
        "up"
    } else {
        "down"
    };
    let pg_s = if !durable.configured {
        "not-configured"
    } else if durable.reachable {
        "up"
    } else {
        "down"
    };
    let backend_s = match backend {
        None => "not-configured",
        Some(true) => "up",
        Some(false) => "down",
    };

    // The core of the cloud is the node + gateway. Healthy iff both are up and
    // consensus is live (when the node reports it). Down iff both core are down.
    let core_up = [node_up, gateway_up].iter().filter(|x| **x).count();
    let mut overall = if node_up && gateway_up && consensus_live != Some(false) {
        // bot/postgres being optional don't drag a core-healthy cloud below
        // "degraded"; surface degraded if any *configured* optional is down.
        let optionals_ok =
            (!bot.configured || bot.reachable) && (!durable.configured || durable.reachable);
        if optionals_ok { "healthy" } else { "degraded" }
    } else if core_up == 0 {
        "down"
    } else {
        "degraded"
    };

    // Derive the alerts from the rolled-up signals, then let a page/warn pull the
    // at-a-glance verdict down so the dashboard pill matches the alert banner. The
    // bridge lane contributes its own conservation/double-mint (page) +
    // dependency-down (warn) alerts on the same footing.
    let mut alerts = compute_alerts(
        node_up,
        node_finalizing,
        consensus_live,
        consensus_divergence,
        gateway_up,
        bot,
        durable,
        backend,
    );
    alerts.extend(bridge::compute_bridge_alerts(bridge));
    if alerts.iter().any(|a| a.severity == "page") && overall != "down" {
        overall = "degraded";
    }
    let _ = sources;

    // Bridge service strings (mirror the established up/down/not-configured shape).
    let svc_str = |r: Option<bool>| match r {
        None => "not-configured",
        Some(true) => "up",
        Some(false) => "down",
    };
    let bridge_relayer = svc_str(bridge.relayer_reachable).to_string();
    let bridge_solana = svc_str(bridge.solana_reachable).to_string();
    let bridge_stripe = svc_str(bridge.stripe_reachable).to_string();
    let bridge_conservation_ok = if bridge.conservation_observed {
        Some(bridge.conservation_ok)
    } else {
        None
    };

    CloudHealth {
        overall: overall.to_string(),
        node: node_s.to_string(),
        gateway: gateway_s.to_string(),
        bot: bot_s.to_string(),
        postgres: pg_s.to_string(),
        backend: backend_s.to_string(),
        federation_members,
        consensus_live,
        node_finalizing,
        consensus_divergence,
        tau_prefix_shifts,
        gossip_messages,
        gossip_stream_rejected,
        finality_latency_avg,
        machines,
        durable_jobs_in_flight: durable.jobs_in_flight,
        total_units_spent: durable.total_units_spent,
        block_height,
        peers,
        pg_active_connections: durable.active_connections,
        pg_max_connections: durable.max_connections,
        pg_db_size_bytes: durable.db_size_bytes,
        bridge_relayer,
        bridge_solana,
        bridge_stripe,
        bridge_conservation_ok,
        bridge_mints_observed: bridge.mints_observed,
        alerts,
    }
}

/// The fraction of postgres connection slots in use that trips a pressure WARN.
const PG_CONN_PRESSURE: f64 = 0.85;

/// Derive operator alerts from the rolled-up health signals. Page = wake someone
/// (consensus correctness / total core outage); warn = degraded, look soon; info
/// is not emitted here (benign counters live as dashboard tiles).
#[allow(clippy::too_many_arguments)]
fn compute_alerts(
    node_up: bool,
    node_finalizing: Option<bool>,
    consensus_live: Option<bool>,
    consensus_divergence: Option<f64>,
    gateway_up: bool,
    bot: &BotView,
    durable: &DurableView,
    backend: Option<bool>,
) -> Vec<Alert> {
    let mut alerts = Vec::new();

    // PAGE: the rust↔lean finalized-order differential diverged. ANY non-zero
    // count is a real consensus bug (a Rust-side bug or a stale/mismatched Lean
    // archive) — the verified Lean order is authoritative for that poll, but the
    // two implementations disagreeing must be investigated immediately.
    if let Some(d) = consensus_divergence {
        if d > 0.0 {
            alerts.push(Alert {
                severity: "page".into(),
                key: "consensus_divergence".into(),
                message: format!(
                    "rust↔lean finality DIVERGENCE: dregg_consensus_differential_divergence_total = {d} (a consensus-implementation bug — investigate now)"
                ),
            });
        }
    }

    // PAGE: the node is down, or up but not finalizing (store unreachable /
    // consensus stalled / no blocks) — the chain is not making progress.
    if !node_up {
        alerts.push(Alert {
            severity: "page".into(),
            key: "node_down".into(),
            message: "dregg node unreachable (no /status) — the chain is down".into(),
        });
    } else if node_finalizing == Some(false) || consensus_live == Some(false) {
        alerts.push(Alert {
            severity: "page".into(),
            key: "node_not_finalizing".into(),
            message:
                "dregg node is up but NOT finalizing (consensus stalled / store unreachable / no blocks)"
                    .into(),
        });
    }

    // WARN: the gateway (the machines API front door) is down.
    if !gateway_up {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "gateway_down".into(),
            message: "gateway unreachable (no /status) — the machines API is down".into(),
        });
    }

    // WARN: the durable / billing postgres is configured but unreachable, or under
    // connection pressure (the meter outbox cannot record charges → lease economy
    // stalls and leases lapse).
    if durable.configured && !durable.reachable {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "postgres_down".into(),
            message: format!(
                "durable postgres unreachable{}",
                durable
                    .error
                    .as_deref()
                    .map(|e| format!(": {e}"))
                    .unwrap_or_default()
            ),
        });
    }
    if let (Some(active), Some(max)) = (durable.active_connections, durable.max_connections) {
        if max > 0 && (active as f64) >= PG_CONN_PRESSURE * (max as f64) {
            alerts.push(Alert {
                severity: "warn".into(),
                key: "postgres_conn_pressure".into(),
                message: format!(
                    "postgres connection pressure: {active}/{max} slots in use (≥{:.0}%)",
                    PG_CONN_PRESSURE * 100.0
                ),
            });
        }
    }

    // WARN: the compute backend (node-a :8021) is unreachable. A
    // refused lease maps to a lapse, so backend-down is the dominant lease-lapse
    // cause; this is the grounded lease-lapse-rate signal.
    if backend == Some(false) {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "backend_down".into(),
            message: "compute backend (:8021/health) unreachable — dispatched leases will lapse"
                .into(),
        });
    }

    // WARN: the discord bot (the community front door) is configured but down.
    if bot.configured && !bot.reachable {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "bot_down".into(),
            message: "discord bot read API unreachable — the community front door is down".into(),
        });
    }

    alerts
}

/// Parse a few summary series out of Prometheus exposition text. Sums label-split
/// counter families (e.g. `dregg_turns_executed_total{status="..."}`).
fn parse_metrics(text: &str) -> MetricsSummary {
    let mut m = MetricsSummary::default();
    // Finality latency is a summary; derive the mean from its sum/count lines.
    let mut finality_sum: Option<f64> = None;
    let mut finality_count: Option<f64> = None;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((name_and_labels, value)) = line.rsplit_once(' ') else {
            continue;
        };
        let Ok(v) = value.trim().parse::<f64>() else {
            continue;
        };
        let metric = name_and_labels.split('{').next().unwrap_or("").trim();
        match metric {
            "dregg_turns_submitted_total" => add(&mut m.turns_submitted, v),
            "dregg_turns_executed_total" => add(&mut m.turns_executed, v),
            "dregg_proofs_verified_total" => add(&mut m.proofs_verified, v),
            "dregg_block_height" => m.block_height = Some(v),
            "dregg_federation_peers_connected" => m.peers_connected = Some(v),
            "dregg_ledger_cell_count" => m.cell_count = Some(v),
            "dregg_consensus_differential_divergence_total" => add(&mut m.consensus_divergence, v),
            "dregg_tau_prefix_shifts_total" => add(&mut m.tau_prefix_shifts, v),
            // Gossip: sum across the {direction} / {peer,reason} label families.
            "dregg_gossip_messages_total" => add(&mut m.gossip_messages, v),
            "dregg_gossip_stream_rejected_total" => add(&mut m.gossip_stream_rejected, v),
            "dregg_consensus_attested_total" => add(&mut m.consensus_attested, v),
            "dregg_consensus_finality_latency_seconds_sum" => add(&mut finality_sum, v),
            "dregg_consensus_finality_latency_seconds_count" => add(&mut finality_count, v),
            _ => {}
        }
    }
    // Mean finality latency = sum/count (guarded against a zero/absent count).
    if let (Some(s), Some(c)) = (finality_sum, finality_count) {
        if c > 0.0 {
            m.finality_latency_avg = Some(s / c);
        }
    }
    m
}

fn add(slot: &mut Option<f64>, v: f64) {
    *slot = Some(slot.unwrap_or(0.0) + v);
}

/// Redact the password from a `postgres://user:pass@host/db` URL for display.
fn redact_db(url: &str) -> String {
    if let Some(at) = url.find('@') {
        if let Some(scheme_end) = url.find("://") {
            let creds = &url[scheme_end + 3..at];
            if let Some((user, _)) = creds.split_once(':') {
                return format!("{}://{user}:***@{}", &url[..scheme_end], &url[at + 1..]);
            }
        }
    }
    url.to_string()
}

/// The current time as RFC3339, or a fallback if formatting fails.
fn now_rfc3339() -> String {
    time::OffsetDateTime::now_utc()
        .format(&time::format_description::well_known::Rfc3339)
        .unwrap_or_else(|_| "unknown".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metrics_parsing_sums_label_families() {
        let text = "# HELP x\n\
            dregg_turns_submitted_total 12\n\
            dregg_turns_executed_total{status=\"ok\"} 7\n\
            dregg_turns_executed_total{status=\"fail\"} 3\n\
            dregg_block_height 42\n\
            dregg_federation_peers_connected 4\n";
        let m = parse_metrics(text);
        assert_eq!(m.turns_submitted, Some(12.0));
        assert_eq!(m.turns_executed, Some(10.0));
        assert_eq!(m.block_height, Some(42.0));
        assert_eq!(m.peers_connected, Some(4.0));
    }

    #[test]
    fn parses_consensus_divergence_and_tau_shifts() {
        let text = "dregg_consensus_differential_divergence_total 0\n\
            dregg_tau_prefix_shifts_total 3\n";
        let m = parse_metrics(text);
        assert_eq!(m.consensus_divergence, Some(0.0));
        assert_eq!(m.tau_prefix_shifts, Some(3.0));
    }

    #[test]
    fn parses_gossip_and_finality_signals() {
        // Gossip volume sums over {direction}; rejections sum over {peer,reason}
        // — exactly the label families the node + dregg-net emit. The pre-seeded
        // sentinel rejection series (0) coexists with the real labelled ones.
        let text = "dregg_gossip_messages_total{direction=\"out\"} 40\n\
            dregg_gossip_messages_total{direction=\"in\"} 60\n\
            dregg_gossip_stream_rejected_total{peer=\"none\",reason=\"none\"} 0\n\
            dregg_gossip_stream_rejected_total{peer=\"10.0.0.7\",reason=\"conn_limit\"} 5\n\
            dregg_gossip_stream_rejected_total{peer=\"10.0.0.7\",reason=\"bad_signature\"} 2\n\
            dregg_consensus_attested_total 18\n\
            dregg_consensus_finality_latency_seconds_sum 12.0\n\
            dregg_consensus_finality_latency_seconds_count 4\n";
        let m = parse_metrics(text);
        assert_eq!(m.gossip_messages, Some(100.0));
        // The storm signature: 7 rejected streams across the peer/reason families.
        assert_eq!(m.gossip_stream_rejected, Some(7.0));
        assert_eq!(m.consensus_attested, Some(18.0));
        // Mean finality latency = 12.0 / 4 = 3.0s.
        assert_eq!(m.finality_latency_avg, Some(3.0));
    }

    #[test]
    fn finality_latency_avg_guards_zero_count() {
        // A node that has not finalized yet exposes count=0 — no mean, not NaN.
        let text = "dregg_consensus_finality_latency_seconds_sum 0\n\
            dregg_consensus_finality_latency_seconds_count 0\n";
        let m = parse_metrics(text);
        assert_eq!(m.finality_latency_avg, None);
    }

    #[test]
    fn divergence_pages_and_backend_warns() {
        // A healthy core but a nonzero divergence pages.
        let alerts = compute_alerts(
            true,
            Some(true),
            Some(true),
            Some(2.0),
            true,
            &BotView::default(),
            &DurableView::default(),
            Some(true),
        );
        assert!(
            alerts
                .iter()
                .any(|a| a.key == "consensus_divergence" && a.severity == "page")
        );

        // Node down pages; backend down warns; clean config emits nothing.
        let down = compute_alerts(
            false,
            None,
            None,
            Some(0.0),
            true,
            &BotView::default(),
            &DurableView::default(),
            Some(false),
        );
        assert!(
            down.iter()
                .any(|a| a.key == "node_down" && a.severity == "page")
        );
        assert!(
            down.iter()
                .any(|a| a.key == "backend_down" && a.severity == "warn")
        );

        let clean = compute_alerts(
            true,
            Some(true),
            Some(true),
            Some(0.0),
            true,
            &BotView::default(),
            &DurableView::default(),
            None,
        );
        assert!(clean.is_empty());
    }

    #[test]
    fn redacts_db_password() {
        assert_eq!(
            redact_db("postgres://dreggnet:secret@postgres:5432/dreggnet"),
            "postgres://dreggnet:***@postgres:5432/dreggnet"
        );
    }
}
