//! The live-edge source — reads the real health surfaces over plain HTTP.
//!
//! This is the **reviewed-go** path (the tested core runs on [`FixtureSource`]).
//! It fills each [`Probe`] from the corresponding surface, leaving an unreachable
//! one as [`Probe::Unreachable`] → Unknown — never falsely green. The surfaces it
//! reads are exactly the ones the operator ops dashboard aggregates, narrowed to
//! the public "is it up?" subset:
//!
//! | Surface          | Read                                                    |
//! |------------------|---------------------------------------------------------|
//! | node `/status`   | finalizing / consensus_live / heights / peers / producer / public_key |
//! | node `/api/federations` | the committee members + member_count + finalized height |
//! | node `/metrics`  | `dregg_consensus_differential_divergence_total` (rust↔lean), `dregg_federation_root_age_seconds` (finality age), `dregg_gossip_streams_rejected_total` (storm visibility) |
//! | gateway `/status`| up + machine count                                       |
//! | control `/healthz` | up                                                     |
//! | bridge `/status` | conservation observed/ok + rail reachability             |
//! | economy URL      | Σδ conservation sum (when a surface exposes it)          |

use serde_json::Value;

use crate::client::{http_get, prom_sum};
use crate::config::StatusConfig;
use crate::model::Incident;
use crate::source::*;

/// The live source over the configured surfaces.
pub struct LiveSource {
    cfg: StatusConfig,
    /// Operator-posted incidents (the live incident log is fed externally; the
    /// auto-detected half is layered by the server over time). Empty by default.
    incidents: Vec<Incident>,
}

impl LiveSource {
    /// Build over the config.
    pub fn new(cfg: StatusConfig) -> Self {
        LiveSource {
            cfg,
            incidents: Vec::new(),
        }
    }

    /// Seed the operator-posted incident log.
    pub fn with_incidents(mut self, incidents: Vec<Incident>) -> Self {
        self.incidents = incidents;
        self
    }
}

impl StatusSource for LiveSource {
    fn health(&self) -> RawHealth {
        let cfg = &self.cfg;
        let node_status = fetch_json(&format!("{}/status", trim(&cfg.node_url)), cfg.timeout);
        let federations = fetch_json(
            &format!("{}/api/federations", trim(&cfg.node_url)),
            cfg.timeout,
        );
        let metrics_text = fetch_text(&format!("{}/metrics", trim(&cfg.node_url)), cfg.timeout);

        let node = node_probe(&node_status);
        let federation = federation_probe(cfg, &node_status, &federations, &metrics_text);

        let gateway = match &cfg.gateway_url {
            None => Probe::NotConfigured,
            Some(u) => match fetch_json(&format!("{}/status", trim(u)), cfg.timeout) {
                Ok(v) => Probe::Reached(GatewayHealth {
                    machines: v.get("machines").and_then(|m| m.as_u64()),
                }),
                Err(e) => Probe::Unreachable(e),
            },
        };

        let control = match &cfg.control_url {
            None => Probe::NotConfigured,
            Some(u) => match http_get(&format!("{}/healthz", trim(u)), cfg.timeout) {
                Ok(r) if r.ok() => Probe::Reached(ControlHealth {
                    servers: r
                        .json()
                        .ok()
                        .and_then(|v| v.get("servers").and_then(|s| s.as_u64())),
                }),
                Ok(r) => Probe::Unreachable(format!("HTTP {}", r.status)),
                Err(e) => Probe::Unreachable(e),
            },
        };

        let bridges = match &cfg.bridge_url {
            None => Probe::NotConfigured,
            Some(u) => match fetch_json(&format!("{}/status", trim(u)), cfg.timeout) {
                Ok(v) => Probe::Reached(bridge_health(&v)),
                Err(e) => Probe::Unreachable(e),
            },
        };

        let economy = match &cfg.economy_url {
            None => Probe::NotConfigured,
            Some(u) => match fetch_json(u, cfg.timeout) {
                Ok(v) => {
                    let delta_sum = v
                        .get("delta_sum")
                        .and_then(|d| d.as_i64())
                        .map(|d| d as i128);
                    Probe::Reached(EconomyHealth {
                        observed: delta_sum.is_some(),
                        delta_sum: delta_sum.unwrap_or(0),
                    })
                }
                Err(e) => Probe::Unreachable(e),
            },
        };

        RawHealth {
            node,
            gateway,
            control,
            bridges,
            economy,
            federation,
            incidents: self.incidents.clone(),
        }
    }
}

/// Map the node `/status` JSON to a probe.
fn node_probe(status: &Result<Value, String>) -> Probe<NodeHealth> {
    match status {
        Ok(v) => Probe::Reached(NodeHealth {
            finalizing: v.get("healthy").and_then(|b| b.as_bool()).unwrap_or(false),
            consensus_live: v
                .get("consensus_live")
                .and_then(|b| b.as_bool())
                .unwrap_or(false),
            dag_height: v.get("dag_height").and_then(|h| h.as_u64()).unwrap_or(0),
            latest_height: v.get("latest_height").and_then(|h| h.as_u64()).unwrap_or(0),
            peer_count: v.get("peer_count").and_then(|p| p.as_u64()).unwrap_or(0),
            state_producer: v
                .get("state_producer")
                .and_then(|s| s.as_str())
                .unwrap_or("unknown")
                .to_string(),
        }),
        Err(e) => Probe::Unreachable(e.clone()),
    }
}

/// Assemble the federation probe from `/api/federations` + the metrics.
///
/// Honest single-vantage law: a public probe sees only THIS node's liveness
/// directly (`/status`); `/api/federations` lists the committee members but not
/// their per-member liveness, so every other member is Unknown — never a false
/// "up". The federation-wide finalized height + finality age come from the local
/// federation entry + the `dregg_federation_root_age_seconds` gauge; the
/// rust↔lean differential + the gossip storm-backpressure visibility come from
/// the Prometheus counters.
fn federation_probe(
    cfg: &StatusConfig,
    node_status: &Result<Value, String>,
    federations: &Result<Value, String>,
    metrics_text: &Result<String, String>,
) -> FederationProbe {
    let metric = |name: &str| metrics_text.as_ref().ok().and_then(|t| prom_sum(t, name));
    let divergence = metric("dregg_consensus_differential_divergence_total").map(|d| d as u64);
    // The node exposes the rejected-stream count if it exports it; otherwise the
    // series is absent → None → Unknown (the storm-visibility seam: the node lane
    // wiring `GossipNetwork::rejected_stream_count()` into `/metrics` under this
    // name is the named cross-lane dependency).
    let gossip_rejected = metric("dregg_gossip_streams_rejected_total")
        .or_else(|| metric("dregg_gossip_rejected_streams_total"))
        .map(|d| d as u64);
    // The age of the last finalized federation root (the finality latency).
    let root_age_secs = metric("dregg_federation_root_age_seconds").map(|s| s as u64);

    // The local federation entry carries the committee + finalized height.
    let local = federations.as_ref().ok().and_then(|v| {
        v.as_array().and_then(|a| {
            a.iter()
                .find(|f| f.get("is_local").and_then(|b| b.as_bool()).unwrap_or(false))
                .or_else(|| a.first())
                .cloned()
        })
    });

    let last_finalized_height = local
        .as_ref()
        .and_then(|f| f.get("latest_height").and_then(|h| h.as_u64()));

    // This node's own liveness/height come from /status (the only member a single
    // public vantage can directly observe).
    let self_up = node_status
        .as_ref()
        .ok()
        .and_then(|v| v.get("consensus_live").and_then(|b| b.as_bool()));
    let self_height = node_status
        .as_ref()
        .ok()
        .and_then(|v| v.get("dag_height").and_then(|h| h.as_u64()));
    // The node's own public key — used to pick THIS node out of the sorted member
    // list (so "self" is the right row, not just members[0]).
    let self_pubkey = node_status
        .as_ref()
        .ok()
        .and_then(|v| v.get("public_key").and_then(|p| p.as_str()))
        .map(|s| s.to_string());

    let members: Vec<String> = local
        .as_ref()
        .and_then(|f| f.get("members").and_then(|m| m.as_array()))
        .map(|a| {
            a.iter()
                .filter_map(|x| x.as_str().map(|s| s.to_string()))
                .collect()
        })
        .unwrap_or_default();

    // Prefer the node-reported committee size, then the member list, then config.
    let member_count = local
        .as_ref()
        .and_then(|f| f.get("member_count").and_then(|c| c.as_u64()))
        .map(|c| c as usize);
    let expected = member_count
        .filter(|&c| c > 0)
        .or_else(|| (!members.is_empty()).then_some(members.len()))
        .unwrap_or(cfg.federation_size);

    // The index of THIS node in the member list (by public key), if identifiable.
    let self_idx = self_pubkey.as_ref().and_then(|pk| {
        members
            .iter()
            .position(|m| m == pk || pk.starts_with(m.as_str()) || m.starts_with(pk.as_str()))
    });

    let mut nodes = Vec::new();
    if members.is_empty() {
        // No committee listing — at least surface this node.
        nodes.push(FedNodeProbe {
            name: "this node".into(),
            up: self_up,
            height: self_height,
            finality_age_secs: root_age_secs,
        });
    } else {
        for (i, m) in members.iter().enumerate() {
            // Only this node's liveness is directly observable from one vantage;
            // if we couldn't identify self by key, fall back to the first member.
            let is_self = self_idx.map(|s| s == i).unwrap_or(i == 0);
            nodes.push(FedNodeProbe {
                name: short_member(m),
                up: if is_self { self_up } else { None },
                height: if is_self { self_height } else { None },
                finality_age_secs: if is_self { root_age_secs } else { None },
            });
        }
    }

    FederationProbe {
        expected,
        nodes,
        last_finalized_height,
        last_finalized_age_secs: root_age_secs,
        divergence,
        gossip_rejected,
    }
}

/// Map a bridge relayer `/status` JSON to the conservation health.
fn bridge_health(v: &Value) -> BridgeHealth {
    let mirrors = v.get("mirrors").and_then(|m| m.as_array());
    let observed = mirrors.map(|a| !a.is_empty()).unwrap_or(false);
    let conservation_ok = mirrors
        .map(|a| {
            a.iter().all(|m| {
                let live = m.get("live_supply").and_then(|x| x.as_u64()).unwrap_or(0);
                let backing = m
                    .get("currently_locked")
                    .and_then(|x| x.as_u64())
                    .or_else(|| m.get("total_verified_payments").and_then(|x| x.as_u64()))
                    .unwrap_or(0);
                live <= backing
            })
        })
        .unwrap_or(true);
    let breach = v
        .get("double_mint_detected")
        .and_then(|b| b.as_bool())
        .unwrap_or(false)
        || (observed && !conservation_ok);
    BridgeHealth {
        solana_reachable: v.get("solana_reachable").and_then(|b| b.as_bool()),
        stripe_reachable: v.get("stripe_reachable").and_then(|b| b.as_bool()),
        conservation_observed: observed,
        conservation_ok,
        breach,
    }
}

/// Truncate a long member key for display.
fn short_member(s: &str) -> String {
    if s.len() > 12 {
        format!("{}…", &s[..12])
    } else {
        s.to_string()
    }
}

/// `GET url` and parse JSON, mapping any failure to an error string.
fn fetch_json(url: &str, timeout: std::time::Duration) -> Result<Value, String> {
    let r = http_get(url, timeout)?;
    if !r.ok() {
        return Err(format!("HTTP {}", r.status));
    }
    r.json()
}

/// `GET url` and return the body text on a 2xx.
fn fetch_text(url: &str, timeout: std::time::Duration) -> Result<String, String> {
    let r = http_get(url, timeout)?;
    if !r.ok() {
        return Err(format!("HTTP {}", r.status));
    }
    Ok(r.text())
}

/// Trim a trailing slash from a base URL.
fn trim(s: &str) -> &str {
    s.trim_end_matches('/')
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    // A faithful capture of the real node `/status` (StatusResponse) — the exact
    // field names `node/src/api.rs::StatusResponse` serializes. `public_key`
    // matches member #2 below so self-identification picks the RIGHT row.
    fn real_status() -> Value {
        json!({
            "healthy": true,
            "peer_count": 4,
            "latest_height": 9210,
            "dag_height": 10844,
            "block_count": 10844,
            "consensus_live": true,
            "federation_mode": "full",
            "public_key": "bbbbbbbbbbbbbbbbbbbbbbbb",
            "state_producer": "lean",
            "lean_producer": true,
            "full_turn_proving": true,
            "producer_covered_effects": 32
        })
    }

    // A faithful capture of the real `/api/federations` (Vec<FederationInfo>),
    // a 5-member committee with the local entry flagged — members are sorted hex
    // public keys (the real shape), and `member_count` is the committee size.
    fn real_federations() -> Value {
        json!([{
            "id": "fedfed00",
            "federation_id": "fedfed00",
            "committee_epoch": 7,
            "threshold": 4,
            "member_count": 5,
            "members": [
                "aaaaaaaaaaaaaaaaaaaaaaaa",
                "bbbbbbbbbbbbbbbbbbbbbbbb",
                "cccccccccccccccccccccccc",
                "dddddddddddddddddddddddd",
                "eeeeeeeeeeeeeeeeeeeeeeee"
            ],
            "is_local": true,
            "latest_height": 10844,
            "latest_root": "deadbeef",
            "num_finalized_roots": 521
        }])
    }

    // A faithful `/metrics` capture — the exact Prometheus series the node emits
    // (plus the gossip rejected-stream series the node lane is to export).
    const REAL_METRICS: &str = "\
# HELP dregg_consensus_differential_divergence_total rust/lean disagreement\n\
# TYPE dregg_consensus_differential_divergence_total counter\n\
dregg_consensus_differential_divergence_total 0\n\
# TYPE dregg_federation_root_age_seconds gauge\n\
dregg_federation_root_age_seconds 6\n\
# TYPE dregg_gossip_messages_total counter\n\
dregg_gossip_messages_total{direction=\"received\"} 81234\n\
dregg_gossip_streams_rejected_total 37\n";

    #[test]
    fn node_probe_maps_the_real_status_shape() {
        let n = node_probe(&Ok(real_status()));
        let h = n.reached().expect("reached");
        assert!(h.finalizing); // from `healthy`
        assert!(h.consensus_live);
        assert_eq!(h.dag_height, 10844);
        assert_eq!(h.latest_height, 9210);
        assert_eq!(h.peer_count, 4);
        assert_eq!(h.state_producer, "lean");
    }

    #[test]
    fn federation_probe_maps_the_real_federations_and_metrics() {
        let cfg = StatusConfig::default();
        let fed = federation_probe(
            &cfg,
            &Ok(real_status()),
            &Ok(real_federations()),
            &Ok(REAL_METRICS.to_string()),
        );
        // The live n=5 committee size comes from the real member_count.
        assert_eq!(fed.expected, 5);
        assert_eq!(fed.nodes.len(), 5);
        assert_eq!(fed.last_finalized_height, Some(10844));
        // The finality age comes from the dregg_federation_root_age_seconds gauge.
        assert_eq!(fed.last_finalized_age_secs, Some(6));
        // The rust↔lean differential counter (0 → agreeing).
        assert_eq!(fed.divergence, Some(0));
        // The storm-backpressure visibility (the rejected-stream counter).
        assert_eq!(fed.gossip_rejected, Some(37));

        // Self-identification by public_key picks member #2 (the matching key),
        // and ONLY that node is observably up — the rest are honest-Unknown.
        let up: Vec<bool> = fed.nodes.iter().map(|n| n.up == Some(true)).collect();
        assert_eq!(
            up.iter().filter(|x| **x).count(),
            1,
            "only self is observable"
        );
        let self_node = &fed.nodes[1];
        assert_eq!(self_node.up, Some(true));
        assert_eq!(self_node.height, Some(10844));
        assert_eq!(self_node.finality_age_secs, Some(6));
        // The others are Unknown (no per-member liveness from one vantage).
        assert!(fed.nodes[0].up.is_none());
        assert!(fed.nodes[4].up.is_none());
    }

    #[test]
    fn gossip_rejection_is_unknown_when_the_metric_is_absent() {
        // The node does not (yet) export the rejected-stream series — honest
        // Unknown, NEVER a false "0 rejections / no storm".
        let cfg = StatusConfig::default();
        let no_gossip = "dregg_federation_root_age_seconds 6\n\
                         dregg_consensus_differential_divergence_total 0\n";
        let fed = federation_probe(
            &cfg,
            &Ok(real_status()),
            &Ok(real_federations()),
            &Ok(no_gossip.to_string()),
        );
        assert_eq!(fed.gossip_rejected, None);
    }

    #[test]
    fn unreachable_metrics_leave_divergence_and_gossip_unknown() {
        let cfg = StatusConfig::default();
        let fed = federation_probe(
            &cfg,
            &Ok(real_status()),
            &Ok(real_federations()),
            &Err("connect dregg-node:8420: connection refused".into()),
        );
        assert_eq!(fed.divergence, None);
        assert_eq!(fed.gossip_rejected, None);
        assert_eq!(fed.last_finalized_age_secs, None);
        // The committee size still comes from /api/federations.
        assert_eq!(fed.expected, 5);
    }

    #[test]
    fn node_unreachable_is_unreachable_probe() {
        let n = node_probe(&Err("connection refused".into()));
        assert!(matches!(n, Probe::Unreachable(_)));
    }

    #[test]
    fn bridge_health_maps_a_real_relayer_status() {
        // A relayer /status with one conserving mirror (live ≤ locked).
        let v = json!({
            "solana_reachable": true,
            "stripe_reachable": true,
            "double_mint_detected": false,
            "mirrors": [{ "live_supply": 100u64, "currently_locked": 100u64 }]
        });
        let b = bridge_health(&v);
        assert!(b.conservation_observed);
        assert!(b.conservation_ok);
        assert!(!b.breach);
        // A breach: more mirror asset circulates than is backed.
        let breached = json!({
            "mirrors": [{ "live_supply": 200u64, "currently_locked": 100u64 }]
        });
        assert!(bridge_health(&breached).breach);
    }
}
