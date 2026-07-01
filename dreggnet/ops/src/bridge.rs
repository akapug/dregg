//! Bridge observability — the Solana/Stripe coin-bridge panel + signals.
//!
//! This AGGREGATES (read-only) the coin-bridge's footprint across the surfaces
//! that already exist; it changes **no** bridge logic. The bridge itself lives in
//! `breadstuffs/bridge/` (`solana_mirror` / `stripe_mirror`): a lock/payment is
//! verified, then a conserved mirror asset is minted as a REAL kernel
//! [`Effect::Mint`]/[`BridgeMint`], and a redeem burns it
//! ([`Effect::Burn`]) — the consume-once lock nullifier is the double-mint gate,
//! and the ledger invariant is `live_supply ≤ currently_locked` (Solana) /
//! `live_supply ≤ total_verified_payments` (Stripe).
//!
//! Three honest tiers of evidence (most- to least-grounded):
//!
//! 1. **Live on the node (grounded today).** Every bridge mint and redeem lands
//!    as a real kernel effect in the dregg ledger, so the node's committed-event
//!    feed (`/api/events`) carries them: `mint`/`bridgemint` is a lock→mint,
//!    `burn` is a redeem. We count them, timestamp the last mint, and feed the
//!    activity. (Burn summaries carry amount+asset; the events feed does not carry
//!    a mint amount today — an honest gap, noted on the panel.)
//! 2. **The relayer status endpoint (optional, `OPS_BRIDGE_URL`).** A relayer that
//!    serializes its `MirrorState` / `StripeMirrorState` (the conservation
//!    quantities + the consumed-lock count) lets us surface AND alert on the
//!    conservation invariant + double-mint. Absent (the staging default) → "not
//!    configured", and the conservation signal is reported as un-observed (never a
//!    false all-clear).
//! 3. **External cluster reachability (optional, plaintext only).** The Solana
//!    devnet RPC (`OPS_SOLANA_RPC_URL`, `getHealth`) and the Stripe webhook
//!    receiver (`OPS_STRIPE_RECEIVER_URL`). The ops binary carries no TLS closure
//!    by design, so an `https` Solana RPC is **not** reachable from here — point
//!    these at a plaintext-proxied health, or read reachability from the relayer
//!    status (tier 2). This is the honest mainnet gap: the geyser inclusion-proof
//!    / trustless light-client path is verified in the bridge crate but is not yet
//!    wired to a live mainnet relayer the dashboard can read.

use serde::Serialize;
use serde_json::Value;

use crate::aggregate::{Alert, NodeView, SourceStatus};
use crate::client::{http_get, http_post};
use crate::config::OpsConfig;

/// One mirrored asset's conservation view, parsed from a relayer status endpoint.
#[derive(Debug, Clone, Serialize)]
pub struct MirrorLedger {
    /// "solana" or "stripe".
    pub rail: String,
    /// Short hex of the mirror's dregg `AssetId`.
    pub asset: String,
    /// The backing quantity: `currently_locked` (Solana) / `total_verified_payments` (Stripe).
    pub locked_or_backing: u64,
    /// A human label for the backing quantity.
    pub backing_label: String,
    /// Mirror supply currently circulating inside dregg (`live_supply`).
    pub live_supply: u64,
    /// The conservation invariant for this ledger: `live_supply ≤ locked_or_backing`.
    pub conserved: bool,
    /// Consumed-lock count (the nullifiers spent so far — `seen_locks` /
    /// `seen_payments` length, or a relayer-reported `locks_consumed`).
    pub locks_consumed: u64,
}

/// One recent bridge action (a lock→mint or a redeem-burn), newest first.
#[derive(Debug, Clone, Serialize)]
pub struct BridgeActivity {
    /// The timestamp as the source reports it (unix number or RFC3339 string).
    pub when: Option<Value>,
    /// "mint" / "bridgemint" / "burn".
    pub kind: String,
    /// Where it was observed: "solana-oracle" (Effect::Mint), "solana-trustless"
    /// (Effect::BridgeMint), "redeem" (Effect::Burn), or "relayer".
    pub rail: String,
    /// The amount, when the source carries it (burn summaries do; the events feed
    /// does not carry mint amounts today).
    pub amount: Option<u64>,
    /// The affected cell (short hex), when known.
    pub cell: Option<String>,
    /// A status string ("committed" for node events, or relayer-reported).
    pub status: String,
}

/// The whole bridge-panel view assembled for one snapshot.
#[derive(Debug, Clone, Serialize, Default)]
pub struct BridgeView {
    /// Whether any bridge surface (relayer/solana/stripe URL) is configured. The
    /// node-derived activity is always attempted independently of this.
    pub configured: bool,
    /// Relayer status-endpoint reachability (None = not configured).
    pub relayer_reachable: Option<bool>,
    /// Solana cluster (devnet) reachability (None = not configured / not probeable).
    pub solana_reachable: Option<bool>,
    /// Stripe webhook receiver reachability (None = not configured).
    pub stripe_reachable: Option<bool>,
    /// Per-mirror conservation ledgers, parsed from the relayer status.
    pub ledgers: Vec<MirrorLedger>,
    /// Recent bridge activity (newest first), node-derived (+ relayer-reported).
    pub recent: Vec<BridgeActivity>,
    /// Count of `mint`/`bridgemint` effects in the node event window.
    pub mints_observed: u64,
    /// Count of `burn` effects in the node event window.
    pub burns_observed: u64,
    /// Timestamp of the most recent mint observed (as the node reports it).
    pub last_mint_at: Option<Value>,
    /// Whether the conservation invariant was actually OBSERVED (a relayer ledger
    /// was parsed). When false, conservation is un-observed — never a false
    /// all-clear.
    pub conservation_observed: bool,
    /// Whether every observed ledger conserves (`live ≤ locked`). Vacuously true
    /// when none are observed.
    pub conservation_ok: bool,
    /// Count of double-mint attempts the nullifier gate REJECTED (informational —
    /// the gate working as intended). Summed across the relayer report.
    pub double_mint_rejected: u64,
    /// Whether a SUCCESSFUL double-mint / conservation breach is detected (the
    /// real critical condition).
    pub breach_detected: bool,
    /// Honest provenance notes (devnet/oracle/mainnet-gap), surfaced verbatim.
    pub notes: Vec<String>,
}

/// Fetch + assemble the bridge view. The node-derived activity reuses the
/// already-fetched [`NodeView`] (no extra node round-trip); the relayer / Solana /
/// Stripe probes are made here against the configured URLs.
pub fn fetch_bridge(
    cfg: &OpsConfig,
    node: &NodeView,
    sources: &mut Vec<SourceStatus>,
) -> BridgeView {
    let mut view = BridgeView {
        configured: cfg.bridge_url.is_some()
            || cfg.solana_rpc_url.is_some()
            || cfg.stripe_receiver_url.is_some(),
        conservation_ok: true,
        notes: default_notes(),
        ..Default::default()
    };

    // Tier 1 — the grounded, always-available node-derived activity.
    let (recent, mints, burns, last_mint) = parse_node_bridge_activity(node.recent_events.as_ref());
    view.recent = recent;
    view.mints_observed = mints;
    view.burns_observed = burns;
    view.last_mint_at = last_mint;

    // Tier 2 — the optional relayer status endpoint (the conservation source).
    if let Some(url) = cfg.bridge_url.as_deref() {
        match http_get(url, cfg.timeout, None) {
            Ok(resp) => {
                let ok = (200..300).contains(&resp.status);
                view.relayer_reachable = Some(ok);
                sources.push(SourceStatus {
                    name: "bridge relayer /status".into(),
                    kind: "http".into(),
                    target: url.to_string(),
                    reachable: ok,
                    http_status: Some(resp.status),
                    latency_ms: resp.elapsed.as_millis(),
                    error: if ok {
                        None
                    } else {
                        Some(format!("HTTP {}", resp.status))
                    },
                });
                if ok {
                    if let Ok(v) = resp.json() {
                        apply_relayer_status(&mut view, &v);
                    }
                }
            }
            Err(e) => {
                view.relayer_reachable = Some(false);
                sources.push(SourceStatus {
                    name: "bridge relayer /status".into(),
                    kind: "http".into(),
                    target: url.to_string(),
                    reachable: false,
                    http_status: None,
                    latency_ms: 0,
                    error: Some(e),
                });
            }
        }
    }

    // Tier 3a — Solana cluster reachability via the JSON-RPC `getHealth` (plaintext
    // only; an https RPC records an honest unreachable from the no-TLS ops binary).
    if let Some(url) = cfg.solana_rpc_url.as_deref() {
        view.solana_reachable = Some(probe_solana(url, cfg, sources));
    }
    // Tier 3b — the Stripe webhook receiver health (a plain GET to its health URL).
    if let Some(url) = cfg.stripe_receiver_url.as_deref() {
        view.stripe_reachable = Some(probe_get("stripe receiver /health", url, cfg, sources));
    }

    view
}

/// The honest provenance notes shown on the panel verbatim.
fn default_notes() -> Vec<String> {
    vec![
        "Node-derived activity (mint/bridgemint/burn effects) is live-readable today; \
         mint amounts are not carried by the events feed (burn summaries are)."
            .into(),
        "Conservation (live ≤ locked) + double-mint are surfaced only when a relayer \
         status endpoint (OPS_BRIDGE_URL) is configured; otherwise reported un-observed."
            .into(),
        "Solana reachability is the devnet/oracle path. The trustless geyser \
         inclusion-proof (mainnet-real) is verified in the bridge crate but not yet \
         wired to a live relayer this dashboard reads — the named mainnet gap."
            .into(),
    ]
}

/// Probe a Solana JSON-RPC endpoint with `getHealth`. Returns reachability and
/// records a [`SourceStatus`]. A healthy cluster returns `{"result":"ok"}`.
fn probe_solana(url: &str, cfg: &OpsConfig, sources: &mut Vec<SourceStatus>) -> bool {
    const BODY: &[u8] = br#"{"jsonrpc":"2.0","id":1,"method":"getHealth"}"#;
    let (reachable, http_status, latency_ms, error) =
        match http_post(url, BODY, "application/json", cfg.timeout) {
            Ok(resp) => {
                // getHealth → `"ok"` on a caught-up node; any 2xx with a `result`
                // counts as reachable (a behind node returns an error object but is
                // still reachable — we report cluster reachability, not sync state).
                let ok = (200..300).contains(&resp.status) && resp.text().contains("result");
                (
                    ok,
                    Some(resp.status),
                    resp.elapsed.as_millis(),
                    if ok {
                        None
                    } else {
                        Some(format!("HTTP {} / no result", resp.status))
                    },
                )
            }
            Err(e) => (false, None, 0, Some(e)),
        };
    sources.push(SourceStatus {
        name: "solana cluster getHealth".into(),
        kind: "http".into(),
        target: url.to_string(),
        reachable,
        http_status,
        latency_ms,
        error,
    });
    reachable
}

/// Probe a plain-GET health URL, recording a [`SourceStatus`].
fn probe_get(name: &str, url: &str, cfg: &OpsConfig, sources: &mut Vec<SourceStatus>) -> bool {
    let (reachable, http_status, latency_ms, error) = match http_get(url, cfg.timeout, None) {
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
        name: name.into(),
        kind: "http".into(),
        target: url.to_string(),
        reachable,
        http_status,
        latency_ms,
        error,
    });
    reachable
}

/// Scan the node's committed-event feed for bridge effects, returning the recent
/// activity, the mint/burn counts, and the most-recent mint timestamp.
///
/// `mint`/`bridgemint` are lock→mints; `burn` is a redeem. The lowercased
/// effect-kind strings match the node's `effect_kind` projection (a `{:?}` head),
/// and burn amount/asset come from the typed `summaries` when present.
pub fn parse_node_bridge_activity(
    events: Option<&Value>,
) -> (Vec<BridgeActivity>, u64, u64, Option<Value>) {
    let mut recent = Vec::new();
    let mut mints = 0u64;
    let mut burns = 0u64;
    let mut last_mint: Option<Value> = None;

    let Some(Value::Array(arr)) = events else {
        return (recent, mints, burns, last_mint);
    };

    for ev in arr {
        let effects: Vec<String> = ev
            .get("effects")
            .and_then(|e| e.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(|s| s.to_ascii_lowercase()))
                    .collect()
            })
            .unwrap_or_default();

        let when = ev.get("timestamp").cloned();
        let cell = ev
            .get("cell_id")
            .and_then(|c| c.as_str())
            .map(|s| short_hex(s));

        for kind in &effects {
            match kind.as_str() {
                "mint" | "bridgemint" => {
                    mints += 1;
                    if last_mint.is_none() {
                        last_mint = when.clone();
                    }
                    recent.push(BridgeActivity {
                        when: when.clone(),
                        kind: kind.clone(),
                        rail: if kind == "bridgemint" {
                            "solana-trustless".into()
                        } else {
                            "solana-oracle".into()
                        },
                        amount: None,
                        cell: cell.clone(),
                        status: "committed".into(),
                    });
                }
                "burn" => {
                    burns += 1;
                    // A burn (redeem) carries amount+asset in the typed summary.
                    let amount = ev
                        .get("summaries")
                        .and_then(|s| s.as_array())
                        .and_then(|a| {
                            a.iter().find_map(|sm| {
                                let is_burn = sm
                                    .get("kind")
                                    .and_then(|k| k.as_str())
                                    .map(|k| k == "burned")
                                    .unwrap_or(false);
                                if is_burn {
                                    sm.get("amount").and_then(|x| x.as_u64())
                                } else {
                                    None
                                }
                            })
                        });
                    recent.push(BridgeActivity {
                        when: when.clone(),
                        kind: "burn".into(),
                        rail: "redeem".into(),
                        amount,
                        cell: cell.clone(),
                        status: "committed".into(),
                    });
                }
                _ => {}
            }
        }
    }

    (recent, mints, burns, last_mint)
}

/// Fold a parsed relayer status JSON into the view. The expected shape mirrors the
/// serialized `MirrorState` / `StripeMirrorState` (see `breadstuffs/bridge/`):
///
/// ```json
/// {
///   "mirrors": [
///     { "rail": "solana", "config": {"asset": "<hex|bytes>"},
///       "currently_locked": 1000, "live_supply": 1000,
///       "seen_locks": ["..."], "seen_redeems": ["..."] },
///     { "rail": "stripe", "config": {"asset": "<hex|bytes>"},
///       "total_verified_payments": 5000, "live_supply": 5000,
///       "seen_payments": ["..."] }
///   ],
///   "double_mint_rejected": 0,
///   "double_mint_detected": false,
///   "solana_reachable": true,
///   "stripe_reachable": true
/// }
/// ```
///
/// Field presence is the rail discriminant when `rail` is absent
/// (`currently_locked` ⇒ solana, `total_verified_payments` ⇒ stripe). All fields
/// are read defensively — a missing field degrades that ledger, never the panel.
fn apply_relayer_status(view: &mut BridgeView, v: &Value) {
    let (ledgers, observed, all_conserved, rejected, breach) = parse_relayer_status(v);
    if observed {
        view.conservation_observed = true;
        view.conservation_ok = all_conserved;
        view.ledgers = ledgers;
    }
    view.double_mint_rejected = view.double_mint_rejected.max(rejected);
    if breach || !all_conserved {
        view.breach_detected = true;
    }
    // Let a relayer report cluster reachability when the direct probe is not set.
    if view.solana_reachable.is_none() {
        view.solana_reachable = v.get("solana_reachable").and_then(|b| b.as_bool());
    }
    if view.stripe_reachable.is_none() {
        view.stripe_reachable = v.get("stripe_reachable").and_then(|b| b.as_bool());
    }
}

/// Pure parse of a relayer status JSON. Returns
/// `(ledgers, observed, all_conserved, double_mint_rejected, double_mint_detected)`.
pub fn parse_relayer_status(v: &Value) -> (Vec<MirrorLedger>, bool, bool, u64, bool) {
    let mut ledgers = Vec::new();
    let mut all_conserved = true;

    let mirrors = v
        .get("mirrors")
        .and_then(|m| m.as_array())
        .cloned()
        .unwrap_or_default();

    for m in &mirrors {
        let live_supply = m.get("live_supply").and_then(|x| x.as_u64()).unwrap_or(0);

        // Rail + backing: explicit `rail`, else inferred from which backing field is present.
        let solana_backing = m.get("currently_locked").and_then(|x| x.as_u64());
        let stripe_backing = m.get("total_verified_payments").and_then(|x| x.as_u64());
        let explicit_rail = m.get("rail").and_then(|r| r.as_str());

        let (rail, locked_or_backing, backing_label) =
            match (explicit_rail, solana_backing, stripe_backing) {
                (Some("stripe"), _, b) | (None, None, b @ Some(_)) => {
                    ("stripe", b.unwrap_or(0), "Stripe-cleared cents")
                }
                (Some("solana"), b, _) | (None, b, _) => {
                    ("solana", b.unwrap_or(0), "locked on Solana")
                }
                (Some(other), _, _) => {
                    // Unknown explicit rail — keep it, prefer whichever backing exists.
                    let b = solana_backing.or(stripe_backing).unwrap_or(0);
                    (other, b, "backing")
                }
            };

        let conserved = live_supply <= locked_or_backing;
        if !conserved {
            all_conserved = false;
        }

        let locks_consumed = m
            .get("locks_consumed")
            .and_then(|x| x.as_u64())
            .or_else(|| count_array(m, "seen_locks"))
            .or_else(|| count_array(m, "seen_payments"))
            .unwrap_or(0);

        let asset = m
            .get("config")
            .and_then(|c| c.get("asset"))
            .map(asset_to_hex)
            .unwrap_or_else(|| "—".to_string());

        ledgers.push(MirrorLedger {
            rail: rail.to_string(),
            asset,
            locked_or_backing,
            backing_label: backing_label.to_string(),
            live_supply,
            conserved,
            locks_consumed,
        });
    }

    let observed = !mirrors.is_empty();
    let rejected = v
        .get("double_mint_rejected")
        .and_then(|x| x.as_u64())
        .unwrap_or(0);
    let detected = v
        .get("double_mint_detected")
        .and_then(|b| b.as_bool())
        .unwrap_or(false);

    (ledgers, observed, all_conserved, rejected, detected)
}

/// Derive the bridge alerts from the assembled view, following the established
/// ops convention: a CORRECTNESS-invariant violation **pages**; a configured but
/// unreachable dependency **warns**; the gate-working count is info (a tile).
pub fn compute_bridge_alerts(view: &BridgeView) -> Vec<Alert> {
    let mut alerts = Vec::new();

    // PAGE — the conservation invariant is broken on some mirror: more mirror
    // asset is circulating than is locked/backed. A critical bridge bug.
    for l in &view.ledgers {
        if !l.conserved {
            alerts.push(Alert {
                severity: "page".into(),
                key: "bridge_conservation_breach".into(),
                message: format!(
                    "BRIDGE CONSERVATION BREACH on the {} mirror (asset {}): live_supply {} > {} {} — more mirror asset circulates than is backed (a critical bridge bug)",
                    l.rail, l.asset, l.live_supply, l.locked_or_backing, l.backing_label
                ),
            });
        }
    }

    // PAGE — a successful double-mint detected (the nullifier gate failed). A
    // detected double-mint is a conservation breach by construction.
    if view.breach_detected && !view.ledgers.iter().any(|l| !l.conserved) {
        alerts.push(Alert {
            severity: "page".into(),
            key: "bridge_double_mint".into(),
            message:
                "BRIDGE DOUBLE-MINT detected (the consume-once lock nullifier was bypassed) — a critical bridge bug"
                    .into(),
        });
    }

    // WARN — a configured bridge dependency is unreachable.
    if view.relayer_reachable == Some(false) {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "bridge_relayer_down".into(),
            message: "bridge relayer status endpoint unreachable — conservation/double-mint cannot be observed".into(),
        });
    }
    if view.solana_reachable == Some(false) {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "bridge_solana_down".into(),
            message:
                "Solana cluster (devnet) unreachable — inbound locks cannot be observed/verified"
                    .into(),
        });
    }
    if view.stripe_reachable == Some(false) {
        alerts.push(Alert {
            severity: "warn".into(),
            key: "bridge_stripe_down".into(),
            message: "Stripe webhook receiver unreachable — USD-credit mints cannot be processed"
                .into(),
        });
    }

    alerts
}

/// Count a named array field's length, if present.
fn count_array(m: &Value, key: &str) -> Option<u64> {
    m.get(key)
        .and_then(|a| a.as_array())
        .map(|a| a.len() as u64)
}

/// Render an `asset` value (a hex string or a JSON byte array) to short hex.
fn asset_to_hex(v: &Value) -> String {
    match v {
        Value::String(s) => short_hex(s),
        Value::Array(bytes) => {
            let hex: String = bytes
                .iter()
                .filter_map(|b| b.as_u64())
                .map(|b| format!("{:02x}", (b & 0xff) as u8))
                .collect();
            short_hex(&hex)
        }
        other => short_hex(&other.to_string()),
    }
}

/// Truncate a hex-ish string to a readable prefix.
fn short_hex(s: &str) -> String {
    if s.len() > 12 {
        format!("{}…", &s[..12])
    } else {
        s.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn node_activity_counts_mints_burns_and_last_mint() {
        let events = json!([
            { "timestamp": 300, "cell_id": "aabbccddeeff0011", "effects": ["mint"] },
            { "timestamp": 200, "cell_id": "1122", "effects": ["setfield", "burn"],
              "summaries": [ { "kind": "burned", "cell": "1122", "asset": "cd", "amount": 50 } ] },
            { "timestamp": 100, "cell_id": "33", "effects": ["bridgemint"] },
            { "timestamp": 90, "cell_id": "44", "effects": ["transfer"] }
        ]);
        let (recent, mints, burns, last) = parse_node_bridge_activity(Some(&events));
        assert_eq!(mints, 2); // mint + bridgemint
        assert_eq!(burns, 1);
        assert_eq!(last, Some(json!(300)));
        // The burn's amount is recovered from the typed summary.
        let burn = recent.iter().find(|a| a.kind == "burn").unwrap();
        assert_eq!(burn.amount, Some(50));
        // bridgemint is tagged trustless, plain mint oracle.
        assert!(
            recent
                .iter()
                .any(|a| a.kind == "bridgemint" && a.rail == "solana-trustless")
        );
        assert!(
            recent
                .iter()
                .any(|a| a.kind == "mint" && a.rail == "solana-oracle")
        );
        // A non-bridge effect produces nothing.
        assert!(!recent.iter().any(|a| a.kind == "transfer"));
    }

    #[test]
    fn node_activity_empty_when_no_events() {
        let (recent, mints, burns, last) = parse_node_bridge_activity(None);
        assert!(recent.is_empty());
        assert_eq!((mints, burns), (0, 0));
        assert_eq!(last, None);
    }

    #[test]
    fn relayer_status_parses_both_rails_and_conserves() {
        let status = json!({
            "mirrors": [
                { "config": {"asset": "abababababab0000"}, "currently_locked": 1000,
                  "live_supply": 1000, "seen_locks": ["a", "b"], "seen_redeems": [] },
                { "rail": "stripe", "config": {"asset": "cdcdcdcdcdcd1111"},
                  "total_verified_payments": 5000, "live_supply": 4500,
                  "seen_payments": ["p1", "p2", "p3"] }
            ],
            "double_mint_rejected": 2
        });
        let (ledgers, observed, ok, rejected, breach) = parse_relayer_status(&status);
        assert!(observed && ok && !breach);
        assert_eq!(rejected, 2);
        assert_eq!(ledgers.len(), 2);
        let sol = ledgers.iter().find(|l| l.rail == "solana").unwrap();
        assert_eq!(sol.locked_or_backing, 1000);
        assert_eq!(sol.live_supply, 1000);
        assert_eq!(sol.locks_consumed, 2);
        assert!(sol.conserved);
        let stripe = ledgers.iter().find(|l| l.rail == "stripe").unwrap();
        assert_eq!(stripe.locked_or_backing, 5000);
        assert_eq!(stripe.locks_consumed, 3);
        assert_eq!(stripe.backing_label, "Stripe-cleared cents");
    }

    #[test]
    fn relayer_status_flags_a_conservation_breach() {
        let status = json!({
            "mirrors": [
                { "config": {"asset": "aa"}, "currently_locked": 100, "live_supply": 250 }
            ]
        });
        let (ledgers, observed, ok, _rej, _det) = parse_relayer_status(&status);
        assert!(observed && !ok);
        assert!(!ledgers[0].conserved);
    }

    #[test]
    fn conservation_breach_pages() {
        let view = BridgeView {
            ledgers: vec![MirrorLedger {
                rail: "solana".into(),
                asset: "aa".into(),
                locked_or_backing: 100,
                backing_label: "locked on Solana".into(),
                live_supply: 250,
                conserved: false,
                locks_consumed: 1,
            }],
            breach_detected: true,
            ..Default::default()
        };
        let alerts = compute_bridge_alerts(&view);
        assert!(
            alerts
                .iter()
                .any(|a| a.key == "bridge_conservation_breach" && a.severity == "page")
        );
        // The breach is reported as the conservation-breach page, not double-counted
        // as a separate double-mint page.
        assert!(!alerts.iter().any(|a| a.key == "bridge_double_mint"));
    }

    #[test]
    fn detected_double_mint_without_ledger_breach_pages() {
        let view = BridgeView {
            breach_detected: true,
            ledgers: vec![], // no parsed ledger, but the relayer flagged a double-mint
            ..Default::default()
        };
        let alerts = compute_bridge_alerts(&view);
        assert!(
            alerts
                .iter()
                .any(|a| a.key == "bridge_double_mint" && a.severity == "page")
        );
    }

    #[test]
    fn unreachable_dependencies_warn() {
        let view = BridgeView {
            relayer_reachable: Some(false),
            solana_reachable: Some(false),
            stripe_reachable: Some(false),
            ..Default::default()
        };
        let alerts = compute_bridge_alerts(&view);
        assert!(
            alerts
                .iter()
                .any(|a| a.key == "bridge_relayer_down" && a.severity == "warn")
        );
        assert!(
            alerts
                .iter()
                .any(|a| a.key == "bridge_solana_down" && a.severity == "warn")
        );
        assert!(
            alerts
                .iter()
                .any(|a| a.key == "bridge_stripe_down" && a.severity == "warn")
        );
        // No correctness page when only reachability is degraded.
        assert!(!alerts.iter().any(|a| a.severity == "page"));
    }

    #[test]
    fn clean_view_emits_no_alerts() {
        let view = BridgeView {
            conservation_ok: true,
            relayer_reachable: Some(true),
            solana_reachable: Some(true),
            stripe_reachable: Some(true),
            ..Default::default()
        };
        assert!(compute_bridge_alerts(&view).is_empty());
    }
}
