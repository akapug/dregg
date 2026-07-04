//! Historical-log viewers — the browsable, filterable "what happened" ledger.
//!
//! Where [`crate::aggregate`] answers *what is the cloud doing right now*, this
//! module answers *what has happened* in a form a human can open, read, and filter.
//! It normalizes every historical surface the snapshot already carries into one
//! uniform [`HistoryEvent`] stream, then lets the operator slice it by **category**
//! (turns / events / leases-machines / compute / economy / bridge), by **who**
//! (the agent / cell / tenant / rail), by **what** (the effect / action / kind), by
//! free text, and by a **time window** — the five viewers the admin portal asks for,
//! served from one faceted endpoint.
//!
//! The unification is deliberate: a single sortable timeline of `(when, category,
//! who, what, result, detail, conservation)` rows is what makes the history
//! *browsable* (one place, newest-first) AND keeps the per-viewer slices honest
//! (the category facet + quick-filters are just projections of the one stream). The
//! builders are pure functions over the fetched JSON, so they unit-test against the
//! real upstream shapes (see the tests at the bottom).

use serde::Serialize;
use serde_json::Value;

use crate::aggregate::CloudSnapshot;

/// One normalized row in the historical log — the atom every viewer renders.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct HistoryEvent {
    /// Unix epoch SECONDS for sorting/filtering. `0` when the source carried no
    /// usable timestamp (these sort to the end, never silently to "now").
    pub ts_epoch: i64,
    /// A human-readable timestamp for display (RFC3339-ish, normalized).
    pub when: String,
    /// Which viewer this belongs to: `turn` · `event` · `lease` · `machine` ·
    /// `compute` · `economy` · `bridge`.
    pub category: String,
    /// Who acted / was charged / was placed — the agent, cell, tenant, or rail.
    pub who: String,
    /// What happened — the effect, action, lifecycle transition, or bridge kind.
    pub what: String,
    /// The outcome — finality, status, machine state, or "conserving".
    pub result: String,
    /// A one-line human summary (units, amounts, region, …).
    pub detail: String,
    /// A conservation note where the surface carries one (`""` otherwise), e.g.
    /// `Σδ=0 (conserving)` for the metered economy, `live ≤ locked` for the bridge.
    pub conservation: String,
}

/// Build the full, unsorted historical-event stream from a snapshot. Every
/// historical surface the snapshot carries is normalized in; the caller filters +
/// sorts (see [`HistoryFilter::apply`]).
pub fn build_history(snap: &CloudSnapshot) -> Vec<HistoryEvent> {
    let mut out = Vec::new();
    // The receipt chain / turn log — enriched with the per-turn effects pulled from
    // the committed-event feed (receipts carry counts + finality; events carry the
    // effect names), so the "what" column is meaningful on the turn viewer.
    let effects_by_turn = index_effects_by_turn(snap.node.recent_events.as_ref());
    from_receipts(
        snap.node.recent_receipts.as_ref(),
        &effects_by_turn,
        &mut out,
    );
    from_events(snap.node.recent_events.as_ref(), &mut out);
    from_machines(&snap.gateway.machines, &mut out);
    // The compute-runs viewer (one row per lease/workflow instance).
    from_durable_jobs(&snap.durable.jobs, &mut out);
    // The economy viewer: the granular per-charge ledger when the outbox exposes
    // it, else a per-lease fallback so the viewer is never empty on an older node.
    if snap.durable.charges.is_empty() {
        economy_from_jobs(&snap.durable.jobs, &mut out);
    } else {
        from_durable_charges(&snap.durable.charges, &mut out);
    }
    from_bot_activity(snap.bot.activity.as_ref(), &mut out);
    from_bridge(&snap.bridge, &mut out);
    out
}

/// The set of categories the history stream can carry, in viewer order. Used to
/// drive the quick-filter buttons even before any data has arrived.
pub const CATEGORIES: &[&str] = &["turn", "event", "machine", "compute", "economy", "bridge"];

// ----------------------------------------------------------------------------
// Per-surface normalizers (pure over the fetched JSON).
// ----------------------------------------------------------------------------

/// Map `turn_hash -> "effect,effect"` from the committed-event feed, so the turn
/// log can show which effects a receipt's turn actually committed.
fn index_effects_by_turn(events: Option<&Value>) -> std::collections::HashMap<String, String> {
    let mut map = std::collections::HashMap::new();
    if let Some(arr) = events.and_then(|v| v.as_array()) {
        for e in arr {
            let Some(th) = e.get("turn_hash").and_then(|v| v.as_str()) else {
                continue;
            };
            let effects = join_effects(e.get("effects"));
            if !effects.is_empty() {
                map.entry(th.to_string()).or_insert(effects);
            }
        }
    }
    map
}

/// The receipt chain → the turn log: who (agent), what (effects), when, result
/// (finality), and the work done (computrons / action count / proof).
fn from_receipts(
    receipts: Option<&Value>,
    effects_by_turn: &std::collections::HashMap<String, String>,
    out: &mut Vec<HistoryEvent>,
) {
    let Some(arr) = receipts.and_then(|v| v.as_array()) else {
        return;
    };
    for r in arr {
        let turn = str_field(r, "turn_hash");
        let agent = str_field(r, "agent");
        let finality = str_field(r, "finality");
        let actions = num_field(r, "action_count");
        let computrons = num_field(r, "computrons_used");
        let has_proof = r
            .get("has_proof")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let effects = effects_by_turn.get(&turn).cloned().unwrap_or_default();
        let (ts_epoch, when) = parse_ts(r.get("timestamp"));
        let what = if effects.is_empty() {
            match actions {
                Some(n) => format!("{n} action(s)"),
                None => "turn".to_string(),
            }
        } else {
            effects
        };
        let mut detail = format!("turn {}", short(&turn, 14));
        if let Some(c) = computrons {
            detail.push_str(&format!(" · {c} computrons"));
        }
        if let Some(n) = actions {
            detail.push_str(&format!(" · {n} action(s)"));
        }
        detail.push_str(if has_proof {
            " · proof ✓"
        } else {
            " · no proof"
        });
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "turn".into(),
            who: if agent.is_empty() {
                "—".into()
            } else {
                agent
            },
            what,
            result: if finality.is_empty() {
                "—".into()
            } else {
                finality
            },
            detail,
            conservation: String::new(),
        });
    }
}

/// The committed-event feed → the effect-level ledger: which cell, which effects,
/// at what height, with what status.
fn from_events(events: Option<&Value>, out: &mut Vec<HistoryEvent>) {
    let Some(arr) = events.and_then(|v| v.as_array()) else {
        return;
    };
    for e in arr {
        let cell = str_field(e, "cell_id");
        let turn = str_field(e, "turn_hash");
        let height = num_field(e, "height");
        let status = status_str(e.get("status"));
        let effects = join_effects(e.get("effects"));
        let (ts_epoch, when) = parse_ts(e.get("timestamp"));
        let mut detail = String::new();
        if let Some(h) = height {
            detail.push_str(&format!("h{h}"));
        }
        if !turn.is_empty() {
            if !detail.is_empty() {
                detail.push_str(" · ");
            }
            detail.push_str(&format!("turn {}", short(&turn, 12)));
        }
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "event".into(),
            who: if cell.is_empty() {
                "—".into()
            } else {
                short(&cell, 18)
            },
            what: if effects.is_empty() {
                "(no effects)".into()
            } else {
                effects
            },
            result: if status.is_empty() {
                "—".into()
            } else {
                status
            },
            detail,
            conservation: String::new(),
        });
    }
}

/// The gateway's machines → the compute/machine lifecycle viewer: each machine's
/// current state, region, and meter units, timestamped by its last update.
fn from_machines(machines: &[Value], out: &mut Vec<HistoryEvent>) {
    for m in machines {
        let app = str_field(m, "app");
        let name = str_field(m, "name");
        let id = str_field(m, "id");
        let state = str_field(m, "state");
        let region = str_field(m, "region");
        let meter = m
            .get("dregg")
            .and_then(|d| d.get("meter_units"))
            .and_then(|v| v.as_i64());
        let (ts_epoch, when) = parse_ts(m.get("updated_at").or_else(|| m.get("created_at")));
        let who = if name.is_empty() {
            short(&id, 14)
        } else {
            name.clone()
        };
        let mut detail = format!("{}/{}", app, who);
        if !region.is_empty() {
            detail.push_str(&format!(" · {region}"));
        }
        if let Some(u) = meter {
            detail.push_str(&format!(" · {u} meter units"));
        }
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "machine".into(),
            who: if app.is_empty() {
                who
            } else {
                format!("{app}/{who}")
            },
            what: "machine".into(),
            result: if state.is_empty() {
                "—".into()
            } else {
                state
            },
            detail,
            conservation: String::new(),
        });
    }
}

/// The durable meter outbox → the compute-runs viewer: each lease/workflow
/// instance's metered steps + units charged. The economy flow is emitted
/// separately (per-charge via [`from_durable_charges`], or per-lease via
/// [`economy_from_jobs`] as a fallback) so the two viewers stay distinct.
fn from_durable_jobs(jobs: &[crate::pg::DurableJob], out: &mut Vec<HistoryEvent>) {
    for j in jobs {
        let (ts_epoch, when) = parse_ts_str(j.last_charge_at.as_deref());
        let lease = short(&j.lease_id, 28);
        let resource = crate::pg::classify_resource(&j.lease_id);
        let what = if resource == "compute" {
            "metered run".to_string()
        } else {
            format!("{resource} hosting")
        };
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "compute".into(),
            who: lease,
            what,
            result: j.status.clone(),
            detail: format!("{} step(s) · {} units charged", j.periods, j.units_charged),
            conservation: String::new(),
        });
    }
}

/// The per-charge meter ledger → the economy viewer: one conserving `$DREGG`
/// charge per metered step, classified by the resource it bills (compute lease vs
/// a hosting `bandwidth`/`uptime`/`publish`/`cert`/`build` bill).
fn from_durable_charges(charges: &[crate::pg::MeterCharge], out: &mut Vec<HistoryEvent>) {
    for c in charges {
        let (ts_epoch, when) = parse_ts_str(c.charged_at.as_deref());
        let what = if c.resource == "compute" {
            "compute charge".to_string()
        } else {
            format!("{} bill", c.resource)
        };
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "economy".into(),
            who: short(&c.lease_id, 28),
            what,
            result: format!("step {}", c.period),
            detail: format!(
                "{} $DREGG · running {} · {}",
                c.amount, c.running_total, c.resource
            ),
            conservation: "Σδ=0 (conserving meter)".into(),
        });
    }
}

/// Per-lease economy fallback (used only when the outbox does not expose the raw
/// per-charge rows): one row per lease with its total units charged.
fn economy_from_jobs(jobs: &[crate::pg::DurableJob], out: &mut Vec<HistoryEvent>) {
    for j in jobs {
        let (ts_epoch, when) = parse_ts_str(j.last_charge_at.as_deref());
        let resource = crate::pg::classify_resource(&j.lease_id);
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "economy".into(),
            who: short(&j.lease_id, 28),
            what: if resource == "compute" {
                "lease charge".to_string()
            } else {
                format!("{resource} bill")
            },
            result: j.status.clone(),
            detail: format!(
                "{} $DREGG units over {} step(s)",
                j.units_charged, j.periods
            ),
            conservation: "Σδ=0 (conserving meter)".into(),
        });
    }
}

/// The bot's app/hermes activity → an app-action history row (who acted, on what).
fn from_bot_activity(activity: Option<&Value>, out: &mut Vec<HistoryEvent>) {
    let Some(arr) = activity.and_then(|v| v.as_array()) else {
        return;
    };
    for a in arr {
        let app = str_field(a, "app");
        let action = str_field(a, "action");
        let actor = str_field(a, "actor_discord_id");
        let subject = str_field(a, "subject");
        let status = str_field(a, "status");
        let (ts_epoch, when) = parse_ts(a.get("timestamp"));
        let mut detail = format!("{app}.{action}");
        if !subject.is_empty() {
            detail.push_str(&format!(" · {}", short(&subject, 28)));
        }
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "event".into(),
            who: if actor.is_empty() {
                app.clone()
            } else {
                short(&actor, 16)
            },
            what: if action.is_empty() {
                "app action".into()
            } else {
                action
            },
            result: if status.is_empty() {
                "—".into()
            } else {
                status
            },
            detail,
            conservation: String::new(),
        });
    }
}

/// The bridge's recent lock→mint / redeem activity + its conservation ledgers →
/// the bridge viewer: each mint/burn timestamped, with the conservation verdict.
fn from_bridge(bridge: &crate::bridge::BridgeView, out: &mut Vec<HistoryEvent>) {
    // The per-rail conservation verdict, to annotate each rail's activity rows.
    let mut conserved_by_rail: std::collections::HashMap<String, bool> =
        std::collections::HashMap::new();
    for l in &bridge.ledgers {
        conserved_by_rail.insert(l.rail.clone(), l.conserved);
    }
    for a in &bridge.recent {
        let (ts_epoch, when) = parse_ts(a.when.as_ref());
        let cons = match conserved_by_rail.get(&a.rail) {
            Some(true) => "live ≤ locked (conserved)".to_string(),
            Some(false) => "BREACH (live > locked)".to_string(),
            None => "un-observed".to_string(),
        };
        let mut detail = a.rail.clone();
        if let Some(amt) = a.amount {
            detail.push_str(&format!(" · {amt}"));
        }
        if let Some(cell) = &a.cell {
            detail.push_str(&format!(" · cell {}", short(cell, 12)));
        }
        out.push(HistoryEvent {
            ts_epoch,
            when,
            category: "bridge".into(),
            who: a.rail.clone(),
            what: a.kind.clone(),
            result: a.status.clone(),
            detail,
            conservation: cons,
        });
    }
}

// ----------------------------------------------------------------------------
// Filtering + faceting.
// ----------------------------------------------------------------------------

/// A parsed history query — the slice the operator asked for.
#[derive(Debug, Clone, Default)]
pub struct HistoryFilter {
    /// Restrict to one category (`turn`/`event`/`machine`/`compute`/`economy`/`bridge`).
    pub category: Option<String>,
    /// Substring match against `who` (case-insensitive).
    pub who: Option<String>,
    /// Substring match against `what` — the effect/action filter (case-insensitive).
    pub what: Option<String>,
    /// Free-text substring across who/what/result/detail (case-insensitive).
    pub text: Option<String>,
    /// Only events at or after this epoch second.
    pub since_epoch: Option<i64>,
    /// Only events at or before this epoch second.
    pub until_epoch: Option<i64>,
    /// Cap the returned rows (after sort). Defaults to [`DEFAULT_LIMIT`].
    pub limit: usize,
}

/// The default row cap when a query does not specify one.
pub const DEFAULT_LIMIT: usize = 500;
/// The hard ceiling on returned rows (a runaway `limit=` is clamped here).
pub const MAX_LIMIT: usize = 5000;

impl HistoryFilter {
    /// Parse a filter from a URL query string. Recognizes `category`, `who`,
    /// `what`/`effect`, `q`/`text`, `since`, `until`, `limit`. The time params
    /// accept an RFC3339 instant, a bare epoch second, OR a relative window
    /// (`30m` / `6h` / `7d`) interpreted as "now minus that" (for `since`).
    pub fn from_query(query: &str, now_epoch: i64) -> HistoryFilter {
        let mut f = HistoryFilter {
            limit: DEFAULT_LIMIT,
            ..Default::default()
        };
        for (k, v) in parse_query(query) {
            match k.as_str() {
                "category" | "cat" => f.category = nonempty(&v),
                "who" => f.who = nonempty(&v),
                "what" | "effect" => f.what = nonempty(&v),
                "q" | "text" => f.text = nonempty(&v),
                "since" => f.since_epoch = parse_when_filter(&v, now_epoch, true),
                "until" => f.until_epoch = parse_when_filter(&v, now_epoch, false),
                "limit" => {
                    if let Ok(n) = v.parse::<usize>() {
                        f.limit = n.clamp(1, MAX_LIMIT);
                    }
                }
                _ => {}
            }
        }
        f
    }

    /// Apply the filter: keep matching rows, sort newest-first (unknown timestamps
    /// last), and truncate to `limit`.
    pub fn apply(&self, events: Vec<HistoryEvent>) -> Vec<HistoryEvent> {
        let mut kept: Vec<HistoryEvent> = events.into_iter().filter(|e| self.matches(e)).collect();
        // Newest first; a 0 epoch (unknown time) sorts to the very end.
        kept.sort_by(|a, b| {
            let ka = if a.ts_epoch == 0 {
                i64::MIN
            } else {
                a.ts_epoch
            };
            let kb = if b.ts_epoch == 0 {
                i64::MIN
            } else {
                b.ts_epoch
            };
            kb.cmp(&ka)
        });
        kept.truncate(self.limit);
        kept
    }

    fn matches(&self, e: &HistoryEvent) -> bool {
        if let Some(c) = &self.category {
            if !e.category.eq_ignore_ascii_case(c) {
                return false;
            }
        }
        if let Some(w) = &self.who {
            if !contains_ci(&e.who, w) {
                return false;
            }
        }
        if let Some(w) = &self.what {
            if !contains_ci(&e.what, w) {
                return false;
            }
        }
        if let Some(t) = &self.text {
            let hay = format!("{} {} {} {}", e.who, e.what, e.result, e.detail);
            if !contains_ci(&hay, t) {
                return false;
            }
        }
        if let Some(since) = self.since_epoch {
            if e.ts_epoch != 0 && e.ts_epoch < since {
                return false;
            }
        }
        if let Some(until) = self.until_epoch {
            if e.ts_epoch != 0 && e.ts_epoch > until {
                return false;
            }
        }
        true
    }
}

/// A count by key, sorted descending by count then key — drives the filter chips.
#[derive(Debug, Clone, Serialize)]
pub struct Facet {
    pub key: String,
    pub count: usize,
}

/// The facets over an (unfiltered) history stream — what the filter UI offers.
#[derive(Debug, Clone, Serialize)]
pub struct HistoryFacets {
    /// Counts per category, in [`CATEGORIES`] order (zero-filled so every viewer
    /// shows even when empty).
    pub categories: Vec<Facet>,
    /// The most active actors (`who`), capped.
    pub actors: Vec<Facet>,
    /// The most common effects/actions (`what`), capped.
    pub effects: Vec<Facet>,
    /// Total events before filtering.
    pub total: usize,
}

/// Compute the facets over the full stream.
pub fn facets(events: &[HistoryEvent]) -> HistoryFacets {
    use std::collections::HashMap;
    let mut cat: HashMap<&str, usize> = HashMap::new();
    let mut who: HashMap<&str, usize> = HashMap::new();
    let mut what: HashMap<&str, usize> = HashMap::new();
    for e in events {
        *cat.entry(e.category.as_str()).or_insert(0) += 1;
        if e.who != "—" && !e.who.is_empty() {
            *who.entry(e.who.as_str()).or_insert(0) += 1;
        }
        if e.what != "—" && !e.what.is_empty() {
            *what.entry(e.what.as_str()).or_insert(0) += 1;
        }
    }
    // Categories: zero-filled, in canonical viewer order.
    let categories = CATEGORIES
        .iter()
        .map(|c| Facet {
            key: (*c).to_string(),
            count: *cat.get(*c).unwrap_or(&0),
        })
        .collect();
    HistoryFacets {
        categories,
        actors: top_facets(who, 20),
        effects: top_facets(what, 20),
        total: events.len(),
    }
}

fn top_facets(map: std::collections::HashMap<&str, usize>, cap: usize) -> Vec<Facet> {
    let mut v: Vec<Facet> = map
        .into_iter()
        .map(|(k, c)| Facet {
            key: k.to_string(),
            count: c,
        })
        .collect();
    v.sort_by(|a, b| b.count.cmp(&a.count).then_with(|| a.key.cmp(&b.key)));
    v.truncate(cap);
    v
}

/// The full history response the `/api/history` endpoint serves: the facets over
/// the whole stream + the filtered, sorted, capped rows.
#[derive(Debug, Clone, Serialize)]
pub struct HistoryView {
    pub generated_at: String,
    /// Total events before the filter (so the UI can show "showing N of M").
    pub total: usize,
    /// Events after the filter (before the limit truncation).
    pub matched: usize,
    pub facets: HistoryFacets,
    pub events: Vec<HistoryEvent>,
}

/// Build the full history view for a snapshot under a query string.
pub fn build_view(snap: &CloudSnapshot, query: &str, now_epoch: i64) -> HistoryView {
    let all = build_history(snap);
    let facets = facets(&all);
    let total = all.len();
    let filter = HistoryFilter::from_query(query, now_epoch);
    // Count matches before the limit truncation for the "showing N of M" line.
    let matched = all.iter().filter(|e| filter.matches(e)).count();
    let events = filter.apply(all);
    HistoryView {
        generated_at: snap.generated_at.clone(),
        total,
        matched,
        facets,
        events,
    }
}

// ----------------------------------------------------------------------------
// Small helpers.
// ----------------------------------------------------------------------------

fn str_field(v: &Value, key: &str) -> String {
    v.get(key)
        .and_then(|x| x.as_str())
        .map(|s| s.to_string())
        .unwrap_or_default()
}

fn num_field(v: &Value, key: &str) -> Option<i64> {
    v.get(key).and_then(|x| x.as_i64())
}

/// Render an effects array (`["transfer","mint"]`) as `"transfer,mint"`. Tolerates
/// effects given as objects with a `kind`/`type` discriminant.
fn join_effects(v: Option<&Value>) -> String {
    let Some(arr) = v.and_then(|x| x.as_array()) else {
        return String::new();
    };
    arr.iter()
        .map(|e| match e {
            Value::String(s) => s.clone(),
            Value::Object(_) => e
                .get("kind")
                .or_else(|| e.get("type"))
                .and_then(|k| k.as_str())
                .map(|s| s.to_string())
                .unwrap_or_else(|| "effect".to_string()),
            other => other.to_string(),
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// Render a status that may be a string (`"finalized"`) or an enum object
/// (`{"committed":{}}` / `{"failed":"reason"}`) into a flat label.
fn status_str(v: Option<&Value>) -> String {
    match v {
        Some(Value::String(s)) => s.clone(),
        Some(Value::Object(m)) => m.keys().next().cloned().unwrap_or_default(),
        Some(other) => other.to_string().trim_matches('"').to_string(),
        None => String::new(),
    }
}

/// Truncate with an ellipsis (char-safe).
fn short(s: &str, n: usize) -> String {
    if s.chars().count() > n {
        let t: String = s.chars().take(n).collect();
        format!("{t}…")
    } else {
        s.to_string()
    }
}

fn contains_ci(haystack: &str, needle: &str) -> bool {
    haystack.to_lowercase().contains(&needle.to_lowercase())
}

fn nonempty(s: &str) -> Option<String> {
    let t = s.trim();
    if t.is_empty() {
        None
    } else {
        Some(t.to_string())
    }
}

/// Parse a timestamp `Value` (epoch number — seconds OR millis — or an RFC3339
/// string) into `(epoch_seconds, display)`. Unknown → `(0, "")`.
pub fn parse_ts(v: Option<&Value>) -> (i64, String) {
    match v {
        Some(Value::Number(n)) => {
            if let Some(i) = n.as_i64() {
                // Heuristic: values past ~ year 2603 in seconds are really millis.
                let secs = if i > 20_000_000_000 { i / 1000 } else { i };
                (secs, epoch_to_rfc3339(secs))
            } else {
                (0, String::new())
            }
        }
        Some(Value::String(s)) => parse_ts_str(Some(s)),
        _ => (0, String::new()),
    }
}

/// Parse an optional timestamp string (RFC3339 or a bare epoch) into
/// `(epoch_seconds, display)`.
pub fn parse_ts_str(s: Option<&str>) -> (i64, String) {
    let Some(s) = s.map(|x| x.trim()).filter(|x| !x.is_empty()) else {
        return (0, String::new());
    };
    // A bare integer string is an epoch.
    if let Ok(i) = s.parse::<i64>() {
        let secs = if i > 20_000_000_000 { i / 1000 } else { i };
        return (secs, epoch_to_rfc3339(secs));
    }
    // Otherwise try RFC3339.
    match time::OffsetDateTime::parse(s, &time::format_description::well_known::Rfc3339) {
        Ok(dt) => (dt.unix_timestamp(), s.to_string()),
        Err(_) => (0, s.to_string()),
    }
}

fn epoch_to_rfc3339(secs: i64) -> String {
    time::OffsetDateTime::from_unix_timestamp(secs)
        .ok()
        .and_then(|dt| {
            dt.format(&time::format_description::well_known::Rfc3339)
                .ok()
        })
        .unwrap_or_default()
}

/// Parse a `since`/`until` filter value: RFC3339, a bare epoch, or a relative
/// window (`30m`/`6h`/`7d`/`90s`). For a relative window, `subtract=true` (the
/// `since` case) returns `now - window`; otherwise `now` itself.
fn parse_when_filter(s: &str, now_epoch: i64, subtract: bool) -> Option<i64> {
    let s = s.trim();
    if s.is_empty() || s.eq_ignore_ascii_case("all") {
        return None;
    }
    if let Some(secs) = parse_relative_window(s) {
        return Some(if subtract {
            now_epoch - secs
        } else {
            now_epoch
        });
    }
    let (e, _) = parse_ts_str(Some(s));
    if e == 0 { None } else { Some(e) }
}

/// Parse `90s` / `30m` / `6h` / `7d` into seconds. `None` if not that shape.
fn parse_relative_window(s: &str) -> Option<i64> {
    let s = s.trim();
    let (num, unit) = s.split_at(s.find(|c: char| !c.is_ascii_digit())?);
    let n: i64 = num.parse().ok()?;
    let mult = match unit {
        "s" => 1,
        "m" => 60,
        "h" => 3600,
        "d" => 86_400,
        "w" => 604_800,
        _ => return None,
    };
    Some(n * mult)
}

/// Parse `a=1&b=two` into `(key, value)` pairs with minimal percent-decoding.
fn parse_query(query: &str) -> Vec<(String, String)> {
    query
        .split('&')
        .filter(|kv| !kv.is_empty())
        .map(|kv| {
            let (k, v) = kv.split_once('=').unwrap_or((kv, ""));
            (k.to_string(), pct_decode(v))
        })
        .collect()
}

/// Minimal percent + `+` decoding for query values.
fn pct_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let Ok(b) = u8::from_str_radix(&s[i + 1..i + 3], 16) {
                out.push(b);
                i += 3;
                continue;
            }
        }
        out.push(if bytes[i] == b'+' { b' ' } else { bytes[i] });
        i += 1;
    }
    String::from_utf8_lossy(&out).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    /// A realistic snapshot fragment exercising every surface.
    fn fixture() -> CloudSnapshot {
        let mut snap = CloudSnapshot {
            generated_at: "2026-06-29T12:00:00Z".into(),
            health: sample_health(),
            sources: vec![],
            node: crate::aggregate::NodeView {
                recent_receipts: Some(json!([
                    {"chain_index":7,"turn_hash":"0xabc123def456","agent":"agent:alice",
                     "timestamp":"2026-06-29T11:59:00Z","computrons_used":42,"action_count":2,
                     "finality":"finalized","has_proof":true},
                    {"chain_index":6,"turn_hash":"0xdeadbeef0001","agent":"agent:bob",
                     "timestamp":1_751_200_000,"computrons_used":10,"action_count":1,
                     "finality":"pending","has_proof":false}
                ])),
                recent_events: Some(json!([
                    {"height":101,"turn_hash":"0xabc123def456","cell_id":"cell:lease:xyz",
                     "timestamp":"2026-06-29T11:59:00Z","status":"committed","effects":["transfer","mint"]},
                    {"height":100,"turn_hash":"0xdeadbeef0001","cell_id":"cell:user:bob",
                     "timestamp":"2026-06-29T11:58:00Z","status":{"failed":{}},"effects":["transfer"]}
                ])),
                ..Default::default()
            },
            gateway: crate::aggregate::GatewayView {
                status: None,
                machines: vec![json!({
                    "app":"demo","id":"m-001","name":"web-1","state":"started","region":"iad",
                    "updated_at":"2026-06-29T11:55:00Z","dregg":{"meter_units":120}
                })],
            },
            bot: crate::aggregate::BotView::default(),
            durable: crate::pg::DurableView {
                jobs: vec![crate::pg::DurableJob {
                    lease_id: "host:bandwidth:site-7".into(),
                    periods: 5,
                    units_charged: 250,
                    last_charge_at: Some("2026-06-29T11:50:00Z".into()),
                    status: "active".into(),
                }],
                ..Default::default()
            },
            bridge: sample_bridge(),
        };
        // The default health builder above is fine; mutate nothing.
        let _ = &mut snap;
        snap
    }

    fn sample_health() -> crate::aggregate::CloudHealth {
        crate::aggregate::CloudHealth {
            overall: "healthy".into(),
            node: "up".into(),
            gateway: "up".into(),
            bot: "not-deployed".into(),
            postgres: "up".into(),
            backend: "up".into(),
            federation_members: Some(1),
            consensus_live: Some(true),
            node_finalizing: Some(true),
            consensus_divergence: Some(0.0),
            tau_prefix_shifts: Some(0.0),
            gossip_messages: Some(0.0),
            gossip_stream_rejected: Some(0.0),
            finality_latency_avg: None,
            machines: Some(1),
            durable_jobs_in_flight: 1,
            total_units_spent: 250,
            block_height: Some(101),
            peers: Some(0),
            pg_active_connections: Some(3),
            pg_max_connections: Some(100),
            pg_db_size_bytes: Some(1024),
            bridge_relayer: "not-configured".into(),
            bridge_solana: "not-configured".into(),
            bridge_stripe: "not-configured".into(),
            bridge_conservation_ok: Some(true),
            bridge_mints_observed: 1,
            alerts: vec![],
        }
    }

    fn sample_bridge() -> crate::bridge::BridgeView {
        crate::bridge::BridgeView {
            ledgers: vec![crate::bridge::MirrorLedger {
                rail: "solana".into(),
                asset: "wDREGG".into(),
                live_supply: 100,
                locked_or_backing: 100,
                backing_label: "locked".into(),
                conserved: true,
                locks_consumed: 3,
            }],
            recent: vec![
                crate::bridge::BridgeActivity {
                    when: Some(json!("2026-06-29T11:45:00Z")),
                    kind: "bridgemint".into(),
                    rail: "solana".into(),
                    amount: Some(50),
                    cell: Some("cell:bridge:in".into()),
                    status: "committed".into(),
                },
                crate::bridge::BridgeActivity {
                    when: Some(json!("2026-06-29T11:40:00Z")),
                    kind: "burn".into(),
                    rail: "solana".into(),
                    amount: Some(20),
                    cell: None,
                    status: "committed".into(),
                },
            ],
            ..Default::default()
        }
    }

    #[test]
    fn builds_rows_from_every_surface() {
        let snap = fixture();
        let all = build_history(&snap);
        let cats: std::collections::HashSet<&str> =
            all.iter().map(|e| e.category.as_str()).collect();
        // Every viewer is represented.
        for c in ["turn", "event", "machine", "compute", "economy", "bridge"] {
            assert!(cats.contains(c), "missing category {c} in {cats:?}");
        }
    }

    #[test]
    fn turn_log_enriches_effects_from_events() {
        let snap = fixture();
        let all = build_history(&snap);
        let turn = all
            .iter()
            .find(|e| e.category == "turn" && e.who == "agent:alice")
            .expect("alice turn");
        // The turn picked up its committed effects from the event feed.
        assert_eq!(turn.what, "transfer,mint");
        assert_eq!(turn.result, "finalized");
        assert!(turn.detail.contains("proof ✓"));
    }

    #[test]
    fn economy_rows_are_marked_conserving() {
        // No raw charges in the base fixture → the per-lease economy fallback.
        let snap = fixture();
        let all = build_history(&snap);
        let econ = all.iter().find(|e| e.category == "economy").unwrap();
        assert!(econ.conservation.contains("conserving"));
        assert!(econ.detail.contains("250 $DREGG"));
    }

    #[test]
    fn economy_uses_per_charge_ledger_when_present() {
        let mut snap = fixture();
        snap.durable.charges = vec![
            crate::pg::MeterCharge {
                lease_id: "host:bandwidth:site-7".into(),
                period: 3,
                amount: 50,
                running_total: 150,
                charged_at: Some("2026-06-29T11:50:00Z".into()),
                resource: "bandwidth".into(),
            },
            crate::pg::MeterCharge {
                lease_id: "wf-uuid-1".into(),
                period: 1,
                amount: 20,
                running_total: 20,
                charged_at: Some("2026-06-29T11:48:00Z".into()),
                resource: "compute".into(),
            },
        ];
        let all = build_history(&snap);
        let econ: Vec<_> = all.iter().filter(|e| e.category == "economy").collect();
        // The economy viewer now reflects the per-charge ledger (2 charges), NOT
        // the single per-lease fallback row.
        assert_eq!(econ.len(), 2);
        assert!(
            econ.iter()
                .any(|e| e.what == "bandwidth bill" && e.detail.contains("50 $DREGG"))
        );
        assert!(econ.iter().any(|e| e.what == "compute charge"));
        // The compute viewer still shows the lease run, classified by resource.
        let compute: Vec<_> = all.iter().filter(|e| e.category == "compute").collect();
        assert!(compute.iter().any(|e| e.what == "bandwidth hosting"));
    }

    #[test]
    fn bridge_rows_carry_conservation_verdict() {
        let snap = fixture();
        let all = build_history(&snap);
        let mint = all
            .iter()
            .find(|e| e.category == "bridge" && e.what == "bridgemint")
            .unwrap();
        assert!(mint.conservation.contains("conserved"));
        assert_eq!(mint.detail, "solana · 50 · cell cell:bridge:…");
    }

    #[test]
    fn filter_by_category_and_text() {
        let snap = fixture();
        let v = build_view(&snap, "category=bridge", 1_751_200_000);
        assert!(v.events.iter().all(|e| e.category == "bridge"));
        assert_eq!(v.events.len(), 2);

        let v2 = build_view(&snap, "q=mint", 1_751_200_000);
        assert!(v2.events.iter().any(|e| e.what.contains("mint")));
        assert!(v2.events.iter().all(|e| {
            let hay = format!("{} {} {} {}", e.who, e.what, e.result, e.detail);
            hay.to_lowercase().contains("mint")
        }));
    }

    #[test]
    fn filter_by_who_substring() {
        let snap = fixture();
        let v = build_view(&snap, "who=alice", 1_751_200_000);
        assert!(!v.events.is_empty());
        assert!(
            v.events
                .iter()
                .all(|e| e.who.to_lowercase().contains("alice"))
        );
    }

    #[test]
    fn newest_first_ordering() {
        let snap = fixture();
        let v = build_view(&snap, "", 1_751_300_000);
        // Descending by epoch; the first non-zero-ts row is the newest.
        let stamped: Vec<i64> = v
            .events
            .iter()
            .map(|e| e.ts_epoch)
            .filter(|t| *t != 0)
            .collect();
        let mut sorted = stamped.clone();
        sorted.sort_by(|a, b| b.cmp(a));
        assert_eq!(stamped, sorted, "events must be newest-first");
    }

    #[test]
    fn relative_since_window_filters() {
        let snap = fixture();
        // now = 2026-06-29T12:00:00Z (epoch 1_782_? ); use a fixed now well after.
        let now = parse_ts_str(Some("2026-06-29T12:00:00Z")).0;
        // A 20-minute window keeps only the >=11:40 rows; an 8-minute window prunes more.
        let wide = build_view(&snap, "since=20m", now);
        let narrow = build_view(&snap, "since=8m", now);
        assert!(
            narrow.events.len() < wide.events.len(),
            "narrow window {} should keep fewer than wide {}",
            narrow.events.len(),
            wide.events.len()
        );
    }

    #[test]
    fn facets_zero_fill_categories() {
        let empty = CloudSnapshot {
            generated_at: "2026-06-29T12:00:00Z".into(),
            health: sample_health(),
            sources: vec![],
            node: crate::aggregate::NodeView::default(),
            gateway: crate::aggregate::GatewayView::default(),
            bot: crate::aggregate::BotView::default(),
            durable: crate::pg::DurableView::default(),
            bridge: crate::bridge::BridgeView::default(),
        };
        let v = build_view(&empty, "", 0);
        assert_eq!(v.total, 0);
        // Every viewer category is still present (zero-filled) for the filter chips.
        assert_eq!(v.facets.categories.len(), CATEGORIES.len());
        assert!(v.facets.categories.iter().all(|f| f.count == 0));
    }

    #[test]
    fn limit_is_clamped() {
        let f = HistoryFilter::from_query("limit=99999999", 0);
        assert_eq!(f.limit, MAX_LIMIT);
        let f2 = HistoryFilter::from_query("limit=0", 0);
        assert_eq!(f2.limit, 1);
    }

    #[test]
    fn parse_ts_handles_epoch_seconds_and_millis() {
        assert_eq!(parse_ts(Some(&json!(1_751_200_000))).0, 1_751_200_000);
        // millis collapse to the same second
        assert_eq!(
            parse_ts(Some(&json!(1_751_200_000_000i64))).0,
            1_751_200_000
        );
        assert_eq!(parse_ts(Some(&json!("not-a-time"))).0, 0);
    }
}
