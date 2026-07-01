//! The incident log + uptime computation.
//!
//! Incidents are either operator-posted or auto-detected from health
//! transitions ([`detect_transition`]). Uptime over a window is the standard
//! status-page figure: `1 − downtime / window`, where downtime is the union of
//! "down"-severity incident intervals clipped to the window. A "degraded"
//! incident is a partial impairment and does NOT subtract from uptime (so the
//! number tracks *availability*, not perfection); an "info" notice never does.

use crate::model::{Incident, OverallStatus, UptimeWindow};

/// Parse an RFC3339 timestamp to Unix epoch seconds, best-effort.
pub fn parse_epoch(rfc3339: &str) -> Option<i64> {
    time::OffsetDateTime::parse(rfc3339, &time::format_description::well_known::Rfc3339)
        .ok()
        .map(|t| t.unix_timestamp())
}

/// Compute the uptime figure over one window ending at `now_epoch`.
///
/// Downtime is the total time inside `[now − window, now]` covered by a "down"
/// incident (open incidents run to `now`). Overlapping intervals are merged so a
/// concurrent multi-service outage is not double-counted.
pub fn uptime_window(
    label: &str,
    window_secs: u64,
    incidents: &[Incident],
    now_epoch: i64,
) -> UptimeWindow {
    let window_start = now_epoch - window_secs as i64;

    // Collect the [start, end] of every DOWN incident, clipped to the window.
    let mut intervals: Vec<(i64, i64)> = Vec::new();
    for inc in incidents {
        if inc.severity != "down" {
            continue;
        }
        let Some(start) = parse_epoch(&inc.started_at) else {
            continue;
        };
        let end = match &inc.resolved_at {
            Some(r) => parse_epoch(r).unwrap_or(now_epoch),
            None => now_epoch, // still open → runs to now
        };
        let clipped_start = start.max(window_start);
        let clipped_end = end.min(now_epoch);
        if clipped_end > clipped_start {
            intervals.push((clipped_start, clipped_end));
        }
    }

    // Merge overlapping intervals, then sum.
    intervals.sort_by_key(|i| i.0);
    let mut downtime: i64 = 0;
    let mut cur: Option<(i64, i64)> = None;
    for (s, e) in intervals {
        match cur {
            None => cur = Some((s, e)),
            Some((cs, ce)) => {
                if s <= ce {
                    cur = Some((cs, ce.max(e)));
                } else {
                    downtime += ce - cs;
                    cur = Some((s, e));
                }
            }
        }
    }
    if let Some((cs, ce)) = cur {
        downtime += ce - cs;
    }

    let downtime = downtime.max(0) as u64;
    let uptime_pct = if window_secs == 0 {
        100.0
    } else {
        let up = (window_secs.saturating_sub(downtime)) as f64;
        (up / window_secs as f64) * 100.0
    };

    UptimeWindow {
        label: label.to_string(),
        window_secs,
        // Round to 3 decimals for a clean "99.987%" display.
        uptime_pct: (uptime_pct * 1000.0).round() / 1000.0,
        downtime_secs: downtime,
    }
}

/// Auto-detect an incident transition: given the previous and current overall
/// status, return an incident to OPEN (on a fall to Degraded/Down) or `None`.
///
/// The caller threads the open incident and calls [`resolve_open`] when the
/// status recovers. This is the auto-detected half of the log; operator-posted
/// incidents are appended directly.
pub fn detect_transition(
    prev: OverallStatus,
    now: OverallStatus,
    now_rfc3339: &str,
    id: &str,
) -> Option<Incident> {
    let was_ok = matches!(prev, OverallStatus::Operational);
    let now_bad = matches!(now, OverallStatus::Degraded | OverallStatus::Down);
    if was_ok && now_bad {
        let severity = if now == OverallStatus::Down {
            "down"
        } else {
            "degraded"
        };
        Some(Incident {
            id: id.to_string(),
            title: format!("Auto-detected: {}", now.headline()),
            severity: severity.to_string(),
            started_at: now_rfc3339.to_string(),
            resolved_at: None,
            affected: Vec::new(),
            body: format!(
                "Automatically opened when overall status transitioned to {}.",
                now.slug()
            ),
        })
    } else {
        None
    }
}

/// Mark an open incident resolved at `now_rfc3339`.
pub fn resolve_open(inc: &mut Incident, now_rfc3339: &str) {
    if inc.resolved_at.is_none() {
        inc.resolved_at = Some(now_rfc3339.to_string());
    }
}
