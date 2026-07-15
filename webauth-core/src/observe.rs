//! Observability for the forward-auth edge: process-wide decision **metrics**
//! (a Prometheus text exposition at `GET /metrics`) and a structured
//! per-decision **audit** line.
//!
//! An auth edge that cannot be investigated after an incident is not operable.
//! Before this module the server emitted only startup banners; now every
//! admit/deny/throttle carries a machine-readable audit record (subject, cap,
//! reason, client, latency) and increments a counter a scrape can read.
//!
//! Zero new dependencies: the Prometheus body is hand-rolled text (the format is
//! trivial and stable) and the audit line is emitted through the small JSON
//! writer in [`crate::json`], so a `subject` or `reason` carrying a quote or
//! newline can never break the record.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use crate::json::JsonObject;

/// Process-wide counters for the forward-auth edge. All fields are monotone
/// counters (a scrape reads deltas); cheap relaxed atomics on the hot path.
#[derive(Debug, Default)]
pub struct Metrics {
    /// Total requests routed (every method/path).
    pub requests: AtomicU64,
    /// `/auth` admits.
    pub admit: AtomicU64,
    /// `/auth` denies mapped to 401 (unauthenticated).
    pub deny_401: AtomicU64,
    /// `/auth` denies mapped to 403 (authenticated but uncapped).
    pub deny_403: AtomicU64,
    /// Requests refused by the per-IP token bucket (429).
    pub rate_limited: AtomicU64,
    /// Requests refused because the client IP is in an escalating lockout (429).
    pub locked_out: AtomicU64,
    /// Connections shed at accept time because the worker pool was saturated (503).
    pub shed: AtomicU64,
    /// Proof-of-possession signature verifications that failed.
    pub pop_fail: AtomicU64,
    /// Login PoP replays blocked by the single-use nonce cache.
    pub replay_blocked: AtomicU64,
    /// Break-glass admits.
    pub break_glass: AtomicU64,
    /// Break-glass attempts that did NOT match (a failed override).
    pub break_glass_fail: AtomicU64,
    /// Decisions where a presented credential was in the revocation deny-set.
    pub revoked_hits: AtomicU64,
    /// Successful `POST /login` (a session cookie was minted).
    pub logins_ok: AtomicU64,
    /// `POST /login` rejections (bad credential / failed PoP / expired / forged).
    pub logins_fail: AtomicU64,
    /// 4xx for a malformed/oversized/unsupported request the parser rejected.
    pub bad_request: AtomicU64,
    /// 5xx the server itself raised (e.g. an unreadable credential wire schema).
    pub server_error: AtomicU64,
    /// Hot revocation-file reloads applied without a restart.
    pub reloads: AtomicU64,
}

impl Metrics {
    pub fn incr(field: &AtomicU64) {
        field.fetch_add(1, Ordering::Relaxed);
    }

    fn get(field: &AtomicU64) -> u64 {
        field.load(Ordering::Relaxed)
    }

    /// Render the Prometheus text exposition (`# HELP`/`# TYPE` + one line per
    /// counter). `uptime_secs` is a gauge the caller supplies.
    pub fn render_prometheus(&self, uptime_secs: u64) -> String {
        let mut out = String::with_capacity(2048);
        let counters: &[(&str, &str, u64)] = &[
            (
                "webauth_requests_total",
                "requests routed",
                Self::get(&self.requests),
            ),
            (
                "webauth_admit_total",
                "/auth admits",
                Self::get(&self.admit),
            ),
            (
                "webauth_deny_401_total",
                "/auth 401 unauthenticated denies",
                Self::get(&self.deny_401),
            ),
            (
                "webauth_deny_403_total",
                "/auth 403 uncapped denies",
                Self::get(&self.deny_403),
            ),
            (
                "webauth_rate_limited_total",
                "requests refused by the per-IP token bucket",
                Self::get(&self.rate_limited),
            ),
            (
                "webauth_locked_out_total",
                "requests refused by escalating lockout",
                Self::get(&self.locked_out),
            ),
            (
                "webauth_shed_total",
                "connections shed at accept (pool saturated)",
                Self::get(&self.shed),
            ),
            (
                "webauth_pop_fail_total",
                "proof-of-possession signature failures",
                Self::get(&self.pop_fail),
            ),
            (
                "webauth_replay_blocked_total",
                "login PoP replays blocked",
                Self::get(&self.replay_blocked),
            ),
            (
                "webauth_break_glass_total",
                "break-glass admits",
                Self::get(&self.break_glass),
            ),
            (
                "webauth_break_glass_fail_total",
                "failed break-glass attempts",
                Self::get(&self.break_glass_fail),
            ),
            (
                "webauth_revoked_hits_total",
                "revocation deny-set hits",
                Self::get(&self.revoked_hits),
            ),
            (
                "webauth_logins_ok_total",
                "successful logins",
                Self::get(&self.logins_ok),
            ),
            (
                "webauth_logins_fail_total",
                "rejected logins",
                Self::get(&self.logins_fail),
            ),
            (
                "webauth_bad_request_total",
                "4xx malformed requests",
                Self::get(&self.bad_request),
            ),
            (
                "webauth_server_error_total",
                "5xx server errors",
                Self::get(&self.server_error),
            ),
            (
                "webauth_reloads_total",
                "hot revocation reloads applied",
                Self::get(&self.reloads),
            ),
        ];
        for (name, help, val) in counters {
            out.push_str(&format!(
                "# HELP {name} {help}\n# TYPE {name} counter\n{name} {val}\n"
            ));
        }
        out.push_str(
            "# HELP webauth_uptime_seconds process uptime\n# TYPE webauth_uptime_seconds gauge\n",
        );
        out.push_str(&format!("webauth_uptime_seconds {uptime_secs}\n"));
        out
    }
}

/// A structured audit record for one decision, emitted as a single JSON line to
/// stderr. Fields are added with the typed setters so an attacker-influenced
/// `subject`/`reason` is escaped, never interpolated raw.
pub struct AuditRecord {
    obj: JsonObject,
}

impl AuditRecord {
    pub fn new(event: &str) -> Self {
        let mut obj = JsonObject::new();
        obj.str("event", event);
        Self { obj }
    }
    pub fn str(mut self, key: &str, value: &str) -> Self {
        self.obj.str(key, value);
        self
    }
    pub fn opt_str(mut self, key: &str, value: Option<&str>) -> Self {
        match value {
            Some(v) => self.obj.str(key, v),
            None => self.obj.null(key),
        };
        self
    }
    pub fn int(mut self, key: &str, value: u64) -> Self {
        self.obj.int(key, value as i64);
        self
    }
    pub fn bool(mut self, key: &str, value: bool) -> Self {
        self.obj.bool(key, value);
        self
    }
    /// Emit the record to stderr (one line). A no-op sink is used in tests.
    pub fn emit(self) {
        eprintln!("{}", self.obj.finish());
    }
    /// The rendered JSON line (used by tests and by [`AuditRecord::emit`]).
    pub fn line(self) -> String {
        self.obj.finish()
    }
}

/// Milliseconds elapsed since `start`, saturating.
pub fn elapsed_ms(start: Instant) -> u64 {
    start.elapsed().as_millis().min(u64::MAX as u128) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prometheus_render_has_counters() {
        let m = Metrics::default();
        Metrics::incr(&m.admit);
        Metrics::incr(&m.admit);
        Metrics::incr(&m.deny_401);
        let text = m.render_prometheus(42);
        assert!(text.contains("webauth_admit_total 2"), "{text}");
        assert!(text.contains("webauth_deny_401_total 1"), "{text}");
        assert!(text.contains("webauth_uptime_seconds 42"), "{text}");
        assert!(
            text.contains("# TYPE webauth_admit_total counter"),
            "{text}"
        );
    }

    #[test]
    fn audit_line_escapes_hostile_fields() {
        let line = AuditRecord::new("auth")
            .str("subject", "dregg:evil\",\"admin\":true")
            .opt_str("cap", None)
            .int("status", 200)
            .bool("admitted", true)
            .line();
        // The injected quote is escaped, so no spurious admin field appears.
        assert!(line.starts_with('{') && line.ends_with('}'), "{line}");
        assert!(
            !line.contains("\"admin\":true"),
            "injection escaped: {line}"
        );
        assert!(
            line.contains("\\\"admin\\\""),
            "the quote is escaped: {line}"
        );
        assert!(line.contains("\"cap\":null"), "{line}");
        assert!(line.contains("\"status\":200"), "{line}");
        assert!(line.contains("\"admitted\":true"), "{line}");
    }
}
