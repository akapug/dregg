//! Per-request observability for the gateway serving loop.
//!
//! The hand-rolled connection loop ([`crate`]'s serving binary) records one
//! sample per served request — the surface it hit (machines / hosting / ask),
//! the response status class, the byte count, and the wall-clock latency — into
//! a process-wide [`Metrics`] of lock-free atomics. The counters render as
//! Prometheus text on `GET /metrics`, so the gateway joins the existing
//! Prometheus/Grafana stack (`docs/MONITORING.md`) instead of leaving request
//! rate, error rate, and tail latency invisible.
//!
//! This is purely additive: recording a sample never changes what a client sees
//! on the wire.

use std::sync::atomic::{AtomicU64, Ordering};

/// The serving surface a request was routed to — the dimension the request
/// counters break down by.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Surface {
    /// The fly-machines control API (`/v1/apps/...`) + the friendly root/status.
    Machines,
    /// A published `<name>.example.com` static minisite.
    Hosting,
    /// The Caddy on-demand-TLS `ask` probe (`/internal/site-exists`).
    Ask,
    /// Anything rejected before routing (a malformed request, a timeout, an
    /// over-cap body) — recorded so abusive traffic is visible too.
    Other,
}

impl Surface {
    const COUNT: usize = 4;

    const fn index(self) -> usize {
        match self {
            Surface::Machines => 0,
            Surface::Hosting => 1,
            Surface::Ask => 2,
            Surface::Other => 3,
        }
    }

    /// The Prometheus label / log field for this surface.
    pub const fn label(self) -> &'static str {
        match self {
            Surface::Machines => "machines",
            Surface::Hosting => "hosting",
            Surface::Ask => "ask",
            Surface::Other => "other",
        }
    }

    const fn all() -> [Surface; Surface::COUNT] {
        [
            Surface::Machines,
            Surface::Hosting,
            Surface::Ask,
            Surface::Other,
        ]
    }
}

/// Status-class buckets: index `n` holds responses with status `n00..n99`
/// (index 0 is the catch-all for anything outside 1xx–5xx).
const CLASS_COUNT: usize = 6;
const CLASS_LABELS: [&str; CLASS_COUNT] = ["other", "1xx", "2xx", "3xx", "4xx", "5xx"];

fn class_index(status: u16) -> usize {
    let c = (status / 100) as usize;
    if (1..=5).contains(&c) { c } else { 0 }
}

/// Process-wide gateway request metrics (lock-free).
#[derive(Debug, Default)]
pub struct Metrics {
    /// `requests_total[surface][class]`.
    requests: [[AtomicU64; CLASS_COUNT]; Surface::COUNT],
    /// Total response bytes written to sockets.
    response_bytes: AtomicU64,
    /// Sum of request-handling latencies, in microseconds.
    duration_micros_sum: AtomicU64,
    /// Total requests served (the count for the latency summary).
    requests_total: AtomicU64,
    /// Responses with a 5xx status (server errors) + connection-level faults.
    errors_total: AtomicU64,
}

impl Metrics {
    /// A fresh, all-zero metrics set.
    pub fn new() -> Metrics {
        Metrics::default()
    }

    /// Record one served request: its surface, response status, the bytes
    /// written to the socket, and the handling latency in microseconds.
    pub fn record(&self, surface: Surface, status: u16, bytes: usize, latency_micros: u64) {
        let class = class_index(status);
        self.requests[surface.index()][class].fetch_add(1, Ordering::Relaxed);
        self.requests_total.fetch_add(1, Ordering::Relaxed);
        self.response_bytes
            .fetch_add(bytes as u64, Ordering::Relaxed);
        self.duration_micros_sum
            .fetch_add(latency_micros, Ordering::Relaxed);
        if status >= 500 {
            self.errors_total.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Record a connection-level fault (a socket error with no HTTP response).
    pub fn record_connection_error(&self) {
        self.errors_total.fetch_add(1, Ordering::Relaxed);
    }

    /// Render the metrics as a Prometheus text-format exposition.
    pub fn render_prometheus(&self) -> String {
        let mut out = String::with_capacity(1024);

        out.push_str(
            "# HELP gateway_requests_total Requests served, by surface and status class.\n",
        );
        out.push_str("# TYPE gateway_requests_total counter\n");
        for surface in Surface::all() {
            for class in 1..CLASS_COUNT {
                let n = self.requests[surface.index()][class].load(Ordering::Relaxed);
                if n == 0 {
                    continue;
                }
                out.push_str(&format!(
                    "gateway_requests_total{{surface=\"{}\",status=\"{}\"}} {n}\n",
                    surface.label(),
                    CLASS_LABELS[class],
                ));
            }
            // The catch-all class only appears if it actually fired.
            let other = self.requests[surface.index()][0].load(Ordering::Relaxed);
            if other != 0 {
                out.push_str(&format!(
                    "gateway_requests_total{{surface=\"{}\",status=\"other\"}} {other}\n",
                    surface.label(),
                ));
            }
        }

        let total = self.requests_total.load(Ordering::Relaxed);
        let bytes = self.response_bytes.load(Ordering::Relaxed);
        let micros = self.duration_micros_sum.load(Ordering::Relaxed);
        let errors = self.errors_total.load(Ordering::Relaxed);
        let seconds = micros as f64 / 1_000_000.0;

        out.push_str(
            "# HELP gateway_response_bytes_total Total response bytes written to sockets.\n",
        );
        out.push_str("# TYPE gateway_response_bytes_total counter\n");
        out.push_str(&format!("gateway_response_bytes_total {bytes}\n"));

        out.push_str("# HELP gateway_request_duration_seconds Request handling latency.\n");
        out.push_str("# TYPE gateway_request_duration_seconds summary\n");
        out.push_str(&format!("gateway_request_duration_seconds_sum {seconds}\n"));
        out.push_str(&format!("gateway_request_duration_seconds_count {total}\n"));

        out.push_str("# HELP gateway_errors_total Server-error responses and connection faults.\n");
        out.push_str("# TYPE gateway_errors_total counter\n");
        out.push_str(&format!("gateway_errors_total {errors}\n"));

        out
    }

    /// Total requests recorded (for tests / introspection).
    pub fn total(&self) -> u64 {
        self.requests_total.load(Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_and_renders() {
        let m = Metrics::new();
        m.record(Surface::Hosting, 200, 1024, 500);
        m.record(Surface::Hosting, 404, 80, 100);
        m.record(Surface::Machines, 500, 50, 200);
        m.record(Surface::Ask, 200, 0, 30);

        assert_eq!(m.total(), 4);
        let text = m.render_prometheus();
        assert!(text.contains("gateway_requests_total{surface=\"hosting\",status=\"2xx\"} 1"));
        assert!(text.contains("gateway_requests_total{surface=\"hosting\",status=\"4xx\"} 1"));
        assert!(text.contains("gateway_requests_total{surface=\"machines\",status=\"5xx\"} 1"));
        assert!(text.contains("gateway_requests_total{surface=\"ask\",status=\"2xx\"} 1"));
        assert!(text.contains("gateway_response_bytes_total 1154"));
        assert!(text.contains("gateway_request_duration_seconds_count 4"));
        // One 5xx → one error.
        assert!(text.contains("gateway_errors_total 1"));
    }

    #[test]
    fn class_index_buckets() {
        assert_eq!(class_index(200), 2);
        assert_eq!(class_index(204), 2);
        assert_eq!(class_index(301), 3);
        assert_eq!(class_index(404), 4);
        assert_eq!(class_index(503), 5);
        assert_eq!(class_index(999), 0);
    }
}
