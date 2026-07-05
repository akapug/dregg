//! The measurement core — what every scenario records (the plan §4).
//!
//! A lock-light collector: atomic lifecycle counters + a per-phase latency sample
//! buffer (percentiles computed on snapshot) + periodic conservation/resource
//! snapshots. `prometheus()` emits the run's series in exposition format so a soak
//! run scrapes into the same Grafana the deploy uses (the MONITORING.md shape).

use std::sync::Mutex;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use std::time::Duration;

/// A lease lifecycle transition the harness observes.
#[derive(Debug, Clone, Copy)]
pub enum LeaseEvent {
    Watched,
    Settled {
        meter_units: i64,
        settled_units: i64,
    },
    Lapsed,
    Reaped,
    Unplaced,
    FailedOver,
}

/// The run's measurement state. `Arc<Metrics>` is shared across the loop drive.
#[derive(Default)]
pub struct Metrics {
    pub watched: AtomicU64,
    pub settled: AtomicU64,
    pub lapsed: AtomicU64,
    pub reaped: AtomicU64,
    pub unplaced: AtomicU64,
    pub failed_over: AtomicU64,
    pub metered_units: AtomicI64,
    pub settled_units: AtomicI64,
    /// Per-lease `watched→settled` latencies (seconds), for p50/p99.
    lease_latency_s: Mutex<Vec<f64>>,
    /// Per-period `metered→settled` finality latencies (seconds).
    finality_latency_s: Mutex<Vec<f64>>,
    /// Sampled in-flight (queue depth) gauge over the run.
    inflight_samples: Mutex<Vec<u64>>,
    /// Sampled `total_supply(asset)` over the run (conservation must be flat).
    supply_samples: Mutex<Vec<i64>>,
    /// Sampled resource snapshots (the soak series).
    resource_samples: Mutex<Vec<ResourceSample>>,
}

/// A point-in-time resource reading (the soak/leak series).
#[derive(Debug, Clone, Copy, Default)]
pub struct ResourceSample {
    pub at_s: f64,
    pub rss_bytes: u64,
    pub open_fds: u64,
    pub durable_store_bytes: u64,
}

impl Metrics {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a lifecycle transition.
    pub fn observe(&self, ev: LeaseEvent) {
        match ev {
            LeaseEvent::Watched => {
                self.watched.fetch_add(1, Ordering::Relaxed);
            }
            LeaseEvent::Settled {
                meter_units,
                settled_units,
            } => {
                self.settled.fetch_add(1, Ordering::Relaxed);
                self.metered_units.fetch_add(meter_units, Ordering::Relaxed);
                self.settled_units
                    .fetch_add(settled_units, Ordering::Relaxed);
            }
            LeaseEvent::Lapsed => {
                self.lapsed.fetch_add(1, Ordering::Relaxed);
            }
            LeaseEvent::Reaped => {
                self.reaped.fetch_add(1, Ordering::Relaxed);
            }
            LeaseEvent::Unplaced => {
                self.unplaced.fetch_add(1, Ordering::Relaxed);
            }
            LeaseEvent::FailedOver => {
                self.failed_over.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    pub fn record_lease_latency(&self, d: Duration) {
        self.lease_latency_s.lock().unwrap().push(d.as_secs_f64());
    }
    pub fn record_finality_latency(&self, d: Duration) {
        self.finality_latency_s
            .lock()
            .unwrap()
            .push(d.as_secs_f64());
    }
    pub fn sample_inflight(&self, n: u64) {
        self.inflight_samples.lock().unwrap().push(n);
    }
    pub fn sample_supply(&self, supply: i64) {
        self.supply_samples.lock().unwrap().push(supply);
    }
    pub fn sample_resource(&self, s: ResourceSample) {
        self.resource_samples.lock().unwrap().push(s);
    }

    /// The full resource series (the soak leak/bound analysis reads this).
    pub fn resource_series(&self) -> Vec<ResourceSample> {
        self.resource_samples.lock().unwrap().clone()
    }

    /// The supply series (every sampled `total_supply` — conservation-over-time).
    pub fn supply_series(&self) -> Vec<i64> {
        self.supply_samples.lock().unwrap().clone()
    }

    /// A snapshot: percentiles + throughput inputs (the SLO check reads this).
    pub fn snapshot(&self, elapsed: Duration) -> MetricSnapshot {
        let lease = self.lease_latency_s.lock().unwrap().clone();
        let finality = self.finality_latency_s.lock().unwrap().clone();
        let supply = self.supply_samples.lock().unwrap().clone();
        let inflight = self.inflight_samples.lock().unwrap().clone();
        let secs = elapsed.as_secs_f64().max(1e-9);
        MetricSnapshot {
            watched: self.watched.load(Ordering::Relaxed),
            settled: self.settled.load(Ordering::Relaxed),
            lapsed: self.lapsed.load(Ordering::Relaxed),
            reaped: self.reaped.load(Ordering::Relaxed),
            failed_over: self.failed_over.load(Ordering::Relaxed),
            metered_units: self.metered_units.load(Ordering::Relaxed),
            settled_units: self.settled_units.load(Ordering::Relaxed),
            settled_per_sec: self.settled.load(Ordering::Relaxed) as f64 / secs,
            lease_p50: pct(&lease, 0.50),
            lease_p99: pct(&lease, 0.99),
            finality_p50: pct(&finality, 0.50),
            finality_p99: pct(&finality, 0.99),
            max_inflight: inflight.iter().copied().max().unwrap_or(0),
            // Conservation: supply is flat iff min == max across all samples.
            supply_flat: supply.windows(2).all(|w| w[0] == w[1]),
            supply_min: supply.iter().copied().min().unwrap_or(0),
            supply_max: supply.iter().copied().max().unwrap_or(0),
            elapsed,
        }
    }

    /// Emit the run's series in Prometheus exposition format (the plan §4 names).
    pub fn prometheus(&self, scenario: &str, elapsed: Duration) -> String {
        let s = self.snapshot(elapsed);
        let l = |name: &str, help: &str, ty: &str, val: String| {
            format!(
                "# HELP {name} {help}\n# TYPE {name} {ty}\n{name}{{scenario=\"{scenario}\"}} {val}\n"
            )
        };
        let mut out = String::new();
        out += &l(
            "dreggnet_wl_watched_total",
            "leases watched",
            "counter",
            s.watched.to_string(),
        );
        out += &l(
            "dreggnet_wl_settled_total",
            "leases settled",
            "counter",
            s.settled.to_string(),
        );
        out += &l(
            "dreggnet_wl_lapsed_total",
            "leases lapsed/reaped",
            "counter",
            s.lapsed.to_string(),
        );
        out += &l(
            "dreggnet_wl_failover_total",
            "dispatches that failed over",
            "counter",
            s.failed_over.to_string(),
        );
        out += &l(
            "dreggnet_wl_settled_per_second",
            "settle throughput",
            "gauge",
            format!("{:.3}", s.settled_per_sec),
        );
        out += &l(
            "dreggnet_wl_lease_latency_seconds_p50",
            "watch→settle p50",
            "gauge",
            format!("{:.6}", s.lease_p50),
        );
        out += &l(
            "dreggnet_wl_lease_latency_seconds_p99",
            "watch→settle p99",
            "gauge",
            format!("{:.6}", s.lease_p99),
        );
        out += &l(
            "dreggnet_wl_finality_latency_seconds_p99",
            "meter→settle p99",
            "gauge",
            format!("{:.6}", s.finality_p99),
        );
        out += &l(
            "dreggnet_wl_inflight_max",
            "max queue depth",
            "gauge",
            s.max_inflight.to_string(),
        );
        out += &l(
            "dreggnet_wl_conservation_supply",
            "asset total_supply (must be flat)",
            "gauge",
            s.supply_max.to_string(),
        );
        for r in self.resource_samples.lock().unwrap().iter() {
            out += &format!(
                "dreggnet_wl_rss_bytes{{scenario=\"{scenario}\",at=\"{:.0}\"}} {}\n",
                r.at_s, r.rss_bytes
            );
            out += &format!(
                "dreggnet_wl_durable_store_bytes{{scenario=\"{scenario}\",at=\"{:.0}\"}} {}\n",
                r.at_s, r.durable_store_bytes
            );
        }
        out
    }
}

/// A computed snapshot (percentiles, throughput, conservation).
#[derive(Debug, Clone)]
pub struct MetricSnapshot {
    pub watched: u64,
    pub settled: u64,
    pub lapsed: u64,
    pub reaped: u64,
    pub failed_over: u64,
    pub metered_units: i64,
    pub settled_units: i64,
    pub settled_per_sec: f64,
    pub lease_p50: f64,
    pub lease_p99: f64,
    pub finality_p50: f64,
    pub finality_p99: f64,
    pub max_inflight: u64,
    pub supply_flat: bool,
    pub supply_min: i64,
    pub supply_max: i64,
    pub elapsed: Duration,
}

/// The `q`-quantile of a sample set (nearest-rank), in seconds. Empty → 0.0.
fn pct(samples: &[f64], q: f64) -> f64 {
    if samples.is_empty() {
        return 0.0;
    }
    let mut v = samples.to_vec();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let idx = ((q * v.len() as f64).ceil() as usize).saturating_sub(1);
    v[idx.min(v.len() - 1)]
}

/// Sample the current process resource use (best-effort, cross-platform).
///
/// Reads RSS + the open-fd count without adding a dependency:
///   - **Linux**: `/proc/self/statm` (RSS pages × page size) + a count of the
///     `/proc/self/fd` entries.
///   - **macOS / BSD**: `ps -o rss= -p <pid>` (KiB) + a count of `/dev/fd`.
/// On any read failure the field stays `0` (best-effort — a zero never trips a
/// leak SLO since the soak compares the steady-state series, not absolute zero).
pub fn sample_process(at_s: f64, durable_store_bytes: u64) -> ResourceSample {
    ResourceSample {
        at_s,
        rss_bytes: read_rss_bytes(),
        open_fds: read_open_fds(),
        durable_store_bytes,
    }
}

/// Resident set size, in bytes (best-effort; `0` on failure).
pub fn read_rss_bytes() -> u64 {
    #[cfg(target_os = "linux")]
    {
        if let Ok(s) = std::fs::read_to_string("/proc/self/statm") {
            // Fields are in pages; the 2nd is resident.
            if let Some(resident) = s
                .split_whitespace()
                .nth(1)
                .and_then(|v| v.parse::<u64>().ok())
            {
                let page = 4096u64; // the near-universal page size; good enough for a trend.
                return resident * page;
            }
        }
        0
    }
    #[cfg(not(target_os = "linux"))]
    {
        // `ps` reports RSS in KiB on macOS/BSD.
        let pid = std::process::id();
        let out = std::process::Command::new("ps")
            .args(["-o", "rss=", "-p", &pid.to_string()])
            .output();
        if let Ok(o) = out {
            if let Ok(s) = String::from_utf8(o.stdout) {
                if let Ok(kib) = s.trim().parse::<u64>() {
                    return kib * 1024;
                }
            }
        }
        0
    }
}

/// The number of open file descriptors (best-effort; `0` on failure).
pub fn read_open_fds() -> u64 {
    #[cfg(target_os = "linux")]
    let dir = "/proc/self/fd";
    #[cfg(not(target_os = "linux"))]
    let dir = "/dev/fd";
    std::fs::read_dir(dir)
        .map(|d| d.count() as u64)
        .unwrap_or(0)
}
