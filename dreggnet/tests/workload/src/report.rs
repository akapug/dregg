//! The run report — the SLO/invariant verdict a scenario's `check()` produces,
//! plus the metric snapshot and the Prometheus exposition text (the plan §4/§7).

use crate::metrics::MetricSnapshot;

/// One SLO or invariant result. The scaffold ships `Todo` placeholders; the
/// overnight run replaces them with calibrated thresholds (`Pass`/`Fail`).
#[derive(Debug, Clone)]
pub enum SloResult {
    /// A checked SLO/invariant with its measured value and verdict.
    Checked {
        name: String,
        measured: String,
        threshold: String,
        pass: bool,
    },
    /// Not yet calibrated — the overnight run fills the threshold in.
    Todo { name: String, note: String },
}

impl SloResult {
    pub fn pass(name: &str, measured: impl ToString, threshold: &str) -> Self {
        SloResult::Checked {
            name: name.to_string(),
            measured: measured.to_string(),
            threshold: threshold.to_string(),
            pass: true,
        }
    }
    pub fn fail(name: &str, measured: impl ToString, threshold: &str) -> Self {
        SloResult::Checked {
            name: name.to_string(),
            measured: measured.to_string(),
            threshold: threshold.to_string(),
            pass: false,
        }
    }
    pub fn todo(name: &str, note: &str) -> Self {
        SloResult::Todo {
            name: name.to_string(),
            note: note.to_string(),
        }
    }
    pub fn is_pass(&self) -> bool {
        matches!(self, SloResult::Checked { pass: true, .. })
    }
    pub fn is_fail(&self) -> bool {
        matches!(self, SloResult::Checked { pass: false, .. })
    }
}

/// The full result of a scenario run: the metric snapshot + the SLO table + the
/// Prometheus text. Scenarios assert against `results` and may write `prometheus`
/// to `target/workload/<scenario>.prom`.
#[derive(Debug, Clone)]
pub struct RunReport {
    pub scenario: String,
    pub snapshot: MetricSnapshot,
    pub results: Vec<SloResult>,
    pub prometheus: String,
}

impl RunReport {
    /// Any hard FAIL (a calibrated SLO that did not meet its threshold)?
    pub fn has_failure(&self) -> bool {
        self.results.iter().any(|r| r.is_fail())
    }

    /// Write the Prometheus exposition text to `target/workload/<scenario>.prom`
    /// (the plan §4 sink — scrapeable into the same Grafana the deploy uses).
    /// Returns the path written (best-effort; logs + continues on an IO error).
    pub fn write_prom(&self) -> Option<std::path::PathBuf> {
        let dir = std::path::Path::new("target/workload");
        if let Err(e) = std::fs::create_dir_all(dir) {
            eprintln!("workload: could not create {}: {e}", dir.display());
            return None;
        }
        let path = dir.join(format!("{}.prom", self.scenario));
        match std::fs::write(&path, &self.prometheus) {
            Ok(()) => Some(path),
            Err(e) => {
                eprintln!("workload: could not write {}: {e}", path.display());
                None
            }
        }
    }

    /// A short stdout table (the `--nocapture` view).
    pub fn print_table(&self) {
        println!("== workload scenario: {} ==", self.scenario);
        let s = &self.snapshot;
        println!(
            "  watched={} settled={} lapsed={} failover={} throughput={:.1}/s",
            s.watched, s.settled, s.lapsed, s.failed_over, s.settled_per_sec
        );
        println!(
            "  lease p50={:.3}ms p99={:.3}ms  finality p99={:.3}ms  max_inflight={}",
            s.lease_p50 * 1e3,
            s.lease_p99 * 1e3,
            s.finality_p99 * 1e3,
            s.max_inflight
        );
        println!(
            "  conservation: supply_flat={} [{}..{}]  meter_units={} settled_units={}",
            s.supply_flat, s.supply_min, s.supply_max, s.metered_units, s.settled_units
        );
        for r in &self.results {
            match r {
                SloResult::Checked {
                    name,
                    measured,
                    threshold,
                    pass,
                } => println!(
                    "  [{}] {name}: {measured} (slo {threshold})",
                    if *pass { "PASS" } else { "FAIL" }
                ),
                SloResult::Todo { name, note } => {
                    println!("  [TODO(overnight)] {name}: {note}")
                }
            }
        }
    }
}
