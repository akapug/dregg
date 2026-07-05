//! Scenario 5.1 — Scale / load.
//!
//! Many concurrent leases/workloads drained through one loop over a small fleet;
//! measure throughput + latency and confirm the loop + the economy hold under
//! concurrency. See `docs/WORKLOAD-TEST-PLAN.md` §5.1.
//!
//! Run: `cargo test -p dreggnet-workload --release scale_load -- --ignored --nocapture`

use dreggnet_workload::{
    Arrival, BudgetModel, LoadProfile, RunReport, Scenario, SloResult, TierMix,
};

struct ScaleLoad {
    backends: (usize, usize),
}

impl Scenario for ScaleLoad {
    fn name(&self) -> &str {
        "scale_load"
    }

    fn profile(&self) -> LoadProfile {
        LoadProfile {
            tenants: 100,
            leases_per_tenant: 10, // 1_000 leases
            arrival: Arrival::Burst,
            tier_mix: TierMix::realistic(),
            steps_per_workload: 2,
            budget_model: BudgetModel::Funded,
            backends: self.backends,
            ..LoadProfile::default()
        }
        .with_env_overrides()
    }

    fn check(&self, report: &RunReport) -> Vec<SloResult> {
        let s = &report.snapshot;
        let (fleet, cap) = self.backends;
        let mut out = Vec::new();
        // Real now: every offered lease reached a terminal state (the loop kept up).
        out.push(if s.settled + s.lapsed >= s.watched {
            SloResult::pass("all_terminal", s.settled + s.lapsed, ">= watched")
        } else {
            SloResult::fail("all_terminal", s.settled + s.lapsed, ">= watched")
        });
        // Calibrated from the first load pass (1_000 leases, 4×16 fleet: ~2_800–2_950
        // settles/s, watch→settle p99 ~356ms of queue-wait — see tests/workload/BASELINES.md).
        // The SLO is a robust floor/ceiling with margin, not the exact observed value
        // (which would be machine-dependent + flaky): a healthy run clears these by ~10×.
        out.push(if s.settled_per_sec >= THROUGHPUT_FLOOR {
            SloResult::pass(
                "throughput_floor",
                format!("{:.0}/s", s.settled_per_sec),
                ">= 250/s",
            )
        } else {
            SloResult::fail(
                "throughput_floor",
                format!("{:.0}/s", s.settled_per_sec),
                ">= 250/s",
            )
        });
        out.push(if s.lease_p99 <= LEASE_P99_CEILING_S {
            SloResult::pass(
                "lease_p99_ceiling",
                format!("{:.1}ms", s.lease_p99 * 1e3),
                "<= 2000ms",
            )
        } else {
            SloResult::fail(
                "lease_p99_ceiling",
                format!("{:.1}ms", s.lease_p99 * 1e3),
                "<= 2000ms",
            )
        });
        // Capacity bound: no backend ever held more than its capacity; the fleet
        // round-robins, so the summed in-flight never exceeds fleet×cap.
        let ceiling = (fleet * cap) as u64;
        out.push(if s.max_inflight <= ceiling {
            SloResult::pass("capacity_bound", s.max_inflight, &format!("<= {ceiling}"))
        } else {
            SloResult::fail("capacity_bound", s.max_inflight, &format!("<= {ceiling}"))
        });
        out
    }
}

/// Calibrated SLO floors/ceilings (see `tests/workload/BASELINES.md`). Robust
/// margins over the observed baseline so a healthy run is unambiguously green.
const THROUGHPUT_FLOOR: f64 = 250.0; // settles/s; observed ~2_800–2_950 at 4×16.
const LEASE_P99_CEILING_S: f64 = 2.0; // watch→settle p99; observed ~356ms (1k-lease burst queue-wait).

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — run via `make test-workload`"]
async fn scale_load_drains_under_concurrency() {
    let scenario = ScaleLoad { backends: (4, 16) };
    let report = scenario.run().await;
    report.print_table();
    // The §3 floor (conservation + meter=settle) is asserted in every run.
    assert!(
        !report.has_failure(),
        "core invariants must hold under load: {:?}",
        report.results
    );
    for r in scenario.check(&report) {
        assert!(!r.is_fail(), "scale-load SLO failed: {r:?}");
    }
}

/// The {1,2,4,8}-backend sweep — drive each fleet size, tabulate throughput + p99
/// vs fleet size (the capacity/failover scaling curve). Conservation + all-terminal
/// must hold at every fleet size; the curve is printed for the baselines note.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — fleet-size sweep (overnight)"]
async fn scale_load_fleet_sweep() {
    println!("== scale_load fleet-size sweep (1_000 leases each) ==");
    println!("  fleet  throughput/s   lease_p50_ms  lease_p99_ms  max_inflight");
    for fleet in [1usize, 2, 4, 8] {
        let scenario = ScaleLoad {
            backends: (fleet, 16),
        };
        let report = scenario.run().await;
        let s = &report.snapshot;
        println!(
            "  {fleet:>5}  {:>11.0}   {:>11.3}  {:>11.3}  {:>11}",
            s.settled_per_sec,
            s.lease_p50 * 1e3,
            s.lease_p99 * 1e3,
            s.max_inflight
        );
        assert!(
            !report.has_failure(),
            "conservation must hold at fleet={fleet}: {:?}",
            report.results
        );
        for r in scenario.check(&report) {
            assert!(!r.is_fail(), "fleet={fleet} SLO failed: {r:?}");
        }
    }
}
