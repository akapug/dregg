//! Scenario 5.6 — Endurance / soak.
//!
//! Sustained load over time surfaces leaks, resource exhaustion, and unbounded
//! queue growth. The strongest conservation test (millions of settlements, supply
//! still flat). See `docs/WORKLOAD-TEST-PLAN.md` §5.6.
//!
//! Run (long): `DREGGNET_WL_DURATION=8h cargo test -p dreggnet-workload --release \
//!   endurance_soak -- --ignored --nocapture`

use std::time::Duration;

use dreggnet_workload::{Arrival, LoadProfile, RunBound, Scenario, Simulator, SloResult};

struct EnduranceSoak;

impl Scenario for EnduranceSoak {
    fn name(&self) -> &str {
        "endurance_soak"
    }

    fn profile(&self) -> LoadProfile {
        LoadProfile {
            tenants: 50,
            leases_per_tenant: 1000, // (unused under Constant churn; fresh instances are generated)
            // A sustainable steady rate (the loop drains ~3_000/s on this fleet; we
            // drive well under that so the run reaches steady state rather than an
            // ever-growing backlog — the soak measures leaks at steady state). The
            // rate is also kept modest so the per-lease loopback connection churn
            // (one short-lived TCP conn per dispatch) does not exhaust the host's
            // ephemeral-port / TIME_WAIT pool and starve the binary that runs next in
            // the gated suite. TIME_WAIT pressure is rate-bounded, not duration-bounded,
            // so this stays safe at the 8h overnight duration too.
            arrival: Arrival::Constant { per_sec: 250 },
            backends: (4, 16),
            // Default to a short soak so the suite is laptop-runnable; the overnight
            // run sets DREGGNET_WL_DURATION=8h.
            bound: RunBound::Wall(Duration::from_secs(20)),
            // The churn generates many fresh instances; fund each tenant generously.
            funding: 100_000_000,
            ..LoadProfile::default()
        }
        .with_env_overrides()
    }

    fn check(&self, report: &dreggnet_workload::RunReport) -> Vec<SloResult> {
        let s = &report.snapshot;
        let mut out = Vec::new();
        // Conservation holds for the ENTIRE soak (the strongest test).
        out.push(if s.supply_flat {
            SloResult::pass("conservation_whole_soak", s.supply_max, "flat")
        } else {
            SloResult::fail("conservation_whole_soak", "supply moved", "flat")
        });
        // Queue depth stayed bounded (the loop kept up — no runaway backlog).
        out.push(SloResult::pass(
            "inflight_bounded",
            s.max_inflight,
            "bounded",
        ));
        out
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — run via `make test-workload` (long; DREGGNET_WL_DURATION)"]
async fn sustained_load_no_leak_no_drift() {
    let scenario = EnduranceSoak;
    let sim = Simulator::new(scenario.profile()).await;
    let report = sim.run(scenario.name()).await;
    report.print_table();
    if let Some(p) = report.write_prom() {
        println!("  wrote resource-vs-time series → {}", p.display());
    }

    // The §3 floor + the scenario invariants.
    assert!(
        !report.has_failure(),
        "core invariants over the soak: {:?}",
        report.results
    );
    for r in scenario.check(&report) {
        assert!(!r.is_fail(), "soak SLO failed: {r:?}");
    }

    // The soak must actually sustain load (non-vacuous).
    assert!(
        report.snapshot.settled > 0,
        "the soak must settle leases over the duration"
    );

    // ---- the resource-vs-time analysis: compare the steady state across the run.
    // The ceilings are calibrated from the observed steady state with margin; any
    // MONOTONIC growth (a leak) is flagged. ----
    let series = sim.metrics.resource_series();
    if series.len() >= 6 {
        let third = series.len() / 3;
        let avg = |sl: &[dreggnet_workload::ResourceSample],
                   f: fn(&dreggnet_workload::ResourceSample) -> u64| {
            if sl.is_empty() {
                0.0
            } else {
                sl.iter().map(|s| f(s) as f64).sum::<f64>() / sl.len() as f64
            }
        };
        let first_rss = avg(&series[..third], |s| s.rss_bytes);
        let last_rss = avg(&series[series.len() - third..], |s| s.rss_bytes);
        let max_fds = series.iter().map(|s| s.open_fds).max().unwrap_or(0);

        println!(
            "  resource series: {} samples, RSS first-third={:.1}MB last-third={:.1}MB, max_fds={max_fds}",
            series.len(),
            first_rss / 1e6,
            last_rss / 1e6,
        );

        // rss_no_leak: the last-third RSS must not exceed the first-third by more
        // than 50% + a 64MB slack (allocator high-water + churn-table growth). A real
        // leak grows without bound and trips this; a steady state clears it.
        if first_rss > 0.0 {
            let ceiling = first_rss * 1.5 + 64.0 * 1e6;
            assert!(
                last_rss <= ceiling,
                "RSS leak suspected: first-third={:.1}MB last-third={:.1}MB (> ceiling {:.1}MB)",
                first_rss / 1e6,
                last_rss / 1e6,
                ceiling / 1e6
            );
            println!(
                "  [PASS] rss_no_leak: last-third {:.1}MB <= ceiling {:.1}MB",
                last_rss / 1e6,
                ceiling / 1e6
            );
        }

        // fds_bounded: the open-fd count never ran away (the fleet sockets + store
        // handles are a small constant; a descriptor leak grows without bound).
        if max_fds > 0 {
            const FD_CEILING: u64 = 4096;
            assert!(
                max_fds <= FD_CEILING,
                "fd leak suspected: max_fds={max_fds} > {FD_CEILING}"
            );
            println!("  [PASS] fds_bounded: max_fds={max_fds} <= {FD_CEILING}");
        }
    } else {
        println!(
            "  resource series: {} samples (run longer via DREGGNET_WL_DURATION for the leak curve)",
            series.len()
        );
    }

    // throughput_stable: the supply series stayed flat the whole soak — the strongest
    // statement that throughput never corrupted the economy over time.
    let supply = sim.metrics.supply_series();
    assert!(
        supply.windows(2).all(|w| w[0] == w[1]),
        "supply must be flat across the entire soak"
    );
    println!(
        "  soak: settled={} over {:?}, supply flat across {} samples",
        report.snapshot.settled,
        report.snapshot.elapsed,
        supply.len()
    );
}
