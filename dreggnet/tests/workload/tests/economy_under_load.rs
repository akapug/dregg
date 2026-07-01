//! Scenario 5.4 — Economy correctness under load.
//!
//! Conservation (Σδ=0), no double-charge, and meter=settle hold under *concurrent*
//! settlement — the economy is the thing most likely to corrupt under races. See
//! `docs/WORKLOAD-TEST-PLAN.md` §5.4.
//!
//! Run: `cargo test -p dreggnet-workload --release economy -- --ignored --nocapture`

use std::sync::Arc;

use dreggnet_control::{ConservingLedger, LeaseCharge, Settlement};
use dreggnet_workload::{BudgetModel, LoadProfile, RunReport, Scenario, Simulator, SloResult};

struct EconomyUnderLoad;

impl Scenario for EconomyUnderLoad {
    fn name(&self) -> &str {
        "economy_under_load"
    }

    fn profile(&self) -> LoadProfile {
        LoadProfile {
            tenants: 200,
            leases_per_tenant: 4,
            backends: (8, 16),
            budget_model: BudgetModel::Mixed(0.2), // 20% lapse
            ..LoadProfile::default()
        }
        .with_env_overrides()
    }

    fn check(&self, report: &RunReport) -> Vec<SloResult> {
        let s = &report.snapshot;
        let mut out = Vec::new();
        // Conservation flat at every sampled instant (not just the end).
        out.push(if s.supply_flat {
            SloResult::pass("conservation_every_instant", s.supply_max, "flat")
        } else {
            SloResult::fail(
                "conservation_every_instant",
                format!("[{}..{}]", s.supply_min, s.supply_max),
                "flat",
            )
        });
        // The metered total equals the settled total under contention.
        out.push(if s.metered_units == s.settled_units {
            SloResult::pass("meter_eq_settle_concurrent", s.settled_units, "== metered")
        } else {
            SloResult::fail(
                "meter_eq_settle_concurrent",
                format!("m={} s={}", s.metered_units, s.settled_units),
                "==",
            )
        });
        out
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
#[ignore = "workload-simulation suite — run via `make test-workload`"]
async fn economy_conserves_under_concurrent_settlement() {
    let scenario = EconomyUnderLoad;
    let sim = Simulator::new(scenario.profile()).await;
    let asset = sim.profile.asset.clone();
    let start = sim.ledger.total_supply(&asset);
    let report = sim.run(scenario.name()).await;
    report.print_table();

    // Supply unchanged across all settlements (the per-instant sampler is in `run`).
    assert_eq!(
        sim.ledger.total_supply(&asset),
        start,
        "Σδ = 0 across concurrent settlement"
    );
    assert!(
        !report.has_failure(),
        "core invariants: {:?}",
        report.results
    );
    for r in scenario.check(&report) {
        assert!(!r.is_fail(), "economy SLO failed: {r:?}");
    }

    // ---- debit == credit reconciliation: Σ tenant debits == Σ backend credits ----
    let funding = sim.profile.funding;
    let total_debit: i64 = sim
        .tenants
        .iter()
        .map(|t| funding - sim.ledger.balance(&asset, &t.id))
        .sum();
    let (fleet, _cap) = sim.profile.backends;
    let total_credit: i64 = (0..fleet)
        .map(|i| sim.ledger.balance(&asset, &format!("backend-{i}")))
        .sum();
    assert_eq!(
        total_debit, total_credit,
        "Σ debits ({total_debit}) must equal Σ credits ({total_credit}) per asset"
    );
    assert!(
        total_debit > 0,
        "the run must settle real value (non-vacuous)"
    );

    // ---- re-drive already-settled leases: the dedup is a hard idempotency key,
    // not a timing artifact — re-settling moves no value. ----
    let before = sim.ledger.total_supply(&asset);
    let mut replays = 0;
    for t in &sim.tenants {
        for tl in &t.leases {
            for period in 1..=2 {
                let charge = LeaseCharge::new(&t.id, "backend-0", &asset, &tl.instance, period, 1);
                if let Ok(r) = sim.ledger.settle(&charge) {
                    if r.replayed {
                        replays += 1;
                    }
                }
            }
        }
    }
    assert_eq!(
        sim.ledger.total_supply(&asset),
        before,
        "re-drive must move nothing"
    );
    assert!(
        replays > 0,
        "the re-drive must observe replays (the dedup is real)"
    );
    println!("  economy: Σdebit={total_debit}=Σcredit, {replays} re-drive replays, supply flat");
}

/// The racing-settle construction: many threads settle the SAME `(lease, period)`
/// key concurrently against one live `ConservingLedger`. Exactly one charge lands
/// (the beneficiary is credited exactly once); every other call observes the
/// recorded receipt (`replayed`). The dedup is a hard idempotency key under a real
/// data race, not a timing artifact.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
#[ignore = "workload-simulation suite — racing settle on one key (overnight)"]
async fn racing_settle_on_one_key_charges_exactly_once() {
    const RACERS: usize = 64;
    const KEYS: usize = 200;
    let ledger = Arc::new(ConservingLedger::new());
    // Fund the payer enough to (incorrectly) cover KEYS charges many times over, so
    // a dedup failure WOULD show up as extra value moved (the test can detect it).
    ledger.fund("USD", "lessee", (KEYS as i64) * (RACERS as i64) * 10);
    let supply_before = ledger.total_supply("USD");

    let mut handles = Vec::new();
    for key in 0..KEYS {
        let lease_id = format!("race-lease-{key}");
        for _ in 0..RACERS {
            let l = ledger.clone();
            let lid = lease_id.clone();
            handles.push(tokio::spawn(async move {
                let charge = LeaseCharge::new("lessee", "provider", "USD", &lid, 1, 7);
                // Every racer submits the identical charge; all return Ok, but only
                // one moves value — the rest replay.
                l.settle(&charge).map(|r| r.replayed).unwrap_or(true)
            }));
        }
    }
    let mut fresh_charges = 0;
    for h in handles {
        let replayed = h.await.expect("racer joined");
        if !replayed {
            fresh_charges += 1;
        }
    }

    // Exactly one fresh charge per key landed — never RACERS of them.
    assert_eq!(
        fresh_charges, KEYS,
        "exactly one fresh charge per key under the race (got {fresh_charges}, want {KEYS})"
    );
    // The provider was credited exactly KEYS×7 — not RACERS×KEYS×7.
    assert_eq!(
        ledger.balance("USD", "provider"),
        (KEYS as i64) * 7,
        "the beneficiary was credited exactly once per key"
    );
    // Conservation across the whole race.
    assert_eq!(
        ledger.total_supply("USD"),
        supply_before,
        "Σδ = 0 across {} concurrent racing settles",
        KEYS * RACERS
    );
    println!(
        "  racing_settle: {} threads on {KEYS} keys → exactly {KEYS} charges, provider credited once/key",
        KEYS * RACERS
    );
}
