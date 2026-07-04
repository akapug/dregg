//! Scenario 5.2 — Multi-tenant isolation.
//!
//! Tenants cannot see, affect, or be billed for each other — the cap bound, the
//! sandbox, the metering separation. Cross-tenant attempts are refused, not
//! silently executed. See `docs/WORKLOAD-TEST-PLAN.md` §5.2.
//!
//! The harness models the isolation substrate the real system commits in a lease
//! cell: each tenant is a distinct funded holder, each lease keys its meter on a
//! per-tenant `(instance, period)`, and the charge's payer is the lease's own
//! lessee. The refusals are asserted on the surfaces that enforce it: the
//! `ConservingLedger`'s per-holder debit + per-`(lease,period)` exactly-once key
//! (a forged charge against a victim's key moves no value / conflicts), and the
//! bridge's funded-lease gate (an unfunded forged lease authorizes no work). The
//! cap/holder binding that makes a forged lease unauthorable lives in the dregg
//! lease cell (the `dregg-verify` rail); here it is modelled by these two gates.
//!
//! Run: `cargo test -p dreggnet-workload --release isolation -- --ignored --nocapture`

use dreggnet_bridge::{CapGrade, Lease, workflow_input_for_lease};
use dreggnet_control::{LeaseCharge, SettleError, Settlement};
use dreggnet_workload::{LoadProfile, RunReport, Scenario, Simulator, SloResult};

struct Isolation;

impl Scenario for Isolation {
    fn name(&self) -> &str {
        "multi_tenant_isolation"
    }

    fn profile(&self) -> LoadProfile {
        LoadProfile {
            tenants: 50,
            leases_per_tenant: 1,
            ..LoadProfile::default()
        }
        .with_env_overrides()
    }

    fn check(&self, _report: &RunReport) -> Vec<SloResult> {
        // The substantive isolation assertions run in the test body (they need the
        // live ledger). This table is the readable summary printed alongside.
        vec![
            SloResult::todo(
                "metering_separation",
                "asserted in body: per-tenant debit == own work",
            ),
            SloResult::todo(
                "dedup_key_per_tenant",
                "asserted in body: forged replay on a victim key moves nothing",
            ),
            SloResult::todo(
                "conflicting_forge_refused",
                "asserted in body: forged different-terms → Conflict",
            ),
            SloResult::todo(
                "unfunded_forge_refused",
                "asserted in body: the bridge gate refuses an unfunded forged lease",
            ),
        ]
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "workload-simulation suite — run via `make test-workload`"]
async fn tenants_are_isolated() {
    let scenario = Isolation;
    let sim = Simulator::new(scenario.profile()).await;
    let asset = sim.profile.asset.clone();
    let funding = sim.profile.funding;

    // The isolation substrate: each tenant funded distinctly + identified distinctly.
    for t in &sim.tenants {
        assert_eq!(
            sim.ledger.balance(&asset, &t.id),
            funding,
            "each tenant funded in its own balance"
        );
    }

    let report = sim.run(scenario.name()).await;
    report.print_table();
    // Conservation across the whole population must hold (§3).
    assert!(
        !report.has_failure(),
        "core invariants: {:?}",
        report.results
    );

    // ---- (a) metering separation: each tenant debited EXACTLY its own work ----
    // The per-tenant lease instance is `lease-{tenant}-0`; its settled total is the
    // tenant's own metered work. A tenant's balance must be funding minus exactly
    // that — no other tenant's activity moved it.
    let mut total_debited = 0i64;
    let mut any_work = false;
    for t in &sim.tenants {
        let instance = format!("lease-{}-0", t.id);
        let own = sim.ledger.settled_total(&instance);
        let debit = funding - sim.ledger.balance(&asset, &t.id);
        assert_eq!(
            debit, own,
            "tenant {} debited {debit} but its own settled work is {own} — cross-tenant leak",
            t.id
        );
        total_debited += debit;
        any_work |= own > 0;
    }
    assert!(any_work, "the run must actually settle work (non-vacuous)");

    // No phantom credit: Σ tenant debits == Σ backend credits, per asset.
    let (fleet, _cap) = sim.profile.backends;
    let total_credited: i64 = (0..fleet)
        .map(|i| sim.ledger.balance(&asset, &format!("backend-{i}")))
        .sum();
    assert_eq!(
        total_debited, total_credited,
        "Σ tenant debits ({total_debited}) == Σ backend credits ({total_credited})"
    );

    // ---- (b) dedup key is per-tenant: a forged charge against a victim's already
    // -settled (lease,period) key — by an adversary, to an attacker-controlled
    // beneficiary — moves NO value (the key is exactly-once, regardless of who
    // submits it). The victim is not billed again; the attacker is not credited. ----
    let victim = "tenant-7";
    let victim_instance = "lease-tenant-7-0";
    let adversary = "tenant-13";
    let attacker_sink = "backend-attacker";
    let v_before = sim.ledger.balance(&asset, victim);
    let a_before = sim.ledger.balance(&asset, adversary);
    let sink_before = sim.ledger.balance(&asset, attacker_sink);
    // Period 1 of the victim's lease was settled at amount 1 (per_period_units).
    let forged_replay = LeaseCharge::new(adversary, attacker_sink, &asset, victim_instance, 1, 1);
    let r = sim
        .ledger
        .settle(&forged_replay)
        .expect("a same-terms re-settle returns the recorded receipt");
    assert!(
        r.replayed,
        "forged re-settle on a victim key must REPLAY, not move value"
    );
    assert_eq!(
        sim.ledger.balance(&asset, victim),
        v_before,
        "victim untouched"
    );
    assert_eq!(
        sim.ledger.balance(&asset, adversary),
        a_before,
        "adversary not debited"
    );
    assert_eq!(
        sim.ledger.balance(&asset, attacker_sink),
        sink_before,
        "attacker not credited"
    );

    // ---- (c) a forged charge on the victim's key with DIFFERENT terms is REFUSED
    // (the key must identify a unique charge) — Conflict, victim untouched. ----
    let forged_conflict =
        LeaseCharge::new(adversary, attacker_sink, &asset, victim_instance, 1, 999);
    assert!(
        matches!(
            sim.ledger.settle(&forged_conflict),
            Err(SettleError::Conflict { .. })
        ),
        "a forged different-terms charge on a victim key must be refused as a Conflict"
    );
    assert_eq!(
        sim.ledger.balance(&asset, victim),
        v_before,
        "victim still untouched after conflict"
    );

    // ---- (d) an unfunded forged cross-tenant lease authorizes NO work — the bridge
    // gate refuses before any workflow starts (the real "no unpaid work" path). ----
    let mut forged_lease = Lease::funded(victim, CapGrade::Sandboxed, &asset, 100, 1);
    forged_lease.funded = false; // the forgery: an unfunded lease claiming the victim
    assert!(
        workflow_input_for_lease(&forged_lease, None).is_err(),
        "an unfunded forged lease must be refused by the bridge gate"
    );

    // Conservation still holds after every adversarial probe.
    assert_eq!(
        sim.ledger.total_supply(&asset),
        (funding * sim.profile.tenants as i64),
        "Σδ = 0 across the run + all adversarial probes"
    );

    println!(
        "  isolation: {} tenants, Σdebit={total_debited}=Σcredit, victim balance flat under 3 forged-attack vectors",
        sim.profile.tenants
    );
}
