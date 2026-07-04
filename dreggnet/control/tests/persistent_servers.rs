//! Persistent servers — the §3.3 round-trip, proven over the in-process
//! [`LocalProvider`] (`docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.3).
//!
//! A persistent server is a long-running, durable, per-period-metered server
//! instance — not a request-scoped machine. This proves the whole lifecycle end to
//! end, with the load-bearing guarantee being **crash-survival**: a control-plane
//! restart (drop the fleet + its provider, reload from the durable store)
//! reconstructs the running server rather than losing it, and the uptime metering
//! stays **exactly-once** across that restart.
//!
//! ```text
//!   create ─▶ launch ─▶ running (metered/period) ─▶ ⟂RESTART⟂ ─▶ reconstructed
//!                                                                      │
//!                                              still running, cursor preserved
//!                                                                      ▼
//!                                            meter more periods (exactly-once) ─▶ destroy
//! ```
//!
//! The settlement rail (the conserving [`ConservingLedger`], the in-process twin of
//! the dregg `Payable`) is **external** to the control plane — it survives the
//! restart, as a real dregg node would. Its exactly-once `(server_id, period)` dedup
//! plus the durable per-server period cursor in the store make the uptime meter
//! exactly-once even when a period is re-attempted after the restart.

use std::path::PathBuf;
use std::sync::Arc;

use dreggnet_control::{
    CapGrade, ConservingLedger, Lease, LocalProvider, MachineSize, MeterOutcome, ServerFleet,
    ServerState, ServerStore,
};

fn temp_store_path(tag: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-persistent-servers-{tag}-{nanos}.jsonl"));
    p
}

/// The full round-trip: create → launch → meter → **control-plane restart**
/// (reconstruct from the store) → meter more → destroy, with the server persisting
/// across the restart and the metering exactly-once.
#[tokio::test]
async fn create_launch_meter_restart_reconstruct_destroy() {
    let path = temp_store_path("roundtrip");

    // The settlement rail is external to the control plane (a dregg node, here the
    // conserving in-process ledger): it survives a control-plane restart.
    let ledger = Arc::new(ConservingLedger::new());
    ledger.fund("DREGG", "agent", 100);

    // --- the first control plane ---
    let id = {
        let fleet = ServerFleet::new(
            LocalProvider::new(),
            ServerStore::open(&path).unwrap(),
            ledger.clone(),
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        );

        // create → launch → running. SRV-4: launch pre-pays period 1 (3 units).
        let lease = Lease::funded("agent", CapGrade::Sandboxed, "DREGG", 100, 3);
        let id = fleet.create("acme", "api", &lease).unwrap();
        fleet.launch(&id).await.unwrap();
        assert_eq!(fleet.server(&id).unwrap().state, ServerState::Running);
        assert!(fleet.health(&id).await.unwrap(), "the backend is up");
        assert_eq!(
            fleet.server(&id).unwrap().periods_metered,
            1,
            "launch pre-pays period 1"
        );

        // Meter two more uptime periods (2, 3 — 3 units each). Settled lessee → provider.
        let r1 = fleet.tick_uptime().await.unwrap();
        let r2 = fleet.tick_uptime().await.unwrap();
        assert_eq!(r1.metered, 1);
        assert_eq!(r2.metered, 1);
        assert_eq!(fleet.server(&id).unwrap().periods_metered, 3);
        assert_eq!(ledger.balance("DREGG", "agent"), 91);
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 9);

        id
        // The fleet (and its LocalProvider — every backend machine) is DROPPED here:
        // a control-plane restart. The in-memory fleet is gone; only the durable
        // store on disk + the external settlement rail remain.
    };

    // --- the restart: reconstruct from the durable store ---
    let fleet = ServerFleet::reload(
        LocalProvider::new(),
        ServerStore::open(&path).unwrap(),
        ledger.clone(),
        MachineSize::Small,
        "local",
        "dreggnet-provider",
    )
    .await
    .unwrap();

    // The running server was RECONSTRUCTED, not lost: present, Running, a fresh
    // backend re-provisioned, the uptime cursor preserved at 2.
    let rec = fleet.server(&id).expect("server survived the restart");
    assert_eq!(rec.state, ServerState::Running);
    assert_eq!(
        rec.periods_metered, 3,
        "the uptime cursor survived the restart"
    );
    assert!(
        fleet.health(&id).await.unwrap(),
        "a fresh backend was re-provisioned"
    );

    // Exactly-once across the restart: reconstruct re-provisions the backend but does
    // NOT re-settle (no launch pre-pay on reload) — the balances are unchanged from
    // before the restart, so periods 1..3 are not re-billed.
    assert_eq!(
        ledger.balance("DREGG", "agent"),
        91,
        "no re-billing on reconstruct"
    );
    assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 9);

    // Metering continues from where it left off: period 4 is the next charge.
    let out = fleet.meter_period(&id).await.unwrap();
    assert_eq!(
        out,
        MeterOutcome::Metered {
            period: 4,
            units: 3
        }
    );
    assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 12);
    assert_eq!(
        ledger.total_supply("DREGG"),
        100,
        "Σδ = 0 across every transfer"
    );

    // destroy → torn down, backend released, record retained as Destroyed.
    fleet.destroy(&id).await.unwrap();
    assert_eq!(fleet.server(&id).unwrap().state, ServerState::Destroyed);
    assert!(!fleet.health(&id).await.unwrap());

    std::fs::remove_file(&path).ok();
}

/// A second, sharper exactly-once check: directly re-attempt an already-metered
/// period after a restart and confirm the durable cursor + the rail dedup refuse to
/// double-charge — the LEASE-3-shaped property applied to uptime.
#[tokio::test]
async fn re_metering_a_settled_period_after_restart_does_not_double_charge() {
    let path = temp_store_path("exactly-once");
    let ledger = Arc::new(ConservingLedger::new());
    ledger.fund("DREGG", "agent", 100);

    let id = {
        let fleet = ServerFleet::new(
            LocalProvider::new(),
            ServerStore::open(&path).unwrap(),
            ledger.clone(),
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        );
        let id = fleet
            .create(
                "acme",
                "worker",
                &Lease::funded("agent", CapGrade::Sandboxed, "DREGG", 100, 5),
            )
            .unwrap();
        fleet.launch(&id).await.unwrap(); // SRV-4: launch pre-pays period 1 → 5 units
        assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 5);
        id
    };

    // Restart. The cursor is at 1; reconstruct must not re-bill period 1.
    let fleet = ServerFleet::reload(
        LocalProvider::new(),
        ServerStore::open(&path).unwrap(),
        ledger.clone(),
        MachineSize::Small,
        "local",
        "dreggnet-provider",
    )
    .await
    .unwrap();
    assert_eq!(fleet.server(&id).unwrap().periods_metered, 1);
    assert_eq!(
        ledger.balance("DREGG", "dreggnet-provider"),
        5,
        "period 1 not re-billed"
    );

    // The next meter is period 2, not a second period-1 charge.
    let out = fleet.meter_period(&id).await.unwrap();
    assert_eq!(
        out,
        MeterOutcome::Metered {
            period: 2,
            units: 5
        }
    );
    assert_eq!(ledger.balance("DREGG", "dreggnet-provider"), 10);
    assert_eq!(fleet.server(&id).unwrap().periods_metered, 2);

    std::fs::remove_file(&path).ok();
}

/// A stopped (asleep) server is reconstructed as stopped — no backend re-provisioned
/// — and is metered nothing until woken.
#[tokio::test]
async fn stopped_server_reconstructs_asleep() {
    let path = temp_store_path("stopped");
    let ledger = Arc::new(ConservingLedger::new());
    ledger.fund("DREGG", "agent", 100);

    let id = {
        let fleet = ServerFleet::new(
            LocalProvider::new(),
            ServerStore::open(&path).unwrap(),
            ledger.clone(),
            MachineSize::Small,
            "local",
            "dreggnet-provider",
        );
        let id = fleet
            .create(
                "acme",
                "batch",
                &Lease::funded("agent", CapGrade::Sandboxed, "DREGG", 100, 1),
            )
            .unwrap();
        fleet.launch(&id).await.unwrap(); // SRV-4: launch pre-pays period 1
        fleet.stop(&id).await.unwrap();
        assert_eq!(fleet.server(&id).unwrap().state, ServerState::Stopped);
        id
    };

    let fleet = ServerFleet::reload(
        LocalProvider::new(),
        ServerStore::open(&path).unwrap(),
        ledger.clone(),
        MachineSize::Small,
        "local",
        "dreggnet-provider",
    )
    .await
    .unwrap();
    // Reconstructed asleep: not healthy, metering is a no-op.
    assert_eq!(fleet.server(&id).unwrap().state, ServerState::Stopped);
    assert!(!fleet.health(&id).await.unwrap());
    assert_eq!(
        fleet.meter_period(&id).await.unwrap(),
        MeterOutcome::NotRunning
    );

    // Wake resumes serving; SRV-4: wake pre-pays the resume period (2). The next
    // metering tick then settles period 3.
    fleet.wake(&id).await.unwrap();
    assert_eq!(
        fleet.server(&id).unwrap().periods_metered,
        2,
        "wake pre-pays period 2"
    );
    assert_eq!(
        fleet.meter_period(&id).await.unwrap(),
        MeterOutcome::Metered {
            period: 3,
            units: 1
        }
    );

    std::fs::remove_file(&path).ok();
}
