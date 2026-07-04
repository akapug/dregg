//! Host witness for the REAL durable persist-PD spine + the app-hosting economy —
//! the deos OS as "the persist-PD IS the postgres, and hosting apps costs coin."
//!
//! This binary drives, on a box with no user-mode qemu-aarch64, the two deliveries
//! end to end against REAL durability (a redb store over a file-backed region — the
//! block-device `StorageBackend` shape; on-device the SAME store rides the seL4
//! block cap):
//!
//!   PART A — the durable spine: a verified turn commits durably (one redb txn, the
//!     fsync boundary) → a read returns it by ordinal/turn_hash/receipt_hash → the
//!     chain self-checks → a "persist-PD restart" (drop the store, reopen over the
//!     SAME file bytes) recovers the head + cursor + log, losing nothing. This is
//!     `commit_store.rs`'s gate, now over real ACID redb, not a BTreeMap.
//!
//!   PART B — the hosting economy: an app (a cell with durable state) pays a
//!     hosting fee to the host cell per period — a CONSERVING value Transfer
//!     (app → host) committed as a verified turn. A fee that lapses EVICTS the app
//!     (a verified, durable turn dropping the hosting), fail-closed. A paid app
//!     persists. Σ value is invariant across every charge.
//!
//! Run: `cargo run --release --bin host_durable_hosting`. The `#[test]`s in
//! `redb_store` + `hosting` are the gauntlet; this binary is the legible narration.

use std::path::Path;

use dregg_persist_hosttest::commit_store::{CommitRecord, GENESIS_ROOT};
use dregg_persist_hosttest::hosting::{ChargeOutcome, HostingEconomy};
use dregg_persist_hosttest::redb_store::{DurableCommitStore, RegionBackend};

fn main() {
    println!("== persist-PD: the durable 'postgres' of the deos OS + the app-hosting economy ==");
    println!("   (redb over a block-device region — the SAME store the persist PD rides over the");
    println!("    seL4 block cap; here file-backed so durability is REAL: a commit survives a restart)\n");

    let dir = std::env::temp_dir().join(format!("dregg-deos-spine-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();

    part_a_durable_spine(&dir.join("spine.redb"));
    println!();
    part_b_hosting_economy(&dir.join("hosting.redb"));

    let _ = std::fs::remove_dir_all(&dir);
    println!("\n== deos spine GREEN: durable verified turns over real redb, and hosting an app");
    println!("== costs coin (a conserving value turn); a lapsed fee evicts, fail-closed ( ◕‿◕ ) ==");
}

/// PART A — the durable spine over real redb, with a persist-PD restart.
fn part_a_durable_spine(path: &Path) {
    println!("-- PART A: the durable commit-log spine (executor commits → persist stores → read) --");

    let creator = [0xA1; 32];
    let head_after;
    let cursor_after;

    {
        let backend = RegionBackend::file(path).expect("open durable region");
        let store = DurableCommitStore::open(backend).expect("open store");

        // turn 0 — genesis. Stamp the (ordinal, prev_root) the durable head hands us.
        let ord0 = store.commit_cursor().unwrap();
        let prev0 = store.head_root().unwrap().unwrap_or(GENESIS_ROOT);
        let turn0 = produce(7000, ord0, prev0, creator);
        let a0 = store.commit_verified_turn(&turn0).expect("genesis commits durably");
        println!("  [1] committed turn 7000 at ordinal {a0} in ONE redb txn (the fsync boundary)");

        // read it back three ways — reads are free.
        let by_ord = store.lookup_by_ordinal(a0).unwrap().unwrap();
        let by_th = store.lookup_by_turn_hash(&turn0.turn_hash).unwrap().unwrap();
        let by_rh = store.lookup_by_receipt_hash(&turn0.receipt_hash).unwrap().unwrap();
        assert_eq!(by_ord, turn0);
        assert_eq!(by_th, turn0);
        assert_eq!(by_rh, turn0);
        println!("  [2] read returns it (by ordinal / turn_hash / receipt_hash all agree) — reads are free");

        // turn 1 — chains onto turn 0.
        let ord1 = store.commit_cursor().unwrap();
        let prev1 = store.head_root().unwrap().unwrap();
        let turn1 = produce(7001, ord1, prev1, creator);
        let a1 = store.commit_verified_turn(&turn1).expect("turn 1 chains and commits");
        println!("  [3] turn 7001 chains onto 7000 (prev_root == prior ledger_root); committed at ordinal {a1}");

        store.verify_chain_intact().expect("the durable chain self-checks");
        println!("  [4] light-client walk over the DURABLE rows -> chain INTACT");

        // a forged (non-chaining) turn is refused; the durable head does not move.
        let mut forged = produce(7002, store.commit_cursor().unwrap(), [0xFF; 32], creator);
        forged.prev_root = [0xFF; 32];
        let r = store.commit_verified_turn(&forged);
        println!("      admit(forged prev_root) -> {}", verdict(&r));
        assert!(r.is_err());
        assert_eq!(store.commit_cursor().unwrap(), 2, "the durable head did NOT move on a refusal");

        head_after = store.head_root().unwrap();
        cursor_after = store.commit_cursor().unwrap();
        // store dropped here — only the file bytes survive (the persist-PD crash).
    }

    // reopen over the SAME bytes — the durable store recovers, losing nothing.
    let backend = RegionBackend::file(path).expect("reopen durable region");
    let store = DurableCommitStore::open(backend).expect("reopen store");
    let resumed_head = store.head_root().unwrap();
    let resumed_cursor = store.commit_cursor().unwrap();
    assert_eq!(resumed_head, head_after);
    assert_eq!(resumed_cursor, cursor_after);
    store.verify_chain_intact().expect("the recovered durable chain is intact");
    println!(
        "  [5] persist-PD RESTART (drop + reopen the file): resumed at cursor {resumed_cursor}, head {} — no turn lost",
        resumed_head.map(|h| hexshort(&h)).unwrap_or_default()
    );
}

/// PART B — the app-hosting economy: pay-to-host as a verified value turn; eviction.
fn part_b_hosting_economy(path: &Path) {
    println!("-- PART B: the app-hosting economy (pay coin to be hosted = a verified value turn) --");

    let backend = RegionBackend::file(path).expect("open hosting region");
    let store = DurableCommitStore::open(backend).expect("open hosting store");
    let mut econ = HostingEconomy::open(store).expect("open economy");

    let host = [0x40; 32];
    let treasury = [0xC0; 32];
    let app_paid = {
        let mut a = [0xA0; 32];
        a[0] = 0x01;
        a
    };
    let app_lapsing = {
        let mut a = [0xA0; 32];
        a[0] = 0x02;
        a
    };

    // genesis mints the supply; the treasury funds two apps' leases.
    let supply = 1000u64;
    econ.genesis_fund(treasury, supply).expect("genesis");
    econ.register_app(app_paid, host, 10).expect("register paid app");
    econ.register_app(app_lapsing, host, 10).expect("register lapsing app");
    econ.top_up(app_paid, treasury, 100).expect("fund paid app (10 periods)");
    econ.top_up(app_lapsing, treasury, 20).expect("fund lapsing app (2 periods)");
    println!("  registered 2 apps on host {} @ fee 10/period; funded paid=100, lapsing=20", hexshort(&host));
    assert_eq!(econ.total_value(), supply, "genesis + top-ups conserve Σ value");

    // charge the PAID app three periods — each a conserving Transfer (app → host).
    println!("  charging the PAID app (it can pay):");
    for _ in 0..3 {
        let before = econ.total_value();
        match econ.charge_period(app_paid).unwrap() {
            ChargeOutcome::Paid { ordinal, period } => {
                println!(
                    "    period {period}: PAID 10 (app→host), durable turn @ ordinal {ordinal}; app bal {}, host bal {}; Σ {} (conserved)",
                    econ.balance(app_paid),
                    econ.balance(host),
                    econ.total_value()
                );
                assert_eq!(econ.total_value(), before, "the charge conserves Σ value");
            }
            ChargeOutcome::Evicted { .. } => unreachable!("the paid app can pay"),
        }
    }
    assert!(econ.is_hosted(app_paid), "the paid app's hosting persists");

    // charge the LAPSING app four periods — pays 2, then is EVICTED (fail-closed).
    println!("  charging the LAPSING app (funded for 2 periods, then dry):");
    let outcomes = econ.run_periods(app_lapsing, 4).unwrap();
    for o in &outcomes {
        match o {
            ChargeOutcome::Paid { period, .. } => {
                println!("    period {period}: PAID 10 (app→host)");
            }
            ChargeOutcome::Evicted { ordinal, period } => {
                println!(
                    "    period {period}: CANNOT PAY -> EVICTED (durable turn @ ordinal {ordinal}); hosting DROPPED, fail-closed"
                );
            }
        }
    }
    assert!(!econ.is_hosted(app_lapsing), "the lapsed app is evicted");
    assert!(matches!(outcomes.last(), Some(ChargeOutcome::Evicted { .. })));

    // the whole hosting history is a durable, self-checking chain; value conserved.
    econ.store().verify_chain_intact().expect("the hosting chain self-checks");
    assert_eq!(econ.total_value(), supply, "value conserved end-to-end (hosting charges, never forges)");
    println!(
        "  hosting history: {} durable verified turns; chain INTACT; Σ value {} == genesis supply (conserved)",
        econ.turn_count(),
        econ.total_value()
    );
}

/// Produce a verified-turn commit record stamped with the head-handed
/// `(ordinal, prev_root)` — the producer contract (`pg-dregg/src/drainer.rs`); the
/// `ledger_root` stands in for the executor's verified post-state root.
fn produce(turn_id: u64, ordinal: u64, prev_root: [u8; 32], creator: [u8; 32]) -> CommitRecord {
    let d = |tag: u8| digest(tag, turn_id, &prev_root);
    CommitRecord {
        ordinal,
        height: ordinal,
        block_id: d(0x04),
        turn_hash: d(0x01),
        creator,
        receipt_hash: d(0x02),
        prev_root,
        ledger_root: d(0x03),
        touched_cells: turn_id.to_le_bytes().to_vec(),
    }
}

fn digest(tag: u8, turn_id: u64, prev: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut acc = 0x9e37_79b9_7f4a_7c15u64 ^ ((tag as u64) << 56) ^ turn_id;
    for (i, b) in prev.iter().enumerate() {
        acc = acc
            .rotate_left(7)
            .wrapping_add(*b as u64)
            .wrapping_mul(0x0100_0000_01b3)
            ^ (i as u64);
    }
    for (i, slot) in out.iter_mut().enumerate() {
        acc = acc.rotate_left(11).wrapping_add(i as u64).wrapping_mul(0x0100_0000_01b3);
        *slot = (acc >> ((i % 8) * 8)) as u8;
    }
    out
}

fn verdict(r: &Result<u64, dregg_persist_hosttest::redb_store::DurableError>) -> String {
    match r {
        Ok(ord) => format!("ADMIT (ordinal {ord})"),
        Err(e) => format!("REFUSE ({e})"),
    }
}

fn hexshort(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(8);
    for byte in b.iter().take(4) {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}
