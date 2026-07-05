//! Durable + crash-resume + conservation proof for the **pg-dregg-backed verified
//! conserving store** over a **real Postgres**.
//!
//! This is the verified-store twin of `durable_resume_pg.rs`'s meter-outbox proof: it
//! replaces the in-process [`ConservingLedger`] with `VerifiedConservingStore` — the
//! settlement ledger persisted as a `pg-dregg` verified hash chain on a real Postgres —
//! and proves the un-gated half (`docs/STAND-INS-CENSUS.md` #7/#16):
//!
//! - **conservation** — every settle moves value payer→beneficiary, Σδ = 0 (the asset's
//!   total supply is unchanged across all settlements);
//! - **exactly-once** — a re-settle of the same `(lease, period)` returns the recorded
//!   receipt and moves nothing, enforced by the Postgres `UNIQUE (lease_id, period)`;
//! - **crash-resume** — a fresh store opened over the SAME Postgres (a settler restart /
//!   a second instance) sees the prior settlements and refuses to double-charge — the
//!   exactly-once key is durable, not in-memory;
//! - **re-validate, don't trust** — the persisted chain re-validates through the real
//!   `pg-dregg` anti-substitution tooth, and a row tampered with by raw SQL is REFUSED.
//!
//! What stays **S3-gated** (the swarm's `pg-dregg` S3 circuit flip — NOT proven here): the
//! per-turn root being the kernel's real Poseidon2 commitment a light client witnesses, and
//! the settlement being a proof-attested on-chain dregg `Payable`. See
//! `dreggnet_durable::verified::S3_GATED_SEAM`.
//!
//! Gating: `#[ignore]` + a live Postgres via `DATABASE_URL` (opt-in; the offline
//! `VerifiedChain` core tests in `src/verified.rs` are the always-green proof):
//!
//! ```text
//!   DATABASE_URL=postgres://localhost/dreggnet \
//!     cargo test -p dreggnet-durable --features pg-dregg --test verified_store_pg -- --ignored --nocapture
//! ```
#![cfg(feature = "pg-dregg")]

use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use dreggnet_durable::settle::LeaseCharge;
use dreggnet_durable::verified::VerifiedConservingStore;
use sqlx::PgPool;

fn database_url() -> Option<String> {
    match std::env::var("DATABASE_URL") {
        Ok(u) => Some(u),
        Err(_) => {
            eprintln!("DATABASE_URL unset; skipping the pg-dregg verified-store test");
            None
        }
    }
}

/// A unique asset + lease tag per run, so repeated runs against a persistent Postgres — and
/// the parallel test threads sharing it — never collide on an already-settled key or an
/// already-funded reserve. Nanos alone collide when threads start in the same tick, so a
/// process-wide atomic counter disambiguates concurrent callers.
fn nonce() -> u128 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let seq = COUNTER.fetch_add(1, Ordering::Relaxed) as u128;
    nanos * 1_000 + seq
}

async fn pool() -> PgPool {
    let url = database_url().expect("DATABASE_URL set (guarded by caller)");
    PgPool::connect(&url)
        .await
        .expect("connect to the test postgres")
}

#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL; opt-in (the offline VerifiedChain tests are the always-green proof)"]
async fn settle_over_the_real_store_conserves_and_is_exactly_once() {
    if database_url().is_none() {
        return;
    }
    let n = nonce();
    let asset = format!("USD-{n}");
    let lessee = format!("lessee-{n}");
    let provider = format!("provider-{n}");

    let store = VerifiedConservingStore::open(pool().await)
        .await
        .expect("open the verified store (creates its tables)");

    // Fund the lessee's reserve, then settle two periods.
    store.fund(&asset, &lessee, 100).await.unwrap();
    assert_eq!(store.total_supply(&asset).await.unwrap(), 100);

    let c1 = LeaseCharge::new(&lessee, &provider, &asset, format!("lease-A-{n}"), 1, 7);
    let r1 = store.settle(&c1).await.expect("settle period 1");
    assert!(!r1.replayed);
    assert_eq!(r1.payer_balance, 93);
    assert_eq!(r1.beneficiary_balance, 7);

    let c2 = LeaseCharge::new(&lessee, &provider, &asset, format!("lease-A-{n}"), 2, 5);
    let r2 = store.settle(&c2).await.expect("settle period 2");
    assert_eq!(r2.payer_balance, 88);
    assert_eq!(r2.beneficiary_balance, 12);

    // Conservation: value moved, none created or destroyed.
    assert_eq!(store.balance(&asset, &lessee).await.unwrap(), 88);
    assert_eq!(store.balance(&asset, &provider).await.unwrap(), 12);
    assert_eq!(store.total_supply(&asset).await.unwrap(), 100, "Σδ = 0");

    // Exactly-once: re-settling period 1 replays — no second move.
    let again = store.settle(&c1).await.expect("re-settle period 1");
    assert!(again.replayed, "a re-settle replays, never re-moves");
    assert_eq!(
        store.balance(&asset, &provider).await.unwrap(),
        12,
        "no double-charge"
    );

    // The persisted chain re-validates through the real pg-dregg anti-substitution tooth.
    let revalidated = store
        .revalidate(&format!("lease-A-{n}"))
        .await
        .expect("query the chain");
    assert!(
        revalidated.is_ok(),
        "the genuine persisted chain re-validates: {revalidated:?}"
    );
}

#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn crash_resume_exactly_once_across_a_restart() {
    if database_url().is_none() {
        return;
    }
    let n = nonce();
    let asset = format!("USD-{n}");
    let lessee = format!("lessee-{n}");
    let provider = format!("provider-{n}");
    let lease = format!("lease-R-{n}");

    // ===== Settler instance #1: fund + settle period 1, then "crash" (drop the store). =====
    {
        let store = VerifiedConservingStore::open(pool().await).await.unwrap();
        store.fund(&asset, &lessee, 50).await.unwrap();
        let c1 = LeaseCharge::new(&lessee, &provider, &asset, &lease, 1, 9);
        let r = store.settle(&c1).await.expect("settle period 1");
        assert!(!r.replayed);
        assert_eq!(store.balance(&asset, &provider).await.unwrap(), 9);
        // 💥 drop: the store's pool closes; Postgres keeps the chain + balances.
    }

    // ===== Settler instance #2: a fresh store over the SAME Postgres (the restart). =====
    {
        let store = VerifiedConservingStore::open(pool().await).await.unwrap();
        // The prior settlement survived: balances are loaded from Postgres, not zeroed.
        assert_eq!(
            store.balance(&asset, &provider).await.unwrap(),
            9,
            "prior settle survived restart"
        );
        assert_eq!(store.balance(&asset, &lessee).await.unwrap(), 41);

        // Re-handing period 1 to the restarted settler REPLAYS — never a second on-chain move.
        let c1 = LeaseCharge::new(&lessee, &provider, &asset, &lease, 1, 9);
        let replay = store
            .settle(&c1)
            .await
            .expect("re-settle period 1 after restart");
        assert!(
            replay.replayed,
            "exactly-once across restart: no double-charge"
        );
        assert_eq!(
            store.balance(&asset, &provider).await.unwrap(),
            9,
            "still 9 — not doubled"
        );

        // A genuinely new period still settles, chaining onto the recovered head.
        let c2 = LeaseCharge::new(&lessee, &provider, &asset, &lease, 2, 6);
        let r2 = store
            .settle(&c2)
            .await
            .expect("settle period 2 post-restart");
        assert!(!r2.replayed);
        assert_eq!(store.balance(&asset, &provider).await.unwrap(), 15);
        assert_eq!(
            store.total_supply(&asset).await.unwrap(),
            50,
            "Σδ = 0 across the restart"
        );
    }
}

#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn concurrent_settles_stay_dense_and_conserve() {
    if database_url().is_none() {
        return;
    }
    let n = nonce();
    let asset = format!("USD-{n}");
    let lessee = format!("lessee-{n}");
    let provider = format!("provider-{n}");
    let lease = format!("lease-C-{n}");

    let store = Arc::new(VerifiedConservingStore::open(pool().await).await.unwrap());
    store.fund(&asset, &lessee, 1_000).await.unwrap();

    // 20 distinct periods settled concurrently — the advisory lock keeps chain ordinals
    // dense and the conserving moves serialized, so all 20 land and Σδ = 0 holds.
    let mut handles = Vec::new();
    for period in 1..=20i64 {
        let store = store.clone();
        let (asset, lessee, provider, lease) = (
            asset.clone(),
            lessee.clone(),
            provider.clone(),
            lease.clone(),
        );
        handles.push(tokio::spawn(async move {
            let c = LeaseCharge::new(&lessee, &provider, &asset, &lease, period, 3);
            store.settle(&c).await
        }));
    }
    for h in handles {
        h.await.unwrap().expect("each concurrent settle succeeds");
    }

    assert_eq!(
        store.settled_total(&lease).await.unwrap(),
        60,
        "20 periods × 3"
    );
    assert_eq!(store.balance(&asset, &provider).await.unwrap(), 60);
    assert_eq!(store.balance(&asset, &lessee).await.unwrap(), 940);
    assert_eq!(
        store.total_supply(&asset).await.unwrap(),
        1_000,
        "Σδ = 0 under concurrency"
    );

    // The concurrently-built chain re-validates through the anti-substitution tooth.
    let revalidated = store.revalidate(&lease).await.expect("query");
    assert!(
        revalidated.is_ok(),
        "concurrent chain re-validates: {revalidated:?}"
    );
}

#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn revalidate_refuses_a_row_tampered_by_raw_sql() {
    if database_url().is_none() {
        return;
    }
    let n = nonce();
    let asset = format!("USD-{n}");
    let lessee = format!("lessee-{n}");
    let provider = format!("provider-{n}");
    let lease = format!("lease-T-{n}");

    let store = VerifiedConservingStore::open(pool().await).await.unwrap();
    store.fund(&asset, &lessee, 100).await.unwrap();
    for period in 1..=3i64 {
        let c = LeaseCharge::new(&lessee, &provider, &asset, &lease, period, 4);
        store.settle(&c).await.expect("settle");
    }
    assert!(
        store.revalidate(&lease).await.unwrap().is_ok(),
        "genuine chain re-validates"
    );

    // Tamper directly in Postgres: inflate a settled row's beneficiary balance (steal value),
    // bypassing the verified-write path entirely.
    sqlx::query(&format!(
        "UPDATE {} SET beneficiary_balance = beneficiary_balance + 1000 WHERE lease_id = $1 AND period = 1",
        VerifiedConservingStore::CHAIN_TABLE
    ))
    .bind(&lease)
    .execute(store.pool())
    .await
    .expect("raw tamper update");

    // The store re-validates its OWN Postgres state and REFUSES the tampered chain — the
    // pg-dregg anti-substitution tooth catches a row that did not arrive through a verified
    // turn (the content no longer binds its committed root).
    let verdict = store
        .revalidate(&lease)
        .await
        .expect("query the tampered chain");
    assert!(
        verdict.is_err(),
        "a raw-SQL-tampered chain row is refused on re-validation"
    );
}

/// #4 / S9-1: a DB-write attacker `UPDATE`s the unchained `dreggnet_settle_balances`
/// table to grant themselves spendable value. The chain + the independent funding
/// authority do not imply that number, so the store-wide balance cross-check REFUSES.
#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn revalidate_balances_refuses_a_tampered_balance_table() {
    if database_url().is_none() {
        return;
    }
    let n = nonce();
    let asset = format!("USD-{n}");
    let lessee = format!("lessee-{n}");
    let provider = format!("provider-{n}");
    let lease = format!("lease-B-{n}");

    let store = VerifiedConservingStore::open(pool().await).await.unwrap();
    store.fund(&asset, &lessee, 100).await.unwrap();
    for period in 1..=2i64 {
        let c = LeaseCharge::new(&lessee, &provider, &asset, &lease, period, 4);
        store.settle(&c).await.expect("settle");
    }
    // Honest store: balances reconcile against funding + chain.
    assert!(
        store.revalidate_balances().await.unwrap().is_ok(),
        "a genuine balance table reconciles"
    );

    // The S9-1 attack: inflate a holder's spendable balance directly, bypassing both
    // the funding authority and the verified chain.
    sqlx::query(&format!(
        "UPDATE {} SET balance = balance + 1000000 WHERE asset = $1 AND holder = $2",
        VerifiedConservingStore::BALANCE_TABLE
    ))
    .bind(&asset)
    .bind(&lessee)
    .execute(store.pool())
    .await
    .expect("raw balance tamper");

    // The cross-check recomputes balances from the re-validated chain + funding and
    // refuses the mismatch — the forged balance can no longer authorize a spend.
    let verdict = store.revalidate_balances().await.expect("query");
    assert!(
        verdict.is_err(),
        "a tampered (unfunded) balance table is refused"
    );
}

/// #5 / S9-2: a DB-write attacker `DELETE`s the chain tail. The dense prefix still
/// chains, but the INDEPENDENT per-lease head authority knows the real turn count, so
/// the truncation guard refuses the short read (rather than deriving its own
/// always-matching count from the truncated read).
#[tokio::test]
#[ignore = "requires a live Postgres via DATABASE_URL"]
async fn revalidate_refuses_a_truncated_tail_via_the_independent_count() {
    if database_url().is_none() {
        return;
    }
    let n = nonce();
    let asset = format!("USD-{n}");
    let lessee = format!("lessee-{n}");
    let provider = format!("provider-{n}");
    let lease = format!("lease-D-{n}");

    let store = VerifiedConservingStore::open(pool().await).await.unwrap();
    store.fund(&asset, &lessee, 100).await.unwrap();
    for period in 1..=3i64 {
        let c = LeaseCharge::new(&lessee, &provider, &asset, &lease, period, 4);
        store.settle(&c).await.expect("settle");
    }
    assert!(
        store.revalidate(&lease).await.unwrap().is_ok(),
        "full chain re-validates"
    );

    // Delete the tail turn (ordinal 2). The head authority still records next_ordinal=3.
    sqlx::query(&format!(
        "DELETE FROM {} WHERE lease_id = $1 AND ordinal = 2",
        VerifiedConservingStore::CHAIN_TABLE
    ))
    .bind(&lease)
    .execute(store.pool())
    .await
    .expect("raw tail delete");

    // The read returns a dense, genesis-anchored prefix [0,1] that chains clean — but
    // the independent expected-count (3) refuses it.
    let verdict = store
        .revalidate(&lease)
        .await
        .expect("query the truncated chain");
    assert!(
        verdict.is_err(),
        "a deleted-tail chain is refused via the independent count"
    );
}
