//! The shared compute FUND end-to-end: the proven `ShareVault` house-capacity
//! driven as a pooled-deposit fund through [`ComputeFundVault`].
//!
//! Every guarantee here is the share-vault capacity's, imaged by the Lean rung
//! `metatheory/Dregg2/Deos/Vault.lean` (`deposit_no_dilution`,
//! `zero_mint_rejected`, `forged_shares_rejected`). These tests drive the REAL
//! `dregg_cell::vault` API through the app's headline — proportional shares, no
//! dilution, conservation, and the ERC-4626 first-depositor inflation attack
//! refused.

use dregg_cell::Cell;
use dregg_cell::vault::{
    KEY_TOTAL_ASSETS, KEY_TOTAL_SHARES, SHARE_VAULT_COLL, ShareVaultError, deposit_shares,
    encode_i64,
};
use starbridge_compute_exchange::{ComputeFundVault, FUND_BUDGET_TOKEN, FundError};

/// A sponsor wallet holding the fund's pooled budget asset.
fn sponsor(pk: u8, balance: i64) -> Cell {
    Cell::with_balance([pk; 32], FUND_BUDGET_TOKEN, balance)
}

/// **Bootstrap + proportional shares.** Two sponsors deposit into ONE fund; the
/// first bootstraps shares 1:1 and the second is minted by the committed
/// share-price relation `d · S / T`. Pooled value is conserved into custody.
#[test]
fn two_sponsors_get_proportional_shares() {
    let mut fund = ComputeFundVault::open();
    assert!(fund.is_open());

    let mut a = sponsor(1, 1_000);
    let mut b = sponsor(2, 1_000);
    let a_id = a.id();
    let b_id = b.id();

    // Sponsor A bootstraps: 100 assets -> 100 shares (1:1 on the empty vault).
    let minted_a = fund.deposit(&mut a, 100).expect("bootstrap deposit");
    assert_eq!(minted_a, 100, "bootstrap mints 1:1");
    assert_eq!(fund.shares_of(a_id), 100);
    assert_eq!(fund.total_assets(), 100);
    assert_eq!(fund.total_shares(), 100);
    assert_eq!(fund.pooled_value(), 100, "value moved into custody");
    assert_eq!(a.state.balance(), 900, "value left A's wallet");

    // Sponsor B deposits 50 into the established fund (T=100, S=100): the
    // share-price relation mints 50·100/100 = 50 shares.
    let minted_b = fund.deposit(&mut b, 50).expect("second deposit");
    assert_eq!(minted_b, 50, "50·S/T = 50·100/100 = 50 shares");
    assert_eq!(fund.shares_of(b_id), 50);
    assert_eq!(fund.total_assets(), 150);
    assert_eq!(fund.total_shares(), 150);
    assert_eq!(fund.pooled_value(), 150);

    // The pool is split proportionally: A owns 100/150, B owns 50/150.
    assert_eq!(
        fund.shares_of(a_id) + fund.shares_of(b_id),
        fund.total_shares()
    );
}

/// **No dilution + correct withdrawal value.** A withdrawal redeems the
/// redeemer's fair slice (`s · T / S`) and no more — the remaining holders are
/// not diluted, value returns from custody to the redeemer, and per-asset value
/// is conserved across the whole run.
#[test]
fn withdraw_redeems_fair_slice_no_dilution() {
    let mut fund = ComputeFundVault::open();
    let mut a = sponsor(1, 1_000);
    let mut b = sponsor(2, 1_000);
    let a_id = a.id();
    let b_id = b.id();

    fund.deposit(&mut a, 200)
        .expect("A deposits 200 -> 200 shares");
    fund.deposit(&mut b, 100)
        .expect("B deposits 100 -> 100 shares");
    // T = 300, S = 300, price-per-share = 1.
    assert_eq!(fund.total_assets(), 300);
    assert_eq!(fund.total_shares(), 300);

    // B redeems all 100 of its shares: 100·300/300 = 100 assets — exactly B's
    // contribution, no more (no dilution of A).
    let redeemed = fund.withdraw(&mut b, 100).expect("B withdraws 100 shares");
    assert_eq!(redeemed, 100, "fair slice s·T/S = 100·300/300");
    assert_eq!(fund.shares_of(b_id), 0, "B's slice fully redeemed");
    assert_eq!(
        b.state.balance(),
        1_000,
        "B made whole — got its value back"
    );

    // A is untouched: still 200 shares of a now-200-asset pool, price-per-share 1.
    assert_eq!(fund.shares_of(a_id), 200);
    assert_eq!(fund.total_assets(), 200);
    assert_eq!(fund.total_shares(), 200);

    // Conservation: A's wallet + B's wallet + pooled custody == the starting total.
    assert_eq!(
        a.state.balance() + b.state.balance() + fund.pooled_value(),
        2_000
    );
}

/// **A sponsor cannot redeem more shares than it holds.** The fund tracks each
/// sponsor's slice; an over-redemption is refused before any value moves.
#[test]
fn cannot_redeem_more_shares_than_held() {
    let mut fund = ComputeFundVault::open();
    let mut a = sponsor(1, 1_000);
    fund.deposit(&mut a, 100)
        .expect("A deposits 100 -> 100 shares");

    let err = fund
        .withdraw(&mut a, 150)
        .expect_err("redeeming 150 of 100 held shares must be refused");
    assert_eq!(
        err,
        FundError::InsufficientShares {
            have: 100,
            want: 150
        }
    );
    // Nothing moved.
    assert_eq!(fund.shares_of(a.id()), 100);
    assert_eq!(fund.total_shares(), 100);
    assert_eq!(a.state.balance(), 900);
}

/// **A forged claimed-share count is refused** — but the fund only ever submits
/// the share-price relation, so the honest path always agrees. We exercise the
/// capacity tooth directly: a deposit claiming a count ≠ `d·S/T` is rejected.
#[test]
fn forged_share_count_is_refused_by_the_capacity() {
    let mut fund = ComputeFundVault::open();
    let mut a = sponsor(1, 1_000);
    fund.deposit(&mut a, 100).expect("bootstrap -> 100 shares");

    // Drive the raw capacity against the fund's host cell: claim 999 shares for a
    // 50-asset deposit when the relation yields 50·100/100 = 50.
    let err =
        deposit_shares(&mut fund.vault, 50, 999).expect_err("a forged share count must be refused");
    assert!(
        matches!(
            err,
            ShareVaultError::ForgedShareCount {
                claimed: 999,
                actual: 50
            }
        ),
        "expected ForgedShareCount, got {err:?}"
    );
}

/// **THE ERC-4626 INFLATION ATTACK — no surface.** The classic first-depositor
/// exploit needs to skew the share price by DONATING value without minting
/// shares. The fund's only value-in path is [`ComputeFundVault::deposit`], which
/// always mints the fair share-price count and advances the committed
/// `total_assets` accordingly — there is no donate path. So an attacker
/// bootstrapping 1 share cannot rob a later victim: the victim's deposit mints
/// fair shares against the committed (un-skewable) counters.
#[test]
fn inflation_attack_has_no_donation_surface() {
    let mut fund = ComputeFundVault::open();
    let mut attacker = sponsor(9, 1_000_000);
    let mut victim = sponsor(2, 1_000);
    let victim_id = victim.id();

    // Attacker bootstraps the fund with a single asset -> 1 share (T=1, S=1).
    assert_eq!(fund.deposit(&mut attacker, 1).expect("bootstrap"), 1);
    assert_eq!(fund.total_assets(), 1);
    assert_eq!(fund.total_shares(), 1);

    // In ERC-4626 the attacker would now DONATE a huge raw balance into the vault
    // to skew balanceOf-derived price; here total_assets is an internal committed
    // counter and there is no API to move it without minting. The victim's 100
    // deposit mints the FAIR 100·1/1 = 100 shares — the attack failed.
    let minted = fund.deposit(&mut victim, 100).expect("victim deposit");
    assert_eq!(minted, 100, "donation-immunity: committed ratio unmoved");
    assert_eq!(fund.shares_of(victim_id), 100);

    // The victim can redeem its full contribution back (it was not robbed).
    let redeemed = fund.withdraw(&mut victim, 100).expect("victim withdraws");
    assert_eq!(redeemed, 100, "victim made whole");
}

/// **THE ZERO-MINT TOOTH bites.** Even if a ratio WERE skewed (the state
/// ERC-4626's `balanceOf` would read), a positive deposit that rounds to ZERO
/// shares is REFUSED by the capacity — a victim is never robbed for nothing. We
/// construct the skewed committed counters directly on a host cell and show
/// `deposit_shares` rejects. Mirrors `Vault.zero_mint_rejected` /
/// `#guard !decide (DepositOk 10001 1 100 0)`.
#[test]
fn zero_mint_deposit_is_refused() {
    // A host cell with a skewed committed ratio: T = 10_001, S = 1. A 100-asset
    // deposit yields 100·1/10001 = 0 shares.
    let mut host = Cell::with_balance([7u8; 32], [7u8; 32], 0);
    host.state
        .set_heap(SHARE_VAULT_COLL, KEY_TOTAL_ASSETS, encode_i64(10_001));
    host.state
        .set_heap(SHARE_VAULT_COLL, KEY_TOTAL_SHARES, encode_i64(1));

    let err = deposit_shares(&mut host, 100, 0)
        .expect_err("a zero-mint deposit must be refused — the inflation tooth");
    assert!(
        matches!(err, ShareVaultError::ZeroSharesMinted),
        "expected ZeroSharesMinted, got {err:?}"
    );
}
