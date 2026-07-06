//! The teeth: paper trades land attested + on-ledger at attested prices, the third-party
//! audit verifies the track record + the mandate held + the P&L, and every guard BITES —
//! an over-mandate trade, an over-budget trade, an unattested-price fill, and a forged /
//! altered / dropped / reordered track record are each refused. Recorded (modeled) brain.
//!
//! ⚑ PAPER-ONLY — every fill here is simulated against an attested price; no real order,
//!   no custody, no real money.

use auditable_fund::{
    AnthropicConfig, AttestedPrice, AuditError, Decision, Fund, FundError, Mandate,
    MandateViolation, ModeledOracle, RecordedBrain, audit_fund,
};

/// A modeled oracle seeded deterministically, quoting one asset at a fixed price.
fn oracle(asset: &str, price: i64) -> ModeledOracle {
    let mut o = ModeledOracle::from_seed(&[0x11u8; 32]);
    o.set_price(asset, price);
    o
}

/// A one-asset mandate: allow `BTC`, cap position at 10 units, budget 1_000_000, up to 16 turns.
fn mandate() -> Mandate {
    Mandate {
        allowed_assets: vec!["BTC".to_string()],
        max_position: 10,
        budget: 1_000_000,
        max_turns: 16,
    }
}

fn open_fund(m: Mandate, oracle: &ModeledOracle) -> Fund {
    Fund::open(
        "fund.audit.dregg",
        m,
        &[0x2au8; 32],
        oracle.config().clone(),
    )
    .expect("open the fund")
}

/// THE HAPPY PATH — a few paper trades land as attested on-ledger turns at attested prices,
/// and the third-party audit verifies the whole track record + reports the P&L.
#[test]
fn paper_trades_land_attested_and_audit_verifies() {
    let ora = oracle("BTC", 100_000); // 100_000 cents / unit
    let mut fund = open_fund(mandate(), &ora);

    // Recorded brain: buy 3, buy 2, hold, sell 4.
    let mut brain = RecordedBrain::new(vec![
        Decision::buy("BTC", 3, "accumulate"),
        Decision::buy("BTC", 2, "add"),
        Decision::hold("wait"),
        Decision::sell("BTC", 4, "take profit"),
    ]);

    for _ in 0..4 {
        fund.step(&ora, &mut brain).expect("the step lands");
    }

    // 5 buy - 4 sell = 1 unit held; cash = 1_000_000 - 5*100_000 + 4*100_000 = 900_000.
    assert_eq!(fund.position("BTC"), 1);
    assert_eq!(fund.cash(), 900_000);

    let track = fund.export();
    let report = audit_fund(&track, fund.decision_config(), ora.config()).expect("audit verifies");

    assert_eq!(report.turns, 4, "four on-ledger turns");
    assert_eq!(report.trades, 3, "three fills");
    assert_eq!(report.holds, 1, "one hold");
    assert_eq!(report.final_cash, 900_000);
    assert_eq!(report.open_positions.get("BTC"), Some(&1));
    // Mark-to-market of the 1 open unit at its last attested price (100_000) → equity 1_000_000.
    assert_eq!(report.mark_to_market, 100_000);
    assert_eq!(report.equity, 1_000_000);
    assert_eq!(report.total_pnl, 0);

    // The finalized chain is light-client-verifiable and each landed turn is a member.
    track.node.verify().expect("chain verifies");
    for r in &track.records {
        assert!(
            track.node.contains(&r.turn_hash),
            "turn on the finalized log"
        );
    }
    // The recomputed commitment equals the on-ledger witness.
    assert!(track.on_ledger_commitment.is_some());
}

/// TOOTH 1 — an over-mandate trade is REFUSED by the cap gate (disallowed asset and
/// over-position), and NOTHING lands.
#[test]
fn over_mandate_trade_is_refused() {
    let mut ora = oracle("BTC", 100_000);
    ora.set_price("DOGE", 50);
    let mut fund = open_fund(mandate(), &ora);

    // (a) Disallowed asset → refused, no state change.
    let mut brain = RecordedBrain::new(vec![Decision::buy("DOGE", 1, "not allowed")]);
    let err = fund
        .step(&ora, &mut brain)
        .expect_err("disallowed asset refused");
    assert!(matches!(
        err,
        FundError::Mandate(MandateViolation::AssetNotAllowed(_))
    ));
    assert_eq!(fund.position("DOGE"), 0);
    assert_eq!(fund.cash(), 1_000_000);
    assert_eq!(fund.export().records.len(), 0, "no turn landed");

    // (b) Over-position (cap = 10; buy 11) → refused.
    let mut brain = RecordedBrain::new(vec![Decision::buy("BTC", 11, "over the position cap")]);
    let err = fund
        .step(&ora, &mut brain)
        .expect_err("over-position refused");
    assert!(matches!(
        err,
        FundError::Mandate(MandateViolation::PositionExceeded { .. })
    ));
    assert_eq!(fund.position("BTC"), 0);
    assert_eq!(fund.export().records.len(), 0);
}

/// TOOTH 2 — an over-budget trade is REFUSED by the bounded budget (the lease). A buy whose
/// cost exceeds available cash cannot land.
#[test]
fn over_budget_trade_is_refused() {
    // Budget only covers 5 units at 100_000; position cap is generous.
    let m = Mandate {
        allowed_assets: vec!["BTC".to_string()],
        max_position: 100,
        budget: 500_000,
        max_turns: 16,
    };
    let ora = oracle("BTC", 100_000);
    let mut fund = open_fund(m, &ora);

    // Buy 6 units → cost 600_000 > budget 500_000 → refused.
    let mut brain = RecordedBrain::new(vec![Decision::buy("BTC", 6, "too big")]);
    let err = fund
        .step(&ora, &mut brain)
        .expect_err("over-budget refused");
    assert!(matches!(
        err,
        FundError::OverBudget {
            need: 600_000,
            have: 500_000
        }
    ));
    assert_eq!(fund.cash(), 500_000, "no draw");
    assert_eq!(fund.export().records.len(), 0, "no turn landed");
}

/// TOOTH 2b — the on-ledger TURN budget is a real executor cap: with `max_turns = 1`, the
/// SECOND on-ledger turn is refused host-side by the minter's rate-limited grant.
#[test]
fn over_turn_budget_is_refused_on_ledger() {
    let m = Mandate {
        allowed_assets: vec!["BTC".to_string()],
        max_position: 100,
        budget: 1_000_000,
        max_turns: 1,
    };
    let ora = oracle("BTC", 100_000);
    let mut fund = open_fund(m, &ora);
    let mut brain = RecordedBrain::new(vec![
        Decision::buy("BTC", 1, "first"),
        Decision::buy("BTC", 1, "second — over the turn budget"),
    ]);
    fund.step(&ora, &mut brain).expect("first turn lands");
    let err = fund
        .step(&ora, &mut brain)
        .expect_err("second turn refused by the executor");
    assert!(matches!(err, FundError::Ledger(_)));
    assert_eq!(fund.export().records.len(), 1, "only one turn landed");
}

/// TOOTH 3 — a fill claimed at an UNATTESTED price is REFUSED. A tampered price attestation
/// (a flipped notarized byte) and a price whose claimed amount is not the notarized one both
/// fail `verify_attested_price` at fill time.
#[test]
fn unattested_price_fill_is_refused() {
    use auditable_fund::PriceOracle;
    use auditable_fund::verify_attested_price;

    let ora = oracle("BTC", 100_000);

    // A genuine attested price verifies.
    let good: AttestedPrice = ora.price("BTC").expect("quote");
    verify_attested_price(&good, ora.config()).expect("a genuine attested price verifies");

    // (a) Tampered attestation → refused.
    let mut tampered = good.clone();
    let n = tampered.attestation.presentation.recv.len();
    tampered.attestation.presentation.recv[n - 3] ^= 0xFF;
    assert!(
        verify_attested_price(&tampered, ora.config()).is_err(),
        "a tampered price attestation is refused"
    );

    // (b) Claimed amount does not match the notarized body → refused (a price the fund can't prove).
    let mut lied = good.clone();
    lied.amount = 1; // claim a different price than the attestation notarizes
    assert!(
        verify_attested_price(&lied, ora.config()).is_err(),
        "a price whose claimed amount is not notarized is refused"
    );

    // And a fund built to trust a DIFFERENT oracle (different notary) refuses this price.
    let other = ModeledOracle::from_seed(&[0x99u8; 32]);
    assert!(
        verify_attested_price(&good, other.config()).is_err(),
        "a price attested under a different notary is refused"
    );
}

/// A helper: run a real 3-trade fund and return its track record + configs for tamper tests.
fn run_track() -> (
    auditable_fund::TrackRecord,
    AnthropicConfig,
    AnthropicConfig,
) {
    let ora = oracle("BTC", 100_000);
    let mut fund = open_fund(mandate(), &ora);
    let mut brain = RecordedBrain::new(vec![
        Decision::buy("BTC", 3, "a"),
        Decision::buy("BTC", 2, "b"),
        Decision::sell("BTC", 1, "c"),
    ]);
    for _ in 0..3 {
        fund.step(&ora, &mut brain).expect("step lands");
    }
    let track = fund.export();
    (track, fund.decision_config().clone(), ora.config().clone())
}

/// TOOTH 4 — a FORGED / altered / dropped / reordered track record FAILS the audit. The
/// green above is not a vacuous accept.
#[test]
fn forged_track_record_fails_audit() {
    // Baseline: the untouched track record audits clean.
    let (track, dcfg, ocfg) = run_track();
    audit_fund(&track, &dcfg, &ocfg).expect("the genuine track record audits");

    // (a) ALTERED FILL — inflate a fill price in a record without re-minting. The stated
    //     price no longer matches the attested amount AND the commitment chain diverges.
    {
        let mut forged = track.clone();
        forged.records[0].price += 50_000;
        forged.records[0].cash_after -= 3 * 50_000; // keep the book internally consistent
        let err = audit_fund(&forged, &dcfg, &ocfg).expect_err("an altered fill fails");
        assert!(
            matches!(
                err,
                AuditError::FillPriceMismatch(0) | AuditError::LedgerCommitmentMismatch
            ),
            "altered fill detected: {err:?}"
        );
    }

    // (b) DROPPED TRADE — remove a record. The turn count and the commitment both diverge.
    {
        let mut forged = track.clone();
        forged.records.pop();
        let err = audit_fund(&forged, &dcfg, &ocfg).expect_err("a dropped trade fails");
        assert!(
            matches!(
                err,
                AuditError::TurnCountMismatch { .. } | AuditError::LedgerCommitmentMismatch
            ),
            "dropped trade detected: {err:?}"
        );
    }

    // (c) REORDERED TRADES — swap two records. The order-sensitive commitment chain diverges.
    {
        let mut forged = track.clone();
        forged.records.swap(0, 1);
        let err = audit_fund(&forged, &dcfg, &ocfg).expect_err("a reordered record fails");
        assert!(
            matches!(
                err,
                AuditError::LedgerCommitmentMismatch | AuditError::MandateBreached { .. }
            ),
            "reordered trades detected: {err:?}"
        );
    }

    // (d) FABRICATED QUANTITY — claim a bigger buy than was minted. The recomputed
    //     commitment (and the re-derived book) diverge from the on-ledger witness.
    {
        let mut forged = track.clone();
        forged.records[0].qty += 5;
        forged.records[0].position_after += 5;
        let err = audit_fund(&forged, &dcfg, &ocfg).expect_err("a fabricated quantity fails");
        assert!(
            matches!(
                err,
                AuditError::LedgerCommitmentMismatch | AuditError::MandateBreached { .. }
            ),
            "fabricated quantity detected: {err:?}"
        );
    }

    // (e) FORGED ON-LEDGER WITNESS — an operator who edits records AND supplies a matching
    //     fake commitment still fails: the fake witness will not equal the recomputed chain
    //     for the tampered records unless the records are the true ones.
    {
        let mut forged = track.clone();
        forged.records[0].qty += 1;
        forged.on_ledger_commitment = forged.records.last().map(|r| r.commit_after);
        let err = audit_fund(&forged, &dcfg, &ocfg).expect_err("a forged witness fails");
        assert!(
            matches!(
                err,
                AuditError::LedgerCommitmentMismatch | AuditError::MandateBreached { .. }
            ),
            "forged witness detected: {err:?}"
        );
    }
}
