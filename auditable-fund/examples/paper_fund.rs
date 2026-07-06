//! A runnable auditable fund: a modeled brain trades a bounded mandate against an attested
//! price oracle; every decision lands as an attested, on-ledger turn; then a THIRD PARTY
//! audits the track record — verifying the chain, the attestations, and the mandate — and
//! reports the P&L.
//!
//! ⚑ PAPER-ONLY. Every fill is simulated against an attested price. No exchange order, no
//!   custody, no real money.
//!
//! Run: `cargo run --manifest-path auditable-fund/Cargo.toml --example paper_fund`

use auditable_fund::{Fund, Mandate, ModeledOracle, ThresholdBrain, audit_fund};

fn main() {
    println!("== The auditable fund (PAPER-ONLY) ==\n");

    // The mandate as caps: BTC only, ≤ 8 units, 1_000_000 cents budget, ≤ 20 on-ledger turns.
    let mandate = Mandate {
        allowed_assets: vec!["BTC".to_string()],
        max_position: 8,
        budget: 1_000_000,
        max_turns: 20,
    };
    println!(
        "mandate: assets={:?} max_position={} budget={} max_turns={}",
        mandate.allowed_assets, mandate.max_position, mandate.budget, mandate.max_turns
    );

    // The attested price oracle (a deterministic modeled zkOracle). The fund pins its notary.
    let mut oracle = ModeledOracle::from_seed(&[0x11u8; 32]);
    let oracle_config = oracle.config().clone();

    let mut fund = Fund::open(
        "demo.fund.dregg",
        mandate,
        &[0x2au8; 32],
        oracle_config.clone(),
    )
    .expect("open");
    let decision_config = fund.decision_config().clone();

    // A modeled momentum brain: buy under 95_000, sell over 105_000.
    let mut brain = ThresholdBrain {
        asset: "BTC".to_string(),
        buy_below: 95_000,
        sell_above: 105_000,
        qty: 2,
    };

    // A modeled price path over several rounds.
    let path = [90_000i64, 92_000, 108_000, 100_000, 94_000, 110_000];
    for (round, &px) in path.iter().enumerate() {
        oracle.set_price("BTC", px);
        oracle.tick();
        match fund.step(&oracle, &mut brain) {
            Ok(o) => {
                let pos = if matches!(o.side, auditable_fund::Side::Hold) {
                    format!("BTC={}", fund.position("BTC"))
                } else {
                    format!("BTC={}", o.position_after)
                };
                println!(
                    "round {round}: price={px:>7}  {:<4} -> cash={:>8} {pos}  turn={}",
                    format!("{:?}", o.side),
                    o.cash_after,
                    hex8(&o.turn_hash),
                );
            }
            Err(e) => println!("round {round}: price={px:>7}  REFUSED: {e}"),
        }
    }

    // ── The third-party audit ──
    println!("\n== third-party audit ==");
    let track = fund.export();
    match audit_fund(&track, &decision_config, &oracle_config) {
        Ok(report) => {
            println!(
                "chain: light-client VERIFIED ({} finalized turns)",
                report.turns
            );
            println!(
                "trades={} holds={}  final_cash={}  open_positions={:?}",
                report.trades, report.holds, report.final_cash, report.open_positions
            );
            println!(
                "mark_to_market={}  equity={}  total_pnl={}  (realized_pnl={})",
                report.mark_to_market, report.equity, report.total_pnl, report.realized_pnl
            );
            println!(
                "\nEVERY decision attested, EVERY fill at an attested price, mandate held EVERY turn — audited, not trusted."
            );
        }
        Err(e) => println!("AUDIT FAILED: {e}"),
    }
}

fn hex8(h: &[u8; 32]) -> String {
    h[..4].iter().map(|b| format!("{b:02x}")).collect()
}
