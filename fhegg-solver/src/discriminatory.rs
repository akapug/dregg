//! Discriminatory / pay-as-bid clearing — a DIFFERENT clearing on the same book.
//!
//! Uniform-price (`clearing.rs`) settles every trade at ONE price `p*`. The
//! discriminatory (pay-as-bid) auction settles each winning order at its OWN
//! limit: a filled bid pays its bid price, a filled ask receives its ask price.
//! Same book, different mechanism — both certified on the one engine.
//!
//! ## Winner-determination is a flow-LP (verify-not-find, reuses Cert-F)
//!
//! The EFFICIENT (surplus-maximising) fill is a max-weight two-sided clearing:
//!
//! ```text
//!   maximize   Σ_b v_b y_b − Σ_a c_a z_a          (gains from trade)
//!   subject to Σ_b y_b = Σ_a z_a                  (volume balance)
//!              0 ≤ y_b ≤ q_b,  0 ≤ z_a ≤ q_a
//! ```
//!
//! with `v_b` the bid limit price, `c_a` the ask limit price, `y_b`/`z_a` the
//! filled quantities. This is EXACTLY a volume-max circulation LP on a two-node
//! graph `{SELL, BUY}`: an ask `a` is an edge `SELL→BUY` (cap `q_a`, weight
//! `−c_a`), a bid `b` is an edge `BUY→SELL` (cap `q_b`, weight `+v_b`).
//! Conservation `Af = 0` at either node forces `Σ y_b = Σ z_a`, and `max wᵀf`
//! IS the gains-from-trade. So the winner-determination lowers to
//! [`crate::pdhg::FlowLp`] and carries the SAME linear [`crate::cert::CertF`]
//! primal-dual certificate — the marginal clearing price is the dual potential
//! `π_BUY − π_SELL`. (Tier-0 at small books, Tier-1 at scale, like any flow-LP.)
//!
//! ## The payment rule is a public function of the fills
//!
//! Given the certified fills, the two mechanisms differ only in settlement:
//!
//! ```text
//!   uniform-price:   every filled unit clears at p* = π_BUY − π_SELL
//!                    buyer pays p*·y_b,  seller gets p*·z_a,  auctioneer surplus 0
//!   discriminatory:  buyer pays v_b·y_b,  seller gets c_a·z_a
//!                    auctioneer surplus = Σ v_b y_b − Σ c_a z_a = wᵀf (the LP value)
//! ```
//!
//! The pay-as-bid auctioneer surplus is precisely the primal objective the Cert-F
//! certificate attests — so certifying the clearing certifies the surplus too.

use crate::cert::CertF;
use crate::clearing::{Order, Side};
use crate::pdhg::{restore_feasibility, solve_cpu, FlowLp};
use serde::Serialize;

/// Node 0 = SELL pool, node 1 = BUY pool of the two-node gains-from-trade graph.
const SELL: u32 = 0;
const BUY: u32 = 1;

/// The gains-from-trade flow-LP built from a book, plus the index map back to the
/// original orders (edge `e` ↔ order `order_of[e]`).
#[derive(Clone, Debug)]
pub struct DiscriminatoryProgram {
    pub lp: FlowLp,
    /// `order_of[e]` = index into the input `orders` slice for edge `e`.
    pub order_of: Vec<usize>,
}

/// Lower a book to the two-node gains-from-trade circulation. Bids become
/// `BUY→SELL` edges (weight `+v_b`), asks become `SELL→BUY` edges (weight `−c_a`);
/// `prices[level]` maps a price-level index to a numeric price.
pub fn build_program(orders: &[Order], prices: &[f64]) -> DiscriminatoryProgram {
    let mut edges = Vec::with_capacity(orders.len());
    let mut w = Vec::with_capacity(orders.len());
    let mut c = Vec::with_capacity(orders.len());
    let mut order_of = Vec::with_capacity(orders.len());
    for (idx, o) in orders.iter().enumerate() {
        let price = prices[(o.limit as usize).min(prices.len() - 1)];
        match o.side {
            Side::Bid => {
                edges.push((BUY, SELL));
                w.push(price); // +v_b
            }
            Side::Ask => {
                edges.push((SELL, BUY));
                w.push(-price); // −c_a
            }
        }
        c.push(o.qty as f64);
        order_of.push(idx);
    }
    DiscriminatoryProgram {
        lp: FlowLp {
            n_nodes: 2,
            edges,
            w,
            c,
        },
        order_of,
    }
}

/// The per-order fills + both settlement schemes for one cleared book.
#[derive(Clone, Debug, Serialize)]
pub struct DiscriminatoryClearing {
    /// Filled quantity per input order (index-aligned).
    pub fills: Vec<f64>,
    /// The cleared volume `V = Σ y_b = Σ z_a`.
    pub volume: f64,
    /// The marginal (uniform) price `p* = π_BUY − π_SELL` from the flow dual.
    pub marginal_price: f64,
    /// Discriminatory buyer outlay `Σ v_b y_b` (buyers pay their own bids).
    pub payg_buyer_pays: f64,
    /// Discriminatory seller receipts `Σ c_a z_a` (sellers get their own asks).
    pub payg_seller_gets: f64,
    /// Pay-as-bid auctioneer surplus `= payg_buyer_pays − payg_seller_gets = wᵀf`.
    pub discriminatory_surplus: f64,
    /// Uniform-price buyer outlay `p*·Σ y_b` (contrast — one price for all).
    pub uniform_buyer_pays: f64,
    /// Uniform-price seller receipts `p*·Σ z_a`.
    pub uniform_seller_gets: f64,
}

/// Solve the winner-determination flow-LP, restore an exact circulation, and read
/// off both settlement schemes. Returns `(clearing, Cert-F certificate)`.
pub fn clear_discriminatory(
    orders: &[Order],
    prices: &[f64],
    iters: usize,
) -> (DiscriminatoryClearing, CertF) {
    let prog = build_program(orders, prices);
    let approx = solve_cpu(&prog.lp, iters);
    let (f, _viol) = restore_feasibility(&prog.lp, approx.f.clone());

    // ε scaled to the price magnitude (the weights are prices).
    let scale = prog
        .lp
        .w
        .iter()
        .fold(1.0f64, |m, &x| m.max(x.abs()))
        .max(1.0);
    let cert = CertF::from_solution(&prog.lp, &f, &approx.y, 0.05 * scale);

    // The marginal (uniform) clearing price is the dual potential difference
    // π_SELL − π_BUY: a bid fills when v_b ≥ π_SELL−π_BUY and an ask fills when
    // c_a ≤ π_SELL−π_BUY, so this potential gap IS the marginal price.
    let marginal_price = approx.y[SELL as usize] - approx.y[BUY as usize];

    // Read fills back onto the original orders + accumulate the two settlements.
    let mut fills = vec![0.0f64; orders.len()];
    let mut volume = 0.0;
    let mut payg_buyer_pays = 0.0;
    let mut payg_seller_gets = 0.0;
    for (e, &oi) in prog.order_of.iter().enumerate() {
        let qty = f[e];
        fills[oi] = qty;
        let o = &orders[oi];
        let price = prices[(o.limit as usize).min(prices.len() - 1)];
        match o.side {
            Side::Bid => {
                volume += qty; // count volume on the buy side once
                payg_buyer_pays += price * qty;
            }
            Side::Ask => {
                payg_seller_gets += price * qty;
            }
        }
    }

    let clearing = DiscriminatoryClearing {
        fills,
        volume,
        marginal_price,
        payg_buyer_pays,
        payg_seller_gets,
        discriminatory_surplus: payg_buyer_pays - payg_seller_gets,
        uniform_buyer_pays: marginal_price * volume,
        uniform_seller_gets: marginal_price * volume,
    };
    (clearing, cert)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clearing::Order;

    /// Prices: level j maps to price j (unit grid).
    fn unit_prices(k: usize) -> Vec<f64> {
        (0..k).map(|j| j as f64).collect()
    }

    #[test]
    fn overlapping_book_clears_and_certifies() {
        // Bids at high prices (7,6), asks at low prices (3,4): they cross.
        let orders = vec![
            Order::bid(100, 7),
            Order::bid(50, 6),
            Order::ask(80, 3),
            Order::ask(40, 4),
        ];
        let (clr, cert) = clear_discriminatory(&orders, &unit_prices(10), 8000);
        let rep = cert.check();
        assert!(
            rep.valid,
            "winner-determination certificate must be valid: {rep:?}"
        );
        assert!(clr.volume > 0.0, "an overlapping book must trade");
        // Volume balance: Σ bid fills == Σ ask fills (conservation).
        let bid_vol: f64 = orders
            .iter()
            .zip(&clr.fills)
            .filter(|(o, _)| o.side == Side::Bid)
            .map(|(_, &f)| f)
            .sum();
        let ask_vol: f64 = orders
            .iter()
            .zip(&clr.fills)
            .filter(|(o, _)| o.side == Side::Ask)
            .map(|(_, &f)| f)
            .sum();
        assert!((bid_vol - ask_vol).abs() < 1e-6, "volume balances");
    }

    #[test]
    fn discriminatory_surplus_is_nonneg_and_beats_uniform() {
        // Pay-as-bid extracts each winner's full bid–ask spread → surplus ≥ the
        // uniform-price auctioneer surplus (which is exactly 0).
        let orders = vec![
            Order::bid(100, 8),
            Order::bid(60, 7),
            Order::ask(90, 2),
            Order::ask(50, 3),
        ];
        let (clr, _) = clear_discriminatory(&orders, &unit_prices(10), 8000);
        // The marginal (uniform) clearing price is positive and lies between the
        // ask range (2,3) and the bid range (7,8): the marginal bid (7) sets it.
        assert!(
            clr.marginal_price > 0.0 && clr.marginal_price < 9.0,
            "marginal price must be a sane positive clearing price: {}",
            clr.marginal_price
        );
        assert!(
            clr.uniform_buyer_pays > 0.0,
            "uniform outlay must be positive"
        );
        assert!(
            clr.discriminatory_surplus > -1e-6,
            "pay-as-bid surplus ≥ 0: {}",
            clr.discriminatory_surplus
        );
        let uniform_surplus = clr.uniform_buyer_pays - clr.uniform_seller_gets;
        assert!(
            uniform_surplus.abs() < 1e-6,
            "uniform-price auctioneer surplus is 0 by construction: {uniform_surplus}"
        );
        // Buyers pay strictly more under pay-as-bid than under one clearing price
        // (they clear ABOVE the marginal price), so the surplus is strictly larger.
        assert!(
            clr.discriminatory_surplus > uniform_surplus + 1e-6,
            "discriminatory surplus {} must exceed uniform {}",
            clr.discriminatory_surplus,
            uniform_surplus
        );
    }

    #[test]
    fn disjoint_book_does_not_trade() {
        // All bids below all asks → no gains from trade → the LP optimum is 0.
        let orders = vec![
            Order::bid(100, 2),
            Order::bid(50, 1),
            Order::ask(80, 7),
            Order::ask(40, 8),
        ];
        let (clr, cert) = clear_discriminatory(&orders, &unit_prices(10), 8000);
        assert!(cert.check().valid, "the zero-flow certificate is valid");
        assert!(
            clr.volume < 1e-6,
            "disjoint book must not trade: V={}",
            clr.volume
        );
        assert!(
            clr.discriminatory_surplus.abs() < 1e-6,
            "no surplus with no trade"
        );
    }

    #[test]
    fn tampered_winner_determination_is_rejected() {
        let orders = vec![Order::bid(100, 7), Order::ask(80, 3), Order::ask(40, 4)];
        let (_, mut cert) = clear_discriminatory(&orders, &unit_prices(10), 8000);
        cert.f[0] += 5.0; // break conservation on the winner-determination flow
        assert!(!cert.check().valid, "tampered fills must be rejected");
    }
}
