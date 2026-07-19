//! **Certified clearing** — the Dark Bazaar CRAWL stone (`docs/deos/THE-DARK-BAZAAR.md` §3.1):
//! attach a fhEgg certificate to the dreggnet-market sealed-bid clearing, so the clearing is
//! **provably fair** (optimal + conserving) instead of merely re-derivable.
//!
//! This is an ADDITIVE path alongside the existing [`crate::MarketOffering`] clearing — nothing in
//! the live LIST/BID/SETTLE flow is rewired yet. A driver hands the revealed book (bidder handles +
//! bid values + the reserve) to [`clear_certified`] and gets back a [`CertifiedClearing`] receipt;
//! anyone can [`verify_certified`] it from scratch without trusting the producer.
//!
//! ## What the receipt contains, and what each part PROVES
//!
//! 1. **The wire settlement** ([`fhegg_solver::wire::Settlement`]) of the book under the built +
//!    tested uniform-price engine. The market's sealed-bid FIRST-PRICE rule (one unit, awarded to
//!    the top revealed bid, at that bid) is encoded as a book: one award ask (qty 1) priced at the
//!    top of the demand — the seller's award policy "sell the single unit at the best offered
//!    price, reserve permitting" said in book form — plus one qty-1 bid per bidder at its value.
//!    `Settlement::verify` re-derives the whole clearing and refuses ANY deviation (winner, price,
//!    every fill). The ask price is *derived from the bids*, and [`verify_certified`] re-derives
//!    the book from the bids, so the encoding is deterministic and binding, not producer-chosen.
//! 2. **The Cert-F certificate** ([`dregg_circuit_prove::cert_f_air::CertFWitness`]) for the award
//!    LP: the 2-node circulation with one unit-capacity edge per bid (weight = the bid value) and a
//!    unit return edge. Its exact optimum IS "award the unit to a highest bidder", and the LP
//!    objective `wᵀf` IS the price paid (first-price). The certificate `(f, π, s)` with `ε = 0`
//!    proves — via the Lean-mirrored integer predicate `Market.Certified`
//!    ([`CertFWitness::check`], every clause recomputed from the vectors) — that the recorded
//!    award **maximises bid value** (optimality: duality gap exactly 0) and **conserves the unit**
//!    (`A f = 0`: exactly one unit awarded, no unit minted or lost).
//!
//! HOW the witness was found is untrusted by design (verify-not-find): here the tight dual
//! `π = (0, v_max)`, `s = (w − Aᵀπ)₊` is constructed analytically, and the CHECKER is the
//! authority. No STARK constraint is authored in this module — the Cert-F AIR is the Lean-emitted,
//! byte-pinned descriptor path (`Market.CertFDescriptor.certFDescriptorOf`, emit-soundness proved
//! generically in Lean); this module only builds the *witness* that path consumes.
//!
//! ## Honest scope (the named residuals)
//!
//! * **STARK receipt: fails closed today.** [`CertifiedClearing::try_prove_stark`] rides
//!   `cert_f_air::prove_cert_f_zk`, which refuses any public program `(A, w, c, ε)` that is not a
//!   Lean-emitted, byte-pinned registered descriptor. A game book's program carries the bids in
//!   `w`, so each public auction program needs an emission plus proved integer range-admission
//!   policy before registration. Until a book program is registered, the STARK path returns the
//!   named refusal rather than a fake receipt. The check-level certificate (the same predicate the
//!   AIR enforces) is what this stone ships.
//! * **This is the PLAINTEXT certified tier.** The solver sees the revealed bids — exactly what
//!   the market's own SETTLE already reveals today, so nothing is *lost*; what is *gained* is the
//!   fairness proof. FHE-encrypted bids (Tier-0 DARK, the house cryptographically blind) are the
//!   named next layer, not claimed here.
//! * **Ties.** Both paths are deterministic but currently choose different stable keys: the
//!   certified wire path chooses the lowest input index, while the live sealed-auction path ranges
//!   over a seal-ordered `BTreeMap` and chooses the lexicographically greatest committed seal among
//!   equal values. Agreement is therefore exact for books with a unique top bid; the exact-tie
//!   policy join remains named rather than falsely equating the receipts.
//! * **Value bounds.** Bid values must sit in `[0, 2^20)` — the wire grid cap
//!   (`MAX_GRID_LEVELS`) and comfortably inside the Cert-F AIR's `VALUE_BITS = 28` range gadget.
//!   Larger denominations need a coarser tick (a caller-side policy, refused here, never rounded).

use dregg_circuit_prove::cert_f_air::{CertFWitness, prove_cert_f_zk, verify_cert_f_zk};
use fhegg_solver::wire::{
    MAX_GRID_LEVELS, Settlement, TickGrid, WIRE_VERSION, WireBook, WireError, WireOrder, WireSide,
    settle,
};
use std::fmt;

/// A bidder's handle in the book (the market's auction-ledger `CellId` widens into it losslessly).
pub type BidderHandle = u64;

/// One revealed sealed bid: `(bidder handle, bid value)`. Values are the market's `i128` bid
/// values; the certified path refuses negatives and values outside the grid (never rounds).
pub type BookBid = (BidderHandle, i128);

/// Everything the certified path refuses, and why. Refusals mirror the live market's own
/// (no bids / below reserve do not settle) plus the wire/certificate gates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertifiedError {
    /// An empty book settles nothing (the market refuses this at SETTLE too).
    NoBids,
    /// A negative bid value is not a bid (the market refuses these at BID time).
    NegativeBid { bidder: BidderHandle },
    /// The top bid is below the reserve — no sale, nothing clears, no certificate
    /// (mirrors the market's reserve tooth: a below-reserve clear is a refusal, not a receipt).
    BelowReserve { high: i128, reserve: i128 },
    /// A bid value at or above the wire grid cap (`MAX_GRID_LEVELS`); refused, never rounded.
    ValueTooLarge { bidder: BidderHandle, value: i128 },
    /// Two bids share a bidder handle (the market's WriteOnce board makes this impossible live;
    /// the certified path refuses rather than guesses).
    DuplicateBidder { bidder: BidderHandle },
    /// A wire-level refusal (settle/verify) — carries the wire engine's own named reason.
    Wire(WireError),
    /// The receipt does not bind / does not re-derive: the FIRST divergence, named.
    Tampered(&'static str),
    /// The built certificate failed the from-scratch Cert-F check — never emitted (fail closed).
    CertInvalid(String),
}

impl fmt::Display for CertifiedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CertifiedError::NoBids => write!(f, "no bids — nothing to clear"),
            CertifiedError::NegativeBid { bidder } => {
                write!(f, "bidder {bidder}: a bid value must be non-negative")
            }
            CertifiedError::BelowReserve { high, reserve } => write!(
                f,
                "the high bid {high} is below the reserve {reserve} — no sale, nothing clears"
            ),
            CertifiedError::ValueTooLarge { bidder, value } => write!(
                f,
                "bidder {bidder}: bid value {value} exceeds the certified grid cap ({MAX_GRID_LEVELS}); refused, never rounded"
            ),
            CertifiedError::DuplicateBidder { bidder } => {
                write!(f, "bidder {bidder} appears twice in the book")
            }
            CertifiedError::Wire(e) => write!(f, "wire refusal: {e}"),
            CertifiedError::Tampered(m) => write!(f, "receipt does not verify: {m}"),
            CertifiedError::CertInvalid(m) => {
                write!(f, "certificate failed its own from-scratch check: {m}")
            }
        }
    }
}

impl std::error::Error for CertifiedError {}

impl From<WireError> for CertifiedError {
    fn from(e: WireError) -> Self {
        CertifiedError::Wire(e)
    }
}

/// The stable market id the certified book carries (versioned with the encoding).
pub const CERTIFIED_MARKET_ID: &str = "dreggnet-market:certified:v1";

/// The order id of the seller's award ask in the certified book.
const AWARD_ORDER_ID: &str = "award";

/// **The certified clearing receipt** — the settlement + the fairness certificate, both bound to
/// the book (which is itself re-derivable from the bids + reserve). Produced by
/// [`clear_certified`]; checked from scratch by [`verify_certified`].
#[derive(Clone, Debug)]
pub struct CertifiedClearing {
    /// The deterministic certified book (re-derivable from `(bids, reserve)` — the binding root).
    pub book: WireBook,
    /// The uniform-price wire settlement of the book (`Settlement::verify` re-derives it exactly).
    pub settlement: Settlement,
    /// The Cert-F award-optimality certificate: `check().valid` with `gap == 0` proves the award
    /// maximises bid value and conserves the single unit.
    pub cert: CertFWitness,
    /// The winning bidder's handle.
    pub winner: BidderHandle,
    /// The price the winner pays (first-price: its own bid) — equals both the settlement's
    /// clearing price and the certificate's public objective `wᵀf`.
    pub price: i128,
}

impl CertifiedClearing {
    /// Attempt the hiding STARK receipt: mint a real dregg BabyBear+FRI proof over the
    /// Lean-emitted Cert-F AIR using `HidingFriPcs`, then self-verify it and return the
    /// public cleared value (`wᵀf` — the price).
    ///
    /// **Fails closed today**: the book's public program `(A, w, c, ε)` is not among the
    /// Lean-registered descriptors (ring-3 / market4), so `prove_cert_f_zk` refuses with the
    /// named "not registered" error. Registration additionally requires a sufficient integer
    /// admission policy; the hiding proof wiring itself lands here with zero rework.
    pub fn try_prove_stark(&self) -> Result<i64, String> {
        let (desc, proof, pis) = prove_cert_f_zk(&self.cert)?;
        verify_cert_f_zk(&desc, &proof, &pis)?;
        Ok(self.cert.objective())
    }
}

/// Validate the raw bids: non-empty, non-negative, in-grid, handle-unique. Returns `v_max`.
fn validate_bids(bids: &[BookBid]) -> Result<i128, CertifiedError> {
    if bids.is_empty() {
        return Err(CertifiedError::NoBids);
    }
    let mut seen: Vec<BidderHandle> = Vec::with_capacity(bids.len());
    let mut v_max: i128 = -1;
    for &(bidder, value) in bids {
        if value < 0 {
            return Err(CertifiedError::NegativeBid { bidder });
        }
        if value >= MAX_GRID_LEVELS as i128 {
            return Err(CertifiedError::ValueTooLarge { bidder, value });
        }
        if seen.contains(&bidder) {
            return Err(CertifiedError::DuplicateBidder { bidder });
        }
        seen.push(bidder);
        v_max = v_max.max(value);
    }
    Ok(v_max)
}

/// Build the deterministic certified book for `(bids, reserve)`: unit tick grid over
/// `[0, v_max]`, ONE award ask (qty 1) at the top of demand, one qty-1 bid per bidder at its
/// value. Refuses (never rounds / never fabricates) on any malformed input, and refuses a
/// below-reserve book — the market's own "no sale" semantics.
pub fn certified_book(bids: &[BookBid], reserve: i128) -> Result<WireBook, CertifiedError> {
    let v_max = validate_bids(bids)?;
    let reserve = reserve.max(0);
    if v_max < reserve {
        return Err(CertifiedError::BelowReserve {
            high: v_max,
            reserve,
        });
    }
    let mut orders = Vec::with_capacity(bids.len() + 1);
    // The seller's award policy in book form: one unit, sold at the best offered price.
    orders.push(WireOrder {
        id: AWARD_ORDER_ID.to_string(),
        side: WireSide::Ask,
        qty: 1,
        price: v_max as u64,
    });
    for &(bidder, value) in bids {
        orders.push(WireOrder {
            id: format!("bid:{bidder}"),
            side: WireSide::Bid,
            qty: 1,
            price: value as u64,
        });
    }
    Ok(WireBook {
        version: WIRE_VERSION,
        market_id: CERTIFIED_MARKET_ID.to_string(),
        grid: TickGrid {
            base: 0,
            tick: 1,
            k: (v_max as u32) + 1,
            price_exponent: 0,
        },
        orders,
    })
}

/// The canonical award-LP program + witness for `(bids, winner_idx)`: 2 nodes, one unit-capacity
/// edge per bid (weight = value) and a unit return edge; flow 1 on the winner's edge; the tight
/// dual `π = (0, v_max)`, `s = (w − Aᵀπ)₊`; `ε = 0`. Exact integers throughout.
fn award_cert(bids: &[BookBid], winner_idx: usize) -> CertFWitness {
    let n = bids.len();
    let v_max: i64 = bids.iter().map(|&(_, v)| v as i64).max().unwrap_or(0);
    let mut edges: Vec<(u32, u32)> = vec![(0, 1); n];
    edges.push((1, 0)); // the unit return edge — caps total awards at one.
    let mut w: Vec<i64> = bids.iter().map(|&(_, v)| v as i64).collect();
    w.push(0);
    let c: Vec<i64> = vec![1; n + 1];
    let mut f: Vec<i64> = vec![0; n + 1];
    f[winner_idx] = 1;
    f[n] = 1;
    let pi: Vec<i64> = vec![0, v_max];
    // s = (w − Aᵀπ)₊: bid edges (0→1) see Aᵀπ = v_max ⇒ s = 0; the return edge (1→0) sees −v_max
    // ⇒ s = v_max. Dual-feasible and non-negative by construction; the CHECK re-derives it all.
    let mut s: Vec<i64> = vec![0; n];
    s.push(v_max);
    for (e, se) in s.iter_mut().enumerate().take(n) {
        *se = (w[e] - v_max).max(0); // 0 for every bid (v_max is the max) — spelled out, not assumed.
    }
    CertFWitness {
        n_nodes: 2,
        edges,
        w,
        c,
        f,
        pi,
        s,
        epsilon: 0,
    }
}

/// Check that `cert`'s PUBLIC program is exactly the canonical award LP of `bids` — the binding
/// that stops a producer proving optimality of a *different* auction. Returns the named first
/// divergence.
fn cert_binds_book(cert: &CertFWitness, bids: &[BookBid]) -> Result<(), CertifiedError> {
    let n = bids.len();
    if cert.n_nodes != 2 || cert.edges.len() != n + 1 {
        return Err(CertifiedError::Tampered(
            "certificate program shape does not match the book",
        ));
    }
    for e in 0..n {
        if cert.edges[e] != (0, 1) {
            return Err(CertifiedError::Tampered("certificate bid edge misdirected"));
        }
        if cert.w[e] != bids[e].1 as i64 {
            return Err(CertifiedError::Tampered(
                "certificate weights do not match the bid values",
            ));
        }
        if cert.c[e] != 1 {
            return Err(CertifiedError::Tampered(
                "certificate bid capacity is not 1",
            ));
        }
    }
    if cert.edges[n] != (1, 0) || cert.w[n] != 0 || cert.c[n] != 1 {
        return Err(CertifiedError::Tampered(
            "certificate return edge does not match the award LP",
        ));
    }
    if cert.epsilon != 0 {
        return Err(CertifiedError::Tampered(
            "certificate epsilon loosened (the award certificate is exact: ε = 0)",
        ));
    }
    Ok(())
}

/// Extract the winning bid index from the settlement fills (fills are index-aligned with the
/// book: `fills[0]` = the award ask, `fills[1 + i]` = `bids[i]`).
fn settlement_winner_idx(settlement: &Settlement, n_bids: usize) -> Result<usize, CertifiedError> {
    if settlement.fills.len() != n_bids + 1 {
        return Err(CertifiedError::Tampered("settlement fill count is wrong"));
    }
    if settlement.fills[0].qty != 1 {
        return Err(CertifiedError::Tampered("the award ask did not fill"));
    }
    let mut winner: Option<usize> = None;
    for i in 0..n_bids {
        match settlement.fills[1 + i].qty {
            0 => {}
            1 => {
                if winner.is_some() {
                    return Err(CertifiedError::Tampered("more than one winning fill"));
                }
                winner = Some(i);
            }
            _ => return Err(CertifiedError::Tampered("a fill exceeds the unit award")),
        }
    }
    winner.ok_or(CertifiedError::Tampered(
        "no winning fill in the settlement",
    ))
}

/// **Clear a book with a certificate.** Uniform-price-settle the deterministic certified book
/// (the drop-in image of the market's first-price award), build the Cert-F award-optimality
/// certificate, and GATE emission on the from-scratch checks: the settlement re-derives
/// (`Settlement::verify`) and the certificate is valid + exactly tight (`gap == 0`). Anything
/// less is a refusal, never a receipt.
pub fn clear_certified(
    bids: &[BookBid],
    reserve: i128,
) -> Result<CertifiedClearing, CertifiedError> {
    let book = certified_book(bids, reserve)?;
    let settlement = settle(&book)?;
    // Emission gate 1: the settlement must re-derive from the book (verify-not-find).
    settlement.verify(&book)?;

    let v_max = bids.iter().map(|&(_, v)| v).max().expect("non-empty");
    if !settlement.crossed
        || settlement.clearing_price != Some(v_max as u64)
        || settlement.cleared_volume != 1
    {
        // By construction the certified book crosses at v_max with one unit; anything else is a
        // wire-engine divergence we refuse to certify rather than paper over.
        return Err(CertifiedError::CertInvalid(format!(
            "settlement diverged from the award encoding: crossed={} price={:?} volume={}",
            settlement.crossed, settlement.clearing_price, settlement.cleared_volume
        )));
    }
    let winner_idx = settlement_winner_idx(&settlement, bids.len())?;
    let (winner, winner_value) = bids[winner_idx];
    if winner_value != v_max {
        return Err(CertifiedError::CertInvalid(
            "the settled winner is not a top bid".to_string(),
        ));
    }

    let cert = award_cert(bids, winner_idx);
    // Emission gate 2: the certificate must pass the from-scratch Lean-mirrored integer check,
    // exactly tight. `CertFWitness::check` recomputes EVERY clause (incl. the duality gap) from
    // the vectors — nothing stored is trusted.
    let chk = cert.check();
    if !chk.valid || chk.gap != 0 {
        return Err(CertifiedError::CertInvalid(format!("{chk:?}")));
    }
    debug_assert_eq!(cert.objective(), v_max as i64, "wᵀf is the price");

    Ok(CertifiedClearing {
        book,
        settlement,
        cert,
        winner,
        price: v_max,
    })
}

/// **Verify a certified clearing from scratch** — the consumer-side gate. Re-derives everything
/// from `(bids, reserve)` and refuses the first divergence:
///
/// 1. the book binds (re-derived book == receipt book);
/// 2. the settlement re-derives exactly (`Settlement::verify` — winner, price, every fill);
/// 3. the certificate's public program binds to the book (weights are the bid values, ε = 0);
/// 4. the certificate passes the Lean-mirrored integer Cert-F check, exactly tight (`gap == 0`)
///    — optimality (the award maximises bid value) + conservation (one unit, no minting);
/// 5. the certificate's awarded flow, the settlement's winning fill, and the receipt's
///    `winner`/`price` all name the same award at the same price (`wᵀf` == clearing price).
pub fn verify_certified(
    bids: &[BookBid],
    reserve: i128,
    receipt: &CertifiedClearing,
) -> Result<(), CertifiedError> {
    // (1) The book binds to the bids + reserve.
    let expected_book = certified_book(bids, reserve)?;
    if receipt.book != expected_book {
        return Err(CertifiedError::Tampered(
            "book does not bind to the bids/reserve",
        ));
    }
    // (2) The settlement re-derives exactly.
    receipt.settlement.verify(&receipt.book)?;
    // (3) The certificate program binds to the book.
    cert_binds_book(&receipt.cert, bids)?;
    // (4) The certificate is valid and exactly tight — every clause recomputed.
    let chk = receipt.cert.check();
    if !chk.valid {
        return Err(CertifiedError::Tampered(
            "certificate fails the Cert-F check",
        ));
    }
    if chk.gap != 0 {
        return Err(CertifiedError::Tampered(
            "certificate gap is not exactly 0 (award not proven optimal)",
        ));
    }
    // (5) Settlement ↔ certificate ↔ receipt all name the same award.
    let n = bids.len();
    let winner_idx = settlement_winner_idx(&receipt.settlement, n)?;
    for i in 0..n {
        let expected_flow = i64::from(i == winner_idx);
        if receipt.cert.f[i] != expected_flow {
            return Err(CertifiedError::Tampered(
                "certificate flow does not match the settlement's winning fill",
            ));
        }
    }
    if receipt.cert.f[n] != 1 {
        return Err(CertifiedError::Tampered(
            "certificate return edge does not carry the award unit",
        ));
    }
    let (winner, winner_value) = bids[winner_idx];
    if receipt.winner != winner || receipt.price != winner_value {
        return Err(CertifiedError::Tampered(
            "receipt winner/price does not match the settlement",
        ));
    }
    if receipt.settlement.clearing_price != Some(winner_value as u64) {
        return Err(CertifiedError::Tampered(
            "settlement clearing price is not the winning bid (first-price binding)",
        ));
    }
    if receipt.cert.objective() != winner_value as i64 {
        return Err(CertifiedError::Tampered(
            "certificate objective wᵀf is not the price",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MarketOffering, TURN_BID, TURN_LIST, TURN_SETTLE};
    use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

    fn seller() -> DreggIdentity {
        DreggIdentity("seller-alice".to_string())
    }
    fn bidder(n: &str) -> DreggIdentity {
        DreggIdentity(format!("bidder-{n}"))
    }

    /// Drive the REAL market end-to-end (list → bids → settle) and return the session.
    fn drive_market(
        game_bids: &[(&str, i64)],
        reserve: i64,
    ) -> (MarketOffering, crate::MarketSession) {
        let off = MarketOffering::new();
        let mut s = off.open(SessionConfig::with_seed(7)).expect("market opens");
        let out = off.advance(
            &mut s,
            Action::new("list", TURN_LIST, reserve, true),
            seller(),
        );
        assert!(matches!(out, Outcome::Landed { .. }), "LIST lands: {out:?}");
        for (who, v) in game_bids {
            let out = off.advance(&mut s, Action::new("bid", TURN_BID, *v, true), bidder(who));
            assert!(matches!(out, Outcome::Landed { .. }), "BID lands: {out:?}");
        }
        (off, s)
    }

    /// THE AGREEMENT TOOTH: the certified clearing of a small game book names the SAME winner at
    /// the SAME price as the live market's own settle — so the certified path is a real drop-in,
    /// not a parallel mechanism. Distinct bid values (the live market's tie-break on exact ties
    /// is HashMap-order nondeterministic — the named divergence in the module doc).
    #[test]
    fn certified_clearing_agrees_with_the_market() {
        let game_bids = [("alice", 30i64), ("bob", 50), ("carol", 40)];
        let (off, mut s) = drive_market(&game_bids, 25);
        let out = off.advance(
            &mut s,
            Action::new("settle", TURN_SETTLE, 0, true),
            seller(),
        );
        assert!(
            matches!(out, Outcome::Landed { .. }),
            "SETTLE lands: {out:?}"
        );
        let market = s.clearing().expect("market cleared").clone();
        assert!(market.conserved(), "the live market conserves");

        // The certified path over the same revealed book (handles = bid order indices).
        let bids: Vec<BookBid> = game_bids
            .iter()
            .enumerate()
            .map(|(i, &(_, v))| (i as u64, v as i128))
            .collect();
        let receipt = clear_certified(&bids, 25).expect("the certified path clears");

        // AGREEMENT: same price, and the winner is the same bid (distinct values ⇒ the value
        // identifies the bid).
        assert_eq!(
            receipt.price,
            market.price(),
            "certified price == market price"
        );
        assert_eq!(
            bids[receipt.winner as usize].1, market.winner.value,
            "certified winner is the market's winning bid"
        );
        assert_eq!(receipt.winner, 1, "bob (index 1) wins at 50");

        // And the market's own verify still holds — the drop-in changed nothing live.
        assert!(off.verify(&s).verified, "the live market chain verifies");
    }

    /// The certificate is REAL: valid under the Lean-mirrored integer Cert-F check, exactly
    /// tight (gap 0), objective == the price, and the whole receipt verifies from scratch.
    #[test]
    fn certificate_verifies_and_is_exactly_tight() {
        let bids: Vec<BookBid> = vec![(10, 30), (11, 50), (12, 40)];
        let receipt = clear_certified(&bids, 25).expect("clears");
        let chk = receipt.cert.check();
        assert!(chk.valid, "Cert-F check must pass: {chk:?}");
        assert_eq!(chk.gap, 0, "exactly tight: the award is proven optimal");
        assert_eq!(receipt.cert.objective(), 50, "wᵀf is the price");
        assert_eq!((receipt.winner, receipt.price), (11, 50));
        verify_certified(&bids, 25, &receipt).expect("the receipt verifies from scratch");
    }

    /// TAMPER TOOTH (settlement): a lied clearing price and a swapped winning fill are both
    /// refused by the wire re-derivation.
    #[test]
    fn tampered_settlement_is_refused() {
        let bids: Vec<BookBid> = vec![(10, 30), (11, 50), (12, 40)];
        let good = clear_certified(&bids, 25).expect("clears");
        verify_certified(&bids, 25, &good).expect("honest receipt verifies");

        // Lie about the price.
        let mut t = good.clone();
        t.settlement.clearing_price = Some(40);
        t.settlement.clearing_price_index = Some(40);
        assert!(
            verify_certified(&bids, 25, &t).is_err(),
            "a lied clearing price must be refused"
        );

        // Hand the award to a loser (fills index-aligned: 0=ask, 1..=bids).
        let mut t = good.clone();
        t.settlement.fills[2].qty = 0; // bob (the real winner)
        t.settlement.fills[1].qty = 1; // alice
        assert!(
            verify_certified(&bids, 25, &t).is_err(),
            "a swapped winning fill must be refused"
        );
    }

    /// TAMPER TOOTH (certificate): moving the awarded flow to a LOSER edge keeps conservation,
    /// box, and dual feasibility intact — ONLY the recomputed duality gap catches it (gap = 10
    /// > ε = 0). This is the optimality tooth: the exact tamper a stored-scalar gap check would
    /// miss, bitten because `CertFWitness::check` recomputes the gap from the vectors.
    #[test]
    fn tampered_certificate_flow_is_refused_by_the_gap() {
        let bids: Vec<BookBid> = vec![(10, 30), (11, 50), (12, 40)];
        let good = clear_certified(&bids, 25).expect("clears");

        let mut t = good.clone();
        t.cert.f[1] = 0; // un-award bob (edge 1, value 50)
        t.cert.f[2] = 1; // award carol (edge 2, value 40) — still conserving, still feasible
        let chk = t.cert.check();
        assert!(
            chk.conserves,
            "the tamper keeps conservation (that is the point)"
        );
        assert!(chk.dual_feasible && chk.slack_sign_ok && chk.box_ok);
        assert!(!chk.gap_ok, "the recomputed gap (10) catches the theft");
        assert!(!chk.valid);
        assert!(
            verify_certified(&bids, 25, &t).is_err(),
            "a sub-optimal award must be refused"
        );

        // Loosening ε to fit the theft is refused by the program binding (ε is pinned to 0).
        let mut t2 = good.clone();
        t2.cert.f[1] = 0;
        t2.cert.f[2] = 1;
        t2.cert.epsilon = 10;
        assert!(
            t2.cert.check().valid,
            "the loosened cert self-checks — binding must catch it"
        );
        assert!(
            verify_certified(&bids, 25, &t2).is_err(),
            "a loosened ε must be refused by the binding"
        );

        // Rewriting a bid weight DOWN (claiming carol bid 10) keeps the certificate SELF-valid
        // (dual still feasible, gap still 0) — only the book binding catches the rewrite. This
        // proves the binding tooth is not redundant with the certificate's own check.
        let mut t3 = good.clone();
        t3.cert.w[2] = 10;
        assert!(
            t3.cert.check().valid,
            "the down-rewritten cert self-checks — binding must be what refuses it"
        );
        assert!(
            verify_certified(&bids, 25, &t3).is_err(),
            "a rewritten bid weight must be refused by the binding"
        );
    }

    /// TAMPER TOOTH (receipt + book): a re-branded winner/price and a re-rooted book are refused.
    #[test]
    fn tampered_receipt_and_book_are_refused() {
        let bids: Vec<BookBid> = vec![(10, 30), (11, 50), (12, 40)];
        let good = clear_certified(&bids, 25).expect("clears");

        let mut t = good.clone();
        t.winner = 12;
        assert!(
            verify_certified(&bids, 25, &t).is_err(),
            "wrong winner refused"
        );

        let mut t = good.clone();
        t.price = 40;
        assert!(
            verify_certified(&bids, 25, &t).is_err(),
            "wrong price refused"
        );

        // The receipt against a DIFFERENT book (someone swapped the bids underneath).
        let other: Vec<BookBid> = vec![(10, 30), (11, 50), (12, 45)];
        assert!(
            verify_certified(&other, 25, &good).is_err(),
            "a receipt must not verify against different bids"
        );
        assert!(
            verify_certified(&bids, 35, &good).is_err(),
            "a receipt must not verify against a different reserve"
        );
    }

    /// The reserve tooth agrees on BOTH paths: below-reserve is a refusal, not a receipt —
    /// exactly the live market's "no sale" semantics.
    #[test]
    fn below_reserve_refuses_on_both_paths() {
        // Live market: high bid 20 under reserve 25 → SETTLE is a refusal.
        let (off, mut s) = drive_market(&[("alice", 15), ("bob", 20)], 25);
        let out = off.advance(
            &mut s,
            Action::new("settle", TURN_SETTLE, 0, true),
            seller(),
        );
        assert!(
            matches!(out, Outcome::Refused(_)),
            "the live market refuses a below-reserve settle: {out:?}"
        );
        assert!(!s.is_settled());

        // Certified path: the same book, the same refusal.
        let bids: Vec<BookBid> = vec![(0, 15), (1, 20)];
        assert_eq!(
            clear_certified(&bids, 25).unwrap_err(),
            CertifiedError::BelowReserve {
                high: 20,
                reserve: 25
            }
        );
    }

    /// Input refusals bite: empty book, negative bid, duplicate handle, over-grid value.
    #[test]
    fn malformed_books_are_refused() {
        assert_eq!(clear_certified(&[], 0).unwrap_err(), CertifiedError::NoBids);
        assert_eq!(
            clear_certified(&[(1, -5)], 0).unwrap_err(),
            CertifiedError::NegativeBid { bidder: 1 }
        );
        assert_eq!(
            clear_certified(&[(1, 10), (1, 20)], 0).unwrap_err(),
            CertifiedError::DuplicateBidder { bidder: 1 }
        );
        let huge = MAX_GRID_LEVELS as i128;
        assert_eq!(
            clear_certified(&[(1, huge)], 0).unwrap_err(),
            CertifiedError::ValueTooLarge {
                bidder: 1,
                value: huge
            }
        );
    }

    /// Exact top-bid ties: the certified path is DETERMINISTIC (lowest input index wins) — the
    /// documented convention. (The live market's HashMap tie pick is not deterministic; the
    /// module doc names the divergence, so ties are certified-path-only for now.)
    #[test]
    fn tied_top_bids_resolve_deterministically() {
        let bids: Vec<BookBid> = vec![(7, 50), (8, 50), (9, 30)];
        let receipt = clear_certified(&bids, 0).expect("clears");
        assert_eq!(
            (receipt.winner, receipt.price),
            (7, 50),
            "lowest index wins the tie"
        );
        verify_certified(&bids, 0, &receipt).expect("tie receipt verifies");
        assert_eq!(
            receipt.cert.check().gap,
            0,
            "a tied winner is still optimal"
        );
    }

    /// THE STARK PIN (fails closed): the certificate is VALID, but the book's public program is
    /// not among the Lean-registered Cert-F descriptors, so the STARK path refuses with the
    /// named error instead of minting anything. This pin FLIPS when the award-LP program family
    /// is emitted from `certFDescriptorOf` + byte-pinned + registered — the named next stone.
    #[test]
    fn stark_receipt_fails_closed_until_the_program_is_registered() {
        let bids: Vec<BookBid> = vec![(10, 30), (11, 50), (12, 40)];
        let receipt = clear_certified(&bids, 25).expect("clears");
        assert!(
            receipt.cert.check().valid,
            "the refusal is registration, not validity"
        );
        let err = receipt
            .try_prove_stark()
            .expect_err("an unregistered program must fail closed");
        assert!(
            err.contains("not registered"),
            "the refusal names registration: {err}"
        );
    }
}
