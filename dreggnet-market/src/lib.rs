//! # DreggNet offering #commerce — a sealed-bid AUCTION / MARKET.
//!
//! The dungeon (offering #0) proved the [`Offering`] abstraction over a *game*; hosted-Hermes
//! over an *agent*; a grain over *compute*; polis over *governance*. This crate proves it reaches
//! an **economic flow** — a market where **value moves**, conservation-checked — by wrapping the
//! real sealed-bid auction substrate as a [`MarketOffering`]:
//!
//!   * **LIST** ([`advance`](Offering::advance) with [`TURN_LIST`]) — a seller opens a listing: a
//!     REAL factory-born auction cell comes alive through the verified executor (a
//!     `CreateCellFromFactory` turn → a genuine [`TurnReceipt`]). The born cell carries the auction
//!     policy FOR LIFE (the `WriteOnce` commit board + the `StrictMonotonic(PHASE)` lifecycle).
//!   * **BID** ([`TURN_BID`]) — a bidder places a **sealed** commit-reveal bid: the [`Bid::seal`]
//!     digest (`BLAKE3(bidder‖value‖nonce)`) lands on the cell's on-ledger `WriteOnce` commit board
//!     as a real verified turn. The teeth are the substrate's, not ours: a **double-bid** (a bidder
//!     overwriting its own committed sealed bid) is a **real executor refusal** (`WriteOnce`); a
//!     **bid after the commit phase closes** is refused by the auction's own phase gate (nothing
//!     submitted — anti-ghost).
//!   * **SETTLE** ([`TURN_SETTLE`]) — the auctioneer closes the commit phase, reveals the bids, and
//!     **clears to the winning sealed bid**. The value moves through the VERIFIED per-asset ring
//!     settlement ([`settle_ring_verified`], the Rust image of the Lean `Ring.settleRing`): the
//!     winner pays its bid of the payment asset to the seller, the slot delivers the good to the
//!     winner, **per-asset Σδ = 0** or the whole award aborts (atomicity + conservation). A
//!     **below-reserve** clear or a **no-valid-bid** auction does **NOT** settle — no value moves,
//!     no resolve turn commits.
//!
//! [`verify`](Offering::verify) re-verifies the cleared chain: re-derive the settlement from the
//! recorded sealed bids and confirm the winner is the real high bid and the value move conserves
//! every asset. [`render`](Offering::render) / [`actions`](Offering::actions) paint the listing +
//! bids as cap-gated deos affordances.
//!
//! ## The substrate wrapped
//!
//! [`starbridge_sealed_auction`] — its in-process [`Auction`] commit/reveal/settle state machine
//! (whose [`Auction::settle`] folds the award ring through the verified executor, conservation-
//! checked) AND its on-ledger auction cell (the factory descriptor + `*_effects` turn builders the
//! executor re-enforces the `WriteOnce` board / `StrictMonotonic(PHASE)` lifecycle on). We consume
//! both altitudes; we re-implement neither sealed bidding nor settlement. See the crate `[HONEST
//! SCOPE]` note at the bottom for what a fuller market (a continuous order book, multi-asset
//! baskets, a live escrow-market clearing organ) adds.

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, EmbeddedExecutor, field_from_u64,
};
use dregg_cell::{CellMode, FactoryCreationParams};

use dregg_intent::verified_settle::VerifiedLedger;

use starbridge_sealed_auction::CellId as AuctionCellId;
use starbridge_sealed_auction::{
    AUCTION_FACTORY_VK, AssetId, Auction, AuctionError, Bid, HIGH_BID_SLOT, PHASE_SLOT, Phase,
    SELLER_SLOT, WINNER_SLOT, auction_child_program_vk, auction_factory_descriptor,
    close_commit_effects, commit_bid_effects, commit_slot, fund_ledger, resolve_effects,
    reveal_bid_effects,
};

use deos_view::{MenuItem, ViewNode};

/// The affordance verb a **seller** fires to open a listing/auction. `arg` is the RESERVE price
/// (the auction does not clear below it). One listing per session (a re-list is refused).
pub const TURN_LIST: &str = "list";

/// The affordance verb a **bidder** fires to place a sealed commit-reveal bid. `arg` is the bid
/// VALUE (the price offered). The `(bidder, value, nonce)` secret is held in the session until
/// SETTLE reveals it; only the [`Bid::seal`] digest is public during the commit phase.
pub const TURN_BID: &str = "bid";

/// The affordance verb the **auctioneer** fires to close the commit phase, reveal, and clear to the
/// winning sealed bid (the value moves, conservation-checked). `arg` is unused.
pub const TURN_SETTLE: &str = "settle";

/// The seller / awarding party's in-process auction-ledger handle (the low byte the verified
/// per-asset ledger indexes by). Receives the winner's payment.
const SELLER_HANDLE: AuctionCellId = 1;
/// The award-slot cell's handle — delivers the good (`slot_asset`) to the winner.
const SLOT_HANDLE: AuctionCellId = 2;
/// Bidder handles start here (bidder `i` = `BIDDER_BASE + i`), disjoint from seller/slot.
const BIDDER_BASE: AuctionCellId = 10;

/// The payment asset — what bidders bid in (the money that moves to the seller).
const PAY: AssetId = [0xA1_u8; 32];
/// The good on offer — the task-token / slot the seller's award cell delivers to the winner.
const GOOD: AssetId = [0x60_u8; 32];

/// A placed sealed bid, held in the session so SETTLE can reveal it. Carries the auction-ledger
/// `handle`, the on-ledger commit `slot` the seal was frozen into (a re-bid to this slot is the
/// `WriteOnce` executor refusal — the anti-double-bid tooth), and the [`Bid`] secret.
#[derive(Clone, Debug)]
struct PlacedBid {
    /// The identity that placed it (a re-bid by the same identity targets its own `slot`).
    who: DreggIdentity,
    /// The auction-ledger handle (seller/slot-disjoint) — the bidder cell in the settlement ring.
    handle: AuctionCellId,
    /// The on-ledger commit-board slot this bid's seal is frozen into (`WriteOnce`).
    slot: usize,
    /// The sealed bid secret `(bidder, value, nonce)` — revealed at SETTLE.
    bid: Bid,
}

/// The record of a cleared auction — the conserved post-ledger + the winning bid + the per-asset
/// conservation the SETTLE move produced. Held so [`MarketOffering::verify`] can re-derive it and a
/// driver can read the value that moved.
#[derive(Clone, Debug)]
pub struct Clearing {
    /// The winning sealed bid (the real high bid among the reveals).
    pub winner: Bid,
    /// The verified post-ledger the award ring folded to (conservation-checked).
    pub post: VerifiedLedger,
    /// The payment-asset total before/after the clear — EQUAL (per-asset Σδ = 0).
    pub pay_conserved: (i128, i128),
    /// The good-asset total before/after the clear — EQUAL (per-asset Σδ = 0).
    pub good_conserved: (i128, i128),
}

impl Clearing {
    /// The winning price (what the winner pays the seller in the payment asset).
    pub fn price(&self) -> i128 {
        self.winner.value
    }

    /// Whether every touched asset's total supply was preserved across the clear (Σδ = 0).
    pub fn conserved(&self) -> bool {
        self.pay_conserved.0 == self.pay_conserved.1
            && self.good_conserved.0 == self.good_conserved.1
    }
}

/// **A live market/auction session over the REAL sealed-auction substrate.** Owns the embedded
/// verified executor + the born auction cell (the listing's on-ledger handle, carrying the auction
/// policy for life), the in-process [`Auction`] commit/reveal/settle mirror (the executable witness
/// of the sealed-bid crypto — whose `settle` clears through the verified per-asset ring), the placed
/// sealed bids, the reserve price, and the accumulated [`TurnReceipt`] chain (the birth + each
/// commit + close + reveals + resolve — every one a real verified turn).
pub struct MarketSession {
    /// The agent driving the market (the auction cell's owner; signs every turn).
    cclerk: AppCipherclerk,
    /// The real embedded verified executor — the sole referee of every LIST/BID/SETTLE turn.
    executor: EmbeddedExecutor,
    /// The born auction cell (`None` until LIST births it). The listing's on-ledger handle; carries
    /// the `WriteOnce` commit board + `StrictMonotonic(PHASE)` lifecycle FOR LIFE.
    auction_cell: Option<CellId>,
    /// The in-process commit/reveal/settle state machine mirroring the on-ledger cell — the
    /// consumed substrate's executable witness of the sealed-bid protocol + the conserved settle.
    auction: Option<Auction>,
    /// The reserve price — the auction does NOT clear below it (a below-reserve high bid is refused).
    reserve: i128,
    /// The seller's identity (bound at LIST; the awarding party).
    seller: Option<DreggIdentity>,
    /// The placed sealed bids, in commit order (each frozen into its own `WriteOnce` slot).
    bids: Vec<PlacedBid>,
    /// A monotone nonce counter — each sealed bid gets a fresh blinding nonce.
    next_nonce: u64,
    /// The committed receipt chain (birth + commits + close + reveals + resolve).
    receipts: Vec<dregg_app_framework::TurnReceipt>,
    /// The cleared auction (`Some` once SETTLE clears to a winner) — the conserved value move.
    clearing: Option<Clearing>,
    /// The deterministic session seed (a re-derivation of the listing under this seed reproduces it).
    seed: u64,
}

impl MarketSession {
    /// Whether the market has been listed (the auction cell is born).
    pub fn is_listed(&self) -> bool {
        self.auction_cell.is_some()
    }

    /// The current auction phase (`None` until listed).
    pub fn phase(&self) -> Option<Phase> {
        self.auction.as_ref().map(|a| a.phase)
    }

    /// Whether the auction has settled (cleared to a winner).
    pub fn is_settled(&self) -> bool {
        self.clearing.is_some()
    }

    /// The number of committed sealed bids so far.
    pub fn bid_count(&self) -> usize {
        self.bids.len()
    }

    /// The number of real verified turns committed (birth + commits + close + reveals + resolve).
    pub fn receipts_len(&self) -> usize {
        self.receipts.len()
    }

    /// The clearing record (`Some` once settled) — the winner + the conserved post-ledger.
    pub fn clearing(&self) -> Option<&Clearing> {
        self.clearing.as_ref()
    }

    /// The reserve price this listing will not clear below.
    pub fn reserve(&self) -> i128 {
        self.reserve
    }

    /// Read the born auction cell's live `PHASE` register off the executor ledger (the on-ledger
    /// phase, `None` if unlisted). The on-ledger mirror of [`Self::phase`].
    pub fn onledger_phase(&self) -> Option<u64> {
        let cell = self.auction_cell?;
        let state = self.executor.cell_state(cell)?;
        Some(field_to_u64(&state.fields[PHASE_SLOT]))
    }

    /// Assign (or look up) the bidder handle + on-ledger slot for `who`. Returns
    /// `(handle, slot, already_placed)` — a bidder that has already bid keeps its slot (a re-bid to
    /// it is the `WriteOnce` refusal).
    fn bidder_slot(&self, who: &DreggIdentity) -> (AuctionCellId, usize, bool) {
        for pb in &self.bids {
            if &pb.who == who {
                return (pb.handle, pb.slot, true);
            }
        }
        let idx = self.bids.len();
        (BIDDER_BASE + idx as AuctionCellId, commit_slot(idx), false)
    }

    /// Build a freshly-funded settlement ledger from the recorded sealed bids: each bidder funded
    /// with its bid value in `PAY` (so the winner can really pay), the award slot funded in `GOOD`,
    /// seller/slot live. The conserved award ring folds against THIS ledger.
    fn fund_settlement(&self) -> VerifiedLedger {
        let good_supply: i128 = self
            .bids
            .iter()
            .map(|b| b.bid.value.max(0))
            .sum::<i128>()
            .max(1);
        let mut rows: Vec<(AuctionCellId, AssetId, i128)> = Vec::new();
        for pb in &self.bids {
            rows.push((pb.handle, PAY, pb.bid.value));
            rows.push((pb.handle, GOOD, 0));
        }
        rows.push((SELLER_HANDLE, PAY, 0));
        rows.push((SELLER_HANDLE, GOOD, 0));
        rows.push((SLOT_HANDLE, GOOD, good_supply));
        rows.push((SLOT_HANDLE, PAY, 0));
        fund_ledger(&rows)
    }
}

/// **The market offering** — a stateless factory over the sealed-bid auction. Each
/// [`open`](Offering::open) deploys a fresh [`MarketSession`] (its own embedded executor + the
/// deployed auction factory); each session hosts ONE listing driven LIST → BID* → SETTLE.
pub struct MarketOffering {
    /// Run-credits a BID's confined pricing overlay costs (`0` → free tier). The substrate turns are
    /// always free + verifiable; this only prices an optional intelligence overlay a frontend runs.
    bid_credits: u64,
}

impl MarketOffering {
    /// The free-tier market (no credit debited per action; the substrate turns are free).
    pub fn new() -> Self {
        MarketOffering { bid_credits: 0 }
    }

    /// A paid-tier market: each BID costs `credits` run-credits (a frontend debits them; the core
    /// only names the cost — the substrate turn itself is always free + verifiable).
    pub fn paid_bids(credits: u64) -> Self {
        MarketOffering {
            bid_credits: credits,
        }
    }

    /// LIST — a seller opens a listing: birth a REAL auction cell through the verified executor and
    /// bind the auction genesis (seller + COMMIT phase). The Landed receipt is the birth turn.
    fn do_list(&self, s: &mut MarketSession, input: &Action, actor: DreggIdentity) -> Outcome {
        if s.is_listed() {
            return Outcome::Refused(
                "this market is already listed (one listing per session)".into(),
            );
        }
        let reserve = input.arg.max(0) as i128;

        // Deploy the auction factory into the embedded executor and birth the auction cell — a real
        // `CreateCellFromFactory` turn refereed by the verified executor. The born cell carries the
        // auction policy (WriteOnce board + StrictMonotonic phase) FOR LIFE.
        s.executor.deploy_factory(auction_factory_descriptor());
        let owner = s.cclerk.public_key().0;
        // A deterministic token so the listing's cell id re-derives under the seed (replay identity).
        let token: [u8; 32] =
            *blake3::hash(format!("dreggnet-market listing seed={}", s.seed).as_bytes()).as_bytes();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(auction_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        // Fund the agent cell so the birth's creation budget is covered.
        s.executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&s.cclerk.cell_id()) {
                agent.state.set_balance(1_000_000_000);
            }
        });
        let birth = s
            .cclerk
            .create_from_factory(AUCTION_FACTORY_VK, owner, token, params);
        let receipt = match s.executor.submit_turn(&birth) {
            Ok(r) => r,
            Err(e) => {
                return Outcome::Refused(format!("the listing cell failed to come alive: {e}"));
            }
        };
        let born = CellId::derive_raw(&owner, &token);
        // Grant the driving agent an owner cap on the born cell + bind the SELLER register (genesis).
        s.executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&s.cclerk.cell_id()) {
                agent.capabilities.grant(born, AuthRequired::Signature);
            }
            if let Some(cell) = ledger.get_mut(&born) {
                cell.state
                    .set_field(SELLER_SLOT, field_from_u64(SELLER_HANDLE as u64));
                // PHASE starts at 0 == COMMIT (born fields are zero) — the listing opens in COMMIT.
            }
        });

        s.auction_cell = Some(born);
        s.auction = Some(Auction::new(SELLER_HANDLE, SLOT_HANDLE, PAY, GOOD));
        s.reserve = reserve;
        s.seller = Some(actor);
        s.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// BID — a bidder places a sealed commit-reveal bid. A re-bid by the same identity targets its
    /// own committed slot → a REAL `WriteOnce` executor refusal (the anti-double-bid tooth); a bid
    /// after the commit phase closes is refused by the auction's own phase gate (anti-ghost).
    fn do_bid(&self, s: &mut MarketSession, input: &Action, actor: DreggIdentity) -> Outcome {
        let Some(cell) = s.auction_cell else {
            return Outcome::Refused("nothing is listed yet — LIST first".into());
        };
        if s.is_settled() {
            return Outcome::Refused("the auction has already settled".into());
        }
        // The commit-phase gate (the consumed substrate's own refusal): no bid after the commit
        // phase closes. Nothing is submitted on a miss (anti-ghost).
        let phase = s
            .auction
            .as_ref()
            .map(|a| a.phase)
            .unwrap_or(Phase::Settled);
        if phase != Phase::Commit {
            return Outcome::Refused("the commit phase is closed — no more sealed bids".into());
        }
        if input.arg < 0 {
            return Outcome::Refused("a bid value must be non-negative".into());
        }
        let value = input.arg as i128;

        let (handle, slot, already) = s.bidder_slot(&actor);

        if already {
            // THE ANTI-DOUBLE-BID TOOTH — a bidder overwriting its own committed sealed bid. We
            // submit the overwrite turn to the bidder's frozen commit slot; the executor's
            // `WriteOnce(commit slot)` REFUSES it. Nothing commits (anti-ghost).
            let switched = Bid::new(handle, value, s.next_nonce);
            let action = s.cclerk.make_action(
                cell,
                "commit_bid",
                commit_bid_effects(cell, slot, &switched.seal()),
            );
            return match s.executor.submit_action(&s.cclerk, action) {
                Ok(_) => Outcome::Refused(
                    "a double-bid unexpectedly committed (the WriteOnce board should have refused it)".into(),
                ),
                Err(e) => Outcome::Refused(format!("double-bid refused: {e}")),
            };
        }

        // A fresh sealed bid — a real verified commit turn onto the WriteOnce board.
        let nonce = s.next_nonce;
        s.next_nonce += 1;
        let bid = Bid::new(handle, value, nonce);
        let seal = bid.seal();
        let action =
            s.cclerk
                .make_action(cell, "commit_bid", commit_bid_effects(cell, slot, &seal));
        let receipt = match s.executor.submit_action(&s.cclerk, action) {
            Ok(r) => r,
            Err(e) => return Outcome::Refused(format!("the sealed commit was refused: {e}")),
        };
        // Mirror into the in-process auction (the executable sealed-bid witness).
        if let Some(a) = s.auction.as_mut() {
            if let Err(e) = a.commit(seal) {
                return Outcome::Refused(format!("commit refused by the auction protocol: {e}"));
            }
        }
        s.bids.push(PlacedBid {
            who: actor,
            handle,
            slot,
            bid,
        });
        s.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// SETTLE — the auctioneer closes the commit phase, reveals every sealed bid, and clears to the
    /// winning bid. The value moves through the VERIFIED per-asset ring settlement (conserved). A
    /// below-reserve high bid or a no-valid-bid auction does NOT settle (no value moves, no resolve).
    fn do_settle(&self, s: &mut MarketSession) -> Outcome {
        let Some(cell) = s.auction_cell else {
            return Outcome::Refused("nothing is listed yet — LIST first".into());
        };
        if s.is_settled() {
            return Outcome::Refused("the auction has already settled".into());
        }
        if s.bids.is_empty() {
            return Outcome::Refused("no sealed bids were placed — nothing to settle".into());
        }

        // (1) Close the commit phase — a real verified turn (StrictMonotonic advances COMMIT→REVEAL).
        if s.auction.as_ref().map(|a| a.phase) == Some(Phase::Commit) {
            let action = s
                .cclerk
                .make_action(cell, "close_commit", close_commit_effects(cell));
            match s.executor.submit_action(&s.cclerk, action) {
                Ok(r) => s.receipts.push(r),
                Err(e) => {
                    return Outcome::Refused(format!("closing the commit phase was refused: {e}"));
                }
            }
            if let Some(a) = s.auction.as_mut() {
                a.seal_commit_phase();
            }
        }

        // (2) Reveal every sealed bid — each a real verified turn; mirror into the in-process auction
        // (a reveal binds ONLY a committed seal — the substrate's uncommitted-cannot-open tooth).
        let bids: Vec<Bid> = s.bids.iter().map(|b| b.bid).collect();
        for b in &bids {
            let action = s.cclerk.make_action(
                cell,
                "reveal_bid",
                reveal_bid_effects(cell, field_from_u64(b.bidder as u64), b.value.max(0) as u64),
            );
            match s.executor.submit_action(&s.cclerk, action) {
                Ok(r) => s.receipts.push(r),
                Err(e) => return Outcome::Refused(format!("a reveal was refused: {e}")),
            }
            if let Some(a) = s.auction.as_mut() {
                if let Err(e) = a.reveal(*b) {
                    return Outcome::Refused(format!(
                        "a reveal was refused by the auction protocol: {e}"
                    ));
                }
            }
        }

        // (3) Clear to the winner through the VERIFIED per-asset ring settlement (conservation-
        //     checked). The award ring is folded through the verified executor by `Auction::settle`.
        let ledger = s.fund_settlement();
        let pay_before = ledger.total_asset(&PAY);
        let good_before = ledger.total_asset(&GOOD);

        let (post, winner) = {
            let a = s.auction.as_mut().expect("listed");
            match a.settle(&ledger) {
                Ok(pw) => pw,
                Err(AuctionError::NoWinner) => {
                    return Outcome::Refused(
                        "no valid revealed bid — the auction does not settle".into(),
                    );
                }
                Err(e) => {
                    return Outcome::Refused(format!(
                        "settlement rejected by the verified executor: {e}"
                    ));
                }
            }
        };

        // (3b) THE RESERVE TOOTH — a winning bid below the reserve does NOT clear. The verified
        //      settlement above already folded, but a below-reserve outcome is not a sale: we do NOT
        //      commit the resolve turn and we leave the session UNSETTLED (the ledger clear is
        //      discarded; the on-ledger cell stays in REVEAL — no WINNER announced).
        if winner.value < s.reserve {
            // Roll the in-process auction back out of Settled so the session stays clearable/honest.
            // (Auction::settle set phase = Settled on success; re-open reveal so state reflects "no sale".)
            if let Some(a) = s.auction.as_mut() {
                a.phase = Phase::Reveal;
            }
            return Outcome::Refused(format!(
                "the high sealed bid {} is below the reserve {} — no sale, nothing settles",
                winner.value, s.reserve
            ));
        }

        let pay_after = post.total_asset(&PAY);
        let good_after = post.total_asset(&GOOD);

        // (4) Resolve — announce the winner on-ledger (a real verified turn: StrictMonotonic
        //     advances REVEAL→RESOLVED; WriteOnce freezes WINNER / HIGH_BID). This is the Landed
        //     receipt for SETTLE.
        let action = s.cclerk.make_action(
            cell,
            "resolve",
            resolve_effects(
                cell,
                field_from_u64(winner.bidder as u64),
                winner.value.max(0) as u64,
            ),
        );
        let receipt = match s.executor.submit_action(&s.cclerk, action) {
            Ok(r) => r,
            Err(e) => return Outcome::Refused(format!("announcing the winner was refused: {e}")),
        };
        s.receipts.push(receipt.clone());
        s.clearing = Some(Clearing {
            winner,
            post,
            pay_conserved: (pay_before, pay_after),
            good_conserved: (good_before, good_after),
        });
        Outcome::Landed {
            receipt,
            ended: true,
        }
    }
}

impl Default for MarketOffering {
    fn default() -> Self {
        MarketOffering::new()
    }
}

impl Offering for MarketOffering {
    type Session = MarketSession;

    fn open(&self, cfg: SessionConfig) -> Result<MarketSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        // A deterministic federation id from the seed (stable listing identity per session).
        let fed = *blake3::hash(format!("dreggnet-market fed seed={seed}").as_bytes()).as_bytes();
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), fed);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        Ok(MarketSession {
            cclerk,
            executor,
            auction_cell: None,
            auction: None,
            reserve: 0,
            seller: None,
            bids: Vec::new(),
            next_nonce: 1,
            receipts: Vec::new(),
            clearing: None,
            seed,
        })
    }

    fn actions(&self, session: &MarketSession) -> Vec<Action> {
        if !session.is_listed() {
            return vec![Action::new(
                "List an item (open a sealed auction)",
                TURN_LIST,
                0,
                true,
            )];
        }
        if session.is_settled() {
            return Vec::new();
        }
        let in_commit = session.phase() == Some(Phase::Commit);
        vec![
            Action::new("Place a sealed bid", TURN_BID, 0, in_commit),
            Action::new(
                "Settle — reveal and clear to the winning bid",
                TURN_SETTLE,
                0,
                !session.bids.is_empty(),
            ),
        ]
    }

    fn advance(&self, session: &mut MarketSession, input: Action, actor: DreggIdentity) -> Outcome {
        match input.turn.as_str() {
            TURN_LIST => self.do_list(session, &input, actor),
            TURN_BID => self.do_bid(session, &input, actor),
            TURN_SETTLE => self.do_settle(session),
            other => Outcome::Refused(format!("unknown market affordance: {other}")),
        }
    }

    /// Re-verify the cleared chain: re-derive the settlement from the recorded sealed bids and
    /// confirm (a) the winner is the real high bid, (b) the value move conserves every asset
    /// (per-asset Σδ = 0), and (c) the on-ledger WINNER / HIGH_BID registers match the real winner.
    /// Before settlement, verify confirms every recorded seal is frozen on the on-ledger commit board.
    fn verify(&self, session: &MarketSession) -> VerifyReport {
        let turns = session.receipts_len();
        let Some(cell) = session.auction_cell else {
            return VerifyReport::broken(turns, "nothing listed — no chain to verify");
        };

        // (a) Every recorded seal must be frozen on the on-ledger WriteOnce commit board.
        let Some(state) = session.executor.cell_state(cell) else {
            return VerifyReport::broken(turns, "the listing cell is not in the ledger");
        };
        for pb in &session.bids {
            if state.fields[pb.slot] != pb.bid.seal() {
                return VerifyReport::broken(
                    turns,
                    format!("commit slot {} does not hold the recorded seal", pb.slot),
                );
            }
        }

        let Some(clearing) = &session.clearing else {
            // Not yet cleared — the committed board is consistent; that is all there is to check.
            return VerifyReport::ok(turns);
        };

        // (b) Re-derive the clear from scratch through the same verified settlement path.
        let mut replay = Auction::new(SELLER_HANDLE, SLOT_HANDLE, PAY, GOOD);
        for pb in &session.bids {
            if replay.commit(pb.bid.seal()).is_err() {
                return VerifyReport::broken(turns, "a recorded seal failed re-commit");
            }
        }
        replay.seal_commit_phase();
        for pb in &session.bids {
            if replay.reveal(pb.bid).is_err() {
                return VerifyReport::broken(
                    turns,
                    "a recorded bid failed re-reveal (not committed)",
                );
            }
        }
        let ledger = session.fund_settlement();
        let (post2, winner2) = match replay.settle(&ledger) {
            Ok(pw) => pw,
            Err(e) => return VerifyReport::broken(turns, format!("re-settlement failed: {e}")),
        };
        // The winner must be the real high bid, and the re-derived post-ledger must match.
        if winner2 != clearing.winner {
            return VerifyReport::broken(
                turns,
                "the re-derived winner differs from the recorded winner",
            );
        }
        let real_high = session
            .bids
            .iter()
            .map(|b| b.bid.value)
            .max()
            .unwrap_or(i128::MIN);
        if clearing.winner.value != real_high {
            return VerifyReport::broken(turns, "the recorded winner is not the real high bid");
        }
        if post2 != clearing.post {
            return VerifyReport::broken(
                turns,
                "the re-derived post-ledger differs (settlement not reproducible)",
            );
        }
        // (c) Conservation must hold (per-asset Σδ = 0).
        if !clearing.conserved() {
            return VerifyReport::broken(turns, "the clear did not conserve every asset (Σδ ≠ 0)");
        }
        // (d) The on-ledger result registers announce the real winner.
        let onchain_winner = field_to_u64(&state.fields[WINNER_SLOT]);
        let onchain_high = field_to_u64(&state.fields[HIGH_BID_SLOT]);
        if onchain_winner != clearing.winner.bidder as u64 {
            return VerifyReport::broken(
                turns,
                "the on-ledger WINNER register does not match the real winner",
            );
        }
        if onchain_high != clearing.winner.value.max(0) as u64 {
            return VerifyReport::broken(
                turns,
                "the on-ledger HIGH_BID register does not match the winning bid",
            );
        }
        VerifyReport::ok(turns)
    }

    fn render(&self, session: &MarketSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        if !session.is_listed() {
            children.push(ViewNode::Text(
                "No listing yet. A seller opens a sealed auction.".into(),
            ));
        } else {
            let phase = match session.phase() {
                Some(Phase::Commit) => "COMMIT (sealed bids accepted)",
                Some(Phase::Reveal) => "REVEAL",
                Some(Phase::Settled) => "SETTLED",
                None => "—",
            };
            children.push(ViewNode::Section {
                title: "Listing".into(),
                tag: "muted".into(),
                children: vec![ViewNode::Text(format!(
                    "reserve {} · phase {} · sealed bids {}",
                    session.reserve,
                    phase,
                    session.bid_count()
                ))],
            });
            if let Some(c) = &session.clearing {
                children.push(ViewNode::Section {
                    title: "Cleared".into(),
                    tag: "genuine".into(),
                    children: vec![ViewNode::Text(format!(
                        "winner bidder#{} at price {} · value moved conservation-checked (Σδ=0: {})",
                        c.winner.bidder, c.winner.value, c.conserved()
                    ))],
                });
            }
        }

        children.push(ViewNode::Section {
            title: "Verified turns".into(),
            tag: "genuine".into(),
            children: vec![ViewNode::Text(session.receipts_len().to_string())],
        });

        let items: Vec<MenuItem> = self
            .actions(session)
            .into_iter()
            .map(|a| MenuItem {
                label: a.label,
                turn: a.turn,
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        if !items.is_empty() {
            children.push(ViewNode::Section {
                title: "Market actions".into(),
                tag: "accent".into(),
                children: vec![ViewNode::Menu { items }],
            });
        }

        Surface(ViewNode::Section {
            title: "DreggNet Market — sealed-bid auction".into(),
            tag: "accent".into(),
            children,
        })
    }

    fn price(&self, input: &Action) -> RunCost {
        // The substrate turns are always free + verifiable; only a BID carries the optional
        // confined-pricing overlay a frontend runs (the free tier by default).
        if input.turn == TURN_BID {
            RunCost::credits(self.bid_credits)
        } else {
            RunCost::free()
        }
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the phase / winner / bid-value registers the auction cell stores).
fn field_to_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}
