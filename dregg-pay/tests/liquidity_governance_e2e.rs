//! End-to-end driven test of the DEFERRED, SIGNER-GATED treasury edges on the
//! MOCK/devnet path — NO real funds, NO keys held by dregg-pay, NO network.
//!
//! Drives the whole authorize→sign→execute chain the way a real deployment would:
//!
//!   * a liquidity-event VOTE reaches quorum → mints a `SwapAuthorization`;
//!   * `JupiterSwap::execute` runs the authorized pile→fuel swap, MOCK-SIGNED by the
//!     operator, and the treasury pile DOWN / fuel UP;
//!   * a swap with an authorization from the WRONG governance authority is REFUSED;
//!   * a BELOW-QUORUM vote yields NO authorization (so no swap can execute);
//!   * `otc_settle` moves the pile to a buyer (mock-signed) and refuses when short.
//!
//! Run: `cargo test -p dregg-pay --test liquidity_governance_e2e -- --nocapture`.

use dregg_pay::{
    DepositAddress, GovernanceAuthority, InMemoryTreasuryStore, JupiterSwap, MockOracle,
    MockSigner, MockSwapVenue, PayConfig, SwapError, Treasury, otc_quote, otc_settle,
};

const ALICE: [u8; 32] = [1u8; 32];
const BOB: [u8; 32] = [2u8; 32];
const CAROL: [u8; 32] = [3u8; 32];

fn config() -> PayConfig {
    // THROWAWAY seed, MOCK $DREGG + MOCK USDC mints — never mainnet.
    let seed = *b"dregg-pay LIQUIDITY throwaway seed -- not real!!";
    let dregg_mint = [0x11u8; 32];
    let treasury_addr = DepositAddress([0xEEu8; 32]);
    let mut c = PayConfig::devnet_mock(seed, dregg_mint, treasury_addr, 1_000_000);
    c.usdc_mint = [0x22u8; 32];
    c
}

#[test]
fn liquidity_vote_authorizes_a_signed_pile_to_fuel_swap() {
    let c = config();
    println!("\n=== dregg-pay LIQUIDITY EDGE — vote → authorize → sign → execute ===");
    println!("network : {:?}", c.network);

    // The operator's governance certification authority (throwaway seed; operator-held
    // in prod, never hardcoded). It lives inside the governance engine.
    let authority = GovernanceAuthority::from_seed([7u8; 32]);
    let mut gov = dregg_pay::LiquidityGovernance::new([9u8; 32], authority, c.mint, c.usdc_mint);
    let authority_pk = gov.authority_public_key();

    // ── 1. PROPOSE a liquidity event: swap 100_000_000 atomic $DREGG, floor 400_000
    //       atomic USDC, over a 3-holder electorate, quorum M = 2. ──
    let proposal = gov
        .propose(
            "convert 100 $DREGG from the pile to USDC fuel?",
            100_000_000,
            400_000,
            vec![ALICE, BOB, CAROL],
            2,
        )
        .unwrap();
    println!(
        "proposal: swap {} atomic $DREGG, floor {} atomic USDC, quorum {}",
        proposal.amount, proposal.min_out, proposal.quorum_m
    );

    // ── 2. VOTE: alice + bob approve — the gated APPROVE option reaches quorum. ──
    let a = gov.issue_ballot(&proposal, ALICE).unwrap();
    let b = gov.issue_ballot(&proposal, BOB).unwrap();
    gov.vote(&proposal, &a, true).unwrap();
    // Below quorum after one vote: no authorization yet.
    assert!(
        gov.finalize(&proposal).unwrap().is_none(),
        "one APPROVE < quorum must not authorize"
    );
    gov.vote(&proposal, &b, true).unwrap();
    let tally = gov.tally(&proposal).unwrap();
    println!("tally [reject, approve] = {:?}", tally.per_option);
    assert_eq!(tally.per_option, vec![0, 2]);

    // ── 3. AUTHORIZE: the passed vote mints a SwapAuthorization. ──
    let auth = gov
        .finalize(&proposal)
        .unwrap()
        .expect("APPROVE at quorum authorizes the swap");
    assert_eq!(auth.amount, 100_000_000);
    assert_eq!(auth.min_out, 400_000);
    assert!(
        auth.verify(&authority_pk),
        "authorization verifies against the authority"
    );
    println!(
        "vote PASSED → SwapAuthorization minted ({} atomic $DREGG)",
        auth.amount
    );

    // ── 4. SIGN + EXECUTE: the operator signer signs; the swap moves pile → fuel. ──
    let treasury = Treasury::new(InMemoryTreasuryStore::new(), c.usdc_decimals);
    treasury.deposit_dregg(100_000_000); // the accumulated pile
    let venue = MockSwapVenue::new(5, 1000); // $0.005/$DREGG → 500_000 atomic USDC
    let swap = JupiterSwap::new(venue, c.mint, c.usdc_mint, authority_pk);
    let signer = MockSigner::from_seed([8u8; 32]); // operator-held; NEVER in dregg-pay

    assert_eq!(treasury.dregg_balance(), 100_000_000);
    assert_eq!(treasury.usdc_balance(), 0);
    let out = swap.execute(&auth, &signer, &treasury).unwrap();
    println!(
        "swap executed (mock-signed): {} $DREGG → {} USDC, tx {}",
        out.dregg_in, out.usdc_out, out.tx_reference
    );
    assert_eq!(out.dregg_in, 100_000_000);
    assert_eq!(out.usdc_out, 500_000);
    assert_eq!(treasury.dregg_balance(), 0, "pile drained by the swap");
    assert_eq!(treasury.usdc_balance(), 500_000, "fuel filled by the swap");

    // ── 5. UNAUTHORIZED: an authorization from a DIFFERENT governance authority is
    //       refused by the swap configured with the real authority pk. Non-vacuous. ──
    let wrong_authority = GovernanceAuthority::from_seed([0x99u8; 32]);
    let mut rogue_gov =
        dregg_pay::LiquidityGovernance::new([9u8; 32], wrong_authority, c.mint, c.usdc_mint);
    let rogue_proposal = rogue_gov
        .propose("rogue swap?", 100_000_000, 1, vec![ALICE], 1)
        .unwrap();
    let ra = rogue_gov.issue_ballot(&rogue_proposal, ALICE).unwrap();
    rogue_gov.vote(&rogue_proposal, &ra, true).unwrap();
    let rogue_auth = rogue_gov
        .finalize(&rogue_proposal)
        .unwrap()
        .expect("the rogue vote passes on ITS engine");
    let treasury2 = Treasury::new(InMemoryTreasuryStore::new(), c.usdc_decimals);
    treasury2.deposit_dregg(100_000_000);
    let refused = swap.execute(&rogue_auth, &signer, &treasury2);
    println!("wrong-authority authorization → {:?}", refused);
    assert_eq!(
        refused,
        Err(SwapError::Unauthorized),
        "a swap not authorized by THIS governance is refused"
    );
    assert_eq!(treasury2.dregg_balance(), 100_000_000, "nothing moved");

    println!("=== liquidity edge invariants held ===\n");
}

#[test]
fn below_quorum_liquidity_vote_yields_no_authorization() {
    let c = config();
    let authority = GovernanceAuthority::from_seed([7u8; 32]);
    let mut gov = dregg_pay::LiquidityGovernance::new([9u8; 32], authority, c.mint, c.usdc_mint);

    // Quorum M = 3 but only ONE holder approves → below quorum.
    let proposal = gov
        .propose("swap?", 50_000_000, 1, vec![ALICE, BOB, CAROL], 3)
        .unwrap();
    let a = gov.issue_ballot(&proposal, ALICE).unwrap();
    gov.vote(&proposal, &a, true).unwrap();

    // The quorum AffineLe refuses the decision-turn → no Decision → no authorization.
    assert!(
        gov.finalize(&proposal).unwrap().is_none(),
        "a below-quorum vote must NOT mint an authorization"
    );
    // And a REJECT majority likewise never authorizes.
    let b = gov.issue_ballot(&proposal, BOB).unwrap();
    let cc = gov.issue_ballot(&proposal, CAROL).unwrap();
    gov.vote(&proposal, &b, false).unwrap();
    gov.vote(&proposal, &cc, false).unwrap();
    assert!(
        gov.finalize(&proposal).unwrap().is_none(),
        "REJECT reaching count must not arm the APPROVE-gated authorization"
    );
}

#[test]
fn otc_settle_moves_pile_and_refuses_when_short() {
    let c = config();
    let oracle = MockOracle::new(0.005);
    let buyer = DepositAddress([0xAB; 32]);
    let signer = MockSigner::from_seed([5u8; 32]);

    // Fund the pile, quote an OTC fill, settle it behind the signer.
    let treasury = Treasury::new(InMemoryTreasuryStore::new(), c.usdc_decimals);
    treasury.deposit_dregg(1_000_000_000);
    let quote = otc_quote(1_000_000, treasury.dregg_balance(), &oracle, &c).unwrap();
    let settled = otc_settle(&quote, &buyer, &signer, &treasury).unwrap();
    println!(
        "\nOTC settle (mock-signed): {} $DREGG → buyer, {} USDC recorded",
        settled.dregg_out, settled.usdc_in
    );
    assert_eq!(settled.dregg_out, 222_222_222);
    assert_eq!(treasury.dregg_balance(), 1_000_000_000 - 222_222_222);
    assert_eq!(
        treasury.usdc_balance(),
        1_000_000,
        "USDC-in recorded as fuel"
    );

    // A settlement against a pile that no longer covers the fill is refused, no move.
    let small = Treasury::new(InMemoryTreasuryStore::new(), c.usdc_decimals);
    small.deposit_dregg(1_000_000); // far below the 222M fill
    let err = otc_settle(&quote, &buyer, &signer, &small).unwrap_err();
    println!("short-pile settle refused: {err}");
    assert_eq!(small.dregg_balance(), 1_000_000, "nothing moved on refusal");
    assert_eq!(small.usdc_balance(), 0);
}
