//! # Multichain / multinode INTEGRATION tests — composed end-to-end flows.
//!
//! These are NOT unit tests of one brick. Each drives a COMPOSED flow across the
//! landed pieces through the shared flow-builder ([`multichain::MultichainHarness`]),
//! exercising the honest multichain/multinode integration level:
//!
//!   * `cross_chain_deposit_a_clear_settle_b_via_socket` — THE HEADLINE: a token
//!     deposited on chain A (LC-attested lock) → shielded clear → settle on chain B,
//!     verified there through the OCIP socket. Forged / foreign / ill-formed
//!     attestations REJECTED at the socket.
//!   * `shielded_transfer_note_to_note` — a private payment (note → note), both
//!     polarities: conserving transfer accepted, an inflating one REJECTED.
//!   * `multi_asset_ring_clears_over_shielded_notes` — the cross-asset price-carrying
//!     ring (3 assets), both polarities.
//!   * `derivatives_price_cert_settles_as_shielded_note` — a REAL Price-Cert
//!     (European bond) settled as a shielded note flow; an arbitrage market yields
//!     no certificate (the honest negative).
//!   * `multinode_mpc_clearing_agrees_and_no_party_sees_all` — the n-party (n=4)
//!     federation MPC clear, wired to agree with the single-party clearing that
//!     settles the notes.
//!
//! HONEST SCOPE (see the module header of `multichain/mod.rs`): the LC binding, the
//! notes, the fhEgg clear, the Price-Cert, the custody gates are REAL. The two
//! chains are two local instances; the socket verify is the real acceptance GATE
//! with a Poseidon2 statement-binding standing in for the BN254 pairing; the
//! federation is an in-process n-party decomposition of the real engine. The real
//! pairing + Solidity deploy + persistent federation are ember-gated.

mod multichain;

use dregg_circuit::field::BABYBEAR_P;
use fhegg_solver::clearing::{Order, Side, clear};
use fhegg_solver::pricecert::{Market, PriceOutcome, solve_price_cert};
use multichain::{
    AcceptError, Chain, DreggSocket, MirrorState, MpcClearing, MultichainHarness, RingLeg,
    SettlementStatement, TransferError, clear_ring, custody_root_lanes, honest_attestation,
    mint_note, prove_settlement,
};

// The dregg instance both chains in the cross-chain flow settle against. A fixed,
// canonical 8-lane genesis anchor (WHICH dregg — the socket's trust root).
const DREGG_GENESIS: [u32; 8] = [11, 22, 33, 44, 55, 66, 77, 88];

const WETH: u64 = 0xC02A_AA39; // low bytes of the real WETH contract, as a felt id
const ETH_MAINNET: u64 = 1;
const BASE_L2: u64 = 8453;

// ===========================================================================
// THE HEADLINE — deposit on chain A → shielded clear → settle on chain B via socket.
// ===========================================================================

#[test]
fn cross_chain_deposit_a_clear_settle_b_via_socket() {
    let mut flow = multichain::FlowReport::new(
        "CROSS-CHAIN — deposit(A, LC-attested) → shielded clear → settle(B) via OCIP socket",
    );
    let mut h = MultichainHarness::new();

    // Two local chains (LABEL: two local instances, NOT two live networks). Chain A
    // = Ethereum-mainnet (the deposit source); chain B = a Base L2 (the settle
    // destination) with the OCIP consumer deployed, trusting the SAME dregg instance.
    let mut chain_a = Chain::new("ETH-mainnet (local)", DREGG_GENESIS);
    let mut chain_b = Chain::new("Base-L2 (local)", DREGG_GENESIS);
    chain_b.deploy_socket(DreggSocket::new(0));

    // -----------------------------------------------------------------------
    // (A) DEPOSIT on chain A — a REAL LC-attested lock (ConsensusProven holding,
    //     mpt_holding_hash binding) mints a shielded note. asset = WETH.
    // -----------------------------------------------------------------------
    let asset = 1u64; // the dregg asset class mirroring WETH
    let lock_a = honest_attestation(asset, 1_000, WETH, 0xA11CE, 0x5107_A, ETH_MAINNET);
    let counter = honest_attestation(asset, 1_000, WETH, 0xB0B, 0x5107_B, ETH_MAINNET);
    assert!(lock_a.is_valid_lock() && counter.is_valid_lock());

    let note_a = h
        .deposit(&mut chain_a, &lock_a, 120, 0xA11CE, 0x5EED_A, 0x7A)
        .expect("valid ConsensusProven lock, value ≤ locked, mints");
    let note_c = h
        .deposit(&mut chain_a, &counter, 100, 0xB0B, 0x5EED_B, 0x7B)
        .expect("valid lock mints the counterparty note");
    let ca = chain_a.custody[&asset];
    flow.record(
        "deposit(A)",
        ca.backed() && ca.locked == 2000 && ca.supply == 220,
        &format!(
            "2 LC-attested locks → shielded notes (values 120,100 hidden); chain-A custody locked {} supply {} (backed)",
            ca.locked, ca.supply
        ),
    );

    // -----------------------------------------------------------------------
    // (B) SHIELDED CLEAR — seal the two deposit notes as a bid+ask, run the REAL
    //     fhEgg engine, mint conserving output notes. The clear is chain-agnostic
    //     (it happens in the shielded layer that spans both chains).
    // -----------------------------------------------------------------------
    let (outputs, vstar, conserves) = h.clear_pair(&note_a, 7, &note_c, 3, 10);
    // note_a bid 120 @ lvl 7, note_c ask 100 @ lvl 3 cross → V* = 100 (ask is short).
    flow.record(
        "shielded clear",
        conserves && vstar == 100,
        &format!("REAL fhEgg clear over deposit notes → V* = {vstar}, Σin = Σout (conserving)"),
    );
    // The output note that will bridge to chain B: the bid's fill (value = V* = 100).
    let bridged = outputs[0].fill_note.clone();
    assert_eq!(bridged.value, 100);

    // -----------------------------------------------------------------------
    // (C) SETTLE on chain B — the bridged output note exits the shielded pool and
    //     releases from chain B's custody. Chain B's custody was seeded with the
    //     mirror backing that arrived cross-chain (the LC attested the lock on A).
    // -----------------------------------------------------------------------
    chain_b.seed_custody(asset, MirrorState::seeded(500, 500));
    let post_b = h
        .settle(&mut chain_b, asset, &bridged)
        .expect("the bridged output note settles on chain B (supply ≤ locked)");
    flow.record(
        "settle(B)",
        post_b.backed() && post_b.supply == 400,
        &format!(
            "bridged note (value 100) unshielded + released on chain B; custody supply {} → {} (backed)",
            500, post_b.supply
        ),
    );

    // -----------------------------------------------------------------------
    // (D) VERIFY on chain B via the OCIP socket — build the settlement statement
    //     (genesis = the trusted dregg instance, final = chain-B post-settle custody
    //     root), prove the wrap, and have chain B's OCIP consumer ACCEPT it: the
    //     cross-chain settlement is verified where chain B lives.
    // -----------------------------------------------------------------------
    let final_root = custody_root_lanes(&post_b);
    let stmt = SettlementStatement {
        genesis_root: DREGG_GENESIS,
        final_root,
        num_turns: 3, // deposit + clear + settle folded
        chain_digest: custody_root_lanes(&chain_a.custody[&asset]),
    };
    let proof = prove_settlement(&stmt);
    let trusts = chain_b
        .trusts
        .as_mut()
        .expect("chain B has the OCIP consumer");
    let accepted = trusts.accept_clearing(&proof, &stmt);
    flow.record(
        "OCIP verify(B)",
        accepted == Ok(final_root) && trusts.is_accepted(&final_root),
        "chain-B OCIP consumer ACCEPTED the dregg attestation (which-dregg ✓ + socket verify ✓)",
    );

    assert!(
        flow.all_ok(),
        "the whole cross-chain flow (deposit A → clear → settle B → OCIP verify) must pass"
    );
    println!(
        "  POSITIVE cross-chain flow: {} stages green",
        flow.stage_count()
    );

    // =======================================================================
    // NEGATIVE polarities — the socket genuinely rejects forged / foreign / ill-formed.
    // =======================================================================
    println!("  --- socket soundness teeth (forged rejected) ---");

    // [neg #1] FORGED / TAMPERED statement — the presented final_root differs from
    // what the proof attests. The pairing (modelled by the binding digest) returns
    // false ⇒ AttestationRejected.
    {
        let mut tampered = stmt.clone();
        tampered.final_root[0] = (tampered.final_root[0] + 1) % multichain::BABYBEAR_P; // still canonical
        let mut victim = chain_b.trusts.as_ref().unwrap().clone();
        let res = victim.accept_clearing(&proof, &tampered);
        assert_eq!(
            res,
            Err(AcceptError::AttestationRejected),
            "a tampered final_root the proof does not attest MUST be rejected"
        );
        println!(
            "  [neg] FORGED statement (tampered final_root) REJECTED — socket verify returned false"
        );
    }

    // [neg #2] FOREIGN dregg instance — a validly-proven statement about a DIFFERENT
    // dregg genesis. Chain B trusts ONE instance; the which-dregg check refuses it
    // BEFORE the pairing.
    {
        let foreign_genesis = [99u32, 98, 97, 96, 95, 94, 93, 92];
        let foreign_stmt = SettlementStatement {
            genesis_root: foreign_genesis,
            final_root,
            num_turns: 3,
            chain_digest: stmt.chain_digest,
        };
        let foreign_proof = prove_settlement(&foreign_stmt); // a REAL proof of the foreign statement
        assert!(
            foreign_proof.attests(&foreign_stmt),
            "the foreign proof genuinely attests its own foreign statement"
        );
        let mut victim = chain_b.trusts.as_ref().unwrap().clone();
        let res = victim.accept_clearing(&foreign_proof, &foreign_stmt);
        assert_eq!(
            res,
            Err(AcceptError::UntrustedDreggInstance),
            "a proof about a FOREIGN dregg instance MUST be refused (which-dregg)"
        );
        println!("  [neg] FOREIGN dregg instance (wrong genesis) REJECTED — before the pairing");
    }

    // [neg #3] ILL-FORMED statement — a non-canonical lane (≥ BabyBear p). The
    // socket's encode reverts (NonCanonicalLane) — distinct from a failed verify.
    {
        let mut illformed = stmt.clone();
        illformed.final_root[0] = multichain::BABYBEAR_P; // ≥ p, non-canonical
        let mut victim = chain_b.trusts.as_ref().unwrap().clone();
        let res = victim.accept_clearing(&proof, &illformed);
        assert!(
            matches!(res, Err(AcceptError::NonCanonical(_))),
            "a non-canonical lane must revert (ill-formed), got {res:?}"
        );
        println!("  [neg] ILL-FORMED statement (non-canonical lane) REVERTED — NonCanonicalLane");
    }

    // [neg #4] SETTLE beyond the destination custody — a note worth more than chain
    // B's mirror supply cannot settle (supply ≤ locked bites).
    {
        let mut chain_thin = Chain::new("thin-L2 (local)", DREGG_GENESIS);
        chain_thin.seed_custody(asset, MirrorState::seeded(50, 50));
        let mut h2 = MultichainHarness::new();
        let big = mint_note(asset, 200, 0xBAD, 0xBAD, 0xBAD);
        h2.pool.insert(big.clone());
        let res = h2.settle(&mut chain_thin, asset, &big);
        assert_eq!(
            res.err(),
            Some(multichain::SettleError::InsufficientLocked),
            "a note worth 200 cannot settle against 50 locked — REFUSED (supply ≤ locked)"
        );
        println!("  [neg] SETTLE-BEYOND-LOCKED on chain B (200 > 50) REJECTED — supply ≤ locked");
    }

    println!(
        "=== CROSS-CHAIN flow closed: deposit(A) → clear → settle(B) → OCIP verify; forged/foreign/ill-formed REJECTED ==="
    );
}

// ===========================================================================
// SHIELDED TRANSFER — note → note (a private payment, no clearing). Both polarities.
// ===========================================================================

#[test]
fn shielded_transfer_note_to_note() {
    let mut flow = multichain::FlowReport::new("SHIELDED TRANSFER — note → note (private payment)");
    let mut h = MultichainHarness::new();

    // A deposited note (value 100) sits in the pool (via a real LC-attested lock).
    let mut chain = Chain::new("local", DREGG_GENESIS);
    let lock = honest_attestation(1, 1_000, WETH, 0x5EED, 0x510, ETH_MAINNET);
    let note = h
        .deposit(&mut chain, &lock, 100, 0x5EED, 0xB11, 0x9A)
        .expect("deposit mints the payment note");

    // POSITIVE: transfer 100 → two output notes (70 to payee, 30 change), conserving.
    let outs = h
        .shielded_transfer(
            &note,
            &[(70, 0xF00, 0xF01, 0xF02), (30, 0xC00, 0xC01, 0xC02)],
        )
        .expect("a conserving note→note transfer must succeed");
    let sum_out: u64 = outs.iter().map(|n| n.value).sum();
    let bound = outs.iter().all(|n| n.value_binding_opens());
    let consumed = h.pool.consumed.contains(&note.nullifier);
    flow.record(
        "transfer 100 → (70 + 30)",
        sum_out == 100 && bound && consumed,
        &format!(
            "Σout = {sum_out} (= Σin), both output notes value-bound, input nullifier consumed"
        ),
    );

    // NEGATIVE #1: an INFLATING transfer (outputs sum > input) is REJECTED (no mint).
    {
        let mut h2 = MultichainHarness::new();
        let mut c2 = Chain::new("local", DREGG_GENESIS);
        let n2 = h2
            .deposit(&mut c2, &lock, 100, 0x5EED, 0xB11, 0x9A)
            .expect("deposit");
        let res =
            h2.shielded_transfer(&n2, &[(70, 0xF00, 0xF01, 0xF02), (50, 0xC00, 0xC01, 0xC02)]);
        assert_eq!(
            res.err(),
            Some(TransferError::NotConserving {
                in_value: 100,
                out_value: 120
            }),
            "an inflating transfer (Σout 120 > Σin 100) MUST be rejected"
        );
        flow.record(
            "inflating transfer (100 → 120)",
            true,
            "REJECTED — Σout ≠ Σin (no value minted across a private payment)",
        );
    }

    // NEGATIVE #2: DOUBLE-SPEND — re-transferring the already-spent input note.
    {
        let res = h.shielded_transfer(&note, &[(100, 0x1, 0x2, 0x3)]);
        assert_eq!(
            res.err(),
            Some(TransferError::Unshield(
                multichain::UnshieldError::NoteNotInPool
            )),
            "the input note already left the pool — a replay finds no live note"
        );
        flow.record(
            "double-spend (replay input)",
            true,
            "REJECTED — the input nullifier was already consumed",
        );
    }

    assert!(flow.all_ok());
    println!("  SHIELDED TRANSFER: conserving payment green; inflation + double-spend REJECTED");
}

// ===========================================================================
// MULTI-ASSET RING — the cross-asset price-carrying clear over shielded notes.
// ===========================================================================

#[test]
fn multi_asset_ring_clears_over_shielded_notes() {
    let mut flow = multichain::FlowReport::new(
        "MULTI-ASSET RING — 3 assets, each leg priced, over shielded notes",
    );

    // Three assets, each with a two-sided shielded book (a leg = a note offering its
    // asset at a price level). The ring is the cross-asset cycle the fhEgg engine
    // clears per book. Mirror of `ShieldedClearing.lean`'s `shielded_ring_clears`.
    const K: usize = 10;
    let legs = vec![
        // asset 1 — bids up to lvl 7, asks from lvl 3 (crosses).
        RingLeg {
            note: mint_note(1, 100, 0x1B0, 0xA01, 0x101),
            side: Side::Bid,
            limit: 7,
        },
        RingLeg {
            note: mint_note(1, 80, 0x1A0, 0xA02, 0x102),
            side: Side::Ask,
            limit: 3,
        },
        // asset 2 — supply-heavy (demand short → V* = 30).
        RingLeg {
            note: mint_note(2, 30, 0x2B0, 0xB01, 0x201),
            side: Side::Bid,
            limit: 8,
        },
        RingLeg {
            note: mint_note(2, 100, 0x2A0, 0xB02, 0x202),
            side: Side::Ask,
            limit: 2,
        },
        // asset 3 — demand-heavy (supply short → V* = 40).
        RingLeg {
            note: mint_note(3, 90, 0x3B0, 0xC01, 0x301),
            side: Side::Bid,
            limit: 9,
        },
        RingLeg {
            note: mint_note(3, 40, 0x3A0, 0xC02, 0x302),
            side: Side::Ask,
            limit: 1,
        },
    ];

    let (outputs, report) = clear_ring(&legs, K);
    for (asset, &(i, o, b, a, v)) in report.per_asset.iter() {
        flow.record(
            &format!("asset {asset} clears"),
            i == o && b == a && b == v,
            &format!("Σin={i} Σout={o} bid_fill={b} ask_fill={a} V*={v} (conserving + crossing)"),
        );
    }
    flow.record(
        "ring conservation",
        report.conserves(),
        "every asset conserves, every note value-bound, all leg nullifiers distinct",
    );
    // Spot-check the short-side V* per asset.
    assert_eq!(
        report.per_asset[&1].4, 80,
        "asset 1: ask (80) short ⇒ V* = 80"
    );
    assert_eq!(
        report.per_asset[&2].4, 30,
        "asset 2: demand (30) short ⇒ V* = 30"
    );
    assert_eq!(
        report.per_asset[&3].4, 40,
        "asset 3: supply (40) short ⇒ V* = 40"
    );
    assert_eq!(outputs.len(), legs.len(), "one fill/change output per leg");
    assert!(flow.all_ok());

    // NEGATIVE #1: an in-ring DOUBLE-SPEND (two legs sharing a nullifier) is caught.
    {
        let dup = legs[0].note.clone();
        let bad_legs = vec![
            RingLeg {
                note: dup.clone(),
                side: Side::Bid,
                limit: 7,
            },
            RingLeg {
                note: dup,
                side: Side::Ask,
                limit: 3,
            }, // same note twice
        ];
        let (_o, bad_report) = clear_ring(&bad_legs, K);
        assert!(
            !bad_report.nullifiers_distinct && !bad_report.conserves(),
            "a ring re-spending one note (shared nullifier) MUST be rejected"
        );
        println!("  [neg] in-ring DOUBLE-SPEND (two legs, one nullifier) REJECTED");
    }

    // NEGATIVE #2: a value-mismatch (tampered) note breaks the ring's binding check.
    {
        let mut tampered = legs[0].note.clone();
        tampered.value += 5; // claim more than the commitment opens to
        assert!(!tampered.value_binding_opens());
        let bad_legs = vec![
            RingLeg {
                note: tampered,
                side: Side::Bid,
                limit: 7,
            },
            RingLeg {
                note: legs[1].note.clone(),
                side: Side::Ask,
                limit: 3,
            },
        ];
        let (_o, bad_report) = clear_ring(&bad_legs, K);
        assert!(!bad_report.all_bound && !bad_report.conserves());
        println!("  [neg] VALUE-MISMATCH note (does not open its commitment) REJECTED");
    }

    println!("  MULTI-ASSET RING: 3 assets clear conserving; double-spend + mismatch REJECTED");
}

// ===========================================================================
// DERIVATIVES — a REAL Price-Cert settled as a shielded note flow. Both polarities.
// ===========================================================================

#[test]
fn derivatives_price_cert_settles_as_shielded_note() {
    let mut flow = multichain::FlowReport::new(
        "DERIVATIVES — Price-Cert (European bond) → shielded note settle",
    );

    // A no-arbitrage market: two Arrow securities (instrument j pays 1 in scenario
    // j), each marked 0.5 (consistent state price π = [0.5, 0.5]). The new product is
    // a bond h = [1,1] (pays 1 in both scenarios). Its certified price = hᵀπ = 1.0.
    let market = Market::from_scenario_major(
        2, // scenarios
        2, // instruments
        &[
            1.0, 0.0, // scenario 0: instrument payoffs
            0.0, 1.0, // scenario 1
        ],
        vec![0.5, 0.5], // marks a
        vec![1.0, 1.0], // new product payoff h (a bond)
        1e-9,           // epsilon
    );

    // POSITIVE: the REAL Price-Cert LP certifies a no-arbitrage price + certificate.
    let outcome = solve_price_cert(&market);
    let price = match &outcome {
        PriceOutcome::Certified(cert) => {
            let rep = cert.check();
            flow.record(
                "Price-Cert (European bond)",
                rep.valid && (cert.primal_price - 1.0).abs() < 1e-6,
                &format!(
                    "REAL fhEgg Price-Cert LP: certified price {:.4}, gap {:.2e}, cert.valid = {}",
                    cert.primal_price, rep.gap, rep.valid
                ),
            );
            cert.primal_price
        }
        PriceOutcome::Arbitrage => panic!("the consistent market must certify a price"),
    };

    // Settle the certified payoff as a shielded note: the price (scaled to an integer
    // unit, ×100) becomes a REAL Poseidon2 note's value, which exits a pool and
    // releases from a derivatives custody — the derivative settles as a note flow.
    let note_value = (price * 100.0).round() as u64; // 100 units
    let asset = 42u64; // the derivatives-pool asset
    let mut h = MultichainHarness::new();
    let deriv_note = mint_note(asset, note_value, 0xDE1, 0xDE2, 0xDE3);
    h.pool.insert(deriv_note.clone());
    let mut deriv_chain = Chain::new("derivatives-pool (local)", DREGG_GENESIS);
    deriv_chain.seed_custody(asset, MirrorState::seeded(1_000, 1_000));
    let post = h
        .settle(&mut deriv_chain, asset, &deriv_note)
        .expect("the certified-price note settles (supply ≤ locked)");
    flow.record(
        "settle Price-Cert as a note",
        post.backed() && post.supply == 1_000 - note_value,
        &format!(
            "certified price {price:.2} → note value {note_value} → settled; custody supply {} → {}",
            1_000, post.supply
        ),
    );

    assert!(flow.all_ok());

    // NEGATIVE #1: an ARBITRAGE (inconsistent) market yields NO certificate — no price
    // to settle. Two identical instruments marked DIFFERENTLY (0.5 vs 0.7) → no π ≥ 0
    // with Hπ = a exists (mirrors `piBad_inconsistent`).
    {
        let bad = Market::from_scenario_major(
            2,
            2,
            &[1.0, 1.0, 1.0, 1.0], // both instruments pay 1 in every scenario (identical)
            vec![0.5, 0.7],        // …but marked differently — inconsistent
            vec![1.0, 0.0],
            1e-9,
        );
        match solve_price_cert(&bad) {
            PriceOutcome::Arbitrage => {
                println!(
                    "  [neg] ARBITRAGE market → NO certificate, NO price to settle (honest negative)"
                );
            }
            PriceOutcome::Certified(_) => panic!("an inconsistent market must NOT certify"),
        }
    }

    // NEGATIVE #2: a TAMPERED derivative note (value does not open its binding) cannot
    // settle — the unshield's value-binding gate fails-closed.
    {
        let mut h2 = MultichainHarness::new();
        let mut c2 = Chain::new("derivatives-pool (local)", DREGG_GENESIS);
        c2.seed_custody(asset, MirrorState::seeded(1_000, 1_000));
        let good = mint_note(asset, 100, 0xDE1, 0xDE2, 0xDE3);
        h2.pool.insert(good.clone());
        let mut tampered = good.clone();
        tampered.value += 7;
        let res = h2.settle(&mut c2, asset, &tampered);
        assert_eq!(
            res.err(),
            Some(multichain::SettleError::Unshield(
                multichain::UnshieldError::NoteNotBound
            )),
            "a tampered derivative note cannot settle — fail-closed"
        );
        println!("  [neg] TAMPERED derivative note (does not open its commitment) REJECTED");
    }

    println!(
        "  DERIVATIVES: Price-Cert certified + settled as a note; arbitrage + tampered REJECTED"
    );
}

// ===========================================================================
// MULTINODE — the n-party (federation) MPC clear, wired to the note-clearing flow.
// ===========================================================================

#[test]
fn multinode_mpc_clearing_agrees_and_no_party_sees_all() {
    let mut flow = multichain::FlowReport::new(
        "MULTINODE — n-party MPC clear (in-process federation sim) agrees with single-party",
    );

    // The same book that a shielded note clearing would settle, split across n = 4
    // federation parties. Each party holds a DISJOINT slice of the order flow; each
    // folds ONLY its own orders into aggregate curves; the curves sum; the crossing
    // is on the sum. (LABEL: in-process decomposition of the REAL fhEgg engine — the
    // cryptographic no-peek summation + n real node processes are ember-gated.)
    const K: usize = 10;
    let book = vec![
        Order {
            side: Side::Bid,
            qty: 100,
            limit: 7,
        },
        Order {
            side: Side::Bid,
            qty: 50,
            limit: 6,
        },
        Order {
            side: Side::Ask,
            qty: 80,
            limit: 3,
        },
        Order {
            side: Side::Ask,
            qty: 40,
            limit: 4,
        },
        Order {
            side: Side::Bid,
            qty: 60,
            limit: 8,
        },
        Order {
            side: Side::Ask,
            qty: 30,
            limit: 2,
        },
        Order {
            side: Side::Ask,
            qty: 20,
            limit: 5,
        },
        Order {
            side: Side::Bid,
            qty: 35,
            limit: 9,
        },
    ];

    let mpc = MpcClearing::new(K)
        .party(vec![book[0], book[1]]) // party 0 sees 2 orders
        .party(vec![book[2], book[3]]) // party 1
        .party(vec![book[4], book[5]]) // party 2
        .party(vec![book[6], book[7]]); // party 3
    let result = mpc.run();
    let reference = mpc.reference(); // the single-party clear over the whole book
    let single = clear(&book, K).cleared_volume;

    flow.record(
        "n-party agreement",
        result.cleared_volume == reference && reference == single,
        &format!(
            "n = {} parties, V* = {} == single-party V* = {single} (the federation computes the same clear)",
            result.n_parties, result.cleared_volume
        ),
    );
    flow.record(
        "no party sees the whole book",
        result.max_party_view < result.total_orders && result.n_parties > 1,
        &format!(
            "largest single-party view = {} of {} orders (each party folds only its own share)",
            result.max_party_view, result.total_orders
        ),
    );

    // The MPC result is exactly the V* that would settle the note clearing: wire it.
    // Seal two notes as the crossing book's extremes and confirm the note-clear V*
    // matches the federation's V* for a matching two-order book.
    {
        let mut h = MultichainHarness::new();
        let mut chain = Chain::new("local", DREGG_GENESIS);
        let lock_bid = honest_attestation(1, 1_000, WETH, 0xB1D, 0x5B, ETH_MAINNET);
        let lock_ask = honest_attestation(1, 1_000, WETH, 0xA5C, 0x5A, BASE_L2);
        let bid = h
            .deposit(&mut chain, &lock_bid, 100, 0xB1D, 0x11, 0x21)
            .unwrap();
        let ask = h
            .deposit(&mut chain, &lock_ask, 80, 0xA5C, 0x12, 0x22)
            .unwrap();
        let (_out, note_vstar, conserves) = h.clear_pair(&bid, 7, &ask, 3, K);
        let mpc2 = MpcClearing::new(K)
            .party(vec![Order {
                side: Side::Bid,
                qty: 100,
                limit: 7,
            }])
            .party(vec![Order {
                side: Side::Ask,
                qty: 80,
                limit: 3,
            }]);
        flow.record(
            "MPC wired into the note clear",
            conserves && note_vstar == mpc2.run().cleared_volume && note_vstar == 80,
            &format!(
                "note-clear V* = {note_vstar} == 2-party MPC V* = {} (the federation clears the shielded notes)",
                mpc2.run().cleared_volume
            ),
        );
    }

    assert!(flow.all_ok());

    // A sanity control: with ONE party (n = 1) the whole book is visible — showing
    // the no-peek property is a real function of the split (n > 1), honestly labelled.
    {
        let solo = MpcClearing::new(K).party(book.clone());
        let r = solo.run();
        assert_eq!(
            r.cleared_volume, single,
            "n=1 also agrees (it is just the single-party clear)"
        );
        assert_eq!(
            r.max_party_view, r.total_orders,
            "with n=1 the sole party sees the whole book — no privacy from the split"
        );
        println!("  [control] n=1: agrees but the sole party sees all — the split is what hides");
    }

    println!(
        "  MULTINODE: n=4 federation MPC == single-party clear; no party sees the whole book (deploy ember-gated)"
    );

    // HONEST LABEL, printed with the flow so the run is self-describing.
}
