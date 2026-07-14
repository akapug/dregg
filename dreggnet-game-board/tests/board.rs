//! FAST: the games' proof-carrying board — it ACCEPTS a real fold proof in O(1), RANKS it
//! **storing NO moves**, REFUSES a forged proof, and its per-game [`ProofAnchor`] binds the
//! VK + genesis + WIN root (a proof for a different game/universe is refused). Plus the ASYNC
//! shape (play → enqueue → prove off-thread → submit the proof).
//!
//! No proving happens here (the fold is minutes-to-hours; that is the `--ignored` end-to-end
//! lane). The proof driven is a REAL folded artifact — see `support::real_proof`.

mod support;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, WholeChainProofBytes};
use dregg_lightclient::verify_history_bytes;
use dreggnet_game_board::{
    Game, GameBoard, JobStatus, MatchProof, ProofAnchor, ProvingService, RejectReason, SubmitError,
    match_anchor,
};

use support::{hex32, real_proof};

/// Build the shippable `MatchProof` a player's prover would have produced for `game` from a
/// real folded artifact (the fold itself is the slow lane's job).
fn shipped(game: Game) -> MatchProof {
    let p = real_proof(game);
    let attested = verify_history_bytes(&p.bytes, &p.vk)
        .expect("the fixture must be a REAL proof the light client accepts");
    eprintln!(
        "[{}] proof source: {} | vk={} | turns={}",
        game.slug(),
        p.source,
        hex32(&p.vk.0),
        attested.num_turns
    );
    MatchProof {
        game,
        proof_bytes: p.bytes,
        attested,
        vk: p.vk,
    }
}

fn bump(mut a: [BabyBear; 8]) -> [BabyBear; 8] {
    a[0] = a[0] + BabyBear::ONE;
    a
}

/// THE PRIVATE-STRATEGY LEADERBOARD: for BOTH games, a match's fold proof is accepted by the
/// proof-carrying board in O(1), RANKED, and the entry stores **no moves** — the tug hand is
/// never revealed, the automatafl moves are never posted.
#[test]
fn board_accepts_and_ranks_a_game_fold_with_no_moves_stored() {
    for game in [Game::MultiwayTug, Game::Automatafl] {
        let proof = shipped(game);
        let mut board = GameBoard::new();
        board.open(game, match_anchor(&proof));

        let accepted = board
            .submit(game, "ada", &proof)
            .expect("the board must ACCEPT the honest game fold proof");
        assert_eq!(accepted.rank, 1, "the sole entry ranks first");
        assert_eq!(accepted.turns, proof.turns());

        let lb = board.leaderboard(game);
        assert_eq!(lb.len(), 1, "the entry is on the board");
        let e = lb[0];
        assert!(e.is_proof_backed(), "the ranked entry is proof-backed");
        assert!(!e.has_moves(), "THE PRIVACY: the entry stores NO moves");
        assert!(
            e.playthrough().is_none(),
            "no playthrough is recoverable — the hand/moves were never posted"
        );
        assert!(e.proof_bytes().is_some(), "the proof envelope IS stored");
        assert_eq!(
            e.attested().expect("attested publics").num_turns,
            proof.turns()
        );
        assert!(
            board.stores_no_moves(game),
            "every ranked entry on {game} stores no moves"
        );

        // Independent re-verification re-runs the O(1) light client, never a replay.
        let t = board
            .reverify(game, &accepted.completion_id)
            .expect("a proof entry re-verifies via the O(1) light client");
        assert_eq!(t, proof.turns());

        eprintln!(
            "{game}: ACCEPTED + RANKED #{} in O(1) ({} turns attested) — 0 moves stored.",
            accepted.rank,
            proof.turns()
        );
    }
}

/// NON-VACUOUS FORGERY: the honest proof is accepted first; a relabeled final root (a forged
/// "I reached the win state" claim) is REJECTED by `verify_history_bytes` and adds nothing.
#[test]
fn a_forged_proof_is_rejected_by_the_light_client() {
    let game = Game::MultiwayTug;
    let proof = shipped(game);
    let mut board = GameBoard::new();
    board.open(game, match_anchor(&proof));

    let ok = board
        .submit(game, "ada", &proof)
        .expect("the honest proof is accepted (non-vacuity)");
    assert_eq!(ok.rank, 1);

    // Relabel the carried final root inside the wire envelope — the exact forgery a cheater
    // would attempt (claim a different, winning end state for a match they did not win).
    let mut env =
        WholeChainProofBytes::from_postcard(&proof.proof_bytes).expect("envelope decodes");
    env.final_root[0] = env.final_root[0].wrapping_add(1);
    let verdict = board.submit_bytes(game, "mallory", env.to_postcard(), proof.turns());
    assert!(
        matches!(
            verdict,
            Err(SubmitError::Refused(RejectReason::ProofRejected(_)))
        ),
        "a relabeled root must be REJECTED by the light client; got {verdict:?}"
    );

    // A relabeled GENESIS root is likewise refused.
    let mut env2 =
        WholeChainProofBytes::from_postcard(&proof.proof_bytes).expect("envelope decodes");
    env2.genesis_root[0] = env2.genesis_root[0].wrapping_add(1);
    let v2 = board.submit_bytes(game, "mallory", env2.to_postcard(), proof.turns());
    assert!(
        matches!(
            v2,
            Err(SubmitError::Refused(RejectReason::ProofRejected(_)))
        ),
        "a relabeled genesis must be REJECTED; got {v2:?}"
    );

    // Garbage bytes are refused too (the decode/verify tooth, not a panic).
    let v3 = board.submit_bytes(game, "mallory", vec![0xAB; 64], proof.turns());
    assert!(
        matches!(v3, Err(SubmitError::Refused(_))),
        "a malformed envelope must be refused; got {v3:?}"
    );

    assert_eq!(
        board.leaderboard(game).len(),
        1,
        "no forged submission reached the board"
    );
    eprintln!("{game}: forged proofs (relabeled final / genesis / garbage) all REJECTED.");
}

/// THE ANCHOR BINDS THE GAME: the board pins (vk, genesis, WIN). A proof under a different VK
/// is refused; a proof that does not start at the pinned genesis is refused; a proof that does
/// not END at the pinned WIN root is refused; a lied turn count is refused. So a valid proof
/// for a DIFFERENT game/universe cannot rank here.
#[test]
fn the_anchor_binds_vk_genesis_and_the_win_root() {
    let proof = shipped(Game::MultiwayTug);
    let att = &proof.attested;

    // ── wrong VK: the board's trust anchor is not this proof's circuit. ──
    let mut b = GameBoard::new();
    b.open(
        Game::MultiwayTug,
        ProofAnchor::new(RecursionVk([0xAA; 32]), att.genesis_root, att.final_root),
    );
    let v = b.submit(Game::MultiwayTug, "ada", &proof);
    assert!(
        matches!(v, Err(SubmitError::Refused(RejectReason::ProofRejected(_)))),
        "a proof under a foreign VK must be refused; got {v:?}"
    );

    // ── wrong WIN root: an honest proof that does not reach the declared win state. ──
    let mut b = GameBoard::new();
    b.open(
        Game::MultiwayTug,
        ProofAnchor::new(proof.vk, att.genesis_root, bump(att.final_root)),
    );
    let v = b.submit(Game::MultiwayTug, "ada", &proof);
    assert!(
        matches!(v, Err(SubmitError::Refused(RejectReason::WinNotProven))),
        "a proof not reaching the pinned WIN root must be refused; got {v:?}"
    );

    // ── wrong GENESIS: the proof attests a different universe's history. ──
    let mut b = GameBoard::new();
    b.open(
        Game::MultiwayTug,
        ProofAnchor::new(proof.vk, bump(att.genesis_root), att.final_root),
    );
    let v = b.submit(Game::MultiwayTug, "ada", &proof);
    assert!(
        matches!(v, Err(SubmitError::Refused(RejectReason::GenesisMismatch))),
        "a proof from a different genesis must be refused; got {v:?}"
    );

    // ── a lied turn count on an otherwise-honest proof. ──
    let mut b = GameBoard::new();
    b.open(Game::MultiwayTug, match_anchor(&proof));
    let v = b.submit_bytes(
        Game::MultiwayTug,
        "ada",
        proof.proof_bytes.clone(),
        proof.turns() + 1,
    );
    assert!(
        matches!(
            v,
            Err(SubmitError::Refused(RejectReason::ResultMismatch { .. }))
        ),
        "a lied turn count must be refused; got {v:?}"
    );

    eprintln!("anchor binding: vk / genesis / WIN root / claimed-turns all BITE.");
}

/// A PROOF FOR A DIFFERENT GAME IS REFUSED: the two games' boards pin different anchors, so a
/// multiway-tug match proof submitted to the automatafl board does not rank — even though it is
/// a perfectly valid proof (it verifies under its own board).
#[test]
fn a_proof_for_another_game_does_not_rank() {
    let tug = shipped(Game::MultiwayTug);
    let afl = shipped(Game::Automatafl);

    let mut board = GameBoard::new();
    board.open(Game::MultiwayTug, match_anchor(&tug));

    // The automatafl board's anchor. Once both games' folds are baked these differ genuinely
    // (different genesis/win endpoints); if this machine has not baked them, we pin an anchor
    // that is EXPLICITLY a different universe's (bumped genesis + win) so the cross-game
    // refusal is never vacuous.
    let afl_anchor = if afl.attested.genesis_root == tug.attested.genesis_root
        && afl.attested.final_root == tug.attested.final_root
    {
        eprintln!(
            "(automatafl fold not baked here — pinning a DISTINCT anchor so the cross-game \
             refusal stays non-vacuous)"
        );
        ProofAnchor::new(
            afl.vk,
            bump(afl.attested.genesis_root),
            bump(afl.attested.final_root),
        )
    } else {
        match_anchor(&afl)
    };
    board.open(Game::Automatafl, afl_anchor);

    // The tug proof ranks on ITS OWN board (non-vacuity: the proof is genuinely valid).
    let ok = board
        .submit(Game::MultiwayTug, "ada", &tug)
        .expect("the tug proof ranks on the tug board");
    assert_eq!(ok.rank, 1);

    // The SAME proof, submitted to the automatafl board, is REFUSED — the anchor binds.
    let v = board.submit(Game::Automatafl, "ada", &tug);
    assert!(
        matches!(
            v,
            Err(SubmitError::Refused(
                RejectReason::GenesisMismatch | RejectReason::WinNotProven
            ))
        ),
        "a valid proof for ANOTHER game must not rank here; got {v:?}"
    );
    assert!(
        board.leaderboard(Game::Automatafl).is_empty(),
        "the automatafl board took nothing"
    );

    // No board open at all: nothing to submit to.
    let mut empty = GameBoard::new();
    assert!(matches!(
        empty.submit(Game::Automatafl, "ada", &afl),
        Err(SubmitError::NoBoard(Game::Automatafl))
    ));

    eprintln!("cross-game: a valid tug proof is REFUSED by the automatafl board (anchor binds).");
}

/// THE ASYNC SHAPE: play (fast) → enqueue → the fold runs on a BACKGROUND worker → the finished
/// proof is submitted → the board verifies it in O(1) and ranks it. The board is never blocked
/// on the fold and never sees a move. (The fold itself is stubbed here by a canned prover that
/// returns a REAL proof — the slow lane drives the real fold through this same service.)
#[test]
fn play_prove_submit_is_asynchronous() {
    let game = Game::MultiwayTug;
    let proof = shipped(game);
    let mut board = GameBoard::new();
    board.open(game, match_anchor(&proof));

    // A prover backend that blocks until released — so we can OBSERVE the job in flight while
    // the (already finished) play sits on the player's side.
    let gate = std::sync::Arc::new((std::sync::Mutex::new(false), std::sync::Condvar::new()));
    let gate_w = std::sync::Arc::clone(&gate);
    let canned = proof.clone();
    let service = ProvingService::spawn(std::sync::Arc::new(move |g: Game, _leaves| {
        let (m, cv) = &*gate_w;
        let mut open = m.lock().unwrap();
        while !*open {
            open = cv.wait(open).unwrap();
        }
        let mut p = canned.clone();
        p.game = g;
        Ok(p)
    }));

    // PLAY is over; the match is enqueued and the player's client returns IMMEDIATELY.
    let leaves = dreggnet_game_board::TugMatch {
        hand: vec![(0, 1001), (1, 1002), (3, 1003)],
        plays: vec![0, 1],
        win: None,
    }
    .leaves()
    .expect("the played match lowers to membership leaves");
    let job = service.enqueue(game, leaves);
    let st = service.status(job);
    assert!(
        !st.is_settled(),
        "the fold is still running in the background; got {st:?}"
    );
    assert!(
        board.leaderboard(game).is_empty(),
        "nothing is on the board until the proof exists"
    );

    // The fold finishes (in production: minutes-to-hours later).
    {
        let (m, cv) = &*gate;
        *m.lock().unwrap() = true;
        cv.notify_all();
    }
    let accepted = service
        .submit_when_ready(&mut board, game, "ada", job)
        .expect("the finished proof is submitted and the board accepts it in O(1)");
    assert_eq!(accepted.rank, 1);
    assert!(matches!(service.status(job), JobStatus::Ready(_)));
    assert!(
        board.stores_no_moves(game),
        "the asynchronously-submitted entry stores NO moves"
    );

    // A prover that FAILS (a forged match has no satisfying leaf → no root) surfaces as a
    // proving failure and nothing reaches the board.
    let failing = ProvingService::spawn(std::sync::Arc::new(|_g, _l| {
        Err("match fold failed: unsatisfiable leaf".to_string())
    }));
    let bad = failing.enqueue(game, Vec::new());
    let v = failing.submit_when_ready(&mut board, game, "mallory", bad);
    assert!(
        matches!(v, Err(SubmitError::Proving(_))),
        "a failed fold must not reach the board; got {v:?}"
    );
    assert_eq!(board.leaderboard(game).len(), 1, "the board is unchanged");

    eprintln!("ASYNC: play → enqueue → background fold → submit → O(1) accept + rank.");
}
