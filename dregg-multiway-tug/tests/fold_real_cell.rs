//! **THE FOLD FOLDS OVER THE REAL WORLDCELL CELL** — not a `pk[0]=7` fixture.
//!
//! The mannequin this closes: the Phase-3 fold minted every leg over a synthetic
//! `producer_cell` (pk[0]=7, balance 1000, identical for every match), so a game's published
//! win root was a genuine commitment but was NOT welded to the actual cell's heap state. Here
//! the terminal win folds over the game's OWN committed cell (`WorldCell::cell_snapshot`),
//! carrying its real pk / balance / heap — the winner it publishes is a register the cell's
//! v9 commitment (`old8`/`new8`, the deployed state-binding prefix) actually commits.
//!
//! The FAST battery drives the weld without a STARK: the real cell's commitment differs from
//! the fixture's, moves with the committed winner, and the win leaf's public-input commitment
//! moves when its `[old8 ‖ new8]` prefix is the real cell's vs the fixture's. The SLOW
//! `#[ignore]` fold mints the deployed recursion artifact and `verify_history` accepts it.
//!
//! The winner weld itself is DEPLOYED at the WorldCell executor: `tests/round.rs`'s
//! `false_win_claim_is_refused` shows a false winner (meeting neither threshold) is refused at
//! the `score` admission by the installed `winner==p ⇒ charm_p>=11 OR guilds_p>=4` implication
//! — so a fold never receives a cell whose committed winner did not win.

use dregg_cell::program::field_from_u64;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_multiway_tug::fold::{cell_wire_commit8, fixture_wire_commit8, win_leaf_bound};
use dregg_multiway_tug::game::MultiwayTug;
use dregg_multiway_tug::reference::Engine;

/// Play a full round on the real executor to a winner whose CHARM crossed the threshold
/// (`>= 11`), returning the deployed game + `(charm, winner)`. The win was committed via the
/// real `score` turn, so the installed win implication already gated it.
fn winning_game() -> (MultiwayTug, u64, u64) {
    let seed = (0u8..=255)
        .find(|&s| {
            let mut e = Engine::new(s as u64);
            while !e.round_complete() {
                e.play_next();
            }
            if e.score().is_some() {
                let p = e.projection();
                p.winner != 0 && p.charm[(p.winner - 1) as usize] >= 11
            } else {
                false
            }
        })
        .expect("a seed yields a winner over the charm threshold");

    let mut eng = Engine::new(seed as u64);
    let game = MultiwayTug::deploy(seed).expect("deploy");
    game.seed(&eng.projection()).expect("genesis seeds");
    while !eng.round_complete() {
        let mv = eng.play_next();
        let proj = eng.projection();
        game.commit_projection(mv.action().method(), &proj)
            .expect("legal play commits");
    }
    let _ = eng.score();
    let scored = eng.projection();
    game.commit_score(&scored).expect("scoring commits");
    let winner = scored.winner;
    let charm = scored.charm[(winner - 1) as usize];
    assert!(
        charm >= 11,
        "the folded winner really crossed the threshold"
    );
    (game, charm, winner)
}

/// The fold's cell is the REAL WorldCell cell — its balance and v9 commitment are NOT the
/// `pk[0]=7`, balance-1000 fixture's.
#[test]
fn folds_over_the_real_cell_not_the_fixture() {
    let (game, _charm, _winner) = winning_game();
    let real = game.world().cell_snapshot().expect("the world-cell exists");

    assert_ne!(
        real.state.balance(),
        1000,
        "the real world-cell balance is not the fixture's 1000"
    );
    let real_commit = cell_wire_commit8(&real);
    assert_ne!(
        real_commit,
        fixture_wire_commit8(),
        "the real cell's v9 commitment must differ from the pk[0]=7 fixture's — the fold no \
         longer folds over a synthetic cell"
    );
}

/// The real cell's commitment REFLECTS the committed winner: overwrite the `winner` register on
/// a clone and the v9 commitment moves. So `old8/new8` (welded to the leg by the deployed
/// state-binding node) genuinely carry the winner the game recorded.
#[test]
fn the_cell_commitment_reflects_the_committed_winner() {
    let (game, _charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let base = cell_wire_commit8(&real);

    let mut tampered = real.clone();
    let winner_key = game.dep().reg("winner") as u64;
    let other = if winner == 1 { 2 } else { 1 };
    tampered
        .state
        .set_field_ext(winner_key, field_from_u64(other));
    let moved = cell_wire_commit8(&tampered);

    assert_ne!(
        base, moved,
        "changing the committed winner must move the cell's v9 commitment — the winner is IN \
         the state old8/new8 commit"
    );
}

/// The win leaf publishes `[old8 ‖ new8 ‖ charm ‖ winner]`, and its public-input commitment
/// (the value the fold binds) MOVES when the `[old8 ‖ new8]` prefix is the real cell's vs the
/// fixture's. This replaces the vacuous `win_output_binds_the_winner` (which only asserted
/// Poseidon2 is injective): the win output is welded to the CELL, not free.
#[test]
fn the_win_leaf_is_welded_to_the_cell_prefix() {
    let (game, charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let real8 = cell_wire_commit8(&real);
    let new8: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(1_000 + i as u32));

    let leaf = win_leaf_bound(real8, new8, charm, winner);
    assert_eq!(
        leaf.public_inputs.len(),
        18,
        "[old8 ‖ new8 ‖ charm ‖ winner]"
    );
    assert_eq!(
        &leaf.public_inputs[0..8],
        &real8,
        "PI[0..8] = the real cell old8"
    );
    assert_eq!(&leaf.public_inputs[8..16], &new8, "PI[8..16] = new8");
    assert_eq!(
        leaf.public_inputs[16],
        BabyBear::from_u64(charm),
        "PI[16] = the bound charm"
    );
    assert_eq!(
        leaf.public_inputs[17],
        BabyBear::from_u64(winner),
        "PI[17] = the bound winner"
    );

    // The SAME win, but with the fixture's roots as the prefix, commits differently — so a
    // sub-proof cannot claim the real cell's win while carrying a fixture transition.
    let fixture_leaf = win_leaf_bound(fixture_wire_commit8(), new8, charm, winner);
    assert_ne!(
        custom_proof_pi_commitment(&leaf.public_inputs),
        custom_proof_pi_commitment(&fixture_leaf.public_inputs),
        "the win leaf's bound commitment must move when its state prefix is the real cell's vs \
         the fixture's — the win is welded to the cell"
    );
}

/// SLOW: the terminal win folds over the REAL cell through the deployed recursion fold, and the
/// pure light client accepts it; a spliced final_root is rejected.
#[test]
#[ignore = "SLOW: deployed custom-binding recursion fold over the real WorldCell win transition (~minutes)"]
fn win_folds_over_the_real_cell_and_lightclient_accepts() {
    use dregg_lightclient::verify_history;

    let (game, charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");

    let mut whole = dregg_multiway_tug::fold::fold_win_over_cell(&real, charm, winner)
        .expect("the real-cell win folds to one proof");
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk)
        .expect("the light client ACCEPTS the honest real-cell win fold");
    assert_eq!(attested.num_turns, 2, "the win turn + the linking tail");
    eprintln!(
        "MULTIWAY-TUG REAL-CELL WIN: folded over the WorldCell's own cell; verify_history OK, \
         num_turns={}, winner={winner}, charm={charm}.",
        attested.num_turns
    );

    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED"
    );
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored real-cell win fold verifies again");
}
