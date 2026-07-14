//! FAST: a PLAYED match of each game lowers to the foldable leaves the fold consumes — and
//! the game's own teeth bite at lowering (a fabricated / replayed card has no leaf; a board
//! transition that is not the automaton step has no honest D1 witness). No proving here.

use dregg_automatafl::reference::{ATT, AUTO, Board, VAC, automaton_step};
use dregg_circuit::field::BabyBear;
use dregg_multiway_tug::hidden_hand::{HandTree, card_leaf};
use dreggnet_game_board::{AutomataflMatch, MatchError, TugMatch, TugWin};

fn hand() -> Vec<(u64, u64)> {
    vec![
        (0, 1001),
        (1, 1002),
        (3, 1003),
        (7, 1004),
        (12, 1005),
        (18, 1006),
    ]
}

/// The driven 5x5 board (the same demo the automatafl crate's own prove/fold gate uses):
/// attractor two north of the automaton.
fn demo_board() -> Board {
    let n = 5usize;
    let mut cells = vec![VAC; n * n];
    cells[4 * n + 2] = ATT;
    cells[2 * n + 2] = AUTO;
    Board {
        n,
        cells,
        auto: (2, 2),
        col_rule: true,
    }
}

/// A PLAYED tug match lowers to one membership leaf per play — public inputs `[blinded_leaf,
/// hand_root]`, the CARD IDS ABSENT — plus the terminal win leaf binding `[charm, winner]`.
/// This is the hand-never-revealed property, at the leaf boundary.
#[test]
fn a_played_tug_match_lowers_to_hand_hiding_membership_leaves() {
    let m = TugMatch {
        hand: hand(),
        plays: vec![0, 3, 12],
        win: Some(TugWin {
            charm: 13,
            winner: 1,
        }),
    };
    let leaves = m.leaves().expect("the played match lowers");
    assert_eq!(leaves.len(), 4, "3 plays + the terminal win turn");

    // Each play's leaf proves membership under the CURRENT remaining-hand root.
    let mut tree = HandTree::commit(m.hand.clone());
    for (i, &card) in m.plays.iter().enumerate() {
        let nonce = tree.opening(card).expect("dealt").1;
        let root = leaves[i].public_inputs[1];
        assert_eq!(
            leaves[i].public_inputs,
            vec![card_leaf(card, nonce), root],
            "PIs are [blinded_leaf, hand_root]"
        );
        assert!(
            !leaves[i].public_inputs.contains(&BabyBear::from_u64(card)),
            "the played card id is NOT in the leaf's public inputs — the hand is hidden"
        );
        tree = tree.without(card);
    }
    // Successive plays prove under DIFFERENT roots (the hand shrinks) — no replay is possible.
    assert_ne!(
        leaves[0].public_inputs[1], leaves[1].public_inputs[1],
        "each play proves against the updated remaining-hand root"
    );
    // The win leaf binds [charm, winner] as its public output.
    assert_eq!(
        leaves[3].public_inputs,
        vec![BabyBear::from_u64(13), BabyBear::from_u64(1)],
        "the terminal leaf binds the WIN as a public output"
    );
}

/// The hidden-hand tooth bites at lowering: a card never dealt, and a card played twice, have
/// NO membership leaf — the match does not lower, so it can never be folded or submitted.
#[test]
fn a_fabricated_or_replayed_card_has_no_leaf() {
    let fabricated = TugMatch {
        hand: hand(),
        plays: vec![0, 20], // 20 was never dealt
        win: None,
    };
    assert!(matches!(
        fabricated.leaves().err(),
        Some(MatchError::NotInHand(20))
    ));

    let double = TugMatch {
        hand: hand(),
        plays: vec![0, 0], // the same card twice
        win: None,
    };
    assert!(
        matches!(double.leaves().err(), Some(MatchError::NotInHand(0))),
        "a played card is no longer under the remaining-hand root"
    );

    assert!(matches!(
        TugMatch {
            hand: hand(),
            plays: vec![],
            win: None
        }
        .leaves()
        .err(),
        Some(MatchError::Empty)
    ));
}

/// A PLAYED automatafl match lowers to one committed D1 leaf per turn, each proving
/// `boards[i+1] == automaton_step(boards[i])`; the boards themselves are never in the proof's
/// public inputs as *moves* — only the transition is attested.
#[test]
fn a_played_automatafl_match_lowers_to_d1_leaves() {
    let m = AutomataflMatch {
        start: demo_board(),
        turns: 2,
    };
    let boards = m.boards();
    assert_eq!(boards.len(), 3, "start + 2 stepped boards");
    assert_eq!(
        boards[1],
        automaton_step(&boards[0]),
        "the played boards ARE the automaton's steps"
    );
    assert_ne!(boards[1], boards[0], "the automaton actually moved");

    let leaves = m.leaves().expect("the played match lowers to D1 leaves");
    assert_eq!(leaves.len(), 2, "one D1 leaf per turn");
    for l in &leaves {
        assert!(l.num_rows > 0);
        assert!(
            !l.program.descriptor.constraints.is_empty(),
            "the D1 AIR carries real constraints"
        );
    }

    assert!(matches!(
        AutomataflMatch {
            start: demo_board(),
            turns: 0
        }
        .leaves()
        .err(),
        Some(MatchError::Empty)
    ));
}
