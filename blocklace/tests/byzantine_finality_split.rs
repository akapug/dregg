//! LIVE-BYZANTINE Attack 1 forge — an equivocating wave leader CANNOT produce
//! two committee-ratified heads (no finality split).
//!
//! This is the concrete refutation of the audit's headline Attack-1 question:
//! "Can a prover-controlled Byzantine node produce two valid quorum certs for
//! conflicting states?" It builds the exact adversarial DAG — the round-robin
//! wave-0 leader double-signs its leader slot into two conflicting blocks — and
//! asserts the deployed `ordering::tau` finalizes NEITHER conflicting head.
//!
//! Two independent deployed gates close it, both exercised here:
//!   1. `find_all_final_leaders` finalizes a wave leader ONLY when it has exactly
//!      one block at the wave-start round (`leader_blocks.len() == 1`), so a
//!      double-signed leader slot super-ratifies nothing.
//!   2. `supermajority_threshold(n) = 2n/3 + 1` has unconditional quorum
//!      intersection, so even if the two heads were leader-eligible the honest
//!      `2f+1` could not form two disjoint ratifying supermajorities.
//!
//! If either gate were removed (e.g. finalizing the FIRST leader block seen, or a
//! `2n/3` threshold at `3|n`), this test would finalize a creator-`L` head and
//! FAIL — so it bites on the real safety property, not a tautology.
//!
//! See `docs/audit/LIVE-BYZANTINE.md` Attack 1.

use dregg_blocklace::ordering::{supermajority_threshold, tau};
use dregg_blocklace::{Block, BlockId, Blocklace};

fn key(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn block(creator: [u8; 32], seq: u64, preds: Vec<BlockId>, payload: Vec<u8>) -> Block {
    Block::new(creator, seq, preds, payload)
}

/// n=4 (f=1). The wave-0 round-robin leader is `participants[0]` (= creator L).
/// L equivocates at its leader slot: two distinct genesis blocks. The three
/// honest creators build a clean round-synchronous DAG on TOP of both forks (the
/// worst case — both forks are visible and referenced), then `tau` runs.
///
/// SAFETY: neither of L's two conflicting heads is finalized — a Byzantine
/// double-signer cannot split finality into two ratified heads.
#[test]
fn equivocating_leader_cannot_super_ratify_two_heads() {
    let participants: Vec<[u8; 32]> = (0u8..4).map(|i| key(10 + i)).collect();
    let leader = participants[0];
    assert_eq!(
        supermajority_threshold(participants.len()),
        3,
        "n=4 supermajority is 3 (the ratifying quorum this forge must deny to both heads)"
    );

    let mut bl = Blocklace::new();

    // ── Round 1 (wave-0 leader slot): L DOUBLE-SIGNS. ──
    // Two conflicting genesis blocks by the leader, plus one honest genesis each
    // from creators 1..3.
    let l_left = block(leader, 0, vec![], b"LEADER-FORK-LEFT".to_vec());
    let l_right = block(leader, 0, vec![], b"LEADER-FORK-RIGHT".to_vec());
    let l_left_id = l_left.id();
    let l_right_id = l_right.id();
    assert_ne!(
        l_left_id, l_right_id,
        "the two leader forks are distinct blocks"
    );
    bl.insert_unverified(l_left).unwrap();
    bl.insert_unverified(l_right).unwrap();

    let mut r1: Vec<BlockId> = vec![l_left_id, l_right_id];
    for (i, c) in participants.iter().enumerate().skip(1) {
        let b = block(*c, 0, vec![], vec![i as u8]);
        r1.push(b.id());
        bl.insert_unverified(b).unwrap();
    }

    // ── Rounds 2 and 3: the three HONEST creators each produce one block per
    //    round, referencing ALL of the previous round (both leader forks
    //    included — the honest nodes observe L's equivocation). ──
    let mut prev = r1;
    for round in 1u64..=2 {
        let mut this = Vec::new();
        for (i, c) in participants.iter().enumerate().skip(1) {
            let b = block(*c, round, prev.clone(), vec![(round * 10) as u8 + i as u8]);
            this.push(b.id());
            bl.insert_unverified(b).unwrap();
        }
        prev = this;
    }

    let order = tau(&bl, &participants);

    // THE SAFETY ASSERTION: neither conflicting leader head is finalized.
    assert!(
        !order.contains(&l_left_id),
        "SPLIT-FINALITY: the equivocating leader's LEFT fork was finalized — a Byzantine \
         double-signer produced a ratified head"
    );
    assert!(
        !order.contains(&l_right_id),
        "SPLIT-FINALITY: the equivocating leader's RIGHT fork was finalized — a Byzantine \
         double-signer produced a ratified head"
    );

    // Stronger: NO block by the equivocating leader is finalized at all (the whole
    // creator is excluded, matching the eviction path).
    for id in &order {
        let b = bl.get(id).expect("finalized id present");
        assert_ne!(
            b.creator, leader,
            "the equivocating leader contributed a finalized block — exclusion failed"
        );
    }
}

/// Determinism companion: every honest node computing `tau` over the SAME lace
/// reaches the SAME (leaderless) verdict — there is not even a transient window
/// where two honest nodes disagree on whether a leader head finalized. (Two `tau`
/// runs over the identical lace must be byte-identical.)
#[test]
fn equivocated_wave_is_deterministically_leaderless_across_nodes() {
    let participants: Vec<[u8; 32]> = (0u8..4).map(|i| key(10 + i)).collect();
    let leader = participants[0];
    let mut bl = Blocklace::new();

    let l_a = block(leader, 0, vec![], b"A".to_vec());
    let l_b = block(leader, 0, vec![], b"B".to_vec());
    let (l_a_id, l_b_id) = (l_a.id(), l_b.id());
    bl.insert_unverified(l_a).unwrap();
    bl.insert_unverified(l_b).unwrap();
    let mut r1 = vec![l_a_id, l_b_id];
    for (i, c) in participants.iter().enumerate().skip(1) {
        let b = block(*c, 0, vec![], vec![i as u8]);
        r1.push(b.id());
        bl.insert_unverified(b).unwrap();
    }
    let mut prev = r1;
    for round in 1u64..=2 {
        let mut this = Vec::new();
        for (i, c) in participants.iter().enumerate().skip(1) {
            let b = block(*c, round, prev.clone(), vec![(round * 10) as u8 + i as u8]);
            this.push(b.id());
            bl.insert_unverified(b).unwrap();
        }
        prev = this;
    }

    // Five independent evaluations (modelling five nodes over the same converged
    // lace) all agree, and none finalizes a leader-fork head.
    let base = tau(&bl, &participants);
    for _ in 0..5 {
        assert_eq!(
            tau(&bl, &participants),
            base,
            "tau must be deterministic across nodes"
        );
    }
    assert!(!base.contains(&l_a_id) && !base.contains(&l_b_id));
}
