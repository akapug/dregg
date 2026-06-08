//! DEEP adversarial tests against the blocklace insert / equivocation detector.
//!
//! These go past the first-pass `blocklace_attacks.rs` (sig forgery, self-fork,
//! malleability, replay) and probe the *structural* claims of the equivocation
//! detector and the trust seams the code documents but does not enforce. Each
//! test maps to a precise Lean claim in `Dregg2/Authority/Blocklace.lean`
//! (Def 4.2 Equivocation = incomparability under `≺`; `observer_detects`).
//!
//! Adversary models:
//!  - a Byzantine *creator* who forks at DIFFERENT seq numbers (the spec says
//!    these forks ARE caught — the content-independent incomparability test, not
//!    the old same-seq heuristic — so we verify the RUNNING code keeps that),
//!  - an adversary exploiting *reception ordering* (does detection depend on the
//!    order blocks arrive? a sound detector must catch the fork regardless),
//!  - a Byzantine creator who forks inside a single `merge` *delta*,
//!  - an attacker supplying an *untrusted checkpoint* (the code documents that
//!    `from_checkpoint` does NOT re-verify signatures — we demonstrate the
//!    forged-block injection that this enables, as a precise FINDING).

use dregg_blocklace::finality::{
    Block, BlockError, Blocklace, BlockId, CheckpointData, MembershipAction, Payload,
};
use ed25519_dalek::ed25519::signature::Signer as _;
use ed25519_dalek::SigningKey as DalekKey;

fn dalek_key(seed: u8) -> DalekKey {
    DalekKey::from_bytes(&[seed; 32])
}

/// Mirror of `finality.rs::signing_content` for the payloads used here, so we
/// can hand-forge a block (creator says X, signed by Y) byte-for-byte.
fn signing_content(creator: &[u8; 32], seq: u64, payload: &Payload, preds: &[BlockId]) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(b"dregg-blocklace-v1");
    buf.extend_from_slice(creator);
    buf.extend_from_slice(&seq.to_le_bytes());
    let payload_bytes = match payload {
        Payload::Ack => vec![0x02u8],
        Payload::Data(d) => {
            let mut v = vec![0x05u8];
            v.extend_from_slice(&(d.len() as u32).to_le_bytes());
            v.extend_from_slice(d);
            v
        }
        _ => panic!("only Ack/Data used in this harness"),
    };
    let h = blake3::hash(&payload_bytes);
    buf.extend_from_slice(h.as_bytes());
    for p in preds {
        buf.extend_from_slice(&p.0);
    }
    buf
}

// ===========================================================================
// DEEP ATTACK 1 — DIFFERENT-SEQ fork (the content-independent claim).
//
// The old `(creator, seq, id≠)` heuristic would MISS a fork where the two arms
// carry different seq numbers. The Lean spec and the current Rust claim to use
// incomparability, which catches it. We build a creator who:
//   b0  (seq 0)
//   ├── armA (seq 1, payload AA)   ── two children of b0 that do NOT reference
//   └── armB (seq 2, payload BB)      each other ⇒ incomparable ⇒ equivocation,
//                                      EVEN THOUGH their seqs differ (1 vs 2).
// A sound detector MUST flag armB. If it does not, the seq-heuristic regressed
// and different-seq forks slip through (a real double-spend vector).
// ===========================================================================

#[test]
fn deep_different_seq_fork_is_detected() {
    let me = dalek_key(11);
    let mut lace = Blocklace::new_simple(me.clone());

    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("b0 ok");

    // Two children of b0 at DIFFERENT seqs, neither referencing the other.
    let arm_a = Block::new(&me, 1, Payload::Data(vec![0xAA]), vec![b0.id()]);
    let arm_b = Block::new(&me, 2, Payload::Data(vec![0xBB]), vec![b0.id()]);

    lace.receive_block(arm_a).expect("armA accepted (first arm)");
    let r = lace.receive_block(arm_b);

    match r {
        Err(BlockError::Equivocation { creator, .. }) => {
            assert_eq!(creator, me.verifying_key().to_bytes());
        }
        other => panic!(
            "FINDING: different-seq fork NOT detected (seq heuristic regressed): {other:?}"
        ),
    }
    assert!(
        lace.is_equivocator(&me.verifying_key().to_bytes()),
        "FINDING: creator not flagged for a genuine different-seq fork"
    );
    eprintln!("[BL DEEP 1] different-seq fork: DEFENDED (incomparability catches it)");
}

// ===========================================================================
// DEEP ATTACK 2 — RECEPTION-ORDER independence.
//
// A sound equivocation detector must catch the fork regardless of which arm
// arrives first. We run the SAME fork in BOTH arrival orders and assert the
// creator ends up flagged either way. If detection were order-dependent (e.g.
// the second arm "buries" the first because some buried block escaped the
// O(blocks) scan), an adversary would pick the order that evades detection.
// ===========================================================================

#[test]
fn deep_fork_detection_is_reception_order_independent() {
    for (first, second) in [(0xAAu8, 0xBBu8), (0xBBu8, 0xAAu8)] {
        let me = dalek_key(12);
        let mut lace = Blocklace::new_simple(me.clone());
        let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
        lace.receive_block(b0.clone()).expect("b0 ok");

        let arm1 = Block::new(&me, 1, Payload::Data(vec![first]), vec![b0.id()]);
        let arm2 = Block::new(&me, 1, Payload::Data(vec![second]), vec![b0.id()]);

        lace.receive_block(arm1).expect("first arm accepted");
        let r = lace.receive_block(arm2);
        assert!(
            matches!(r, Err(BlockError::Equivocation { .. })),
            "FINDING: fork escaped detection in arrival order ({first:#x} then {second:#x})"
        );
        assert!(
            lace.is_equivocator(&me.verifying_key().to_bytes()),
            "FINDING: creator unflagged for order ({first:#x},{second:#x})"
        );
    }
    eprintln!("[BL DEEP 2] order-independence: DEFENDED (both orders flag the fork)");
}

// ===========================================================================
// DEEP ATTACK 3 — fork hidden DEEP in the chain (a long branch evasion probe).
//
// The detector scans `self.blocks` for same-creator incomparable pairs. Build a
// LONG honest chain b0..b5, then a fork off b2 that the creator tries to "hide"
// behind later blocks. We extend ONE arm several blocks (b3..b5), then drop the
// SECOND arm (an incomparable seq-3 sibling of b3). It must still be detected:
// the past of the long arm does NOT include the sibling, and vice versa.
// ===========================================================================

#[test]
fn deep_buried_fork_off_old_block_is_detected() {
    let me = dalek_key(13);
    let mut lace = Blocklace::new_simple(me.clone());

    // Honest spine b0..b3.
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).unwrap();
    let b1 = Block::new(&me, 1, Payload::Data(vec![1]), vec![b0.id()]);
    lace.receive_block(b1.clone()).unwrap();
    let b2 = Block::new(&me, 2, Payload::Data(vec![2]), vec![b1.id()]);
    lace.receive_block(b2.clone()).unwrap();
    let b3 = Block::new(&me, 3, Payload::Data(vec![3]), vec![b2.id()]);
    lace.receive_block(b3.clone()).unwrap();
    // Extend the spine further to "bury" the fork point.
    let b4 = Block::new(&me, 4, Payload::Data(vec![4]), vec![b3.id()]);
    lace.receive_block(b4.clone()).unwrap();

    // Now a SIBLING of b3: a second seq-3 block also off b2, different payload.
    // It is incomparable to b3 (and to b4, which descends from b3, not it).
    let sibling = Block::new(&me, 3, Payload::Data(vec![0x33]), vec![b2.id()]);
    let r = lace.receive_block(sibling);
    assert!(
        matches!(r, Err(BlockError::Equivocation { .. })),
        "FINDING: a fork buried under a longer branch escaped detection"
    );
    assert!(lace.is_equivocator(&me.verifying_key().to_bytes()));
    eprintln!("[BL DEEP 3] buried fork off old block: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 4 — fork delivered INSIDE A SINGLE merge() DELTA.
//
// The audit note in finality.rs claims merge() mirrors receive_block() for
// equivocation. We hand it a causally-closed delta that CONTAINS both fork
// arms, so the topo-sort inserts them back to back. The creator must end up
// flagged and NOT left as a live tip.
// ===========================================================================

#[test]
fn deep_fork_within_single_merge_delta_is_flagged() {
    let me = dalek_key(14);
    let mut lace = Blocklace::new_simple(me.clone());
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).unwrap();

    let arm_a = Block::new(&me, 1, Payload::Data(vec![0xAA]), vec![b0.id()]);
    let arm_b = Block::new(&me, 1, Payload::Data(vec![0xBB]), vec![b0.id()]);

    // A single delta carrying BOTH arms (closed: b0 already present).
    let delta = vec![arm_a, arm_b];
    let _ = lace.merge(delta); // merge swallows the equivocation, continues

    assert!(
        lace.is_equivocator(&me.verifying_key().to_bytes()),
        "FINDING: in-delta fork did not flag the creator (merge != receive_block)"
    );
    assert!(
        !lace.tips().contains_key(&me.verifying_key().to_bytes()),
        "FINDING: equivocator left as a live tip after in-delta fork"
    );
    eprintln!("[BL DEEP 4] in-delta fork: DEFENDED (flagged + tip removed)");
}

// ===========================================================================
// DEEP ATTACK 5 — FINDING: from_checkpoint() trusts forged blocks.
//
// finality.rs::from_checkpoint documents: "blocks are NOT re-verified against
// signatures." We construct a checkpoint containing a block whose `creator` is
// a victim's key but whose signature is GARBAGE (no private key used), and show
// it is admitted into the restored blocklace and queryable as a real block.
//
// This is a precise operational gap, NOT a break of the receive_block path: the
// `from_checkpoint` doc-comment says to use it "only for trusted checkpoint
// sources." We assert the bad outcome so it is LOGGED, and flag that any
// network/peer-supplied checkpoint path is an unauthenticated-block injection.
// ===========================================================================

#[test]
fn finding_from_checkpoint_admits_forged_unsigned_blocks() {
    let attacker = dalek_key(20);
    let victim_pk = dalek_key(21).verifying_key().to_bytes();

    // A block CLAIMING the victim as creator, with a bogus signature (signed by
    // the attacker over a DIFFERENT message — would never pass verify_signature).
    let content = signing_content(&victim_pk, 7, &Payload::Data(vec![0xDE, 0xAD]), &[]);
    let bogus_sig = attacker.sign(b"not even the right message").to_bytes();
    let forged = Block {
        creator: victim_pk,
        seq: 7,
        payload: Payload::Data(vec![0xDE, 0xAD]),
        predecessors: vec![],
        signature: bogus_sig,
    };
    let _ = content; // (the real signed content is intentionally NOT used)

    // Sanity: this block would be REJECTED by the authenticated receive path.
    {
        let mut honest = Blocklace::new_simple(dalek_key(22));
        let r = honest.receive_block(forged.clone());
        assert!(
            matches!(r, Err(BlockError::InvalidSignature { .. })),
            "the forged block must fail the authenticated receive path"
        );
    }

    // But via an untrusted checkpoint, it sails in unverified.
    let checkpoint = CheckpointData {
        blocks: vec![forged.to_bytes()],
        tips: Default::default(),
        equivocators: vec![],
        ordered_block_ids: vec![],
        attested_block_ids: vec![],
    };
    let restored =
        Blocklace::from_checkpoint(&checkpoint, dalek_key(23), 1).expect("restore ok");

    let forged_id = forged.id();
    // FINDING: the forged, never-signed block is present in the restored lace.
    assert!(
        restored.contains(&forged_id),
        "if this is now false, from_checkpoint started verifying signatures (fix landed)"
    );
    let got = restored.get(&forged_id).expect("forged block present");
    assert_eq!(got.creator, victim_pk);
    eprintln!(
        "[BL DEEP 5 / FINDING] from_checkpoint admits forged unsigned blocks (creator={:02x}{:02x}..): BROKEN if checkpoint source is untrusted",
        victim_pk[0], victim_pk[1]
    );
}

// ===========================================================================
// DEEP ATTACK 6 — checkpoint can also smuggle a CAUSAL CYCLE / dangling pred.
//
// from_checkpoint skips closure checks ("order doesn't matter since we skip
// closure checks"). We inject a block whose predecessor is a non-existent id.
// The receive path would reject with MissingPredecessor; the checkpoint path
// admits it. We log this as the closure-bypass companion to FINDING 5.
// ===========================================================================

#[test]
fn finding_from_checkpoint_admits_dangling_predecessor() {
    let me = dalek_key(24);
    // A block whose predecessor id is pure fiction (never received).
    let phantom = BlockId([0x77; 32]);
    let dangling = Block::new(&me, 1, Payload::Data(vec![9]), vec![phantom]);

    // Authenticated path: MissingPredecessor.
    {
        let mut honest = Blocklace::new_simple(dalek_key(25));
        let r = honest.receive_block(dangling.clone());
        assert!(
            matches!(r, Err(BlockError::MissingPredecessor { .. })),
            "receive path must reject a dangling predecessor"
        );
    }

    // Checkpoint path: admitted with no closure check.
    let checkpoint = CheckpointData {
        blocks: vec![dangling.to_bytes()],
        tips: Default::default(),
        equivocators: vec![],
        ordered_block_ids: vec![],
        attested_block_ids: vec![],
    };
    let restored =
        Blocklace::from_checkpoint(&checkpoint, dalek_key(26), 1).expect("restore ok");
    assert!(
        restored.contains(&dangling.id()),
        "if false, from_checkpoint started enforcing closure (fix landed)"
    );
    // The phantom predecessor is genuinely absent: a non-closed view.
    assert!(
        !restored.contains(&phantom),
        "phantom predecessor should not exist; the restored view is non-closed"
    );
    eprintln!("[BL DEEP 6 / FINDING] from_checkpoint admits dangling-predecessor (non-closed view): BROKEN if checkpoint source is untrusted");
}

// ===========================================================================
// DEEP ATTACK 7 — payload-tamper does not survive (id binds payload).
//
// Take an honest block, mutate its payload but keep the original signature.
// The id() recomputes over the payload, so it becomes a NEW id whose signature
// no longer verifies. Confirms an on-wire payload swap cannot ride an honest
// signature.
// ===========================================================================

#[test]
fn deep_payload_tamper_breaks_signature() {
    let me = dalek_key(15);
    let mut lace = Blocklace::new_simple(me.clone());
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).unwrap();

    let honest = Block::new(&me, 1, Payload::Data(vec![1, 2, 3]), vec![b0.id()]);
    let mut tampered = honest.clone();
    tampered.payload = Payload::Data(vec![4, 5, 6]); // swap payload, keep sig

    let r = lace.receive_block(tampered);
    assert!(
        matches!(r, Err(BlockError::InvalidSignature { .. })),
        "FINDING: payload-tampered block accepted on honest signature"
    );
    eprintln!("[BL DEEP 7] payload tamper: DEFENDED (sig covers payload hash)");
}

// ===========================================================================
// DEEP ATTACK 8 — predecessor-set tamper breaks signature (causal binding).
//
// The signed content includes the predecessor ids. Swap a block's predecessor
// list after signing and confirm the signature fails — an attacker cannot
// re-parent a block to rewrite causal history while keeping its signature.
// ===========================================================================

#[test]
fn deep_predecessor_tamper_breaks_signature() {
    let me = dalek_key(16);
    let mut lace = Blocklace::new_simple(me.clone());
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).unwrap();
    let b1 = Block::new(&me, 1, Payload::Data(vec![1]), vec![b0.id()]);
    lace.receive_block(b1.clone()).unwrap();

    // An honest b2 off b1; re-parent it to b0 after signing.
    let honest = Block::new(&me, 2, Payload::Data(vec![2]), vec![b1.id()]);
    let mut reparented = honest.clone();
    reparented.predecessors = vec![b0.id()];

    let r = lace.receive_block(reparented);
    assert!(
        matches!(r, Err(BlockError::InvalidSignature { .. })),
        "FINDING: re-parented block accepted (predecessors not signed)"
    );
    eprintln!("[BL DEEP 8] predecessor tamper: DEFENDED (preds in signed content)");
}

// ===========================================================================
// DEEP ATTACK 9 — a membership-vote block from a non-member creator is still a
// signature-valid block, but the equivocation/insert layer is creator-agnostic.
// We confirm the blocklace itself does NOT confer membership: a stranger's
// signed block inserts fine (the lace is permissionless at the DAG layer); it is
// the CONSTITUTION layer that must reject non-member votes. We assert the lace
// admits it (so we know exactly where the trust boundary sits) — this is a
// boundary note, not a finding (constitution.rs::record_vote drops non-members).
// ===========================================================================

#[test]
fn boundary_blocklace_dag_is_permissionless_membership_is_constitution_layer() {
    let me = dalek_key(17);
    let stranger = dalek_key(99); // not in any constitution
    let mut lace = Blocklace::new_simple(me.clone());

    // A genuinely-signed block by a stranger, carrying a membership vote payload.
    let vote_block = Block::new(
        &stranger,
        0,
        Payload::MembershipVote {
            action: MembershipAction::Join {
                node_id: stranger.verifying_key().to_bytes(),
            },
        },
        vec![],
    );
    // It is correctly signed by the stranger, so the DAG layer admits it.
    lace.receive_block(vote_block.clone())
        .expect("a correctly-signed stranger block inserts at the DAG layer");
    assert!(lace.contains(&vote_block.id()));
    eprintln!(
        "[BL DEEP 9 / BOUNDARY] DAG layer is permissionless; membership enforcement lives in constitution.rs::record_vote (is_participant gate)"
    );
}
