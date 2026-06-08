//! Adversarial tests against the blocklace (Lean
//! `Authority/Blocklace::equivocation_detectable / observer_detects` and the
//! `finality.rs` byzantine-repelling tooth).
//!
//! Adversary models:
//!  - a Byzantine *creator* who forks their own strand (should be detected),
//!  - a *forger* who tries to inject a block as another creator (bad sig),
//!  - a *framer* who tries to make an HONEST creator look like an equivocator
//!    via signature malleability (the subtle one — block id binds the sig).

use dregg_blocklace::finality::{Block, BlockError, Blocklace, Payload};
use ed25519_dalek::ed25519::signature::Signer as _;
use ed25519_dalek::SigningKey as DalekKey;

fn dalek_key(seed: u8) -> DalekKey {
    DalekKey::from_bytes(&[seed; 32])
}

/// Reconstruct the block signing content (mirrors finality.rs::signing_content
/// for the Ack/Data payloads used here). Domain-separated, payload hashed.
fn signing_content(creator: &[u8; 32], seq: u64, payload: &Payload, preds: &[[u8; 32]]) -> Vec<u8> {
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
        buf.extend_from_slice(p);
    }
    buf
}

// ===========================================================================
// ATTACK 1 — Byzantine creator forks their OWN strand (equivocation).
// Lean claims: detectable as an incomparable pair; tip evicted.
// ===========================================================================

#[test]
fn attack_byzantine_self_fork_is_detected_and_evicted() {
    let me = dalek_key(1);
    let mut lace = Blocklace::new_simple(me.clone());

    // Genesis-ish: a seq-0 block with no predecessors.
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("b0 ok");

    // Two DISTINCT seq-1 blocks both extending b0 with different payloads.
    // (Same creator, same seq, mutually non-preceding ⇒ a fork.)
    let fork_a = Block::new(&me, 1, Payload::Data(vec![0xAA]), vec![b0.id()]);
    let fork_b = Block::new(&me, 1, Payload::Data(vec![0xBB]), vec![b0.id()]);

    lace.receive_block(fork_a).expect("first arm accepted");
    let r = lace.receive_block(fork_b);
    // EVIDENCE: the second arm is flagged as equivocation.
    match r {
        Err(BlockError::Equivocation { creator, .. }) => {
            assert_eq!(creator, me.verifying_key().to_bytes());
        }
        other => panic!("expected Equivocation, got {other:?}"),
    }
    assert!(lace.is_equivocator(&me.verifying_key().to_bytes()));
    eprintln!("[BL ATTACK 1] self-fork: DEFENDED (detected + flagged)");
}

// ===========================================================================
// ATTACK 2 — forge a block as a DIFFERENT creator (no private key).
// Lean/Rust claim: verify_signature rejects.
// ===========================================================================

#[test]
fn attack_forge_block_for_other_creator_is_rejected() {
    let me = dalek_key(2);
    let victim_pk = dalek_key(3).verifying_key().to_bytes();
    let mut lace = Blocklace::new_simple(me.clone());

    // Sign with OUR key but claim the victim is the creator. id()/verify use
    // `creator` as the verifying key, so the signature won't verify.
    let content = signing_content(&victim_pk, 0, &Payload::Ack, &[]);
    let sig = me.sign(&content).to_bytes();
    let forged = Block {
        creator: victim_pk,
        seq: 0,
        payload: Payload::Ack,
        predecessors: vec![],
        signature: sig,
    };
    let r = lace.receive_block(forged);
    assert!(matches!(r, Err(BlockError::InvalidSignature { .. })));
    eprintln!("[BL ATTACK 2] cross-creator forgery: DEFENDED (sig rejected)");
}

// ===========================================================================
// ATTACK 3 — FRAMING via signature malleability. The block id binds the
// signature bytes: id = blake3(content || signature). If a non-canonical
// re-encoding of an honest block's signature still VERIFIES, it yields a NEW
// id with the SAME (creator, seq, preds) but is incomparable to the original
// → detect_equivocation would flag the HONEST creator as an equivocator and
// evict them. We probe whether dalek v2 accepts a malleated signature.
//
// Outcome interpretation:
//  - If the malleated sig is REJECTED -> DEFENDED (dalek v2 strictness saves us).
//  - If ACCEPTED and the honest creator gets evicted -> FINDING (framing works).
// ===========================================================================

#[test]
fn probe_signature_malleability_framing() {
    let honest = dalek_key(4);
    let mut lace = Blocklace::new_simple(honest.clone());

    let b0 = Block::new(&honest, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("b0 ok");

    let b1 = Block::new(&honest, 1, Payload::Data(vec![1, 2, 3]), vec![b0.id()]);
    lace.receive_block(b1.clone()).expect("honest b1 ok");

    // Malleate: add the ed25519 group order L to the S scalar (upper 32 bytes).
    // L = 2^252 + 27742317777372353535851937790883648493 (little-endian).
    const L: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ];
    let mut mal = b1.signature;
    // s' = s + L  (mod 2^256, little-endian add with carry).
    let mut carry = 0u16;
    for i in 0..32 {
        let v = mal[32 + i] as u16 + L[i] as u16 + carry;
        mal[32 + i] = (v & 0xff) as u8;
        carry = v >> 8;
    }

    let framed = Block {
        creator: b1.creator,
        seq: 1,
        payload: b1.payload.clone(),
        predecessors: b1.predecessors.clone(),
        signature: mal,
    };

    // First: does the malleated block even verify?
    let verifies = framed.verify_signature().is_ok();
    // Then: feed it to the lace and see if the honest creator is framed.
    let r = lace.receive_block(framed);
    let framed_out = lace.is_equivocator(&honest.verifying_key().to_bytes());

    eprintln!(
        "[BL ATTACK 3 / PROBE] malleated-sig verifies={} receive_block={:?} honest_framed={}",
        verifies, r, framed_out
    );
    // Assert the SAFE outcome so this test FAILS loudly if framing ever works.
    assert!(
        !framed_out,
        "FINDING: honest creator framed as equivocator via signature malleability"
    );
}

// ===========================================================================
// ATTACK 4 — replay the SAME honest block twice (idempotency / no self-frame).
// Re-receiving an identical block must be a no-op, NOT a self-equivocation.
// ===========================================================================

#[test]
fn attack_replay_same_block_is_idempotent_not_equivocation() {
    let me = dalek_key(5);
    let mut lace = Blocklace::new_simple(me.clone());
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("first ok");
    // Replay identical block: same id, already present -> Ok, no equivocation.
    lace.receive_block(b0.clone()).expect("replay ok");
    assert!(!lace.is_equivocator(&me.verifying_key().to_bytes()));
    eprintln!("[BL ATTACK 4] identical replay: DEFENDED (idempotent)");
}
