//! **The federation-exit path binds the executor, or it is not an exit path.**
//!
//! `verify_via_receipt_chain` is the "federation exit": an agent presents a
//! receipt chain and proves its state without the federation vouching for it.
//! Its doc used to claim the chain "proves that the state was produced by a
//! sequence of valid, **executor-checked** turns from genesis."
//!
//! It did not check any executor signature, and it takes no executor keys, so
//! it could not. The structural checks — genesis, hash-linking, state
//! continuity, agent consistency — involve no executor at all. This test
//! constructs the consequence: a chain fabricated from nothing, by no executor,
//! to an attacker-chosen head state, which `verify_via_receipt_chain` accepts.
//!
//! [`verify_via_receipt_chain_strict`] is the fix: it threads trusted executor
//! keys and requires a valid signature on every receipt. The lenient one is
//! retained (a caller who binds the executor elsewhere — attested root,
//! committee QC — wants the structural check alone) with its doc corrected to
//! say what it does.

use dregg_cell::CellId;
use dregg_federation::{verify_via_receipt_chain, verify_via_receipt_chain_strict};
use dregg_turn::{TurnReceipt, VerifyError, sign_receipt};

const EXECUTOR_SEED: [u8; 32] = [0x42; 32];

fn make_receipt(
    agent: CellId,
    pre_state: [u8; 32],
    post_state: [u8; 32],
    previous_receipt_hash: Option<[u8; 32]>,
) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: pre_state,
        post_state_hash: post_state,
        timestamp: 1000,
        effects_hash: [0u8; 32],
        computrons_used: 100,
        action_count: 1,
        previous_receipt_hash,
        agent,
        federation_id: [0u8; 32],
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}

/// Build a structurally-perfect chain of `n` receipts ending at `head_state`.
/// If `sign` is true every receipt is executor-signed under `EXECUTOR_SEED`.
///
/// Note what an attacker needs to run this: nothing. No executor, no key, no
/// federation. `sign: false` is a chain fabricated out of thin air.
fn build_chain(agent: CellId, n: usize, head_state: [u8; 32], sign: bool) -> Vec<TurnReceipt> {
    assert!(n > 0);
    let mut chain: Vec<TurnReceipt> = Vec::with_capacity(n);
    let mut state = [1u8; 32];

    for i in 0..n {
        let pre_state = state;
        // The last receipt lands exactly on the chosen head state.
        let post_state = if i == n - 1 {
            head_state
        } else {
            state[0] = (i + 2) as u8;
            state
        };
        state = post_state;

        let previous_receipt_hash = if i == 0 {
            None
        } else {
            Some(chain[i - 1].receipt_hash())
        };

        let mut r = make_receipt(agent, pre_state, post_state, previous_receipt_hash);
        r.timestamp = 1000 + i as i64;
        r.turn_hash = [i as u8; 32];
        if sign {
            r.executor_signature = Some(sign_receipt(&r, &EXECUTOR_SEED));
        }
        chain.push(r);
    }
    chain
}

fn executor_pubkey() -> [u8; 32] {
    ed25519_dalek::SigningKey::from_bytes(&EXECUTOR_SEED)
        .verifying_key()
        .to_bytes()
}

/// **The fabricated-exit forgery.** A chain no executor ever signed, asserting
/// an attacker-chosen head state, is accepted by the structural exit path and
/// rejected by the strict one.
#[test]
fn strict_exit_rejects_a_chain_no_executor_signed() {
    let agent = CellId::from_bytes([1u8; 32]);
    let pk = executor_pubkey();
    let honest_head = [0xEE; 32];

    // ── HONEST POLE FIRST. A genuine, executor-signed chain to its real head
    // must pass BOTH paths. Without this, "strict rejected the forgery" would
    // be indistinguishable from "strict rejects everything" — a vacuous canary.
    let honest = build_chain(agent, 3, honest_head, /* sign */ true);
    verify_via_receipt_chain(&honest, Some(honest_head))
        .expect("honest pole: a real chain must pass the structural exit path");
    verify_via_receipt_chain_strict(&honest, Some(honest_head), &[pk])
        .expect("honest pole: a real chain must pass the STRICT exit path");

    // ── THE FORGERY: same shape, same head, NO executor anywhere. An attacker
    // builds this with no key and no federation.
    let forged_head = [0xAA; 32];
    let forged = build_chain(agent, 3, forged_head, /* sign */ false);

    // Strict names the adversary at the exact index.
    let err = verify_via_receipt_chain_strict(&forged, Some(forged_head), &[pk])
        .expect_err("STRICT exit must reject a chain with no executor signatures");
    assert!(
        matches!(err, VerifyError::ExecutorSignatureMissing { index: 0 }),
        "strict must reject with ExecutorSignatureMissing, got {err:?}"
    );

    // The structural path ACCEPTS the fabrication, to an arbitrary head state.
    // This is what "executor-checked" claimed to prevent and did not. Pinned as
    // the lenient path's DOCUMENTED behaviour: if this ever rejects, the
    // function became strict and its doc must be brought along.
    verify_via_receipt_chain(&forged, Some(forged_head)).expect(
        "verify_via_receipt_chain is structure-only by construction and accepts an \
         unsigned fabrication. If this now rejects, the function changed semantics — \
         update its doc, which promises only the structural check.",
    );
}

/// The signature-strip variant: take a GENUINE chain and delete one signature.
/// Every structural check still passes because none of them involve the
/// executor — only strict can tell.
#[test]
fn strict_exit_rejects_a_stripped_signature() {
    let agent = CellId::from_bytes([2u8; 32]);
    let pk = executor_pubkey();
    let head = [0xCD; 32];

    // ── HONEST POLE FIRST.
    let chain = build_chain(agent, 3, head, true);
    verify_via_receipt_chain_strict(&chain, Some(head), &[pk])
        .expect("honest pole: the signed chain passes strict");

    // ── THE FORGERY: strip the middle receipt's signature, touch nothing else.
    let mut stripped = chain.clone();
    stripped[1].executor_signature = None;

    let err = verify_via_receipt_chain_strict(&stripped, Some(head), &[pk])
        .expect_err("strict must reject the stripped chain");
    assert!(
        matches!(err, VerifyError::ExecutorSignatureMissing { index: 1 }),
        "expected ExecutorSignatureMissing at the stripped index, got {err:?}"
    );

    // Structurally invisible — which is precisely why strict must exist.
    verify_via_receipt_chain(&stripped, Some(head))
        .expect("the strip is invisible to every structural check");
}

/// Strict still binds the head: a chain that is perfectly signed but does not
/// reach the claimed state is rejected, and rejected as a state break rather
/// than as a signature problem. Adding the executor check must not cost the
/// check that was already there.
#[test]
fn strict_exit_still_binds_the_expected_head_state() {
    let agent = CellId::from_bytes([3u8; 32]);
    let pk = executor_pubkey();
    let real_head = [0x11; 32];

    // ── HONEST POLE FIRST: it passes against its true head.
    let chain = build_chain(agent, 2, real_head, true);
    verify_via_receipt_chain_strict(&chain, Some(real_head), &[pk])
        .expect("honest pole: passes against the head it actually reaches");

    // A genuinely-signed chain claimed to prove a DIFFERENT state.
    let err = verify_via_receipt_chain_strict(&chain, Some([0x99; 32]), &[pk])
        .expect_err("a signed chain must not prove a state it does not reach");
    assert!(
        matches!(err, VerifyError::StateChainBreak { .. }),
        "expected StateChainBreak (not a signature error — the signatures are fine), got {err:?}"
    );

    // And with no expected head, the chain is accepted on its own terms.
    verify_via_receipt_chain_strict(&chain, None, &[pk])
        .expect("no expected head ⇒ only the chain's own validity is asserted");
}

/// An exit verifier with no trusted executor keys trusts nobody. It must not
/// degrade into the structural path.
#[test]
fn strict_exit_with_no_trusted_keys_rejects() {
    let agent = CellId::from_bytes([4u8; 32]);
    let pk = executor_pubkey();
    let head = [0x77; 32];
    let chain = build_chain(agent, 2, head, true);

    // ── HONEST POLE FIRST.
    verify_via_receipt_chain_strict(&chain, Some(head), &[pk])
        .expect("honest pole: verifies against the real executor key");

    let err = verify_via_receipt_chain_strict(&chain, Some(head), &[])
        .expect_err("no trusted keys ⇒ nothing to verify against ⇒ reject");
    assert!(
        matches!(err, VerifyError::ExecutorSignatureInvalid { index: 0 }),
        "expected ExecutorSignatureInvalid, got {err:?}"
    );
}
