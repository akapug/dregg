//! End-to-end no-single-viewer fhEgg clearing tooth.
//!
//! Plaintext orders live only in independently spawned trader closures.  The
//! coordinator receives authenticated ciphertext envelopes, folds two encrypted
//! curves, opens only one-time-padded BFV values through n-of-n threshold shares,
//! and hands opaque per-party arithmetic inputs to the distributed MPC runtime.
//! The exact `(p*, V*)` result and reveal-only transcript are finally bound to
//! the authenticated sources by a replay-protected quorum receipt.
//!
//! This is semi-honest MPC with trusted Beaver preprocessing.  Ed25519 closes
//! source/session/transcript attribution, not malicious input validity or
//! malicious MPC correctness; the latter still need row-validity proofs and
//! authenticated/MACed MPC transport.

use std::thread;
use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhe::bfv::PublicKey;
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};
use fhegg_fhe::additive::CollectiveOrderFoldEngine;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest,
};
use fhegg_fhe::boundary::{
    MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession, MaskedOpening,
};
use fhegg_fhe::mpc_party::{
    local_channels, run_party, trusted_dealer_triples, PartyArithmeticInput, PartyMpcSession,
};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressError, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    MIN_SMUDGE_BITS,
};
use fhegg_fhe::{reference_clear, Order, Side};
use rand::rngs::StdRng;
use rand::SeedableRng;

const N: usize = 2;
const K: usize = 4;
const VALUE_BITS: usize = 16;

fn collective_keygen(
    params: &BfvParams,
) -> (KeygenSession, Vec<ThresholdParty>, CollectivePublicKey) {
    let session = KeygenSession::from_seed(N, [0x31; 32]).expect("fixed public CRP session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(N);
    for party in 0..N {
        let (state, contribution) =
            ThresholdParty::join(&session, party, params).expect("party-local key share");
        coordinator
            .accept(contribution)
            .expect("unique public key contribution");
        parties.push(state);
    }
    let collective = coordinator.finish().expect("complete keygen quorum");
    (session, parties, collective)
}

/// Run one target curve through encrypted masks and smudged n-of-n threshold
/// opening.  Returned mask states still retain every private `r_i`; only the
/// one-time-padded opening is public.
fn threshold_masked_curve(
    nonce: [u8; 32],
    target: fhegg_fhe::bfv_lean::LeanCiphertext,
    params: &BfvParams,
    collective: &CollectivePublicKey,
    threshold_parties: &[ThresholdParty],
) -> (Vec<MaskedBoundaryParty>, MaskedOpening) {
    let session = MaskedDecryptSession::from_public(nonce, N, K, target, params)
        .expect("public masked-decrypt session");
    let mut coordinator = MaskedDecryptCoordinator::new(session.clone(), params.clone());
    let mut mask_states = Vec::with_capacity(N);
    for party in 0..N {
        let (state, encrypted_mask) =
            MaskedBoundaryParty::prepare(&session, party, params, collective)
                .expect("party retains mask and exports only Enc(mask)");
        coordinator
            .accept(encrypted_mask)
            .expect("full unique mask contribution");
        mask_states.push(state);
    }
    let masked = coordinator.finish().expect("homomorphically masked target");
    let framed = threshold_parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(masked.ciphertext(), MIN_SMUDGE_BITS)
                .expect("Lean-pinned smudged partial decrypt")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();
    let opening = masked
        .open_framed(&framed, params)
        .expect("full exact-ciphertext quorum opens padded curve only");
    (mask_states, opening)
}

#[test]
fn authenticated_traders_to_threshold_bfv_to_party_mpc_to_attested_result() {
    let params = BfvParams::fold_set();
    let (keygen_session, threshold_parties, collective) = collective_keygen(&params);

    // These values are moved into separate trader closures below.  No clearing
    // coordinator API accepts `Order`; it accepts only strict signed wire bytes.
    let orders = [
        Order {
            side: Side::Bid,
            limit: 2,
            qty: 7,
        },
        Order {
            side: Side::Ask,
            limit: 1,
            qty: 4,
        },
        Order {
            side: Side::Bid,
            limit: 1,
            qty: 5,
        },
        Order {
            side: Side::Ask,
            limit: 2,
            qty: 6,
        },
    ];
    let expected = reference_clear(&orders, K);
    assert_eq!(expected.p_star, Some(2));
    assert_eq!(expected.v_star, 7);

    let trader_keys = (0..orders.len())
        .map(|trader| SigningKey::from_bytes(&[0x51 + trader as u8; 32]))
        .collect::<Vec<_>>();
    let trader_public_keys = trader_keys
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect::<Vec<_>>();
    let ingress_session =
        OrderIngressSession::new([0x61; 32], K, &params, &collective).expect("ingress session");
    let public_key_bytes = collective.pk.to_bytes();

    let trader_threads = orders
        .into_iter()
        .zip(trader_keys.iter().cloned())
        .enumerate()
        .map(|(trader, (order, signing_key))| {
            let params = params.clone();
            let session = ingress_session.clone();
            let public_key_bytes = public_key_bytes.clone();
            thread::spawn(move || {
                let pk = PublicKey::from_bytes(&public_key_bytes, params.arc())
                    .expect("public collective key parses at trader");
                let collective = CollectivePublicKey { pk };
                SignedOrderSubmission::encrypt_and_sign(
                    &session,
                    trader,
                    0,
                    &order,
                    &params,
                    &collective,
                    &signing_key,
                )
                .expect("trader-local encrypted signed order")
                .0
                .to_wire_bytes()
            })
        })
        .collect::<Vec<_>>();
    let mut wires = trader_threads
        .into_iter()
        .map(|trader| trader.join().expect("trader exits"))
        .collect::<Vec<_>>();

    let mut book = AuthenticatedOrderBook::new(ingress_session.clone(), trader_public_keys)
        .expect("strict trader roster");

    // Structurally valid ciphertext tampering remains attributable and fails
    // signature verification.  It does not burn the source sequence.
    // The side tag is public and structurally valid in either state; flipping it
    // proves the signature covers semantics as well as ciphertext bytes.
    let mut tampered_wire = wires[0].clone();
    let side_offset = 8 + 32 + 8 + 8;
    tampered_wire[side_offset] ^= 1;
    let tampered =
        SignedOrderSubmission::from_wire_bytes(&tampered_wire, &ingress_session, &params)
            .expect("tamper remains a canonical ciphertext envelope");
    assert_eq!(
        book.accept(tampered),
        Err(OrderIngressError::InvalidSignature { trader: 0 })
    );

    // Arrival order cannot change the final source/ciphertext binding order.
    wires.reverse();
    for wire in &wires {
        let submission = SignedOrderSubmission::from_wire_bytes(wire, &ingress_session, &params)
            .expect("strict authenticated order wire");
        book.accept(submission).expect("fresh signed source");
    }
    let replay = SignedOrderSubmission::from_wire_bytes(
        wires.last().expect("nonempty"),
        &ingress_session,
        &params,
    )
    .expect("replay parses");
    assert_eq!(
        book.accept(replay),
        Err(OrderIngressError::DuplicateSource {
            trader: 0,
            sequence: 0,
        })
    );
    let batch = book.finish();
    assert_eq!(batch.len(), 4);
    assert_eq!(batch.ordered_inputs().len(), 8);
    let (encrypted_rows, ordered_inputs) = batch.into_parts();

    // The coordinator folds ciphertexts only.  The CPU backend is chosen so
    // this proof-of-composition has no adapter/environment dependency.
    let folded = CollectiveOrderFoldEngine::cpu_only()
        .fold_rows(encrypted_rows, K, params.plaintext_modulus())
        .expect("authenticated encrypted book folds");

    let (demand_masks, demand_opening) = threshold_masked_curve(
        [0x71; 32],
        folded.d_ct,
        &params,
        &collective,
        &threshold_parties,
    );
    let (supply_masks, supply_opening) = threshold_masked_curve(
        [0x72; 32],
        folded.s_ct,
        &params,
        &collective,
        &threshold_parties,
    );

    let mpc_session = PartyMpcSession::new(
        [0x73; 32],
        N,
        K,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("boundary-compatible distributed MPC session");

    // Each party closure consumes its private mask states and creates an opaque
    // PartyArithmeticInput locally.  The joining/launching coordinator cannot
    // inspect the two mod-t rows through that type's API.
    let input_threads = demand_masks
        .into_iter()
        .zip(supply_masks)
        .enumerate()
        .map(|(party, (demand_state, supply_state))| {
            let demand_opening = demand_opening.clone();
            let supply_opening = supply_opening.clone();
            let session = mpc_session.clone();
            thread::spawn(move || {
                let demand = demand_state
                    .derive_mod_t_share(&demand_opening)
                    .expect("party-local demand share");
                let supply = supply_state
                    .derive_mod_t_share(&supply_opening)
                    .expect("party-local supply share");
                let mut sharing_rng = StdRng::seed_from_u64(0x7400 + party as u64);
                PartyArithmeticInput::new(&session, party, &demand, &supply, &mut sharing_rng)
                    .expect("private rows become opaque MPC ingress")
            })
        })
        .collect::<Vec<_>>();
    let inputs = input_threads
        .into_iter()
        .map(|party| party.join().expect("boundary party exits"))
        .collect::<Vec<_>>();

    let mut triple_rng = StdRng::seed_from_u64(0x7500);
    let triples = trusted_dealer_triples(&mpc_session, &mut triple_rng)
        .expect("shape-only trusted preprocessing");
    let (coordinator, endpoints) = local_channels(&mpc_session);
    let mpc_threads = inputs
        .into_iter()
        .zip(triples)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let distributed = coordinator
        .coordinate(&mpc_session)
        .expect("complete distributed clearing quorum");
    for party in mpc_threads {
        party
            .join()
            .expect("MPC party exits")
            .expect("MPC party completes");
    }
    assert_eq!(distributed.crossing.p_star, expected.p_star);
    assert_eq!(distributed.crossing.v_star, u64::from(expected.v_star));
    assert!(distributed.transcript.is_reveal_only(&mpc_session));

    // Bind the actual authenticated inputs, actual public BFV identity, actual
    // reveal-only transcript, and exact output into an endorsed receipt.
    let committee_keys = [
        SigningKey::from_bytes(&[0x76; 32]),
        SigningKey::from_bytes(&[0x77; 32]),
    ];
    let verifier = AuthenticatedQuorumVerifier::new(
        committee_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        N,
    )
    .expect("unanimous committee receipt policy");
    let bfv = BfvPublicIdentity::from_public(&params, &keygen_session, &collective);
    let context = ExpectedClearingContext {
        session: &mpc_session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &ordered_inputs,
        transcript: &distributed.transcript,
        crossing: &distributed.crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &context,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical source/result claim");
    let claim_digest = receipt.claim_digest();
    let signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| {
            verifier
                .sign_claim(&claim_digest, party, key)
                .expect("committee endorses exact claim")
        })
        .collect::<Vec<_>>();
    receipt.computation_integrity = verifier
        .assemble_evidence(&claim_digest, &signatures)
        .expect("canonical unanimous evidence");

    // Source substitution fails before replay state is consumed.
    let mut wrong_inputs = ordered_inputs.clone();
    wrong_inputs[0] = InputDigest::commitment([0x99; 32]);
    let wrong_context = ExpectedClearingContext {
        ordered_inputs: &wrong_inputs,
        ..context
    };
    let mut replay_guard = InMemoryReplayGuard::default();
    assert_eq!(
        receipt.verify_full(&wrong_context, &verifier, &mut replay_guard),
        Err(AttestationError::BindingMismatch)
    );
    receipt
        .verify_full(&context, &verifier, &mut replay_guard)
        .expect("exact authenticated private clearing accepts once");
    assert_eq!(
        receipt.verify_full(&context, &verifier, &mut replay_guard),
        Err(AttestationError::ReplayDetected)
    );
}
