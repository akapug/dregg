//! Regression: `Turn` (and the `Action`s in its call forest) MUST round-trip
//! through postcard.
//!
//! Postcard is a non-self-describing positional format. A
//! `#[serde(skip_serializing_if = "…")]` field is not written when the
//! predicate is true, but the deserializer still reads it positionally —
//! desyncing the byte stream and failing with "Found an Option discriminant
//! that wasn't 0 or 1" (or "expected more data"). That is exactly how the
//! gossip/blocklace finalized-turn path and `/api/turns/submit-signed` broke:
//! every turn with a defaulted optional field (the common case) was
//! undecodable, so turns never replicated.
//!
//! This test pins the fix: no `skip_serializing_if` may reappear on any field
//! that rides inside `Turn` over the wire.

use dregg_turn::action::{Action, Authorization, DelegationMode, Effect, symbol};
use dregg_turn::forest::CallForest;
use dregg_turn::turn::{Finality, Turn, TurnReceipt};
use dregg_turn::verify_receipt_chain;
use dregg_types::CellId;

fn minimal_action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: symbol("submit"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

fn turn_with(effects: Vec<Effect>) -> Turn {
    let agent = CellId::from_bytes([1u8; 32]);
    let mut forest = CallForest::new();
    forest.add_root(minimal_action(agent, effects));
    Turn {
        agent,
        nonce: 3,
        fee: 500,
        memo: Some("wire roundtrip".to_string()),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

fn receipt(agent: CellId, marker: u8, previous_receipt_hash: Option<[u8; 32]>) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [marker; 32],
        forest_hash: [marker.wrapping_add(1); 32],
        pre_state_hash: [marker.wrapping_add(2); 32],
        post_state_hash: [marker.wrapping_add(3); 32],
        timestamp: marker as i64,
        effects_hash: [marker.wrapping_add(4); 32],
        computrons_used: marker as u64,
        action_count: 1,
        previous_receipt_hash,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Finality::Final,
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}

fn assert_roundtrips(turn: &Turn) {
    let bytes = postcard::to_stdvec(turn).expect("postcard serialize");
    let decoded: Turn = postcard::from_bytes(&bytes)
        .expect("postcard MUST round-trip Turn (no skip_serializing_if)");
    // Re-encode the decoded value; a positional desync would also corrupt this.
    let bytes2 = postcard::to_stdvec(&decoded).expect("re-serialize decoded turn");
    assert_eq!(bytes, bytes2, "postcard re-encode must be byte-stable");
    assert_eq!(turn.nonce, decoded.nonce);
    assert_eq!(turn.fee, decoded.fee);
    assert_eq!(turn.memo, decoded.memo);
    assert_eq!(
        turn.call_forest.action_count(),
        decoded.call_forest.action_count()
    );
}

#[test]
fn empty_consumed_capability_receipt_chain_roundtrips_and_verifies() {
    let agent = CellId::from_bytes([4u8; 32]);
    let first = receipt(agent, 10, None);
    let second = receipt(agent, 11, Some(first.receipt_hash()));
    let chain = vec![first, second];

    verify_receipt_chain(&chain).expect("source chain verifies");
    assert!(chain.iter().all(|r| r.consumed_capabilities.is_empty()));

    let json = serde_json::to_vec(&chain).expect("receipt chain JSON serializes");
    let from_json: Vec<TurnReceipt> =
        serde_json::from_slice(&json).expect("receipt chain JSON deserializes");
    verify_receipt_chain(&from_json).expect("JSON round-tripped chain verifies");
    assert!(from_json.iter().all(|r| r.consumed_capabilities.is_empty()));
    assert_eq!(
        chain
            .iter()
            .map(TurnReceipt::receipt_hash)
            .collect::<Vec<_>>(),
        from_json
            .iter()
            .map(TurnReceipt::receipt_hash)
            .collect::<Vec<_>>()
    );

    let bytes = postcard::to_stdvec(&from_json).expect("receipt chain postcard serializes");
    let from_postcard: Vec<TurnReceipt> =
        postcard::from_bytes(&bytes).expect("receipt chain postcard deserializes");
    let bytes2 = postcard::to_stdvec(&from_postcard).expect("receipt chain postcard reserializes");
    assert_eq!(bytes, bytes2, "postcard receipt chain bytes are stable");
    verify_receipt_chain(&from_postcard).expect("postcard round-tripped chain verifies");
    assert!(
        from_postcard
            .iter()
            .all(|r| r.consumed_capabilities.is_empty())
    );
}

#[test]
fn turn_with_defaulted_optionals_roundtrips() {
    // The common case: every optional/sidecar field at its default. This is the
    // exact shape that previously failed to deserialize.
    assert_roundtrips(&turn_with(vec![]));
}

#[test]
fn turn_with_transfer_effect_roundtrips() {
    let to = CellId::from_bytes([2u8; 32]);
    let from = CellId::from_bytes([1u8; 32]);
    assert_roundtrips(&turn_with(vec![Effect::Transfer {
        from,
        to,
        amount: 100,
    }]));
}

#[test]
fn turn_with_note_create_effect_roundtrips() {
    // NoteCreate carries the previously-skipped `value_commitment` / `range_proof`
    // optionals; exercise them at default (None) to pin the Effect-variant fix.
    use dregg_cell::NoteCommitment;
    assert_roundtrips(&turn_with(vec![Effect::NoteCreate {
        commitment: NoteCommitment([7u8; 32]),
        value: 42,
        asset_type: 0,
        encrypted_note: vec![],
        value_commitment: None,
        range_proof: None,
    }]));
}
