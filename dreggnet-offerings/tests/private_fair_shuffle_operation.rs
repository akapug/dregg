#![cfg(feature = "private-fair-shuffle-operation")]

use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_SHUFFLE_COMMIT_OPERATION, PRIVATE_SHUFFLE_PROVE_OPERATION,
    PRIVATE_SHUFFLE_REVEAL_OPERATION, encode_private_shuffle_commitment,
    private_fair_shuffle_session_for_seed,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{DreggIdentity, Offering, OfferingHost, SessionConfig, SessionId};
use dungeon_on_dregg::private_fair_shuffle::{PARTICIPANTS, PreparedFairShuffle};

fn actor(participant: usize) -> DreggIdentity {
    DreggIdentity(format!("shuffle-player-{participant}"))
}

#[test]
fn hosted_dungeon_enforces_actor_bound_commit_prove_and_selective_reveal() {
    let offering = DungeonOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(0xFA17))
        .expect("dungeon opens");
    let prepared = PreparedFairShuffle::fresh(
        session.private_fair_shuffle_session_id(),
        0,
        [12_345, 1, 2, 3, 4, 5, 6, 7],
    )
    .expect("private deal witness");

    let first = encode_private_shuffle_commitment(0, prepared.participant_commitment(0).unwrap());
    offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            &first,
            actor(0),
        )
        .expect("first commitment lands");
    let stolen_seat =
        encode_private_shuffle_commitment(1, prepared.participant_commitment(1).unwrap());
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_SHUFFLE_COMMIT_OPERATION,
                &stolen_seat,
                actor(0),
            )
            .is_err(),
        "one authenticated actor cannot occupy two participant slots"
    );
    assert!(session.private_fair_shuffle_table().commitments()[1].is_none());

    for participant in 1..PARTICIPANTS {
        let payload = encode_private_shuffle_commitment(
            participant as u8,
            prepared.participant_commitment(participant).unwrap(),
        );
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_SHUFFLE_COMMIT_OPERATION,
                &payload,
                actor(participant),
            )
            .unwrap();
    }

    let receipt = prepared
        .prove_receipt(session.private_fair_shuffle_table())
        .expect("real hiding proof");
    let proof = receipt.to_postcard().unwrap();
    let applied = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_PROVE_OPERATION,
            &proof,
            DreggIdentity("shuffle-prover".to_string()),
        )
        .expect("accepted proof lands");
    assert!(
        applied
            .public_fields
            .iter()
            .any(|(key, value)| key == "outcome" && value == "accepted")
    );
    assert!(
        session
            .private_fair_shuffle_table()
            .accepted_receipt()
            .is_some()
    );

    let opening = prepared.card_opening(6).unwrap().to_postcard().unwrap();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_SHUFFLE_REVEAL_OPERATION,
                &opening,
                actor(5),
            )
            .is_err(),
        "a different authenticated seat cannot obtain the opening"
    );
    assert_eq!(
        session.private_fair_shuffle_table().revealed_cards()[6],
        None
    );

    let revealed = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_SHUFFLE_REVEAL_OPERATION,
            &opening,
            actor(6),
        )
        .expect("seat-owned opening lands");
    assert!(revealed.public_fields.iter().any(|(key, _)| key == "card"));
    assert!(session.private_fair_shuffle_table().revealed_cards()[6].is_some());

    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_SHUFFLE_REVEAL_OPERATION,
                &opening,
                actor(6),
            )
            .is_err(),
        "opening replay is refused"
    );
}

#[test]
fn fair_deal_operation_journal_restores_the_exact_public_protocol_state() {
    const SEED: u64 = 0xFA18;
    let store = InMemoryResumeStore::new();
    let id = SessionId::new("durable-fair-deal");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();

    let prepared = PreparedFairShuffle::fresh(
        private_fair_shuffle_session_for_seed(SEED),
        0,
        [9_999, 1, 2, 3, 4, 5, 6, 7],
    )
    .unwrap();
    let mut mirror = dungeon_on_dregg::private_fair_shuffle::FairShuffleTable::new(
        private_fair_shuffle_session_for_seed(SEED),
    )
    .unwrap();
    for participant in 0..PARTICIPANTS {
        let commitment = prepared.participant_commitment(participant).unwrap();
        mirror.commit(participant, commitment).unwrap();
        host.invoke_binary_operation(
            "dungeon",
            &id,
            PRIVATE_SHUFFLE_COMMIT_OPERATION,
            &encode_private_shuffle_commitment(participant as u8, commitment),
            actor(participant),
        )
        .unwrap();
    }
    let proof = prepared
        .prove_receipt(&mirror)
        .unwrap()
        .to_postcard()
        .unwrap();
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_SHUFFLE_PROVE_OPERATION,
        &proof,
        DreggIdentity("proof-relay".to_string()),
    )
    .unwrap();
    let opening = prepared.card_opening(3).unwrap().to_postcard().unwrap();
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_SHUFFLE_REVEAL_OPERATION,
        &opening,
        actor(3),
    )
    .unwrap();

    let log = store.load("dungeon", &id).expect("durable operation log");
    assert_eq!(log.operations.len(), PARTICIPANTS + 2);
    assert!(
        log.operations
            .iter()
            .all(|operation| operation.replay_is_canonical_request)
    );
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let render = format!("{:?}", reopened.render("dungeon", &id).unwrap().0);
    assert!(render.contains("accepted attempt 0"));
    assert!(render.contains("1 private card opening(s) landed"));
}
