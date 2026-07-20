#![cfg(feature = "private-preference-operation")]

use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_PREFERENCE_OPERATION, private_preference_session_for_seed,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{DreggIdentity, Offering, OfferingHost, SessionConfig, SessionId};
use dungeon_on_dregg::private_preference::{PrivateBallot, prove_private_preference};

const SEED: u64 = 0xC011EC7;

fn ballots() -> [PrivateBallot; 4] {
    [
        PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
        PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
        PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
        PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
    ]
}

#[test]
fn hosted_dungeon_accepts_one_hiding_party_choice_atomically() {
    let offering = DungeonOffering::new();
    let mut session = offering.open(SessionConfig::with_seed(SEED)).unwrap();
    assert!(
        offering
            .binary_operations(&session)
            .iter()
            .any(|operation| operation.name == PRIVATE_PREFERENCE_OPERATION)
    );

    let proof_session = private_preference_session_for_seed(SEED);
    let receipt = prove_private_preference(proof_session, &ballots()).unwrap();
    let honest = receipt.to_postcard().unwrap();

    let wrong = prove_private_preference(proof_session + 1, &ballots())
        .unwrap()
        .to_postcard()
        .unwrap();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_PREFERENCE_OPERATION,
                &wrong,
                DreggIdentity("intruder".to_string()),
            )
            .is_err()
    );
    assert!(session.private_preference_decision().is_none());
    assert!(session.private_preference_actor().is_none());

    let mut corrupt = honest.clone();
    let at = corrupt.len() - 1;
    corrupt[at] ^= 1;
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_PREFERENCE_OPERATION,
                &corrupt,
                DreggIdentity("intruder".to_string()),
            )
            .is_err()
    );
    assert!(session.private_preference_decision().is_none());

    let landed = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_PREFERENCE_OPERATION,
            &honest,
            DreggIdentity("guild-counsel".to_string()),
        )
        .unwrap();
    assert_eq!(landed.operation, PRIVATE_PREFERENCE_OPERATION);
    assert_eq!(session.private_preference_decision().unwrap().winner(), 1);
    assert_eq!(
        session.private_preference_actor(),
        Some(&DreggIdentity("guild-counsel".to_string()))
    );

    let before = session.private_preference_decision();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_PREFERENCE_OPERATION,
                &honest,
                DreggIdentity("replayer".to_string()),
            )
            .is_err()
    );
    assert_eq!(session.private_preference_decision(), before);
}

#[test]
fn private_party_choice_reverifies_from_the_operation_journal_after_restart() {
    let id = SessionId::new("durable-private-party-counsel");
    let proof_session = private_preference_session_for_seed(SEED);
    let honest = prove_private_preference(proof_session, &ballots())
        .unwrap()
        .to_postcard()
        .unwrap();
    let store = InMemoryResumeStore::new();
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(SEED))
        .unwrap();
    host.invoke_binary_operation(
        "dungeon",
        &id,
        PRIVATE_PREFERENCE_OPERATION,
        &honest,
        DreggIdentity("guild-counsel".to_string()),
    )
    .unwrap();

    let log = store.load("dungeon", &id).unwrap();
    assert_eq!(log.operations.len(), 1);
    assert!(log.operations[0].replay_is_canonical_request);
    assert!(log.operations[0].replay_disclosure.contains("no ballot"));
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let rendered = format!("{:?}", reopened.render("dungeon", &id).unwrap().0);
    assert!(rendered.contains("the party privately chose #1"));
    assert!(rendered.contains("descend the drowned stair"));

    assert!(
        reopened
            .invoke_binary_operation(
                "dungeon",
                &id,
                PRIVATE_PREFERENCE_OPERATION,
                &honest,
                DreggIdentity("restart-replayer".to_string()),
            )
            .is_err()
    );
}
