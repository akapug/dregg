#![cfg(feature = "private-raid-operation")]

use dreggnet_offerings::dungeon::{DungeonOffering, PRIVATE_RAID_OPERATION};
use dreggnet_offerings::{DreggIdentity, Offering, SessionConfig};
use dungeon_on_dregg::private_raid::{RaidRole, prove_private_assignment};

fn scores() -> [[u8; 4]; 4] {
    [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]]
}

#[test]
fn hosted_dungeon_accepts_one_real_private_raid_proof_atomically() {
    let offering = DungeonOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(31_337))
        .expect("dungeon opens");
    let proof_session = session.private_raid_session_id();
    // Other independently feature-gated private mechanics may share this
    // offering.  The raid test asserts discovery by stable identity instead of
    // assuming it is the only binary operation installed.
    assert!(
        offering
            .binary_operations(&session)
            .iter()
            .any(|operation| operation.name == PRIVATE_RAID_OPERATION)
    );

    let receipt = prove_private_assignment(proof_session, scores(), [[true; 4]; 4])
        .expect("private assignment proves");
    let honest = receipt.to_postcard().expect("canonical receipt");

    let mut corrupt = honest.clone();
    let at = corrupt.len() - 1;
    corrupt[at] ^= 1;
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_RAID_OPERATION,
                &corrupt,
                DreggIdentity("mallory".to_string()),
            )
            .is_err()
    );
    assert!(session.private_raid_assignment().is_none());
    assert!(session.private_raid_actor().is_none());

    let wrong_session = prove_private_assignment(proof_session + 1, scores(), [[true; 4]; 4])
        .unwrap()
        .to_postcard()
        .unwrap();
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_RAID_OPERATION,
                &wrong_session,
                DreggIdentity("mallory".to_string()),
            )
            .is_err()
    );
    assert!(session.private_raid_assignment().is_none());

    let applied = offering
        .invoke_binary_operation(
            &mut session,
            PRIVATE_RAID_OPERATION,
            &honest,
            DreggIdentity("party-captain".to_string()),
        )
        .expect("verified assignment lands");
    assert_eq!(applied.operation, PRIVATE_RAID_OPERATION);
    let assignment = session
        .private_raid_assignment()
        .expect("assignment stored");
    assert_eq!(
        assignment.roles(),
        [
            RaidRole::Striker,
            RaidRole::Bulwark,
            RaidRole::Mender,
            RaidRole::Pathfinder,
        ]
    );
    assert_eq!(
        session.private_raid_actor(),
        Some(&DreggIdentity("party-captain".to_string()))
    );

    let landed = assignment;
    assert!(
        offering
            .invoke_binary_operation(
                &mut session,
                PRIVATE_RAID_OPERATION,
                &honest,
                DreggIdentity("replayer".to_string()),
            )
            .is_err()
    );
    assert_eq!(session.private_raid_assignment(), Some(landed));
    assert_eq!(
        session.private_raid_actor(),
        Some(&DreggIdentity("party-captain".to_string()))
    );
}
