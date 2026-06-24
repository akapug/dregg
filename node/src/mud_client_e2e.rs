//! mud_client_e2e.rs — THE PLAYABLE MUD CLIENT, PROVEN BY PLAYING A REAL SESSION.
//!
//! This drives the [`crate::mud_client`] engine through a full text-MUD loop against a
//! REAL HTTP node (a `boot_mud_world` in-process node + served TCP listener), proving you
//! can actually PLAY the node-hosted living world:
//!
//!   1. CONNECT + LOOK — the client reads the room/character/NPC cells off the real ledger
//!      (the character starts level 1, 0 xp, in the Entrance; the watchman calm);
//!   2. GAIN-XP — fire the `gain-xp` affordance (a signed, verified turn) → xp = 120 lands;
//!   3. MOVE — fire `move` → the character walks into the Hall (room = 2) on the ledger;
//!   4. TICK — the GM's reactive program observes the ledger and the WORLD RESPONDS: a
//!      LEVEL-UP (level 2, xp reset) + the NPC going ALERT — GM superpowers a player cannot
//!      reach;
//!   5. DESCEND — fire `descend` into the player's PERSONAL dungeon instance (a fork the GM
//!      admitted them to) → the instance's flag flips on the ledger (the player entered);
//!   6. THE ASYMMETRY (receipted refusals): `descend` into the SEALED dungeon (no cap) and a
//!      GM-only NPC write are both REFUSED by the executor's authority gate, leaving the
//!      world unchanged — while the GM's own moves over the same cells committed.
//!
//! Every accepted step carries a turn hash (a receipt). The whole session runs over the
//! genuine remote-client path (discover + signed `/turns/submit`), the same one a cockpit
//! or a thin terminal uses.
#![cfg(all(test, feature = "deos-host"))]

use crate::mud_client::{MudClient, boot_mud_world, gm_tick};

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn client_plays_the_node_hosted_mud_living_world() {
    // ── CONNECT ── boot a self-contained playable world (node + hosted GM + served port).
    let session = boot_mud_world("mud-client-test-aria")
        .await
        .expect("boot the playable MUD world");
    let client = MudClient::from_session(&session);

    // ── (1) LOOK ── the world the client reads is the REAL committed ledger state.
    let view = client.look().await.expect("look at the starting room");
    assert!(
        view.contains("the Entrance"),
        "the player starts in the Entrance; view was:\n{view}"
    );
    assert!(
        view.contains("level 1"),
        "the character starts at level 1; view was:\n{view}"
    );
    assert_eq!(
        client.room().await.expect("room"),
        1,
        "starts in the Entrance (room 1)"
    );
    assert_eq!(
        client.stats().await.expect("stats"),
        (1, 0),
        "starts level 1, 0 xp"
    );
    assert_eq!(
        client.npc_mood().await.expect("mood"),
        0,
        "the watchman starts calm"
    );

    // ── (2) GAIN-XP ── a real signed, verified turn → xp lands on the ledger.
    let gain = client.gain_xp().await.expect("fire gain-xp");
    assert!(
        gain.accepted,
        "the player's gain-xp turn was accepted; error={:?}",
        gain.error
    );
    assert!(
        gain.turn_hash.is_some(),
        "an accepted gain-xp turn carries a receipt (turn hash)"
    );
    assert_eq!(
        client.stats().await.expect("stats after gain-xp").1,
        120,
        "xp rose to 120 on the ledger"
    );

    // ── (3) MOVE ── walk into the Hall (room = 2) on the real ledger.
    let mov = client.do_move().await.expect("fire move");
    assert!(
        mov.accepted,
        "the player's move turn was accepted; error={:?}",
        mov.error
    );
    assert_eq!(
        client.room().await.expect("room after move"),
        2,
        "moved into the Hall (room 2)"
    );

    // ── (4) TICK ── the GM observes + the WORLD RESPONDS (level-up + NPC reaction).
    gm_tick(session.node_state(), client.world())
        .await
        .expect("the GM reactive tick runs");
    assert_eq!(
        client.stats().await.expect("stats after tick"),
        (2, 0),
        "the GM LEVELED the character up to 2 and reset xp (a GM superpower)"
    );
    assert_eq!(
        client.npc_mood().await.expect("mood after tick"),
        1,
        "the watchman REACTED to the player's arrival (mood ALERT)"
    );

    // ── (5) DESCEND ── enter the player's PERSONAL dungeon instance (admitted ⇒ succeeds).
    assert!(
        !client.dungeon_descended().await.expect("dungeon flag pre"),
        "the dungeon starts un-descended"
    );
    let (visible, descend) = client
        .descend()
        .await
        .expect("fire descend into the personal dungeon");
    assert!(
        visible,
        "the personal dungeon's `descend` affordance is discoverable"
    );
    assert!(
        descend.accepted,
        "descend into the ADMITTED dungeon is authorized (the GM granted the player a cap); error={:?}",
        descend.error
    );
    assert!(
        client.dungeon_descended().await.expect("dungeon flag post"),
        "the player DESCENDED — the instance's flag flipped on the real ledger"
    );

    // ── (6a) THE ASYMMETRY: descend into the SEALED dungeon (no cap) → REFUSED ───────────
    let (sealed_visible, sealed) = client
        .descend_sealed()
        .await
        .expect("attempt descend into the sealed dungeon");
    assert!(
        sealed_visible,
        "the sealed dungeon's surface is discoverable (you can SEE it)"
    );
    assert!(
        !sealed.accepted,
        "but descending the SEALED dungeon is REFUSED (no cap — fork isolation); outcome={sealed:?}"
    );

    // ── (6b) THE ASYMMETRY: a GM-only NPC write the player holds no cap over → REFUSED ───
    let mood_before = client.npc_mood().await.expect("npc mood before forge");
    let forge = client
        .forge_npc()
        .await
        .expect("attempt the forbidden NPC write");
    assert!(
        !forge.accepted,
        "a player CANNOT write the NPC (no cap held — GM-only); outcome={forge:?}"
    );
    assert_eq!(
        client.npc_mood().await.expect("npc mood after forge"),
        mood_before,
        "the refused forge left the NPC's mood unchanged on the ledger"
    );
}
