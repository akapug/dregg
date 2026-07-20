//! The semantic quest's opaque graph-reduction receipts cross the same shared
//! web/Telegram/Discord operation adapter as the rest of the playable dungeon.

#![cfg(feature = "private-quest-operation")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_QUEST_DISCLOSURE, PRIVATE_QUEST_MEDIA_TYPE, PRIVATE_QUEST_OPERATION,
    private_quest_session_for_seed,
};
use dreggnet_offerings::{OfferingHost, SessionConfig, SessionId};
use dreggnet_web::discord_activity::{DiscordActivityState, discord_activity_router};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation};
use dungeon_on_dregg::private_quest::{
    PrivateQuestMove, PrivateQuestRaid, encode_private_quest_receipt,
};
use tower::ServiceExt;

const OFFERING: &str = "dungeon";
const SESSION: &str = "private-semantic-quest";
const SEED: u64 = 0x5155_4553;

fn catalog() -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        host.register(OFFERING, "The Warden's Keep", DungeonOffering::new());
        host.open_session(
            OFFERING,
            SessionId::new(SESSION),
            SessionConfig::with_seed(SEED),
        )
        .expect("private quest dungeon opens");
        host
    }))
}

async fn response(app: &Router, request: Request<Body>) -> (u16, Vec<u8>) {
    let response = app.clone().oneshot(request).await.expect("router response");
    let status = response.status().as_u16();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body")
        .to_vec();
    (status, body)
}

fn upload(path: &str, body: Vec<u8>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", PRIVATE_QUEST_MEDIA_TYPE)
        .header("cookie", "dregg_user=quest-party")
        .body(Body::from(body))
        .unwrap()
}

#[tokio::test]
async fn private_graph_quest_is_playable_through_the_shared_frontend_surface() {
    let catalog = catalog();
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg_miniapp_router(Arc::new(TgMiniAppState::new(
            Arc::clone(&catalog),
            "test-bot-token",
            [0x51; 32],
            86_400,
        ))))
        .merge(discord_activity_router(Arc::new(
            DiscordActivityState::new(Arc::clone(&catalog), "client", "secret", [0x52; 32], 86_400),
        )));

    let operations_path = format!("/offerings/{OFFERING}/session/{SESSION}/operations");
    let (status, discovered) = response(
        &app,
        Request::builder()
            .uri(&operations_path)
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let discovered = String::from_utf8(discovered).unwrap();
    assert!(discovered.contains(PRIVATE_QUEST_OPERATION));
    assert!(discovered.contains(PRIVATE_QUEST_MEDIA_TYPE));
    assert!(discovered.contains(PRIVATE_QUEST_DISCLOSURE));

    let route = format!("{operations_path}/{PRIVATE_QUEST_OPERATION}");
    let mut producer =
        PrivateQuestRaid::new(private_quest_session_for_seed(SEED)).expect("external producer");
    let first = encode_private_quest_receipt(
        &producer
            .advance(producer.command(PrivateQuestMove::ScoutVeiledRoute))
            .expect("first private reduction"),
    )
    .unwrap();
    let second = encode_private_quest_receipt(
        &producer
            .advance(producer.command(PrivateQuestMove::BreakWardenSeal))
            .expect("second private reduction"),
    )
    .unwrap();

    // The native-platform endpoints publish the same operation but refuse an
    // unauthenticated actor before proof consumption.
    for prefix in ["/tg", "/da"] {
        let path = format!(
            "{prefix}/offerings/{OFFERING}/session/{SESSION}/operations/{PRIVATE_QUEST_OPERATION}"
        );
        let anonymous = Request::builder()
            .method("POST")
            .uri(path)
            .header("content-type", PRIVATE_QUEST_MEDIA_TYPE)
            .body(Body::from(first.clone()))
            .unwrap();
        assert_eq!(response(&app, anonymous).await.0, 401);
    }

    let (status, first_result) = response(&app, upload(&route, first)).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&first_result));
    assert!(String::from_utf8(first_result).unwrap().contains("newRoot"));
    let (status, second_result) = response(&app, upload(&route, second)).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&second_result));

    // The proof operation changes the normal playable dungeon surface; it is
    // not a disconnected verifier demo.
    let (status, game) = response(
        &app,
        Request::builder()
            .uri(format!("/offerings/{OFFERING}/session/{SESSION}"))
            .header("cookie", "dregg_user=quest-party")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Private semantic quest"));
    assert!(game.contains("2/2 opaque reductions verified"));
    assert!(game.contains("2 authenticated submitter(s)"));
    assert!(game.contains("Proof-bearing operations"));
    assert!(game.contains(PRIVATE_QUEST_OPERATION));
    assert!(game.contains("Verify &amp; apply"));
}
