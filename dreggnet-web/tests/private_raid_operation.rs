//! A real hiding raid-role assignment enters the live dungeon through the one
//! hosted-operation adapter and becomes visible on the ordinary game surface.

#![cfg(feature = "private-raid-operation")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use dreggnet_offerings::dungeon::{
    DungeonOffering, PRIVATE_RAID_DISCLOSURE, PRIVATE_RAID_MEDIA_TYPE, PRIVATE_RAID_OPERATION,
};
use dreggnet_offerings::{OfferingHost, SessionConfig, SessionId};
use dreggnet_web::discord_activity::{DiscordActivityState, discord_activity_router};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{CatalogState, catalog_router, fhegg_operation, web_identity};
use dungeon_on_dregg::private_raid::prove_private_assignment;
use tower::ServiceExt;

const OFFERING: &str = "dungeon";
const SESSION: &str = "private-raid-one";
const SEED: u64 = 31_337;

fn scores() -> [[u8; 4]; 4] {
    [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]]
}

fn catalog() -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(|| {
        let mut host = OfferingHost::new();
        host.register(OFFERING, "The Warden's Keep", DungeonOffering::new());
        host.open_session(
            OFFERING,
            SessionId::new(SESSION),
            SessionConfig::with_seed(SEED),
        )
        .expect("private raid dungeon opens");
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

fn upload(path: &str, body: impl Into<Body>) -> Request<Body> {
    Request::builder()
        .method("POST")
        .uri(path)
        .header("content-type", PRIVATE_RAID_MEDIA_TYPE)
        .header("cookie", "dregg_user=raid-captain")
        .body(body.into())
        .unwrap()
}

#[tokio::test]
async fn private_assignment_crosses_the_shared_transport_and_changes_the_live_game() {
    let catalog = catalog();
    let tg = tg_miniapp_router(Arc::new(TgMiniAppState::new(
        Arc::clone(&catalog),
        "test-bot-token",
        [0x71; 32],
        86_400,
    )));
    let da = discord_activity_router(Arc::new(DiscordActivityState::new(
        Arc::clone(&catalog),
        "client",
        "secret",
        [0x72; 32],
        86_400,
    )));
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg)
        .merge(da);

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
    assert!(discovered.contains(PRIVATE_RAID_OPERATION));
    assert!(discovered.contains(PRIVATE_RAID_MEDIA_TYPE));
    assert!(discovered.contains(PRIVATE_RAID_DISCLOSURE));

    let route = format!("{operations_path}/{PRIVATE_RAID_OPERATION}");
    let proof_session = ((SEED % 2_013_265_920) + 1) as u32;
    let honest = prove_private_assignment(proof_session, scores(), [[true; 4]; 4])
        .expect("real private assignment proves")
        .to_postcard()
        .expect("canonical transport");

    let wrong_media = Request::builder()
        .method("POST")
        .uri(&route)
        .header("content-type", "application/octet-stream")
        .header("cookie", "dregg_user=raid-captain")
        .body(Body::from(honest.clone()))
        .unwrap();
    assert_eq!(response(&app, wrong_media).await.0, 415);

    let wrong_session = prove_private_assignment(proof_session + 1, scores(), [[true; 4]; 4])
        .unwrap()
        .to_postcard()
        .unwrap();
    assert_eq!(response(&app, upload(&route, wrong_session)).await.0, 409);

    let mut corrupt = honest.clone();
    let last = corrupt.len() - 1;
    corrupt[last] ^= 1;
    assert_ne!(response(&app, upload(&route, corrupt)).await.0, 200);

    // Both native-platform routes exist and enforce their stronger actor gate
    // before consuming the identical proof body.
    for prefix in ["/tg", "/da"] {
        let platform_route = format!(
            "{prefix}/offerings/{OFFERING}/session/{SESSION}/operations/{PRIVATE_RAID_OPERATION}"
        );
        let anonymous = Request::builder()
            .method("POST")
            .uri(platform_route)
            .header("content-type", PRIVATE_RAID_MEDIA_TYPE)
            .body(Body::from(honest.clone()))
            .unwrap();
        assert_eq!(response(&app, anonymous).await.0, 401);
    }

    let (status, applied) = response(&app, upload(&route, honest.clone())).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&applied));
    let applied = String::from_utf8(applied).unwrap();
    assert!(applied.contains("applied"));
    assert!(applied.contains("Striker"));
    assert!(applied.contains("Bulwark"));
    assert!(applied.contains("Mender"));
    assert!(applied.contains("Pathfinder"));

    assert_eq!(response(&app, upload(&route, honest)).await.0, 409);

    // The operation is not a sidecar: the normal playable dungeon surface now
    // renders the proof-produced party roles and the attributed submitter.
    let (status, game) = response(
        &app,
        Request::builder()
            .uri(format!("/offerings/{OFFERING}/session/{SESSION}"))
            .header("cookie", "dregg_user=raid-captain")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Private raid muster"));
    assert!(game.contains("verified roles"));
    assert!(game.contains("submitted by"));
    assert!(game.contains(&web_identity("raid-captain").0));
}
