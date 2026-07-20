//! A trader-local encrypted amount request crosses the shared web operation
//! adapter and changes the ordinary Dark Bazaar pool surface.

#![cfg(feature = "dark-amm-game")]

use std::sync::Arc;

use axum::{Router, body::Body, http::Request};
use dreggnet_market::dark_amm_game::{
    DARK_AMM_DISCLOSURE, DARK_AMM_MEDIA_TYPE, DARK_AMM_OFFERING_KEY, DARK_AMM_OPERATION,
    DarkAmmGameOffering, DarkAmmHostKeyMaterial, produce_encrypted_swap_seeded,
};
use dreggnet_offerings::OfferingHost;
use dreggnet_web::discord_activity::{DiscordActivityState, discord_activity_router};
use dreggnet_web::telegram_miniapp::{TgMiniAppState, tg_miniapp_router};
use dreggnet_web::{
    CatalogState, DARK_AMM_SECRET_KEY_FILE_ENV, catalog_router, dark_amm_key_from, fhegg_operation,
    register_dark_amm_from,
};
use tower::ServiceExt;

const SESSION: &str = "dark-pool-web";

fn session_seed() -> u64 {
    let digest = blake3::hash(SESSION.as_bytes());
    u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap())
}

fn catalog(key_file: String) -> Arc<CatalogState> {
    Arc::new(CatalogState::with_host(move || {
        let mut host = OfferingHost::new();
        assert!(
            register_dark_amm_from(&mut host, |name| {
                (name == DARK_AMM_SECRET_KEY_FILE_ENV).then(|| key_file.clone())
            })
            .expect("protected deployment key registers")
        );
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
        .header("content-type", DARK_AMM_MEDIA_TYPE)
        .header("cookie", "dregg_user=veiled-liquidity-party")
        .body(Body::from(body))
        .unwrap()
}

#[tokio::test]
async fn encrypted_amount_swap_lands_through_shared_web_telegram_discord_affordance() {
    let key_material = DarkAmmHostKeyMaterial::generate_for_demo([0xB4; 32])
        .expect("deployment-owned Dark Pool keys");
    let dir = std::env::temp_dir().join(format!(
        "dregg-web-dark-amm-{}-{}",
        std::process::id(),
        session_seed()
    ));
    std::fs::create_dir(&dir).expect("create isolated deployment-key directory");
    let key_file = dir.join("dark-pool.dbak");
    std::fs::write(&key_file, key_material.to_secret_wire_bytes())
        .expect("write deployment key fixture");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o644))
            .expect("make fixture deliberately unsafe");
        let refused = match dark_amm_key_from(|_| Some(key_file.display().to_string())) {
            Err(refused) => refused,
            Ok(_) => panic!("group-readable custody must fail closed"),
        };
        assert!(refused.contains("remove all group/other permissions"));
        std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o600))
            .expect("protect deployment key fixture");
    }
    assert!(
        dark_amm_key_from(|_| None)
            .expect("absent env is a deliberate disable")
            .is_none()
    );
    // This is external producer material: public key/session/cursor only. The
    // operator seed remains on the host side and never enters the request.
    let public = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(session_seed())
        .expect("public producer context");
    let exact = produce_encrypted_swap_seeded(&public, 50, 300, 200, 400, [0x51; 32])
        .expect("trader encrypts dx/dy")
        .to_wire_bytes();

    let catalog = catalog(key_file.display().to_string());
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg_miniapp_router(Arc::new(TgMiniAppState::new(
            Arc::clone(&catalog),
            "test-bot-token",
            [0x52; 32],
            86_400,
        ))))
        .merge(discord_activity_router(Arc::new(
            DiscordActivityState::new(Arc::clone(&catalog), "client", "secret", [0x53; 32], 86_400),
        )));

    // The ordinary catalog GET lazily opens the table with the shared
    // blake3(web-session-id) seed. This is the same binding exported by the
    // operator's `dark-amm-tool public-id` command.
    let game_path = format!("/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}");
    let (status, opened_game) = response(
        &app,
        Request::builder()
            .uri(&game_path)
            .header("cookie", "dregg_user=veiled-liquidity-party")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    assert!(
        String::from_utf8(opened_game)
            .unwrap()
            .contains("0 encrypted swap(s) accepted")
    );

    let operations_path =
        format!("/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}/operations");
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
    assert!(discovered.contains(DARK_AMM_OPERATION));
    assert!(discovered.contains(DARK_AMM_MEDIA_TYPE));
    assert!(discovered.contains(DARK_AMM_DISCLOSURE));

    let route = format!("{operations_path}/{DARK_AMM_OPERATION}");
    for prefix in ["/tg", "/da"] {
        let native_route = format!(
            "{prefix}/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}/operations/{DARK_AMM_OPERATION}"
        );
        let anonymous = Request::builder()
            .method("POST")
            .uri(native_route)
            .header("content-type", DARK_AMM_MEDIA_TYPE)
            .body(Body::from(exact.clone()))
            .unwrap();
        assert_eq!(response(&app, anonymous).await.0, 401);
    }

    let wrong_media = Request::builder()
        .method("POST")
        .uri(&route)
        .header("content-type", "application/octet-stream")
        .header("cookie", "dregg_user=veiled-liquidity-party")
        .body(Body::from(exact.clone()))
        .unwrap();
    assert_eq!(response(&app, wrong_media).await.0, 415);

    let (status, receipt) = response(&app, upload(&route, exact.clone())).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&receipt));
    let receipt = String::from_utf8(receipt).unwrap();
    assert!(receipt.contains("requestDigest"));
    assert!(receipt.contains("acceptedSwaps"));
    assert!(!receipt.contains("\"dx\""));
    assert!(!receipt.contains("\"dy\""));

    // Replay is a conflict, not a second mutation.
    assert_eq!(response(&app, upload(&route, exact)).await.0, 409);

    let (status, game) = response(
        &app,
        Request::builder()
            .uri(game_path)
            .header("cookie", "dregg_user=veiled-liquidity-party")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("encrypted constant-product table"));
    assert!(game.contains("1 encrypted swap(s) accepted"));
    assert!(game.contains("public invariant k=90000"));
    assert!(game.contains("Proof-bearing operations"));
    assert!(game.contains(DARK_AMM_OPERATION));
    assert!(game.contains("Verify &amp; apply"));

    std::fs::remove_dir_all(dir).expect("remove isolated deployment-key directory");
}
