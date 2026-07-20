//! The proof-required Dark Pool is one frontend-neutral operation: web accepts
//! it and the Telegram/Discord adapters expose the same authenticated route.

#![cfg(feature = "dark-amm-game")]

use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::{Router, body::Body, http::Request};
use dregg_circuit_prove::dark_amm_private::{PrivateAmmWitness, prove_zk};
use dreggnet_market::dark_amm_game::{
    DARK_AMM_OFFERING_KEY, DARK_AMM_PROVED_DISCLOSURE, DARK_AMM_PROVED_MEDIA_TYPE,
    DARK_AMM_PROVED_OPERATION, DARK_AMM_SAME_OPENING_DISCLOSURE, DARK_AMM_SAME_OPENING_MEDIA_TYPE,
    DARK_AMM_SAME_OPENING_OPERATION, DarkAmmGameOffering, DarkAmmHostKeyMaterial,
    DarkAmmPrivateSwapAuthority, produce_proved_encrypted_swap,
    produce_proved_encrypted_swap_seeded,
};
use dreggnet_offerings::{OfferingHost, SessionId};
use dreggnet_web::discord_activity::{
    ACTIVITY_TICKET_HEADER, DiscordActivityState, DiscordCodeExchange, DiscordTokenExchange,
    OAuthError, discord_activity_router,
};
use dreggnet_web::telegram_miniapp::{
    INIT_DATA_HEADER, TgMiniAppState, tg_miniapp_router, validate_init_data_at, webapp_secret_key,
};
use dreggnet_web::{
    CatalogState, DARK_AMM_AUTHORITY_KEYS_ENV, DARK_AMM_AUTHORITY_THRESHOLD_ENV,
    DARK_AMM_INITIAL_ROOT_ENV, DARK_AMM_SECRET_KEY_FILE_ENV, catalog_router, fhegg_operation,
    register_dark_amm_from,
};
use ed25519_dalek::SigningKey;
use fhegg_fhe::amm_same_opening::Tier1SameOpeningAuthority;
use hmac::{Hmac, Mac};
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;
use sha2::Sha256;
use tower::ServiceExt;

const SESSION: &str = "shielded-dark-pool-web";
const TG_SESSION: &str = "shielded-dark-pool-telegram";
const DA_SESSION: &str = "shielded-dark-pool-discord";
const TG_OFFERING_KEY: &str = "dark-pool-telegram";
const DA_OFFERING_KEY: &str = "dark-pool-discord";
const TG_TOKEN: &str = "123456789:test-only-dark-pool-token";
const TG_UID: u64 = 7_001;
const DA_UID: u64 = 8_002;
const TG_BOT_SECRET: [u8; 32] = [0x72; 32];
const DA_BOT_SECRET: [u8; 32] = [0x73; 32];

fn session_seed_for(session: &str) -> u64 {
    let digest = blake3::hash(session.as_bytes());
    u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap())
}

fn session_seed() -> u64 {
    session_seed_for(SESSION)
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or(0)
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn root_hex(root: &[u32; 8]) -> String {
    root.iter()
        .map(|lane| format!("{lane:08x}"))
        .collect::<Vec<_>>()
        .join(":")
}

fn url_encode(value: &str) -> String {
    let mut out = String::new();
    for byte in value.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                out.push(byte as char);
            }
            _ => out.push_str(&format!("%{byte:02X}")),
        }
    }
    out
}

/// Mint Telegram's production initData shape forward from a test-only bot token.
fn telegram_init_data(uid: u64) -> String {
    type HmacSha256 = Hmac<Sha256>;

    let auth_date = unix_now();
    let user = format!(r#"{{"id":{uid},"first_name":"Veiled","username":"dark_pool"}}"#);
    let signature = "test-only-third-party-signature";
    let data_check_string = format!(
        "auth_date={auth_date}\nquery_id=dark-pool-e2e\nsignature={signature}\nuser={user}"
    );
    let secret = webapp_secret_key(TG_TOKEN);
    let mut mac = HmacSha256::new_from_slice(&secret).expect("HMAC accepts a 32-byte key");
    mac.update(data_check_string.as_bytes());
    let hash: [u8; 32] = mac.finalize().into_bytes().into();
    let init_data = format!(
        "query_id=dark-pool-e2e&user={}&auth_date={auth_date}&signature={signature}&hash={}",
        url_encode(&user),
        hex32(&hash)
    );
    validate_init_data_at(&secret, &init_data, auth_date, 86_400)
        .expect("test initData passes the production verifier");
    init_data
}

struct StubDiscordExchange;

impl DiscordTokenExchange for StubDiscordExchange {
    fn exchange(
        &self,
        _client_id: &str,
        _client_secret: &str,
        code: &str,
    ) -> Result<DiscordCodeExchange, OAuthError> {
        if code != "test-only-dark-pool-code" {
            return Err(OAuthError::TokenStatus(401));
        }
        Ok(DiscordCodeExchange {
            user_id: DA_UID,
            access_token: "test-only-discord-access-token".to_string(),
            username: Some("dark_pool".to_string()),
        })
    }
}

struct PreparedSameOpening {
    request: Vec<u8>,
    old_root: [u32; 8],
    new_root: [u32; 8],
}

fn prepare_same_opening_request(
    session: &str,
    key_material: &DarkAmmHostKeyMaterial,
    issuers: &[SigningKey; 3],
    new_blind_base: u32,
    dx_seed: [u8; 32],
    dy_seed: [u8; 32],
) -> PreparedSameOpening {
    let seed = session_seed_for(session);
    let bootstrap = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(seed)
        .unwrap();
    let witness = PrivateAmmWitness::try_new(
        100,
        900,
        50,
        300,
        core::array::from_fn(|lane| 7_000 + lane as u32),
        core::array::from_fn(|lane| new_blind_base + lane as u32),
    )
    .unwrap();
    let (proof, statement) = prove_zk(bootstrap.private_amm_receipt_session(), &witness).unwrap();
    let issuer_public = issuers
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect::<Vec<_>>();
    let authority = Tier1SameOpeningAuthority::new(issuer_public.clone(), 2).unwrap();
    let public = DarkAmmGameOffering::demo_same_opening_required(
        key_material.clone(),
        statement.old_root,
        issuer_public,
        2,
    )
    .unwrap()
    .public_session_for_seed(seed)
    .unwrap();
    let proved = produce_proved_encrypted_swap_seeded(
        &public,
        50,
        300,
        200,
        400,
        statement,
        proof.to_postcard().unwrap(),
        dx_seed,
        dy_seed,
    )
    .unwrap();
    let private_authority =
        DarkAmmPrivateSwapAuthority::try_new(&public, witness, dx_seed, dy_seed, &proved).unwrap();
    let endorsements = [0usize, 2]
        .map(|index| {
            private_authority
                .endorse_same_opening(&public, &proved, &authority, index, &issuers[index])
                .unwrap()
        })
        .to_vec();
    let request = private_authority
        .assemble_same_opening_request(&public, proved, &authority, &endorsements)
        .unwrap()
        .to_wire_bytes();
    PreparedSameOpening {
        request,
        old_root: statement.old_root,
        new_root: statement.new_root,
    }
}

async fn response(app: &Router, request: Request<Body>) -> (u16, Vec<u8>) {
    let response = app.clone().oneshot(request).await.unwrap();
    let status = response.status().as_u16();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap()
        .to_vec();
    (status, body)
}

#[tokio::test]
async fn proved_receipt_crosses_web_and_shared_bot_operation_surface() {
    let key_material = DarkAmmHostKeyMaterial::generate_for_demo([0xC4; 32]).unwrap();
    let legacy = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(session_seed())
        .unwrap();
    let old_blind = core::array::from_fn(|lane| 4_000 + lane as u32);
    let new_blind = core::array::from_fn(|lane| 5_000 + lane as u32);
    let witness = PrivateAmmWitness::try_new(100, 900, 50, 300, old_blind, new_blind).unwrap();
    let (proof, statement) = prove_zk(legacy.private_amm_receipt_session(), &witness).unwrap();
    let proof_bytes = proof.to_postcard().unwrap();

    let public = DarkAmmGameOffering::demo_proof_required(key_material.clone(), statement.old_root)
        .unwrap()
        .public_session_for_seed(session_seed())
        .unwrap();
    let mut rng = StdRng::seed_from_u64(91);
    let request =
        produce_proved_encrypted_swap(&public, 50, 300, 200, 400, statement, proof_bytes, &mut rng)
            .unwrap()
            .to_wire_bytes();

    let dir = std::env::temp_dir().join(format!(
        "dregg-web-proved-amm-{}-{}",
        std::process::id(),
        session_seed()
    ));
    std::fs::create_dir(&dir).unwrap();
    let key_file = dir.join("dark-pool.dbak");
    std::fs::write(&key_file, key_material.to_secret_wire_bytes()).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
    let root_value = statement
        .old_root
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let key_file_string = key_file.display().to_string();
    let catalog = Arc::new(CatalogState::with_host(move || {
        let mut host = OfferingHost::new();
        register_dark_amm_from(&mut host, |name| match name {
            DARK_AMM_SECRET_KEY_FILE_ENV => Some(key_file_string.clone()),
            DARK_AMM_INITIAL_ROOT_ENV => Some(root_value.clone()),
            _ => None,
        })
        .unwrap();
        host
    }));
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg_miniapp_router(Arc::new(TgMiniAppState::new(
            Arc::clone(&catalog),
            "test-bot-token",
            [0x62; 32],
            86_400,
        ))))
        .merge(discord_activity_router(Arc::new(
            DiscordActivityState::new(Arc::clone(&catalog), "client", "secret", [0x63; 32], 86_400),
        )));

    let game_path = format!("/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}");
    assert_eq!(
        response(
            &app,
            Request::builder()
                .uri(&game_path)
                .header("cookie", "dregg_user=shielded-trader")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .0,
        200
    );
    let operations_path = format!("{game_path}/operations");
    let (status, body) = response(
        &app,
        Request::builder()
            .uri(&operations_path)
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let body = String::from_utf8(body).unwrap();
    assert!(body.contains(DARK_AMM_PROVED_OPERATION));
    assert!(body.contains(DARK_AMM_PROVED_MEDIA_TYPE));
    assert!(body.contains(DARK_AMM_PROVED_DISCLOSURE));
    assert!(!body.contains("dark-bazaar.private-amm-swap.v1"));

    for prefix in ["/tg", "/da"] {
        let route = format!(
            "{prefix}/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}/operations/{DARK_AMM_PROVED_OPERATION}"
        );
        let anonymous = Request::builder()
            .method("POST")
            .uri(route)
            .header("content-type", DARK_AMM_PROVED_MEDIA_TYPE)
            .body(Body::from(request.clone()))
            .unwrap();
        assert_eq!(response(&app, anonymous).await.0, 401);
    }

    let route = format!("{operations_path}/{DARK_AMM_PROVED_OPERATION}");
    let upload = || {
        Request::builder()
            .method("POST")
            .uri(&route)
            .header("content-type", DARK_AMM_PROVED_MEDIA_TYPE)
            .header("cookie", "dregg_user=shielded-trader")
            .body(Body::from(request.clone()))
            .unwrap()
    };
    let (status, receipt) = response(&app, upload()).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&receipt));
    let receipt = String::from_utf8(receipt).unwrap();
    assert!(receipt.contains("proofDigest"));
    assert!(receipt.contains("statementDigest"));
    assert!(receipt.contains("newRoot"));
    assert_eq!(response(&app, upload()).await.0, 409);

    let (_, game) = response(
        &app,
        Request::builder()
            .uri(game_path)
            .header("cookie", "dregg_user=shielded-trader")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Hiding receipt required"));
    assert!(game.contains("1 encrypted swap(s) accepted"));
    assert!(game.contains("same dx/dy opening"));

    std::fs::remove_dir_all(dir).unwrap();
}

#[tokio::test]
async fn exact_opening_v3_crosses_the_same_web_telegram_and_discord_surface() {
    let key_material = DarkAmmHostKeyMaterial::generate_for_demo([0xD4; 32]).unwrap();
    let issuers = [0x81, 0x82, 0x83].map(|seed| SigningKey::from_bytes(&[seed; 32]));
    let issuer_public = issuers
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect::<Vec<_>>();
    let web_request = prepare_same_opening_request(
        SESSION,
        &key_material,
        &issuers,
        8_000,
        [0x51; 32],
        [0x52; 32],
    );
    let tg_request = prepare_same_opening_request(
        TG_SESSION,
        &key_material,
        &issuers,
        9_000,
        [0x61; 32],
        [0x62; 32],
    );
    let da_request = prepare_same_opening_request(
        DA_SESSION,
        &key_material,
        &issuers,
        10_000,
        [0x71; 32],
        [0x72; 32],
    );
    assert_ne!(web_request.old_root, tg_request.old_root);
    assert_ne!(web_request.old_root, da_request.old_root);
    assert_ne!(web_request.request, tg_request.request);
    assert_ne!(tg_request.request, da_request.request);

    let dir = std::env::temp_dir().join(format!(
        "dregg-web-same-opening-amm-{}-{}",
        std::process::id(),
        session_seed()
    ));
    std::fs::create_dir(&dir).unwrap();
    let key_file = dir.join("dark-pool.dbak");
    std::fs::write(&key_file, key_material.to_secret_wire_bytes()).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
    let root_value = web_request
        .old_root
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",");
    let authority_keys = issuer_public
        .iter()
        .map(|key| {
            key.iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        })
        .collect::<Vec<_>>()
        .join(",");
    let key_file_string = key_file.display().to_string();
    let extra_key_material = key_material.clone();
    let extra_issuer_public = issuer_public.clone();
    let tg_old_root = tg_request.old_root;
    let da_old_root = da_request.old_root;
    let catalog = Arc::new(CatalogState::with_host(move || {
        let mut host = OfferingHost::new();
        register_dark_amm_from(&mut host, |name| match name {
            DARK_AMM_SECRET_KEY_FILE_ENV => Some(key_file_string.clone()),
            DARK_AMM_INITIAL_ROOT_ENV => Some(root_value.clone()),
            DARK_AMM_AUTHORITY_KEYS_ENV => Some(authority_keys.clone()),
            DARK_AMM_AUTHORITY_THRESHOLD_ENV => Some("2".to_string()),
            _ => None,
        })
        .unwrap();
        host.register(
            TG_OFFERING_KEY,
            "The Dark Bazaar — Telegram exact-opening table",
            DarkAmmGameOffering::demo_same_opening_required(
                extra_key_material.clone(),
                tg_old_root,
                extra_issuer_public.clone(),
                2,
            )
            .unwrap(),
        );
        host.register(
            DA_OFFERING_KEY,
            "The Dark Bazaar — Discord exact-opening table",
            DarkAmmGameOffering::demo_same_opening_required(
                extra_key_material.clone(),
                da_old_root,
                extra_issuer_public.clone(),
                2,
            )
            .unwrap(),
        );
        host
    }));
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(fhegg_operation::router(Arc::clone(&catalog)))
        .merge(tg_miniapp_router(Arc::new(TgMiniAppState::new(
            Arc::clone(&catalog),
            TG_TOKEN,
            TG_BOT_SECRET,
            86_400,
        ))))
        .merge(discord_activity_router(Arc::new(
            DiscordActivityState::with_oauth(
                Arc::clone(&catalog),
                "test-only-client",
                "test-only-client-secret",
                DA_BOT_SECRET,
                86_400,
                Arc::new(StubDiscordExchange),
            ),
        )));

    // The browser's asserted identity still drives its own independent hosted
    // session. Telegram and Discord below must authenticate cryptographically
    // and cannot reuse this request because their receipt sessions differ.
    let game_path = format!("/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}");
    assert_eq!(
        response(
            &app,
            Request::builder()
                .uri(&game_path)
                .header("cookie", "dregg_user=exact-opening-trader")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .0,
        200
    );
    let operations_path = format!("{game_path}/operations");
    let (status, body) = response(
        &app,
        Request::builder()
            .uri(&operations_path)
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200);
    let body = String::from_utf8(body).unwrap();
    assert!(body.contains(DARK_AMM_SAME_OPENING_OPERATION));
    assert!(body.contains(DARK_AMM_SAME_OPENING_MEDIA_TYPE));
    assert!(body.contains(DARK_AMM_SAME_OPENING_DISCLOSURE));
    assert!(!body.contains(DARK_AMM_PROVED_OPERATION));

    for prefix in ["/tg", "/da"] {
        let route = format!(
            "{prefix}/offerings/{DARK_AMM_OFFERING_KEY}/session/{SESSION}/operations/{DARK_AMM_SAME_OPENING_OPERATION}"
        );
        assert_eq!(
            response(
                &app,
                Request::builder()
                    .method("POST")
                    .uri(route)
                    .header("content-type", DARK_AMM_SAME_OPENING_MEDIA_TYPE)
                    .body(Body::from(web_request.request.clone()))
                    .unwrap(),
            )
            .await
            .0,
            401
        );
    }

    let route = format!("{operations_path}/{DARK_AMM_SAME_OPENING_OPERATION}");
    let upload = || {
        Request::builder()
            .method("POST")
            .uri(&route)
            .header("content-type", DARK_AMM_SAME_OPENING_MEDIA_TYPE)
            .header("cookie", "dregg_user=exact-opening-trader")
            .body(Body::from(web_request.request.clone()))
            .unwrap()
    };
    let (status, receipt) = response(&app, upload()).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&receipt));
    let receipt: serde_json::Value = serde_json::from_slice(&receipt).unwrap();
    assert_eq!(
        receipt["publicFields"]["newRoot"].as_str(),
        Some(root_hex(&web_request.new_root).as_str())
    );
    assert!(receipt["publicFields"]["sameOpeningClaimDigest"].is_string());
    assert!(receipt["publicFields"]["proofDigest"].is_string());
    assert_eq!(response(&app, upload()).await.0, 409);

    let (_, game) = response(
        &app,
        Request::builder()
            .uri(game_path)
            .header("cookie", "dregg_user=exact-opening-trader")
            .body(Body::empty())
            .unwrap(),
    )
    .await;
    let game = String::from_utf8(game).unwrap();
    assert!(game.contains("Hiding + Tier-1 exact-opening receipts required"));
    assert!(game.contains("1 encrypted swap(s) accepted"));
    assert!(game.contains("n=1/opening-threshold=1"));

    // Telegram: mint a real HMAC-covered initData envelope, use it to open an
    // independent hosted session, and then land the complete owning v3 body.
    let tg_init_data = telegram_init_data(TG_UID);
    let tg_game_path = format!("/tg/offerings/{TG_OFFERING_KEY}/session/{TG_SESSION}");
    assert_eq!(
        response(
            &app,
            Request::builder()
                .uri(&tg_game_path)
                .header(INIT_DATA_HEADER, &tg_init_data)
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .0,
        200
    );

    // Discord: drive the actual /da/token handler through its injected OAuth
    // seam, then use only the production-minted bearer ticket below.
    let (status, token_body) = response(
        &app,
        Request::builder()
            .method("POST")
            .uri("/da/token")
            .header("content-type", "application/json")
            .body(Body::from(r#"{"code":"test-only-dark-pool-code"}"#))
            .unwrap(),
    )
    .await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&token_body));
    let token_body: serde_json::Value = serde_json::from_slice(&token_body).unwrap();
    let da_ticket = token_body["ticket"].as_str().unwrap().to_string();
    assert_eq!(
        token_body["access_token"].as_str(),
        Some("test-only-discord-access-token")
    );
    let da_game_path = format!("/da/offerings/{DA_OFFERING_KEY}/session/{DA_SESSION}");
    assert_eq!(
        response(
            &app,
            Request::builder()
                .uri(&da_game_path)
                .header(ACTIVITY_TICKET_HEADER, &da_ticket)
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .0,
        200
    );

    let tg_route = format!("{tg_game_path}/operations/{DARK_AMM_SAME_OPENING_OPERATION}");
    let da_route = format!("{da_game_path}/operations/{DARK_AMM_SAME_OPENING_OPERATION}");

    // Bearer formats are domain-separated in practice as well as by name: a
    // Telegram initData string cannot authenticate Discord and a Discord
    // ticket cannot authenticate Telegram. Both gates run before body parsing
    // or operation mutation.
    assert_eq!(
        response(
            &app,
            Request::builder()
                .method("POST")
                .uri(&da_route)
                .header(ACTIVITY_TICKET_HEADER, &tg_init_data)
                .header("content-type", DARK_AMM_SAME_OPENING_MEDIA_TYPE)
                .body(Body::from(da_request.request.clone()))
                .unwrap(),
        )
        .await
        .0,
        400
    );
    assert_eq!(
        response(
            &app,
            Request::builder()
                .method("POST")
                .uri(&tg_route)
                .header(INIT_DATA_HEADER, &da_ticket)
                .header("content-type", DARK_AMM_SAME_OPENING_MEDIA_TYPE)
                .body(Body::from(tg_request.request.clone()))
                .unwrap(),
        )
        .await
        .0,
        400
    );

    let tg_upload = || {
        Request::builder()
            .method("POST")
            .uri(&tg_route)
            .header(INIT_DATA_HEADER, &tg_init_data)
            .header("content-type", DARK_AMM_SAME_OPENING_MEDIA_TYPE)
            .body(Body::from(tg_request.request.clone()))
            .unwrap()
    };
    let (status, tg_receipt) = response(&app, tg_upload()).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&tg_receipt));
    let tg_receipt: serde_json::Value = serde_json::from_slice(&tg_receipt).unwrap();
    assert_eq!(
        tg_receipt["publicFields"]["newRoot"].as_str(),
        Some(root_hex(&tg_request.new_root).as_str())
    );
    assert_eq!(
        tg_receipt["publicFields"]["acceptedSwaps"].as_str(),
        Some("1")
    );
    assert_eq!(response(&app, tg_upload()).await.0, 409);

    let da_upload = || {
        Request::builder()
            .method("POST")
            .uri(&da_route)
            .header(ACTIVITY_TICKET_HEADER, &da_ticket)
            .header("content-type", DARK_AMM_SAME_OPENING_MEDIA_TYPE)
            .body(Body::from(da_request.request.clone()))
            .unwrap()
    };
    let (status, da_receipt) = response(&app, da_upload()).await;
    assert_eq!(status, 200, "{}", String::from_utf8_lossy(&da_receipt));
    let da_receipt: serde_json::Value = serde_json::from_slice(&da_receipt).unwrap();
    assert_eq!(
        da_receipt["publicFields"]["newRoot"].as_str(),
        Some(root_hex(&da_request.new_root).as_str())
    );
    assert_eq!(
        da_receipt["publicFields"]["acceptedSwaps"].as_str(),
        Some("1")
    );
    assert_eq!(response(&app, da_upload()).await.0, 409);

    for (offering, session) in [
        (DARK_AMM_OFFERING_KEY, SESSION),
        (TG_OFFERING_KEY, TG_SESSION),
        (DA_OFFERING_KEY, DA_SESSION),
    ] {
        let report = catalog
            .verify(offering, &SessionId::new(session))
            .expect("each player surface opened an independent Dark Pool session");
        assert!(report.verified, "{session}: {report:?}");
        assert_eq!(report.turns, 1, "{session}: exactly one v3 swap committed");
    }

    std::fs::remove_dir_all(dir).unwrap();
}
