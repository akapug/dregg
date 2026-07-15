//! **The deterministic sprite art surface — driven.**
//!
//! `dreggnet-web` serves `dreggnet-sprite`'s byte-identical `AssetId → SVG` art: an
//! `image/svg+xml` endpoint, a `Tile{handle}` painter, and a gallery. This drives all three
//! through the real merged app (axum `oneshot`) + the pure functions, and pins the house norm the
//! whole thing rides: **same asset ⇒ byte-identical SVG**.

use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_web::sprite::AssetKind;
use dreggnet_web::{make_app, sprite};
use tower::ServiceExt;

async fn get(app: &axum::Router, uri: &str) -> (StatusCode, String, String) {
    let resp = app
        .clone()
        .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
        .await
        .unwrap();
    let status = resp.status();
    let ctype = resp
        .headers()
        .get(axum::http::header::CONTENT_TYPE)
        .and_then(|v| v.to_str().ok())
        .unwrap_or("")
        .to_string();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    (status, ctype, String::from_utf8_lossy(&bytes).to_string())
}

/// The core house norm: the same `(kind, reference)` renders byte-identical SVG, every time.
#[test]
fn same_asset_renders_byte_identical_svg() {
    let a = sprite::svg_for(AssetKind::Gear, "warden-blade");
    let b = sprite::svg_for(AssetKind::Gear, "warden-blade");
    assert_eq!(a, b, "a sprite must be a pure function of its asset ref");
    assert!(a.contains("<svg"), "the render is an SVG document");
    // A different reference gives (near-certainly) different art.
    let c = sprite::svg_for(AssetKind::Gear, "hoard-key");
    assert_ne!(a, c, "distinct asset refs give distinct sprites");
}

/// A 64-hex reference is decoded verbatim; a friendly label hashes to a stable address — both yield
/// a fixed asset, and the hex round-trips through `asset_ref`.
#[test]
fn asset_ref_resolves_hex_verbatim_and_labels_stably() {
    let hex = "11".repeat(32); // 64 hex chars -> [0x11; 32]
    let id = sprite::asset_ref(&hex);
    assert_eq!(id.bytes(), [0x11u8; 32], "a 64-hex ref decodes verbatim");
    // A label is stable across calls.
    assert_eq!(
        sprite::asset_ref("council-sigil").bytes(),
        sprite::asset_ref("council-sigil").bytes(),
        "a label maps deterministically to one address"
    );
}

/// `parse_kind` recognises the two kinds + synonyms and rejects nonsense.
#[test]
fn kind_parsing() {
    assert!(matches!(sprite::parse_kind("gear"), Some(AssetKind::Gear)));
    assert!(matches!(sprite::parse_kind("CARD"), Some(AssetKind::Card)));
    assert!(sprite::parse_kind("bogus").is_none());
}

/// `GET /sprite/{kind}/{ref}` serves the deterministic SVG as `image/svg+xml`; an unknown kind 404s.
#[tokio::test]
async fn sprite_endpoint_serves_svg() {
    let app = make_app();
    let (status, ctype, body) = get(&app, "/sprite/gear/warden-blade").await;
    assert_eq!(status, StatusCode::OK);
    assert!(ctype.starts_with("image/svg+xml"), "content-type: {ctype}");
    assert!(body.contains("<svg"), "an SVG document");
    // The endpoint is byte-stable: a second fetch is identical.
    let (_, _, body2) = get(&app, "/sprite/gear/warden-blade").await;
    assert_eq!(body, body2);
    // The same asset ref under a different kind renders a distinct sprite.
    let (_, _, card) = get(&app, "/sprite/card/warden-blade").await;
    assert_ne!(body, card);
    // An unknown kind 404s.
    let (status, _, _) = get(&app, "/sprite/nope/warden-blade").await;
    assert_eq!(status, StatusCode::NOT_FOUND);
}

/// `GET /gallery` renders the deterministic art grid (a live SVG per cell).
#[tokio::test]
async fn gallery_renders() {
    let app = make_app();
    let (status, _, body) = get(&app, "/gallery").await;
    assert_eq!(status, StatusCode::OK);
    assert!(body.contains("sprite-grid"), "the gallery grid is present");
    assert!(body.contains("<svg"), "each cell is a live SVG");
    assert!(body.contains("warden-blade"), "a known asset label shows");
}

/// A `Tile{handle}` whose handle names an asset paints as the inline SVG sprite; an explicit kind in
/// the handle is honoured; an empty handle yields no sprite (the caller falls back).
#[test]
fn tile_handle_painting() {
    // Explicit kind.
    let gear = sprite::tile_html("sprite:gear:warden-blade", 96, 96).expect("gear tile");
    assert!(gear.contains("<svg"));
    assert!(gear.contains("sprite-tile"));
    // A bare ref defaults to a card sprite.
    let bare = sprite::tile_html("council-sigil", 96, 96).expect("bare tile");
    assert!(bare.contains("<svg"));
    // The explicit-kind gear differs from the default-card bare render of the same ref.
    let gear_ref = sprite::tile_html("sprite:gear:council-sigil", 96, 96).expect("gear tile");
    assert_ne!(gear_ref, bare, "kind selects distinct art for one ref");
    // An empty handle names no asset.
    assert!(sprite::tile_html("", 96, 96).is_none());
}
