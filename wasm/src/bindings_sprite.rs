//! **THE IN-HOUSE SPRITE, RENDERED IN THE TAB** — the deterministic generative
//! `content-addressed asset → SVG` renderer ([`dreggnet_sprite`]) exposed as a pair of
//! wasm getters. A [`dreggnet_asset::AssetId`] (a blake3 content address) is turned into a
//! composed vector SVG sprite by a PURE, deterministic function, so the browser paints the
//! *exact same bytes* a stranger re-renders off the same asset id.
//!
//! ## What is real here
//!
//! - [`sprite_svg`] (`spriteSvg(kind, assetIdHex)`) — the composed vector SVG string for an
//!   asset, `kind ∈ {"gear","card"}`. **Same asset ⇒ byte-identical SVG** (the whole point:
//!   anyone re-renders the identical art and can verify it); a different [`AssetId`] ⇒ a
//!   (near-certainly) different sprite. There are no floats/trig/unordered iteration in the
//!   renderer, so the string is a pure function of the trait vector on every platform.
//! - [`traits_json`] (`traitsJson(kind, assetIdHex)`) — the DERIVED trait vector as JSON
//!   (`{ kind, rarity: { name, tier }, fingerprint, axes: {…} }`). The traits are derived
//!   FROM the asset's content address via the real [`dregg_dice`](dregg_dice) draw stream
//!   (rarity by the committed provably-fair weighted draw), so "this is a legendary" is
//!   re-derivable, not a claim.
//!
//! Both are pure functions of the hex asset id + the kind — no keys, no state, no executor,
//! no networking. FAIL-CLOSED: a bad kind, non-hex, or wrong-length id is a `JsError` and NO
//! sprite (the renderer is never handed a half-decoded id).
//!
//! ## Honest scope — what this leg is NOT
//!
//! This is the **paint-the-sprite-in-tab** getter. It exposes the COMMITTED renderer
//! (`dreggnet-sprite/src/lib.rs`) — it does not modify it. Layered around it and NOT built
//! here: the `<dregg-sprite>` custom element that calls this getter and paints the SVG in a
//! closed shadow (the extension path, `extension/src/elements/dregg-sprite.ts`); the in-tree
//! deos `Tile{handle}` → sprite resolution (the web/native surface path — the wire that
//! resolves a card's opaque tile handle to this SVG, `deos-view/src/tree.rs:223`); the
//! first-class asset `trait_root` field (the named E1 pass); and richer art.
//!
//! ## PLATFORM NOTE
//!
//! `dreggnet-sprite`'s deps (`dreggnet-asset` → `dregg-schema`/`spween-dregg`/`dregg-cell`/
//! `dregg-app-framework`, `dregg-dice`, `blake3`) are all already in this graph and wasm32-
//! safe, so this module is in the shipped wasm32 bundle AND the native `cargo test` (the
//! tests below run natively under `cfg(not(target_arch = "wasm32"))`).

use wasm_bindgen::prelude::*;

use dreggnet_asset::AssetId;
use dreggnet_sprite::{AssetKind, card_traits, gear_traits, render};

/// Parse the sprite kind string into an [`AssetKind`] (fail-closed on any other value).
fn parse_kind(kind: &str) -> Result<AssetKind, String> {
    match kind {
        "gear" | "Gear" | "GEAR" => Ok(AssetKind::Gear),
        "card" | "Card" | "CARD" => Ok(AssetKind::Card),
        other => Err(format!(
            "unknown sprite kind {other:?} (expected \"gear\" or \"card\")"
        )),
    }
}

/// Decode a 32-byte [`AssetId`] from hex (an optional `0x` prefix is accepted). Fail-closed
/// on non-hex digits, an odd length, or the wrong number of bytes — no half-decoded id.
fn parse_asset_hex(asset_hex: &str) -> Result<AssetId, String> {
    let hex = asset_hex.strip_prefix("0x").unwrap_or(asset_hex);
    if hex.len() != 64 {
        return Err(format!(
            "asset id must be exactly 32 bytes (64 hex chars), got {} chars",
            hex.len()
        ));
    }
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("asset id is not valid hex: {e}"))?;
    }
    Ok(AssetId(bytes))
}

/// PRODUCER core: render the deterministic SVG for `(kind, asset_hex)`. `String` errors,
/// wasm-bindgen-free, so the fail-closed + determinism paths are testable NATIVELY.
pub(crate) fn sprite_svg_core(kind: &str, asset_hex: &str) -> Result<String, String> {
    let kind = parse_kind(kind)?;
    let asset = parse_asset_hex(asset_hex)?;
    Ok(render(kind, &asset))
}

/// PRODUCER core: the derived trait vector for `(kind, asset_hex)` as a canonical JSON
/// string. `String` errors, natively testable.
pub(crate) fn traits_json_core(kind: &str, asset_hex: &str) -> Result<String, String> {
    use serde_json::json;
    let k = parse_kind(kind)?;
    let asset = parse_asset_hex(asset_hex)?;
    let value = match k {
        AssetKind::Gear => {
            let t = gear_traits(&asset);
            json!({
                "kind": "gear",
                "rarity": { "name": t.rarity.name(), "tier": t.rarity.tier() },
                "fingerprint": t.fingerprint(),
                "axes": {
                    "blade": t.blade,
                    "material": t.material,
                    "rune": t.rune,
                    "guard": t.guard,
                    "notches": t.notches,
                    "gem": t.gem,
                    "mark": t.mark,
                },
            })
        }
        AssetKind::Card => {
            let t = card_traits(&asset);
            json!({
                "kind": "card",
                "rarity": { "name": t.rarity.name(), "tier": t.rarity.tier() },
                "fingerprint": t.fingerprint(),
                "axes": {
                    "frame": t.frame,
                    "emblem": t.emblem,
                    "palette": t.palette,
                    "pips": t.pips,
                    "accent": t.accent,
                },
            })
        }
    };
    Ok(value.to_string())
}

/// **The deterministic sprite SVG for an asset, IN THE TAB.** `kind` is `"gear"` or
/// `"card"`; `asset_id_hex` is the 32-byte [`AssetId`] as hex (an optional `0x` prefix is
/// accepted). Returns the composed vector SVG string — **same asset ⇒ byte-identical SVG**.
/// FAIL-CLOSED: a bad kind / non-hex / wrong-length id is a `JsError` and NO sprite.
#[wasm_bindgen(js_name = spriteSvg)]
pub fn sprite_svg(kind: &str, asset_id_hex: &str) -> Result<String, JsError> {
    sprite_svg_core(kind, asset_id_hex).map_err(|e| JsError::new(&e))
}

/// **The derived trait vector for an asset, IN THE TAB** — the JSON companion to
/// [`sprite_svg`]. Returns `{ kind, rarity: { name, tier }, fingerprint, axes: {…} }` — the
/// same trait vector that composes the SVG, re-derivable by anyone from the asset id.
/// FAIL-CLOSED on a bad kind / non-hex / wrong-length id.
#[wasm_bindgen(js_name = traitsJson)]
pub fn traits_json(kind: &str, asset_id_hex: &str) -> Result<String, JsError> {
    traits_json_core(kind, asset_id_hex).map_err(|e| JsError::new(&e))
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    /// Two distinct asset ids (arbitrary 32-byte content addresses, as hex).
    const ASSET_A: &str = "1111111111111111111111111111111111111111111111111111111111111111";
    const ASSET_B: &str = "2222222222222222222222222222222222222222222222222222222222222222";

    /// A well-formed SVG comes back for both kinds, and it is a REAL SVG document
    /// (opens `<svg`, closes `</svg>`).
    #[test]
    fn both_kinds_render_a_well_formed_svg() {
        for kind in ["gear", "card"] {
            let svg = sprite_svg_core(kind, ASSET_A)
                .unwrap_or_else(|e| panic!("{kind} must render: {e}"));
            assert!(svg.contains("<svg"), "{kind}: an <svg> root");
            assert!(
                svg.trim_end().ends_with("</svg>"),
                "{kind}: a closed </svg>"
            );
            assert!(svg.len() > 200, "{kind}: a composed, non-trivial sprite");
        }
    }

    /// DETERMINISM (the whole point): the same asset id ⇒ the BYTE-IDENTICAL SVG, across
    /// independent calls, for both kinds. A stranger re-renders the same bytes.
    #[test]
    fn same_asset_is_byte_identical() {
        for kind in ["gear", "card"] {
            let a1 = sprite_svg_core(kind, ASSET_A).unwrap();
            let a2 = sprite_svg_core(kind, ASSET_A).unwrap();
            assert_eq!(a1, a2, "{kind}: same asset ⇒ byte-identical SVG");
            // The `0x`-prefixed spelling of the same id is the same asset ⇒ same bytes.
            let a3 = sprite_svg_core(kind, &format!("0x{ASSET_A}")).unwrap();
            assert_eq!(a1, a3, "{kind}: the 0x-prefixed id is the SAME asset");
        }
    }

    /// A different asset id ⇒ a different sprite (the content address drives the art).
    #[test]
    fn different_asset_is_a_different_sprite() {
        for kind in ["gear", "card"] {
            let a = sprite_svg_core(kind, ASSET_A).unwrap();
            let b = sprite_svg_core(kind, ASSET_B).unwrap();
            assert_ne!(a, b, "{kind}: a different asset ⇒ a different sprite");
        }
    }

    /// The two KINDS render different art for the same asset id.
    #[test]
    fn gear_and_card_differ_for_the_same_asset() {
        let gear = sprite_svg_core("gear", ASSET_A).unwrap();
        let card = sprite_svg_core("card", ASSET_A).unwrap();
        assert_ne!(gear, card, "gear and card are distinct sprites");
    }

    /// The trait JSON is well-formed, carries the kind + a rarity {name,tier} + a
    /// fingerprint, and is DETERMINISTIC (same asset ⇒ same trait vector).
    #[test]
    fn traits_json_is_well_formed_and_deterministic() {
        for kind in ["gear", "card"] {
            let j1 =
                traits_json_core(kind, ASSET_A).unwrap_or_else(|e| panic!("{kind} traits: {e}"));
            let j2 = traits_json_core(kind, ASSET_A).unwrap();
            assert_eq!(j1, j2, "{kind}: same asset ⇒ same trait vector");
            let v: serde_json::Value = serde_json::from_str(&j1).expect("valid JSON");
            assert_eq!(v["kind"], serde_json::json!(kind));
            assert!(v["rarity"]["name"].is_string(), "a rarity name");
            assert!(v["rarity"]["tier"].is_u64(), "a rarity tier index");
            assert!(v["fingerprint"].is_string(), "a trait fingerprint");
            assert!(v["axes"].is_object(), "the trait axes");
        }
    }

    /// FAIL-CLOSED: a bad kind, non-hex, and wrong-length id each produce NO sprite.
    #[test]
    fn bad_input_fails_closed() {
        assert!(
            sprite_svg_core("wand", ASSET_A).is_err(),
            "unknown kind refused"
        );
        assert!(
            sprite_svg_core("gear", "not hex").is_err(),
            "non-hex refused"
        );
        assert!(
            sprite_svg_core("gear", "abcd").is_err(),
            "wrong length refused"
        );
        assert!(
            sprite_svg_core("gear", &"zz".repeat(32)).is_err(),
            "non-hex digits refused"
        );
        assert!(
            traits_json_core("wand", ASSET_A).is_err(),
            "traits: unknown kind refused"
        );
    }
}
