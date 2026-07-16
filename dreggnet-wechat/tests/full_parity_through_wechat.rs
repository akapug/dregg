//! **The driven FULL-PORTFOLIO parity proof — WeChat registers the SAME 18 offerings the web catalog
//! does, and the viewer threads through the OA surface.**
//!
//! `multi_offering_through_wechat.rs` proved THREE heterogeneous offerings play through the WeChat OA
//! numbered-reply surface. This closes the gap the audit found: WeChat registered only three while
//! the web catalog ([`dreggnet_web::demo_host`]) registers eighteen — automatafl, multiway-tug, and
//! the eight do-once RPG feature surfaces were ABSENT because their crates were not deps. Now
//! [`wechat_default_host`] deps them and registers the full set, AND `present_room` threads the
//! participant's derived identity through the viewer-aware `render_for`/`actions_for`. This drives:
//!
//! - **all 18 offering keys are registered** on the WeChat host (the exact gap);
//! - a newly-registered game (**automatafl**) is REACHABLE and renders a NON-EMPTY OA message (a
//!   CoordGrid board degrades to a text grid on the text-only OA renderer — expected, not a silent
//!   drop);
//! - the **multiway-tug hidden hand** threads the viewer: two participants over a shared room each
//!   see THEIR OWN card ids, and the two hands DIFFER — per-viewer discrimination on the OA surface,
//!   the `hidden_hand_web.rs` shape (before the fix, `present_room` painted the viewer-blind fog to
//!   everyone);
//! - a real turn drives through a newly-registered game (tug's opening `comp` lands a receipt), and
//!   the committed chain re-verifies.

use dreggnet_offerings::SessionId;
use dreggnet_wechat::host::{WeChatHost, WeChatReply};
use dreggnet_wechat::transport::MockTransport;
use dreggnet_wechat::{WeChatFrontend, WeChatMessage};

const BOT_SECRET: [u8; 32] = [7u8; 32];
const ALICE: &str = "oALICE_wechat_openid";
const BOB: &str = "oBOB_wechat_openid";

/// The full 18-offering set the web catalog registers (`dreggnet_web::demo_host`).
const EXPECTED_KEYS: [&str; 18] = [
    "dungeon",
    "council",
    "market",
    "tug",
    "automatafl",
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "tavern",
    "party",
    "doc",
    "names",
    "compute",
    "grain",
    "hermes",
];

fn host() -> WeChatHost<MockTransport> {
    WeChatHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// The OA message content currently on `openid`'s conversation (the surface last presented to them).
fn surface_content(h: &WeChatHost<MockTransport>, openid: &str) -> String {
    let psid = WeChatFrontend::<MockTransport>::session_id(openid);
    h.frontend()
        .session(&psid)
        .expect("a surface is presented to this participant")
        .presented
        .content
        .clone()
}

/// The 1-based number of the first numbered option on `openid`'s current surface (the first
/// affordance the user can reply). Panics if the surface offers nothing.
fn first_option_number(h: &WeChatHost<MockTransport>, openid: &str) -> String {
    let psid = WeChatFrontend::<MockTransport>::session_id(openid);
    let slot = h.frontend().session(&psid).expect("a surface is presented");
    slot.presented
        .options
        .first()
        .expect("the surface offers at least one affordance")
        .index
        .to_string()
}

/// **All 18 offerings the web catalog registers are registered on the WeChat host** — the exact gap
/// the audit found (automatafl, multiway-tug, and the eight RPG surface keys were absent).
#[test]
fn the_wechat_host_registers_the_full_eighteen_offering_portfolio() {
    let h = host();
    let offs = h.list_offerings();
    let keys: Vec<&str> = offs.iter().map(|o| o.key.as_str()).collect();
    for want in EXPECTED_KEYS {
        assert!(
            keys.contains(&want),
            "offering `{want}` is registered on WeChat (full web parity): {keys:?}"
        );
    }
    assert!(
        offs.len() >= EXPECTED_KEYS.len(),
        "the host lists at least the 18 portfolio offerings: {} < {}",
        offs.len(),
        EXPECTED_KEYS.len()
    );
}

/// A newly-registered game (**automatafl**) is REACHABLE through the WeChat host and renders a
/// NON-EMPTY OA message — the CoordGrid board degrades to a text grid on the text-only OA renderer
/// (expected), NOT a silent empty. A reply drives one turn through the substrate + re-renders.
#[test]
fn automatafl_is_reachable_and_renders_a_non_empty_surface_on_wechat() {
    let mut h = host();
    h.open("automatafl", ALICE)
        .expect("automatafl opens on WeChat");
    assert_eq!(h.active_offering(ALICE), Some("automatafl"));

    let content = surface_content(&h, ALICE);
    assert!(
        !content.trim().is_empty(),
        "the automatafl board renders a non-empty (degraded-to-text) OA message, not a silent drop: {content:?}"
    );

    // Drive one turn: reply the first affordance the board offers (a `select` on a movable piece).
    let n = first_option_number(&h, ALICE);
    match h.reply(WeChatMessage::text(ALICE, n)) {
        WeChatReply::Advanced { key, .. } => {
            assert_eq!(
                key, "automatafl",
                "the reply drove the automatafl substrate"
            );
            assert!(
                !surface_content(&h, ALICE).trim().is_empty(),
                "the board re-renders a non-empty surface after the turn"
            );
        }
        other => panic!("an automatafl reply should advance the substrate, got {other:?}"),
    }
}

/// **The multiway-tug hidden hand threads the viewer on the WeChat OA surface.** Two participants
/// over a shared room each claim a seat by playing; `present_room` projects each re-render FOR the
/// participant's derived identity (`render_for`), so each sees THEIR OWN card ids — and the two hands
/// DIFFER. A seated player never sees the opponent's cards (fog). This is the `hidden_hand_web.rs`
/// shape on the OA surface: per-viewer discrimination, driven end-to-end.
#[test]
fn the_tug_hidden_hand_threads_the_viewer_on_wechat() {
    let mut h = host();
    let room = SessionId::new("wx-tug-room");

    // ALICE joins the shared tug room, then plays the opening Competition — claims seat A, lands, and
    // `present_room` re-renders FOR alice: her own hand is revealed on her OA message. A joiner holds
    // no seat yet, so her surface is the spectator fog (no action menu); she claims a seat with the
    // `#<turn>:<arg>` MARKED reply (the Mini-Program-button path — a marked id fires even when it is
    // not a numbered option, the executor gating it), exactly the shape the market `#list`/`#bid`
    // value replies take.
    h.join("tug", &room, ALICE).expect("ALICE joins the tug");
    let alice_reply = h.reply(WeChatMessage::text(ALICE, "#comp:3"));
    assert!(
        matches!(alice_reply, WeChatReply::Advanced { ref outcome, .. } if outcome.landed()),
        "alice's opening comp lands + claims seat A: {alice_reply:?}"
    );
    let alice_content = surface_content(&h, ALICE);
    assert!(
        !alice_content.trim().is_empty(),
        "the tug surface for the seated player is non-empty (not a silent drop)"
    );
    assert!(
        alice_content.contains("Your hand") && alice_content.contains("card #"),
        "seat A (alice) sees HER OWN card ids on her OA message: {alice_content}"
    );
    assert!(
        alice_content.contains("Opponent (hidden hand)"),
        "the opponent's hand stays fog for the seated viewer: {alice_content}"
    );

    // BOB joins and replies a move — claims seat B; `present_room` re-renders FOR bob: his own,
    // DIFFERENT hand. (The reply may land or be a real turn-order refusal — either way the seat is
    // claimed and the surface re-renders AS bob, the viewer-thread we assert.)
    h.join("tug", &room, BOB).expect("BOB joins the tug");
    let _ = h.reply(WeChatMessage::text(BOB, "#secret:0"));
    let bob_content = surface_content(&h, BOB);
    assert!(
        bob_content.contains("Your hand") && bob_content.contains("card #"),
        "seat B (bob) sees HIS OWN card ids on his OA message: {bob_content}"
    );
    assert_ne!(
        alice_content, bob_content,
        "the viewer threaded: alice's seat-A hand and bob's seat-B hand render DIFFERENTLY \
         (per-viewer discrimination, not the viewer-blind fog everyone shared before the fix)"
    );

    // The committed chain re-verifies by replay — a real driven turn through a newly-registered game.
    let report = h.verify("tug", &room).expect("the tug session is live");
    assert!(
        report.verified,
        "the tug chain re-verifies: {}",
        report.detail
    );
}
