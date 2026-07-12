//! **The driven end-to-end proof** — a `TelegramFrontend` over the REAL `DungeonOffering`, DRIVEN
//! with a MOCK transport: NO Telegram token, NO network. It proves a Telegram user plays the SAME
//! offering core, on the SAME real substrate, as the Discord bot:
//!
//! - a Telegram user opens a session; the offering's [`Surface`] renders as a `sendMessage` with
//!   the RIGHT inline-keyboard payload (we assert the request shape the transport recorded);
//! - a button-press `CallbackQuery` collects the right typed [`Action`] + the presser's DERIVED
//!   dregg identity;
//! - the core [`Offering::advance`]s that action on the substrate → a REAL landed [`TurnReceipt`];
//! - an illegal move (a killing blow past the HP floor) is a real executor [`Outcome::Refused`] —
//!   nothing commits, no receipt (the anti-ghost tooth), same as on Discord;
//! - [`Offering::verify`] re-verifies the whole playthrough by replay.
//!
//! The transport is a [`MockTransport`] — the assertions are all against the request bodies it
//! recorded, which serialize to the exact Bot API `sendMessage` wire shape.

use dreggnet_offerings::dungeon::{DungeonOffering, KEEP_NAME, TURN_CHOOSE};
use dreggnet_offerings::{Frontend, Offering, Outcome, SessionConfig};
use dreggnet_telegram::api::{LOCK_GLYPH, decode_callback, encode_callback};
use dreggnet_telegram::transport::MockTransport;
use dreggnet_telegram::{CallbackQuery, ChatKind, TelegramFrontend};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON, KP_TRADE_BLOWS};

/// A deterministic bot secret for the tests (a real deploy loads 32 bytes from env).
const BOT_SECRET: [u8; 32] = [7u8; 32];

/// A DM chat (positive id) → single-player. Open a dungeon, present the opening surface, and
/// assert the recorded `sendMessage` carries the room text + an inline keyboard whose buttons ARE
/// the offering's cap-gated affordances (`callback_data == "choose:<idx>"`), one row each.
#[test]
fn present_renders_the_surface_as_an_inline_keyboard_of_affordances() {
    let off = DungeonOffering::new();
    let s = off
        .open(SessionConfig::with_seed(3))
        .expect("the Keep opens");

    let mut fe = TelegramFrontend::new(BOT_SECRET, MockTransport::new());
    let chat_id: i64 = 424242; // a positive chat id → a DM.
    let sid = TelegramFrontend::<MockTransport>::session_id(chat_id, None);
    fe.spin_session(sid.clone());
    assert_eq!(
        fe.session(&sid).unwrap().kind,
        ChatKind::Dm,
        "a positive chat id is single-player"
    );

    let surface = off.render(&s);
    let actions = off.actions(&s);
    fe.present(&sid, &surface, &actions);
    assert!(fe.last_send_error().is_none(), "the mock send succeeds");

    let req = fe.transport().last().expect("a sendMessage was recorded");
    assert_eq!(req.chat_id, chat_id, "sent to the session's chat");
    assert_eq!(req.message_thread_id, None, "a DM has no forum topic");
    assert!(
        req.text.contains(KEEP_NAME),
        "the message text names the Keep + room: {:?}",
        req.text
    );

    let kb = req
        .reply_markup
        .as_ref()
        .expect("the surface's affordances render as an inline keyboard");
    assert_eq!(
        kb.inline_keyboard.len(),
        actions.len(),
        "one keyboard row per cap-gated affordance"
    );
    // Every affordance's button carries its {turn,arg} as callback_data, decodable back.
    for (row, act) in kb.inline_keyboard.iter().zip(actions.iter()) {
        assert_eq!(row.len(), 1, "one button per row (the vertical Menu shape)");
        let btn = &row[0];
        assert_eq!(
            btn.callback_data,
            encode_callback(&act.turn, act.arg),
            "the button carries the affordance {{turn, arg}}"
        );
        assert_eq!(
            decode_callback(&btn.callback_data),
            Some((act.turn.clone(), act.arg))
        );
    }

    // The ungated press-on affordance is present + enabled → no lock glyph on its label.
    let press_btn = kb
        .inline_keyboard
        .iter()
        .flatten()
        .find(|b| b.callback_data == encode_callback(TURN_CHOOSE, KP_PRESS_ON as i64))
        .expect("the press-on affordance is on the keyboard");
    assert!(
        !press_btn.text.starts_with(LOCK_GLYPH),
        "an enabled affordance is not dimmed"
    );
}

/// The full frontend-agnostic lifecycle on Telegram: present → a `CallbackQuery` press collects the
/// typed [`Action`] + the presser's DERIVED identity → the CORE resolves it on the substrate as ONE
/// real turn (a genuine [`TurnReceipt`]) → the world advances → re-present → verify by replay →
/// teardown. The SAME `DungeonOffering` the Discord frontend drives — asserted.
#[test]
fn a_telegram_button_press_lands_a_real_turnreceipt_through_the_core() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(9)).expect("open");
    assert_eq!(s.current_passage_name().as_deref(), Some("gatehall"));
    assert_eq!(s.receipts_len(), 1, "genesis is the first verified turn");

    let mut fe = TelegramFrontend::new(BOT_SECRET, MockTransport::new());
    let chat_id: i64 = -1001234; // a supergroup id (negative) → a collective.
    let sid = TelegramFrontend::<MockTransport>::session_id(chat_id, None);
    fe.spin_session(sid.clone());
    assert_eq!(
        fe.session(&sid).unwrap().kind,
        ChatKind::Group,
        "a negative chat id is a collective (group)"
    );

    fe.present(&sid, &off.render(&s), &off.actions(&s));

    // A Telegram user "presses" the press-on button — a real callback query, no network.
    let press_data = encode_callback(TURN_CHOOSE, KP_PRESS_ON as i64);
    let ev = CallbackQuery::press(chat_id, 555_000_111, press_data);
    let (got_sid, action, actor) = fe
        .collect(ev)
        .expect("a press maps back to a presented affordance");
    assert_eq!(got_sid, sid, "the press resolves to its session");
    assert_eq!(
        action.arg, KP_PRESS_ON as i64,
        "the typed action is press-on"
    );
    assert_eq!(action.turn, TURN_CHOOSE);
    assert_eq!(
        actor,
        fe.identity(555_000_111),
        "the presser's derived dregg identity attributes the move"
    );
    // The derived identity is a real Ed25519 public-key hex (32 bytes → 64 hex chars).
    assert_eq!(actor.as_str().len(), 64, "a real Ed25519 pubkey hex handle");
    assert!(actor.as_str().chars().all(|c| c.is_ascii_hexdigit()));

    // THE CORE resolves the collected action on the REAL substrate — one real turn.
    match off.advance(&mut s, action, actor.clone()) {
        Outcome::Landed { receipt, ended } => {
            assert!(!ended, "pressing on does not end the Keep");
            assert_ne!(
                receipt.turn_hash, [0u8; 32],
                "a genuine committed turn hash"
            );
        }
        other => panic!("a legal Telegram move must land a real receipt, got {other:?}"),
    }
    assert_eq!(
        s.receipts_len(),
        2,
        "a real verified turn landed from Telegram"
    );
    assert_eq!(
        s.current_passage_name().as_deref(),
        Some("hall"),
        "the world advanced to the plundered hall"
    );
    assert_eq!(
        s.actor_of_step(0),
        Some(&actor),
        "the Telegram presser is attributed"
    );

    // Re-present the advanced room, claim the crown via another press, verify, teardown.
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let claim_data = encode_callback(TURN_CHOOSE, KP_CLAIM_RED as i64);
    let (_sid, claim, actor2) = fe
        .collect(CallbackQuery::press(chat_id, 555_000_111, claim_data))
        .expect("claim-red is on the hall keyboard");
    assert!(
        off.advance(&mut s, claim, actor2).landed(),
        "claiming the crown lands a real turn"
    );
    assert_eq!(s.receipts_len(), 3);

    let report = off.verify(&s);
    assert!(
        report.verified,
        "the Telegram playthrough re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 3);

    fe.teardown(&sid);
    assert!(
        fe.session(&sid).is_none(),
        "teardown archives the session surface"
    );
}

/// An illegal move on Telegram is a REAL executor refusal (the anti-ghost tooth), identical to
/// Discord: at low HP the trade-blows affordance is a dimmed cap-tooth (its button is
/// [`LOCK_GLYPH`]-prefixed but still pressable), and firing it through the core commits nothing —
/// no receipt, the world does not move. The honest prefix still re-verifies.
#[test]
fn an_illegal_telegram_press_is_refused_no_receipt_anti_ghost() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(8)).expect("open");

    let mut fe = TelegramFrontend::new(BOT_SECRET, MockTransport::new());
    let chat_id: i64 = 900900;
    let sid = TelegramFrontend::<MockTransport>::session_id(chat_id, None);
    fe.spin_session(sid.clone());

    let blow_data = encode_callback(TURN_CHOOSE, KP_TRADE_BLOWS as i64);

    // Two survivable trade-blows (hp 50 → 30 → 10), each collected + landed via the frontend.
    for _ in 0..2 {
        fe.present(&sid, &off.render(&s), &off.actions(&s));
        let (_sid, blow, actor) = fe
            .collect(CallbackQuery::press(chat_id, 42, blow_data.clone()))
            .expect("trade-blows is on the keyboard");
        assert!(
            off.advance(&mut s, blow, actor).landed(),
            "a survivable blow lands"
        );
    }
    assert_eq!(s.read_var("hp"), 10, "two blows dropped hp to 10");
    let before = s.receipts_len();

    // At hp 10 the trade-blows affordance is now a dimmed cap-tooth: present it and confirm its
    // button is lock-prefixed but STILL on the keyboard (shown, not hidden).
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    let req = fe.transport().last().unwrap();
    let blow_btn = req
        .reply_markup
        .as_ref()
        .unwrap()
        .inline_keyboard
        .iter()
        .flatten()
        .find(|b| b.callback_data == blow_data)
        .expect("the killing-blow affordance is still offered (dimmed)");
    assert!(
        blow_btn.text.starts_with(LOCK_GLYPH),
        "the ineligible affordance is a dimmed cap-tooth: {:?}",
        blow_btn.text
    );

    // Press it anyway — the frontend collects it (the executor is the sole referee, not the button
    // state), and the REAL executor refuses on advance: nothing commits.
    let (_sid, blow, actor) = fe
        .collect(CallbackQuery::press(chat_id, 42, blow_data))
        .expect("a dimmed affordance is still collectable (anti-ghost is the executor's job)");
    match off.advance(&mut s, blow, actor) {
        Outcome::Refused(_) => {}
        other => panic!("a killing blow must be a real executor refusal, got {other:?}"),
    }
    assert_eq!(
        s.receipts_len(),
        before,
        "no receipt landed for the refused move"
    );
    assert_eq!(s.read_var("hp"), 10, "hp unchanged after the refusal");
    assert_eq!(
        s.current_passage_name().as_deref(),
        Some("gatehall"),
        "the world did not move"
    );
    assert!(
        off.verify(&s).verified,
        "the honest prefix re-verifies after the refusal"
    );
}

/// Identity derivation is deterministic + distinct per user, and a forum-topic session is a
/// collective scoped to one topic thread (a topic-per-session in one supergroup). Also: the
/// frontend refuses to collect an affordance it never presented.
#[test]
fn identity_is_deterministic_forum_topics_scope_sessions_and_unpresented_is_refused() {
    let mut fe = TelegramFrontend::new(BOT_SECRET, MockTransport::new());

    // Deterministic + distinct.
    assert_eq!(
        fe.identity(1001),
        fe.identity(1001),
        "same user → same identity"
    );
    assert_ne!(
        fe.identity(1001),
        fe.identity(1002),
        "distinct users → distinct identities"
    );

    // A forum topic scopes a session under one thread.
    let chat_id: i64 = -1009999;
    let sid = TelegramFrontend::<MockTransport>::session_id(chat_id, Some(77));
    fe.spin_session(sid.clone());
    let slot = fe.session(&sid).unwrap();
    assert_eq!(
        slot.kind,
        ChatKind::ForumTopic,
        "a topic thread is a scoped collective"
    );
    assert_eq!(slot.message_thread_id, Some(77));
    // Round-trips: chat_of recovers the chat + topic from the session id.
    assert_eq!(
        TelegramFrontend::<MockTransport>::chat_of(&sid),
        Some((chat_id, Some(77)))
    );

    // Nothing real presented yet (spin only) → a press collects None.
    let ev = CallbackQuery::press_in_topic(chat_id, 77, 3, encode_callback(TURN_CHOOSE, 0));
    assert!(
        fe.collect(ev).is_none(),
        "an unpresented affordance is not collected"
    );
}
