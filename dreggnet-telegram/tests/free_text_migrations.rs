//! **The FREE-TEXT migration proofs — the three never-migrated offerings (hermes, names, compute)
//! plus the doc's newly-SELECTABLE text slot, all driven in-chat over [`MockTransport`].**
//!
//! Before this wave, three offerings solicited a value that only a free-text message can carry, but
//! the in-chat router had no way to deliver it: a Hermes prompt was dropped (the brain classified
//! the affordance VERB), a names register registered the literal button label, a compute settle was
//! impossible (its result text was always `None`), and the document was silently append-only (the
//! router always chose the FIRST text affordance). Each is closed by the `taking_text` +
//! `input.text` migration on the offering, plus the SELECTABLE-arm routing in the host.
//!
//! The proof shape per offering: ARM the text affordance (a press), send a plain-text message, and
//! confirm it REACHES the offering (a real executor verdict), plus the negative — with nothing
//! armed, plain text is Ignored (never swallowed).

use dreggnet_offerings::Outcome;
use dreggnet_telegram::CallbackQuery;
use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::runtime::{PressDecision, TextDecision, route_text_decided};
use dreggnet_telegram::transport::MockTransport;

const BOT_SECRET: [u8; 32] = [21u8; 32];
const ALICE: u64 = 4001;
const BOB: u64 = 4002;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[])
}

/// Assert that a chat with `key` open, but nothing armed, IGNORES a plain-text message (no greedy
/// capture) — the shared negative every migrated offering must satisfy.
fn assert_unarmed_ignores(h: &mut TelegramHost<MockTransport>, key: &str, chat: i64, uid: u64) {
    h.open(key, chat, None, uid).expect("opens");
    let (reply, decision) = route_text_decided(h, chat, None, uid, "just some chatter");
    assert!(
        matches!(decision, TextDecision::Ignored),
        "{key}: with nothing armed, plain text must be Ignored, got {decision:?}",
    );
    assert!(reply.is_none(), "{key}: ignored chatter draws no reply");
}

// ─────────────────────────────────────────────────────────────────────────────
// HERMES — a prompt is free text; arming the prompt routes the typed message to the brain.
// ─────────────────────────────────────────────────────────────────────────────

/// A Hermes PROMPT is a `taking_text` affordance: arming it and typing a message drives ONE real
/// confined, metered turn on the substrate — a genuine `TurnReceipt`. (Before the migration the
/// brain classified the affordance VERB "prompt", never the user's words.)
#[test]
fn hermes_prompt_routes_typed_text_to_a_real_turn() {
    let mut h = host();
    let chat: i64 = 5001;
    let sid = h.open("hermes", chat, None, ALICE).expect("hermes opens");

    // The Hermes surface presents one prompt affordance per tool class, each soliciting text.
    let prompt = h
        .frontend()
        .session(&sid)
        .and_then(|s| s.presented.iter().find(|a| a.wants_text).cloned())
        .expect("hermes presents a text-soliciting prompt affordance");

    // Arm it (a press on a text template arms, it does not advance).
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback(&prompt.turn, prompt.arg),
    )) {
        HostPress::TextArmed { key, .. } => assert_eq!(key, "hermes"),
        other => panic!("arming a Hermes prompt must TextArm, got {other:?}"),
    }

    // Type the actual prompt — it reaches the confined agent and LANDS one real metered turn
    // (a fresh session has head-room for any class, so the first turn commits deterministically).
    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "read notes.txt");
    match decision {
        TextDecision::TextInput {
            press: PressDecision::Landed { key, .. },
        } => assert_eq!(
            key, "hermes",
            "the typed prompt landed a real confined turn"
        ),
        other => panic!("the typed prompt must land a real turn, got {other:?}"),
    }
    assert!(reply.is_some(), "the confined turn produced a verdict");
}

/// Negative: hermes open, nothing armed → plain text is Ignored.
#[test]
fn hermes_open_but_unarmed_ignores_chatter() {
    let mut h = host();
    assert_unarmed_ignores(&mut h, "hermes", 5009, ALICE);
}

// ─────────────────────────────────────────────────────────────────────────────
// NAMES — a name is free text; arming register routes the typed name (not the button label).
// ─────────────────────────────────────────────────────────────────────────────

/// A names REGISTER is a `taking_text` affordance: arming it and typing a name routes THAT name to
/// the offering (before the migration a press registered the decorated button label
/// "register a free name"). Reaching the offering is the executor's verdict.
#[test]
fn names_register_routes_the_typed_name_to_the_offering() {
    let mut h = host();
    let chat: i64 = 5101;
    let sid = h.open("names", chat, None, ALICE).expect("names opens");

    // The register affordance solicits text.
    let register = h
        .frontend()
        .session(&sid)
        .and_then(|s| s.presented.iter().find(|a| a.turn == "register").cloned())
        .expect("names presents a register affordance");
    assert!(register.wants_text, "register solicits the name as text");

    // Arm it, then type the bare name.
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("register", register.arg),
    )) {
        HostPress::TextArmed { key, .. } => assert_eq!(key, "names"),
        other => panic!("arming register must TextArm, got {other:?}"),
    }
    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "alice.dregg");
    match decision {
        TextDecision::TextInput { .. } => {}
        other => panic!("the typed name must route as TextInput, got {other:?}"),
    }
    // It reached the offering (a real executor verdict came back — the register was ATTEMPTED with
    // the typed name, not silently dropped and not the literal button label).
    assert!(reply.is_some(), "the register attempt produced a verdict");
}

/// Negative: names open, nothing armed → plain text is Ignored.
#[test]
fn names_open_but_unarmed_ignores_chatter() {
    let mut h = host();
    assert_unarmed_ignores(&mut h, "names", 5109, ALICE);
}

// ─────────────────────────────────────────────────────────────────────────────
// COMPUTE — the settle RESULT is free text; without taking_text the settle is impossible in-chat.
// ─────────────────────────────────────────────────────────────────────────────

/// The compute SETTLE folds the worker's RESULT onto its text payload. With the settle affordance
/// now `taking_text`, an in-chat settle is possible: post → claim → ARM settle → type the result →
/// the escrow settles conserved (a real ended turn). Before the migration the result was always
/// `None` and the settle hard-refused — impossible in-chat.
#[test]
fn compute_settle_routes_the_typed_result_and_settles() {
    let mut h = host();
    let chat: i64 = 5201;
    let sid = h.open("compute", chat, None, ALICE).expect("compute opens");

    // POST (requester ALICE escrows budget 1000) and CLAIM (worker BOB at 800) — value-taking
    // presses carry their value in the callback arg (no text needed).
    assert!(
        matches!(
            h.press(CallbackQuery::press(
                chat,
                ALICE,
                encode_callback("post", 1000)
            )),
            HostPress::Advanced {
                outcome: Outcome::Landed { .. },
                ..
            }
        ),
        "the post lands",
    );
    assert!(
        matches!(
            h.press(CallbackQuery::press(
                chat,
                BOB,
                encode_callback("claim", 800)
            )),
            HostPress::Advanced {
                outcome: Outcome::Landed { .. },
                ..
            }
        ),
        "the claim lands",
    );

    // ARM settle (a press on the now-enabled `taking_text` settle affordance).
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("settle", 0),
    )) {
        HostPress::TextArmed { key, .. } => assert_eq!(key, "compute"),
        other => panic!("arming settle must TextArm (it carries the result text), got {other:?}"),
    }

    // The requester types the worker's RESULT — the settle now has its text and releases the escrow.
    match h.press_text(chat, None, ALICE, "blake3:rendered-frame-batch-ok") {
        HostPress::Advanced {
            key,
            outcome: Outcome::Landed { ended, .. },
        } => {
            assert_eq!(key, "compute");
            assert!(ended, "a settle ends the session");
        }
        other => panic!("the typed result must settle the escrow, got {other:?}"),
    }

    let report = h
        .verify("compute", &sid)
        .expect("compute exposes a verifier");
    assert!(
        report.verified && report.turns == 3,
        "post + claim + settle all verify: {} turns, {}",
        report.turns,
        report.detail,
    );
}

/// Negative: compute open (a bare post-only surface), nothing armed → plain text is Ignored.
#[test]
fn compute_open_but_unarmed_ignores_chatter() {
    let mut h = host();
    assert_unarmed_ignores(&mut h, "compute", 5209, ALICE);
}

// ─────────────────────────────────────────────────────────────────────────────
// DOC — the SELECTABLE fix: a non-first text affordance (set-title) is now reachable.
// ─────────────────────────────────────────────────────────────────────────────

/// The document presents FOUR text affordances (insert-at-tip, insert-at-start, set-title, and —
/// on a clash — resolve-title). The old router always chose the FIRST (insert), making the document
/// silently append-only. Now each is SELECTABLE by pressing it: arming `set_title` makes THAT the
/// pending text slot (not insert), so a typed value reaches set-title.
#[test]
fn doc_set_title_is_selectable_not_just_the_first_insert() {
    let mut h = host();
    let chat: i64 = 5301;
    let sid = h.open("doc", chat, None, ALICE).expect("doc opens");

    // set-title is present and distinct from insert.
    let set_title = h
        .frontend()
        .session(&sid)
        .and_then(|s| s.presented.iter().find(|a| a.turn == "set_title").cloned())
        .expect("the document presents a set-title affordance");
    assert!(set_title.wants_text);

    // Arm set-title (NOT insert) — the selectable fix.
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("set_title", set_title.arg),
    )) {
        HostPress::TextArmed { key, action } => {
            assert_eq!(key, "doc");
            assert_eq!(
                action.turn, "set_title",
                "the ARMED slot is set-title, not the first insert (the append-only bug is fixed)",
            );
        }
        other => panic!("arming set-title must TextArm it, got {other:?}"),
    }

    // The pending text slot is now set-title (the old find-first always returned insert).
    let pending = h.pending_text_action(&sid).expect("set-title is armed");
    assert_eq!(
        pending.turn, "set_title",
        "the pending text slot is the SELECTED one"
    );

    // A typed value reaches the set-title path (a real executor verdict — reached the offering).
    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "The Dragon's Ledger");
    match decision {
        TextDecision::TextInput { .. } => {}
        other => panic!("the typed title must route as TextInput to set-title, got {other:?}"),
    }
    assert!(
        reply.is_some(),
        "set-title produced a verdict (reached the offering)"
    );
}

/// Negative: doc open, nothing armed → plain text is Ignored (already covered structurally in
/// `free_text_routing.rs`; repeated here so each migrated surface carries its own negative).
#[test]
fn doc_open_but_unarmed_ignores_chatter() {
    let mut h = host();
    assert_unarmed_ignores(&mut h, "doc", 5309, ALICE);
}
