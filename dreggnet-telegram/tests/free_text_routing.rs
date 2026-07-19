//! **FREE-TEXT input routing — the runtime routes a plain-text message as a pending text
//! affordance's input.** All over [`MockTransport`] (no token, no network), the same seam split
//! the runtime shell is built on.
//!
//! The gap this closes: a text-input offering (the collaborative document) presents affordances
//! that SOLICIT free text — an insert template, a set-title — but the runtime only routed fixed
//! commands + numeric `/act` args, so a plain-text message a user typed fell through to
//! [`TextDecision::Ignored`] and the document could never be driven in-chat. Now, when — and only
//! when — the chat's open offering presents an affordance carrying the
//! [`Action::wants_text`](dreggnet_offerings::Action::wants_text) discriminator, the plain-text
//! message becomes that affordance's text payload and advances one real turn (the executor stays
//! the sole referee); with no such affordance pending, ordinary chatter is still ignored; a
//! command is still a command.

use dreggnet_telegram::TelegramFrontend;
use dreggnet_telegram::host::TelegramHost;
use dreggnet_telegram::runtime::{HELP_TEXT, TextDecision, route_text_decided};
use dreggnet_telegram::transport::MockTransport;

/// A deterministic bot secret (a real deploy loads/derives 32 bytes in the bin).
const BOT_SECRET: [u8; 32] = [9u8; 32];
const ALICE: u64 = 1001;

/// A fresh in-memory host over the full catalog (no council members needed here).
fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[])
}

/// With a text-input offering open (the collaborative document), a plain-text message routes as
/// that affordance's text input — it reaches the substrate as one real turn (the executor
/// referees it), instead of falling through to `Ignored`.
#[test]
fn plain_text_with_a_pending_text_affordance_routes_as_text_input() {
    let mut h = host();
    let chat: i64 = 77;
    let sid = h
        .open("doc", chat, None, ALICE)
        .expect("the document opens");

    // The document surface SOLICITS text — an insert template is pending (detected off the
    // `wants_text` discriminator, not a hard-coded verb list).
    let pending = h
        .pending_text_action(&sid)
        .expect("the open document presents a text-soliciting affordance");
    assert!(pending.wants_text, "the pending affordance solicits text");
    assert_eq!(
        pending.turn, "insert",
        "the first text template is the continue-the-document insert",
    );
    assert_eq!(
        pending.text, None,
        "it is a template — no content yet; the user supplies the prose",
    );

    // A plain-text (non-command) message: routed as the affordance's text input.
    let (reply, decision) = route_text_decided(
        &mut h,
        chat,
        None,
        ALICE,
        "the dragon's hoard glittered in the torchlight",
    );

    match decision {
        TextDecision::TextInput { .. } => {}
        other => panic!("expected the free text to route as TextInput, got {other:?}"),
    }
    // It reached the substrate (the executor is the referee), so the router has an ack to send —
    // NOT the silent `None` of ignored chatter.
    assert!(
        reply.is_some(),
        "a routed text input yields a human ack (the executor's verdict)",
    );
}

/// With an offering open that solicits NO text (the dungeon — scene-choice buttons only), a
/// plain-text message stays `Ignored`: free text is claimed only when a text affordance is
/// genuinely pending, never swallowing arbitrary chatter.
#[test]
fn plain_text_with_no_pending_text_affordance_stays_ignored() {
    let mut h = host();
    let chat: i64 = 78;
    let sid = h
        .open("dungeon", chat, None, ALICE)
        .expect("the dungeon opens");

    assert!(
        h.pending_text_action(&sid).is_none(),
        "the dungeon presents no text-soliciting affordance (scene choices only)",
    );

    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "hello, anyone here?");
    assert!(
        matches!(decision, TextDecision::Ignored),
        "with no pending text affordance, plain chatter is ignored, got {decision:?}",
    );
    assert!(reply.is_none(), "ignored chatter draws no reply");
}

/// No open session at all: a plain-text message is ordinary chatter (nothing pending), ignored.
#[test]
fn plain_text_with_no_open_session_stays_ignored() {
    let mut h = host();
    let chat: i64 = 79;
    let sid = TelegramFrontend::<MockTransport>::session_id(chat, None);
    assert!(h.pending_text_action(&sid).is_none(), "nothing is open");

    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "just talking");
    assert!(matches!(decision, TextDecision::Ignored));
    assert!(reply.is_none());
}

/// A command is STILL a command even while a text affordance is pending — the leading `/` wins,
/// so `/help` is not swallowed as document prose.
#[test]
fn a_command_still_routes_as_a_command_while_text_is_pending() {
    let mut h = host();
    let chat: i64 = 80;
    let sid = h
        .open("doc", chat, None, ALICE)
        .expect("the document opens");
    assert!(
        h.pending_text_action(&sid).is_some(),
        "a text affordance is pending (the document is open)",
    );

    // `/help` — a command — routes as Help, not as text input, despite the pending affordance.
    let (reply, decision) = route_text_decided(&mut h, chat, None, ALICE, "/help");
    assert!(
        matches!(decision, TextDecision::Help),
        "a leading-slash command still routes as a command, got {decision:?}",
    );
    assert_eq!(
        reply.as_deref(),
        Some(HELP_TEXT),
        "the help text answered — the command was not swallowed as document text",
    );
}
