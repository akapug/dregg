//! # The RUNTIME SHELL — what turns the library into a RUNNING bot.
//!
//! Everything below the [`crate::transport::HttpPost`] byte seam stays exactly as committed (pure
//! request builders, the injected transport, the [`TelegramHost`] router over the shared catalog).
//! This module adds the process around it, in the same testable split:
//!
//! - **[`BotApi`]** — the raw-method client for the calls a running bot needs beyond
//!   `sendMessage`: `getUpdates` (the LONG POLL), `answerCallbackQuery` (ack a press so the
//!   client's spinner stops), plain-text `sendMessage` replies, `getMe` (the startup token
//!   check). Same shape as [`crate::transport::RawBotApi`]: pure URL/body composition over an
//!   injected [`HttpPost`].
//! - **[`parse_updates`]** — the pure `Update[]` → [`BotEvent`] decoder (a button callback, a
//!   text command, or a Mini App `web_app_data` round-trip), plus the next long-poll offset.
//!   Driven directly in the tests with the real Bot API JSON shapes — no network needed to
//!   prove the routing.
//! - **[`route_callback`] / [`route_text`]** — one press / one command → the ONE router
//!   ([`TelegramHost::press`] / [`TelegramHost::open`]), including the RESTART path: a press in a
//!   chat whose session was durably resumed but not yet rebound ([`TelegramHost::resume_chat`])
//!   re-presents the live surface and retries, so a stale button from before the restart still
//!   lands.
//! - **[`durable_telegram_host`]** — the full shared catalog over a
//!   [`FileResumeStore`](dreggnet_offerings::FileResumeStore) (the same durable-store idiom
//!   `dreggnet-web`'s `demo_host_over` mounts): every open + landed advance is written through as
//!   a move-log, and boot RESUMES every persisted session by replay — a tampered log refuses to
//!   reopen (fail-closed; the file is kept as evidence).
//! - **[`run_update_loop`]** — the forever loop the bin runs: long-poll → decode → route → ack.
//!
//! The bin (`src/bin/dreggnet-telegram-bot.rs`) wires token-from-env + the store + this loop; the
//! systemd unit under `deploy/telegram/` keeps it running. The only thing a test cannot drive is
//! the real `api.telegram.org` edge — that needs the ops-gated bot token.

use std::path::PathBuf;

use serde_json::{Value, json};

use dreggnet_offerings::{FileResumeStore, OfferingHost, Outcome, VerifyReport};

use crate::api::{decode_callback, encode_callback};
use crate::audit::{self, Actor, AuditEvent, AuditOutcome, Input, Surface};
use crate::host::{HostPress, TURN_VERIFY, TelegramHost, telegram_default_host};
use crate::transport::{HttpPost, Transport, TransportError};
use crate::{CallbackQuery, ChatId, TelegramFrontend, TelegramUserId};

/// How long the server holds a `getUpdates` long poll open (seconds). The Bot API allows up to
/// ~50; the HTTP client timeout ([`crate::reqwest_transport`]) sits above this.
pub const POLL_TIMEOUT_SECS: u64 = 50;

/// The Bot API cap on an `answerCallbackQuery` toast text.
const CALLBACK_ANSWER_MAX: usize = 200;

/// The `/help` (and `/start`) text — the shell's whole command surface, honestly enumerated.
/// The Descent leads (the featured game — it lives on the web surface, not in this catalog);
/// the offering catalog is framed as the Lab, matching `dreggnet_catalog::lab_intro`.
pub const HELP_TEXT: &str = "DreggNet Cloud — every move is a real, verifiable executor turn.\n\
    ⚔️ The featured game is The Descent — one dungeon a day, one life, a no-cheat board. \
    It lives on the web surface, at /descent.\n\
    🧪 The Lab — experimental engine surfaces, for the curious:\n\
    /offerings — the lab shelf (press a button to open one)\n\
    /open <key> — open an offering in this chat (e.g. /open dungeon)\n\
    /play — Mini App launch buttons: the rich web surface, per offering (DMs only)\n\
    /link — bind this Telegram to your dregg root key (one you, across platforms; DMs only)\n\
    /verify — re-verify this chat's committed chain by replay\n\
    /act <turn> <arg> — fire a value-taking turn (e.g. /act bid 500)\n\
    /help — this text\n\
    A group chat plays as a collective; a DM plays solo. Sessions survive bot restarts.";

// ─────────────────────────────────────────────────────────────────────────────
// The raw-method Bot API client (getUpdates / answerCallbackQuery / getMe / text replies)
// ─────────────────────────────────────────────────────────────────────────────

/// **The raw-method Bot API client** the update loop drives. Pure composition (URL + JSON body +
/// the `{ok, result}` envelope) over an injected [`HttpPost`] — the same split as
/// [`crate::transport::RawBotApi`], for the methods a RUNNING bot needs around the send path.
pub struct BotApi<H: HttpPost> {
    token: String,
    base_url: String,
    http: H,
}

impl<H: HttpPost> BotApi<H> {
    /// A client for `token`, POSTing through `http`, against the public Bot API host.
    pub fn new(token: impl Into<String>, http: H) -> Self {
        BotApi {
            token: token.into(),
            base_url: "https://api.telegram.org".to_string(),
            http,
        }
    }

    /// Override the Bot API host (a self-hosted Bot API server, or a test double).
    pub fn with_base_url(mut self, base_url: impl Into<String>) -> Self {
        self.base_url = base_url.into();
        self
    }

    /// Call `method` with the JSON `body`, unwrap the `{ok, result}` envelope, return `result`.
    pub fn call(&self, method: &str, body: &Value) -> Result<Value, TransportError> {
        let url = format!("{}/bot{}/{}", self.base_url, self.token, method);
        let resp = self
            .http
            .post_json(&url, &body.to_string())
            .map_err(TransportError)?;
        let v: Value = serde_json::from_str(&resp)
            .map_err(|e| TransportError(format!("decode {method} response: {e}")))?;
        if v.get("ok").and_then(Value::as_bool) != Some(true) {
            let desc = v
                .get("description")
                .and_then(Value::as_str)
                .unwrap_or("Bot API returned ok=false");
            return Err(TransportError(format!("{method}: {desc}")));
        }
        Ok(v.get("result").cloned().unwrap_or(Value::Null))
    }

    /// `getMe` — the startup token check. Returns the bot's username.
    pub fn get_me(&self) -> Result<String, TransportError> {
        let me = self.call("getMe", &json!({}))?;
        Ok(me
            .get("username")
            .and_then(Value::as_str)
            .unwrap_or("<unnamed bot>")
            .to_string())
    }

    /// One `getUpdates` LONG POLL: block server-side up to [`POLL_TIMEOUT_SECS`] for new updates
    /// at/after `offset`. Returns the raw `result` array (decode with [`parse_updates`]).
    pub fn get_updates(&self, offset: Option<i64>) -> Result<Value, TransportError> {
        let mut body = json!({
            "timeout": POLL_TIMEOUT_SECS,
            "allowed_updates": ["message", "callback_query"],
        });
        if let Some(o) = offset {
            body["offset"] = json!(o);
        }
        self.call("getUpdates", &body)
    }

    /// Ack a button press (`answerCallbackQuery`) with a short toast — the client's loading
    /// spinner stops. Text is truncated to the Bot API's 200-char cap.
    pub fn answer_callback(&self, callback_id: &str, text: &str) -> Result<(), TransportError> {
        let toast: String = text.chars().take(CALLBACK_ANSWER_MAX).collect();
        self.call(
            "answerCallbackQuery",
            &json!({ "callback_query_id": callback_id, "text": toast }),
        )
        .map(|_| ())
    }

    /// Send a plain-text reply into a chat (command answers, verify reports) — distinct from the
    /// session's presented surface message, which the [`TelegramHost`]'s own transport owns.
    pub fn send_text(
        &self,
        chat_id: ChatId,
        topic: Option<i64>,
        text: &str,
    ) -> Result<(), TransportError> {
        let mut body = json!({ "chat_id": chat_id, "text": text });
        if let Some(t) = topic {
            body["message_thread_id"] = json!(t);
        }
        self.call("sendMessage", &body).map(|_| ())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Update decoding (pure — driven directly by the tests with real Bot API JSON)
// ─────────────────────────────────────────────────────────────────────────────

/// One decoded incoming update the shell routes — a button press or a text message.
#[derive(Debug, Clone)]
pub enum BotEvent {
    /// An inline-button press (`callback_query`): the Bot API callback id (for the ack) plus the
    /// typed [`CallbackQuery`] the library routes.
    Callback {
        /// The `callback_query.id` — `answerCallbackQuery` needs it to stop the spinner.
        callback_id: String,
        /// The press, in the library's own event type.
        query: CallbackQuery,
    },
    /// A text message (`message.text`) — the command surface (`/offerings`, `/open`, …).
    Text {
        /// The chat the message was sent in.
        chat_id: ChatId,
        /// The forum-topic thread, if any.
        topic: Option<i64>,
        /// The sending Telegram user.
        uid: TelegramUserId,
        /// The message text.
        text: String,
    },
    /// Data a Mini App sent back through `Telegram.WebApp.sendData` (`message.web_app_data`) —
    /// a service message from a KEYBOARD-launched web-view. Routed by [`route_web_app_data`]:
    /// a payload in the ONE affordance codec routes as a synthetic press (the executor stays
    /// the sole referee); anything else is acknowledged, never trusted — a client string can
    /// never name an identity or bypass the presented-affordance gate.
    WebAppData {
        /// The chat the service message landed in.
        chat_id: ChatId,
        /// The forum-topic thread, if any.
        topic: Option<i64>,
        /// The Telegram user whose web-view sent the data.
        uid: TelegramUserId,
        /// The raw `web_app_data.data` payload (client-authored — untrusted).
        data: String,
        /// The `web_app_data.button_text` — the keyboard button's label, display only.
        button_text: Option<String>,
    },
}

/// **Decode a `getUpdates` `result` array** into the events the shell routes, plus the NEXT poll
/// offset (max `update_id` + 1 — confirming these updates consumed so the server drops them).
/// Unknown/partial update shapes are skipped, never a crash: the loop must survive whatever the
/// wire brings.
pub fn parse_updates(result: &Value) -> (Vec<BotEvent>, Option<i64>) {
    let mut events = Vec::new();
    let mut next: Option<i64> = None;
    let Some(arr) = result.as_array() else {
        return (events, next);
    };
    for u in arr {
        if let Some(id) = u.get("update_id").and_then(Value::as_i64) {
            next = Some(next.map_or(id + 1, |n| n.max(id + 1)));
        }
        if let Some(cb) = u.get("callback_query") {
            let (Some(callback_id), Some(uid), Some(msg), Some(data)) = (
                cb.get("id").and_then(Value::as_str),
                cb.get("from")
                    .and_then(|f| f.get("id"))
                    .and_then(Value::as_u64),
                cb.get("message"),
                cb.get("data").and_then(Value::as_str),
            ) else {
                continue;
            };
            let Some(chat_id) = msg
                .get("chat")
                .and_then(|c| c.get("id"))
                .and_then(Value::as_i64)
            else {
                continue;
            };
            events.push(BotEvent::Callback {
                callback_id: callback_id.to_string(),
                query: CallbackQuery {
                    chat_id,
                    message_thread_id: msg.get("message_thread_id").and_then(Value::as_i64),
                    from_user_id: uid,
                    data: data.to_string(),
                },
            });
        } else if let Some(m) = u.get("message") {
            let (Some(chat_id), Some(uid)) = (
                m.get("chat")
                    .and_then(|c| c.get("id"))
                    .and_then(Value::as_i64),
                m.get("from")
                    .and_then(|f| f.get("id"))
                    .and_then(Value::as_u64),
            ) else {
                continue;
            };
            let topic = m.get("message_thread_id").and_then(Value::as_i64);
            // A Mini App's `sendData` round-trip arrives as a `web_app_data` service message
            // (no `text`), so it is checked FIRST — the same skip-not-crash posture for
            // anything partial.
            if let Some(wad) = m.get("web_app_data") {
                let Some(data) = wad.get("data").and_then(Value::as_str) else {
                    continue;
                };
                events.push(BotEvent::WebAppData {
                    chat_id,
                    topic,
                    uid,
                    data: data.to_string(),
                    button_text: wad
                        .get("button_text")
                        .and_then(Value::as_str)
                        .map(str::to_string),
                });
            } else if let Some(text) = m.get("text").and_then(Value::as_str) {
                events.push(BotEvent::Text {
                    chat_id,
                    topic,
                    uid,
                    text: text.to_string(),
                });
            }
        }
    }
    (events, next)
}

// ─────────────────────────────────────────────────────────────────────────────
// Routing (one event → the ONE TelegramHost router → a human ack)
// ─────────────────────────────────────────────────────────────────────────────

/// **The MACHINE account of a routed press** — what the audit envelope records (the human ack
/// stays [`describe_press`]'s). Extracted from the [`HostPress`] BEFORE it is consumed, so the
/// update loop emits [`AuditEvent`]s in the design's §3 taxonomy without re-deriving anything.
#[derive(Debug, Clone)]
pub enum PressDecision {
    /// A menu press opened the named offering.
    Opened(String),
    /// A turn landed — carries THE receipt-chain join (`hex(TurnReceipt.turn_hash)`).
    Landed {
        /// The offering key the turn advanced.
        key: String,
        /// `hex(TurnReceipt.turn_hash)` — the join to the committed chain.
        turn_hash: String,
        /// Whether the session ended.
        ended: bool,
    },
    /// The executor refused the move (anti-ghost: nothing committed).
    ExecutorRefused {
        /// The offering key.
        key: String,
        /// The executor's own reason.
        why: String,
    },
    /// A [`TURN_VERIFY`](crate::host::TURN_VERIFY) press re-verified the chain.
    Verified {
        /// The offering key.
        key: String,
        /// The report verdict (`None` = the offering exposes no verifier).
        verified: Option<bool>,
        /// Turns replayed.
        turns: u64,
    },
    /// Frontend-level refusal BEFORE the substrate (stale keyboard / unknown affordance).
    NotOffered,
    /// Nothing open in the chat (post-resume-retry).
    NoSession,
    /// The restart-resume path found a persisted offering but could not reopen it.
    ReopenFailed(String),
}

impl PressDecision {
    /// Read the machine decision off a [`HostPress`] (borrow — the press is still yours to
    /// [`describe_press`]).
    pub fn of(press: &HostPress) -> PressDecision {
        match press {
            HostPress::Opened(key) => PressDecision::Opened(key.clone()),
            HostPress::Advanced {
                key,
                outcome: Outcome::Landed { receipt, ended },
            } => PressDecision::Landed {
                key: key.clone(),
                turn_hash: audit::hex32(&receipt.turn_hash),
                ended: *ended,
            },
            HostPress::Advanced {
                key,
                outcome: Outcome::Refused(why),
            } => PressDecision::ExecutorRefused {
                key: key.clone(),
                why: why.clone(),
            },
            HostPress::Verified { key, report } => PressDecision::Verified {
                key: key.clone(),
                verified: report.as_ref().map(|r| r.verified),
                turns: report.as_ref().map(|r| r.turns as u64).unwrap_or(0),
            },
            HostPress::NotOffered => PressDecision::NotOffered,
            HostPress::NoSession => PressDecision::NoSession,
        }
    }

    /// The §3 taxonomy mapping: `(decision.kind, decision.reason, outcome, offering)`.
    pub fn audit_parts(&self) -> (&'static str, String, AuditOutcome, Option<String>) {
        match self {
            PressDecision::Opened(key) => (
                "routed",
                String::new(),
                AuditOutcome::None,
                Some(key.clone()),
            ),
            PressDecision::Landed {
                key,
                turn_hash,
                ended,
            } => (
                "routed",
                String::new(),
                AuditOutcome::Landed {
                    turn_hash: turn_hash.clone(),
                    ended: *ended,
                },
                Some(key.clone()),
            ),
            PressDecision::ExecutorRefused { key, why } => (
                "routed", // the substrate WAS reached; the refusal is the executor's
                String::new(),
                AuditOutcome::Refused { why: why.clone() },
                Some(key.clone()),
            ),
            PressDecision::Verified {
                key,
                verified,
                turns,
            } => (
                "routed",
                String::new(),
                AuditOutcome::Verified {
                    verified: verified.unwrap_or(false),
                    turns: *turns,
                },
                Some(key.clone()),
            ),
            PressDecision::NotOffered => (
                "refused",
                "not_offered".to_string(),
                AuditOutcome::None,
                None,
            ),
            PressDecision::NoSession => (
                "refused",
                "no_session".to_string(),
                AuditOutcome::None,
                None,
            ),
            PressDecision::ReopenFailed(key) => (
                "error",
                "resume_reopen_failed".to_string(),
                AuditOutcome::None,
                Some(key.clone()),
            ),
        }
    }
}

/// **Route a button press through the host**, with the RESTART-RESUME path: if the chat answers
/// [`HostPress::NoSession`] (this process never presented there) but the chat's session was
/// durably RESUMED on boot, rebind it ([`TelegramHost::resume_chat`]), re-present the live
/// surface ([`TelegramHost::open`] — idempotent, the resumed state is kept), and retry the press
/// once against the fresh keyboard. Returns the human ack for `answerCallbackQuery`.
pub fn route_callback<T: Transport>(host: &mut TelegramHost<T>, query: CallbackQuery) -> String {
    route_callback_decided(host, query).0
}

/// [`route_callback`] plus the machine [`PressDecision`] — the audit-emitting caller's form
/// (design §9: `route_*` expose the structured decision alongside the human string).
pub fn route_callback_decided<T: Transport>(
    host: &mut TelegramHost<T>,
    query: CallbackQuery,
) -> (String, PressDecision) {
    match host.press(query.clone()) {
        HostPress::NoSession => {
            let sid = TelegramFrontend::<T>::session_id(query.chat_id, query.message_thread_id);
            let Some(key) = host.resume_chat(&sid) else {
                return (
                    "No session in this chat yet — send /offerings to pick one.".to_string(),
                    PressDecision::NoSession,
                );
            };
            if host
                .open(
                    &key,
                    query.chat_id,
                    query.message_thread_id,
                    query.from_user_id,
                )
                .is_err()
            {
                return (
                    format!("Could not reopen {key} — send /offerings."),
                    PressDecision::ReopenFailed(key),
                );
            }
            let press = host.press(query);
            let decision = PressDecision::of(&press);
            (describe_press(press), decision)
        }
        press => {
            let decision = PressDecision::of(&press);
            (describe_press(press), decision)
        }
    }
}

/// **Route a text message** — the command surface. `None` means nothing to reply (ordinary
/// chatter is ignored; the offerings menu / opened surface are their own messages, sent through
/// the host's transport).
pub fn route_text<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    text: &str,
) -> Option<String> {
    route_text_decided(host, chat_id, topic, uid, text).0
}

/// The machine account of a routed text message — the audit envelope's half of
/// [`route_text_decided`]. `Ignored` (ordinary chatter) is deliberately NOT audited by the
/// loop: no decision was made and group chatter is not an interaction with the bot.
#[derive(Debug, Clone)]
pub enum TextDecision {
    /// `/start` `/help` — the help text answered.
    Help,
    /// `/offerings` `/menu` — the offerings menu presented.
    Menu,
    /// `/play` — the Mini App launch menu; `why` is the honest refusal when unserved.
    PlayMenu {
        /// Whether the launch menu was actually sent.
        served: bool,
        /// The human reason when it was not.
        why: Option<String>,
    },
    /// `/open <key>` — `err` carries the host's refusal, if any.
    Open {
        /// The requested offering key.
        key: String,
        /// The open error, if the host refused.
        err: Option<String>,
    },
    /// `/verify` / `/act` minted a synthetic press — the press's own decision.
    Press {
        /// Which command minted the press.
        cmd: String,
        /// The routed press's machine decision.
        press: PressDecision,
    },
    /// A recognized command with unusable arguments.
    Usage {
        /// The command whose usage was answered.
        cmd: String,
    },
    /// An unrecognized slash command.
    Unknown {
        /// The command word as typed.
        cmd: String,
    },
    /// **Plain text routed as a pending text affordance's input** — the chat had an open
    /// text-input offering (a document session soliciting an insert / title), so the message
    /// became that affordance's [`Action::text`](dreggnet_offerings::Action::text) payload and
    /// advanced one real turn. Carries the routed press's machine decision (the executor's
    /// verdict — a landed edit or a real refusal).
    TextInput {
        /// The routed press's machine decision.
        press: PressDecision,
    },
    /// Ordinary chatter — no decision, no reply, no audit event.
    Ignored,
}

/// [`route_text`] plus the machine [`TextDecision`] — the audit-emitting caller's form.
pub fn route_text_decided<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    text: &str,
) -> (Option<String>, TextDecision) {
    let text = text.trim();
    let (cmd, rest) = match text.split_once(char::is_whitespace) {
        Some((c, r)) => (c, r.trim()),
        None => (text, ""),
    };
    // In a group, commands arrive suffixed with the bot's username: `/open@MyBot dungeon`.
    let cmd = cmd.split('@').next().unwrap_or(cmd);
    match cmd {
        "/start" | "/help" => (Some(HELP_TEXT.to_string()), TextDecision::Help),
        "/offerings" | "/menu" => {
            host.present_offerings_menu(chat_id, topic);
            (None, TextDecision::Menu)
        }
        // The Mini App launch tier: a menu of `web_app` buttons opening the rich web surface,
        // one per offering. `Err` is the honest human reply (tier unarmed / group chat —
        // Telegram only honors `web_app` inline buttons in DMs / a transport failure).
        "/play" | "/webapp" => match host.present_play_menu(chat_id, topic) {
            Ok(()) => (
                None, // the launch menu IS the reply
                TextDecision::PlayMenu {
                    served: true,
                    why: None,
                },
            ),
            Err(why) => (
                Some(why.clone()),
                TextDecision::PlayMenu {
                    served: false,
                    why: Some(why),
                },
            ),
        },
        "/link" => match host.present_link_menu(chat_id, topic) {
            Ok(()) => (
                None, // the link launch button IS the reply
                TextDecision::PlayMenu {
                    served: true,
                    why: None,
                },
            ),
            Err(why) => (
                Some(why.clone()),
                TextDecision::PlayMenu {
                    served: false,
                    why: Some(why),
                },
            ),
        },
        "/open" => {
            if rest.is_empty() {
                return (
                    Some("Usage: /open <key> — see /offerings for the catalog.".to_string()),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            }
            match host.open(rest, chat_id, topic, uid) {
                Ok(_) => (
                    None, // the opened surface IS the reply
                    TextDecision::Open {
                        key: rest.to_string(),
                        err: None,
                    },
                ),
                Err(e) => (
                    Some(format!("Cannot open {rest}: {e}")),
                    TextDecision::Open {
                        key: rest.to_string(),
                        err: Some(e.to_string()),
                    },
                ),
            }
        }
        // `/verify` and `/act` mint the same synthetic press a pinned button would — the ONE
        // router (with the restart-resume path) handles both.
        "/verify" => {
            let (ack, press) = route_callback_decided(
                host,
                CallbackQuery {
                    chat_id,
                    message_thread_id: topic,
                    from_user_id: uid,
                    data: encode_callback(TURN_VERIFY, 0),
                },
            );
            (
                Some(ack),
                TextDecision::Press {
                    cmd: cmd.to_string(),
                    press,
                },
            )
        }
        "/act" => {
            let usage = "Usage: /act <turn> <arg> — e.g. /act bid 500".to_string();
            let Some((turn, arg)) = rest.split_once(char::is_whitespace) else {
                return (
                    Some(usage),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            };
            let Ok(arg) = arg.trim().parse::<i64>() else {
                return (
                    Some(usage),
                    TextDecision::Usage {
                        cmd: cmd.to_string(),
                    },
                );
            };
            let (ack, press) = route_callback_decided(
                host,
                CallbackQuery {
                    chat_id,
                    message_thread_id: topic,
                    from_user_id: uid,
                    data: encode_callback(turn, arg),
                },
            );
            (
                Some(ack),
                TextDecision::Press {
                    cmd: cmd.to_string(),
                    press,
                },
            )
        }
        _ if cmd.starts_with('/') => (
            None,
            TextDecision::Unknown {
                cmd: cmd.to_string(),
            },
        ),
        // FREE TEXT (a non-command message). If — and ONLY if — the chat has an open offering
        // whose surface is SOLICITING text (a document session presenting an insert / title
        // template, [`TelegramHost::pending_text_action`]), route the whole message as that
        // affordance's text input; the executor referees what lands. Otherwise it is ordinary
        // chatter and stays `Ignored` (never swallow arbitrary group talk — text is only claimed
        // when a text affordance is genuinely pending for this chat's session).
        _ => {
            let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
            if host.pending_text_action(&sid).is_some() {
                let press = host.press_text(chat_id, topic, uid, text);
                let decision = PressDecision::of(&press);
                (
                    Some(describe_press(press)),
                    TextDecision::TextInput { press: decision },
                )
            } else {
                (None, TextDecision::Ignored)
            }
        }
    }
}

impl TextDecision {
    /// The §3 taxonomy mapping: `(decision.kind, reason, outcome, offering, input.kind)`.
    /// `None` = ordinary chatter — not an interaction, no audit event.
    pub fn audit_parts(
        &self,
    ) -> Option<(&'static str, String, AuditOutcome, Option<String>, String)> {
        match self {
            TextDecision::Help => Some((
                "routed",
                String::new(),
                AuditOutcome::None,
                None,
                "/help".to_string(),
            )),
            TextDecision::Menu => Some((
                "routed",
                String::new(),
                AuditOutcome::None,
                None,
                "/offerings".to_string(),
            )),
            TextDecision::PlayMenu { served, why } => Some((
                if *served { "routed" } else { "refused" },
                if *served {
                    String::new()
                } else {
                    format!(
                        "webapp_unavailable: {}",
                        why.as_deref().unwrap_or("unknown")
                    )
                },
                AuditOutcome::None,
                None,
                "/play".to_string(),
            )),
            TextDecision::Open { key, err } => Some((
                if err.is_none() { "routed" } else { "refused" },
                err.as_ref()
                    .map(|e| format!("open_failed: {e}"))
                    .unwrap_or_default(),
                AuditOutcome::None,
                Some(key.clone()),
                "/open".to_string(),
            )),
            TextDecision::Press { cmd, press } => {
                let (kind, reason, outcome, offering) = press.audit_parts();
                Some((kind, reason, outcome, offering, cmd.clone()))
            }
            TextDecision::Usage { cmd } => Some((
                "refused",
                "usage".to_string(),
                AuditOutcome::None,
                None,
                cmd.clone(),
            )),
            TextDecision::Unknown { cmd } => Some((
                "refused",
                "unknown_command".to_string(),
                AuditOutcome::None,
                None,
                cmd.clone(),
            )),
            // Free text routed into a pending text affordance — the press's own decision, under
            // a `text` input kind (design §8: user free text IS the trail).
            TextDecision::TextInput { press } => {
                let (kind, reason, outcome, offering) = press.audit_parts();
                Some((kind, reason, outcome, offering, "text".to_string()))
            }
            TextDecision::Ignored => None,
        }
    }
}

/// **Route a `web_app_data` payload** — what a Mini App sent back via
/// `Telegram.WebApp.sendData`. The payload is CLIENT-AUTHORED and untrusted: it can never name
/// an identity (the acting identity derives from the Telegram `uid` the update itself
/// attributes, exactly as a button press) and never bypasses a gate. A payload in the ONE
/// affordance codec (`turn:arg` — [`decode_callback`]) is routed as a synthetic press through
/// [`route_callback`], so it faces the same presented-affordance check + the same executor
/// refereeing as any button; anything else is acknowledged honestly and dropped. Returns the
/// human reply.
pub fn route_web_app_data<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    data: &str,
) -> String {
    route_web_app_data_decided(host, chat_id, topic, uid, data).0
}

/// The machine account of a routed `web_app_data` payload.
#[derive(Debug, Clone)]
pub enum WebAppDecision {
    /// The payload decoded in the ONE affordance codec and routed as a synthetic press.
    Press(PressDecision),
    /// The payload decoded as nothing — acknowledged-and-dropped (client-authored, untrusted).
    Dropped {
        /// The payload length (the payload itself is client-authored noise; the length is the
        /// honest record).
        len: usize,
    },
}

/// [`route_web_app_data`] plus the machine [`WebAppDecision`] — the audit-emitting caller's
/// form.
pub fn route_web_app_data_decided<T: Transport>(
    host: &mut TelegramHost<T>,
    chat_id: ChatId,
    topic: Option<i64>,
    uid: TelegramUserId,
    data: &str,
) -> (String, WebAppDecision) {
    if decode_callback(data).is_some() {
        let (ack, press) = route_callback_decided(
            host,
            CallbackQuery {
                chat_id,
                message_thread_id: topic,
                from_user_id: uid,
                data: data.to_string(),
            },
        );
        (ack, WebAppDecision::Press(press))
    } else {
        (
            format!(
                "Mini App sent {} byte(s) — no affordance decoded, nothing landed. State-changing \
                 turns land through the app's own verified channel.",
                data.len()
            ),
            WebAppDecision::Dropped { len: data.len() },
        )
    }
}

/// The human account of a routed press — what the presser's ack toast says.
pub fn describe_press(press: HostPress) -> String {
    match press {
        HostPress::Opened(key) => format!("Opened {key}."),
        HostPress::Advanced {
            outcome: Outcome::Landed { ended, .. },
            ..
        } => {
            if ended {
                "Turn landed — session complete. /verify replays the whole chain.".to_string()
            } else {
                "Turn landed — one real verified receipt.".to_string()
            }
        }
        HostPress::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => format!("Refused by the executor: {why}"),
        HostPress::Verified { key, report } => describe_verify(&key, report.as_ref()),
        HostPress::NotOffered => {
            "That button is not on the current surface (a stale keyboard?).".to_string()
        }
        HostPress::NoSession => "No session in this chat yet — send /offerings.".to_string(),
    }
}

/// The human account of a re-verification.
pub fn describe_verify(key: &str, report: Option<&VerifyReport>) -> String {
    match report {
        Some(r) if r.verified => format!(
            "{key}: {} turn(s) re-verified by replay — {}",
            r.turns, r.detail
        ),
        Some(r) => format!(
            "{key}: VERIFY FAILED after {} turn(s) — {}",
            r.turns, r.detail
        ),
        None => format!("{key} exposes no verifier."),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The durable host + the forever loop
// ─────────────────────────────────────────────────────────────────────────────

/// **The full shared catalog over a durable session store** — the host build the bin ships to
/// [`TelegramHost::with_host`]'s owning thread. With a `dir`: opens a
/// [`FileResumeStore`](dreggnet_offerings::FileResumeStore) there, attaches it (every session
/// open + landed advance + signed-replay floor is written through as a move-log), and
/// boot-resumes every persisted session by REPLAY — the identical committed state, or a
/// fail-closed refusal for a tampered log (logged; the file is kept as evidence). An unopenable
/// dir degrades to the in-memory host with a loud warning (the bot still boots; sessions are
/// ephemeral) — the same posture as `dreggnet-web`'s `demo_host_over`. `None` → in-memory.
pub fn durable_telegram_host(dir: Option<PathBuf>, council_members: Vec<[u8; 32]>) -> OfferingHost {
    let mut host = telegram_default_host(council_members);
    let Some(dir) = dir else {
        return host;
    };
    match FileResumeStore::open(&dir) {
        Ok(store) => {
            host = host.with_resume_store(Box::new(store));
            let results = host.resume_all();
            let resumed = results.iter().filter(|(_, r)| r.is_ok()).count();
            let refused = results.len() - resumed;
            eprintln!(
                "session store {} attached: {resumed} session(s) resumed by move-log replay, \
                 {refused} refused",
                dir.display()
            );
            for (log, outcome) in &results {
                if let Err(e) = outcome {
                    eprintln!(
                        "  REFUSED (fail-closed; file kept): {}/{}: {e}",
                        log.key, log.id.0
                    );
                }
                // The boot-resume decision, durably (design §2.2: today stderr-only) — one
                // `resume` event per persisted log, routed (resumed) or refused (fail-closed).
                let ev = AuditEvent::new(
                    "telegram",
                    Actor::system("boot-resume"),
                    Surface::Resume,
                    Input::new("resume", json!({ "store": dir.display().to_string() })),
                )
                .in_session(Some(log.key.clone()), Some(log.id.0.clone()));
                audit::log().emit(match outcome {
                    Ok(_) => ev.decided("routed", ""),
                    Err(e) => {
                        ev.decided("refused", "resume_failed")
                            .with_outcome(AuditOutcome::Error {
                                what: e.to_string(),
                            })
                    }
                });
            }
        }
        Err(e) => {
            eprintln!(
                "WARN: cannot open session dir {}: {e} — sessions stay IN-MEMORY (a restart \
                 drops them)",
                dir.display()
            );
        }
    }
    host
}

/// **The forever loop**: long-poll `getUpdates`, decode, route every event through the ONE
/// router, ack. A transport error backs off 5s and re-polls (the loop must outlive flaky
/// networks); `persist_offset` is called with each new offset so a restart does not replay
/// already-routed updates (the bin writes it beside the session store).
pub fn run_update_loop<T: Transport, H: HttpPost>(
    host: &mut TelegramHost<T>,
    api: &BotApi<H>,
    mut offset: Option<i64>,
    mut persist_offset: impl FnMut(i64),
) {
    loop {
        let result = match api.get_updates(offset) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("getUpdates failed: {e} — retrying in 5s");
                std::thread::sleep(std::time::Duration::from_secs(5));
                continue;
            }
        };
        let (events, next) = parse_updates(&result);
        if let Some(n) = next {
            offset = Some(n);
            persist_offset(n);
        }
        for ev in events {
            match ev {
                BotEvent::Callback { callback_id, query } => {
                    let (chat, topic) = (query.chat_id, query.message_thread_id);
                    // AUDIT EMIT (ingress + outcome, one stack frame): the press's envelope —
                    // who (custodial uid → derived identity), what (callback_data), the
                    // decision taxonomy, and the receipt-chain join on a landed turn.
                    let sid = TelegramFrontend::<T>::session_id(chat, topic);
                    let actor = Actor::custodial(
                        query.from_user_id.to_string(),
                        host.identity(query.from_user_id).0,
                    );
                    let data = query.data.clone();
                    let (ack, decision) = route_callback_decided(host, query);
                    let (kind, reason, outcome, offering) = decision.audit_parts();
                    audit::log().emit(
                        AuditEvent::new(
                            "telegram",
                            actor,
                            Surface::Callback,
                            Input::new("callback", json!({ "callback_data": data })),
                        )
                        .in_session(offering, Some(sid.0.clone()))
                        .decided(kind, reason)
                        .with_outcome(outcome),
                    );
                    if let Err(e) = api.answer_callback(&callback_id, &ack) {
                        eprintln!("answerCallbackQuery failed: {e}");
                    }
                    // A long ack (a verify report, an executor refusal with detail) does not fit
                    // a 200-char toast — also land it in the chat.
                    if ack.len() > 180 {
                        if let Err(e) = api.send_text(chat, topic, &ack) {
                            eprintln!("sendMessage (long ack) failed: {e}");
                        }
                    }
                }
                BotEvent::Text {
                    chat_id,
                    topic,
                    uid,
                    text,
                } => {
                    let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
                    let actor = Actor::custodial(uid.to_string(), host.identity(uid).0);
                    let (reply, decision) = route_text_decided(host, chat_id, topic, uid, &text);
                    // AUDIT EMIT: every routed command (ordinary chatter maps to None — not an
                    // interaction). User free text IS the trail (§8); no /key-class command
                    // exists on this surface.
                    if let Some((kind, reason, outcome, offering, input_kind)) =
                        decision.audit_parts()
                    {
                        audit::log().emit(
                            AuditEvent::new(
                                "telegram",
                                actor,
                                Surface::Command,
                                Input::new(&*input_kind, json!({ "text": text })),
                            )
                            .in_session(offering, Some(sid.0.clone()))
                            .decided(kind, reason)
                            .with_outcome(outcome),
                        );
                    }
                    if let Some(reply) = reply {
                        if let Err(e) = api.send_text(chat_id, topic, &reply) {
                            eprintln!("sendMessage failed: {e}");
                        }
                    }
                }
                BotEvent::WebAppData {
                    chat_id,
                    topic,
                    uid,
                    data,
                    ..
                } => {
                    let sid = TelegramFrontend::<T>::session_id(chat_id, topic);
                    let actor = Actor::custodial(uid.to_string(), host.identity(uid).0);
                    let (reply, decision) =
                        route_web_app_data_decided(host, chat_id, topic, uid, &data);
                    // AUDIT EMIT: the Mini App sendData round-trip — routed as a synthetic
                    // press, or acknowledged-and-dropped (client-authored, untrusted).
                    let (kind, reason, outcome, offering) = match &decision {
                        WebAppDecision::Press(p) => p.audit_parts(),
                        WebAppDecision::Dropped { .. } => (
                            "refused",
                            "no_affordance_decoded".to_string(),
                            AuditOutcome::None,
                            None,
                        ),
                    };
                    audit::log().emit(
                        AuditEvent::new(
                            "telegram",
                            actor,
                            Surface::WebAppData,
                            Input::new("web_app_data", json!({ "data": data, "len": data.len() })),
                        )
                        .in_session(offering, Some(sid.0.clone()))
                        .decided(kind, reason)
                        .with_outcome(outcome),
                    );
                    if let Err(e) = api.send_text(chat_id, topic, &reply) {
                        eprintln!("sendMessage (web_app_data reply) failed: {e}");
                    }
                }
            }
        }
    }
}
