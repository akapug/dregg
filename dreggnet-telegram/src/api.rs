//! **The PURE Telegram Bot API layer** — request-building with NO transport, NO token, NO
//! network. Mirrors the discord-bot's `build_*_request` split (a pure request builder separate
//! from the live `Http` call): here [`build_present_request`] turns an offering [`Surface`] +
//! its cap-gated [`Action`]s into a [`SendMessageRequest`] whose serde encoding IS the real Bot
//! API `sendMessage` JSON wire body. A test that asserts the request shape asserts the wire
//! shape; a [`crate::transport::Transport`] is the only thing that ever touches the network.
//!
//! ## Surface → inline keyboard (the affordance mapping)
//! An offering's [`Surface`] is a deos [`deos_view::ViewNode`]; its [`Action`]s are cap-gated
//! `{turn, arg}` affordances. Telegram renders them as an **inline keyboard**: one button per
//! affordance (one row each, mirroring the dungeon's vertical `Menu`), the button's
//! `callback_data` carrying the `{turn, arg}` (see [`encode_callback`] / [`decode_callback`]) so a
//! press round-trips back to the same [`Action`]. A `!enabled` affordance is the **cap tooth
//! shown, not hidden**: rendered with a dim lock glyph but still pressable — the executor is the
//! sole referee, so firing it lands a real [`dreggnet_offerings::Outcome::Refused`] (anti-ghost),
//! exactly as on Discord.

use deos_view::AffordanceTransport;
use dreggnet_offerings::{Action, Surface};
use serde::{Deserialize, Serialize};

use crate::render::render_surface_text;

/// Encode an affordance `{turn, arg}` into Telegram `callback_data` (`"<turn>:<arg>"`). The
/// inverse of [`decode_callback`]. Deterministic and byte-bounded (≤ 64 bytes for any real
/// affordance). The Telegram binding of the ONE `deos_view::affordance` codec.
pub fn encode_callback(turn: &str, arg: i64) -> String {
    deos_view::affordance_id(turn, arg, AffordanceTransport::Telegram)
}

/// Decode Telegram `callback_data` back into `(turn, arg)` — the inverse of [`encode_callback`].
/// Splits on the LAST separator so `turn` may (in principle) contain earlier ones. `None` if the
/// data is malformed (no separator, or a non-integer arg) — a press the frontend never minted. The
/// Telegram binding of the ONE `deos_view::affordance` codec.
pub fn decode_callback(data: &str) -> Option<(String, i64)> {
    deos_view::affordance::parse_affordance_id(data, AffordanceTransport::Telegram)
}

/// The dim lock glyph prefixing a `!enabled` (ineligible) affordance's button label — the cap
/// tooth shown, not hidden. The button is still pressable; the executor refuses it on `advance`.
pub const LOCK_GLYPH: &str = "🔒 ";

/// One **inline keyboard button** — the Bot API `InlineKeyboardButton` (the fields we use). Its
/// `callback_data` carries the affordance `{turn, arg}`; a press delivers it back verbatim in a
/// `CallbackQuery`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InlineKeyboardButton {
    /// The button label (the affordance's human text; a `!enabled` one is [`LOCK_GLYPH`]-prefixed).
    pub text: String,
    /// The affordance `{turn, arg}`, [`encode_callback`]-encoded — echoed back on a press.
    pub callback_data: String,
}

/// An **inline keyboard** — the Bot API `InlineKeyboardMarkup`: a grid of [`InlineKeyboardButton`]
/// rows. The dungeon paints one affordance per row (mirroring the vertical deos `Menu`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InlineKeyboardMarkup {
    /// Rows of buttons (each inner `Vec` is one keyboard row).
    pub inline_keyboard: Vec<Vec<InlineKeyboardButton>>,
}

/// A **`sendMessage` request** — the Bot API `sendMessage` body, verbatim. Its serde encoding is
/// exactly the JSON wire body a live bot POSTs to `https://api.telegram.org/bot<token>/sendMessage`
/// (a test asserting this struct's shape asserts the real wire shape). Built purely by
/// [`build_present_request`]; sent by a [`crate::transport::Transport`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SendMessageRequest {
    /// The target chat (a Telegram chat id — negative for groups/supergroups, positive for DMs).
    pub chat_id: i64,
    /// The message text (the offering's rendered room prose + party state + verified-turn count).
    pub text: String,
    /// The affordance controls — an inline keyboard of the cap-gated actions. `None` when the
    /// surface offers no moves (a terminal room).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reply_markup: Option<InlineKeyboardMarkup>,
    /// For a forum-topic session, the topic thread this message posts under. `None` for a plain
    /// chat/DM. (The Bot API `message_thread_id`.)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message_thread_id: Option<i64>,
}

/// **Build the `sendMessage` request that presents `surface` + `actions` in `chat_id`** — the
/// pure Surface→(text + inline keyboard) mapping. The text is the deos view-tree walked into
/// Telegram-flavored prose ([`render_surface_text`]); the keyboard is one row per affordance,
/// each button's `callback_data` carrying its `{turn, arg}` so a press round-trips back to the
/// [`Action`]. A `!enabled` affordance is rendered dimmed ([`LOCK_GLYPH`]) but still included —
/// the cap tooth shown, not hidden (the executor refuses it on `advance`). `message_thread_id`
/// scopes the message to a forum topic when the session is a topic-per-session.
pub fn build_present_request(
    chat_id: i64,
    message_thread_id: Option<i64>,
    surface: &Surface,
    actions: &[Action],
) -> SendMessageRequest {
    let text = render_surface_text(surface);
    let reply_markup = if actions.is_empty() {
        None
    } else {
        let rows = actions
            .iter()
            .map(|a| {
                let label = if a.enabled {
                    a.label.clone()
                } else {
                    format!("{LOCK_GLYPH}{}", a.label)
                };
                vec![InlineKeyboardButton {
                    text: label,
                    callback_data: encode_callback(&a.turn, a.arg),
                }]
            })
            .collect();
        Some(InlineKeyboardMarkup {
            inline_keyboard: rows,
        })
    };
    SendMessageRequest {
        chat_id,
        text,
        reply_markup,
        message_thread_id,
    }
}
