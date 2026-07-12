//! **The PURE WeChat API layer** — request-building with NO transport, NO access-token, NO
//! network. Mirrors the telegram frontend's pure/live split ([`build_present_request`] separate
//! from a [`crate::transport::Transport`]): here it turns an offering [`Surface`] + its cap-gated
//! [`Action`]s into a [`CustomSendRequest`] whose serde encoding IS the real WeChat
//! `cgi-bin/message/custom/send` JSON wire body. A test that asserts the request shape asserts the
//! wire shape; a [`crate::transport::Transport`] is the only thing that ever touches the network.
//!
//! ## Surface → a numbered reply list (the WeChat affordance mapping)
//! A WeChat Official Account forbids arbitrary per-message buttons. So an offering's cap-gated
//! [`Action`]s are rendered as a **numbered list appended to the message text** — one line per
//! affordance, `1.`-indexed — and the user **replies with the number** to pick a move (the reply
//! arrives as an inbound text message; see [`crate::WeChatMessage`] / [`parse_reply_index`]). The
//! numbering is over ALL presented affordances (enabled + locked): a `!enabled` affordance is the
//! **cap tooth shown, not hidden** — it keeps its number and is still selectable, but is marked
//! with a [`LOCK_GLYPH`] + `(locked)`, and firing it lands a real
//! [`dreggnet_offerings::Outcome::Refused`] (anti-ghost), exactly as on Discord / Telegram.
//!
//! ## The RICH alternative — a Mini-Program card
//! For a Mini-Program surface (which CAN render real buttons in WXML), [`build_miniprogram_card`]
//! produces a [`MiniProgramCard`] payload: one [`MiniProgramButton`] per affordance carrying its
//! `{turn, arg, enabled}`. This is the heavier path (MP review + custom WXML); the OA numbered-reply
//! is the CANONICAL surface (lightest, OA-native). Both map the SAME affordances — no reinvention.

use dreggnet_offerings::{Action, Surface};
use serde::{Deserialize, Serialize};

use crate::render::render_surface_text;

/// The `msgtype` of an OA text message — the only message type the numbered-reply loop uses
/// (both the outbound [`CustomSendRequest`] and the inbound reply are `"text"`).
pub const MSG_TYPE_TEXT: &str = "text";

/// The dim lock glyph prefixing a `!enabled` (ineligible) affordance's numbered line — the cap
/// tooth shown, not hidden. The line still carries its reply number; the executor refuses the move
/// on `advance`.
pub const LOCK_GLYPH: &str = "🔒 ";

/// Parse a WeChat reply's text into a **1-based affordance index** — the WeChat analogue of the
/// telegram `decode_callback`. Takes the leading run of ASCII digits (so `"2"`, `"2."`, and
/// `"2 trade blows"` all resolve to `2`), so a user can reply with just the number. `None` if the
/// reply has no leading digit or names index `0` (there is no 0th affordance — the list is 1-based).
pub fn parse_reply_index(content: &str) -> Option<usize> {
    let digits: String = content
        .trim()
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    let n: usize = digits.parse().ok()?;
    if n == 0 { None } else { Some(n) }
}

/// Render the affordances as the **numbered reply block** appended to an OA message — one `N.` line
/// per affordance (1-based), a `!enabled` one prefixed with [`LOCK_GLYPH`] and suffixed `(locked)`.
/// `None` when there are no affordances (a terminal room — nothing to reply). The header tells the
/// user how to act on WeChat: reply with the number.
pub fn render_affordance_block(actions: &[Action]) -> Option<String> {
    if actions.is_empty() {
        return None;
    }
    let mut out = String::from("Reply with the number of your move:");
    for (i, a) in actions.iter().enumerate() {
        let n = i + 1; // 1-based reply number
        if a.enabled {
            out.push_str(&format!("\n{n}. {}", a.label));
        } else {
            out.push_str(&format!("\n{n}. {LOCK_GLYPH}{} (locked)", a.label));
        }
    }
    Some(out)
}

/// The **text payload** of an OA message — `{ "content": "…" }` (the WeChat `text` object).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextPayload {
    /// The full message body: the rendered surface prose + the numbered affordance block.
    pub content: String,
}

/// A **Customer Service `custom/send` request** — the WeChat `cgi-bin/message/custom/send` body,
/// verbatim. Its serde encoding is exactly the JSON wire body a live OA POSTs to
/// `https://api.weixin.qq.com/cgi-bin/message/custom/send?access_token=<TOKEN>` (a test asserting
/// this struct's shape asserts the real wire shape). Built purely by [`build_present_request`];
/// sent by a [`crate::transport::Transport`]. This is an ACTIVE push (matching the `Frontend`
/// trait's `present`); WeChat also allows a token-free PASSIVE REPLY in the webhook HTTP response,
/// but the active push is the general shape the orchestrator drives (honest scope: it needs a token).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CustomSendRequest {
    /// The target user — the recipient's WeChat OpenID (per-OA opaque handle).
    pub touser: String,
    /// The message type — always [`MSG_TYPE_TEXT`] for the numbered-reply loop.
    pub msgtype: String,
    /// The text body (surface prose + numbered affordance block).
    pub text: TextPayload,
}

/// **Build the `custom/send` request that presents `surface` + `actions` to `openid`** — the pure
/// Surface→(text + numbered reply list) mapping. The prose is the deos view-tree walked into
/// WeChat-flavored text ([`render_surface_text`]); the affordances are appended as a numbered list
/// ([`render_affordance_block`]) the user replies to by number. A `!enabled` affordance is rendered
/// dimmed ([`LOCK_GLYPH`] + `(locked)`) but still numbered — the cap tooth shown, not hidden (the
/// executor refuses it on `advance`).
pub fn build_present_request(
    openid: &str,
    surface: &Surface,
    actions: &[Action],
) -> CustomSendRequest {
    let mut content = render_surface_text(surface);
    if let Some(block) = render_affordance_block(actions) {
        if !content.is_empty() {
            content.push_str("\n\n");
        }
        content.push_str(&block);
    }
    CustomSendRequest {
        touser: openid.to_string(),
        msgtype: MSG_TYPE_TEXT.to_string(),
        text: TextPayload { content },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The RICH alternative — a Mini-Program card payload (real buttons in WXML).
// ─────────────────────────────────────────────────────────────────────────────

/// One **Mini-Program card button** — a real tappable affordance in a Mini-Program's WXML (which,
/// unlike the OA, CAN render arbitrary buttons). Carries the affordance `{turn, arg}` a tap fires
/// back to the MP backend, and `enabled` (a `!enabled` button renders dimmed but still fires — the
/// executor is the sole referee).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MiniProgramButton {
    /// The button label (the affordance's human text).
    pub label: String,
    /// The affordance verb (the dungeon's `"choose"`).
    pub turn: String,
    /// The affordance argument (the scene choice index).
    pub arg: i64,
    /// Whether the affordance is currently eligible (a decoration; the executor still refuses an
    /// ineligible move on `advance`).
    pub enabled: bool,
}

/// A **Mini-Program card** payload — the RICH surface alternative to the OA numbered reply. The MP
/// renders `body` as text and `buttons` as real WXML buttons (each tap fires its `{turn, arg}` back
/// to the MP backend, which resolves it on the core exactly like a numbered reply). This is the
/// heavier path (Mini-Program review + custom WXML); the OA numbered-reply is canonical.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MiniProgramCard {
    /// The card body text (the rendered surface prose).
    pub body: String,
    /// One button per cap-gated affordance (the ballot options).
    pub buttons: Vec<MiniProgramButton>,
}

/// **Build the Mini-Program card payload** presenting `surface` + `actions` — the pure
/// Surface→(text + real buttons) mapping for the rich MP surface. One [`MiniProgramButton`] per
/// affordance, carrying its `{turn, arg, enabled}`. Same affordances as the OA numbered list.
pub fn build_miniprogram_card(surface: &Surface, actions: &[Action]) -> MiniProgramCard {
    MiniProgramCard {
        body: render_surface_text(surface),
        buttons: actions
            .iter()
            .map(|a| MiniProgramButton {
                label: a.label.clone(),
                turn: a.turn.clone(),
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect(),
    }
}
