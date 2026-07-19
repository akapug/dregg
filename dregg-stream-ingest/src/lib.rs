//! # `dregg-stream-ingest` — the crowd-stream INGESTION layer
//!
//! The dep-light front of the crowd-stream engine (`docs/CROWD-STREAM-ENGINE-DESIGN.md`):
//! a live-stream platform event → a normalized [`StreamEvent`] → a paid-weighted
//! [`WeightedBallot`] a poll can tally. It is deliberately **serde-only** — it carries no
//! dependency on the collective/offering/circuit tree, so it builds and tests in isolation
//! while the rest of the workspace is mid-refactor.
//!
//! ## The shape
//!
//! ```text
//! platform payload (YouTube liveChatMessages JSON / …)
//!   → PlatformAdapter::parse  → Vec<StreamEvent>      (normalized: who, what kind, how much, text)
//!   → events_to_ballots(opts) → Vec<WeightedBallot>   (text → option; Super Chat micros → weight)
//! ```
//!
//! The WIRING that turns these ballots into a real quorum-certified turn (mint a per-voter
//! custody key, cast a signed ballot into `dungeon_on_dregg::collective::CollectiveRound`,
//! `resolve_into_world`) lives in `dreggnet-web::crowd_round` — the layer that pays for the
//! offering-stack deps. This crate stops at the pure, testable mapping.
//!
//! ## Honest scope
//!
//! The only official/best-paying platform modeled here is **YouTube** ([`YouTubeAdapter`]).
//! Twitch (EventSub/IRC cheers) and TikTok (unofficial webcast gifts) are named seams: a new
//! [`PlatformAdapter`] impl each, producing the SAME [`StreamEvent`]. The mapping from a paid
//! amount to a vote weight is a *policy* ([`weight_for`]) — whole dollars, floored at one — not
//! a platform fact; tune it per deployment.

use serde::{Deserialize, Serialize};

/// The kind of a live-stream interaction. `Chat`/`Like` are unpaid (weight 1); `SuperChat`/
/// `Gift` carry a paid [`StreamEvent::amount_micros`] that scales their vote weight.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EventKind {
    /// A plain chat message (unpaid).
    Chat,
    /// A YouTube Super Chat / Twitch cheer — a paid, highlighted message.
    SuperChat,
    /// A paid gift / Super Sticker / TikTok gift.
    Gift,
    /// A like / heart tap (unpaid).
    Like,
}

impl EventKind {
    /// Whether this kind carries a paid amount that should scale its vote weight.
    pub fn is_paid(self) -> bool {
        matches!(self, EventKind::SuperChat | EventKind::Gift)
    }
}

/// A **normalized live-stream event** — the platform-agnostic shape every [`PlatformAdapter`]
/// produces. One viewer interaction: who authored it, what kind it was, how much (if paid) in
/// micros of the platform currency, its display text, and its timestamp (unix seconds; `0` when
/// the platform payload carried none / an unparseable one).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StreamEvent {
    /// The source platform tag (e.g. `"youtube"`).
    pub platform: String,
    /// The author's stable platform id (a YouTube channel id, a Twitch user id, …). This is the
    /// per-viewer identity the round derives a custody key from.
    pub author_id: String,
    /// The interaction kind.
    pub kind: EventKind,
    /// The paid amount in micros of the platform currency (`amountMicros`); `0` for unpaid kinds.
    pub amount_micros: u64,
    /// The message text (a Super Chat's user comment, a chat's message body). What a vote is
    /// matched against.
    pub text: String,
    /// Unix-seconds timestamp of the event; `0` if the payload carried none / an unparseable one.
    pub ts: i64,
}

/// A **paid-weighted ballot** — a viewer's vote for one poll option, weighted by what they paid.
/// This is the pure, engine-free hand-off shape: the round driver mints a custody key per
/// [`voter`](Self::voter) and casts a signed ballot for [`option_idx`](Self::option_idx) with
/// [`weight`](Self::weight) influence (a Super Chat outweighs a plain chat).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WeightedBallot {
    /// The voter's platform author id (the same [`StreamEvent::author_id`]).
    pub voter: String,
    /// The chosen poll option (index into the round's option list).
    pub option_idx: usize,
    /// The vote's influence — [`weight_for`] of the source event (≥ 1).
    pub weight: u64,
}

/// A source platform's ingestion adapter — parse its raw payload into normalized
/// [`StreamEvent`]s. A new platform (Twitch EventSub, TikTok webcast) is one more impl
/// producing the SAME event shape; the downstream ballot mapping is platform-agnostic.
pub trait PlatformAdapter {
    /// The platform tag this adapter stamps onto its events (matches [`StreamEvent::platform`]).
    fn platform(&self) -> &str;
    /// Parse a raw platform payload into normalized events. Malformed / unrecognized entries are
    /// **skipped**, never fatal — a live poll must not die on one bad chat frame.
    fn parse(&self, raw: &str) -> Vec<StreamEvent>;
}

/// The **YouTube Live Chat** adapter — the one official, best-paying platform (Super Chat is a
/// documented 70/30 split). Parses a `liveChatMessages.list` API response
/// ([`parse_youtube_livechat`]).
#[derive(Clone, Copy, Debug, Default)]
pub struct YouTubeAdapter;

impl PlatformAdapter for YouTubeAdapter {
    fn platform(&self) -> &str {
        "youtube"
    }
    fn parse(&self, raw: &str) -> Vec<StreamEvent> {
        parse_youtube_livechat(raw)
    }
}

/// **Parse a YouTube `liveChatMessages.list` response** into normalized [`StreamEvent`]s.
///
/// Reads the documented API shape: a top-level `items` array whose each entry carries a
/// `snippet` (`type`, `publishedAt`, `displayMessage`, and the per-type detail object —
/// `superChatDetails.amountMicros`, `textMessageDetails.messageText`) and an `authorDetails`
/// (`channelId`). Recognized `snippet.type`s:
///
/// * `textMessageEvent` → [`EventKind::Chat`] (text = `textMessageDetails.messageText`);
/// * `superChatEvent`   → [`EventKind::SuperChat`] (amount = `superChatDetails.amountMicros`,
///   text = `superChatDetails.userComment`);
/// * `superStickerEvent`→ [`EventKind::Gift`] (amount = `superStickerDetails.amountMicros`).
///
/// Other event types (memberships, sponsors) carry no vote and are skipped. `amountMicros`
/// arrives as a JSON **string** in the API; a numeric form is also accepted. Malformed items
/// (no author, unparseable) are skipped — the parse never fails on partial input, it returns
/// what it could read.
pub fn parse_youtube_livechat(json: &str) -> Vec<StreamEvent> {
    let root: serde_json::Value = match serde_json::from_str(json) {
        Ok(v) => v,
        Err(_) => return Vec::new(),
    };
    let items = match root.get("items").and_then(|v| v.as_array()) {
        Some(a) => a,
        None => return Vec::new(),
    };
    items.iter().filter_map(parse_youtube_item).collect()
}

/// Parse one `items[]` entry; `None` if it is not a vote-bearing, author-attributed event.
fn parse_youtube_item(item: &serde_json::Value) -> Option<StreamEvent> {
    let snippet = item.get("snippet")?;
    let ty = snippet.get("type").and_then(|v| v.as_str()).unwrap_or("");

    // Author id: the documented location is `authorDetails.channelId`; some payloads carry it
    // as `snippet.authorChannelId` — accept either. No author ⇒ no attributable ballot.
    let author_id = item
        .get("authorDetails")
        .and_then(|a| a.get("channelId"))
        .and_then(|v| v.as_str())
        .or_else(|| snippet.get("authorChannelId").and_then(|v| v.as_str()))
        .unwrap_or("")
        .to_string();
    if author_id.is_empty() {
        return None;
    }

    let ts = snippet
        .get("publishedAt")
        .and_then(|v| v.as_str())
        .and_then(rfc3339_to_unix_seconds)
        .unwrap_or(0);
    let display = snippet
        .get("displayMessage")
        .and_then(|v| v.as_str())
        .unwrap_or("");

    let mk = |kind: EventKind, amount_micros: u64, text: String| StreamEvent {
        platform: "youtube".to_string(),
        author_id: author_id.clone(),
        kind,
        amount_micros,
        text,
        ts,
    };

    match ty {
        "textMessageEvent" => {
            let text = snippet
                .get("textMessageDetails")
                .and_then(|d| d.get("messageText"))
                .and_then(|v| v.as_str())
                .filter(|s| !s.is_empty())
                .unwrap_or(display)
                .to_string();
            Some(mk(EventKind::Chat, 0, text))
        }
        "superChatEvent" => {
            let details = snippet.get("superChatDetails");
            let amount = details
                .and_then(|d| d.get("amountMicros"))
                .and_then(parse_micros)
                .unwrap_or(0);
            let text = details
                .and_then(|d| d.get("userComment"))
                .and_then(|v| v.as_str())
                .filter(|s| !s.is_empty())
                .unwrap_or(display)
                .to_string();
            Some(mk(EventKind::SuperChat, amount, text))
        }
        "superStickerEvent" => {
            let amount = snippet
                .get("superStickerDetails")
                .and_then(|d| d.get("amountMicros"))
                .and_then(parse_micros)
                .unwrap_or(0);
            Some(mk(EventKind::Gift, amount, display.to_string()))
        }
        // Memberships, sponsor milestones, tombstones, … carry no vote.
        _ => None,
    }
}

/// `amountMicros` is a JSON **string** in the API (`"5000000"`); accept a bare number too.
fn parse_micros(v: &serde_json::Value) -> Option<u64> {
    if let Some(s) = v.as_str() {
        s.trim().parse::<u64>().ok()
    } else {
        v.as_u64()
    }
}

/// **The vote weight of an event** — the paid-influence policy. Unpaid kinds (chat, like) weigh
/// `1`; paid kinds (Super Chat, gift) weigh **one per whole dollar** of the paid amount, floored
/// at `1` (a sub-dollar tip still counts as a single vote). E.g. a `$5.00` Super Chat
/// (`5_000_000` micros) weighs `5`; a `$0.50` Super Chat weighs `1`.
///
/// This is deliberately *bounded and legible*, not `amountMicros` verbatim (which would let one
/// Super Chat mint millions of ballots). The round driver additionally caps the per-voter weight
/// when it materializes seats.
pub fn weight_for(event: &StreamEvent) -> u64 {
    if event.kind.is_paid() {
        (event.amount_micros / 1_000_000).max(1)
    } else {
        1
    }
}

/// **Map events to weighted ballots** against a poll's `options`. Each event whose text names an
/// option becomes one [`WeightedBallot`] for that option, weighted by [`weight_for`]; an event
/// that names no option is dropped. Matching ([`match_option`]) accepts an explicit numeric vote
/// (`"2"`, `"!vote 2"`, `"option 2"`, `"#2"` — 1-based) or a keyword (an option label appearing
/// in the text, longest-label-wins). Case-insensitive.
pub fn events_to_ballots(events: &[StreamEvent], options: &[&str]) -> Vec<WeightedBallot> {
    events
        .iter()
        .filter_map(|e| {
            match_option(&e.text, options).map(|option_idx| WeightedBallot {
                voter: e.author_id.clone(),
                option_idx,
                weight: weight_for(e),
            })
        })
        .collect()
}

/// Match a message to a poll option index, or `None`. Tries an explicit numeric vote first, then
/// a keyword (option-label substring) match, preferring the longest matching label so a short
/// label cannot shadow a longer, more specific one.
fn match_option(text: &str, options: &[&str]) -> Option<usize> {
    let t = text.trim().to_lowercase();
    if t.is_empty() {
        return None;
    }

    // 1) An explicit numeric vote: strip the vote-verb noise and read the first integer as a
    //    1-based option number.
    if let Some(n) = parse_vote_number(&t) {
        if n >= 1 && n <= options.len() {
            return Some(n - 1);
        }
    }

    // 2) A keyword match: the option label appears verbatim in the text. Longest label wins.
    let mut best: Option<(usize, usize)> = None; // (option index, matched label length)
    for (i, opt) in options.iter().enumerate() {
        let label = opt.trim().to_lowercase();
        if label.is_empty() {
            continue;
        }
        if t.contains(&label) {
            let len = label.len();
            if best.map_or(true, |(_, bl)| len > bl) {
                best = Some((i, len));
            }
        }
    }
    best.map(|(i, _)| i)
}

/// Pull a 1-based option number from a vote message, tolerating the common vote-verb prefixes
/// (`!vote 2`, `vote2`, `option 2`, `choice 2`, `#2`, or a bare `2`). Returns the first integer
/// token found, or `None`.
fn parse_vote_number(t: &str) -> Option<usize> {
    let cleaned = t
        .replace('!', " ")
        .replace('#', " ")
        .replace("vote", " ")
        .replace("option", " ")
        .replace("choice", " ");
    cleaned
        .split_whitespace()
        .find_map(|tok| tok.parse::<usize>().ok())
}

/// RFC3339 (`YYYY-MM-DDTHH:MM:SS[.fff][Z|±hh:mm]`) → unix **seconds**, or `None`. A compact,
/// dependency-free parser (integer civil-days arithmetic) for the `publishedAt` timestamp — the
/// fractional seconds and any timezone offset are ignored (YouTube stamps UTC `Z`).
fn rfc3339_to_unix_seconds(s: &str) -> Option<i64> {
    let (date, time) = s.split_once('T')?;
    let mut d = date.split('-');
    let year: i64 = d.next()?.parse().ok()?;
    let month: i64 = d.next()?.parse().ok()?;
    let day: i64 = d.next()?.parse().ok()?;
    if d.next().is_some() || !(1..=12).contains(&month) || !(1..=31).contains(&day) {
        return None;
    }

    // Strip the fractional part and any timezone suffix down to HH:MM:SS.
    let time = time.trim_end_matches('Z');
    let time = time
        .split_once('+')
        .map(|(h, _)| h)
        .unwrap_or(time)
        .split_once('.')
        .map(|(h, _)| h)
        .unwrap_or(time);
    let mut tp = time.split(':');
    let hour: i64 = tp.next()?.parse().ok()?;
    let minute: i64 = tp.next()?.parse().ok()?;
    let second: i64 = tp.next().unwrap_or("0").parse().ok()?;
    if !(0..=23).contains(&hour) || !(0..=59).contains(&minute) || !(0..=60).contains(&second) {
        return None;
    }

    Some(days_from_civil(year, month, day) * 86_400 + hour * 3_600 + minute * 60 + second)
}

/// Days since 1970-01-01 for a proleptic-Gregorian `y-m-d` (Howard Hinnant's `days_from_civil`,
/// pure integer arithmetic).
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = (if y >= 0 { y } else { y - 399 }) / 400;
    let yoe = y - era * 400; // [0, 399]
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146_097 + doe - 719_468
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fixture `liveChatMessages.list` response: a plain chat that names an option, a Super Chat
    /// (with a paid amount + comment) that names a different option, and a chat that names none.
    fn youtube_fixture() -> &'static str {
        r#"{
          "kind": "youtube#liveChatMessageListResponse",
          "items": [
            {
              "snippet": {
                "type": "textMessageEvent",
                "publishedAt": "2024-06-01T12:00:05Z",
                "displayMessage": "please press on!",
                "textMessageDetails": { "messageText": "please press on!" }
              },
              "authorDetails": { "channelId": "UC_viewer_A" }
            },
            {
              "snippet": {
                "type": "superChatEvent",
                "publishedAt": "2024-06-01T12:00:07Z",
                "displayMessage": "$5.00 from Viewer B",
                "superChatDetails": {
                  "amountMicros": "5000000",
                  "currency": "USD",
                  "userComment": "TRADE BLOWS now!!"
                }
              },
              "authorDetails": { "channelId": "UC_viewer_B" }
            },
            {
              "snippet": {
                "type": "textMessageEvent",
                "publishedAt": "2024-06-01T12:00:09Z",
                "displayMessage": "hello everyone lol",
                "textMessageDetails": { "messageText": "hello everyone lol" }
              },
              "authorDetails": { "channelId": "UC_viewer_C" }
            }
          ]
        }"#
    }

    #[test]
    fn parses_youtube_chat_superchat_and_plain() {
        let events = parse_youtube_livechat(youtube_fixture());
        assert_eq!(events.len(), 3, "all three items normalize to events");

        // The chat.
        assert_eq!(events[0].kind, EventKind::Chat);
        assert_eq!(events[0].author_id, "UC_viewer_A");
        assert_eq!(events[0].amount_micros, 0);
        assert_eq!(events[0].text, "please press on!");
        assert_eq!(events[0].platform, "youtube");
        // publishedAt was parsed to a real unix timestamp (not the 0 fallback).
        assert!(
            events[0].ts > 1_700_000_000,
            "publishedAt parsed: {}",
            events[0].ts
        );

        // The Super Chat carries its paid amount + the user comment as text.
        assert_eq!(events[1].kind, EventKind::SuperChat);
        assert_eq!(events[1].author_id, "UC_viewer_B");
        assert_eq!(events[1].amount_micros, 5_000_000);
        assert_eq!(events[1].text, "TRADE BLOWS now!!");

        // The non-voting chat still normalizes (it just names no option downstream).
        assert_eq!(events[2].kind, EventKind::Chat);
        assert_eq!(events[2].author_id, "UC_viewer_C");
    }

    #[test]
    fn maps_events_to_weighted_ballots() {
        let events = parse_youtube_livechat(youtube_fixture());
        let options = ["trade blows", "press on"];
        let ballots = events_to_ballots(&events, &options);

        // Two of the three events name an option; the "hello everyone" chat drops out.
        assert_eq!(
            ballots.len(),
            2,
            "only the two option-naming events produce ballots"
        );

        // Viewer A's plain chat → option 1 ("press on"), weight 1.
        let a = ballots
            .iter()
            .find(|b| b.voter == "UC_viewer_A")
            .expect("A voted");
        assert_eq!(a.option_idx, 1, "'press on' is option index 1");
        assert_eq!(a.weight, 1, "a plain chat weighs one");

        // Viewer B's $5 Super Chat → option 0 ("trade blows"), weight 5 (one per dollar).
        let b = ballots
            .iter()
            .find(|b| b.voter == "UC_viewer_B")
            .expect("B voted");
        assert_eq!(b.option_idx, 0, "'trade blows' is option index 0");
        assert_eq!(b.weight, 5, "a $5 Super Chat weighs five");

        // Viewer C named no option.
        assert!(
            ballots.iter().all(|b| b.voter != "UC_viewer_C"),
            "the non-matching chat cast nothing"
        );
    }

    #[test]
    fn numeric_and_keyword_voting_both_resolve() {
        let options = ["trade blows", "press on"];
        let ev = |author: &str, text: &str| StreamEvent {
            platform: "youtube".into(),
            author_id: author.into(),
            kind: EventKind::Chat,
            amount_micros: 0,
            text: text.into(),
            ts: 0,
        };
        // "!vote 1" / "2" / "#2" resolve numerically (1-based); a keyword resolves by label.
        let events = [
            ev("n1", "!vote 1"),
            ev("n2", "2"),
            ev("n3", "option 2 please"),
            ev("k1", "i say we PRESS ON"),
            ev("z", "whatever"),
        ];
        let ballots = events_to_ballots(&events, &options);
        let idx = |a: &str| ballots.iter().find(|b| b.voter == a).map(|b| b.option_idx);
        assert_eq!(idx("n1"), Some(0), "!vote 1 → option 0");
        assert_eq!(idx("n2"), Some(1), "2 → option 1");
        assert_eq!(idx("n3"), Some(1), "option 2 → option 1");
        assert_eq!(idx("k1"), Some(1), "keyword 'press on' → option 1");
        assert_eq!(idx("z"), None, "an unrelated message names no option");
    }

    #[test]
    fn weight_policy_is_whole_dollars_floored_at_one() {
        let paid = |micros: u64| StreamEvent {
            platform: "youtube".into(),
            author_id: "x".into(),
            kind: EventKind::SuperChat,
            amount_micros: micros,
            text: String::new(),
            ts: 0,
        };
        assert_eq!(weight_for(&paid(2_000_000)), 2, "$2 → 2");
        assert_eq!(weight_for(&paid(500_000)), 1, "$0.50 → floored to 1");
        assert_eq!(
            weight_for(&paid(0)),
            1,
            "a zero-amount paid event still weighs 1"
        );
    }

    #[test]
    fn malformed_payloads_are_skipped_not_fatal() {
        assert!(parse_youtube_livechat("not json at all").is_empty());
        assert!(parse_youtube_livechat("{}").is_empty(), "no items array");
        // An item with no author is dropped; a good item beside it survives.
        let mixed = r#"{"items":[
            {"snippet":{"type":"textMessageEvent","displayMessage":"press on"}},
            {"snippet":{"type":"textMessageEvent","displayMessage":"press on"},"authorDetails":{"channelId":"UC_ok"}}
        ]}"#;
        let events = parse_youtube_livechat(mixed);
        assert_eq!(events.len(), 1, "only the author-attributed item survives");
        assert_eq!(events[0].author_id, "UC_ok");
    }

    #[test]
    fn rfc3339_parses_a_known_instant() {
        // 2024-06-01T12:00:05Z = 1717243205 (unix seconds).
        assert_eq!(
            rfc3339_to_unix_seconds("2024-06-01T12:00:05Z"),
            Some(1_717_243_205)
        );
        // 1970 epoch.
        assert_eq!(rfc3339_to_unix_seconds("1970-01-01T00:00:00Z"), Some(0));
        // Fractional + offset are tolerated (offset ignored — treated as the wall-clock UTC).
        assert_eq!(
            rfc3339_to_unix_seconds("2024-06-01T12:00:05.123Z"),
            Some(1_717_243_205)
        );
        assert_eq!(rfc3339_to_unix_seconds("garbage"), None);
    }
}
