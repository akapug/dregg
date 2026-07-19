//! # `overlay` — the transparent OBS vote overlay + the live SSE push
//!
//! The spectator surface of the crowd-stream engine (`docs/CROWD-STREAM-ENGINE-DESIGN.md`): a
//! **transparent-background OBS browser source** that shows the crowd's live vote tally, updated by
//! a real **server→browser push**. There is no SSE/WebSocket anywhere else in `dreggnet-web` today
//! (the only liveness is a client-initiated `X-Fragment` swap on the acting client's OWN POST); an
//! overlay showing *other people's* votes needs the server to push, so this module adds the first
//! `axum::response::sse::Sse` route + a broadcast-on-vote fan-out.
//!
//! ## The pieces
//!
//! * [`OverlayState`] — a [`crate::crowd_round::CrowdRound`] behind a mutex + a
//!   [`tokio::sync::broadcast`] channel of rendered tally-widget HTML. An ingest updates the round
//!   and broadcasts the re-rendered widget to every connected overlay.
//! * [`overlay_document`] — the transparent OBS page: `background: transparent`, all chrome
//!   stripped, one `#tally` container the SSE client swaps `innerHTML` on. It reuses the deos
//!   [`deos_view::render_html`] renderer (the SAME `ViewNode` IR the cockpit paints) for the widget.
//! * [`overlay_router`] — `GET /overlay` (the page), `GET /overlay/sse` (the push stream),
//!   `POST /overlay/ingest` + `/overlay/ingest/youtube` (feed votes; each broadcasts the new tally).
//!
//! ## Honest scope
//!
//! The widget is a **static snapshot re-rendered + pushed server-side** on every vote (not an in-tab
//! wasm executor like the deos live cards) — right for an overlay whose data comes from the stream,
//! not from the viewer's tab. Resolving a window into a certified world turn ([`OverlayState::close_tick`])
//! needs a live game `WorldCell` + `Scene` and a timer; the demo mount exercises ingest→push, and a
//! deployment supplies the world + interval (see [`OverlayState::close_tick`]). Platform API keys, an
//! OBS instance, and a LIVE-enabled channel are ember's.

use std::convert::Infallible;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use axum::Router;
use axum::extract::State;
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::response::{Html, Json};
use axum::routing::{get, post};
use tokio::sync::broadcast;
use tokio_stream::wrappers::BroadcastStream;
use tokio_stream::{Stream, StreamExt};

use deos_view::{ViewNode, render_html};
use dregg_stream_ingest::{PlatformAdapter, StreamEvent, YouTubeAdapter};
use dungeon_on_dregg::collective::{CertifiedTurn, CollectiveError, Proposal, QUORUM};
use dungeon_on_dregg::narrator::Command;
use spween_dregg::{Scene, WorldCell};

use crate::crowd_round::{CrowdRound, TallyPreview};

/// The broadcast channel depth — a slow overlay that falls this far behind drops the stale frames
/// (a `Lagged` the SSE stream skips) and catches up on the next push. Tally frames are idempotent
/// snapshots, so a dropped intermediate frame is harmless.
const BROADCAST_CAPACITY: usize = 64;

/// **The live overlay state.** Wraps a [`CrowdRound`] (the vote accumulator) and a broadcast
/// channel of rendered tally-widget HTML. Every ingest advances the round and pushes the freshly
/// rendered widget to all connected overlays; `GET /overlay/sse` subscribes.
pub struct OverlayState {
    round: Mutex<CrowdRound>,
    tx: broadcast::Sender<String>,
    /// The last rendered widget HTML — the first-paint a fresh `GET /overlay` / a new SSE
    /// subscriber receives before the next push.
    last_html: Mutex<String>,
}

impl OverlayState {
    /// Wrap a [`CrowdRound`] in a fresh overlay state (an empty broadcast + the round's current
    /// tally as the first paint).
    pub fn new(round: CrowdRound) -> Arc<OverlayState> {
        let (tx, _rx) = broadcast::channel(BROADCAST_CAPACITY);
        let html = render_tally_widget_html(&round.preview());
        Arc::new(OverlayState {
            round: Mutex::new(round),
            tx,
            last_html: Mutex::new(html),
        })
    }

    /// Ingest normalized stream events into the round and push the new tally. Returns the fresh
    /// preview (what the overlay now shows).
    pub fn ingest_events(&self, events: Vec<StreamEvent>) -> TallyPreview {
        let preview = {
            let mut round = self.round.lock().unwrap();
            round.ingest_batch(events);
            round.preview()
        };
        self.publish(&preview);
        preview
    }

    /// Ingest a raw YouTube `liveChatMessages` payload (parsed by the [`YouTubeAdapter`]) and push
    /// the new tally.
    pub fn ingest_youtube(&self, raw: &str) -> TallyPreview {
        self.ingest_events(YouTubeAdapter.parse(raw))
    }

    /// **Close the current window into the game world** → ONE certified turn, then push the (now
    /// reset, or unchanged-on-refusal) tally. This is the "on a timer close→resolve→advance" tick:
    /// a deployment calls it every round window with the live game `world`/`scene`. Returns the
    /// [`CertifiedTurn`] on success, or the [`CollectiveError`] (below quorum / illegal command) —
    /// see [`CrowdRound::close_into_world`].
    pub fn close_tick(
        &self,
        world: &WorldCell,
        scene: &Scene,
    ) -> Result<CertifiedTurn, CollectiveError> {
        let (result, preview) = {
            let mut round = self.round.lock().unwrap();
            let result = round.close_into_world(world, scene);
            (result, round.preview())
        };
        self.publish(&preview);
        result
    }

    /// Render + store + broadcast a tally snapshot. `send` returns `Err` only when no overlay is
    /// connected yet — harmless (the stored `last_html` still feeds the next subscriber's first
    /// paint).
    fn publish(&self, preview: &TallyPreview) -> usize {
        let html = render_tally_widget_html(preview);
        *self.last_html.lock().unwrap() = html.clone();
        self.tx.send(html).unwrap_or(0)
    }

    /// The current widget HTML (the first paint for a fresh page / SSE subscriber).
    fn current_html(&self) -> String {
        self.last_html.lock().unwrap().clone()
    }

    /// Subscribe to the tally-push stream.
    fn subscribe(&self) -> broadcast::Receiver<String> {
        self.tx.subscribe()
    }
}

/// **Assemble the overlay router.** Mounted into the merged app by `make_app`
/// (`docs/CROWD-STREAM-ENGINE-DESIGN.md`):
/// * `GET  /overlay`               — the transparent OBS page (add as a browser source);
/// * `GET  /overlay/sse`           — the server→browser tally push (an `EventSource` stream);
/// * `POST /overlay/ingest`        — feed normalized [`StreamEvent`]s (JSON array); pushes the tally;
/// * `POST /overlay/ingest/youtube`— feed a raw YouTube `liveChatMessages` JSON body; pushes the tally.
pub fn overlay_router(state: Arc<OverlayState>) -> Router {
    Router::new()
        .route("/overlay", get(get_overlay))
        .route("/overlay/sse", get(get_overlay_sse))
        .route("/overlay/ingest", post(post_overlay_ingest))
        .route("/overlay/ingest/youtube", post(post_overlay_ingest_youtube))
        .with_state(state)
}

/// A demo overlay over the keep round (trade blows / press on) — what `make_app` mounts so the
/// route exists out of the box. A real deployment builds its own [`OverlayState::new`] over the
/// round for the game being streamed.
pub fn demo_state() -> Arc<OverlayState> {
    let round = CrowdRound::open(
        "The gate-warden bars the way — what does the party do?",
        vec![
            Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
            Proposal::new("Press past into the plundered hall", Command::press_on()),
        ],
        vec!["trade blows".to_string(), "press on".to_string()],
        QUORUM,
    );
    OverlayState::new(round)
}

/// `GET /overlay` — the transparent OBS page, first-painted at the current tally.
async fn get_overlay(State(state): State<Arc<OverlayState>>) -> Html<String> {
    Html(overlay_document(&state.current_html()))
}

/// `GET /overlay/sse` — the tally push. Emits the current tally immediately, then every broadcast
/// frame as a `tally` SSE event. A lagged subscriber's dropped frames are skipped (the next frame
/// is a full snapshot). 15s keep-alive comments hold the connection open through idle stretches.
async fn get_overlay_sse(
    State(state): State<Arc<OverlayState>>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let initial = state.current_html();
    let live = BroadcastStream::new(state.subscribe()).filter_map(|msg| match msg {
        Ok(html) => Some(Ok::<Event, Infallible>(tally_event(html))),
        // A `Lagged` (the subscriber fell behind the channel depth) — skip; the next frame is a
        // complete snapshot, so no state is lost.
        Err(_lagged) => None,
    });
    let stream = tokio_stream::once(Ok::<Event, Infallible>(tally_event(initial))).chain(live);
    Sse::new(stream).keep_alive(
        KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("keep-alive"),
    )
}

/// `POST /overlay/ingest` — feed a JSON array of normalized [`StreamEvent`]s; returns the new tally.
async fn post_overlay_ingest(
    State(state): State<Arc<OverlayState>>,
    Json(events): Json<Vec<StreamEvent>>,
) -> Json<TallyPreview> {
    Json(state.ingest_events(events))
}

/// `POST /overlay/ingest/youtube` — feed a raw YouTube `liveChatMessages` JSON body; returns the
/// new tally. The body is the platform payload verbatim (what a `liveChatMessages.list` poll hands
/// back); the [`YouTubeAdapter`] normalizes it.
async fn post_overlay_ingest_youtube(
    State(state): State<Arc<OverlayState>>,
    body: String,
) -> Json<TallyPreview> {
    Json(state.ingest_youtube(&body))
}

/// One SSE `tally` frame carrying a widget-HTML fragment. `render_html` output is newline-free, so
/// it rides as a single SSE `data:` line.
fn tally_event(html: String) -> Event {
    Event::default().event("tally").data(html)
}

/// Render the tally widget to an HTML fragment via the deos [`render_html`] renderer — the SAME
/// `ViewNode` IR the native/web cockpit paints. Static nodes ([`ViewNode::Progress`]/`Pill`/`Text`)
/// so each pushed snapshot is complete (no in-tab executor).
pub fn render_tally_widget_html(preview: &TallyPreview) -> String {
    render_html(&tally_widget_tree(preview), &[])
}

/// Build the tally widget's [`ViewNode`] tree: a titled section of one row per option (label +
/// a static vote bar), a divider, and a quorum pill + voter count.
fn tally_widget_tree(preview: &TallyPreview) -> ViewNode {
    // The bar scale is the current leader's votes (min 1), so the leading bar is full and the
    // others read as a fraction of it.
    let max = preview
        .options
        .iter()
        .map(|o| o.votes)
        .max()
        .unwrap_or(0)
        .max(1);

    let rows: Vec<ViewNode> = preview
        .options
        .iter()
        .enumerate()
        .map(|(i, o)| {
            let marker = if preview.leader == Some(i) {
                "\u{25B6} "
            } else {
                "\u{2003} "
            };
            ViewNode::Row(vec![
                ViewNode::Text(format!("{marker}{}", o.label)),
                ViewNode::Progress {
                    value: o.votes,
                    max,
                    label: format!("{} votes", o.votes),
                },
            ])
        })
        .collect();

    let (pill_text, pill_tag) = if preview.quorum_met() {
        (
            format!("QUORUM MET {}/{}", preview.total, preview.quorum),
            "good",
        )
    } else {
        (
            format!("{}/{} to quorum", preview.total, preview.quorum),
            "warn",
        )
    };

    ViewNode::Section {
        title: preview.question.clone(),
        tag: "crowd".to_string(),
        children: vec![
            ViewNode::VStack(rows),
            ViewNode::Divider,
            ViewNode::Row(vec![
                ViewNode::Pill {
                    text: pill_text,
                    tag: pill_tag.to_string(),
                    slot: None,
                    cases: vec![],
                },
                ViewNode::Text(format!("{} voters", preview.voters)),
            ]),
        ],
    }
}

/// **The transparent OBS overlay document.** A full standalone page with `background: transparent`
/// and all cockpit chrome stripped (no card frame, no nav), sized as an overlay browser-source. The
/// `#tally` container holds the first-paint widget; the [`OVERLAY_JS`] client subscribes to
/// `/overlay/sse` and swaps its `innerHTML` on each pushed frame.
pub fn overlay_document(widget_html: &str) -> String {
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>Crowd Vote Overlay</title>\n\
<style>{OVERLAY_CSS}</style>\n\
</head>\n\
<body>\n\
<main id=\"tally\" class=\"overlay-root\">{widget}</main>\n\
<script>{OVERLAY_JS}</script>\n\
</body>\n\
</html>\n",
        OVERLAY_CSS = OVERLAY_CSS,
        widget = widget_html,
        OVERLAY_JS = OVERLAY_JS,
    )
}

/// The overlay stylesheet — transparent page, a translucent panel behind the widget for legibility
/// over arbitrary video, and styling for the deos widget classes `render_html` emits. Self-contained
/// (it does NOT pull the opaque cockpit CSS): an OBS browser source composites this straight onto the
/// stream.
const OVERLAY_CSS: &str = "\
:root { color-scheme: dark; }\
html, body { margin: 0; padding: 0; background: transparent; }\
body { font-family: ui-sans-serif, system-ui, -apple-system, 'Segoe UI', Roboto, sans-serif; }\
.overlay-root { padding: 16px; max-width: 520px; }\
.deos-section { background: rgba(12,14,22,0.72); border: 1px solid rgba(255,255,255,0.14); border-radius: 14px; padding: 14px 16px; box-shadow: 0 6px 24px rgba(0,0,0,0.45); backdrop-filter: blur(4px); }\
.deos-section-title { font-size: 18px; font-weight: 700; color: #f4f6ff; margin-bottom: 12px; text-shadow: 0 1px 3px rgba(0,0,0,0.8); }\
.deos-vstack { display: flex; flex-direction: column; gap: 10px; }\
.deos-row { display: flex; align-items: center; gap: 12px; }\
.deos-text { color: #e7ebff; font-size: 15px; text-shadow: 0 1px 3px rgba(0,0,0,0.8); min-width: 160px; }\
.deos-divider { border: 0; border-top: 1px solid rgba(255,255,255,0.14); margin: 12px 0; }\
.deos-progress { flex: 1; }\
.deos-progress-label { display: block; font-size: 12px; color: #aeb6d8; margin-bottom: 3px; text-shadow: 0 1px 2px rgba(0,0,0,0.8); }\
.deos-progress-track { height: 12px; border-radius: 7px; background: rgba(255,255,255,0.10); overflow: hidden; }\
.deos-progress-fill { height: 100%; border-radius: 7px; background: linear-gradient(90deg, #5b8bff, #8b5bff); transition: width 320ms ease; }\
.deos-pill { display: inline-block; padding: 3px 12px; border-radius: 999px; font-size: 13px; font-weight: 700; }\
.deos-pill[data-tag='good'] { background: rgba(60,200,120,0.22); color: #7bf0ad; border: 1px solid rgba(60,200,120,0.5); }\
.deos-pill[data-tag='warn'] { background: rgba(240,190,60,0.18); color: #f5d27a; border: 1px solid rgba(240,190,60,0.45); }\
";

/// The overlay client — subscribe to the tally push and swap `#tally`. `EventSource` auto-reconnects
/// on a dropped connection, so a restarted server / a network blip self-heals with no client code.
const OVERLAY_JS: &str = "\
(function () {\
  var box = document.getElementById('tally');\
  if (!box || typeof EventSource === 'undefined') return;\
  var es = new EventSource('/overlay/sse');\
  es.addEventListener('tally', function (e) { box.innerHTML = e.data; });\
  es.onerror = function () { /* EventSource retries automatically */ };\
})();\
";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn widget_renders_the_tally_snapshot() {
        let state = demo_state();
        let events = YouTubeAdapter.parse(
            r#"{"items":[
                {"snippet":{"type":"superChatEvent","displayMessage":"$5","superChatDetails":{"amountMicros":"5000000","userComment":"trade blows"}},"authorDetails":{"channelId":"UC_a"}},
                {"snippet":{"type":"textMessageEvent","textMessageDetails":{"messageText":"press on"}},"authorDetails":{"channelId":"UC_b"}}
            ]}"#,
        );
        let preview = state.ingest_events(events);
        assert_eq!(preview.total, 6, "$5 trade-blows (5) + a press-on chat (1)");
        assert_eq!(preview.voters, 2);

        let html = render_tally_widget_html(&preview);
        assert!(
            html.contains("deos-section"),
            "the widget is a deos section"
        );
        assert!(html.contains("gate-warden"), "carries the question");
        assert!(html.contains("deos-progress-fill"), "renders vote bars");
        // No newlines in the fragment ⇒ it rides one SSE data: line.
        assert!(
            !html.contains('\n'),
            "render_html output is single-line (SSE-safe)"
        );
    }

    #[test]
    fn overlay_document_is_transparent_and_chrome_free() {
        let doc = overlay_document(&demo_state().current_html());
        assert!(
            doc.contains("background: transparent"),
            "the page background is transparent"
        );
        assert!(
            doc.contains("/overlay/sse"),
            "the client subscribes to the push"
        );
        assert!(
            doc.contains("id=\"tally\""),
            "the swappable container is present"
        );
        // No cockpit back-nav chrome.
        assert!(!doc.contains("all cards"), "no cockpit chrome");
    }

    #[test]
    fn ingest_publishes_to_subscribers() {
        let state = demo_state();
        let mut rx = state.subscribe();
        let _ = state.ingest_events(vec![StreamEvent {
            platform: "youtube".into(),
            author_id: "UC_x".into(),
            kind: dregg_stream_ingest::EventKind::Chat,
            amount_micros: 0,
            text: "press on".into(),
            ts: 0,
        }]);
        let pushed = rx
            .try_recv()
            .expect("a frame was broadcast to the subscriber");
        assert!(
            pushed.contains("deos-section"),
            "the pushed frame is the rendered widget"
        );
    }
}
