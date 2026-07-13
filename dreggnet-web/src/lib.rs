//! # `dreggnet-web` — the WEB [`Frontend`] over the ONE offering core.
//!
//! The third surface (Discord #0 · Telegram · **web**) over the frontend-agnostic
//! [`dreggnet_offerings`] core. A [`WebFrontend`] is an **affordance-renderer**: it derives a
//! per-web-user [`DreggIdentity`], `present`s an offering's [`Surface`], `collect`s a web POST
//! back into a typed `(SessionId, Action, DreggIdentity)`, and — its web-specific job —
//! [`renders`](WebFrontend::render) that deos [`Surface`] into an **HTML fragment**: the room
//! prose/state plus a `<form>`/`<button>` per cap-gated affordance, each POSTing its [`Action`].
//!
//! [`WebState`] hosts the axum surface over a [`DungeonOffering`] (offering #0):
//! - `GET  /session/{id}`        — open (lazily, seeded from the id) + render the current
//!   [`Surface`] as a full HTML page (the fragment wrapped in a document);
//! - `POST /session/{id}/act`    — read the web identity (a `dregg_user` cookie / `?user=`
//!   param), [`collect`](Frontend::collect) the `{turn, arg}` form back into the presented
//!   [`Action`], [`advance`](dreggnet_offerings::Offering::advance) ONE real turn on the
//!   substrate, and re-render (a legal move lands a real receipt; an illegal one is a real
//!   executor refusal surfaced as an honest banner — the anti-ghost tooth);
//! - `GET  /session/{id}/verify` — re-verify the whole committed chain by replay.
//!
//! The executor stays the sole referee: the web surface never trusts a rendered `enabled`
//! decoration — a crafted POST of a dimmed affordance still lands as a real
//! [`Outcome::Refused`](dreggnet_offerings::Outcome::Refused) on the substrate.
//!
//! ## The multi-offering catalog — all offerings, any surface
//!
//! [`WebState`] above hosts offering #0 alone. [`CatalogState`] + [`catalog_router`] make the web a
//! **multi-offering catalog** over the frontend-agnostic [`OfferingHost`]: browse the registered
//! offerings and play ANY of them in the browser through the SAME verbs, the `Session` type erased.
//! - `GET  /offerings`                           — the catalog (a card + "play" link per offering);
//! - `GET  /offerings/{key}/session/{id}`        — open (lazily) + render an offering session;
//! - `POST /offerings/{key}/session/{id}/act`    — advance ONE real turn on that offering + re-render;
//! - `GET  /offerings/{key}/session/{id}/verify` — re-verify that offering's committed chain.
//!
//! [`catalog_default_host`] registers three heterogeneous offerings — a dungeon (game), a council
//! (governance), a market (commerce). Because some sessions are `!Send`, the host runs on ONE owning
//! thread behind a `Send + Sync` [`HostThread`] handle (the discord-bot `Store` pattern generalised
//! to a whole registry) — the SAME host a Telegram / WeChat frontend adopts unchanged.
//!
//! ## Honest scope
//! This renders the affordance [`Surface`] as HTML **directly** (server-rendered forms). The
//! fuller path — `deos-js` + `deos-web-cells` (the live signal-bound web cell rendering, where
//! a `bind`/`gauge`/`tabs` node is a fine-grained reactive DOM binding) — is the follow-up, as
//! is a real deployment (a served bind address, a session store, `dregg-pay` credit debits on
//! the paid tier). What is proven here: a REAL `Frontend` over `dreggnet-offerings`, served via
//! axum, DRIVEN — affordances → HTML controls, a POST → an `Action` → one real turn, a session
//! playing through, executor-refereed, `verify` holding.

/// THE SPECTATOR / PROVENANCE surface for *The Descent* (the flagship's growth artifact): a
/// stranger opens a URL and INDEPENDENTLY re-verifies a run — a re-verified no-cheat leaderboard
/// (`GET /descent/leaderboard`) + a run-card that re-executes the recorded run to PASS/FAIL
/// (`GET /descent/run/{id}`). Additive; see [`descent::descent_router`].
pub mod descent;

pub use descent::{DescentState, descent_router, run_share_path};

use std::collections::HashMap;
use std::sync::mpsc::{SyncSender, sync_channel};
use std::sync::{Arc, Mutex};

use axum::{
    Router,
    extract::{Form, Path, Query, State},
    http::{HeaderMap, header},
    response::{Html, IntoResponse, Json},
    routing::{get, post},
};
use serde::Deserialize;

use deos_view::{MenuItem, SessionFormBackend, SurfaceBackend, ViewNode};
use dreggnet_council::{CandidateProposal, CouncilOffering};
use dreggnet_market::MarketOffering;
use dreggnet_offerings::dungeon::{DungeonOffering, DungeonSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, HostError, Offering, OfferingHost, OfferingInfo, Outcome,
    SessionConfig, SessionId, Surface, VerifyReport,
};

/// What the web frontend last presented for a session — the deos [`Surface`] and the cap-gated
/// [`Action`]s beside it (what it paints as HTML forms). Mirrors `mock::Presented`.
#[derive(Debug, Clone)]
pub struct Presented {
    /// The presented deos affordance surface (the view-tree the HTML renderer walks).
    pub surface: Surface,
    /// The affordances presented alongside it (each an HTML form/button).
    pub actions: Vec<Action>,
}

/// A web platform interaction — a POST of a presented affordance form. Stands in for the Discord
/// `ComponentInteraction` / Telegram `CallbackQuery`; carries the session it targets, the web
/// user (mapped to a [`DreggIdentity`] via [`WebFrontend::identity`]), and the `{turn, arg}`
/// pressed. Mirrors `mock::MockEvent` (the frontend-agnostic proof: the SAME round-trip).
#[derive(Debug, Clone)]
pub struct WebEvent {
    /// The session the POST targets.
    pub session: SessionId,
    /// The web user id (a `dregg_user` cookie / `?user=` param) → a derived [`DreggIdentity`].
    pub user: String,
    /// The submitted affordance's verb (the form's `turn` field — matches [`Action::turn`]).
    pub turn: String,
    /// The submitted affordance's argument (the form's `arg` field — matches [`Action::arg`]).
    pub arg: i64,
}

/// **The web [`Frontend`]** — a headless affordance-renderer that records what it was asked to
/// present per session and maps a web POST back into a typed offering [`Action`], PLUS the
/// web-specific [`render`](WebFrontend::render): the deos [`Surface`] → an HTML fragment.
///
/// Platform user = a `String` (the web session user); a platform event = a [`WebEvent`]. Identity
/// is derived deterministically (blake3 of the user id) so the SAME user → the SAME
/// [`DreggIdentity`] — mirroring the Discord `UserCipherclerk` derivation *shape* (the doc's
/// mandate: a derived cryptographic identity, not a nickname; the real web deployment would
/// derive a per-user Ed25519 key the same way the bot does).
#[derive(Debug, Default)]
pub struct WebFrontend {
    presented: HashMap<SessionId, Presented>,
}

impl WebFrontend {
    /// A fresh web frontend with no open sessions.
    pub fn new() -> Self {
        WebFrontend::default()
    }

    /// What was last presented for `session` (the surface + its actions), if any.
    pub fn presented(&self, session: &SessionId) -> Option<&Presented> {
        self.presented.get(session)
    }

    /// The affordances last presented for `session` (the forms a browser would show).
    pub fn presented_actions(&self, session: &SessionId) -> &[Action] {
        self.presented
            .get(session)
            .map(|p| p.actions.as_slice())
            .unwrap_or(&[])
    }

    /// Whether a surface slot is currently open for `session`.
    pub fn is_open(&self, session: &SessionId) -> bool {
        self.presented.contains_key(session)
    }

    /// **Render a deos [`Surface`] into an HTML fragment** — the web frontend's core job. Walks
    /// the [`ViewNode`] tree: prose → `<p>`, a [`Section`](ViewNode::Section) → a titled
    /// `<section>`, and a [`Menu`](ViewNode::Menu) of cap-gated affordances → one `<form
    /// method=post action="/session/{id}/act">` PER row, carrying the affordance's `{turn, arg}`
    /// as hidden inputs and a submit `<button>` (a `!enabled` row is rendered `disabled` +
    /// dimmed — the cap tooth SHOWN, not hidden; only a decoration, the executor still refuses a
    /// crafted POST of it). This is the HTML analogue of the native cockpit painting the SAME
    /// tree to gpui widgets / the Discord renderer painting it to an embed.
    pub fn render(&self, session: &SessionId, surface: &Surface) -> String {
        // Render through the deos-view server-form backend (the moved-in `view_html`): one POST
        // form per affordance, containers recursed so a nested affordance is never dropped. The
        // frontend no longer maintains its own subset walker.
        SessionFormBackend {
            session_id: session.0.clone(),
        }
        .render(surface.view(), &[])
    }
}

impl Frontend for WebFrontend {
    type PlatformUser = String;
    type PlatformEvent = WebEvent;

    /// Derive `user`'s [`DreggIdentity`] — blake3(user) hex. Deterministic: the SAME web user
    /// always maps to the SAME identity (mirroring the Discord `UserCipherclerk::derive(...)
    /// .public_key_hex()` derivation *shape*).
    fn identity(&self, user: String) -> DreggIdentity {
        web_identity(&user)
    }

    /// Open an (empty) surface slot for `session`.
    fn spin_session(&mut self, session: SessionId) {
        self.presented.entry(session).or_insert(Presented {
            surface: Surface(ViewNode::VStack(Vec::new())),
            actions: Vec::new(),
        });
    }

    /// Record the presented surface + actions (the HTML the next GET paints).
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]) {
        self.presented.insert(
            session.clone(),
            Presented {
                surface: surface.clone(),
                actions: actions.to_vec(),
            },
        );
    }

    /// Map a [`WebEvent`] POST back to the offering [`Action`] it names: find the presented
    /// affordance matching `(turn, arg)` and return it with the firing web user's derived
    /// identity. `None` if the session is unknown or the affordance was not presented (a POST for
    /// a control the surface did not offer — a frontend-level honest refusal, before the
    /// substrate).
    fn collect(&self, ev: WebEvent) -> Option<(SessionId, Action, DreggIdentity)> {
        let presented = self.presented.get(&ev.session)?;
        let action = presented
            .actions
            .iter()
            .find(|a| a.turn == ev.turn && a.arg == ev.arg)
            .cloned()?;
        Some((ev.session.clone(), action, self.identity(ev.user)))
    }

    /// Close `session`'s surface slot (archive on completion).
    fn teardown(&mut self, session: &SessionId) {
        self.presented.remove(session);
    }
}

/// **The axum web surface state** — the ONE [`DungeonOffering`] core, the live per-session
/// [`DungeonSession`]s (the real verifiable state chains), and the [`WebFrontend`] recording what
/// each session last presented. Shared behind an `Arc` as the axum handler `State`.
pub struct WebState {
    /// The offering core (offering #0). Stateless factory; each session is a real playthrough.
    offering: DungeonOffering,
    /// The live sessions — a real `DungeonSession` (WorldCell + playthrough) per session id.
    sessions: Mutex<HashMap<SessionId, DungeonSession>>,
    /// The web frontend recording each session's last-presented surface + actions.
    frontend: Mutex<WebFrontend>,
}

impl WebState {
    /// A fresh web surface over the free-tier dungeon offering.
    pub fn new() -> Self {
        WebState {
            offering: DungeonOffering::new(),
            sessions: Mutex::new(HashMap::new()),
            frontend: Mutex::new(WebFrontend::new()),
        }
    }

    /// A web surface over a caller-provided offering (e.g. [`DungeonOffering::paid`]).
    pub fn with_offering(offering: DungeonOffering) -> Self {
        WebState {
            offering,
            sessions: Mutex::new(HashMap::new()),
            frontend: Mutex::new(WebFrontend::new()),
        }
    }

    /// Whether a session is open.
    pub fn is_open(&self, id: &SessionId) -> bool {
        self.sessions.lock().unwrap().contains_key(id)
    }

    /// Ensure a session is open: on first touch, [`open`](Offering::open) a fresh
    /// [`DungeonSession`] (seeded deterministically from the session id, so a re-open of the same
    /// id is the SAME replay-verifiable world), spin its frontend slot, and present the initial
    /// surface (so a first POST can already `collect` the gatehall affordances).
    pub fn ensure_open(&self, id: &SessionId) {
        {
            let sessions = self.sessions.lock().unwrap();
            if sessions.contains_key(id) {
                return;
            }
        }
        let session = self
            .offering
            .open(SessionConfig::with_seed(seed_from_id(&id.0)))
            .expect("the Keep opens");
        let surface = self.offering.render(&session);
        let actions = self.offering.actions(&session);
        self.sessions.lock().unwrap().insert(id.clone(), session);
        let mut fe = self.frontend.lock().unwrap();
        fe.spin_session(id.clone());
        fe.present(id, &surface, &actions);
    }

    /// Re-verify a session's whole committed chain by replay (the offering's own proof).
    pub fn verify(&self, id: &SessionId) -> Option<VerifyReport> {
        let sessions = self.sessions.lock().unwrap();
        sessions.get(id).map(|s| self.offering.verify(s))
    }

    /// The number of real verified turns (genesis + committed steps) in a session.
    pub fn receipts_len(&self, id: &SessionId) -> Option<usize> {
        let sessions = self.sessions.lock().unwrap();
        sessions.get(id).map(|s| s.receipts_len())
    }

    /// The session's current room (passage) name, if still running.
    pub fn current_room(&self, id: &SessionId) -> Option<String> {
        let sessions = self.sessions.lock().unwrap();
        sessions.get(id).and_then(|s| s.current_passage_name())
    }

    /// Re-derive the current surface + actions from the live session, tell the frontend to
    /// present them (keeping the affordance surface current for the next `collect`), render the
    /// fragment, and wrap it in a full HTML page with `notice` and the live verify status.
    fn render_page(&self, id: &SessionId, notice: Option<&str>) -> String {
        let (surface, actions, verify) = {
            let sessions = self.sessions.lock().unwrap();
            let session = match sessions.get(id) {
                Some(s) => s,
                None => return page_missing(id),
            };
            (
                self.offering.render(session),
                self.offering.actions(session),
                self.offering.verify(session),
            )
        };
        let fragment = {
            let mut fe = self.frontend.lock().unwrap();
            fe.present(id, &surface, &actions);
            fe.render(id, &surface)
        };
        page(id, notice, &fragment, &verify)
    }
}

impl Default for WebState {
    fn default() -> Self {
        WebState::new()
    }
}

/// The `{turn, arg}` POST body of a `POST /session/{id}/act` — the submitted affordance form
/// (`<input name=turn>` / `<input name=arg>`). `arg` is parsed straight into the [`Action`]'s
/// `i64` (the deos `{turn, arg}` wire shape).
#[derive(Debug, Clone, Deserialize)]
pub struct ActForm {
    /// The affordance verb (the dungeon's `"choose"`).
    pub turn: String,
    /// The affordance argument (the scene choice index).
    pub arg: i64,
}

/// The `?user=` query params of a request (the web identity, alongside the `dregg_user` cookie).
#[derive(Debug, Clone, Default, Deserialize)]
pub struct WebQuery {
    /// The web user id — a deterministic input to identity derivation. Absent → the cookie, then
    /// `"anon"`.
    #[serde(default)]
    pub user: Option<String>,
}

/// **Build the axum router** over a shared [`WebState`]. The web session surface:
/// - `GET  /session/{id}`        — render the current [`Surface`] as an HTML page;
/// - `POST /session/{id}/act`    — collect the form, advance one real turn, re-render;
/// - `GET  /session/{id}/verify` — re-verify the committed chain by replay (JSON).
pub fn router(state: Arc<WebState>) -> Router {
    Router::new()
        .route("/session/{id}", get(get_session))
        .route("/session/{id}/act", post(post_act))
        .route("/session/{id}/verify", get(get_verify))
        .with_state(state)
}

/// `GET /session/{id}` — open the session (lazily) and render its current affordance surface as a
/// full HTML page (the room prose/state + a form/button per cap-gated affordance).
async fn get_session(State(state): State<Arc<WebState>>, Path(id): Path<String>) -> Html<String> {
    let id = SessionId::new(id);
    state.ensure_open(&id);
    Html(state.render_page(&id, None))
}

/// `POST /session/{id}/act` — the real-turn seam. Reads the web identity (a `dregg_user` cookie /
/// `?user=` param), [`collect`](Frontend::collect)s the `{turn, arg}` form back into the presented
/// [`Action`], and [`advance`](Offering::advance)s ONE real turn on the substrate. A legal move
/// lands a real receipt (the world moves); an illegal / crafted one is a real executor
/// [`Outcome::Refused`] surfaced as an honest banner — nothing commits (anti-ghost). Re-renders
/// the (possibly-advanced) committed state.
async fn post_act(
    State(state): State<Arc<WebState>>,
    Path(id): Path<String>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
    Form(form): Form<ActForm>,
) -> Html<String> {
    let id = SessionId::new(id);
    state.ensure_open(&id);

    let user = web_user(&headers, &query);
    let ev = WebEvent {
        session: id.clone(),
        user,
        turn: form.turn,
        arg: form.arg,
    };

    // Collect the POST back into the typed Action + the firing web user's derived identity.
    let collected = {
        let fe = state.frontend.lock().unwrap();
        fe.collect(ev)
    };

    let notice = match collected {
        None => {
            // A POST for a control the surface never offered — an honest frontend-level refusal,
            // before the substrate.
            "Refused: that affordance is not on the current surface.".to_string()
        }
        Some((_sid, action, actor)) => {
            // The CORE resolves the collected action on the substrate — ONE real turn.
            let outcome = {
                let mut sessions = state.sessions.lock().unwrap();
                let session = sessions
                    .get_mut(&id)
                    .expect("the session is open (ensure_open ran)");
                state.offering.advance(session, action, actor)
            };
            match outcome {
                Outcome::Landed { ended, .. } => {
                    if ended {
                        "The Keep is cleared — the objective is met, one real turn at a time."
                            .to_string()
                    } else {
                        "Turn committed — a real verified receipt landed.".to_string()
                    }
                }
                // The executor is the sole referee: a crafted POST of a dimmed / ineligible
                // affordance lands as a REAL refusal — nothing committed, the world unmoved.
                Outcome::Refused(why) => {
                    format!("Refused: {why} (nothing committed — anti-ghost).")
                }
            }
        }
    };

    Html(state.render_page(&id, Some(&notice)))
}

/// `GET /session/{id}/verify` — re-verify the whole committed chain by replay; the offering's own
/// proof, exposed over HTTP as JSON.
async fn get_verify(
    State(state): State<Arc<WebState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let id = SessionId::new(id);
    match state.verify(&id) {
        Some(report) => Json(serde_json::json!({
            "verified": report.verified,
            "turns": report.turns,
            "detail": report.detail,
        })),
        None => Json(serde_json::json!({
            "verified": false,
            "turns": 0,
            "detail": "no such session",
        })),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — the deos ViewNode → HTML walk, and the page chrome.
// ─────────────────────────────────────────────────────────────────────────────

/// Wrap an HTML fragment in a full document with the notice banner + the live verify line.
fn page(id: &SessionId, notice: Option<&str>, fragment: &str, verify: &VerifyReport) -> String {
    let notice_html = notice
        .map(|n| {
            let cls = if n.starts_with("Refused") {
                "notice refused"
            } else {
                "notice ok"
            };
            format!("<div class=\"{cls}\">{}</div>", esc(n))
        })
        .unwrap_or_default();
    let verify_cls = if verify.verified { "ok" } else { "refused" };
    let verify_html = format!(
        "<div class=\"verify {cls}\">chain re-verified by replay: <strong>{v}</strong> \
         ({turns} verified turns) — {detail}</div>",
        cls = verify_cls,
        v = if verify.verified { "yes" } else { "NO" },
        turns = verify.turns,
        detail = esc(&verify.detail),
    );
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — session {id}</title>{style}</head><body>\
         <main class=\"session\">{notice}{fragment}{verify}</main></body></html>",
        id = esc(&id.0),
        style = STYLE,
        notice = notice_html,
        fragment = fragment,
        verify = verify_html,
    )
}

/// The page shown for a `POST` / verify against a session id that is not open.
fn page_missing(id: &SessionId) -> String {
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <title>DreggNet Cloud — session {id}</title>{style}</head><body>\
         <main class=\"session\"><div class=\"notice refused\">No such session — \
         GET /session/{id} to open it.</div></main></body></html>",
        id = esc(&id.0),
        style = STYLE,
    )
}

/// The web identity for a request — the `?user=` param, else the `dregg_user` cookie, else
/// `"anon"`. Fed to [`WebFrontend::identity`] (a deterministic derivation → a stable
/// [`DreggIdentity`]).
fn web_user(headers: &HeaderMap, query: &WebQuery) -> String {
    if let Some(u) = query.user.as_ref() {
        if !u.is_empty() {
            return u.clone();
        }
    }
    if let Some(cookie) = headers.get(header::COOKIE).and_then(|v| v.to_str().ok()) {
        for part in cookie.split(';') {
            let part = part.trim();
            if let Some(v) = part.strip_prefix("dregg_user=") {
                if !v.is_empty() {
                    return v.to_string();
                }
            }
        }
    }
    "anon".to_string()
}

/// **Derive a web user's frontend-agnostic [`DreggIdentity`]** — `blake3(user)` hex. Deterministic
/// (the SAME user → the SAME identity), mirroring the Discord `UserCipherclerk::derive(...)
/// .public_key_hex()` derivation *shape*. Shared by [`WebFrontend::identity`] and the multi-offering
/// catalog's POST handler so both attribute a turn to the same identity — and so a council registers
/// its members from the SAME derivation (`blake3(user)` bytes as the member pubkey; see
/// [`catalog_default_host`]).
pub fn web_identity(user: &str) -> DreggIdentity {
    DreggIdentity(blake3::hash(user.as_bytes()).to_hex().to_string())
}

/// A deterministic session seed from a session id (so a re-open of the same id is the SAME
/// replay-verifiable world). blake3(id) → the low 8 bytes as a `u64`.
fn seed_from_id(id: &str) -> u64 {
    let h = blake3::hash(id.as_bytes());
    let b = h.as_bytes();
    u64::from_le_bytes(b[..8].try_into().unwrap())
}

/// Minimal HTML escaping for server-rendered text (no client JS; the same idiom the bot's admin
/// portal uses).
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// The page's inlined stylesheet (self-contained; no external assets).
const STYLE: &str = "<style>\
body{font-family:ui-sans-serif,system-ui,-apple-system,sans-serif;background:#0b1020;color:#cfe;margin:0;padding:2rem;line-height:1.5}\
.session{max-width:44rem;margin:0 auto}\
.deos-section{border:1px solid #244;border-radius:8px;padding:1rem 1.25rem;margin:1rem 0;background:#111a2e}\
.deos-section h2{margin:0 0 .5rem;font-size:1.05rem;color:#7fd}\
.tag-accent h2{color:#00b4d8}.tag-genuine h2{color:#5f8}.tag-muted h2{color:#89a;font-weight:500}\
.prose{margin:.35rem 0;color:#dfeaff}\
.affordances{display:flex;flex-direction:column;gap:.5rem}\
.affordance button{width:100%;text-align:left;padding:.6rem .9rem;border-radius:6px;border:1px solid #2a5;background:#123;color:#cfe;font-size:1rem;cursor:pointer}\
.affordance button:hover{background:#1a3a2a}\
.affordance.dimmed button{border-color:#433;color:#977;background:#1a1414;cursor:not-allowed;opacity:.6}\
.notice{padding:.6rem .9rem;border-radius:6px;margin-bottom:1rem;font-weight:600}\
.notice.ok{background:#0f2a1a;color:#7f8;border:1px solid #2a5}\
.notice.refused{background:#2a1414;color:#f99;border:1px solid #833}\
.verify{margin-top:1rem;font-size:.85rem;color:#89a}\
.verify.ok strong{color:#5f8}.verify.refused strong{color:#f77}\
.catalog{max-width:44rem;margin:0 auto}\
.catalog h1{font-size:1.4rem;color:#7fd}\
.offering-card{border:1px solid #244;border-radius:8px;padding:1rem 1.25rem;margin:1rem 0;background:#111a2e}\
.offering-card h2{margin:0 0 .35rem;font-size:1.1rem;color:#00b4d8}\
.offering-card a.play{display:inline-block;margin-top:.5rem;padding:.5rem .9rem;border-radius:6px;border:1px solid #2a5;background:#123;color:#cfe;text-decoration:none}\
.offering-card a.play:hover{background:#1a3a2a}\
.crumb{max-width:44rem;margin:0 auto 1rem;font-size:.85rem}\
.crumb a{color:#7fd}\
.affordance input.arg{width:100%;margin-bottom:.35rem;padding:.4rem .6rem;border-radius:6px;border:1px solid #2a5;background:#0d1526;color:#cfe;font-size:.95rem}\
table.board{width:100%;border-collapse:collapse;margin:1rem 0}\
table.board th,table.board td{text-align:left;padding:.5rem .6rem;border-bottom:1px solid #244}\
table.board th{color:#7fd;font-size:.85rem;text-transform:uppercase;letter-spacing:.04em}\
table.board td a{color:#5f8;text-decoration:none}table.board td a:hover{text-decoration:underline}\
</style>";

// ═════════════════════════════════════════════════════════════════════════════════════════
// THE MULTI-OFFERING WEB CATALOG — the generic offering router lifted to the core.
//
// The single-DungeonOffering surface above is offering #0 on the web. This section makes
// dreggnet-web a MULTI-OFFERING catalog over the frontend-agnostic `OfferingHost`: browse the
// registered offerings, then open + play ANY of them (a dungeon, a council, a market) in the
// browser — the SAME `open/advance/render/verify` verbs, one registry, the Session type erased.
//
// Routes (additive to `router` above; a separate `catalog_router`):
//   GET  /offerings                              — the catalog (a card + "play" link per offering)
//   GET  /offerings/{key}/session/{id}           — open (lazily) + render an offering session
//   POST /offerings/{key}/session/{id}/act       — advance ONE real turn + re-render
//   GET  /offerings/{key}/session/{id}/verify    — re-verify the committed chain (JSON)
// ═════════════════════════════════════════════════════════════════════════════════════════

/// A unit of work run ON the host's owning thread, against the live [`OfferingHost`].
type HostJob = Box<dyn FnOnce(&mut OfferingHost) + Send + 'static>;

/// **A thread-confined [`OfferingHost`] handle.** The host owns heterogeneous offering sessions,
/// some of which are `!Send` (a [`CouncilOffering`] session holds `Rc`-backed ballot caps — the
/// same reason the discord-bot's per-offering `Store` uses a dedicated thread). So the host cannot
/// be a `Mutex<OfferingHost>` in an axum `State` (that needs `Send`). Instead the host lives on ONE
/// owning thread and every access is a job shipped to it; only the job's plain-data result
/// (a [`Surface`], an [`Outcome`], a [`VerifyReport`], a `Vec<OfferingInfo>` — all `Send`) crosses
/// back. The handle itself is just a channel sender, so it is `Send + Sync` and drops straight into
/// an axum `State`. This is the discord-bot `Store` generalised to a whole registry — the pattern a
/// Telegram / WeChat frontend reuses unchanged.
pub struct HostThread {
    jobs: SyncSender<HostJob>,
}

impl HostThread {
    /// Spawn the owning thread and BUILD the host on it (`build` runs on the thread, so the
    /// registered offerings + their sessions are born there and never cross a thread boundary).
    pub fn spawn(build: impl FnOnce() -> OfferingHost + Send + 'static) -> HostThread {
        let (jobs, rx) = sync_channel::<HostJob>(64);
        std::thread::Builder::new()
            .name("offering-host".to_string())
            .spawn(move || {
                let mut host = build();
                while let Ok(job) = rx.recv() {
                    job(&mut host);
                }
            })
            .expect("spawn the offering host thread");
        HostThread { jobs }
    }

    /// Run `f` against the host on the owning thread and hand back its (`Send`) result. Blocks the
    /// caller until the job returns — one short, CPU-bound offering turn, same cost profile as the
    /// single-offering surface's `Mutex` critical section.
    pub fn run<R: Send + 'static>(
        &self,
        f: impl FnOnce(&mut OfferingHost) -> R + Send + 'static,
    ) -> R {
        let (tx, rx) = sync_channel::<R>(1);
        self.jobs
            .send(Box::new(move |host| {
                let _ = tx.send(f(host));
            }))
            .expect("the offering host thread is alive");
        rx.recv().expect("the offering host thread answered")
    }
}

/// **The axum state for the multi-offering catalog** — a thread-confined [`OfferingHost`] behind a
/// `Send + Sync` handle. Shared behind an `Arc` as the handler `State`.
pub struct CatalogState {
    /// The host handle (the registry of offerings + their live sessions, on its owning thread).
    host: HostThread,
}

impl CatalogState {
    /// A fresh catalog over the DEFAULT offerings (dungeon + council + market) — see
    /// [`catalog_default_host`].
    pub fn new() -> Self {
        CatalogState {
            host: HostThread::spawn(catalog_default_host),
        }
    }

    /// A catalog over a caller-built host (the offerings are registered inside `build`, which runs
    /// on the owning thread). Lets a deployment register its own offering set.
    pub fn with_host(build: impl FnOnce() -> OfferingHost + Send + 'static) -> Self {
        CatalogState {
            host: HostThread::spawn(build),
        }
    }

    /// The registered offerings (the catalog listing).
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.host.run(|h| h.list_offerings())
    }

    /// Re-verify session `(key, id)`'s committed chain (`None` if absent) — the offering's own proof.
    pub fn verify(&self, key: &str, id: &SessionId) -> Option<VerifyReport> {
        let key = key.to_string();
        let id = id.clone();
        self.host.run(move |h| h.verify(&key, &id))
    }

    /// Whether session `(key, id)` is live.
    pub fn is_open(&self, key: &str, id: &SessionId) -> bool {
        let key = key.to_string();
        let id = id.clone();
        self.host.run(move |h| h.is_open(&key, &id))
    }
}

impl Default for CatalogState {
    fn default() -> Self {
        CatalogState::new()
    }
}

/// **The default catalog host** — registers the three heterogeneous offerings the web catalog
/// plays: the dungeon (a game), the council (governance), and the market (commerce). Built on the
/// host's owning thread ([`HostThread::spawn`]), so each offering's `!Send` internals stay confined.
///
/// The council's electorate is derived from web usernames so a browser user can really vote: a web
/// user's [`DreggIdentity`] is `blake3(user)` hex, and a council member's identity is the hex of its
/// pubkey — so setting a member's pubkey to `blake3(user)`'s bytes makes that web user a council
/// member (`alice` and `bob` here). Quorum is 2, so a proposal enacts only once BOTH approve — a
/// real vote, drivable through the browser.
pub fn catalog_default_host() -> OfferingHost {
    let mut host = OfferingHost::new();
    host.register(
        "dungeon",
        "The Warden's Keep — a verifiable dungeon (offering #0)",
        DungeonOffering::new(),
    );

    // The council electorate: the web users who can vote (member pubkey = blake3(user) bytes).
    let members: Vec<[u8; 32]> = ["alice", "bob"]
        .iter()
        .map(|u| *blake3::hash(u.as_bytes()).as_bytes())
        .collect();
    host.register(
        "council",
        "DreggNet Council — propose · vote · enact",
        CouncilOffering::new(
            members,
            vec![
                CandidateProposal::new("Fund the archive", 42),
                CandidateProposal::new("Ratify the charter", 7),
            ],
            2, // quorum M = 2 (both members must approve)
        ),
    );

    host.register(
        "market",
        "DreggNet Market — a sealed-bid auction (list · bid · settle)",
        MarketOffering::new(),
    );
    host
}

/// **Build the multi-offering catalog router** over a shared [`CatalogState`]. Additive to
/// [`router`] — mount both on one axum app (or serve the catalog alone).
pub fn catalog_router(state: Arc<CatalogState>) -> Router {
    Router::new()
        .route("/offerings", get(get_catalog))
        .route("/offerings/{key}/session/{id}", get(get_offering_session))
        .route("/offerings/{key}/session/{id}/act", post(post_offering_act))
        .route(
            "/offerings/{key}/session/{id}/verify",
            get(get_offering_verify),
        )
        .with_state(state)
}

/// `GET /offerings` — the catalog page: a card per registered offering (title + live-session count)
/// with a "play" link opening a browser session of it.
async fn get_catalog(State(state): State<Arc<CatalogState>>) -> Html<String> {
    let offerings = state.list_offerings();
    Html(catalog_page(&offerings))
}

/// `GET /offerings/{key}/session/{id}` — open the offering session (lazily, seeded from the id) and
/// render its current [`Surface`] as an HTML page (prose/state + a POST form per cap-gated affordance).
async fn get_offering_session(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
) -> Html<String> {
    let sid = SessionId::new(id);
    // Ensure the session is open (deploy on first touch), then render.
    let opened = {
        let key = key.clone();
        let sid = sid.clone();
        state.host.run(move |h| h.ensure_open(&key, &sid))
    };
    if let Err(HostError::UnknownOffering(_)) = opened {
        return Html(catalog_missing_offering(&key));
    }
    Html(render_offering_page(&state, &key, &sid, None))
}

/// The `{turn, arg}` POST body of `POST /offerings/{key}/session/{id}/act`.
#[derive(Debug, Clone, Deserialize)]
pub struct OfferingActForm {
    /// The affordance verb (the offering's turn — `"choose"`, `"propose"`, `"approve"`, `"bid"`, …).
    pub turn: String,
    /// The affordance argument (a choice/proposal index, or a value-taking turn's value).
    #[serde(default)]
    pub arg: i64,
}

/// The result of collecting + resolving a catalog POST.
enum CatalogAct {
    /// The affordance was offered and resolved on the substrate (a real landed receipt / refusal).
    Advanced(Outcome),
    /// The turn is not on the current surface — an honest frontend-level refusal, before the substrate.
    NotOffered,
    /// The offering or session is absent (a routing miss).
    Missing,
}

/// `POST /offerings/{key}/session/{id}/act` — the real-turn seam for ANY offering. Reads the web
/// identity, PRESENTS the current surface (the offering's live [`Offering::actions`]), COLLECTS the
/// posted `{turn, arg}` against it (a turn the surface does not offer is refused before the
/// substrate), and [`OfferingHost::advance`]s ONE real turn. A legal move lands a real receipt; an
/// illegal / crafted one is a real executor [`Outcome::Refused`] (anti-ghost). Re-renders.
async fn post_offering_act(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    Query(query): Query<WebQuery>,
    Form(form): Form<OfferingActForm>,
) -> Html<String> {
    let sid = SessionId::new(id);
    // Ensure open first (so a POST to a fresh session still resolves against a live offering).
    let opened = {
        let key = key.clone();
        let sid = sid.clone();
        state.host.run(move |h| h.ensure_open(&key, &sid))
    };
    if let Err(HostError::UnknownOffering(_)) = opened {
        return Html(catalog_missing_offering(&key));
    }

    let actor = web_identity(&web_user(&headers, &query));

    // PRESENT the current surface + COLLECT the posted affordance + ADVANCE, atomically on the
    // host thread: the turn must be among the offering's current affordances (offered), then the
    // executor is the sole referee of the {turn, arg} on the substrate.
    let acted = {
        let key = key.clone();
        let sid = sid.clone();
        let turn = form.turn.clone();
        let arg = form.arg;
        state.host.run(move |h| {
            let Some(actions) = h.actions(&key, &sid) else {
                return CatalogAct::Missing;
            };
            if !actions.iter().any(|a| a.turn == turn) {
                return CatalogAct::NotOffered;
            }
            // The label + enabled are decoration; the executor resolves the TYPED (turn, arg).
            let action = Action::new(turn.clone(), turn, arg, true);
            match h.advance(&key, &sid, action, actor) {
                Some(o) => CatalogAct::Advanced(o),
                None => CatalogAct::Missing,
            }
        })
    };

    let notice = match acted {
        CatalogAct::Advanced(Outcome::Landed { ended, .. }) => {
            if ended {
                "Turn committed — the session reached its objective, one real turn at a time."
                    .to_string()
            } else {
                "Turn committed — a real verified receipt landed.".to_string()
            }
        }
        CatalogAct::Advanced(Outcome::Refused(why)) => {
            format!("Refused: {why} (nothing committed — anti-ghost).")
        }
        CatalogAct::NotOffered => {
            "Refused: that affordance is not on the current surface.".to_string()
        }
        CatalogAct::Missing => "Refused: no such offering session.".to_string(),
    };

    Html(render_offering_page(&state, &key, &sid, Some(&notice)))
}

/// `GET /offerings/{key}/session/{id}/verify` — re-verify the committed chain by the offering's own
/// proof, exposed over HTTP as JSON.
async fn get_offering_verify(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
) -> impl IntoResponse {
    let sid = SessionId::new(id);
    match state.verify(&key, &sid) {
        Some(report) => Json(serde_json::json!({
            "verified": report.verified,
            "turns": report.turns,
            "detail": report.detail,
        })),
        None => Json(serde_json::json!({
            "verified": false,
            "turns": 0,
            "detail": "no such offering session",
        })),
    }
}

/// Render an offering session as a full HTML page: its [`Surface`] as POST forms + the live verify
/// line + an optional notice banner. Fetches the surface + verify report from the host thread.
fn render_offering_page(
    state: &CatalogState,
    key: &str,
    id: &SessionId,
    notice: Option<&str>,
) -> String {
    let rendered = {
        let key = key.to_string();
        let id = id.clone();
        state
            .host
            .run(move |h| h.render(&key, &id).zip(h.verify(&key, &id)))
    };
    let Some((surface, verify)) = rendered else {
        return page_missing(id);
    };
    let title = state
        .host
        .run({
            let key = key.to_string();
            move |h| h.title(&key).map(|t| t.to_string())
        })
        .unwrap_or_else(|| key.to_string());
    let fragment = render_catalog_forms(surface.view(), key, &id.0);
    offering_page(&title, id, notice, &fragment, &verify)
}

/// **Render an offering's [`ViewNode`] surface into POST-form controls** — the multi-offering
/// analogue of deos-view's `render_session_forms`, but each affordance POSTs to
/// `/offerings/{key}/session/{id}/act` (carrying the offering key + session in the route). Prose →
/// `<p>`, a [`Section`](ViewNode::Section) → a titled `<section>`, a [`Menu`](ViewNode::Menu) row /
/// a [`Button`](ViewNode::Button) → one POST form; containers recurse. A `!enabled` affordance is
/// rendered `disabled` + dimmed (the cap tooth SHOWN, not hidden — a decoration; the executor still
/// refuses a crafted POST of it). A value-taking turn's `arg` is an editable number input (so a
/// market bid's value can be typed); a fixed-choice affordance defaults it to the presented arg.
fn render_catalog_forms(node: &ViewNode, key: &str, id: &str) -> String {
    let mut out = String::new();
    catalog_node(node, key, id, &mut out);
    out
}

fn catalog_node(node: &ViewNode, key: &str, id: &str, out: &mut String) {
    match node {
        ViewNode::Text(t) => {
            if !t.trim().is_empty() {
                out.push_str("<p class=\"prose\">");
                out.push_str(&esc(t));
                out.push_str("</p>");
            }
        }
        ViewNode::Section {
            title,
            tag,
            children,
        } => {
            out.push_str(&format!(
                "<section class=\"deos-section tag-{}\"><h2>{}</h2>",
                esc(tag),
                esc(title)
            ));
            for c in children {
                catalog_node(c, key, id, out);
            }
            out.push_str("</section>");
        }
        ViewNode::Menu { items } => {
            out.push_str("<div class=\"affordances\">");
            for it in items {
                out.push_str(&catalog_form(key, id, it));
            }
            out.push_str("</div>");
        }
        ViewNode::Button { label, turn, arg } => {
            let it = MenuItem {
                label: label.clone(),
                turn: turn.clone(),
                arg: *arg,
                enabled: true,
            };
            out.push_str(&catalog_form(key, id, &it));
        }
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            for c in cs {
                catalog_node(c, key, id, out);
            }
        }
        ViewNode::Grid { children, .. } => {
            for c in children {
                catalog_node(c, key, id, out);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                catalog_node(p, key, id, out);
            }
        }
        ViewNode::Host { view: Some(v), .. } => catalog_node(v, key, id, out),
        ViewNode::Adept(inner) => catalog_node(inner, key, id, out),
        ViewNode::Divider => out.push_str("<hr>"),
        _ => {}
    }
}

/// One affordance POST-form control for the catalog: `<form method=post
/// action="/offerings/{key}/session/{id}/act">` carrying the affordance's `{turn, arg}` — `turn` as
/// a hidden input, `arg` as an EDITABLE number input defaulting to the presented value (so a
/// value-taking turn, a market bid, takes a typed value while a fixed-choice affordance just
/// submits its default). A `!enabled` row is dimmed + `disabled` (a decoration; the executor is the
/// referee).
fn catalog_form(key: &str, id: &str, it: &MenuItem) -> String {
    let (disabled, cls) = if it.enabled {
        ("", "affordance")
    } else {
        (" disabled", "affordance dimmed")
    };
    format!(
        "<form class=\"{cls}\" method=\"post\" action=\"/offerings/{key}/session/{id}/act\">\
         <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
         <input class=\"arg\" type=\"number\" name=\"arg\" value=\"{arg}\">\
         <button type=\"submit\"{disabled}>{label}</button></form>",
        cls = cls,
        key = esc(key),
        id = esc(id),
        turn = esc(&it.turn),
        arg = it.arg,
        disabled = disabled,
        label = esc(&it.label),
    )
}

/// The `GET /offerings` catalog page — a card + "play" link per registered offering.
fn catalog_page(offerings: &[OfferingInfo]) -> String {
    let mut cards = String::new();
    for o in offerings {
        cards.push_str(&format!(
            "<div class=\"offering-card\"><h2>{title}</h2>\
             <p class=\"prose\">key <code>{key}</code> · {n} open session(s)</p>\
             <a class=\"play\" href=\"/offerings/{key}/session/{key}-web\">▶ Play {key}</a></div>",
            title = esc(&o.title),
            key = esc(&o.key),
            n = o.open_sessions,
        ));
    }
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — offerings</title>{style}</head><body>\
         <main class=\"catalog\"><h1>DreggNet Cloud — all offerings, any surface</h1>\
         <p class=\"prose\">Every offering is a confined, verifiable, per-session thing on the real \
         dregg substrate. Pick one to play it in the browser — each move is a real executor turn.</p>\
         {cards}</main></body></html>",
        style = STYLE,
        cards = cards,
    )
}

/// Wrap an offering session's fragment in a full HTML page (breadcrumb + notice + verify line).
fn offering_page(
    title: &str,
    id: &SessionId,
    notice: Option<&str>,
    fragment: &str,
    verify: &VerifyReport,
) -> String {
    let notice_html = notice
        .map(|n| {
            let cls = if n.starts_with("Refused") {
                "notice refused"
            } else {
                "notice ok"
            };
            format!("<div class=\"{cls}\">{}</div>", esc(n))
        })
        .unwrap_or_default();
    let verify_cls = if verify.verified { "ok" } else { "refused" };
    let verify_html = format!(
        "<div class=\"verify {cls}\">chain re-verified: <strong>{v}</strong> \
         ({turns} verified turns) — {detail}</div>",
        cls = verify_cls,
        v = if verify.verified { "yes" } else { "NO" },
        turns = verify.turns,
        detail = esc(&verify.detail),
    );
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet Cloud — {title}</title>{style}</head><body>\
         <div class=\"crumb\"><a href=\"/offerings\">← all offerings</a> · \
         <strong>{title}</strong> · session {id}</div>\
         <main class=\"session\">{notice}{fragment}{verify}</main></body></html>",
        title = esc(title),
        id = esc(&id.0),
        style = STYLE,
        notice = notice_html,
        fragment = fragment,
        verify = verify_html,
    )
}

/// The page shown for a `GET`/`POST` against an unregistered offering key.
fn catalog_missing_offering(key: &str) -> String {
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <title>DreggNet Cloud — unknown offering</title>{style}</head><body>\
         <main class=\"session\"><div class=\"notice refused\">No offering registered under \
         <code>{key}</code>. <a href=\"/offerings\">Browse the catalog.</a></div></main></body></html>",
        key = esc(key),
        style = STYLE,
    )
}
