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
//! ## Honest scope
//! This renders the affordance [`Surface`] as HTML **directly** (server-rendered forms). The
//! fuller path — `deos-js` + `deos-web-cells` (the live signal-bound web cell rendering, where
//! a `bind`/`gauge`/`tabs` node is a fine-grained reactive DOM binding) — is the follow-up, as
//! is a real deployment (a served bind address, a session store, `dregg-pay` credit debits on
//! the paid tier). What is proven here: a REAL `Frontend` over `dreggnet-offerings`, served via
//! axum, DRIVEN — affordances → HTML controls, a POST → an `Action` → one real turn, a session
//! playing through, executor-refereed, `verify` holding.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use axum::{
    Router,
    extract::{Form, Path, Query, State},
    http::{HeaderMap, header},
    response::{Html, IntoResponse, Json},
    routing::{get, post},
};
use serde::Deserialize;

use deos_view::ViewNode;
use dreggnet_offerings::dungeon::{DungeonOffering, DungeonSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, Offering, Outcome, SessionConfig, SessionId, Surface,
    VerifyReport,
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
        let mut out = String::new();
        view_html(surface.view(), session, &mut out);
        out
    }
}

impl Frontend for WebFrontend {
    type PlatformUser = String;
    type PlatformEvent = WebEvent;

    /// Derive `user`'s [`DreggIdentity`] — blake3(user) hex. Deterministic: the SAME web user
    /// always maps to the SAME identity (mirroring the Discord `UserCipherclerk::derive(...)
    /// .public_key_hex()` derivation *shape*).
    fn identity(&self, user: String) -> DreggIdentity {
        DreggIdentity(blake3::hash(user.as_bytes()).to_hex().to_string())
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

/// Walk a deos [`ViewNode`] into HTML, appending to `out`. Handles the shapes an offering's
/// surface produces (prose, sections, the affordance menu) and recurses generic containers; a
/// [`Menu`](ViewNode::Menu) row becomes a real POST form (the affordance control).
fn view_html(node: &ViewNode, sid: &SessionId, out: &mut String) {
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
                view_html(c, sid, out);
            }
            out.push_str("</section>");
        }
        ViewNode::Menu { items } => {
            out.push_str("<div class=\"affordances\">");
            for it in items {
                let (disabled, cls) = if it.enabled {
                    ("", "affordance")
                } else {
                    (" disabled", "affordance dimmed")
                };
                // One <form> per affordance — a real POST of its {turn, arg} to the act route.
                out.push_str(&format!(
                    "<form class=\"{cls}\" method=\"post\" action=\"/session/{sid}/act\">\
                     <input type=\"hidden\" name=\"turn\" value=\"{turn}\">\
                     <input type=\"hidden\" name=\"arg\" value=\"{arg}\">\
                     <button type=\"submit\"{disabled}>{label}</button>\
                     </form>",
                    cls = cls,
                    sid = esc(&sid.0),
                    turn = esc(&it.turn),
                    arg = it.arg,
                    disabled = disabled,
                    label = esc(&it.label),
                ));
            }
            out.push_str("</div>");
        }
        // Generic containers: recurse children in order.
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            for c in cs {
                view_html(c, sid, out);
            }
        }
        ViewNode::Grid { children, .. } => {
            for c in children {
                view_html(c, sid, out);
            }
        }
        ViewNode::Divider => out.push_str("<hr>"),
        // Any richer node an offering does not (yet) emit on this surface: the deos-js/web-cells
        // path renders these live (bind/gauge/tabs/…). Skipped by this direct HTML renderer.
        _ => {}
    }
}

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
</style>";
