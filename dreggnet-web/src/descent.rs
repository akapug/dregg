//! # `descent` — THE SPECTATOR / PROVENANCE surface for *The Descent*.
//!
//! The flagship's **growth artifact** (docs/GAME-STRATEGY.md Phase 3.2 — "the shareable verified
//! run"): a stranger opens a URL and *independently verifies* someone's run of the daily descent.
//! Not "trust me, I did this" — the page **re-executes the recorded run** server-side, on render,
//! against a fresh identically-seeded world, and shows the verdict. The unfair growth mechanic is a
//! proof, not a claim: a forged run shows **FAIL**, not a fake pass.
//!
//! Two server-rendered surfaces, additive to the [`catalog_router`](crate::catalog_router):
//! - `GET /descent/leaderboard[?day={key}]` — the day's **no-cheat leaderboard**: the ranked runs
//!   that provably reached the hoard, each row **re-verified on render** ([`verify_completion`], the
//!   same no-cheat verifier [`ugc_dregg::Registry::reverify_entry`]/`submit` run) against the day's
//!   published [`Universe`]. A forged / incomplete / lost run **does not appear** — it is excluded by
//!   re-verification, not by trusting a stored flag.
//! - `GET /descent/run/{id}` — a **run-card**: the run's summary (day / seed, character level+class,
//!   depth reached, alive/dead, the outcome) plus an **INDEPENDENT VERIFICATION panel** that replays
//!   the recorded receipt chain ([`spween_dregg::verify`] — chain-linkage + re-execution against a
//!   fresh, identically-seeded world) and shows **PASS/FAIL**. An honest run (won *or* lost) PASSES;
//!   a tampered run FAILS. The `id` is the **shareable link shape** the bot's result embed points at
//!   (see [`run_share_path`]).
//!
//! ## What is real vs. named
//! REAL here: the **server-side independent re-verification** — every leaderboard row and every
//! run-card is re-executed from the recorded moves on render (no trusted "verified" bit is stored;
//! [`Run`] is a plain, *untrusted* record, exactly as a persistence layer would hand one back). The
//! no-cheat property is [`ugc_dregg`]'s verbatim ([`verify_completion`]); the run-card replay is
//! [`spween_dregg`]'s audited re-verifier. NAMED, not built here: a live bind address / deployment;
//! *client-side* verification or a downloadable proof (this serves server-rendered HTML — the
//! stranger re-verifies by trusting THIS server, or by re-running the open-source verifier on the
//! recorded playthrough themselves); the `deos-js` live cell render. The bot links to a run by
//! putting [`run_share_path`] in its result embed.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};

use axum::{
    Router,
    extract::{Path, Query, State},
    response::Html,
    routing::get,
};
use serde::Deserialize;

use dreggnet_offerings::daily_descent::{DAILY_DEPLOY_SEED, DailyDescent, HOARD_GOLD, daily_scene};
use procgen_dregg::CommittedSeed;
use spween_dregg::{
    PASSAGE_ENDED, PASSAGE_SLOT, Playthrough, Scene, WorldCell, compile_scene, parse, verify,
};
use ugc_dregg::{Completion, Universe, verify_completion};

use crate::{STYLE, esc};

/// The author label the day's world is published under (a stable content-address input; the daily
/// world is anonymous-authored on the no-cheat board).
const DAY_AUTHOR: &str = "the-descent";

// ═══════════════════════════════════════════════════════════════════════════════
// The recorded, re-verifiable material.
// ═══════════════════════════════════════════════════════════════════════════════

/// A **published day** — the beacon-seeded daily world, its parsed scene + var→slot map (for
/// reading committed vars off a verified state), and its content-addressed [`Universe`] (what the
/// no-cheat board re-verifies against). Everyone who derives the day's seed derives the byte-identical
/// world, so this is reproducible provenance, not a private fixture.
struct Day {
    /// The day's key (e.g. a date / beacon-round tag). `?day=` selects it; the default is "today".
    key: String,
    /// The committed seed the day's world was drawn from (short-hex shown for provenance).
    seed: CommittedSeed,
    /// The day's world spec (title / warden HP / depth).
    day: DailyDescent,
    /// The parsed scene — re-deployed fresh for every run-card replay (never mutated).
    scene: Scene,
    /// The published, content-addressed universe (the no-cheat re-verification target).
    universe: Universe,
    /// var→slot map, to read `depth`/`gold`/`downed` off a (verified) committed state vector.
    var_slots: BTreeMap<String, usize>,
    /// The run ids recorded for this day (candidates for the board — each re-verified on render).
    run_ids: Vec<String>,
}

/// A **recorded run** — an UNTRUSTED record (a player name + the recorded [`Playthrough`] + display
/// metadata). Nothing here is believed: the leaderboard re-verifies it with [`verify_completion`]
/// and the run-card replays it with [`spween_dregg::verify`], on render, every time.
struct Run {
    /// The shareable run id (the `/descent/run/{id}` path segment).
    id: String,
    /// The day this run belongs to.
    day_key: String,
    /// The player label (display).
    player: String,
    /// The player's persistent character level at record time (profile metadata — NOT part of the
    /// run's independent re-verification, which covers the run's moves + committed outcome).
    level: u64,
    /// The player's chosen class id at record time (profile metadata; `0` = unset).
    class: u64,
    /// The recorded receipt chain — the un-retconnable material the surface re-executes.
    play: Playthrough,
}

/// **The spectator/provenance state** — published days + recorded (untrusted) runs, behind one
/// `Mutex`. Shared as an axum `State<Arc<DescentState>>`. All the material is plain `Send + Sync`
/// data (a scene / universe / playthrough), so — unlike the `!Send` council sessions behind the
/// catalog's [`HostThread`](crate::HostThread) — it lives directly in the `Arc`.
pub struct DescentState {
    inner: Mutex<Inner>,
}

#[derive(Default)]
struct Inner {
    days: HashMap<String, Day>,
    runs: HashMap<String, Run>,
    /// The day `GET /descent/leaderboard` shows when no `?day=` is given (the first opened day).
    today: Option<String>,
}

impl DescentState {
    /// A fresh surface with no days or runs.
    pub fn new() -> Self {
        DescentState {
            inner: Mutex::new(Inner::default()),
        }
    }

    /// **Open (publish) a day's world** under `key`, drawn from `seed` — derive the byte-identical
    /// daily world everyone else derives, parse + compile its scene, and publish its content-addressed
    /// [`Universe`] (the no-cheat re-verification target). The first day opened becomes the default
    /// "today". Idempotent per key.
    pub fn open_day(&self, key: &str, seed: CommittedSeed) {
        let day = daily_scene(&seed);
        let scene = parse(&day.source, "daily-descent.scene").expect("the day's scene parses");
        let var_slots = compile_scene(&scene)
            .map(|c| c.var_slots)
            .unwrap_or_default();
        let universe = day
            .universe(DAY_AUTHOR)
            .expect("the day's world publishes as a universe");
        let mut inner = self.inner.lock().unwrap();
        inner.days.insert(
            key.to_string(),
            Day {
                key: key.to_string(),
                seed,
                day,
                scene,
                universe,
                var_slots,
                run_ids: Vec::new(),
            },
        );
        if inner.today.is_none() {
            inner.today = Some(key.to_string());
        }
    }

    /// Set which opened day `GET /descent/leaderboard` shows by default.
    pub fn set_today(&self, key: &str) {
        self.inner.lock().unwrap().today = Some(key.to_string());
    }

    /// **Ingest a recorded run** for a day — store the (untrusted) playthrough + display metadata
    /// under the shareable `run_id`. No verification happens here: the surface re-verifies on every
    /// render. Returns `false` if the day is not open. `run_id` is what [`run_share_path`] links to.
    pub fn ingest_run(
        &self,
        day_key: &str,
        run_id: &str,
        player: &str,
        level: u64,
        class: u64,
        play: Playthrough,
    ) -> bool {
        let mut inner = self.inner.lock().unwrap();
        if !inner.days.contains_key(day_key) {
            return false;
        }
        inner.runs.insert(
            run_id.to_string(),
            Run {
                id: run_id.to_string(),
                day_key: day_key.to_string(),
                player: player.to_string(),
                level,
                class,
                play,
            },
        );
        if let Some(day) = inner.days.get_mut(day_key) {
            if !day.run_ids.iter().any(|r| r == run_id) {
                day.run_ids.push(run_id.to_string());
            }
        }
        true
    }
}

impl Default for DescentState {
    fn default() -> Self {
        DescentState::new()
    }
}

/// **The shareable link shape** for a run — the path the bot's result embed points a stranger at
/// (`https://<host>/descent/run/{run_id}`). Opening it re-verifies the run and shows the proof.
pub fn run_share_path(run_id: &str) -> String {
    format!("/descent/run/{run_id}")
}

// ═══════════════════════════════════════════════════════════════════════════════
// Router + handlers.
// ═══════════════════════════════════════════════════════════════════════════════

/// **Build the spectator/provenance router** over a shared [`DescentState`]. Additive — mount it on
/// the same axum app as [`router`](crate::router) / [`catalog_router`](crate::catalog_router).
///
/// - `GET /descent/leaderboard[?day={key}]` — the day's re-verified no-cheat board;
/// - `GET /descent/run/{id}` — a run-card with the independent-verification panel.
pub fn descent_router(state: Arc<DescentState>) -> Router {
    Router::new()
        .route("/descent/leaderboard", get(get_leaderboard))
        .route("/descent/run/{id}", get(get_run_card))
        .with_state(state)
}

/// The `?day=` selector for the leaderboard (absent → the default "today").
#[derive(Debug, Clone, Default, Deserialize)]
pub struct DayQuery {
    /// The day key to show; absent → the state's designated "today".
    #[serde(default)]
    pub day: Option<String>,
}

/// `GET /descent/leaderboard[?day={key}]` — render the day's no-cheat leaderboard. Every candidate
/// run is **re-verified on render** ([`verify_completion`] against the day's published universe): a
/// run that provably reached the hoard is ranked (by verified turns-to-win); a forged / incomplete /
/// lost run is **excluded** (it never trusted a stored flag).
async fn get_leaderboard(
    State(state): State<Arc<DescentState>>,
    Query(q): Query<DayQuery>,
) -> Html<String> {
    let inner = state.inner.lock().unwrap();
    let key = q.day.clone().or_else(|| inner.today.clone());
    let Some(key) = key else {
        return Html(leaderboard_missing(None));
    };
    let Some(day) = inner.days.get(&key) else {
        return Html(leaderboard_missing(Some(&key)));
    };

    // Re-verify EVERY candidate on render. Only a provable win ranks; anything else is excluded.
    let mut rows: Vec<Row> = Vec::new();
    for rid in &day.run_ids {
        let Some(run) = inner.runs.get(rid) else {
            continue;
        };
        let completion = Completion {
            universe: day.universe.id(),
            player: run.player.clone(),
            play: run.play.clone(),
            claimed_turns: run.play.steps.len(),
        };
        // THE NO-CHEAT TOOTH, on render: re-execute against a fresh identically-seeded world +
        // require the win + bind the claimed result. A forged / lost / incomplete run errs → skipped.
        if let Ok(turns) = verify_completion(&day.universe, &completion) {
            let depth = final_var(day, &run.play, "depth");
            rows.push(Row {
                run_id: rid.clone(),
                player: run.player.clone(),
                turns,
                depth,
            });
        }
    }
    // Rank by verified turns-to-win (lower first); stable for ties.
    rows.sort_by(|a, b| a.turns.cmp(&b.turns).then_with(|| a.player.cmp(&b.player)));

    Html(leaderboard_page(day, &rows))
}

/// `GET /descent/run/{id}` — render a run-card: the run's summary + the independent-verification
/// panel. The panel **replays the recorded receipt chain** ([`spween_dregg::verify`]) against a fresh,
/// identically-seeded world — an honest run (won or lost) PASSES; a tampered run FAILS. The committed
/// outcome (depth / hoard / defeat) is read off the verified final state (trusted only on PASS).
async fn get_run_card(
    State(state): State<Arc<DescentState>>,
    Path(id): Path<String>,
) -> Html<String> {
    let inner = state.inner.lock().unwrap();
    let Some(run) = inner.runs.get(&id) else {
        return Html(run_missing(&id));
    };
    let Some(day) = inner.days.get(&run.day_key) else {
        return Html(run_missing(&id));
    };

    // INDEPENDENT RE-VERIFICATION: deploy a fresh, identically-seeded world and re-execute the
    // recorded moves (chain-linkage + replay). Not a trusted flag — a real re-run, here, now.
    let verified = match WorldCell::deploy(&day.scene, DAILY_DEPLOY_SEED) {
        Ok(fresh) => verify(fresh, &day.scene, &run.play).is_ok(),
        Err(_) => false,
    };

    // The committed outcome, read off the (verified) final recorded state.
    let last_state = run.play.steps.last().map(|s| s.state.as_slice());
    let ended = last_state
        .and_then(|s| s.get(PASSAGE_SLOT))
        .is_some_and(|&p| p == PASSAGE_ENDED);
    let gold = final_var(day, &run.play, "gold");
    let depth = final_var(day, &run.play, "depth");
    let downed = final_var(day, &run.play, "downed");
    let won = ended && gold == HOARD_GOLD;
    let fell = downed == 1;

    Html(run_card_page(
        day, run, verified, won, fell, ended, depth, gold,
    ))
}

/// Read a committed var off a playthrough's final recorded state via the day's var→slot map (`0` if
/// absent). Sound to read only when the chain re-verifies (which guarantees the recorded state is the
/// faithfully-reproduced one).
fn final_var(day: &Day, play: &Playthrough, name: &str) -> u64 {
    let Some(last) = play.steps.last() else {
        return 0;
    };
    day.var_slots
        .get(name)
        .and_then(|&slot| last.state.get(slot))
        .copied()
        .unwrap_or(0)
}

// ═══════════════════════════════════════════════════════════════════════════════
// Rendering.
// ═══════════════════════════════════════════════════════════════════════════════

/// One ranked, re-verified leaderboard row.
struct Row {
    run_id: String,
    player: String,
    turns: usize,
    depth: u64,
}

/// A short hex provenance tag of a day's seed (first 4 bytes) — the same tag `daily_scene` uses.
fn seed_tag(seed: &CommittedSeed) -> String {
    seed.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// The leaderboard page — a ranked table of provably-winning runs, each row re-verified on render
/// and linking to its run-card.
fn leaderboard_page(day: &Day, rows: &[Row]) -> String {
    let mut table = String::new();
    if rows.is_empty() {
        table.push_str(
            "<p class=\"prose\">No verified runs yet — a run appears here only once it re-executes to \
             the hoard. A forged or unfinished run never ranks.</p>",
        );
    } else {
        table.push_str(
            "<table class=\"board\"><thead><tr><th>#</th><th>player</th><th>turns</th>\
             <th>depth</th><th>proof</th></tr></thead><tbody>",
        );
        for (i, r) in rows.iter().enumerate() {
            table.push_str(&format!(
                "<tr><td>{rank}</td><td>{player}</td><td>{turns}</td><td>{depth}</td>\
                 <td><a href=\"{href}\">verify this run →</a></td></tr>",
                rank = i + 1,
                player = esc(&r.player),
                turns = r.turns,
                depth = r.depth,
                href = esc(&run_share_path(&r.run_id)),
            ));
        }
        table.push_str("</tbody></table>");
    }
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>The Descent — {title} · leaderboard</title>{style}</head><body>\
         <main class=\"session\">\
         <section class=\"deos-section tag-accent\"><h2>The Descent — {title}</h2>\
         <p class=\"prose\">Day <code>{key}</code> · seed <code>{seed}</code> · warden HP {whp} · \
         depth {rooms}</p>\
         <p class=\"prose\">The no-cheat leaderboard. Every row is <strong>re-verified on this \
         request</strong> — re-executed from its recorded moves against a fresh identically-seeded \
         world, required to reach the hoard. A forged or unfinished run does not appear.</p></section>\
         {table}\
         <p class=\"verify ok\">Independent by construction — open any run to re-verify it yourself.</p>\
         </main></body></html>",
        title = esc(&day.day.title),
        key = esc(&day.key),
        seed = esc(&seed_tag(&day.seed)),
        whp = day.day.warden_hp,
        rooms = day.day.deepening_rooms,
        style = STYLE,
        table = table,
    )
}

/// A run-card — the run summary + the independent-verification panel (PASS/FAIL).
#[allow(clippy::too_many_arguments)]
fn run_card_page(
    day: &Day,
    run: &Run,
    verified: bool,
    won: bool,
    fell: bool,
    ended: bool,
    depth: u64,
    gold: u64,
) -> String {
    // The verification panel — the whole point of the page.
    let panel = if verified {
        "<section class=\"deos-section tag-genuine\"><h2>Independent verification — PASS</h2>\
         <p class=\"prose\">This run was <strong>re-executed on this request</strong>: a fresh, \
         identically-seeded world was deployed and driven through the recorded moves, and the \
         committed receipt chain re-verified (chain-linkage + replay). You are not trusting a stored \
         result — you are seeing the run <strong>proven</strong>.</p>\
         <p class=\"verify ok\">verified by re-execution: <strong>yes</strong></p></section>"
            .to_string()
    } else {
        "<section class=\"deos-section tag-accent\" style=\"border-color:#833\">\
         <h2 style=\"color:#f77\">Independent verification — FAIL</h2>\
         <p class=\"prose\">Re-execution against a fresh identically-seeded world <strong>rejected</strong> \
         this record: the recorded moves do not honestly reproduce the committed chain. This run is \
         <strong>forged or tampered</strong> — its claimed outcome below is NOT proven.</p>\
         <p class=\"verify refused\">verified by re-execution: <strong>NO</strong></p></section>"
            .to_string()
    };

    // The outcome line — trusted only on PASS.
    let outcome = if !verified {
        "unverifiable (forged / tampered record)".to_string()
    } else if won {
        format!("SURVIVED — seized the hoard ({gold} gold) at depth {depth}")
    } else if fell {
        format!("FELL — downed by the warden at depth {depth}; the run is lost")
    } else if ended {
        format!("turned back — the descent ended without the hoard (depth {depth})")
    } else {
        format!("in progress — depth {depth}")
    };
    let alive = if fell {
        "dead (hardcore permadeath — final)"
    } else {
        "alive"
    };
    let class = if run.class == 0 {
        "unset".to_string()
    } else {
        format!("class #{}", run.class)
    };
    let turns = run.play.steps.len() + 1; // genesis + committed steps

    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <meta name=viewport content=\"width=device-width, initial-scale=1\">\
         <title>The Descent — {player}'s run</title>{style}</head><body>\
         <main class=\"session\">\
         <section class=\"deos-section tag-accent\"><h2>The Descent — {title}</h2>\
         <p class=\"prose\"><strong>{player}</strong> · day <code>{key}</code> · seed \
         <code>{seed}</code></p>\
         <p class=\"prose\">Character: level {level} · {class}</p>\
         <p class=\"prose\">Outcome: <strong>{outcome}</strong></p>\
         <p class=\"prose\">Status: {alive} · {turns} verified turns · warden HP {whp}</p></section>\
         {panel}\
         <p class=\"verify\"><a href=\"/descent/leaderboard?day={key}\">← today's no-cheat leaderboard</a></p>\
         </main></body></html>",
        player = esc(&run.player),
        title = esc(&day.day.title),
        key = esc(&day.key),
        seed = esc(&seed_tag(&day.seed)),
        level = run.level,
        class = esc(&class),
        outcome = esc(&outcome),
        alive = alive,
        turns = turns,
        whp = day.day.warden_hp,
        style = STYLE,
        panel = panel,
    )
}

/// The page shown when no day (or an unknown day) is requested.
fn leaderboard_missing(key: Option<&str>) -> String {
    let what = match key {
        Some(k) => format!("No day <code>{}</code> is open.", esc(k)),
        None => "No daily descent is open yet.".to_string(),
    };
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <title>The Descent — leaderboard</title>{style}</head><body>\
         <main class=\"session\"><div class=\"notice refused\">{what}</div></main></body></html>",
        style = STYLE,
        what = what,
    )
}

/// The page shown for an unknown run id.
fn run_missing(id: &str) -> String {
    format!(
        "<!doctype html><html lang=en><head><meta charset=utf-8>\
         <title>The Descent — unknown run</title>{style}</head><body>\
         <main class=\"session\"><div class=\"notice refused\">No such run <code>{id}</code>.</div>\
         </main></body></html>",
        style = STYLE,
        id = esc(id),
    )
}
