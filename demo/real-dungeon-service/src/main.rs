//! # real-dungeon-service — the REAL `dungeon-on-dregg` engine, played + verified over HTTP.
//!
//! The honest replacement for the LARP `/game` lane. It hosts the committed real game —
//! [`dungeon_on_dregg::deploy_keep`] (The Warden's Keep) — on `spween-dregg`'s real
//! [`WorldCell`](spween_dregg::WorldCell), the same `EmbeddedExecutor`/cell/`TurnReceipt` the
//! flagship substrate uses. Not a re-skin of `attested-dm`'s toy `WorldCell`/blake3 ledger:
//! this service does not depend on `attested-dm` at all.
//!
//! ## A move is a real executor turn over the wire
//!
//! `POST /session/move {"index":N}` looks up the chosen [`spween::Choice`] at the player's
//! current room and drives it at the real executor via
//! [`WorldCell::apply_choice`](spween_dregg::WorldCell::apply_choice): the choice's effects
//! become `Effect::SetField` cell writes, its navigation advances the passage slot, and the
//! whole thing is ONE cap-bounded turn the [`EmbeddedExecutor`] admits IFF the installed
//! [`CellProgram`] gate case passes on the post-state. A LEGAL move returns a real
//! [`TurnReceipt`](dregg_app_framework::TurnReceipt) (its `turnHash`/`preStateHash`/
//! `postStateHash` surfaced verbatim from the wire). An ILLEGAL move — e.g. claiming the
//! already-held crown for a rival banner (a `WriteOnce` tooth), an over-budget second ward
//! (a cross-slot `FieldLteField`), a killing blow (a `FieldGte` HP floor), climbing the
//! collapsed stair (a `Monotonic` ratchet) — is a real [`WorldError::Refused`] from the
//! executor that commits NOTHING (anti-ghost: the session state is unchanged).
//!
//! ## The endpoints
//!
//! * `POST /session/start {"seed":N?}` — (re)deploy a fresh keep WorldCell; seed the
//!   fight/budget the intro passage sets at genesis (`hp = 50`, `mana_budget = 50`).
//! * `GET  /session/state` — the current room, the executor-committed vars, ended/won, the
//!   committed receipt count + the last few receipt hashes.
//! * `GET  /session/moves` — the LEGAL moves at the current room, each with the real executor
//!   `StateConstraint` teeth guarding it (proof the rule is a kernel predicate, not app code).
//! * `POST /session/move {"index":N}` — one real cap-bounded turn (see above).
//! * `GET  /session/verify` — re-drive a fresh, identically-seeded keep through the recorded
//!   choice sequence ([`verify_by_replay`](spween_dregg::verify_by_replay)) and check the
//!   receipt chain links (`pre == prev.post`). Returns `verified: true` for an honest run.
//! * `GET  /` help; `GET /play` a minimal browser play page.
//!
//! ## Honest scope
//!
//! Verification here is **O(N) `verify_by_replay` + chain-linkage** — a stranger re-executes
//! the whole recorded turn sequence. It is NOT the succinct light client (a separate,
//! Lane-D-blocked workstream); this service does not claim it. A production deployment still
//! needs: player authentication + per-identity sessions (this is one in-memory session behind a
//! mutex), durable persistence of the ledger/receipts (state is process memory), and real
//! hosting/TLS (it binds a plain local HTTP/1.1 loop).
//!
//! Start: `cargo run -p real-dungeon-service` (binds `127.0.0.1:7879`; override
//! `REAL_DUNGEON_BIND`). `--self-check` drives a full playthrough in-process and exits.

use std::sync::{Arc, Mutex};

use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::{
    KP_CAST_WARD, KP_CLAIM_BLUE, KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE, KP_TRADE_BLOWS,
    case_constraints, choice_at, deploy_keep, keep_compiled, keep_scene,
};
use http_serve::{HttpMethod, ServeRequest, WebResponse, serve_http};
use serde_json::{Value as Json, json};
use spween::{Choice, PassageContent};
use spween_dregg::{
    CompiledStory, Playthrough, Scene, StepReceipt, Value, WorldCell, WorldError, choice_method,
    verify_by_replay,
};

/// The bind address (override with `REAL_DUNGEON_BIND`). Distinct from the LARP
/// `dungeon-service`'s `:7878` so both can run side by side.
const DEFAULT_BIND: &str = "127.0.0.1:7879";

/// The default deploy seed (deterministic cell identity + state hashes; a re-deploy at the
/// same seed reproduces exactly — what the replay verifier leans on).
const DEFAULT_SEED: u8 = 70;

// ─────────────────────────────────────────────────────────────────────────────
// The session — ONE real keep WorldCell + the recorded (verifiable) choice chain.
// ─────────────────────────────────────────────────────────────────────────────

/// A live game session over one real [`WorldCell`]. The `world` is the sole authority (its
/// committed cell state IS the game state); `steps` records each committed move so `/verify`
/// can rebuild a [`Playthrough`] and re-drive it by replay.
struct Session {
    /// The deploy seed (a fresh identically-seeded keep reproduces this session on replay).
    seed: u8,
    /// The real world-cell hosting the keep (the executor + ledger live inside it).
    world: WorldCell,
    /// The keep scene (the choice/passage source the moves + replay speak in).
    scene: Scene,
    /// The compiled + augmented program, for introspecting the executor teeth on each move.
    compiled: CompiledStory,
    /// passage index → room name (read off the committed passage slot).
    names: Vec<String>,
    /// The committed slot vector right after deploy+seed — the replay `genesis_state`.
    genesis_state: Vec<u64>,
    /// The committed move steps, in order (the input to `verify_by_replay`).
    steps: Vec<StepReceipt>,
}

impl Session {
    /// Deploy a fresh keep and seed the fight/budget the intro passage sets at genesis.
    fn new(seed: u8) -> Session {
        let mut world = deploy_keep(seed);
        // The KEEP intro passage's entry effects (`~ hp = 50`, `~ mana_budget = 50`) are what
        // the stock `Driver` commits at genesis. This service drives the executor directly via
        // `apply_choice` (the executor as sole referee, bypassing the client runtime), so it
        // seeds the same slots here — exactly as `examples/universe.rs` does — so a fresh
        // Driver-based replay (which DOES run the intro effects) reproduces the same state.
        world.seed_var("hp", Value::Int(50));
        world.seed_var("mana_budget", Value::Int(50));

        let compiled = keep_compiled();
        let mut names = vec![String::new(); compiled.passage_index.len()];
        for (name, &idx) in &compiled.passage_index {
            if idx < names.len() {
                names[idx] = name.clone();
            }
        }
        let genesis_state = world.snapshot();
        Session {
            seed,
            world,
            scene: keep_scene(),
            compiled,
            names,
            genesis_state,
            steps: Vec::new(),
        }
    }

    /// The player's current room name, or `None` if the scene has ended (won).
    fn current_room(&self) -> Option<&str> {
        self.world
            .read_passage()
            .and_then(|i| self.names.get(i))
            .map(|s| s.as_str())
    }

    /// The choices at `room` (in order), as `(index, &Choice)`.
    fn choices_of<'a>(scene: &'a Scene, room: &str) -> Vec<(usize, &'a Choice)> {
        scene
            .passages
            .iter()
            .find(|p| p.name.as_str() == room)
            .map(|p| {
                p.content
                    .iter()
                    .filter_map(|c| match c {
                        PassageContent::Choice(ch) => Some(ch),
                        _ => None,
                    })
                    .enumerate()
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Has the keep been cleared (a real WIN)? The scene ended AND the hoard was seized.
    fn won(&self) -> bool {
        self.world.read_passage().is_none() && self.world.read_var("gold") == 500
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// JSON views.
// ─────────────────────────────────────────────────────────────────────────────

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex8(h: &[u8; 32]) -> String {
    hex(&h[..8])
}

/// The receipt hashes, verbatim from the wire.
fn receipt_json(r: &TurnReceipt) -> Json {
    json!({
        "turnHash": hex(&r.turn_hash),
        "preStateHash": hex(&r.pre_state_hash),
        "postStateHash": hex(&r.post_state_hash),
    })
}

/// The full game state read off the committed cell.
fn state_json(s: &Session) -> Json {
    let ended = s.world.read_passage().is_none();
    let last: Vec<Json> = s
        .steps
        .iter()
        .rev()
        .take(3)
        .map(|st| {
            json!({
                "room": st.passage,
                "choice": st.choice_index,
                "turnHash": hex(&st.receipt.turn_hash),
            })
        })
        .collect();
    json!({
        "game": "The Warden's Keep",
        "room": s.current_room().unwrap_or("(cleared)"),
        "ended": ended,
        "won": s.won(),
        "vars": {
            "hp": s.world.read_var("hp"),
            "gold": s.world.read_var("gold"),
            "depth": s.world.read_var("depth"),
            "relic_owner": s.world.read_var("relic_owner"),
            "mana_spent": s.world.read_var("mana_spent"),
            "mana_budget": s.world.read_var("mana_budget"),
        },
        "committedMoves": s.steps.len(),
        "cellId": hex8(&s.world.cell_id().0),
        "recentReceipts": last,
    })
}

/// The legal moves at the current room, each with the real executor teeth guarding it.
fn moves_json(s: &Session) -> Json {
    let Some(room) = s.current_room().map(|r| r.to_string()) else {
        return json!({ "room": "(cleared)", "ended": true, "moves": [] });
    };
    let moves: Vec<Json> = Session::choices_of(&s.scene, &room)
        .into_iter()
        .map(|(i, ch)| {
            let teeth: Vec<String> = case_constraints(&s.compiled, &choice_method(&room, i))
                .iter()
                .map(|c| format!("{c:?}"))
                .collect();
            json!({
                "index": i,
                "text": ch.text.as_str(),
                "hasSpweenCondition": ch.condition.is_some(),
                "executorTeeth": teeth,
            })
        })
        .collect();
    json!({ "room": room, "ended": false, "moves": moves })
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// `POST /session/start {"seed":N?}` — (re)deploy a fresh keep and return the opening state.
fn handle_start(state: &Mutex<Session>, body: &[u8]) -> WebResponse {
    let seed = serde_json::from_slice::<Json>(body)
        .ok()
        .and_then(|v| v.get("seed").and_then(Json::as_u64))
        .map(|n| n as u8)
        .unwrap_or(DEFAULT_SEED);
    let mut s = state.lock().unwrap();
    *s = Session::new(seed);
    WebResponse::json(
        json!({ "ok": true, "seed": seed, "state": state_json(&s) })
            .to_string()
            .into_bytes(),
    )
}

/// `GET /session/state`.
fn handle_state(state: &Mutex<Session>) -> WebResponse {
    let s = state.lock().unwrap();
    WebResponse::json(state_json(&s).to_string().into_bytes())
}

/// `GET /session/moves`.
fn handle_moves(state: &Mutex<Session>) -> WebResponse {
    let s = state.lock().unwrap();
    WebResponse::json(moves_json(&s).to_string().into_bytes())
}

/// `POST /session/move {"index":N}` — drive one real cap-bounded turn at the executor.
fn handle_move(state: &Mutex<Session>, body: &[u8]) -> WebResponse {
    let parsed: Json = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let index = match parsed.get("index").and_then(Json::as_u64) {
        Some(n) => n as usize,
        None => return WebResponse::error(400, "missing integer field `index`"),
    };

    let mut s = state.lock().unwrap();
    let Some(room) = s.current_room().map(|r| r.to_string()) else {
        return WebResponse::json(
            json!({
                "ok": false, "refused": true,
                "reason": "the keep is already cleared \u{2014} the scene has ended",
                "state": state_json(&s),
            })
            .to_string()
            .into_bytes(),
        );
    };

    let choices = Session::choices_of(&s.scene, &room);
    if index >= choices.len() {
        return WebResponse::json(
            json!({
                "ok": false, "refused": true,
                "reason": format!("room `{room}` has no choice {index} (it has {})", choices.len()),
                "state": state_json(&s),
            })
            .to_string()
            .into_bytes(),
        );
    }

    // Look up the exact `Choice` and drive it at the real executor. `apply_choice` is the
    // primitive where the executor is the SOLE referee: an ineligible/forged pick is refused
    // in-band by the installed `CellProgram` gate case, and nothing commits (anti-ghost).
    let choice = choice_at(&s.scene, &room, index);
    match s.world.apply_choice(&room, index, &choice) {
        Ok(receipt) => {
            let step = StepReceipt {
                passage: room.clone(),
                choice_index: index,
                receipt: receipt.clone(),
                state: s.world.snapshot(),
                // Single-player `apply_choice` turn: nothing pinned in DECISION_EXT_KEY
                // (`Some` is only for collective `advance_certified` turns).
                decision_commitment: None,
            };
            s.steps.push(step);
            WebResponse::json(
                json!({
                    "ok": true,
                    "committed": true,
                    "move": { "room": room, "index": index, "text": choice.text.as_str() },
                    "receipt": receipt_json(&receipt),
                    "state": state_json(&s),
                })
                .to_string()
                .into_bytes(),
            )
        }
        Err(WorldError::Refused(why)) => WebResponse::json(
            json!({
                "ok": false,
                "refused": true,
                "reason": why,
                "note": "refused by the real executor (an installed StateConstraint tooth failed on the post-state) \u{2014} nothing committed (anti-ghost)",
                "state": state_json(&s),
            })
            .to_string()
            .into_bytes(),
        ),
        Err(other) => WebResponse::json(
            json!({ "ok": false, "error": other.to_string(), "state": state_json(&s) })
                .to_string()
                .into_bytes(),
        ),
    }
}

/// `GET /session/verify` — re-drive a fresh, identically-seeded keep through the recorded
/// choice sequence (replay) and check the receipt chain links.
fn handle_verify(state: &Mutex<Session>) -> WebResponse {
    let s = state.lock().unwrap();

    // (1) CHAIN LINKAGE over the committed step receipts: each turn is genuine (non-zero,
    //     distinct) and links to its predecessor (`pre == prev.post`). Splicing / dropping /
    //     reordering / tampering breaks a link. (Mirrors `verify_chain_linkage` over the
    //     move steps; the seeded genesis is a setup write, not a turn, so it is not in the
    //     receipt chain — the same pairwise linkage `examples/universe.rs` checks.)
    let (chain_ok, chain_note) = chain_links(&s.steps);

    // (2) REPLAY: re-drive a FRESH, identically-seeded keep through the recorded choices and
    //     confirm every step reproduces the recorded committed state, in passage order. A
    //     forged/ineligible pick is refused by the real executor on replay; an altered record
    //     diverges. The fresh keep's stock `Driver` runs the intro entry-effects as genesis,
    //     so it needs no manual seeding.
    let play = Playthrough {
        genesis: TurnReceipt::default(),
        genesis_state: s.genesis_state.clone(),
        steps: s.steps.clone(),
    };
    let replay = verify_by_replay(deploy_keep(s.seed), &s.scene, &play);
    let (replay_ok, replay_note) = match &replay {
        Ok(()) => (true, "replay reproduced every committed state".to_string()),
        Err(e) => (false, e.to_string()),
    };

    WebResponse::json(
        json!({
            "verified": chain_ok && replay_ok,
            "chainLinks": chain_ok,
            "chainNote": chain_note,
            "replayOk": replay_ok,
            "replayNote": replay_note,
            "committedMoves": s.steps.len(),
            "scope": "O(N) verify_by_replay + chain-linkage (a stranger re-executes the recorded turn sequence). NOT the succinct light client (separate, Lane-D-blocked) \u{2014} not claimed here.",
            "note": "verify_by_replay is the authoritative un-retconnable tooth (it reproduces every committed state). chainLinks holds when the winning moves are contiguous; a refused move interleaved between them advances the AGENT receipt chain (anti-replay) and discontinues the world-move pre/post chain without changing any committed state \u{2014} so demonstrate illegal refusals in a separate probe.",
        })
        .to_string()
        .into_bytes(),
    )
}

/// Chain-linkage check over the committed move steps (non-zero, distinct, `pre == prev.post`).
fn chain_links(steps: &[StepReceipt]) -> (bool, String) {
    let mut seen = std::collections::HashSet::new();
    for (i, st) in steps.iter().enumerate() {
        if st.receipt.turn_hash == [0u8; 32] {
            return (false, format!("step {i} has a zero turn hash"));
        }
        if !seen.insert(st.receipt.turn_hash) {
            return (false, format!("step {i} duplicates an earlier turn hash"));
        }
        if i > 0 && st.receipt.pre_state_hash != steps[i - 1].receipt.post_state_hash {
            return (
                false,
                format!("chain broken at step {i} (pre != prev.post)"),
            );
        }
    }
    (
        true,
        format!(
            "{} move receipts link cleanly (pre == prev.post)",
            steps.len()
        ),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Routing + serving.
// ─────────────────────────────────────────────────────────────────────────────

fn route(state: &Mutex<Session>, req: &ServeRequest) -> WebResponse {
    let path = req.target.split('?').next().unwrap_or(&req.target);
    match (req.method, path) {
        (HttpMethod::Post, "/session/start") => handle_start(state, &req.body),
        (HttpMethod::Get, "/session/state") => handle_state(state),
        (HttpMethod::Get, "/session/moves") => handle_moves(state),
        (HttpMethod::Post, "/session/move") => handle_move(state, &req.body),
        (HttpMethod::Get, "/session/verify") => handle_verify(state),
        (HttpMethod::Get, "/") => WebResponse::text(INDEX_HELP),
        (HttpMethod::Get, "/play") => WebResponse {
            status: 200,
            content_type: "text/html; charset=utf-8".to_string(),
            body: PLAY_HTML.as_bytes().to_vec(),
        },
        _ => WebResponse::error(404, "not found"),
    }
}

const INDEX_HELP: &str = "real-dungeon-service \u{2014} the REAL dungeon-on-dregg engine (The Warden's Keep) over HTTP\n\
    a move is one cap-bounded turn at the real executor; an illegal move is a real executor refusal.\n\n\
    POST /session/start {\"seed\":N?}   (re)deploy a fresh keep WorldCell\n\
    GET  /session/state                the executor-committed game state\n\
    GET  /session/moves                the legal moves + the executor teeth guarding each\n\
    POST /session/move  {\"index\":N}    drive one real turn -> a real TurnReceipt (or a real refusal)\n\
    GET  /session/verify               replay + chain-linkage over the recorded receipt chain\n\
    GET  /play                         a minimal browser play page\n";

const PLAY_HTML: &str = r#"<!doctype html><meta charset=utf-8><title>The Warden's Keep — real dregg</title>
<style>body{font:15px/1.5 ui-monospace,monospace;max-width:44rem;margin:2rem auto;padding:0 1rem;background:#12100e;color:#e8e0d0}
h1{font-size:1.2rem}button{font:inherit;margin:.15rem;padding:.3rem .6rem;background:#2a2620;color:#e8e0d0;border:1px solid #5a5040;border-radius:4px;cursor:pointer}
button:hover{background:#3a342a}pre{white-space:pre-wrap;background:#1c1a16;padding:.6rem;border-radius:6px}.r{color:#c9a227}.bad{color:#d06a5a}.ok{color:#7ac07a}</style>
<h1>The Warden's Keep <span style=opacity:.6>— the real dungeon-on-dregg engine</span></h1>
<div><button onclick=start()>▶ New session</button><button onclick=verify()>✓ Verify (replay)</button></div>
<div id=moves></div><pre id=log></pre>
<script>
const log=(m)=>{document.getElementById('log').textContent=m};
async function j(u,b){const r=await fetch(u,b?{method:'POST',body:JSON.stringify(b)}:{});return r.json()}
async function refresh(){const s=await j('/session/state');const mv=await j('/session/moves');
 let h='<div>room: <b>'+s.room+'</b> · hp '+s.vars.hp+' · gold '+s.vars.gold+' · depth '+s.vars.depth+(s.won?' · <span class=ok>WON</span>':'')+'</div>';
 (mv.moves||[]).forEach(m=>{h+='<button onclick="mv('+m.index+')">'+m.text+(m.executorTeeth.length?' 🔒':'')+'</button>'});
 document.getElementById('moves').innerHTML=h;return s}
async function start(){await j('/session/start',{});log('new keep deployed');refresh()}
async function mv(i){const r=await j('/session/move',{index:i});
 if(r.ok){log('✔ committed turn '+r.receipt.turnHash.slice(0,16)+'…\npre '+r.receipt.preStateHash.slice(0,16)+'… post '+r.receipt.postStateHash.slice(0,16)+'…')}
 else{log('REFUSED by the executor: '+r.reason)}refresh()}
async function verify(){const v=await j('/session/verify');log((v.verified?'✓ VERIFIED':'✗ FAILED')+' — replay '+v.replayOk+', chain '+v.chainLinks+'\n'+v.scope)}
start();
</script>"#;

fn main() -> std::io::Result<()> {
    if std::env::args().any(|a| a == "--self-check") {
        return self_check();
    }
    let bind = std::env::var("REAL_DUNGEON_BIND").unwrap_or_else(|_| DEFAULT_BIND.to_string());
    let state = Arc::new(Mutex::new(Session::new(DEFAULT_SEED)));
    eprintln!(
        "real-dungeon-service: hosting the REAL dungeon-on-dregg engine (The Warden's Keep) on \
         http://{bind}  (POST /session/start, GET /session/moves, POST /session/move, GET /session/verify)"
    );
    let handler = move |req: &ServeRequest| route(&state, req);
    serve_http(&bind, handler)
}

// ─────────────────────────────────────────────────────────────────────────────
// In-process self-check — drives a full playthrough to a WIN, an illegal refusal, and verify.
// ─────────────────────────────────────────────────────────────────────────────

fn self_check() -> std::io::Result<()> {
    println!("== real-dungeon-service :: self-check ==");
    println!(
        "hosting the REAL dungeon-on-dregg engine (The Warden's Keep) \u{2014} a move is a real executor turn.\n"
    );
    let mut fails = 0;

    // ── PHASE 1 — the winning run (contiguous legal moves) → a real receipt chain → /verify true.
    println!("── PHASE 1 · play The Warden's Keep to a WIN (real executor turns) ──");
    let state = Mutex::new(Session::new(DEFAULT_SEED));
    let plan: &[(usize, &str)] = &[
        (
            KP_TRADE_BLOWS,
            "trade blows with the warden (FieldGte hp floor)",
        ),
        (KP_PRESS_ON, "press on into the hall"),
        (KP_CLAIM_RED, "claim the crown for the Red Hand (WriteOnce)"),
        (
            KP_DESCEND,
            "descend the collapsing stair (Monotonic ratchet)",
        ),
        (KP_CAST_WARD, "cast the sealing ward (FieldLteField budget)"),
        (KP_SEIZE, "seize the hoard"),
    ];
    for (idx, label) in plan {
        let resp = move_via(&state, *idx);
        if resp["ok"].as_bool().unwrap_or(false) {
            let th = resp["receipt"]["turnHash"].as_str().unwrap_or("");
            println!(
                "  [OK ] move {idx} {label} -> committed turn {}…",
                &th[..th.len().min(16)]
            );
        } else {
            println!(
                "  [BAD] move {idx} {label} -> {}",
                resp["reason"].as_str().unwrap_or("?")
            );
            fails += 1;
        }
    }
    let won = state.lock().unwrap().won();
    println!("  WIN state reached: {won}");
    fails += (!won) as i32;

    let v = verify_via(&state);
    println!(
        "  /session/verify -> verified={} (replay={}, chain={})",
        v["verified"], v["replayOk"], v["chainLinks"]
    );
    println!("  chainNote: {}", v["chainNote"].as_str().unwrap_or(""));
    if v["verified"].as_bool() != Some(true) {
        fails += 1;
    }

    // ── PHASE 2 — an ILLEGAL move over the wire is a REAL executor refusal (anti-ghost).
    // A fresh session: walk to the hall, let the Red Hand claim the crown, then attempt the
    // rival Blue-Hand claim on the SAME crown. The executor's WriteOnce tooth refuses it in-band
    // and nothing commits (relic_owner still Red). Kept separate from the verified run because a
    // refused turn advances the AGENT's receipt chain (anti-replay), which would discontinue the
    // world-move pre/post chain — see the /verify note.
    println!("\n── PHASE 2 · an illegal move is a REAL executor refusal (anti-ghost) ──");
    let s2 = Mutex::new(Session::new(DEFAULT_SEED));
    move_via(&s2, KP_PRESS_ON); // gatehall -> hall
    let red = move_via(&s2, KP_CLAIM_RED);
    println!(
        "  Red claims the crown -> ok={}, relic_owner={}",
        red["ok"], red["state"]["vars"]["relic_owner"]
    );
    let blue = move_via(&s2, KP_CLAIM_BLUE);
    let refused = blue["refused"].as_bool().unwrap_or(false);
    let owner_after = blue["state"]["vars"]["relic_owner"].as_u64().unwrap_or(0);
    println!(
        "  Blue claims the SAME crown -> refused={refused}: {}",
        blue["reason"].as_str().unwrap_or("")
    );
    println!("  anti-ghost: relic_owner still {owner_after} (unchanged, Red holds it)");
    if !(refused && owner_after == 1) {
        fails += 1;
    }

    println!();
    if fails == 0 {
        println!(
            "ALL CHECKS PASSED \u{2014} the real keep is deployed, played to a WIN with a real receipt chain, /verify true, and an illegal move refused by the real executor (anti-ghost)."
        );
        Ok(())
    } else {
        println!("{fails} CHECK(S) FAILED");
        std::process::exit(1);
    }
}

fn move_via(state: &Mutex<Session>, index: usize) -> Json {
    let body = json!({ "index": index }).to_string();
    serde_json::from_slice(&handle_move(state, body.as_bytes()).body).unwrap_or(Json::Null)
}
fn verify_via(state: &Mutex<Session>) -> Json {
    serde_json::from_slice(&handle_verify(state).body).unwrap_or(Json::Null)
}
