//! # game_api — THE SUNKEN VAULT, playable over HTTP.
//!
//! A second lane on the dungeon-service (additive to `/narrate`): a real dungeon-crawler
//! over ONE [`attested_dm::sunken_vault`] [`attested_dm::GameWorld`] and one
//! [`attested_dm::GameSession`]. A local language model (`gemma2:2b` via ollama) NARRATES
//! each room and action; the WORLD RESOLVES every move by [`attested_dm::resolve_action`]'s
//! deterministic rules. You cannot narrate through a locked door, take an absent item, pass
//! the Warden without the sword, or win without carrying the amulet to the gate.
//!
//! ## The AI narrates; the world resolves.
//!
//! Each turn: the free-text command is parsed into a *closed typed* [`attested_dm::GameAction`]
//! (`Move | Take | Use | Examine | Attack`), gemma2 narrates the moment atmospherically (its
//! prose carries NO authority), and the resolver decides. A legal move lands as ONE verified
//! chain turn ([`attested_dm::DungeonMaster::narrate_game_move`]) carrying its
//! [`attested_dm::GameBinding`]; a refused move leaves the world unchanged and lands no receipt
//! (the anti-ghost tooth). gemma2 may narrate the dark stair opening — the world says: barred,
//! it needs the lantern.
//!
//! ## What is REAL vs modeled (honest)
//!
//! * REAL and load-bearing: the WORLD RESOLUTION (a locked exit / absent item / unbeaten Warden
//!   is refused deterministically, regardless of prose), the CAP GATE (a `Take` is a
//!   cap-permitted grant on the dungeon's own item whitelist), and the HASH-CHAIN (every landed
//!   move is a prev-linked, injection-free, on-chain turn binding its typed action + room).
//! * REAL: the narration is a genuine `gemma2:2b` when ollama is reachable
//!   (`narratorKind: "model:gemma2:2b"`); else a deterministic scripted narrator.
//! * MODELED: the attestation's *authentic* leg is an in-tree fixture (`RecordedDm`), as in the
//!   `/narrate` lane. The receipt does not prove a real model produced the bytes; the resolver,
//!   the cap gate, and the chain are the real teeth.

use std::sync::Mutex;

use attested_dm::{
    sunken_vault, GameAction, GameBrain, GameSession, GameStatus, GameWorld, Gate, PlayResult,
    Proposal, Room, WorldCell,
};
use http_serve::WebResponse;
use serde_json::{json, Value};

use crate::ollama;

// ─────────────────────────────────────────────────────────────────────────────
// The narrator — a real gemma2 when reachable, else a deterministic scripted narrator.
// Either way the ACTION is parsed deterministically (the world resolves it); the model's
// only job is atmospheric prose, which has no authority over the outcome.
// ─────────────────────────────────────────────────────────────────────────────

/// The vault's dungeon-master narrator.
#[derive(Clone)]
pub enum VaultNarrator {
    /// A live ollama model at `endpoint` named `model` (e.g. `gemma2:2b`).
    Model { endpoint: String, model: String },
    /// A deterministic offline narrator (only when ollama is unreachable).
    Scripted,
}

/// The AI's proposal for a turn plus the narrator kind that produced it this turn (which may
/// be a scripted fallback even in `Model` mode, if the model call failed).
pub struct Proposed {
    pub proposal: Proposal,
    pub narrator_kind: String,
}

impl VaultNarrator {
    /// The narrator kind at the mode level (before any per-turn fallback).
    pub fn base_kind(&self) -> String {
        match self {
            VaultNarrator::Model { model, .. } => format!("model:{model}"),
            VaultNarrator::Scripted => "scripted:VaultGm".to_string(),
        }
    }

    /// Narrate + propose a typed action for `command` in `room`. The command is parsed
    /// deterministically into a closed [`GameAction`]; gemma2 (or the scripted fallback)
    /// narrates around it. `Err` if the command names no move (the DM asks to rephrase).
    pub fn propose(
        &self,
        room: &Room,
        world: &WorldCell,
        command: &str,
    ) -> Result<Proposed, String> {
        let action = parse_command(command).ok_or_else(|| {
            format!("The dungeon master tilts their head: \u{201c}{command}?\u{201d}")
        })?;
        let (narration, kind) = match self {
            VaultNarrator::Model { endpoint, model } => {
                match narrate_action(endpoint, model, room, world, command, &action) {
                    Ok(p) => (p, format!("model:{model}")),
                    Err(e) => {
                        eprintln!(
                            "dungeon-service /game: gemma2 narration failed ({e}); scripted this turn"
                        );
                        (
                            scripted_narration(room, &action),
                            "scripted:VaultGm(fallback)".to_string(),
                        )
                    }
                }
            }
            VaultNarrator::Scripted => (
                scripted_narration(room, &action),
                "scripted:VaultGm".to_string(),
            ),
        };
        Ok(Proposed {
            proposal: Proposal::new(narration, action),
            narrator_kind: kind,
        })
    }
}

impl GameBrain for VaultNarrator {
    fn take_turn(&self, room: &Room, world: &WorldCell, command: &str) -> Result<Proposal, String> {
        self.propose(room, world, command).map(|p| p.proposal)
    }
}

/// Ask gemma2 to narrate the moment (1-2 vivid sentences). The model is TOLD it does not
/// decide outcomes — it only describes. Returns just the narration prose (brace-stripped).
fn narrate_action(
    endpoint: &str,
    model: &str,
    room: &Room,
    world: &WorldCell,
    command: &str,
    action: &GameAction,
) -> Result<String, String> {
    let inv: Vec<String> = world.inventory.iter().cloned().collect();
    let carrying = if inv.is_empty() {
        "nothing".to_string()
    } else {
        inv.join(", ")
    };
    let prompt = format!(
        "You are the dungeon master of THE SUNKEN VAULT, a drowned dark-fantasy dungeon. \
         Narrate vividly but briefly, in the second person. You do NOT decide outcomes \u{2014} \
         the world resolves every move; you only describe the moment atmospherically.\n\
         Current room: {name} \u{2014} {desc}\n\
         The adventurer is carrying: {carrying}.\n\
         The adventurer's command: \"{command}\" (interpreted as the move: {label}).\n\n\
         Respond ONLY with a JSON object of this exact shape:\n\
         {{\"narration\": \"<1-2 vivid sentences continuing the scene; no curly braces; no \
         meta-commentary; do not claim the move succeeded or failed>\"}}",
        name = room.name,
        desc = room.description,
        label = action.label(),
    );
    let inner = ollama::generate_json(endpoint, model, &prompt)?;
    let narration = inner
        .get("narration")
        .and_then(Value::as_str)
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .ok_or_else(|| "model reply had no `narration` string".to_string())?;
    let stripped: String = narration
        .chars()
        .filter(|c| *c != '{' && *c != '}')
        .collect();
    let t = stripped.trim();
    if t.is_empty() {
        Ok("The dark holds its breath.".to_string())
    } else {
        Ok(t.to_string())
    }
}

/// The deterministic offline narrator (only when ollama is unreachable, or a turn's model
/// call failed). Atmospheric, but carries no authority — the resolver still decides.
fn scripted_narration(room: &Room, action: &GameAction) -> String {
    let here = room.name.to_lowercase();
    match action {
        GameAction::Move(to) => {
            format!("Lantern-shadows swaying, you leave the {here} and press on toward the {to}.")
        }
        GameAction::Take(i) => {
            format!("You reach into the gloom of the {here} and close your hand around the {i}.")
        }
        GameAction::Use(i, Some(t)) => {
            format!("Breath held, you work the {i} against the {t} in the {here}.")
        }
        GameAction::Use(i, None) => format!("You raise the {i} into the {here}'s dark."),
        GameAction::Examine => format!(
            "You steady your light and study the {here}: {}",
            room.description
        ),
        GameAction::Attack(t) => format!("Steel bared, you throw yourself at the {t}."),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The command parser — free text -> a closed typed GameAction, canonicalized to the
// dungeon's own item / target ids so the resolver recognizes them.
// ─────────────────────────────────────────────────────────────────────────────

/// Parse a free-text command into a closed [`GameAction`], canonicalizing loose words
/// ("key" -> `rusted_key`, "door" -> `iron_door`, …) to the ids the resolver expects.
fn parse_command(command: &str) -> Option<GameAction> {
    let lowered = command.trim().to_lowercase();
    // Keep alphanumerics, whitespace, and underscore (item ids carry underscores); drop the rest.
    let cleaned: String = lowered
        .chars()
        .map(|ch| {
            if ch.is_alphanumeric() || ch.is_whitespace() || ch == '_' {
                ch
            } else {
                ' '
            }
        })
        .collect();
    let words: Vec<&str> = cleaned.split_whitespace().collect();
    let head = *words.first()?;

    match head {
        "go" | "move" | "walk" | "head" | "descend" | "ascend" | "climb" | "enter" | "travel"
        | "run" | "step" => {
            let dir = words
                .iter()
                .skip(1)
                .find_map(|w| canon_dir(w))
                .or_else(|| words.get(1).map(|w| w.to_string()))?;
            Some(GameAction::Move(dir))
        }
        d if canon_dir(d).is_some() => Some(GameAction::Move(canon_dir(d).unwrap())),
        "take" | "grab" | "get" | "pick" | "loot" | "collect" | "seize" | "lift" => {
            let item = words
                .iter()
                .skip(1)
                .find(|w| !is_stopword(w) && **w != "up")?;
            Some(GameAction::Take(canon_item(item)))
        }
        "use" | "unlock" | "open" | "turn" | "insert" | "apply" | "wield" => {
            parse_use(head, &words)
        }
        "look" | "examine" | "inspect" | "survey" | "search" | "observe" | "study" | "peer" => {
            Some(GameAction::Examine)
        }
        "attack" | "fight" | "strike" | "kill" | "slay" | "hit" | "assault" | "charge" => {
            let t = words.iter().skip(1).find(|w| !is_stopword(w))?;
            Some(GameAction::Attack(canon_target(t)))
        }
        _ => None,
    }
}

/// Parse a "use / unlock / open" phrase into `Use(item, target)`. "use KEY on DOOR" names the
/// item first; "unlock DOOR with KEY" names the target first.
fn parse_use(head: &str, words: &[&str]) -> Option<GameAction> {
    let rest: Vec<&str> = words
        .iter()
        .skip(1)
        .cloned()
        .filter(|w| !is_stopword(w))
        .collect();
    let conn = rest
        .iter()
        .position(|w| matches!(*w, "on" | "with" | "against" | "into" | "in" | "to" | "at"));
    let (left, right): (&[&str], &[&str]) = match conn {
        Some(i) => (&rest[..i], &rest[i + 1..]),
        None => (&rest[..], &[]),
    };
    // "unlock/open DOOR with KEY" → item on the right; otherwise item on the left.
    let (item_side, target_side): (&[&str], &[&str]) = if matches!(head, "unlock" | "open") {
        (right, left)
    } else {
        (left, right)
    };

    let mut item: Option<String> = None;
    let mut target: Option<String> = None;
    for w in item_side {
        let ci = canon_item(w);
        if is_known_item(&ci) {
            item = Some(ci);
            break;
        }
    }
    for w in target_side {
        let ct = canon_target(w);
        if is_known_target(&ct) {
            target = Some(ct);
            break;
        }
    }
    // Fallback: scan the whole phrase for a known item / target.
    if item.is_none() {
        for w in &rest {
            let ci = canon_item(w);
            if is_known_item(&ci) {
                item = Some(ci);
                break;
            }
        }
    }
    if target.is_none() {
        for w in &rest {
            let ct = canon_target(w);
            if is_known_target(&ct) {
                target = Some(ct);
                break;
            }
        }
    }
    let item = item.or_else(|| rest.first().map(|w| canon_item(w)))?;
    Some(GameAction::Use(item, target))
}

fn is_stopword(w: &str) -> bool {
    matches!(w, "the" | "a" | "an" | "my" | "your" | "some")
}

fn canon_dir(w: &str) -> Option<String> {
    let d = match w {
        "north" | "n" => "north",
        "south" | "s" => "south",
        "east" | "e" => "east",
        "west" | "w" => "west",
        "up" | "u" | "upstairs" | "upward" | "upwards" => "up",
        "down" | "d" | "downstairs" | "downward" | "downwards" => "down",
        _ => return None,
    };
    Some(d.to_string())
}

fn canon_item(w: &str) -> String {
    let c = match w {
        "key" | "rusted" | "rusted_key" | "rustedkey" | "rustkey" => "rusted_key",
        "lantern" | "lamp" | "light" | "torch" | "lantirn" => "lantern",
        "sword" | "blade" | "weapon" => "sword",
        "amulet" | "heart" | "pendant" | "talisman" => "amulet",
        "pearl" => "pearl",
        other => return other.to_string(),
    };
    c.to_string()
}

fn canon_target(w: &str) -> String {
    let c = match w {
        "door" | "iron" | "iron_door" | "irondoor" | "lock" => "iron_door",
        "warden" | "knight" | "guardian" => "warden",
        other => return other.to_string(),
    };
    c.to_string()
}

fn is_known_item(id: &str) -> bool {
    matches!(id, "rusted_key" | "lantern" | "sword" | "amulet" | "pearl")
}

fn is_known_target(id: &str) -> bool {
    matches!(id, "iron_door" | "warden")
}

// ─────────────────────────────────────────────────────────────────────────────
// The service state — ONE GameSession (world + attested cap-bounded DM + narrator).
// ─────────────────────────────────────────────────────────────────────────────

/// The `/game` lane state: the live session, a clone of the narrator (called by the handler
/// to capture the AI's per-turn prose before the world resolves), and the last narrator kind.
pub struct GameState {
    session: GameSession<VaultNarrator>,
    brain: VaultNarrator,
    last_narrator_kind: String,
}

/// Build the `/game` state: probe ollama once, open a fresh sunken vault.
pub fn build_game_state() -> GameState {
    let brain = probe_vault_narrator();
    match &brain {
        VaultNarrator::Model { model, .. } => {
            eprintln!("dungeon-service /game: narrator = REAL model `{model}` (ollama)")
        }
        VaultNarrator::Scripted => {
            eprintln!("dungeon-service /game: narrator = scripted (ollama unreachable)")
        }
    }
    let last_narrator_kind = brain.base_kind();
    let session = GameSession::with_brain(sunken_vault(), brain.clone());
    GameState {
        session,
        brain,
        last_narrator_kind,
    }
}

/// Probe ollama once; a successful generation → the model, else the scripted fallback.
fn probe_vault_narrator() -> VaultNarrator {
    let endpoint =
        std::env::var("OLLAMA_ENDPOINT").unwrap_or_else(|_| "http://127.0.0.1:11434".to_string());
    let model = std::env::var("OLLAMA_MODEL").unwrap_or_else(|_| "gemma2:2b".to_string());
    match ollama::generate_json(
        &endpoint,
        &model,
        "Respond ONLY with the JSON object {\"narration\": \"a torch gutters against wet stone\"}.",
    ) {
        Ok(_) => VaultNarrator::Model { endpoint, model },
        Err(e) => {
            eprintln!("dungeon-service /game: model probe failed ({e}); scripted fallback");
            VaultNarrator::Scripted
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The JSON views.
// ─────────────────────────────────────────────────────────────────────────────

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A running fingerprint over the receipt chain (order-sensitive), for observing that a
/// refused move changes nothing. The authoritative tamper-evidence is in `/game/verify`.
fn commitment_hex(world: &WorldCell) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"sunken-vault-receipt-fingerprint-v1");
    for r in world.receipts() {
        h.update(&r);
    }
    hex(h.finalize().as_bytes())
}

fn status_str(s: GameStatus) -> &'static str {
    match s {
        GameStatus::Playing => "playing",
        GameStatus::Won => "won",
        GameStatus::Lost => "lost",
    }
}

fn gate_satisfied(g: &Gate, world: &WorldCell) -> bool {
    match g {
        Gate::NeedsItem(i) => world.inventory.contains(i),
        Gate::NeedsFlag(k, v) => world.flags.get(k).copied().unwrap_or(0) >= *v,
    }
}

/// A legible reason a gated exit is currently barred (mirrors the engine's `GateReason`
/// display, with friendlier text for the two known flag-gates).
fn gate_reason_str(g: &Gate) -> String {
    match g {
        Gate::NeedsItem(i) => format!("it needs the {i}"),
        Gate::NeedsFlag(k, _) if k == "door_unlocked" => {
            "the iron door is still locked".to_string()
        }
        Gate::NeedsFlag(k, _) if k == "warden_defeated" => {
            "the Warden still bars the way".to_string()
        }
        Gate::NeedsFlag(k, v) => format!("it stays sealed until {k} \u{2265} {v}"),
    }
}

fn objective_str(map: &GameWorld) -> String {
    let gate = map
        .room(&map.objective.room)
        .map(|r| r.name.clone())
        .unwrap_or_else(|| map.objective.room.clone());
    format!(
        "Escape the drowned vault with its heart: carry the {} to the {}.",
        map.objective.holding, gate
    )
}

/// The full game state view (shared by `/game/state` and the `state` field of `/game/act`).
fn state_json(gs: &GameState) -> Value {
    let session = &gs.session;
    let world = session.world();
    let map = session.map();

    let (room_json, exits, items_here) = match session.current_room() {
        Some(r) => {
            let exits: Vec<Value> = r
                .exits
                .iter()
                .map(|(dir, exit)| {
                    let (locked, reason) = match &exit.gate {
                        None => (false, Value::Null),
                        Some(g) => {
                            if gate_satisfied(g, world) {
                                (false, Value::Null)
                            } else {
                                (true, json!(gate_reason_str(g)))
                            }
                        }
                    };
                    let to_name = map
                        .room(&exit.to_room)
                        .map(|rr| rr.name.clone())
                        .unwrap_or_else(|| exit.to_room.clone());
                    json!({
                        "name": dir,
                        "to": exit.to_room,
                        "toName": to_name,
                        "locked": locked,
                        "gateReason": reason,
                    })
                })
                .collect();
            let items_here: Vec<String> = map.items_here(&r.id, world).into_iter().collect();
            (
                json!({ "id": r.id, "name": r.name, "description": r.description }),
                exits,
                items_here,
            )
        }
        None => (
            json!({ "id": world.scene, "name": "?", "description": "You are nowhere." }),
            Vec::new(),
            Vec::new(),
        ),
    };

    json!({
        "room": room_json,
        "inventory": world.inventory.iter().cloned().collect::<Vec<_>>(),
        "exits": exits,
        "itemsHere": items_here,
        "objective": objective_str(map),
        "status": status_str(session.status()),
        "receiptCount": world.ledger.len(),
        "commitmentHex": commitment_hex(world),
        "narratorKind": gs.last_narrator_kind,
    })
}

fn action_json(a: &GameAction) -> Value {
    match a {
        GameAction::Move(to) => json!({ "kind": "move", "to": to }),
        GameAction::Take(i) => json!({ "kind": "take", "item": i }),
        GameAction::Use(i, t) => json!({ "kind": "use", "item": i, "target": t }),
        GameAction::Examine => json!({ "kind": "look" }),
        GameAction::Attack(t) => json!({ "kind": "attack", "target": t }),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// `GET /game/state`.
pub fn handle_state(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    WebResponse::json(state_json(&g).to_string().into_bytes())
}

/// `POST /game/act {"command":"<free text>"}` — the AI narrates + proposes a typed action;
/// the world resolves it; a legal move lands as one verified turn; a refused move leaves the
/// world unchanged (the AI's flavor prose may still show, but `outcome:"refused"`).
pub fn handle_act(gs: &Mutex<GameState>, body: &[u8]) -> WebResponse {
    let parsed: Value = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let command = match parsed.get("command").and_then(Value::as_str) {
        Some(s) => s.to_string(),
        None => return WebResponse::error(400, "missing string field `command`"),
    };

    let mut g = gs.lock().unwrap();

    // The game is already decided — no further moves resolve.
    if g.session.status() != GameStatus::Playing {
        let reason = format!("the game is over ({})", status_str(g.session.status()));
        let state = state_json(&g);
        let resp = json!({
            "ok": false,
            "narration": "",
            "action": Value::Null,
            "outcome": "refused",
            "reason": reason,
            "state": state,
        });
        return WebResponse::json(resp.to_string().into_bytes());
    }

    let room = match g.session.current_room().cloned() {
        Some(r) => r,
        None => return WebResponse::error(500, "no current room"),
    };

    // The AI proposes (gemma2 narrates + the command is parsed into a typed action).
    let proposed = g.brain.propose(&room, g.session.world(), &command);
    let (proposal, kind) = match proposed {
        Ok(p) => (p.proposal, p.narrator_kind),
        Err(msg) => {
            // Unparsed: nothing lands; the DM asks the player to rephrase.
            g.last_narrator_kind = g.brain.base_kind();
            let state = state_json(&g);
            let resp = json!({
                "ok": false,
                "narration": msg,
                "action": Value::Null,
                "outcome": "refused",
                "reason": "the dungeon master could not read that as a move \u{2014} try 'go down', 'take lantern', 'use key on iron door', 'attack warden', or 'look'",
                "state": state,
            });
            return WebResponse::json(resp.to_string().into_bytes());
        }
    };
    g.last_narrator_kind = kind;
    let ai_narration = proposal.narration.clone();
    let action_j = action_json(&proposal.action);
    let action_label = proposal.action.label();

    // THE WORLD DISPOSES — resolve the proposed action; a legal move lands one verified turn.
    let result = g.session.play(proposal, "player", &command);
    let (ok, outcome, reason, world_note) = match &result {
        PlayResult::Landed { narration, .. } => (true, "landed", Value::Null, json!(narration)),
        PlayResult::Refused(r) => (false, "refused", json!(r.to_string()), Value::Null),
        PlayResult::DmRefused(e) => (false, "refused", json!(e.to_string()), Value::Null),
        PlayResult::Unparsed(m) => (false, "refused", json!(m), Value::Null),
    };

    let state = state_json(&g);
    let mut resp = json!({
        "ok": ok,
        "narration": ai_narration,
        "action": action_j,
        "actionLabel": action_label,
        "outcome": outcome,
        "state": state,
    });
    if !reason.is_null() {
        resp["reason"] = reason;
    }
    if !world_note.is_null() {
        resp["worldNote"] = world_note;
    }
    WebResponse::json(resp.to_string().into_bytes())
}

/// `GET /game/verify` — re-verify the whole game ledger as a hash chain.
pub fn handle_verify(gs: &Mutex<GameState>) -> WebResponse {
    let g = gs.lock().unwrap();
    let verified = g.session.verify().is_ok();
    let resp = json!({
        "verified": verified,
        "checks": "chain",
        "receiptCount": g.session.world().ledger.len(),
        "note": "re-verifies the whole game ledger as a hash chain \u{2014} every landed move authentic (fixture leg), well-formed, injection-free, and prev-linked on-chain; each landed turn also binds its typed GameAction \u{2016} room into its receipt, so a rewritten move or swapped room breaks the link",
    });
    WebResponse::json(resp.to_string().into_bytes())
}

/// `POST /game/reset` — a fresh sunken vault (a playthrough restarts cleanly).
pub fn handle_reset(gs: &Mutex<GameState>) -> WebResponse {
    let mut g = gs.lock().unwrap();
    let brain = g.brain.clone();
    g.session = GameSession::with_brain(sunken_vault(), brain);
    g.last_narrator_kind = g.brain.base_kind();
    let state = state_json(&g);
    WebResponse::json(
        json!({ "ok": true, "state": state })
            .to_string()
            .into_bytes(),
    )
}
