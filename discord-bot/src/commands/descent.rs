//! `/descent` — THE DESCENT played LIVE in Discord: today's beacon-seeded, permadeath
//! procgen roguelite over the committed [`DailyDescentOffering`].
//!
//! This is the flagship's earning core (docs/GAME-STRATEGY.md Phase 1) made playable in the bot.
//! It drives the SAME committed
//! [`dreggnet_offerings::daily_descent::DailyDescentOffering`] the crate's own driven test does —
//! nothing is re-implemented here; the bot is a live *surface* over the real substrate:
//!
//! 1. **Today's beacon-seeded world.** [`resolve_todays_beacon`] pins a REAL published drand
//!    `quicknet` round (the committed beacon path); the day's [`CommittedSeed`] is
//!    [`DailyBeacon::seed`] (a BLS-pairing-verified fold of the round output). Everyone who plays
//!    "today" gets the byte-identical dungeon; a different day's verified round gives a different
//!    world (proven at the scene level in the tests). *A live drand HTTP fetch that advances the
//!    round each real day is the NAMED seam* — here we play the pinned round as today's beacon.
//! 2. **A permadeath run on the real executor.** Each move is one cap-bounded turn the verified
//!    executor admits (a real [`TurnReceipt`]); a blow you could not survive is REFUSED
//!    (`FieldGte(hp,1)`); a reckless line falls into a committed DEFEAT passage — a run can be
//!    genuinely LOST, and (hardcore) the persistent character PERISHES, `WriteOnce`-final.
//! 3. **A persistent, carrying character.** Level / class / earned XP / a hardcore death carry
//!    across days through the durable [`crate::character_store::SqliteCharacterStore`], keyed by
//!    the player's derived dregg identity (the SAME identity `/dungeon` attributes ballots to).
//! 4. **A no-cheat leaderboard.** A WON run publishes today's world as a
//!    [`ugc_dregg::Universe`] and submits a [`ugc_dregg::Completion`] the board accepts ONLY if it
//!    re-executes to the WIN on a stranger's re-execution — a forged / lost / incomplete run is
//!    refused ([`Registry::submit`]).
//!
//! ## What is live here vs the named seams
//! - **Live:** the daily offering, permadeath, the carrying character, the no-cheat board, and the
//!   paid/free AI narrator (the same `$DREGG` credit gate `/dungeon` uses, [`crate::pay`]).
//! - **Named seams:** the live drand HTTP fetch (advancing the round each real UTC day — here a
//!   pinned round); the midnight cron / `RevealReactor` auto-reveal (here a manual `/descent play`
//!   or scheduled trigger); the web spectator page (a separate lane); a durable leaderboard (the
//!   board is in-process here — the durable UGC store is `/gallery`'s).
//!
//! ## Threading
//! A live [`DailyRun`] holds `spween_dregg::WorldCell`s whose installed `Mandate`s are not `Send`
//! (the same reason [`crate::commands::offering::Store`] pins its sessions to a dedicated thread).
//! So the per-player runs + the in-process leaderboard live on ONE dedicated
//! [`DescentStore`] thread, driven by `Send` jobs that return `Send` snapshots; the async narrator
//! network call happens OFF that thread (on the Discord worker), exactly as `/dungeon` narrates
//! after a round resolves.

use std::collections::HashMap;
use std::sync::OnceLock;
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    ButtonStyle, CommandDataOptionValue, CommandInteraction, CommandOptionType,
    ComponentInteraction, Context, CreateActionRow, CreateButton, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateEmbedFooter, CreateInteractionResponse,
    CreateInteractionResponseMessage,
};

use dreggnet_offerings::character::CharacterStore;
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, DailyRun, GATE_FALL, GATE_HEAL, GATE_MEASURED, GATE_PRESS,
    GATE_RECKLESS, HOARD_FORCE, HOARD_GOLD, HOARD_SEIZE, KEY_TAKE,
};
use dreggnet_offerings::{DreggIdentity, OfferingError, Outcome};
use dungeon_on_dregg::progression::{MAGE, ROGUE, WARRIOR};
use procgen_dregg::beacon::DailyBeacon;
use ugc_dregg::{Registry, RejectReason, Universe, UniverseId};

use crate::BotState;
use crate::character_store::SqliteCharacterStore;
use crate::commands::offering::identity_of;

/// The Descent brand colour (a deep permadeath crimson-violet, distinct from `/dungeon`'s teal).
const DESCENT_COLOR: u32 = 0x9D174D;
/// The honest tagline that footers every Descent surface.
const TAGLINE: &str = "beacon-seeded · permadeath · the chain remembers · no-cheat board";
/// The leaderboard author label today's world is published under.
const BOARD_AUTHOR: &str = "the-descent";

// ─────────────────────────────────────────────────────────────────────────────
// Today's beacon — the committed drand `quicknet` round (the pinned reveal path).
// ─────────────────────────────────────────────────────────────────────────────

/// A REAL, PUBLISHED drand `quicknet` round (round 1_000_000) — the same vector `dregg-dice`'s
/// interop test and `dreggnet-offerings`' driven test pin. Here it is "today's beacon": a verified
/// reveal whose BLS pairing check holds, so the day's seed is a pure, un-grindable function of it.
const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
/// The round's threshold-BLS signature (the reveal `DailyBeacon::verify` re-checks by pairing).
const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

/// **Resolve today's daily beacon** — the pinned, verifiable drand `quicknet` reveal.
///
/// *The live drand HTTP fetch (advancing the round each real UTC day via
/// [`procgen_dregg::beacon::quicknet_round_for_utc_day`]) is the NAMED client seam.* Here we return
/// the committed pinned round: a genuine reveal whose pairing check holds, so `/descent` plays a
/// real beacon-verified day (a forged reveal is refused by [`DailyDescentOffering::open`]).
pub fn resolve_todays_beacon() -> DailyBeacon {
    DailyBeacon::quicknet(
        DRAND_QUICKNET_ROUND,
        hex::decode(DRAND_QUICKNET_SIG_HEX).expect("the pinned drand signature decodes"),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Scene-source parsing — the day's world is emitted as spween DSL text on
// `run.day().source`; the bot reads the current room's prose + its ordered choice
// labels straight out of it (the SAME order `WorldCell::apply_choice` indexes with),
// so the buttons carry the exact theme-flavoured labels the executor gates.
// ─────────────────────────────────────────────────────────────────────────────

/// The lines of the `=== <room>` section of a spween scene source (between its header and the
/// next `===`), so the room's prose + choices can be read out.
fn section_lines<'a>(source: &'a str, room: &str) -> Vec<&'a str> {
    let header = format!("=== {room}");
    let mut out = Vec::new();
    let mut in_section = false;
    for line in source.lines() {
        if let Some(rest) = line.strip_prefix("=== ") {
            // A `=== name` header: enter iff it is ours, else leave.
            in_section = rest.trim() == room;
            continue;
        }
        // A bare `===` also closes the section.
        if line.trim_start().starts_with("===") {
            in_section = false;
            continue;
        }
        if in_section {
            out.push(line);
        }
    }
    let _ = header;
    out
}

/// The ordered choice labels of `room` — each `* [Label] { cond }` line's `[Label]`, in scene
/// order (so the position IS the choice index the executor checks the gate case against).
fn room_choices(source: &str, room: &str) -> Vec<String> {
    section_lines(source, room)
        .iter()
        .filter_map(|line| {
            let t = line.trim_start();
            let t = t.strip_prefix("* ")?;
            let start = t.find('[')?;
            let end = t.find(']')?;
            if end > start {
                Some(t[start + 1..end].to_string())
            } else {
                None
            }
        })
        .collect()
}

/// The room's scripted prose (the descriptive lines of the section — not the `~` effects, the
/// `*` choices, or the choice bodies). This is the scene's own description a scripted narrator uses.
fn room_prose(source: &str, room: &str) -> String {
    let mut parts: Vec<String> = Vec::new();
    for line in section_lines(source, room) {
        let t = line.trim();
        if t.is_empty() || t.starts_with('~') || t.starts_with('*') || t.starts_with("->") {
            continue;
        }
        // Choice bodies are indented (`  ~ ...` / `  -> ...`) and already filtered; description
        // prose is a flush-left paragraph.
        if line.starts_with(' ') {
            continue;
        }
        parts.push(t.to_string());
    }
    parts.join(" ")
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-room ballot the bot renders — the ordered labels + a cap-eligibility
// decoration (the executor is the sole referee; a `!enabled` press still surfaces
// as a real refusal, so this is guidance, not the gate).
// ─────────────────────────────────────────────────────────────────────────────

/// One rendered move: the label, the choice index it applies, and whether its scene condition
/// currently holds (a decoration — the executor still refuses an ineligible move on `advance`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct MoveOption {
    label: String,
    index: usize,
    enabled: bool,
}

/// Whether choice `index` in `room` is currently eligible, read off the committed cell vars. Only
/// the `gate` room is gated; every other room's moves are ungated (always `true`).
fn choice_enabled(run: &DailyRun, room: &str, index: usize) -> bool {
    if room != "gate" {
        return true;
    }
    let hp = run.read_var("hp");
    let warden_hp = run.read_var("warden_hp");
    let heals_used = run.read_var("heals_used");
    match index {
        GATE_MEASURED => hp >= 16,
        GATE_RECKLESS => hp >= 31,
        GATE_HEAL => heals_used == 0,
        GATE_PRESS => warden_hp == 0,
        GATE_FALL => hp <= 20,
        _ => true,
    }
}

/// The rendered ballot for the run's current room — the scene labels (in index order) with the
/// eligibility decoration. Empty when the run has ended.
fn ballot(run: &DailyRun) -> Vec<MoveOption> {
    let Some(room) = run.current_room() else {
        return Vec::new();
    };
    room_choices(&run.day().source, &room)
        .into_iter()
        .enumerate()
        .map(|(index, label)| MoveOption {
            enabled: choice_enabled(run, &room, index),
            label,
            index,
        })
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// A `Send` snapshot of a run for rendering — taken on the store thread, rendered
// (and narrated) on the Discord worker. Carries only plain data.
// ─────────────────────────────────────────────────────────────────────────────

/// How a piece of narration was produced — surfaced honestly in the footer (mirrors `/dungeon`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NarratorKind {
    /// A real hosted model (AWS Bedrock) narrated it — a PAID run that spent one $DREGG credit.
    Bedrock,
    /// A real local `gemma2:2b` (ollama) narrated it (the free tier).
    Gemma,
    /// ollama was unreachable; the scene's own scripted prose stood in (the free tier).
    Scripted,
}

impl NarratorKind {
    fn label(self) -> &'static str {
        match self {
            NarratorKind::Bedrock => "narrator: bedrock (real AI · paid with a $DREGG credit)",
            NarratorKind::Gemma => "narrator: gemma2:2b (free)",
            NarratorKind::Scripted => "narrator: scripted (free)",
        }
    }
}

/// A `Send` render snapshot of a live run — the day + the committed vitals + the current ballot.
#[derive(Clone, Debug)]
struct RunView {
    day_title: String,
    /// The current room name (`None` once the run has ended).
    room: Option<String>,
    /// The current room's scripted prose (the narrator's fallback + the italic under-line).
    prose: String,
    hp: u64,
    warden_hp: u64,
    depth: u64,
    gold: u64,
    heals_used: u64,
    turns: usize,
    ended: bool,
    won: bool,
    dead: bool,
    level: u64,
    xp: u64,
    class_name: String,
    options: Vec<MoveOption>,
}

impl RunView {
    /// Snapshot a live run for rendering (on the store thread — plain data only).
    fn of(run: &DailyRun) -> RunView {
        let room = run.current_room();
        let prose = room
            .as_ref()
            .map(|r| room_prose(&run.day().source, r))
            .unwrap_or_default();
        let sheet = run.character().sheet();
        RunView {
            day_title: run.day().title.clone(),
            room,
            prose,
            hp: run.read_var("hp"),
            warden_hp: run.read_var("warden_hp"),
            depth: run.depth(),
            gold: run.read_var("gold"),
            heals_used: run.read_var("heals_used"),
            turns: run.turns(),
            ended: run.is_ended(),
            won: run.is_won(),
            dead: run.is_dead(),
            level: run.character().level(),
            xp: run.character().xp(),
            class_name: sheet.class_name().to_string(),
            options: ballot(run),
        }
    }
}

/// The `Send` result of advancing a run by one move — for the async render + narration layer.
#[derive(Clone, Debug)]
enum MoveResult {
    /// No run is open for this player.
    NoRun,
    /// The run already ended; nothing to advance.
    AlreadyEnded(RunView),
    /// The executor REFUSED the move (a gate bit): nothing committed, the room unchanged.
    Refused { why: String, view: RunView },
    /// The move landed a real committed turn; the post-move snapshot + any board outcome.
    Landed {
        view: RunView,
        /// The board rank this WON run earned (`None` for a continuing / lost run).
        rank: Option<usize>,
        /// An honest one-line note about the board outcome (submitted / refused / lost).
        board_note: String,
    },
}

// ─────────────────────────────────────────────────────────────────────────────
// The generic core — driven by BOTH the live store thread (over the durable
// `SqliteCharacterStore`) and the tests (over an `InMemoryCharacterStore`). Nothing
// here touches Discord; it is the daily offering + the no-cheat board, welded.
// ─────────────────────────────────────────────────────────────────────────────

/// **Open today's run for `who`** and PUBLISH today's world to `board` (idempotent) so a later WIN
/// can be submitted. Verifies the beacon (a forged reveal yields no run — fail-closed), draws the
/// day's world, deploys the run, and loads the player's persistent character.
fn open_core<S: CharacterStore>(
    off: &DailyDescentOffering<S>,
    board: &mut Registry,
    who: DreggIdentity,
    beacon: &DailyBeacon,
    class: Option<u64>,
) -> Result<(DailyRun, UniverseId), OfferingError> {
    let run = off.open(who, beacon)?;
    // A new player may pick a class (frozen `WriteOnce`; a re-class / a dead character is refused —
    // ignored, the run still opens).
    if let Some(class_id) = class {
        let _ = off.choose_class(&run, class_id);
    }
    let universe = run
        .day()
        .universe(BOARD_AUTHOR)
        .map_err(|e| OfferingError::Deploy(format!("could not publish today's world: {e:?}")))?;
    let uid = board.publish(universe);
    Ok((run, uid))
}

/// **Advance the run by one move; settle a terminal outcome.** Applies `choice` as one real turn;
/// on a landed move that ENDED the run it SAVES the character (persisting earned XP / a hardcore
/// death) and, iff the run WON, submits a [`ugc_dregg::Completion`] to the no-cheat `board`.
fn advance_core<S: CharacterStore>(
    off: &mut DailyDescentOffering<S>,
    run: &mut DailyRun,
    board: &mut Registry,
    universe_id: UniverseId,
    player: &str,
    choice: usize,
) -> MoveResult {
    if run.is_ended() {
        return MoveResult::AlreadyEnded(RunView::of(run));
    }
    match off.advance(run, choice) {
        Outcome::Refused(why) => MoveResult::Refused {
            why,
            view: RunView::of(run),
        },
        Outcome::Landed { ended, .. } => {
            let mut rank = None;
            let mut board_note = String::new();
            if ended {
                // Persist the character (earned XP / a hardcore death carries to the next day).
                off.save(run);
                if run.is_won() {
                    match off.completion(run, BOARD_AUTHOR, player) {
                        Ok(completion) => {
                            debug_assert_eq!(completion.universe, universe_id);
                            match board.submit(completion) {
                                Ok(accepted) => {
                                    rank = Some(accepted.rank);
                                    board_note = format!(
                                        "Ranked #{} on today's no-cheat board ({} verified turns).",
                                        accepted.rank, accepted.turns
                                    );
                                }
                                Err(e) => {
                                    board_note = format!("The board refused the run: {e}");
                                }
                            }
                        }
                        Err(e) => board_note = format!("Could not build a completion: {e:?}"),
                    }
                } else {
                    board_note =
                        "The descent ended without the hoard — it does not rank.".to_string();
                }
            }
            MoveResult::Landed {
                view: RunView::of(run),
                rank,
                board_note,
            }
        }
    }
}

/// A `Send` view of today's leaderboard — the ranked entries (player + turns-to-win).
#[derive(Clone, Debug)]
struct BoardView {
    day_title: String,
    entries: Vec<(usize, String, usize)>,
}

/// The current no-cheat leaderboard for today's world.
fn board_core(board: &Registry, universe_id: UniverseId, day_title: &str) -> BoardView {
    let entries = board
        .leaderboard(universe_id)
        .iter()
        .enumerate()
        .map(|(i, e)| (i + 1, short_player(&e.player), e.turns))
        .collect();
    BoardView {
        day_title: day_title.to_string(),
        entries,
    }
}

/// A short, legible player tag (the first 12 chars of the identity/label).
fn short_player(p: &str) -> String {
    p.chars().take(12).collect()
}

// ─────────────────────────────────────────────────────────────────────────────
// The dedicated store thread — owns every live run + the in-process board, keyed
// by discord user id. Mirrors `crate::commands::offering::Store`: `Send` jobs in,
// `Send` snapshots out; the non-`Send` `WorldCell`s never leave this thread. Each
// job captures a cheap `SqliteCharacterStore` clone (all durable state is in sqlite)
// to build the stateless daily offering.
// ─────────────────────────────────────────────────────────────────────────────

/// One player's live daily run + the board id of the day it is playing.
struct Slot {
    run: DailyRun,
    universe_id: UniverseId,
    narrator: NarratorKind,
    last_narration: String,
}

/// The world the store thread owns: every player's live run + the day's no-cheat board.
struct DescentWorld {
    slots: HashMap<u64, Slot>,
    board: Registry,
}

type DescentJob = Box<dyn FnOnce(&mut DescentWorld) + Send + 'static>;

/// The dedicated single-thread owner of all live runs + the board.
struct DescentStore {
    jobs: SyncSender<DescentJob>,
}

impl DescentStore {
    fn spawn() -> DescentStore {
        let (tx, rx) = sync_channel::<DescentJob>(64);
        std::thread::Builder::new()
            .name("descent-store".to_string())
            .spawn(move || {
                let mut world = DescentWorld {
                    slots: HashMap::new(),
                    board: Registry::new(),
                };
                while let Ok(job) = rx.recv() {
                    job(&mut world);
                }
            })
            .expect("spawn the descent store thread");
        DescentStore { jobs: tx }
    }

    /// Run `f` on the store thread and return its `Send` result.
    fn run<R: Send + 'static>(&self, f: impl FnOnce(&mut DescentWorld) -> R + Send + 'static) -> R {
        let (tx, rx) = sync_channel(1);
        let _ = self.jobs.send(Box::new(move |w| {
            let _ = tx.send(f(w));
        }));
        rx.recv().expect("the descent store thread is alive")
    }
}

/// The process-global store thread (lazy).
fn store() -> &'static DescentStore {
    static STORE: OnceLock<DescentStore> = OnceLock::new();
    STORE.get_or_init(DescentStore::spawn)
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register the `/descent` command (play / verify / board / today).
pub fn register() -> CreateCommand {
    CreateCommand::new("descent")
        .description(
            "THE DESCENT — today's beacon-seeded permadeath roguelite (your character carries)",
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "play",
                "Descend into today's dungeon (a real permadeath run on the dregg executor)",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "class",
                    "Pick your class if unclassed (warrior / mage / rogue) — frozen once chosen",
                )
                .add_string_choice("warrior", "warrior")
                .add_string_choice("mage", "mage")
                .add_string_choice("rogue", "rogue")
                .required(false),
            ),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify your current run's committed chain by replay",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "board",
            "Today's no-cheat leaderboard (a run ranks ONLY if it re-executes to the win)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "today",
            "Describe today's dungeon — its beacon-verified reveal + how it plays",
        ))
}

/// Route `/descent` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "play" => handle_play(ctx, command, state).await,
        "verify" => handle_verify(ctx, command, state).await,
        "board" => handle_board(ctx, command, state).await,
        "today" => handle_today(ctx, command).await,
        _ => {}
    }
}

async fn respond(
    ctx: &Context,
    command: &CommandInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
    ephemeral: bool,
) {
    let mut msg = CreateInteractionResponseMessage::new()
        .embed(embed)
        .components(rows);
    if ephemeral {
        msg = msg.ephemeral(true);
    }
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

fn class_id_of(label: &str) -> Option<u64> {
    match label {
        "warrior" => Some(WARRIOR),
        "mage" => Some(MAGE),
        "rogue" => Some(ROGUE),
        _ => None,
    }
}

// ─── /descent play ─────────────────────────────────────────────────────────────

async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let who = identity_of(state, user_id);
    let class = command.data.options.first().and_then(|sub| {
        if let CommandDataOptionValue::SubCommand(opts) = &sub.value {
            opts.first()
                .and_then(|o| o.value.as_str())
                .and_then(class_id_of)
        } else {
            None
        }
    });

    let store_clone = state.characters.clone();
    let beacon = resolve_todays_beacon();

    // Open today's run on the store thread (verifies the beacon, deploys the world, loads the
    // carried character, publishes today's world to the board). `Send` in, a `Send` `RunView` out.
    let opened: Result<RunView, String> = store().run(move |w| {
        let off = DailyDescentOffering::new(store_clone);
        match open_core(&off, &mut w.board, who, &beacon, class) {
            Ok((run, uid)) => {
                let view = RunView::of(&run);
                w.slots.insert(
                    user_id,
                    Slot {
                        run,
                        universe_id: uid,
                        narrator: NarratorKind::Scripted,
                        last_narration: String::new(),
                    },
                );
                Ok(view)
            }
            Err(e) => Err(e.to_string()),
        }
    });

    let view = match opened {
        Ok(v) => v,
        Err(why) => {
            let embed = error_embed(
                "Today's descent did not open",
                &format!("The beacon-seeded world failed to deploy: {why}"),
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };

    // Narrate the opening room OFF the store thread (the network call), then record it.
    let (narration, kind) = narrate_room_gated(
        state,
        user_id,
        view.room.as_deref().unwrap_or("the threshold"),
        &view.prose,
    )
    .await;
    record_narration(user_id, &narration, kind);

    let embed = room_embed(&view, &narration, kind);
    let rows = move_rows(user_id, &view.options);
    respond(ctx, command, embed, rows, false).await;
}

// ─── the move buttons (a press advances the presser's OWN run) ──────────────────

/// Route a `descent:` component press. custom_id: `descent:move:<userId>:<choiceIndex>`.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.clone();
    let parts: Vec<&str> = id.split(':').collect();
    if parts.len() != 4 || parts[1] != "move" {
        return;
    }
    let owner: u64 = match parts[2].parse() {
        Ok(n) => n,
        Err(_) => return,
    };
    let choice: usize = match parts[3].parse() {
        Ok(n) => n,
        Err(_) => return,
    };
    let presser = component.user.id.get();

    // A descent is a SOLO permadeath run — only its owner may move it.
    if presser != owner {
        let _ = component
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .content(
                            "This is not your descent — run `/descent play` to begin your own.",
                        )
                        .ephemeral(true),
                ),
            )
            .await;
        return;
    }

    let store_clone = state.characters.clone();
    let player = short_player(&identity_of(state, owner).0);
    let result = store().run(move |w| {
        let Some(slot) = w.slots.get_mut(&owner) else {
            return MoveResult::NoRun;
        };
        let mut off = DailyDescentOffering::new(store_clone);
        let uid = slot.universe_id;
        advance_core(&mut off, &mut slot.run, &mut w.board, uid, &player, choice)
    });

    match result {
        MoveResult::NoRun => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(
                                "Your descent has expired — run `/descent play` to begin anew.",
                            )
                            .ephemeral(true),
                    ),
                )
                .await;
        }
        MoveResult::Refused { why, view } => {
            // A real executor refusal: the room is unchanged, no receipt committed (anti-ghost).
            let (narration, kind) = current_narration(owner, &view);
            let embed = room_embed(&view, &narration, kind).field(
                "Refused — the world disposed",
                format!("```{}```", truncate(&why, 500)),
                false,
            );
            update_message(ctx, component, embed, move_rows(owner, &view.options)).await;
        }
        MoveResult::AlreadyEnded(view) => {
            let embed = result_embed(&view, None, "This descent has already ended.");
            update_message(ctx, component, embed, vec![]).await;
        }
        MoveResult::Landed {
            view,
            rank,
            board_note,
        } => {
            if view.ended {
                let embed = result_embed(&view, rank, &board_note);
                update_message(ctx, component, embed, vec![]).await;
            } else {
                // Narrate the NEXT room OFF the store thread, then re-render.
                let (narration, kind) = narrate_room_gated(
                    state,
                    owner,
                    view.room.as_deref().unwrap_or("the dark"),
                    &view.prose,
                )
                .await;
                record_narration(owner, &narration, kind);
                let embed = room_embed(&view, &narration, kind);
                update_message(ctx, component, embed, move_rows(owner, &view.options)).await;
            }
        }
    }
}

async fn update_message(
    ctx: &Context,
    component: &ComponentInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
) {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::UpdateMessage(
                CreateInteractionResponseMessage::new()
                    .embed(embed)
                    .components(rows),
            ),
        )
        .await;
}

/// Record how the current room was narrated (a brief job on the store thread).
fn record_narration(owner: u64, narration: &str, kind: NarratorKind) {
    let narration = narration.to_string();
    store().run(move |w| {
        if let Some(slot) = w.slots.get_mut(&owner) {
            slot.narrator = kind;
            slot.last_narration = narration;
        }
    });
}

/// The narration last recorded for this player's current room (so a refusal re-render keeps the
/// prose and never re-hits the network). Falls back to the room's scripted prose.
fn current_narration(owner: u64, view: &RunView) -> (String, NarratorKind) {
    let recorded = store().run(move |w| {
        w.slots
            .get(&owner)
            .map(|s| (s.last_narration.clone(), s.narrator))
    });
    match recorded {
        Some((n, k)) if !n.trim().is_empty() => (n, k),
        _ => (view.prose.clone(), NarratorKind::Scripted),
    }
}

// ─── /descent verify ────────────────────────────────────────────────────────────

async fn handle_verify(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let user_id = command.user.id.get();
    let store_clone = state.characters.clone();
    enum V {
        NoRun,
        Report {
            verified: bool,
            turns: usize,
            detail: String,
        },
    }
    let outcome = store().run(move |w| match w.slots.get(&user_id) {
        None => V::NoRun,
        Some(slot) => {
            let off = DailyDescentOffering::new(store_clone);
            let report = off.verify(&slot.run);
            V::Report {
                verified: report.verified,
                turns: slot.run.turns(),
                detail: report.detail,
            }
        }
    });

    let embed = match outcome {
        V::NoRun => warn_embed(
            "No descent open",
            "You have no run open. Begin one with `/descent play`.",
        ),
        V::Report {
            verified: true,
            turns,
            ..
        } => base_embed("✓ Your descent re-verifies by replay").description(format!(
            "**{turns} verified turns** re-verify: a fresh, identically beacon-seeded world-cell, \
             re-driven through your recorded choices, reproduces exactly your committed state \
             chain. A reordered, mutated, or ineligible move would break replay."
        )),
        V::Report { turns, detail, .. } => error_embed(
            "✗ Your descent FAILS replay",
            &format!("The recorded chain did not re-verify ({turns} turns):\n`{detail}`"),
        ),
    };
    respond(ctx, command, embed, vec![], true).await;
}

// ─── /descent board ───────────────────────────────────────────────────────────

async fn handle_board(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    // Today's board id is derived from the beacon-drawn world (published on any `/descent play`).
    // Compute it purely (no state needed) so the board renders even before this process's first run.
    let beacon = resolve_todays_beacon();
    let (day_title, uid) = match today_universe(&beacon) {
        Ok(v) => v,
        Err(why) => {
            let embed = error_embed("Today's board is unavailable", &why);
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };
    let view = store().run(move |w| board_core(&w.board, uid, &day_title));
    respond(ctx, command, board_embed(&view), vec![], false).await;
}

// ─── /descent today ─────────────────────────────────────────────────────────────

async fn handle_today(ctx: &Context, command: &CommandInteraction) {
    let beacon = resolve_todays_beacon();
    let title = today_universe(&beacon)
        .map(|(t, _)| t)
        .unwrap_or_else(|_| "today's descent".to_string());
    let desc = format!(
        "**{title}** — today's dungeon is a pure function of a beacon-verified drand `quicknet` \
         reveal (round {round}). Everyone plays the byte-identical world; a different day's \
         verified round gives a different dungeon.\n\n\
         Every move is one cap-bounded turn the verified executor admits:\n\
         • **the warden** — a blow you could not survive is refused (`FieldGte(hp,1)`)\n\
         • **the field-dressing** — a one-shot heal (`FieldLte(heals_used,1)`)\n\
         • **the sealed hoard-door** — opens only with the key (`FieldGte(has_key,1)`)\n\
         • **defeat is real** — a reckless line falls into a committed DEFEAT, and (hardcore) \
         your persistent character PERISHES, un-undoably\n\n\
         Your character (level / class / earned XP / a hardcore death) carries across days. A WON \
         run posts to the no-cheat board — ranked only if it re-executes to the win.\n\n\
         Descend with `/descent play`.\n\n\
         _Named seams: the live drand fetch that advances the round each real day; the midnight \
         auto-reveal; a web spectator page._",
        round = DRAND_QUICKNET_ROUND,
    );
    let embed = base_embed(&format!("{title} — the day's reveal")).description(desc);
    respond(ctx, command, embed, vec![], true).await;
}

/// Today's world title + its content-addressed board id, computed purely from the verified beacon
/// (no live run needed). Fails closed if the beacon does not verify.
fn today_universe(beacon: &DailyBeacon) -> Result<(String, UniverseId), String> {
    let seed = beacon
        .seed()
        .map_err(|e| format!("the beacon did not verify: {e:?}"))?;
    let day = dreggnet_offerings::daily_descent::daily_scene(&seed);
    let universe: Universe =
        Universe::authored(&day.title, BOARD_AUTHOR, &day.source, day.win_condition())
            .map_err(|e| format!("could not author today's world: {e:?}"))?;
    Ok((day.title, universe.id()))
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — embeds + move buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// A fixed-width HP bar `[█████████░░░░░░░]`.
fn hp_bar(cur: u64, max: u64, width: usize) -> String {
    let max = max.max(1);
    let filled = ((cur.min(max) as f64 / max as f64) * width as f64).round() as usize;
    let filled = filled.min(width);
    let mut out = String::with_capacity(width + 2);
    out.push('[');
    out.extend(std::iter::repeat('█').take(filled));
    out.extend(std::iter::repeat('░').take(width - filled));
    out.push(']');
    out
}

/// The status HUD read straight off the committed cell.
fn status_block(view: &RunView) -> String {
    let state = if view.dead {
        "PERISHED (hardcore)"
    } else if view.won {
        "SURVIVED — hoard seized"
    } else if view.ended {
        "descent ended"
    } else {
        "descending"
    };
    format!(
        "HP     {hp_bar} {hp}/50\n\
         warden {warden_hp}   depth {depth}   gold {gold}   heals {heals}/1\n\
         hero   L{level} {class}  ·  XP {xp}\n\
         state  {state}   ·   verified turns {turns}",
        hp_bar = hp_bar(view.hp, 50, 16),
        hp = view.hp,
        warden_hp = view.warden_hp,
        depth = view.depth,
        gold = view.gold,
        heals = view.heals_used,
        level = view.level,
        class = view.class_name,
        xp = view.xp,
        state = state,
        turns = view.turns,
    )
}

/// The live room embed: the narrated prose, the status HUD, and the move ballot.
fn room_embed(view: &RunView, narration: &str, kind: NarratorKind) -> CreateEmbed {
    let mut desc = truncate(narration, 1600);
    if narration.trim() != view.prose.trim() && !view.prose.trim().is_empty() {
        desc.push_str("\n\n");
        desc.push_str(&format!("_{}_", truncate(&view.prose, 800)));
    }
    let room = view.room.clone().unwrap_or_else(|| "the dark".to_string());
    base_embed(&format!("{} — {}", view.day_title, room))
        .description(truncate(&desc, 4000))
        .field("Vitals", format!("```{}```", status_block(view)), false)
        .footer(footer(kind))
}

/// The final result embed — depth, alive/dead, the win/loss verdict, board rank, and a
/// `/descent verify`-able receipt note.
fn result_embed(view: &RunView, rank: Option<usize>, board_note: &str) -> CreateEmbed {
    let (title, verdict) = if view.won {
        (
            "🏆 The hoard is seized — the descent is SURVIVED",
            "You reached the hoard and carried it out. A verified win.".to_string(),
        )
    } else if view.dead {
        (
            "💀 PERISHED — the descent is lost",
            "A blow you could not answer felled you. Your hardcore character has PERISHED, \
             un-undoably — the death carries to every future day."
                .to_string(),
        )
    } else {
        (
            "The descent ended",
            "The run ended without the hoard.".to_string(),
        )
    };
    let rank_line = match rank {
        Some(r) => format!("\n\n**Leaderboard: ranked #{r}** on today's no-cheat board."),
        None => String::new(),
    };
    let body = format!(
        "{verdict}{rank_line}\n\n{note}\n\n**{turns} verified turns** on the chain — run \
         `/descent verify` to re-check them by replay.",
        verdict = verdict,
        rank_line = rank_line,
        note = board_note,
        turns = view.turns,
    );
    base_embed(&format!("{} — {}", view.day_title, title))
        .description(truncate(&body, 4000))
        .field(
            "Final vitals",
            format!("```{}```", status_block(view)),
            false,
        )
        .footer(footer(NarratorKind::Scripted))
}

/// The no-cheat leaderboard embed.
fn board_embed(view: &BoardView) -> CreateEmbed {
    let body = if view.entries.is_empty() {
        "No verified survivors yet today. Be the first — `/descent play`.".to_string()
    } else {
        let mut lines = String::new();
        for (rank, player, turns) in view.entries.iter().take(20) {
            lines.push_str(&format!("{rank:>2}. {player:<14} {turns} turns\n"));
        }
        format!("```{}```", truncate(&lines, 1800))
    };
    base_embed(&format!("{} — today's no-cheat board", view.day_title))
        .description(format!(
            "Ranked by turns-to-win (lower is better). A run ranks ONLY if its recorded receipt \
             chain re-executes to the WIN on an independent re-run — a forged or incomplete run is \
             refused.\n\n{body}"
        ))
        .footer(footer(NarratorKind::Scripted))
}

/// The move buttons for the current room, chunked into Discord action rows of five. A locked
/// (ineligible) move is a red button decoration; the executor is still the sole referee.
fn move_rows(owner: u64, options: &[MoveOption]) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for (row_idx, chunk) in options.chunks(5).enumerate() {
        if row_idx >= 5 {
            break;
        }
        let mut buttons: Vec<CreateButton> = Vec::new();
        for opt in chunk {
            let label = if opt.enabled {
                opt.label.clone()
            } else {
                format!("🔒 {}", opt.label)
            };
            let style = if opt.enabled {
                ButtonStyle::Primary
            } else {
                ButtonStyle::Secondary
            };
            buttons.push(
                CreateButton::new(format!("descent:move:{owner}:{}", opt.index))
                    .label(truncate(&label, 78))
                    .style(style),
            );
        }
        if !buttons.is_empty() {
            rows.push(CreateActionRow::Buttons(buttons));
        }
    }
    rows
}

fn base_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new().title(title).color(DESCENT_COLOR)
}

fn error_embed(title: &str, body: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(body)
        .color(0xE63946)
}

fn warn_embed(title: &str, body: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(body)
        .color(0xE9C46A)
}

fn footer(kind: NarratorKind) -> CreateEmbedFooter {
    CreateEmbedFooter::new(format!("{} · {}", kind.label(), TAGLINE))
}

// ─────────────────────────────────────────────────────────────────────────────
// The narrator — the SAME $DREGG credit gate `/dungeon` uses (real Bedrock paid,
// local gemma2:2b free, scripted fallback). The paid backend is never free-ridden:
// a paid narration debits exactly one credit AFTER a successful hosted call.
// ─────────────────────────────────────────────────────────────────────────────

/// Narrate a room, spending a `$DREGG` run-credit on real Bedrock when the player has one, else the
/// FREE tier (ollama gemma / scripted). The narrator kind is reported honestly.
async fn narrate_room_gated(
    state: &BotState,
    discord_user_id: u64,
    room_name: &str,
    room_desc: &str,
) -> (String, NarratorKind) {
    let discord = discord_user_id.to_string();
    if state.pay.can_run_paid(&discord) {
        if let Some(paid) = state.pay.paid.clone() {
            let system = narrator_system_prompt();
            let prompt = format!("Room: {room_name}. {room_desc}");
            // The hosted Bedrock client drives its OWN runtime with `block_on`; run it off-worker.
            let narration = tokio::task::spawn_blocking(move || paid.narrate(&system, &prompt))
                .await
                .ok()
                .and_then(|r| r.ok())
                .filter(|n| !n.text.trim().is_empty());
            if let Some(n) = narration {
                let _ = state.pay.debit_one(&discord);
                return (sanitize(&n.text), NarratorKind::Bedrock);
            }
        }
    }
    narrate_room_free(room_name, room_desc).await
}

/// The Descent narrator's system instruction (a solo permadeath crawl, not a party dungeon).
fn narrator_system_prompt() -> String {
    "You are the dungeon master of a solo permadeath descent into a beacon-cursed dungeon. In two \
     vivid, ominous sentences, set the scene for the lone descender as they arrive. Do NOT use \
     curly braces."
        .to_string()
}

/// The FREE narrator tier — a real local `gemma2:2b` over ollama, falling back to the scene's own
/// scripted prose (reported honestly as `Scripted`) when ollama is unreachable.
async fn narrate_room_free(room_name: &str, room_desc: &str) -> (String, NarratorKind) {
    match gemma_narrate(room_name, room_desc).await {
        Some(text) if !text.trim().is_empty() => (sanitize(&text), NarratorKind::Gemma),
        _ => (room_desc.to_string(), NarratorKind::Scripted),
    }
}

/// One ollama `/api/generate` call (model `gemma2:2b`, `stream:false`). `None` on any failure.
async fn gemma_narrate(room_name: &str, room_desc: &str) -> Option<String> {
    let endpoint =
        std::env::var("OLLAMA_URL").unwrap_or_else(|_| "http://127.0.0.1:11434".to_string());
    let url = format!("{}/api/generate", endpoint.trim_end_matches('/'));
    let prompt = format!(
        "You are the dungeon master of a solo permadeath dungeon descent. In two vivid, ominous \
         sentences, set the scene for the lone descender as they arrive. Do NOT use curly braces. \
         Room: {room_name}. {room_desc}"
    );
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(20))
        .build()
        .ok()?;
    let body = serde_json::json!({
        "model": "gemma2:2b",
        "prompt": prompt,
        "stream": false,
        "options": { "temperature": 0.7 },
    });
    let resp = client.post(&url).json(&body).send().await.ok()?;
    if !resp.status().is_success() {
        return None;
    }
    let value: serde_json::Value = resp.json().await.ok()?;
    value
        .get("response")
        .and_then(|v| v.as_str())
        .map(str::to_string)
}

/// Drop the two JSON-hostile bytes + control chars but KEEP `{`/`}` (the executor, not this tidy,
/// is what refuses an injecting move).
fn sanitize(s: &str) -> String {
    s.chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control() || *c == '\n')
        .collect::<String>()
        .trim()
        .to_string()
}

/// Truncate to at most `max` chars (char-safe), appending `…` when cut.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the live daily /descent DRIVEN end to end over the REAL committed
// `DailyDescentOffering`, through the bot's own core (open → play → win/lose →
// carry → verify → no-cheat board), plus the scene-source render helpers + the
// beacon-daily property. No live Discord required (the sync cores the handlers
// call are driven directly over an in-memory character store).
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::character::InMemoryCharacterStore;
    use dreggnet_offerings::daily_descent::daily_scene;

    fn player(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_string())
    }

    /// Drive a CAREFUL winning line to the hoard through the bot's `advance_core` (fight the
    /// warden down, healing once if the beacon drew a tough warden, press past, take the key, walk
    /// the corridors, force the door, seize the hoard). Returns the terminal `MoveResult`.
    fn drive_win(
        off: &mut DailyDescentOffering<InMemoryCharacterStore>,
        run: &mut DailyRun,
        board: &mut Registry,
        uid: UniverseId,
        who: &str,
    ) -> MoveResult {
        let mut last = MoveResult::NoRun;
        for _ in 0..64 {
            let Some(room) = run.current_room() else {
                break;
            };
            let ci = match room.as_str() {
                "gate" => {
                    if run.read_var("warden_hp") == 0 {
                        GATE_PRESS
                    } else if run.read_var("hp") >= 16 {
                        GATE_MEASURED
                    } else {
                        GATE_HEAL
                    }
                }
                "keyroom" => KEY_TAKE,
                "hoardgate" => HOARD_FORCE,
                "hoard" => HOARD_SEIZE,
                r if r.starts_with("corridor") => CORRIDOR_ON,
                other => panic!("unexpected room in a winning line: {other}"),
            };
            last = advance_core(off, run, board, uid, who, ci);
            assert!(
                matches!(last, MoveResult::Landed { .. }),
                "a careful move must land in {room}, got {last:?}"
            );
        }
        last
    }

    /// THE HARD GATE, DRIVEN: a live daily descent plays today's beacon-seeded dungeon end to end —
    /// a careful line reaches the hoard + posts to the no-cheat board; the character earns XP; the
    /// run re-verifies by replay.
    #[test]
    fn a_careful_descent_wins_earns_and_ranks_on_the_no_cheat_board() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let who = player("player-winner");
        let (mut run, uid) = open_core(
            &off,
            &mut board,
            who,
            &resolve_todays_beacon(),
            Some(WARRIOR),
        )
        .expect("open today's beacon-seeded run");

        let result = drive_win(&mut off, &mut run, &mut board, uid, "winner");
        assert!(run.is_won(), "the careful line reached the hoard");
        assert_eq!(run.read_var("gold"), HOARD_GOLD, "the hoard is seized");
        assert!(!run.is_dead(), "a winner did not perish");
        // Earned XP: felled the warden (50) + seized the hoard (150).
        assert_eq!(
            run.character().xp(),
            dreggnet_offerings::daily_descent::XP_FELL_WARDEN
                + dreggnet_offerings::daily_descent::XP_SEIZE_HOARD,
            "XP earned from real landed outcomes"
        );
        // The terminal move ranked the WON run #1 on the no-cheat board.
        match result {
            MoveResult::Landed { view, rank, .. } => {
                assert!(view.ended && view.won);
                assert_eq!(rank, Some(1), "the first verified win ranks #1");
            }
            other => panic!("the winning seize must land + rank, got {other:?}"),
        }
        // Independent re-verification of the ranked entry (a stranger's re-run).
        let entry_ok = board
            .leaderboard(uid)
            .first()
            .map(|e| board.reverify_entry(uid, &e.completion_id).is_ok())
            .unwrap_or(false);
        assert!(entry_ok, "the ranked entry independently re-verifies");
    }

    /// A RECKLESS line DIES: a reckless opener burns HP to the brink, then a fall into the committed
    /// defeat passage ends the run in a real hardcore death — and it does NOT rank.
    #[test]
    fn a_reckless_descent_dies_and_does_not_rank() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let who = player("player-faller");
        let (mut run, uid) =
            open_core(&off, &mut board, who, &resolve_todays_beacon(), None).expect("open");
        assert!(!run.is_dead(), "alive at the start");

        // Reckless all-out blow: hp 50 → 20 (the warden still stands, the fall move unlocks).
        let r1 = advance_core(&mut off, &mut run, &mut board, uid, "faller", GATE_RECKLESS);
        assert!(
            matches!(r1, MoveResult::Landed { .. }),
            "the reckless opener commits"
        );
        assert!(run.read_var("hp") <= 20 && run.read_var("warden_hp") > 0);

        // Fall into the terminal defeat room — a real committed loss.
        let r2 = advance_core(&mut off, &mut run, &mut board, uid, "faller", GATE_FALL);
        assert!(matches!(r2, MoveResult::Landed { .. }), "the fall commits");
        assert_eq!(run.current_room().as_deref(), Some("downed"));

        // Close the defeat passage — the run ENDS in death.
        let r3 = advance_core(&mut off, &mut run, &mut board, uid, "faller", 0);
        match r3 {
            MoveResult::Landed { view, rank, .. } => {
                assert!(view.ended, "the run ended");
                assert!(view.dead, "the hardcore character PERISHED");
                assert!(!view.won, "a lost run did not reach the hoard");
                assert_eq!(rank, None, "a lost run does not rank");
            }
            other => panic!("the defeat close must land + not rank, got {other:?}"),
        }
        assert!(run.is_dead(), "hardcore death");
        assert!(
            run.character().attempt_resurrect().is_err(),
            "a hardcore death is final — resurrection refused"
        );
        // The board still has no ranked entry (the lost run was never submitted).
        assert!(
            board.leaderboard(uid).is_empty(),
            "nothing ranks from a loss"
        );
    }

    /// THE CHARACTER CARRIES: the SAME identity resumes its leveled character across a SIMULATED
    /// NEW DAY (a fresh offering/run over the same store); a different identity is fresh.
    #[test]
    fn the_character_carries_across_a_simulated_new_day() {
        let store = InMemoryCharacterStore::new();
        let mut off = DailyDescentOffering::new(store);
        let mut board = Registry::new();
        let alice = player("player-alice");

        // Day 1: a fresh Warrior wins, earns 200 XP, levels to 2, and the run END saves it.
        let (mut run, uid) = open_core(
            &off,
            &mut board,
            alice.clone(),
            &resolve_todays_beacon(),
            Some(WARRIOR),
        )
        .expect("open day 1");
        assert_eq!(
            run.character().level(),
            1,
            "a new adventurer begins at level 1"
        );
        drive_win(&mut off, &mut run, &mut board, uid, "alice");
        assert_eq!(run.character().xp(), 200, "earned the warden + the hoard");
        off.level_up(&run).expect("level 2 (xp 200 >= 100)");
        off.save(&run); // (advance_core already saved on the terminal move; this carries the level-up)
        assert!(off.store().has(&alice), "alice's character is persisted");

        // Day 2 (simulated): the SAME identity RESUMES the carried character.
        let (day2, _uid2) =
            open_core(&off, &mut board, alice, &resolve_todays_beacon(), None).expect("open day 2");
        assert_eq!(
            day2.character().level(),
            2,
            "carried level across the day boundary"
        );
        assert_eq!(day2.character().xp(), 200, "carried XP");
        assert_eq!(day2.character().class(), WARRIOR, "carried class");

        // A DIFFERENT identity is a fresh character.
        let (bob, _uid3) = open_core(
            &off,
            &mut board,
            player("player-bob"),
            &resolve_todays_beacon(),
            None,
        )
        .expect("open bob");
        assert_eq!(bob.character().level(), 1, "a different identity is fresh");
        assert_eq!(bob.character().xp(), 0);
    }

    /// THE NO-CHEAT BOARD refuses a FORGED run and accepts the honest one (non-vacuous).
    #[test]
    fn the_board_refuses_a_forged_run_and_accepts_the_honest_one() {
        let mut off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let (mut win, uid) = open_core(
            &off,
            &mut board,
            player("honest"),
            &resolve_todays_beacon(),
            None,
        )
        .expect("open");
        drive_win(&mut off, &mut win, &mut board, uid, "honest");
        assert!(win.is_won());

        // FORGE: swap the opening measured blow for a reckless one — the recorded state diverges.
        let honest = off
            .completion(&win, BOARD_AUTHOR, "honest")
            .expect("completion");
        let mut forged = honest.clone();
        if let Some(first) = forged.play.steps.first_mut() {
            first.choice_index = GATE_RECKLESS;
        }
        forged.player = "cheater".to_string();
        let out = board.submit(forged);
        assert!(
            matches!(
                out,
                Err(RejectReason::FailedVerification(_)) | Err(RejectReason::DidNotWin)
            ),
            "a forged run is refused by the no-cheat board, got {out:?}"
        );
        // Non-vacuous: the honest run is accepted on the same board.
        assert!(board.submit(honest).is_ok(), "the honest run is accepted");
    }

    /// BEACON-DAILY: today's dungeon is beacon-deterministic (same seed → same world), and a
    /// different day's verified round gives a DIFFERENT dungeon.
    #[test]
    fn todays_dungeon_is_beacon_deterministic_and_a_new_day_differs() {
        let today_seed = resolve_todays_beacon().seed().expect("today's seed");
        // Same seed → byte-identical world (determinism the leaderboard leans on).
        assert_eq!(
            daily_scene(&today_seed).source,
            daily_scene(&today_seed).source,
            "same beacon seed → same dungeon"
        );
        // A different day's beacon output → a different daily seed → a different world.
        let other_seed = procgen_dregg::daily_seed(&[0x5c; 32]);
        assert_ne!(today_seed.as_bytes(), other_seed.as_bytes());
        assert_ne!(
            daily_scene(&today_seed).source,
            daily_scene(&other_seed).source,
            "a different day's beacon gives a different dungeon"
        );
    }

    /// A FORGED beacon cannot open a day (fail-closed) — non-vacuous: the honest beacon opens.
    #[test]
    fn a_forged_beacon_cannot_open_a_day() {
        let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let mut sig = hex::decode(DRAND_QUICKNET_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND, sig);
        assert!(
            open_core(&off, &mut board, player("p"), &forged, None).is_err(),
            "a forged beacon must not open a day"
        );
        assert!(
            open_core(
                &off,
                &mut board,
                player("p"),
                &resolve_todays_beacon(),
                None
            )
            .is_ok(),
            "the honest beacon opens"
        );
    }

    /// The scene-source render helpers read the current room's ordered choice labels + prose
    /// straight out of the emitted DSL (the SAME order the executor indexes with).
    #[test]
    fn the_render_helpers_read_the_scene_source() {
        let seed = resolve_todays_beacon().seed().expect("seed");
        let day = daily_scene(&seed);

        // The gate room has the five warden choices in index order.
        let gate = room_choices(&day.source, "gate");
        assert_eq!(gate.len(), 5, "the gate offers five moves: {gate:?}");
        assert!(gate[GATE_MEASURED].to_lowercase().contains("measured"));
        assert!(gate[GATE_RECKLESS].to_lowercase().contains("reckless"));
        assert!(
            gate[GATE_HEAL].to_lowercase().contains("wound")
                || gate[GATE_HEAL].to_lowercase().contains("dressing")
        );
        assert!(gate[GATE_FALL].to_lowercase().contains("fall"));

        // The hoard room has exactly the one WIN move; the gate has readable prose.
        assert_eq!(room_choices(&day.source, "hoard").len(), 1);
        assert!(
            !room_prose(&day.source, "gate").trim().is_empty(),
            "the gate has prose"
        );

        // Eligibility decoration: at genesis (hp 50, warden up) the press-past move is locked.
        let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let run = off
            .open(player("look"), &resolve_todays_beacon())
            .expect("open");
        let opts = ballot(&run);
        let press = opts
            .iter()
            .find(|o| o.index == GATE_PRESS)
            .expect("press-past present");
        assert!(
            !press.enabled,
            "press-past is locked while the warden stands"
        );
        let measured = opts
            .iter()
            .find(|o| o.index == GATE_MEASURED)
            .expect("measured present");
        assert!(measured.enabled, "a measured blow is available at full HP");

        // The move buttons build (one row, five buttons for the gate).
        let rows = move_rows(42, &opts);
        assert!(!rows.is_empty(), "the ballot renders buttons");
    }

    /// The custom-id round-trips: `descent:move:<owner>:<idx>` parses back to (owner, idx).
    #[test]
    fn the_move_custom_id_round_trips() {
        let rows = move_rows(
            777,
            &[MoveOption {
                label: "Measured blow".into(),
                index: 0,
                enabled: true,
            }],
        );
        // Rebuild the id the button carries and parse it exactly as `handle_component` does.
        let id = format!("descent:move:{}:{}", 777, 0);
        let parts: Vec<&str> = id.split(':').collect();
        assert_eq!(parts.len(), 4);
        assert_eq!(parts[1], "move");
        assert_eq!(parts[2].parse::<u64>().unwrap(), 777);
        assert_eq!(parts[3].parse::<usize>().unwrap(), 0);
        assert!(!rows.is_empty());
    }
}
