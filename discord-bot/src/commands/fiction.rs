//! `/dungeon` — a whole Discord channel plays a shared, AI-narrated, on-chain dungeon.
//!
//! This is the [`attested_dm`] fiction engine surfaced as a **party game**: a channel opens a
//! session, the bot posts the room (gemma2 narrates it, the engine describes it) with a row of
//! **buttons for the candidate moves**, and every button press is a **ballot** — one write-once
//! vote per Discord user per round, attributed not to a nickname but to that user's derived
//! **dregg identity** (`cipherclerk::UserCipherclerk::derive(...).public_key_hex()`). When the
//! round closes, the **plurality winner** is played through [`GameSession::command`]: a legal
//! move lands as one verified, attested, on-chain turn (the receipt count grows); an illegal one
//! is refused in-band — the crowd decided, the world disposed, room unchanged, no receipt (the
//! anti-ghost tooth). `/dungeon verify` re-verifies the whole hash chain in-channel.
//!
//! The engine is the SOURCE OF TRUTH: the AI narrates, the world resolves, the chain remembers.
//! A jailbroken narration cannot open a locked door or mint an unearned item — only a move the
//! deterministic resolver admits ever changes the world.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use serenity::all::{
    ButtonStyle, CommandDataOptionValue, CommandInteraction, CommandOptionType,
    ComponentInteraction, Context, CreateActionRow, CreateButton, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateEmbedFooter, CreateInteractionResponse,
    CreateInteractionResponseMessage,
};

use attested_dm::{
    GameSession, GameStatus, GameWorld, Issue, PlayResult, WorldCell, bramble_keep, deepdark_mine,
    parse_world, starfall_spire, sunken_vault, validate,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;

/// The bot-branded teal (matches `embeds::DREGG_COLOR`).
const DUNGEON_COLOR: u32 = 0x7B2CBF;
/// The honest tagline that footers every dungeon surface.
const TAGLINE: &str = "the AI narrates · the world resolves · the chain remembers";

// ─────────────────────────────────────────────────────────────────────────────
// Embedded sample dungeons (authored in the `.dungeon` DSL) — compiled in so the
// bot always has them, no runtime path dependency. The four hand-written worlds
// come from the engine directly.
// ─────────────────────────────────────────────────────────────────────────────

const LANTERN_FEN: &str = include_str!("../../../attested-dm/dungeons/lantern_fen.dungeon");
const CLOCKWORK_ORCHARD: &str =
    include_str!("../../../attested-dm/dungeons/clockwork_orchard.dungeon");
const EMBER_OBSERVATORY: &str =
    include_str!("../../../attested-dm/dungeons/ember_observatory.dungeon");

/// The playable catalogue: `(slug, display name, one-line blurb)`.
const CATALOG: &[(&str, &str, &str)] = &[
    (
        "sunken-vault",
        "The Sunken Vault",
        "a drowned vault, a Warden, a heart to carry out",
    ),
    (
        "bramble-keep",
        "The Bramble Keep",
        "thorn-choked halls and a foe that bleeds you slow",
    ),
    (
        "starfall-spire",
        "The Starfall Spire",
        "an orrery of learned words and warded stairs",
    ),
    (
        "deepdark-mine",
        "The Deepdark Mine",
        "a lamp that burns down; the dark is absolute",
    ),
    (
        "lantern-fen",
        "The Lantern Fen",
        "a bog crossing lit one guttering lantern at a time",
    ),
    (
        "clockwork-orchard",
        "The Clockwork Orchard",
        "brass trees, a Keeper's trade, a heartspring",
    ),
    (
        "ember-observatory",
        "The Ember Observatory",
        "a cold dome and the spark to relight it",
    ),
];

/// Load the [`GameWorld`] for a catalogue slug (builtins built directly; samples parsed from
/// their embedded DSL source). `None` for an unknown slug.
fn load_world(slug: &str) -> Option<GameWorld> {
    match slug {
        "sunken-vault" => Some(sunken_vault()),
        "bramble-keep" => Some(bramble_keep()),
        "starfall-spire" => Some(starfall_spire()),
        "deepdark-mine" => Some(deepdark_mine()),
        // The samples parse fail-closed; a sound sample yields a world, else it is simply
        // absent from the catalogue at runtime (it never ships a broken world to the channel).
        "lantern-fen" => parse_playable(LANTERN_FEN),
        "clockwork-orchard" => parse_playable(CLOCKWORK_ORCHARD),
        "ember-observatory" => parse_playable(EMBER_OBSERVATORY),
        _ => None,
    }
}

/// The display name for a slug (falls back to the slug itself).
fn display_name(slug: &str) -> String {
    CATALOG
        .iter()
        .find(|(s, _, _)| *s == slug)
        .map(|(_, n, _)| n.to_string())
        .unwrap_or_else(|| slug.to_string())
}

// ─────────────────────────────────────────────────────────────────────────────
// The forge flow — parse + validate an authored dungeon, fail-closed.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a `/dungeon forge` source was refused.
#[derive(Clone, Debug)]
pub enum ForgeError {
    /// A syntactic / whole-file parse error, carrying its 1-based line and message.
    Parse { line: usize, message: String },
    /// The source parsed but the validator found blocking (`is_error`) issues — every one listed.
    Invalid(Vec<Issue>),
}

/// **Forge a playable world from `.dungeon` source, fail-closed.** Parses syntactically
/// ([`parse_world`]) then runs the semantic [`validate`] and refuses if ANY issue
/// [`Issue::is_error`]s — listing every blocking issue, not just the first. A returned world is
/// guaranteed sound enough to open a session over.
pub fn forge_world(src: &str) -> Result<GameWorld, ForgeError> {
    let world = parse_world(src).map_err(|e| ForgeError::Parse {
        line: e.line,
        message: e.message,
    })?;
    let errors: Vec<Issue> = validate(&world)
        .into_iter()
        .filter(Issue::is_error)
        .collect();
    if !errors.is_empty() {
        return Err(ForgeError::Invalid(errors));
    }
    Ok(world)
}

/// Parse a bundled sample only if it is fully playable (used at catalogue-load time).
fn parse_playable(src: &str) -> Option<GameWorld> {
    forge_world(src).ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// The round / ballot model — the write-once vote, the tally, the plurality winner.
// ─────────────────────────────────────────────────────────────────────────────

/// One candidate move on the ballot — its human label and the command it plays.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoteOption {
    /// The button label (e.g. `"go to The Cistern"`, `"take lantern"`, `"🔒 iron door"`).
    pub label: String,
    /// The engine command this option resolves to (e.g. `"go cistern"`, `"take lantern"`).
    pub command: String,
}

/// **A voting round** — the candidate moves and the write-once ballots cast against them. A voter
/// is a **derived dregg public key** (hex), never a Discord nickname: a ballot is attributable to
/// a real cryptographic identity.
#[derive(Clone, Debug, Default)]
pub struct Round {
    /// The round number (monotonic per session). A ballot for a stale round is rejected.
    pub round: u64,
    /// The candidate moves, in stable order (the index is the ballot's option id).
    pub options: Vec<VoteOption>,
    /// The ballots cast: voter public-key hex → chosen option index. **Write-once**: a second
    /// vote from the same key is refused (see [`Round::cast`]).
    pub ballots: HashMap<String, usize>,
}

/// The outcome of attempting to cast a ballot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BallotOutcome {
    /// The ballot was recorded (first vote from this voter this round).
    Recorded,
    /// The voter already voted this round — the ballot is refused (write-once).
    AlreadyVoted,
    /// The option index is out of range for this round.
    BadOption,
}

impl Round {
    /// A fresh round with the given number and candidate options.
    pub fn new(round: u64, options: Vec<VoteOption>) -> Round {
        Round {
            round,
            options,
            ballots: HashMap::new(),
        }
    }

    /// **Cast a write-once ballot.** `voter` is the voter's derived dregg public-key hex. The first
    /// vote is [`BallotOutcome::Recorded`]; any later vote from the same key is
    /// [`BallotOutcome::AlreadyVoted`] (the world does not let a voter stuff the box). An
    /// out-of-range option is [`BallotOutcome::BadOption`].
    pub fn cast(&mut self, voter: &str, option: usize) -> BallotOutcome {
        if option >= self.options.len() {
            return BallotOutcome::BadOption;
        }
        if self.ballots.contains_key(voter) {
            return BallotOutcome::AlreadyVoted;
        }
        self.ballots.insert(voter.to_string(), option);
        BallotOutcome::Recorded
    }

    /// The vote count per option index, in option order.
    pub fn tally(&self) -> Vec<usize> {
        let mut counts = vec![0usize; self.options.len()];
        for &idx in self.ballots.values() {
            if idx < counts.len() {
                counts[idx] += 1;
            }
        }
        counts
    }

    /// **The plurality winner's option index** — the option with the most votes, ties broken
    /// **deterministically toward the lowest option index** (documented, reproducible). `None`
    /// only when there are no options at all; a round with options but zero ballots still resolves
    /// to option `0` (the deterministic default the crowd left to the world).
    pub fn winner(&self) -> Option<usize> {
        if self.options.is_empty() {
            return None;
        }
        let counts = self.tally();
        // `max_by_key` over (count, reversed index) — highest count wins; on a tie the LOWEST
        // index wins (we negate the index so the smallest index has the largest key).
        (0..self.options.len()).max_by_key(|&i| (counts[i], std::cmp::Reverse(i)))
    }
}

/// **A per-channel play session** — the engine session, the world slug, the live round, and how
/// the last narration was produced (never misreported).
pub struct DungeonSession {
    /// The engine session (world + attested cap-bounded DM + hash-chain ledger).
    pub game: GameSession,
    /// The catalogue slug (or `"authored"` for a forged world) — for display.
    pub slug: String,
    /// The world's display name.
    pub name: String,
    /// The live voting round.
    pub round: Round,
    /// How the current room narration was produced (`gemma2:2b` or `scripted`).
    pub narrator: NarratorKind,
    /// The narration text posted for the current room — kept so a live vote re-render preserves
    /// the gemma2 prose (a vote never re-hits the network, so it never misreports the narrator).
    pub last_narration: String,
    /// The `.dungeon` SOURCE this session was forged from, if it was authored (vs a bundled world).
    /// Kept so `/dungeon publish` can save exactly what is being played.
    pub authored_source: Option<String>,
}

/// How a piece of narration was produced — surfaced honestly in the embed footer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NarratorKind {
    /// A real local `gemma2:2b` (ollama) narrated it.
    Gemma,
    /// ollama was unreachable; the engine's own scripted description stood in.
    Scripted,
}

impl NarratorKind {
    fn label(self) -> &'static str {
        match self {
            NarratorKind::Gemma => "narrator: gemma2:2b",
            NarratorKind::Scripted => "narrator: scripted",
        }
    }
}

/// The per-channel session store — keyed by Discord channel id. A module-global (behind a
/// `OnceLock<Mutex<…>>`) so it needs no change to `BotState`; every command locks it briefly and
/// never holds the guard across an `.await` (narration happens outside the lock).
fn sessions() -> &'static Mutex<HashMap<u64, DungeonSession>> {
    static SESSIONS: OnceLock<Mutex<HashMap<u64, DungeonSession>>> = OnceLock::new();
    SESSIONS.get_or_init(|| Mutex::new(HashMap::new()))
}

// ─────────────────────────────────────────────────────────────────────────────
// Candidate-move generation — the ballot for the current room.
// ─────────────────────────────────────────────────────────────────────────────

/// Build the candidate ballot for the current room: each exit (open, or 🔒 gated — a locked
/// exit stays on the ballot so the crowd CAN vote it and see the world refuse it), each item
/// present (take), each foe (attack), each NPC (talk), and always a `look`. Capped at 20 so the
/// components fit Discord's five rows of five.
fn round_options(map: &GameWorld, world: &WorldCell) -> Vec<VoteOption> {
    let here = &world.scene;
    let mut options: Vec<VoteOption> = Vec::new();

    if let Some(room) = map.rooms.get(here) {
        // Exits — labelled by destination name; 🔒 marks a gate not yet satisfied.
        for (dir, exit) in &room.exits {
            let dest = map
                .rooms
                .get(&exit.to_room)
                .map(|r| r.name.clone())
                .unwrap_or_else(|| exit.to_room.clone());
            let locked = exit
                .gate
                .as_ref()
                .map(|g| !gate_open(g, world))
                .unwrap_or(false);
            let label = if locked {
                format!("🔒 {dest} ({dir})")
            } else {
                format!("go {dest} ({dir})")
            };
            options.push(VoteOption {
                label: truncate(&label, 80),
                command: format!("go {}", exit.to_room),
            });
        }
        // Items present here.
        for item in map.items_here(here, world) {
            options.push(VoteOption {
                label: truncate(&format!("take {item}"), 80),
                command: format!("take {item}"),
            });
        }
    }
    // A one-shot hostile or an HP-bearing foe in this room.
    if let Some(h) = map.hostiles.get(here) {
        options.push(VoteOption {
            label: truncate(&format!("attack {}", h.name), 80),
            command: format!("attack {}", h.name),
        });
    }
    if let Some(c) = map.combat.get(here) {
        options.push(VoteOption {
            label: truncate(&format!("attack {}", c.name), 80),
            command: format!("attack {}", c.name),
        });
    }
    // NPCs standing here.
    for npc in map.npcs_here(here) {
        options.push(VoteOption {
            label: truncate(&format!("talk to {}", npc.name), 80),
            command: format!("talk to {}", npc.id),
        });
    }

    options.truncate(19);
    options.push(VoteOption {
        label: "look around".to_string(),
        command: "look".to_string(),
    });
    options
}

/// Whether a gate is currently satisfied (mirrors the engine's private `Gate::satisfied` via the
/// public world state — item held, or flag high enough). Used only to decorate the button label;
/// the resolver is still the sole authority over whether the move lands.
fn gate_open(gate: &attested_dm::game::Gate, world: &WorldCell) -> bool {
    use attested_dm::game::Gate;
    match gate {
        Gate::NeedsItem(i) => world.inventory.contains(i),
        Gate::NeedsFlag(k, v) => world.flags.get(k).copied().unwrap_or(0) >= *v,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// A `source` string option (a fenced ```code block``` works) — shared by check/forge/publish.
fn source_opt(required: bool) -> CreateCommandOption {
    CreateCommandOption::new(
        CommandOptionType::String,
        "source",
        "The .dungeon source (a fenced ```code block``` works too)",
    )
    .required(required)
}

/// An `attachment` option — attach a `.dungeon` file instead of pasting.
fn attachment_opt() -> CreateCommandOption {
    CreateCommandOption::new(
        CommandOptionType::Attachment,
        "attachment",
        "A .dungeon file to read instead of pasting source",
    )
    .required(false)
}

/// Register the `/dungeon` command (list / start / close / verify / check / forge / publish / library).
pub fn register() -> CreateCommand {
    // `world` is free-text: it accepts a bundled slug OR a published library name (see /list, /library).
    let start = CreateCommandOption::new(
        CommandOptionType::SubCommand,
        "start",
        "Open a shared dungeon in this channel (bundled slug or a published name)",
    )
    .add_sub_option(
        CreateCommandOption::new(
            CommandOptionType::String,
            "world",
            "Bundled slug or published name",
        )
        .required(false),
    );

    CreateCommand::new("dungeon")
        .description("Play — and author — a shared, AI-narrated, on-chain dungeon as a channel")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "List the bundled playable worlds",
        ))
        .add_option(start)
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "close",
            "Close the round: play the party's plurality choice, post the next round",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify the whole hash chain of this channel's playthrough",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "check",
                "LINT a .dungeon (no session): parse + validate, list every issue",
            )
            .add_sub_option(source_opt(false))
            .add_sub_option(attachment_opt()),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "forge",
                "Play a dungeon someone authored: paste its .dungeon source or attach a file",
            )
            .add_sub_option(source_opt(false))
            .add_sub_option(attachment_opt()),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "publish",
                "Save an authored world to the community library (source, attachment, or last-forged)",
            )
            .add_sub_option(
                CreateCommandOption::new(CommandOptionType::String, "name", "A library name for the world")
                    .required(true),
            )
            .add_sub_option(source_opt(false))
            .add_sub_option(attachment_opt()),
        )
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "library",
            "List community-published worlds",
        ))
}

/// Route `/dungeon` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "list" => handle_list(ctx, command).await,
        "start" => handle_start(ctx, command, state).await,
        "close" => handle_close(ctx, command).await,
        "verify" => handle_verify(ctx, command).await,
        "check" => handle_check(ctx, command).await,
        "forge" => handle_forge(ctx, command).await,
        "publish" => handle_publish(ctx, command, state).await,
        "library" => handle_library(ctx, command, state).await,
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

// ─── /dungeon list ───────────────────────────────────────────────────────────

async fn handle_list(ctx: &Context, command: &CommandInteraction) {
    let mut desc = String::from(
        "Pick one with `/dungeon start world:<slug>`. Author your own with `/dungeon check` + `/dungeon forge`, and see community worlds with `/dungeon library`.\n\n",
    );
    for (slug, name, blurb) in CATALOG {
        // Only advertise worlds that actually load (a sample that failed to parse is hidden).
        if load_world(slug).is_some() {
            desc.push_str(&format!("**{name}** — {blurb}\n`{slug}`\n\n"));
        }
    }
    let embed = base_embed("The bundled playable worlds")
        .description(desc)
        .footer(footer(NarratorKind::Scripted));
    respond(ctx, command, embed, vec![], true).await;
}

// ─── /dungeon start ──────────────────────────────────────────────────────────

async fn handle_start(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let requested =
        subcommand_string(command, "world").unwrap_or_else(|| "sunken-vault".to_string());

    // (1) A bundled world?
    if let Some(world) = load_world(&requested) {
        let name = display_name(&requested);
        open_session_and_post(ctx, command, state, world, requested, name).await;
        return;
    }

    // (2) A community-published world? Re-parse its stored SOURCE fail-closed (never a cached shape).
    match state.db.get_dungeon_world(&requested).await {
        Ok(Some(rec)) => match forge_world(&rec.source) {
            Ok(world) => {
                open_generic_and_post(
                    ctx,
                    command,
                    world,
                    rec.name.clone(),
                    rec.display_name.clone(),
                    Some(rec.source),
                )
                .await;
            }
            Err(_) => {
                let embed = error_embed(
                    "That published world no longer parses",
                    &format!(
                        "`{}` is in the library but its stored source fails to parse now. Nothing started.",
                        rec.name
                    ),
                );
                respond(ctx, command, embed, vec![], true).await;
            }
        },
        Ok(None) => {
            let embed = error_embed(
                "No such world",
                &format!(
                    "`{requested}` is neither a bundled world nor a published one. Try `/dungeon list` or `/dungeon library`."
                ),
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        Err(e) => {
            let embed = error_embed(
                "Library unavailable",
                &format!("Could not read the world library: {e}"),
            );
            respond(ctx, command, embed, vec![], true).await;
        }
    }
}

// ─── /dungeon check — the LINTER (no session) ─────────────────────────────────

async fn handle_check(ctx: &Context, command: &CommandInteraction) {
    let src = match gather_source(command).await {
        Ok(s) => s,
        Err(e) => {
            let embed = warn_embed("Nothing to check", &e);
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };
    // Stage 1 — PARSE (syntactic). Fail-closed, line-pinned.
    let world = match parse_world(&src) {
        Ok(w) => w,
        Err(e) => {
            let embed = error_embed(
                "❌ parse — the dungeon would not parse",
                &format!(
                    "`line {}: {}`\n\nFail-closed. No session started.",
                    e.line, e.message
                ),
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };
    // Stage 2 — VALIDATE (semantic). List EVERY issue with its severity.
    let issues = validate(&world);
    let error_count = issues.iter().filter(|i| i.is_error()).count();
    let obj = &world.objective;
    let obj_room = world
        .rooms
        .get(&obj.room)
        .map(|r| r.name.clone())
        .unwrap_or_else(|| obj.room.clone());
    if issues.is_empty() {
        let embed = base_embed("✓ validates clean")
            .description(format!(
                "**{} room(s)** · objective: reach **{}** holding the **{}**.\n\nPlay it now with `/dungeon forge` (same source).",
                world.rooms.len(),
                obj_room,
                obj.holding,
            ))
            .footer(footer(NarratorKind::Scripted));
        respond(ctx, command, embed, vec![], true).await;
    } else {
        let mut body = String::new();
        for issue in &issues {
            let mark = if issue.is_error() { "❌" } else { "⚠" };
            body.push_str(&format!("{mark} {}\n", issue.message));
        }
        let embed = if error_count > 0 {
            error_embed(
                &format!("❌ {error_count} blocking error(s) — not playable"),
                &truncate(&body, 3800),
            )
        } else {
            base_embed("⚠ warnings only — playable")
                .description(truncate(&body, 3800))
                .footer(footer(NarratorKind::Scripted))
        };
        respond(ctx, command, embed, vec![], true).await;
    }
}

// ─── /dungeon forge — check + OPEN a session ──────────────────────────────────

async fn handle_forge(ctx: &Context, command: &CommandInteraction) {
    let src = match gather_source(command).await {
        Ok(s) => s,
        Err(e) => {
            let embed = warn_embed("Nothing to forge", &e);
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };
    match forge_world(&src) {
        Err(ForgeError::Parse { line, message }) => {
            let embed = error_embed(
                "❌ parse — the dungeon would not parse",
                &format!(
                    "`line {line}: {message}`\n\nFail-closed — no session started. Fix the source and forge again."
                ),
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        Err(ForgeError::Invalid(issues)) => {
            let mut body =
                String::from("The validator refused this world (every blocking issue):\n\n");
            for issue in &issues {
                body.push_str(&format!("❌ {}\n", issue.message));
            }
            body.push_str(
                "\nFail-closed — no session started. `/dungeon check` shows warnings too.",
            );
            let embed = error_embed(
                "❌ validate — the dungeon is not sound",
                &truncate(&body, 3800),
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        Ok(world) => {
            let name =
                extract_world_name(&src).unwrap_or_else(|| "An authored dungeon".to_string());
            // A forged session remembers its SOURCE so `/dungeon publish` can save exactly this.
            open_generic_and_post(ctx, command, world, "authored".to_string(), name, Some(src))
                .await;
        }
    }
}

// ─── /dungeon publish — save to the community library ─────────────────────────

async fn handle_publish(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(name) = subcommand_string(command, "name") else {
        let embed = warn_embed(
            "Name required",
            "Give the world a library name: `/dungeon publish name:<name>`.",
        );
        respond(ctx, command, embed, vec![], true).await;
        return;
    };
    let name = slugify(&name);
    // Source: a supplied source/attachment wins; else the channel session's last-forged source.
    let src = match gather_source(command).await {
        Ok(s) => Some(s),
        Err(_) => {
            let channel = command.channel_id.get();
            sessions()
                .lock()
                .ok()
                .and_then(|store| store.get(&channel).and_then(|s| s.authored_source.clone()))
        }
    };
    let Some(src) = src else {
        let embed = warn_embed(
            "Nothing to publish",
            "Supply a `source:`/`attachment:`, or `/dungeon forge` a world in this channel first, then publish it.",
        );
        respond(ctx, command, embed, vec![], true).await;
        return;
    };
    // Only publish a SOUND world (parses + validates clean).
    let world = match forge_world(&src) {
        Ok(w) => w,
        Err(ForgeError::Parse { line, message }) => {
            let embed = error_embed(
                "❌ parse — cannot publish",
                &format!("`line {line}: {message}`"),
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
        Err(ForgeError::Invalid(issues)) => {
            let mut body = String::from("Only sound worlds are published. Blocking issues:\n\n");
            for issue in &issues {
                body.push_str(&format!("❌ {}\n", issue.message));
            }
            let embed = error_embed("❌ validate — cannot publish", &truncate(&body, 3600));
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };
    let display = extract_world_name(&src).unwrap_or_else(|| name.clone());
    let author_discord_id = command.user.id.get().to_string();
    // The author LABEL — the publisher's derived dregg public key hex (deterministic per user).
    // This records WHO published; it is NOT a signature over the source.
    let author_pubkey = UserCipherclerk::derive(
        &state.config.bot_secret,
        command.user.id.get(),
        state.federation_id_bytes,
    )
    .public_key_hex()
    .to_string();
    let rec = crate::db::DungeonWorldRecord {
        name: name.clone(),
        display_name: display.clone(),
        source: src,
        author_discord_id,
        author_pubkey: author_pubkey.clone(),
        validates_clean: true,
        room_count: world.rooms.len() as i64,
        created_at: now_secs(),
    };
    match state.db.publish_dungeon_world(&rec).await {
        Ok(()) => {
            let embed = base_embed(&format!("Published: {display}"))
                .description(format!(
                    "Saved to the community library as `{name}` — **{} room(s)**, validates clean.\n\nPlay it with `/dungeon start world:{name}`.",
                    world.rooms.len()
                ))
                .field("Author", format!("<@{}>", command.user.id.get()), true)
                .field("Author key (label)", format!("`{}…`", &author_pubkey[..author_pubkey.len().min(16)]), true)
                .footer(CreateEmbedFooter::new(
                    "provenance = author label (derived dregg pubkey), NOT a signature over the source",
                ));
            respond(ctx, command, embed, vec![], false).await;
        }
        Err(e) => {
            let embed = error_embed(
                "Could not publish",
                &format!("The library write failed: {e}"),
            );
            respond(ctx, command, embed, vec![], true).await;
        }
    }
}

// ─── /dungeon library — list community worlds ─────────────────────────────────

async fn handle_library(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    match state.db.list_dungeon_worlds().await {
        Ok(worlds) if worlds.is_empty() => {
            let embed = base_embed("The community library is empty")
                .description("No worlds published yet. Author one, `/dungeon check` it, then `/dungeon publish name:<name>`.")
                .footer(footer(NarratorKind::Scripted));
            respond(ctx, command, embed, vec![], true).await;
        }
        Ok(worlds) => {
            let mut desc = String::from("Play any with `/dungeon start world:<name>`.\n\n");
            for w in worlds.iter().take(20) {
                let clean = if w.validates_clean {
                    "✓ clean"
                } else {
                    "⚠ has issues"
                };
                desc.push_str(&format!(
                    "**{}** · `{}`\n{} room(s) · {} · by <@{}>\n\n",
                    w.display_name, w.name, w.room_count, clean, w.author_discord_id
                ));
            }
            let embed = base_embed("Community dungeon library")
                .description(truncate(&desc, 3800))
                .footer(CreateEmbedFooter::new(
                    "provenance = author label (derived dregg pubkey) · sources re-parsed on load",
                ));
            respond(ctx, command, embed, vec![], true).await;
        }
        Err(e) => {
            let embed = error_embed(
                "Library unavailable",
                &format!("Could not read the library: {e}"),
            );
            respond(ctx, command, embed, vec![], true).await;
        }
    }
}

// ─── /dungeon verify ─────────────────────────────────────────────────────────

async fn handle_verify(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    let (verified, count, name, break_msg) = {
        let store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get(&channel) {
            None => {
                drop(store);
                let embed = warn_embed(
                    "No session",
                    "This channel has no dungeon open. Start one with `/dungeon start`.",
                );
                respond(ctx, command, embed, vec![], true).await;
                return;
            }
            Some(sess) => {
                let count = sess.game.world().ledger.len();
                match sess.game.verify() {
                    Ok(()) => (true, count, sess.name.clone(), None),
                    Err(b) => (false, count, sess.name.clone(), Some(b.to_string())),
                }
            }
        }
    };
    let embed = if verified {
        base_embed(&format!("✓ {name} — chain re-verifies"))
            .description(format!(
                "**{count} verified turns** re-verify as one unbroken hash chain: every landed move is authentic, on-chain, and un-forged.\n\nReorder, mutation, or mid-history insertion would all break this walk."
            ))
            .footer(footer(NarratorKind::Scripted))
    } else {
        error_embed(
            &format!("✗ {name} — chain BREAKS"),
            &format!(
                "The ledger did not re-verify:\n`{}`",
                break_msg.unwrap_or_default()
            ),
        )
    };
    respond(ctx, command, embed, vec![], false).await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Session open + round posting.
// ─────────────────────────────────────────────────────────────────────────────

async fn open_session_and_post(
    ctx: &Context,
    command: &CommandInteraction,
    _state: &BotState,
    world: GameWorld,
    slug: String,
    name: String,
) {
    open_generic_and_post(ctx, command, world, slug, name, None).await;
}

/// Open a session for this channel over `world`, narrate the start room, and post the round-0
/// embed + ballot buttons. Replaces any existing session in the channel. `source` is the authored
/// `.dungeon` text if this world was forged (so `/dungeon publish` can save it), else `None`.
async fn open_generic_and_post(
    ctx: &Context,
    command: &CommandInteraction,
    world: GameWorld,
    slug: String,
    name: String,
    source: Option<String>,
) {
    let channel = command.channel_id.get();

    // Build the session + first round inside the lock, snapshot the render data, then narrate
    // OUTSIDE the lock (narration hits the network).
    let (room_name, room_desc, snap) = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        let game = GameSession::open(world);
        let options = round_options(game.map(), game.world());
        let room = game.current_room();
        let room_name = room
            .map(|r| r.name.clone())
            .unwrap_or_else(|| game.world().scene.clone());
        let room_desc = game.look();
        let round = Round::new(0, options);
        let snap = render_snapshot(&game, &name, &round);
        store.insert(
            channel,
            DungeonSession {
                game,
                slug,
                name,
                round,
                narrator: NarratorKind::Scripted,
                last_narration: String::new(),
                authored_source: source,
            },
        );
        (room_name, room_desc, snap)
    };

    let (narration, kind) = narrate_room(&room_name, &room_desc).await;
    // Record the narrator kind + prose for this posted room (honest footer, live-vote re-render).
    if let Ok(mut store) = sessions().lock() {
        if let Some(sess) = store.get_mut(&channel) {
            sess.narrator = kind;
            sess.last_narration = narration.clone();
        }
    }

    let embed = round_embed(&snap, &narration, kind);
    let rows = ballot_rows(&snap.options, snap.round);
    respond(ctx, command, embed, rows, false).await;
}

// ─────────────────────────────────────────────────────────────────────────────
// /dungeon close — resolve the plurality winner through the engine.
// ─────────────────────────────────────────────────────────────────────────────

async fn handle_close(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();

    // Resolve the round entirely inside the lock (pure, no network), snapshotting what to render
    // + what to narrate for the next room.
    enum CloseRender {
        NoSession,
        Empty, // a round with no options at all (shouldn't happen)
        Resolved {
            resolution: ResolvedRound,
            next_room_name: String,
            next_room_desc: String,
            next_snapshot: Option<RenderSnapshot>,
        },
    }

    let render = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get_mut(&channel) {
            None => CloseRender::NoSession,
            Some(sess) => match sess.round.winner() {
                None => CloseRender::Empty,
                Some(winner_idx) => {
                    let winner = sess.round.options[winner_idx].clone();
                    let tally = sess.round.tally();
                    let votes_for_winner = tally.get(winner_idx).copied().unwrap_or(0);
                    let total_ballots: usize = sess.round.ballots.len();
                    let round_no = sess.round.round;

                    // THE WORLD DISPOSES — play the crowd's choice through the engine.
                    let result = sess.game.command("party", &winner.command);
                    let status = sess.game.status();
                    let receipts = sess.game.world().ledger.len();

                    let resolution = ResolvedRound {
                        world_name: sess.name.clone(),
                        round_no,
                        winner_label: winner.label.clone(),
                        winner_command: winner.command.clone(),
                        votes_for_winner,
                        total_ballots,
                        was_tie: is_tie(&tally, winner_idx),
                        result: describe_result(&result),
                        status,
                        receipts,
                    };

                    // Open the next round unless the game ended.
                    if status == GameStatus::Playing {
                        let options = round_options(sess.game.map(), sess.game.world());
                        let next = Round::new(round_no + 1, options);
                        let room = sess.game.current_room();
                        let next_room_name = room
                            .map(|r| r.name.clone())
                            .unwrap_or_else(|| sess.game.world().scene.clone());
                        let next_room_desc = sess.game.look();
                        let snap = render_snapshot(&sess.game, &sess.name, &next);
                        sess.round = next;
                        CloseRender::Resolved {
                            resolution,
                            next_room_name,
                            next_room_desc,
                            next_snapshot: Some(snap),
                        }
                    } else {
                        CloseRender::Resolved {
                            resolution,
                            next_room_name: String::new(),
                            next_room_desc: String::new(),
                            next_snapshot: None,
                        }
                    }
                }
            },
        }
    };

    match render {
        CloseRender::NoSession => {
            let embed = warn_embed(
                "No session",
                "This channel has no dungeon open. Start one with `/dungeon start`.",
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        CloseRender::Empty => {
            let embed = warn_embed(
                "No moves",
                "There is nothing to vote on. Try `/dungeon verify` or start a new world.",
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        CloseRender::Resolved {
            resolution,
            next_room_name,
            next_room_desc,
            next_snapshot,
        } => {
            match next_snapshot {
                Some(snap) => {
                    // Narrate the NEW room outside the lock.
                    let (narration, kind) = narrate_room(&next_room_name, &next_room_desc).await;
                    if let Ok(mut store) = sessions().lock() {
                        if let Some(sess) = store.get_mut(&channel) {
                            sess.narrator = kind;
                            sess.last_narration = narration.clone();
                        }
                    }
                    let embed = resolution_then_round_embed(&resolution, &snap, &narration, kind);
                    let rows = ballot_rows(&snap.options, snap.round);
                    respond(ctx, command, embed, rows, false).await;
                }
                None => {
                    // Game over — no next round.
                    let embed = resolution_final_embed(&resolution);
                    respond(ctx, command, embed, vec![], false).await;
                }
            }
        }
    }
}

/// Whether the winning option `idx` shares its vote count with ANY OTHER option — i.e. the
/// deterministic lowest-index tie-break was exercised. (`idx` is the winner, always the lowest
/// index at the max count, so a *lower*-only scan would always be false; we must scan every other
/// option.)
fn is_tie(tally: &[usize], idx: usize) -> bool {
    let top = tally.get(idx).copied().unwrap_or(0);
    tally.iter().enumerate().any(|(j, &c)| j != idx && c == top)
}

/// A plain-language account of a play result for the channel.
struct ResultView {
    /// The headline line ("A verified turn landed." / "Refused — …").
    headline: String,
    /// The engine's own narration (or the refusal reason).
    body: String,
    /// Whether this changed the world (landed a receipt).
    landed: bool,
}

fn describe_result(result: &PlayResult) -> ResultView {
    match result {
        PlayResult::Landed { narration, .. } => ResultView {
            headline: "A verified turn landed on the chain.".to_string(),
            body: narration.clone(),
            landed: true,
        },
        PlayResult::Refused(reason) => ResultView {
            headline:
                "Refused — the crowd decided, the world disposed: room unchanged, no receipt."
                    .to_string(),
            body: reason.to_string(),
            landed: false,
        },
        PlayResult::DmRefused(e) => ResultView {
            headline: "Refused by the dungeon-master's tooth — no receipt.".to_string(),
            body: e.to_string(),
            landed: false,
        },
        PlayResult::Unparsed(msg) => ResultView {
            headline: "The dungeon-master could not read that move — nothing landed.".to_string(),
            body: msg.clone(),
            landed: false,
        },
    }
}

/// The resolved-round facts to render.
struct ResolvedRound {
    world_name: String,
    round_no: u64,
    winner_label: String,
    winner_command: String,
    votes_for_winner: usize,
    total_ballots: usize,
    was_tie: bool,
    result: ResultView,
    status: GameStatus,
    receipts: usize,
}

// ─────────────────────────────────────────────────────────────────────────────
// Component route — a button press is a ballot.
// ─────────────────────────────────────────────────────────────────────────────

/// Route a `fiction:` component press (a ballot). custom_id: `fiction:vote:<round>:<optionIdx>`.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.clone();
    let parts: Vec<&str> = id.split(':').collect();
    // fiction : vote : <round> : <idx>
    if parts.len() != 4 || parts[1] != "vote" {
        return;
    }
    let round: u64 = parts[2].parse().unwrap_or(u64::MAX);
    let option: usize = match parts[3].parse() {
        Ok(n) => n,
        Err(_) => return,
    };

    let channel = component.channel_id.get();
    let user_id = component.user.id.get();

    // The voter id is the user's DERIVED DREGG IDENTITY — its Ed25519 public key hex — NOT the
    // Discord nickname. Deterministic per (bot_secret, user id, federation).
    let voter =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes)
            .public_key_hex()
            .to_string();

    enum Reply {
        Ephemeral(String),
        Update {
            snapshot: RenderSnapshot,
            narration: String,
            kind: NarratorKind,
        },
    }

    let reply = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get_mut(&channel) {
            None => Reply::Ephemeral(
                "There is no dungeon open in this channel. Start one with `/dungeon start`."
                    .to_string(),
            ),
            Some(sess) => {
                if sess.round.round != round {
                    Reply::Ephemeral(
                        "That round already closed. Vote on the current round's buttons."
                            .to_string(),
                    )
                } else {
                    match sess.round.cast(&voter, option) {
                        BallotOutcome::AlreadyVoted => Reply::Ephemeral(format!(
                            "You already voted this round (as `{}…`). One ballot per identity.",
                            &voter[..voter.len().min(16)]
                        )),
                        BallotOutcome::BadOption => {
                            Reply::Ephemeral("That option is no longer on the ballot.".to_string())
                        }
                        BallotOutcome::Recorded => {
                            // Re-render the SAME message with the updated live tally + same buttons,
                            // preserving the already-posted narration + its (honest) narrator kind.
                            let snapshot = render_snapshot(&sess.game, &sess.name, &sess.round);
                            Reply::Update {
                                snapshot,
                                narration: sess.last_narration.clone(),
                                kind: sess.narrator,
                            }
                        }
                    }
                }
            }
        }
    };

    match reply {
        Reply::Ephemeral(text) => {
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(text)
                            .ephemeral(true),
                    ),
                )
                .await;
        }
        Reply::Update {
            snapshot,
            narration,
            kind,
        } => {
            // The room narration already lives on the message; a vote keeps the tally live by
            // re-rendering the SAME stored narration (no network, so it never misreports the
            // narrator kind). Fall back to the engine description only if nothing was stored.
            let narration = if narration.trim().is_empty() {
                snapshot.room_desc.clone()
            } else {
                narration
            };
            let embed = round_embed(&snapshot, &narration, kind);
            let rows = ballot_rows(&snapshot.options, snapshot.round);
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
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — embeds + ballot buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// A snapshot of everything needed to render a round embed + its buttons, taken while the lock is
/// held so the network narration can happen afterwards without the lock.
#[derive(Clone)]
pub struct RenderSnapshot {
    world_name: String,
    round: u64,
    room_name: String,
    room_desc: String,
    inventory: Vec<String>,
    objective: String,
    receipts: usize,
    options: Vec<VoteOption>,
    tally: Vec<usize>,
    ballots: usize,
}

fn render_snapshot(game: &GameSession, world_name: &str, round: &Round) -> RenderSnapshot {
    let world = game.world();
    let room = game.current_room();
    let room_name = room
        .map(|r| r.name.clone())
        .unwrap_or_else(|| world.scene.clone());
    let obj = &game.map().objective;
    let obj_room = game
        .map()
        .rooms
        .get(&obj.room)
        .map(|r| r.name.clone())
        .unwrap_or_else(|| obj.room.clone());
    RenderSnapshot {
        world_name: world_name.to_string(),
        round: round.round,
        room_name,
        room_desc: game.look(),
        inventory: world.inventory.iter().cloned().collect(),
        objective: format!("reach {obj_room} holding the {}", obj.holding),
        receipts: world.ledger.len(),
        options: round.options.clone(),
        tally: round.tally(),
        ballots: round.ballots.len(),
    }
}

/// The round embed: the room (narrated), inventory, objective, receipts, and the live ballot.
fn round_embed(snap: &RenderSnapshot, narration: &str, kind: NarratorKind) -> CreateEmbed {
    let inv = if snap.inventory.is_empty() {
        "— (empty)".to_string()
    } else {
        snap.inventory.join(", ")
    };
    let mut desc = String::new();
    desc.push_str(&truncate(narration, 1400));
    // Only append the engine's own room description when the narration is DIFFERENT from it (a
    // gemma2 narration adds flavor; a scripted fallback IS the description, so don't print twice).
    if narration.trim() != snap.room_desc.trim() {
        desc.push_str("\n\n");
        desc.push_str(&format!("_{}_", truncate(&snap.room_desc, 800)));
    }

    base_embed(&format!("{} — {}", snap.world_name, snap.room_name))
        .description(truncate(&desc, 4000))
        .field("Inventory", inv, false)
        .field("Objective", snap.objective.clone(), false)
        .field("Verified turns", snap.receipts.to_string(), true)
        .field(
            format!("Round {}", snap.round),
            format!("{} ballot(s) cast", snap.ballots),
            true,
        )
        .field(
            "The party's move — vote a button below",
            tally_block(&snap.options, &snap.tally),
            false,
        )
        .footer(footer(kind))
}

/// The combined "round resolved → next round" embed after `/dungeon close`.
fn resolution_then_round_embed(
    res: &ResolvedRound,
    snap: &RenderSnapshot,
    narration: &str,
    kind: NarratorKind,
) -> CreateEmbed {
    let mut embed = round_embed(snap, narration, kind);
    let tie = if res.was_tie {
        " (tie → lowest option index)"
    } else {
        ""
    };
    let outcome = format!(
        "**Round {} closed.** The party chose **{}** — `{}` with {}/{} ballot(s){}.\n\n{}\n> {}",
        res.round_no,
        res.winner_label,
        res.winner_command,
        res.votes_for_winner,
        res.total_ballots,
        tie,
        res.result.headline,
        truncate(&res.result.body, 600),
    );
    embed = embed.field("Last move", truncate(&outcome, 1000), false);
    embed
}

/// The final embed when the game ended (Won/Lost) on the closed round.
fn resolution_final_embed(res: &ResolvedRound) -> CreateEmbed {
    let (title, verdict) = match res.status {
        GameStatus::Won => (
            "🏆 The party WON",
            "The objective is met — the crowd carried it out together.",
        ),
        GameStatus::Lost => (
            "💀 The party fell",
            "A lose condition fired. The chain remembers how it ended.",
        ),
        GameStatus::Playing => ("The round closed", ""),
    };
    let tie = if res.was_tie {
        " (tie → lowest option index)"
    } else {
        ""
    };
    let body = format!(
        "**{}** — `{}` with {}/{} ballot(s){}.\n\n{}\n> {}\n\n{}\n\n**{} verified turns** on the chain. Run `/dungeon verify` to re-check them.",
        res.winner_label,
        res.winner_command,
        res.votes_for_winner,
        res.total_ballots,
        tie,
        res.result.headline,
        truncate(&res.result.body, 800),
        verdict,
        res.receipts,
    );
    base_embed(&format!("{} — {}", res.world_name, title))
        .description(truncate(&body, 4000))
        .footer(footer(NarratorKind::Scripted))
}

/// A monospace tally block: `go north  ▓▓▓ 3` per option.
fn tally_block(options: &[VoteOption], tally: &[usize]) -> String {
    if options.is_empty() {
        return "—".to_string();
    }
    let mut out = String::new();
    for (i, opt) in options.iter().enumerate() {
        let n = tally.get(i).copied().unwrap_or(0);
        let bar = "▓".repeat(n.min(12));
        out.push_str(&format!(
            "`{:>2}` {} {} {}\n",
            i,
            truncate(&opt.label, 32),
            bar,
            n
        ));
    }
    truncate(&out, 1000)
}

/// The ballot buttons for a round, chunked into Discord action rows of five (max five rows).
fn ballot_rows(options: &[VoteOption], round: u64) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for (row_idx, chunk) in options.chunks(5).enumerate() {
        if row_idx >= 5 {
            break;
        }
        let mut buttons: Vec<CreateButton> = Vec::new();
        for (i, opt) in chunk.iter().enumerate() {
            let idx = row_idx * 5 + i;
            let style = if opt.command == "look" {
                ButtonStyle::Secondary
            } else if opt.label.starts_with('🔒') {
                ButtonStyle::Danger
            } else {
                ButtonStyle::Primary
            };
            buttons.push(
                CreateButton::new(format!("fiction:vote:{round}:{idx}"))
                    .label(truncate(&opt.label, 78))
                    .style(style),
            );
        }
        rows.push(CreateActionRow::Buttons(buttons));
    }
    rows
}

fn base_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new().title(title).color(DUNGEON_COLOR)
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
// The narrator — a real local gemma2:2b via ollama, scripted fallback (honest).
// ─────────────────────────────────────────────────────────────────────────────

/// Narrate a room. Tries a real local `gemma2:2b` over ollama's `/api/generate`
/// (`stream:false` → `.response`); if ollama is unreachable OR returns nothing usable, falls back
/// to the engine's own scripted description and reports `NarratorKind::Scripted` — the narrator is
/// NEVER misreported.
async fn narrate_room(room_name: &str, room_desc: &str) -> (String, NarratorKind) {
    match gemma_narrate(room_name, room_desc).await {
        Some(text) if !text.trim().is_empty() => (sanitize(&text), NarratorKind::Gemma),
        _ => (room_desc.to_string(), NarratorKind::Scripted),
    }
}

/// One ollama `/api/generate` call (model `gemma2:2b`, `stream:false`). `None` on any failure
/// (unreachable, timeout, malformed) so the caller falls back to scripted.
async fn gemma_narrate(room_name: &str, room_desc: &str) -> Option<String> {
    let endpoint =
        std::env::var("OLLAMA_URL").unwrap_or_else(|_| "http://127.0.0.1:11434".to_string());
    let url = format!("{}/api/generate", endpoint.trim_end_matches('/'));
    let prompt = format!(
        "You are the dungeon master of a shared party dungeon crawl. In two vivid sentences, \
         set the scene for the party as they arrive. Do NOT use curly braces. \
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

/// Drop the two JSON-hostile bytes + control chars but KEEP `{`/`}` (so a would-be `{{` is not
/// laundered) — mirrors the engine's own field cleaning philosophy. The engine's attestation leg
/// is what actually refuses an injecting narration when a move lands; here we only tidy display.
fn sanitize(s: &str) -> String {
    s.chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control() || *c == '\n')
        .collect::<String>()
        .trim()
        .to_string()
}

// ─────────────────────────────────────────────────────────────────────────────
// Small helpers.
// ─────────────────────────────────────────────────────────────────────────────

/// The string value of a leaf option `name` inside the first subcommand.
fn subcommand_string(command: &CommandInteraction, name: &str) -> Option<String> {
    let sub = command.data.options.first()?;
    let opts = match &sub.value {
        CommandDataOptionValue::SubCommand(opts) => opts,
        _ => return None,
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

/// Strip a leading/trailing Markdown code fence (```…```), keeping the inner source. If the first
/// fenced line names a language (```dungeon), that line is dropped too.
fn strip_fence(raw: &str) -> String {
    let t = raw.trim();
    if let Some(rest) = t.strip_prefix("```") {
        let rest = rest.strip_suffix("```").unwrap_or(rest);
        // Drop the optional language tag on the first line.
        let mut lines = rest.lines();
        let first = lines.clone().next().unwrap_or("");
        if !first.contains(' ')
            && !first.contains(':')
            && first.len() < 16
            && !first.trim().is_empty()
        {
            // Looks like a lone language tag — drop it.
            lines.next();
            return lines.collect::<Vec<_>>().join("\n");
        }
        return rest.to_string();
    }
    t.to_string()
}

/// The cap on an authored source we will read (256 KiB) — a `.dungeon` is text and small.
const MAX_SRC_BYTES: usize = 256 * 1024;

/// The [`Attachment`] bound to leaf option `name` inside the first subcommand, resolved against
/// the interaction's `resolved.attachments`.
fn subcommand_attachment<'a>(
    command: &'a CommandInteraction,
    name: &str,
) -> Option<&'a serenity::all::Attachment> {
    let sub = command.data.options.first()?;
    let opts = match &sub.value {
        CommandDataOptionValue::SubCommand(opts) => opts,
        _ => return None,
    };
    let id = opts
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::Attachment(id) => Some(*id),
            _ => None,
        })?;
    command.data.resolved.attachments.get(&id)
}

/// **Gather the `.dungeon` source for check/forge/publish**, from an attachment (fetched, size-
/// capped, UTF-8-checked) or a pasted `source:` (fence-stripped). An attachment wins if both are
/// present. `Err` carries a user-facing message.
async fn gather_source(command: &CommandInteraction) -> Result<String, String> {
    if let Some(att) = subcommand_attachment(command, "attachment") {
        return fetch_attachment_source(att).await;
    }
    if let Some(s) = subcommand_string(command, "source") {
        let src = strip_fence(&s);
        if src.trim().is_empty() {
            return Err("The `source:` you gave is empty.".to_string());
        }
        return Ok(src);
    }
    Err("Provide a `.dungeon` source — paste it in `source:` (a ```code block``` works) or attach a `.dungeon` file.".to_string())
}

/// Fetch a `.dungeon` attachment's bytes and decode them, rejecting an over-cap or non-UTF-8 body.
async fn fetch_attachment_source(att: &serenity::all::Attachment) -> Result<String, String> {
    if att.size as usize > MAX_SRC_BYTES {
        return Err(format!(
            "That attachment is {} bytes — the cap is {} KiB.",
            att.size,
            MAX_SRC_BYTES / 1024
        ));
    }
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(20))
        .build()
        .map_err(|e| e.to_string())?;
    let resp = client
        .get(&att.url)
        .send()
        .await
        .map_err(|e| format!("Could not fetch the attachment: {e}"))?;
    let bytes = resp
        .bytes()
        .await
        .map_err(|e| format!("Could not read the attachment: {e}"))?;
    decode_source_bytes(&bytes)
}

/// Decode raw attachment bytes into a source string, enforcing the size cap and UTF-8. Pure (no
/// network) so the cap + non-UTF-8 rejection are unit-testable.
fn decode_source_bytes(bytes: &[u8]) -> Result<String, String> {
    if bytes.len() > MAX_SRC_BYTES {
        return Err(format!(
            "That file is {} bytes — the cap is {} KiB.",
            bytes.len(),
            MAX_SRC_BYTES / 1024
        ));
    }
    String::from_utf8(bytes.to_vec())
        .map_err(|_| "That file is not valid UTF-8 text — a .dungeon is plain text.".to_string())
}

/// Extract the world's display name from a `.dungeon` `name:` header line, if present.
fn extract_world_name(src: &str) -> Option<String> {
    for line in src.lines() {
        let l = line.trim();
        if let Some(rest) = l.strip_prefix("name:") {
            let name = rest.trim().trim_matches('"').trim();
            if !name.is_empty() {
                return Some(name.to_string());
            }
        }
    }
    None
}

/// A conservative library-name slug: lowercase, spaces/underscores → dashes, keep `[a-z0-9-]`.
fn slugify(s: &str) -> String {
    let mut out = String::new();
    for c in s.trim().to_lowercase().chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c);
        } else if c == ' ' || c == '_' || c == '-' {
            out.push('-');
        }
    }
    let trimmed = out.trim_matches('-').to_string();
    if trimmed.is_empty() {
        "world".to_string()
    } else {
        trimmed
    }
}

/// Unix seconds now.
fn now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// Truncate `s` to at most `max` characters (char-safe), appending `…` when cut.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the round/ballot logic, the engine seam, the forge flow, and the
// deterministic voter-id derivation. No live Discord required.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use attested_dm::GameStatus;

    fn opt(label: &str, command: &str) -> VoteOption {
        VoteOption {
            label: label.to_string(),
            command: command.to_string(),
        }
    }

    // ── (a) round / ballot logic ─────────────────────────────────────────────

    #[test]
    fn a_ballot_is_write_once_per_voter() {
        let mut round = Round::new(0, vec![opt("go north", "go north"), opt("look", "look")]);
        assert_eq!(round.cast("pubkey_alice", 0), BallotOutcome::Recorded);
        // A second vote from the SAME derived identity is refused (no box-stuffing).
        assert_eq!(round.cast("pubkey_alice", 1), BallotOutcome::AlreadyVoted);
        // The first vote stands.
        assert_eq!(round.tally(), vec![1, 0]);
        // A different identity votes freely.
        assert_eq!(round.cast("pubkey_bob", 1), BallotOutcome::Recorded);
        assert_eq!(round.tally(), vec![1, 1]);
    }

    #[test]
    fn a_bad_option_index_is_refused() {
        let mut round = Round::new(0, vec![opt("look", "look")]);
        assert_eq!(round.cast("pk", 9), BallotOutcome::BadOption);
        assert!(round.ballots.is_empty());
    }

    #[test]
    fn plurality_winner_is_the_most_voted() {
        let mut round = Round::new(
            0,
            vec![
                opt("north", "go n"),
                opt("south", "go s"),
                opt("look", "look"),
            ],
        );
        round.cast("a", 1);
        round.cast("b", 1);
        round.cast("c", 0);
        assert_eq!(round.winner(), Some(1)); // south, 2 votes
    }

    #[test]
    fn ties_break_toward_the_lowest_option_index() {
        let mut round = Round::new(0, vec![opt("north", "go n"), opt("south", "go s")]);
        round.cast("a", 0);
        round.cast("b", 1);
        // 1–1 tie → the LOWEST index (0) wins, deterministically.
        assert_eq!(round.winner(), Some(0));
        assert!(is_tie(&round.tally(), 0));
    }

    #[test]
    fn an_empty_round_defaults_to_option_zero() {
        let round = Round::new(0, vec![opt("look", "look")]);
        // No ballots at all → the world still resolves the default (index 0).
        assert_eq!(round.winner(), Some(0));
    }

    // ── (b) the engine seam: a voted legal move lands; a voted locked exit is refused ──

    #[test]
    fn a_voted_legal_move_lands_a_receipt() {
        // The Sunken Vault opens in the antechamber with the lantern present. A vote to TAKE the
        // lantern is a legal move: it lands as one verified turn and the receipt count grows.
        let mut game = GameSession::open(sunken_vault());
        let before = game.world().ledger.len();
        // The crowd's plurality command:
        let result = game.command("party", "take lantern");
        assert!(result.landed(), "take lantern is legal: {result:?}");
        assert_eq!(
            game.world().ledger.len(),
            before + 1,
            "a verified turn landed"
        );
        assert!(game.world().inventory.contains("lantern"));
    }

    #[test]
    fn a_voted_locked_exit_is_refused_world_unchanged_no_receipt() {
        // The stair down from the antechamber is dark/gated — locked until the lantern is held.
        // The crowd votes to descend it WITHOUT the lantern: the world disposes — refused, the
        // world is unchanged, and NO receipt lands (the anti-ghost tooth).
        let mut game = GameSession::open(sunken_vault());
        let before_scene = game.world().scene.clone();
        let before_receipts = game.world().ledger.len();
        // Try every exit from the start room that is currently gated; assert at least one refuses
        // and nothing lands.
        let start_room = game.current_room().cloned().expect("start room exists");
        let mut saw_refusal = false;
        for exit in start_room.exits.values() {
            if exit.gate.is_some() {
                let result = game.command("party", &format!("go {}", exit.to_room));
                assert!(
                    !result.landed(),
                    "a gated exit taken without its key must NOT land: {result:?}"
                );
                assert!(matches!(result, PlayResult::Refused(_)));
                saw_refusal = true;
            }
        }
        assert!(
            saw_refusal,
            "the vault's start room has a gated exit to exercise"
        );
        // World unchanged: same room, no new receipts.
        assert_eq!(
            game.world().scene,
            before_scene,
            "room unchanged after refusal"
        );
        assert_eq!(
            game.world().ledger.len(),
            before_receipts,
            "no receipt landed for the refused crowd choice"
        );
    }

    #[test]
    fn the_session_chain_reverifies_after_a_landed_move() {
        let mut game = GameSession::open(sunken_vault());
        game.command("party", "take lantern");
        assert!(game.verify().is_ok(), "the hash chain re-verifies");
        assert_eq!(game.status(), GameStatus::Playing);
    }

    // ── (c) the forge flow: broken refuses (no session), a sound sample starts ──

    #[test]
    fn forge_broken_dungeon_is_refused_and_starts_no_session() {
        let broken = include_str!("../../../attested-dm/dungeons/broken.dungeon");
        let result = forge_world(broken);
        assert!(
            result.is_err(),
            "the broken dungeon must be refused fail-closed"
        );
        match result {
            Err(ForgeError::Parse { line, .. }) => {
                assert!(line >= 1, "a parse error names a source line");
            }
            Err(ForgeError::Invalid(issues)) => {
                assert!(
                    !issues.is_empty(),
                    "every blocking validator issue is listed"
                );
                assert!(issues.iter().all(|i| i.is_error()));
            }
            Ok(_) => panic!("broken.dungeon must not produce a playable world"),
        }
    }

    #[test]
    fn forge_clockwork_orchard_starts_a_session() {
        let src = include_str!("../../../attested-dm/dungeons/clockwork_orchard.dungeon");
        let world = forge_world(src).expect("the clockwork orchard is a sound, playable world");
        // A session opens over the AUTHORED world and can be looked at + played.
        let game = GameSession::open(world);
        assert!(!game.look().is_empty());
        assert!(
            !round_options(game.map(), game.world()).is_empty(),
            "the room offers candidate moves"
        );
    }

    #[test]
    fn a_fenced_code_block_is_stripped_before_parsing() {
        let src = include_str!("../../../attested-dm/dungeons/clockwork_orchard.dungeon");
        let fenced = format!("```dungeon\n{src}\n```");
        let stripped = strip_fence(&fenced);
        assert!(
            forge_world(&stripped).is_ok(),
            "the fenced source forges the same world"
        );
    }

    // ── (d) the voter id IS the cipherclerk-derived public key (deterministic) ──

    #[test]
    fn the_voter_id_equals_the_derived_public_key_deterministically() {
        let bot_secret = [7u8; 32];
        let fed = [9u8; 32];
        let discord_user_id: u64 = 123456789012345678;
        let a = UserCipherclerk::derive(&bot_secret, discord_user_id, fed);
        let b = UserCipherclerk::derive(&bot_secret, discord_user_id, fed);
        // The derivation is deterministic: same user → same dregg public key (the ballot voter id).
        assert_eq!(a.public_key_hex(), b.public_key_hex());
        // And it is a real 32-byte Ed25519 public key (64 hex chars), not a nickname.
        assert_eq!(a.public_key_hex().len(), 64);
        // Different users → different voter ids.
        let c = UserCipherclerk::derive(&bot_secret, discord_user_id + 1, fed);
        assert_ne!(a.public_key_hex(), c.public_key_hex());
    }

    #[test]
    fn round_options_include_look_and_the_start_room_moves() {
        let game = GameSession::open(sunken_vault());
        let options = round_options(game.map(), game.world());
        assert!(
            options.iter().any(|o| o.command == "look"),
            "a look is always on the ballot"
        );
        assert!(
            options.len() >= 2,
            "the start room offers more than just a look"
        );
    }

    // ── (e) /dungeon check — the linter's two stages ─────────────────────────

    #[test]
    fn check_broken_dungeon_lists_validator_errors() {
        // `/dungeon check` runs parse (syntactic) then validate; the broken world parses
        // syntactically but the validator finds blocking errors (dangling exit, unreachable
        // objective, an item placed nowhere) — every one listed, no session.
        let broken = include_str!("../../../attested-dm/dungeons/broken.dungeon");
        let world = parse_world(broken).expect("broken.dungeon parses syntactically");
        let issues = validate(&world);
        let errors: Vec<_> = issues.iter().filter(|i| i.is_error()).collect();
        assert!(
            !errors.is_empty(),
            "the validator reports the broken world's blocking errors"
        );
    }

    #[test]
    fn check_clockwork_orchard_validates_clean() {
        let src = include_str!("../../../attested-dm/dungeons/clockwork_orchard.dungeon");
        let world = parse_world(src).expect("parses");
        let issues = validate(&world);
        assert!(
            issues.iter().all(|i| !i.is_error()),
            "the clockwork orchard validates with no blocking errors"
        );
    }

    #[test]
    fn a_syntax_broken_source_yields_a_line_pinned_parse_error() {
        // No `name:`, no `start:`, no rooms — a whole-file / syntactic failure.
        let garbage = "this is not a dungeon at all\njust some words\n";
        let err = parse_world(garbage).expect_err("garbage must not parse");
        // A DungeonError carries a line (0 = whole-file) and a message — fail-closed.
        assert!(
            !err.message.is_empty(),
            "the parse error names what is wrong"
        );
        // And forge starts no session (it is Err).
        assert!(forge_world(garbage).is_err());
    }

    // ── (f) the source-input plumbing: size cap + non-utf8 ───────────────────

    #[test]
    fn the_size_cap_rejects_an_oversized_source() {
        let big = vec![b'x'; MAX_SRC_BYTES + 1];
        assert!(
            decode_source_bytes(&big).is_err(),
            "an over-cap body is rejected"
        );
        let ok = vec![b'x'; 16];
        assert!(decode_source_bytes(&ok).is_ok(), "a small body decodes");
    }

    #[test]
    fn a_non_utf8_attachment_is_rejected() {
        // 0xFF is never valid UTF-8.
        let bytes = [0x66u8, 0x6f, 0x6f, 0xff, 0xfe];
        assert!(
            decode_source_bytes(&bytes).is_err(),
            "a non-utf8 body is rejected"
        );
    }

    #[test]
    fn extract_world_name_reads_the_header() {
        let src = "name: The Clockwork Orchard\nstart: gate\n";
        assert_eq!(
            extract_world_name(src).as_deref(),
            Some("The Clockwork Orchard")
        );
        assert_eq!(extract_world_name("no header here"), None);
    }

    #[test]
    fn slugify_makes_a_library_name() {
        assert_eq!(slugify("The Clockwork Orchard"), "the-clockwork-orchard");
        assert_eq!(slugify("  weird__name!!  "), "weird-name");
    }

    // ── (g) publish + library + start round-trip through the db ──────────────

    #[tokio::test]
    async fn publish_library_start_round_trip_through_the_db() {
        use crate::db::{Database, DungeonWorldRecord};

        let db = Database::connect("sqlite::memory:").await.unwrap();
        let src =
            include_str!("../../../attested-dm/dungeons/clockwork_orchard.dungeon").to_string();
        // A sound world (parses + validates clean) is what gets published.
        let world = forge_world(&src).expect("clockwork orchard is sound");
        let rec = DungeonWorldRecord {
            name: "clockwork-orchard".to_string(),
            display_name: extract_world_name(&src).unwrap(),
            source: src.clone(),
            author_discord_id: "424242".to_string(),
            author_pubkey: "deadbeef".to_string(),
            validates_clean: true,
            room_count: world.rooms.len() as i64,
            created_at: 1_700_000_000,
        };
        db.publish_dungeon_world(&rec).await.unwrap();

        // /dungeon library lists it.
        let listed = db.list_dungeon_worlds().await.unwrap();
        assert_eq!(listed.len(), 1);
        assert_eq!(listed[0].name, "clockwork-orchard");
        assert_eq!(listed[0].author_discord_id, "424242");

        // /dungeon start <name> loads it — re-parsed from the STORED SOURCE (never a cached shape).
        let fetched = db
            .get_dungeon_world("clockwork-orchard")
            .await
            .unwrap()
            .unwrap();
        assert_eq!(fetched.source, src, "the exact source round-trips");
        let reparsed =
            forge_world(&fetched.source).expect("the stored source re-parses into a world");
        let game = GameSession::open(reparsed);
        assert!(
            !game.look().is_empty(),
            "the re-loaded published world is playable"
        );

        // A missing name is absent.
        assert!(db.get_dungeon_world("no-such").await.unwrap().is_none());
    }
}
