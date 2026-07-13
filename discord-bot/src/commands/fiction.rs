//! `/dungeon` — a whole Discord channel plays a shared, AI-narrated dungeon on the
//! **REAL dregg executor**.
//!
//! The play path is [`dungeon_on_dregg`]'s committed universe — "The Warden's Keep" —
//! hosted on [`spween_dregg`]'s real [`WorldCell`]: the same `EmbeddedExecutor`, cell,
//! `CellProgram` and [`TurnReceipt`] the flagship substrate uses, NOT `attested-dm`'s
//! toy `WorldCell`/blake3 ledger. What the party pays for and plays is verifiable
//! substrate, not a LARP hash-chain.
//!
//! ## The ballot runs through the GENERIC collective adapter
//!
//! `/dungeon`'s write-once ballot is no longer a bespoke mechanism living here — it is the
//! generic [`crate::commands::offering`] adapter's **collective mode**, driven against the
//! real [`DungeonOffering`] (which is [`crate::commands::offering::DiscordOffering`], see
//! `crate::commands::dungeon_offering`). The offering session (world-cell + receipt chain)
//! and the live [`CollectiveRound`] both live in the adapter's per-offering
//! [`Store`](crate::commands::offering::Store); a button press records a write-once ballot in
//! that round (the mechanism [`cast_vote`](crate::commands::offering::cast_vote) wraps), and
//! `/dungeon close` resolves the plurality winner through
//! [`close_round`](crate::commands::offering::close_round) → `Offering::advance_collective`:
//! ONE real cap-bounded turn carrying the whole `CollectiveDecision` (the real electorate +
//! the tally + the "party" carrier). A legal move lands a real [`TurnReceipt`]; an illegal one
//! — a move the executor's installed `StateConstraint` refuses (a killing blow past the HP
//! floor, a second grab of a `WriteOnce` relic, an over-budget ward, a climb up a one-way
//! stair) — is a real refusal: the crowd decided, the world disposed, nothing commits, no
//! receipt (the anti-ghost tooth). `/dungeon verify` re-verifies the whole receipt chain by
//! REPLAY, through the offering's own `verify`.
//!
//! ## What stays HERE (the frontend the offering core deliberately does not carry)
//!
//! The bot owns the LIVE Discord surface — the rich ballot embeds, the per-run thread
//! orchestration, and the **paid narrator credit gate** ([`narrate_room_gated`], a real
//! Bedrock spend debited exactly once after a successful hosted call, with the free-tier
//! gemma/scripted fallback). That flow is intact and byte-identical; narration is invoked in
//! the async layer AFTER the round resolves and the next room's state is in hand. A thin
//! per-channel [`DungeonMeta`] map holds only what the collective adapter's `Live` does not:
//! how the current room was narrated, the last narration text (so a vote re-render never
//! re-hits the network), and the orchestrated-thread key to tear down at run end.
//!
//! The executor is the SOURCE OF TRUTH: the AI narrates, the world resolves, the chain
//! remembers. A jailbroken narration cannot open a gated stair or mint an unearned relic —
//! only a move the verified executor admits ever changes the world.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use serenity::all::{
    ButtonStyle, ChannelId, CommandInteraction, CommandOptionType, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateCommand, CreateCommandOption, CreateEmbed,
    CreateEmbedFooter, CreateInteractionResponse, CreateInteractionResponseMessage, CreateMessage,
    Permissions,
};

use dreggnet_offerings::dungeon::{DungeonOffering, KEEP_NAME, KEEP_OBJECTIVE};
use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::commands::offering::{
    Cast, CollectiveClose, CollectiveRound, Live, close_in, close_round, open_in, with_live,
};
use crate::orchestration::{OpenAuthority, SessionSpec};

/// The bot-branded teal (matches `embeds::DREGG_COLOR`).
const DUNGEON_COLOR: u32 = 0x7B2CBF;
/// The honest tagline that footers every dungeon surface.
const TAGLINE: &str = "the AI narrates · the world resolves · the chain remembers";

// ─────────────────────────────────────────────────────────────────────────────
// The REAL engine adapter — the ballot mechanism is now the GENERIC collective
// adapter's collective mode (`crate::commands::offering`), driven against the
// committed `DungeonOffering` (offering #0) over the SAME `spween-dregg` WorldCell.
// The adapter's per-offering `Store` owns open / the write-once `CollectiveRound` /
// advance_collective (one real crowd turn → Landed/Refused) / verify (replay). The bot
// owns only the payment gate (`narrate_room_gated`), the per-run thread flow, and the
// embeds — everything the offering core deliberately does not carry.
// ─────────────────────────────────────────────────────────────────────────────

/// The move outcome carried through the bot's rendering — the offering core's own
/// anti-ghost [`Outcome`]: a landed real `TurnReceipt`, or a real executor refusal.
type MoveOutcome = Outcome;

/// The stateless offering the bot drives (the free tier — the bot runs its OWN narrator
/// payment gate in [`narrate_room_gated`], so the offering's `price` is unused here). The
/// crowd turn's carrier is the offering's `collective_carrier()` default (`"party"`) — the
/// same session-level actor `/dungeon` has always attributed a plurality turn to.
fn offering() -> DungeonOffering {
    DungeonOffering::new()
}

// ─────────────────────────────────────────────────────────────────────────────
// The per-channel narration/thread metadata — everything the collective adapter's
// `Live<DungeonOffering>` (offering session + write-once round) does NOT carry.
// ─────────────────────────────────────────────────────────────────────────────

/// Per-channel narration + thread state kept beside the adapter's live session (which owns
/// the world-cell + the ballot). Nothing here touches the substrate — it is display state and
/// the orchestrated-thread teardown key.
struct DungeonMeta {
    /// How the current room narration was produced (bedrock / gemma / scripted).
    narrator: NarratorKind,
    /// The narration text posted for the current room — kept so a live vote re-render
    /// preserves the prose (a vote never re-hits the network, so it never misreports it).
    last_narration: String,
    /// If this run got its OWN orchestrated surface (a per-run thread), the session key to
    /// tear it down with at completion. `None` = the classic in-channel run.
    orchestrated_key: Option<String>,
}

/// The per-channel narration/thread metadata store, keyed by the channel the run plays in (a
/// spun thread's id when threaded, else the invoking channel) — the SAME key the adapter's
/// live session is stored under. A module-global so it needs no change to `BotState`; every
/// access locks briefly and never holds the guard across an `.await`.
fn meta() -> &'static Mutex<HashMap<u64, DungeonMeta>> {
    static META: OnceLock<Mutex<HashMap<u64, DungeonMeta>>> = OnceLock::new();
    META.get_or_init(|| Mutex::new(HashMap::new()))
}

// ─────────────────────────────────────────────────────────────────────────────
// The rendered ballot option (a UI value, NOT the ballot mechanism) — derived from
// the collective round's frozen candidate `Action`s.
// ─────────────────────────────────────────────────────────────────────────────

/// One candidate move as rendered on the ballot — its human label and the real scene choice
/// index it resolves to (the index [`WorldCell::apply_choice`] checks the gate case against,
/// i.e. the collective round option's [`dreggnet_offerings::Action::arg`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoteOption {
    /// The button label (e.g. `"Press on into the plundered hall"`, `"🔒 Trade blows"`).
    pub label: String,
    /// The scene choice index (within the current passage) this option applies.
    pub choice_index: usize,
}

/// The rendered ballot options for a live collective round — the round's frozen candidate
/// [`Action`](dreggnet_offerings::Action)s (the exact set the votes are cast against), with an
/// ineligible move decorated `🔒` (a decoration; the executor is the sole referee — a gated
/// illegal move still surfaces as a real refusal on close).
fn ballot_options(round: &CollectiveRound) -> Vec<VoteOption> {
    round
        .options
        .iter()
        .map(|a| {
            let label = if a.enabled {
                a.label.clone()
            } else {
                format!("🔒 {}", a.label)
            };
            VoteOption {
                label: truncate(&label, 80),
                choice_index: a.arg as usize,
            }
        })
        .collect()
}

/// How a piece of narration was produced — surfaced honestly in the embed footer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NarratorKind {
    /// A real hosted model (AWS Bedrock) narrated it — a PAID run that spent one $DREGG credit.
    Bedrock,
    /// A real local `gemma2:2b` (ollama) narrated it (the free tier).
    Gemma,
    /// ollama was unreachable; the scene's own scripted description stood in (the free tier).
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

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register the `/dungeon` command (list / start / close / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("dungeon")
        .description("Play a shared, AI-narrated dungeon on the REAL dregg executor, as a channel")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "Describe the hosted world and its executor-enforced rules",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "start",
            "Open the Warden's Keep in this channel (a real world-cell)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "close",
            "Close the round: apply the party's plurality choice as a real turn, post the next round",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify this channel's playthrough by replay (the real receipt chain)",
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
        "close" => handle_close(ctx, command, state).await,
        "verify" => handle_verify(ctx, command).await,
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
    let desc = format!(
        "**{KEEP_NAME}** — a dungeon hosted on the REAL dregg executor.\n\n\
         Every move is one cap-bounded turn the verified executor admits; every rule is an \
         executor-enforced `StateConstraint`, not app bookkeeping:\n\
         • **the gate-warden** — a killing blow past the HP floor is refused (`FieldGte`)\n\
         • **the reliquary crown** — the first hand to close on it holds it; a rival re-claim is refused (`WriteOnce`)\n\
         • **the collapsing stair** — descent is one-way; climbing back is refused (`Monotonic`)\n\
         • **the sealing ward** — will is a finite budget; an over-spend is refused (`FieldLteField`)\n\n\
         Open it with `/dungeon start`. Each button is a write-once ballot (one vote per \
         dregg identity); `/dungeon close` applies the party's plurality choice as a real \
         turn; `/dungeon verify` re-verifies the receipt chain by replay."
    );
    let embed = base_embed(&format!("{KEEP_NAME} — the hosted world"))
        .description(desc)
        .footer(footer(NarratorKind::Scripted));
    respond(ctx, command, embed, vec![], true).await;
}

// ─── /dungeon start ──────────────────────────────────────────────────────────

/// **The channel-spin decision (the documented seam, now wired).** Decide whether a
/// `/dungeon start` gets its OWN dedicated per-run surface, and build the orchestrator
/// [`SessionSpec`] for it — or fall back to the classic in-channel run.
///
/// The UX call: a **THREAD per run**, not a whole channel. A thread is lighter (it does
/// not clutter the guild sidebar), Discord archives it natively at teardown, and it keeps
/// the party in the invoking channel's context (the run is a branch of the conversation,
/// not a room elsewhere). A dedicated channel is only warranted for a semi-private run
/// with its own permission overwrites; a dungeon is a collective, watchable crawl.
///
/// It is **gated**, so `/dungeon` never breaks where the bot cannot spin threads:
/// - **not in a guild** (a DM) → `None` (there is nothing to thread under);
/// - **the bot lacks the thread perms** (`CREATE_PUBLIC_THREADS` + `SEND_MESSAGES_IN_THREADS`
///   in this channel) → `None`.
///
/// On `None`, [`handle_start`] plays the run in the invoking channel exactly as before.
/// The spec is keyed by the invoking channel id (one live dungeon thread per channel; a
/// re-open returns the existing session), self-service (the requester owns the run they
/// start — [`OpenAuthority::AdminOrSelfOwner`]), public (a run the channel can watch), and
/// queue-linked so messages in the thread become dregg turns.
fn plan_thread_spin(
    guild_id: Option<u64>,
    app_perms: Option<Permissions>,
    invoking_channel: u64,
    requester: u64,
    admin_id: Option<u64>,
) -> Option<SessionSpec> {
    let guild_id = guild_id?;
    let perms = app_perms?;
    if !(perms.contains(Permissions::CREATE_PUBLIC_THREADS)
        && perms.contains(Permissions::SEND_MESSAGES_IN_THREADS))
    {
        return None;
    }
    Some(
        SessionSpec::new(
            "dungeon",
            invoking_channel.to_string(),
            guild_id,
            requester,
            requester,
        )
        .admin(admin_id)
        .authority(OpenAuthority::AdminOrSelfOwner)
        .in_thread(invoking_channel)
        .public()
        .queue("dungeon-run")
        .announce("The dungeon awakens — the party plays here.")
        .topic("a dregg dungeon run"),
    )
}

async fn handle_start(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let invoking_channel = command.channel_id.get();

    // Fail-closed deploy GATE: validate the world-cell deploys BEFORE spinning any thread,
    // exactly as before. The live session is opened in the generic collective store below (a
    // deterministic redeploy under the same seed — genesis-only, local, no network). The
    // deterministic seed is the invoking channel id, so a re-open reproduces the same world
    // identity (what the replay verifier leans on).
    if let Err(e) = offering().open(SessionConfig::with_seed(invoking_channel)) {
        let embed = error_embed(
            "The Keep did not deploy",
            &format!("The world-cell deploy failed: {e}"),
        );
        respond(ctx, command, embed, vec![], true).await;
        return;
    }

    // THE CHANNEL-SPIN SEAM, WIRED. Spin a per-run thread iff gating allows; otherwise
    // (DM, or a perms-poor guild) `orchestrated_key` stays `None` and the run plays in
    // the invoking channel exactly as before. A spin failure mid-flight also falls back.
    let mut target_channel = invoking_channel;
    let mut orchestrated_key = None;
    if let Some(spec) = plan_thread_spin(
        command.guild_id.map(|g| g.get()),
        command.app_permissions,
        invoking_channel,
        command.user.id.get(),
        state.config.admin_discord_id,
    ) {
        match state
            .orchestrator
            .open(
                spec.clone(),
                &state.discord_caps,
                &state.event_bridge,
                &ctx.http,
            )
            .await
        {
            Ok(live) => {
                target_channel = live.channel_id;
                orchestrated_key = Some(spec.key());
            }
            Err(e) => {
                tracing::warn!(error = %e, "dungeon thread-spin failed; falling back in-channel");
            }
        }
    }

    // Open the LIVE session + its auto-opened write-once collective round in the GENERIC
    // collective store, keyed by `target_channel` (the thread id when spun, else the invoking
    // channel) and seeded by the invoking channel. A vote or `/dungeon close` from inside that
    // surface resolves against this session. `open_in` replaces any session already open.
    if let Err(e) = open_in(
        target_channel,
        offering(),
        SessionConfig::with_seed(invoking_channel),
    ) {
        let embed = error_embed(
            "The Keep did not deploy",
            &format!("The world-cell deploy failed: {e}"),
        );
        respond(ctx, command, embed, vec![], true).await;
        return;
    }
    meta().lock().unwrap_or_else(|e| e.into_inner()).insert(
        target_channel,
        DungeonMeta {
            narrator: NarratorKind::Scripted,
            last_narration: String::new(),
            orchestrated_key,
        },
    );

    // Snapshot the first room from the store, then narrate OUTSIDE any lock (narration hits
    // the network).
    let (room_name, room_desc, snap) = with_live::<DungeonOffering, _>(target_channel, |live| {
        let room_name = live
            .session
            .current_passage_name()
            .unwrap_or_else(|| "the threshold".to_string());
        let room_desc = live.session.current_prose();
        let snap = render_snapshot(live, KEEP_NAME);
        (room_name, room_desc, snap)
    })
    .expect("the session was just opened in the store");

    let (narration, kind) =
        narrate_room_gated(state, command.user.id.get(), &room_name, &room_desc).await;
    if let Ok(mut m) = meta().lock() {
        if let Some(d) = m.get_mut(&target_channel) {
            d.narrator = kind;
            d.last_narration = narration.clone();
        }
    }

    if target_channel != invoking_channel {
        // The run lives in its OWN thread: post the room + ballot there and point the
        // invoker to it (an ephemeral pointer, so the parent channel is not spammed).
        let posted = ChannelId::new(target_channel)
            .send_message(
                &ctx.http,
                CreateMessage::new()
                    .embed(round_embed(&snap, &narration, kind))
                    .components(ballot_rows(&snap.options, snap.round)),
            )
            .await;
        if posted.is_ok() {
            let ping = base_embed(&format!("{KEEP_NAME} — your run has its own thread"))
                .description(format!(
                    "The party plays in <#{target_channel}>. Vote the buttons there; run \
                     `/dungeon close` and `/dungeon verify` from inside the thread."
                ))
                .footer(footer(kind));
            respond(ctx, command, ping, vec![], true).await;
            return;
        }
        // Posting into the thread failed — re-key the (pre-turn) session under the invoking
        // channel and post the room here instead, so the run still happens. Re-keying a
        // store session is a close + reopen under the same seed (no turns have happened, so
        // the redeployed world is identical). The empty thread is left for the orchestrator's
        // own teardown paths.
        tracing::warn!("posting the dungeon room into the spun thread failed; playing in-channel");
        close_in::<DungeonOffering>(target_channel);
        let _ = open_in(
            invoking_channel,
            offering(),
            SessionConfig::with_seed(invoking_channel),
        );
        if let Ok(mut m) = meta().lock() {
            if let Some(mut moved) = m.remove(&target_channel) {
                moved.orchestrated_key = None;
                m.insert(invoking_channel, moved);
            }
        }
    }

    let embed = round_embed(&snap, &narration, kind);
    let rows = ballot_rows(&snap.options, snap.round);
    respond(ctx, command, embed, rows, false).await;
}

// ─── /dungeon close — resolve the plurality winner as a REAL turn ─────────────

async fn handle_close(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let channel = command.channel_id.get();

    enum CloseRender {
        NoSession,
        Empty,
        Resolved {
            resolution: ResolvedRound,
            next_room_name: String,
            next_room_desc: String,
            next_snapshot: Option<RenderSnapshot>,
            /// The orchestrated-surface key to tear down, iff this close ENDED the run
            /// AND the run had its own spun thread. `None` = keep the surface (round did
            /// not end) or an in-channel run (nothing to archive).
            teardown_key: Option<String>,
        },
    }

    // THE WORLD DISPOSES — resolve the crowd's plurality choice as ONE real cap-bounded crowd
    // turn THROUGH THE GENERIC COLLECTIVE ADAPTER (`close_round` → `advance_collective`): it
    // tallies the write-once ballots, drives the winning `Action`, records the whole
    // `CollectiveDecision` beside the committed step, and opens the next round.
    let render = match close_round::<DungeonOffering>(channel) {
        CollectiveClose::NoRound | CollectiveClose::NoSession => CloseRender::NoSession,
        CollectiveClose::Empty => CloseRender::Empty,
        CollectiveClose::Resolved(res) => {
            // Read the post-turn state (advance_collective already applied it + opened the
            // next round over the resulting state).
            let post = with_live::<DungeonOffering, _>(channel, |live| {
                let ended = live.session.is_ended();
                let receipts = live.session.receipts_len();
                if ended {
                    (ended, receipts, String::new(), String::new(), None)
                } else {
                    let next_room_name = live
                        .session
                        .current_passage_name()
                        .unwrap_or_else(|| "the dark".to_string());
                    let next_room_desc = live.session.current_prose();
                    let snap = render_snapshot(live, KEEP_NAME);
                    (ended, receipts, next_room_name, next_room_desc, Some(snap))
                }
            });
            match post {
                None => CloseRender::NoSession,
                Some((ended, receipts, next_room_name, next_room_desc, next_snapshot)) => {
                    let top = res.tally.winning_votes();
                    let resolution = ResolvedRound {
                        world_name: KEEP_NAME.to_string(),
                        round_no: res.round,
                        winner_label: res.winner.label.clone(),
                        votes_for_winner: res.tally.winning_votes() as usize,
                        total_ballots: res.tally.total_votes() as usize,
                        // The deterministic lowest-index tie-break was exercised iff the top
                        // count is shared by more than one option.
                        was_tie: res.tally.counts.iter().filter(|c| c.votes == top).count() > 1,
                        result: describe_outcome(&res.outcome),
                        ended,
                        receipts,
                    };
                    let teardown_key = if ended {
                        meta()
                            .lock()
                            .ok()
                            .and_then(|m| m.get(&channel).and_then(|d| d.orchestrated_key.clone()))
                    } else {
                        None
                    };
                    CloseRender::Resolved {
                        resolution,
                        next_room_name,
                        next_room_desc,
                        next_snapshot,
                        teardown_key,
                    }
                }
            }
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
                "There is nothing to vote on. Try `/dungeon verify` or `/dungeon start` a new run.",
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        CloseRender::Resolved {
            resolution,
            next_room_name,
            next_room_desc,
            next_snapshot,
            teardown_key,
        } => match next_snapshot {
            Some(snap) => {
                let (narration, kind) = narrate_room_gated(
                    state,
                    command.user.id.get(),
                    &next_room_name,
                    &next_room_desc,
                )
                .await;
                if let Ok(mut m) = meta().lock() {
                    if let Some(d) = m.get_mut(&channel) {
                        d.narrator = kind;
                        d.last_narration = narration.clone();
                    }
                }
                let embed = resolution_then_round_embed(&resolution, &snap, &narration, kind);
                let rows = ballot_rows(&snap.options, snap.round);
                respond(ctx, command, embed, rows, false).await;
            }
            None => {
                let embed = resolution_final_embed(&resolution);
                respond(ctx, command, embed, vec![], false).await;
                // The run ended: if it had its own spun thread, TEAR IT DOWN — archive the
                // surface, unlink the queue, and revoke every capability cell it held. A
                // best-effort archive: a failure here does not un-end the run.
                if let Some(key) = teardown_key {
                    if let Err(e) = state
                        .orchestrator
                        .teardown(&key, &state.discord_caps, &state.event_bridge, &ctx.http)
                        .await
                    {
                        tracing::warn!(error = %e, session = %key, "dungeon teardown failed");
                    }
                }
            }
        },
    }
}

/// A plain-language account of a move outcome for the channel.
struct ResultView {
    /// The headline line.
    headline: String,
    /// The engine's own narration (the executor refusal reason on a refusal).
    body: String,
    /// Whether this landed a real receipt.
    landed: bool,
}

fn describe_outcome(outcome: &MoveOutcome) -> ResultView {
    match outcome {
        MoveOutcome::Landed { .. } => ResultView {
            headline: "A verified turn landed on the chain.".to_string(),
            body:
                "The world resolved the party's choice — a real, committed, executor-admitted turn."
                    .to_string(),
            landed: true,
        },
        MoveOutcome::Refused(why) => ResultView {
            headline:
                "Refused — the crowd decided, the world disposed: room unchanged, no receipt."
                    .to_string(),
            body: format!("The executor refused the move: {why}"),
            landed: false,
        },
    }
}

/// The resolved-round facts to render.
struct ResolvedRound {
    world_name: String,
    round_no: u64,
    winner_label: String,
    votes_for_winner: usize,
    total_ballots: usize,
    was_tie: bool,
    result: ResultView,
    ended: bool,
    receipts: usize,
}

// ─── /dungeon verify ─────────────────────────────────────────────────────────

async fn handle_verify(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    enum VerifyOutcome {
        NoSession,
        Result {
            verified: bool,
            count: usize,
            name: String,
            break_msg: Option<String>,
        },
    }
    // Re-verify by replay THROUGH THE OFFERING CORE (`Offering::verify`), against the session
    // the collective adapter owns.
    let outcome = with_live::<DungeonOffering, _>(channel, |live| {
        let count = live.session.receipts_len();
        let report = live.offering.verify(&live.session);
        if report.verified {
            VerifyOutcome::Result {
                verified: true,
                count,
                name: KEEP_NAME.to_string(),
                break_msg: None,
            }
        } else {
            VerifyOutcome::Result {
                verified: false,
                count,
                name: KEEP_NAME.to_string(),
                break_msg: Some(report.detail),
            }
        }
    })
    .unwrap_or(VerifyOutcome::NoSession);

    let (verified, count, name, break_msg) = match outcome {
        VerifyOutcome::NoSession => {
            let embed = warn_embed(
                "No session",
                "This channel has no dungeon open. Start one with `/dungeon start`.",
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
        VerifyOutcome::Result {
            verified,
            count,
            name,
            break_msg,
        } => (verified, count, name, break_msg),
    };
    let embed = if verified {
        base_embed(&format!("✓ {name} — playthrough re-verifies by replay"))
            .description(format!(
                "**{count} verified turns** re-verify: a fresh, identically-seeded world-cell, re-driven through the recorded choices, reproduces exactly this committed state chain in passage order.\n\nA reordered, mutated, or forged (ineligible) choice would break replay — the executor refuses on re-drive, or the reproduced state diverges."
            ))
            .footer(footer(NarratorKind::Scripted))
    } else {
        error_embed(
            &format!("✗ {name} — replay BREAKS"),
            &format!(
                "The playthrough did not re-verify:\n`{}`",
                break_msg.unwrap_or_default()
            ),
        )
    };
    respond(ctx, command, embed, vec![], false).await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Component route — a button press is a ballot.
// ─────────────────────────────────────────────────────────────────────────────

/// The resolution of a `/dungeon` ballot press against the migrated generic collective round
/// — the sync core [`handle_component`] wraps (and the tests drive directly).
#[derive(Debug)]
enum BallotCast {
    /// No dungeon session is open in the channel.
    NoSession,
    /// The press is for a round that already closed (its buttons are stale).
    StaleRound,
    /// The voter already cast a write-once ballot this round.
    AlreadyVoted,
    /// The option is no longer on the ballot.
    BadOption,
    /// The write-once ballot was recorded; the re-render snapshot (with the updated tally).
    Recorded(RenderSnapshot),
}

/// **Cast one write-once `/dungeon` ballot** into the GENERIC collective round the adapter
/// owns (the mechanism [`cast_vote`](crate::commands::offering::cast_vote) wraps), by the
/// pressed option's *position*, guarding the stale-round case atomically on the store thread —
/// the round-guard the `/dungeon` UI has always had, which the round-number-agnostic by-arg
/// `cast_vote` helper does not carry. On a recorded ballot, snapshots the round for re-render.
fn cast_ballot(channel: u64, voter: DreggIdentity, round: u64, option: usize) -> BallotCast {
    with_live::<DungeonOffering, _>(channel, move |live| {
        let cast = match live.round.as_mut() {
            Some(r) if r.round == round => r.cast(&voter, option),
            // A session with no round, or a press for a round that already closed: stale.
            Some(_) | None => return BallotCast::StaleRound,
        };
        match cast {
            // Snapshot AFTER recording so the tally reflects this vote. The mutable borrow of
            // `live.round` ends with `cast` above, so re-borrowing `live` here is sound.
            Cast::Recorded => BallotCast::Recorded(render_snapshot(live, KEEP_NAME)),
            Cast::AlreadyVoted => BallotCast::AlreadyVoted,
            // BadOption, and the electorate/round variants unreachable for the open-crowd
            // dungeon, all present as "no longer on the ballot".
            _ => BallotCast::BadOption,
        }
    })
    .unwrap_or(BallotCast::NoSession)
}

/// Route a `fiction:` component press (a ballot). custom_id: `fiction:vote:<round>:<optionPos>`.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.clone();
    let parts: Vec<&str> = id.split(':').collect();
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
    let voter_hex =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes)
            .public_key_hex()
            .to_string();
    let voter_short = voter_hex[..voter_hex.len().min(16)].to_string();
    let voter = DreggIdentity(voter_hex);

    enum Reply {
        Ephemeral(String),
        Update {
            snapshot: RenderSnapshot,
            narration: String,
            kind: NarratorKind,
        },
    }

    let reply = match cast_ballot(channel, voter, round, option) {
        BallotCast::NoSession => Reply::Ephemeral(
            "There is no dungeon open in this channel. Start one with `/dungeon start`."
                .to_string(),
        ),
        BallotCast::StaleRound => Reply::Ephemeral(
            "That round already closed. Vote on the current round's buttons.".to_string(),
        ),
        BallotCast::AlreadyVoted => Reply::Ephemeral(format!(
            "You already voted this round (as `{voter_short}…`). One ballot per identity."
        )),
        BallotCast::BadOption => {
            Reply::Ephemeral("That option is no longer on the ballot.".to_string())
        }
        BallotCast::Recorded(snapshot) => {
            let (narration, kind) = meta()
                .lock()
                .ok()
                .and_then(|m| {
                    m.get(&channel)
                        .map(|d| (d.last_narration.clone(), d.narrator))
                })
                .unwrap_or_else(|| (String::new(), NarratorKind::Scripted));
            Reply::Update {
                snapshot,
                narration,
                kind,
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

/// A snapshot of everything needed to render a round embed + its buttons, taken while the
/// live session is held on the store thread so the network narration can happen afterwards.
#[derive(Clone, Debug)]
pub struct RenderSnapshot {
    world_name: String,
    round: u64,
    room_name: String,
    room_desc: String,
    state_line: String,
    objective: String,
    receipts: usize,
    options: Vec<VoteOption>,
    tally: Vec<usize>,
    ballots: usize,
}

/// Snapshot a channel's live session (the offering session + its collective round) for
/// rendering. Reads the migrated adapter's [`Live`]: the room prose/state from the offering
/// session, and the ballot options / per-option tally / ballot count from the collective round.
fn render_snapshot(live: &Live<DungeonOffering>, world_name: &str) -> RenderSnapshot {
    let room_name = live
        .session
        .current_passage_name()
        .unwrap_or_else(|| "the dark".to_string());
    let (round, options, tally, ballots) = match live.round.as_ref() {
        Some(r) => (r.round, ballot_options(r), r.counts(), r.ballots.len()),
        None => (0, Vec::new(), Vec::new(), 0),
    };
    RenderSnapshot {
        world_name: world_name.to_string(),
        round,
        room_name,
        room_desc: live.session.current_prose(),
        state_line: live.session.state_line(),
        objective: KEEP_OBJECTIVE.to_string(),
        receipts: live.session.receipts_len(),
        options,
        tally,
        ballots,
    }
}

/// The round embed: the room (narrated), state, objective, receipts, and the live ballot.
fn round_embed(snap: &RenderSnapshot, narration: &str, kind: NarratorKind) -> CreateEmbed {
    let mut desc = String::new();
    desc.push_str(&truncate(narration, 1400));
    if narration.trim() != snap.room_desc.trim() && !snap.room_desc.trim().is_empty() {
        desc.push_str("\n\n");
        desc.push_str(&format!("_{}_", truncate(&snap.room_desc, 800)));
    }

    base_embed(&format!("{} — {}", snap.world_name, snap.room_name))
        .description(truncate(&desc, 4000))
        .field("Party", snap.state_line.clone(), false)
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
        "**Round {} closed.** The party chose **{}** with {}/{} ballot(s){}.\n\n{}\n> {}",
        res.round_no,
        res.winner_label,
        res.votes_for_winner,
        res.total_ballots,
        tie,
        res.result.headline,
        truncate(&res.result.body, 600),
    );
    embed = embed.field("Last move", truncate(&outcome, 1000), false);
    embed
}

/// The final embed when the dungeon ended on the closed round.
fn resolution_final_embed(res: &ResolvedRound) -> CreateEmbed {
    let (title, verdict) = if res.ended && res.result.landed {
        (
            "🏆 The Keep is cleared",
            "The objective is met — the crowd carried it out together, one real turn at a time.",
        )
    } else {
        ("The round closed", "")
    };
    let tie = if res.was_tie {
        " (tie → lowest option index)"
    } else {
        ""
    };
    let body = format!(
        "**{}** with {}/{} ballot(s){}.\n\n{}\n> {}\n\n{}\n\n**{} verified turns** on the chain. Run `/dungeon verify` to re-check them by replay.",
        res.winner_label,
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

/// A monospace tally block: `Trade blows  ▓▓▓ 3` per option.
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
/// The custom-id is `fiction:vote:<round>:<optionPos>` — the wire `/dungeon` owns (routed to
/// [`handle_component`] in `main.rs`); the option position is what the ballot records.
fn ballot_rows(options: &[VoteOption], round: u64) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for (row_idx, chunk) in options.chunks(5).enumerate() {
        if row_idx >= 5 {
            break;
        }
        let mut buttons: Vec<CreateButton> = Vec::new();
        for (i, opt) in chunk.iter().enumerate() {
            let idx = row_idx * 5 + i;
            let style = if opt.label.starts_with('🔒') {
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
// The narrator — a real hosted Bedrock (paid), local gemma2:2b (free), scripted fallback.
// (KEPT byte-for-byte: the paid credit gate is the bot's frontend concern, deliberately not
// carried by the offering core.)
// ─────────────────────────────────────────────────────────────────────────────

/// **The credit gate.** Narrate a room for `discord_user_id`, spending a `$DREGG` run-credit
/// on a real Bedrock narration when the user has one, else falling back to the FREE tier
/// ([`narrate_room`], ollama/scripted). The paid backend is never free-ridden: a paid
/// narration debits exactly one credit AFTER a successful hosted call. The narrator kind is
/// reported honestly.
async fn narrate_room_gated(
    state: &BotState,
    discord_user_id: u64,
    room_name: &str,
    room_desc: &str,
) -> (String, NarratorKind) {
    let discord = discord_user_id.to_string();

    if !state.pay.can_run_paid(&discord) {
        return narrate_room(room_name, room_desc).await;
    }
    let Some(paid) = state.pay.paid.clone() else {
        return narrate_room(room_name, room_desc).await;
    };

    let system = "You are the dungeon master of a shared party dungeon crawl. In two vivid \
                  sentences, set the scene for the party as they arrive. Do NOT use curly braces."
        .to_string();
    let prompt = format!("Room: {room_name}. {room_desc}");

    // The hosted Bedrock client drives its OWN Tokio runtime with `block_on`, which must not run
    // on a bot async worker — do the paid narration on a blocking thread.
    let narration = tokio::task::spawn_blocking(move || paid.narrate(&system, &prompt))
        .await
        .ok()
        .and_then(|r| r.ok())
        .filter(|n| !n.text.trim().is_empty());

    match narration {
        Some(n) => {
            let _ = state.pay.debit_one(&discord);
            (sanitize(&n.text), NarratorKind::Bedrock)
        }
        None => narrate_room(room_name, room_desc).await,
    }
}

/// Narrate a room (the FREE tier). Tries a real local `gemma2:2b` over ollama; if unreachable
/// OR returns nothing usable, falls back to the scene's own scripted description and reports
/// `NarratorKind::Scripted` — the narrator is NEVER misreported.
async fn narrate_room(room_name: &str, room_desc: &str) -> (String, NarratorKind) {
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
/// laundered). The executor is what actually refuses an injecting move; here we only tidy display.
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
// Tests — the MIGRATED ballot path driven through the generic collective adapter: the
// write-once ballot (cast core `cast_ballot` + the render snapshot), the plurality winner
// resolved as ONE real cap-bounded `advance_collective` (a legal winner lands a real
// TurnReceipt; an illegal winner is a real executor refusal; verify_by_replay holds), the
// deterministic tie-break, and the deterministic voter-id. No live Discord required.
// (The canonical collective-mode proof on the real dungeon lives in
// `crate::commands::dungeon_offering`; here we exercise `/dungeon`'s own cast core + render.)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dungeon_on_dregg::{KP_PRESS_ON, KP_TRADE_BLOWS};

    /// A 64-hex-ish dregg identity from a short tag (an open-crowd voter — the dungeon does
    /// not restrict the electorate).
    fn ident(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// Open a fresh Keep session (world-cell + auto-opened write-once collective round) in the
    /// generic adapter's store, keyed by `channel` — the SAME path `/dungeon start` drives.
    fn open_channel(channel: u64, seed: u64) {
        close_in::<DungeonOffering>(channel);
        open_in(channel, offering(), SessionConfig::with_seed(seed))
            .expect("the Keep opens on a real world-cell");
    }

    /// The live collective round's number.
    fn current_round(channel: u64) -> u64 {
        with_live::<DungeonOffering, _>(channel, |l| {
            l.round.as_ref().map(|r| r.round).unwrap_or(u64::MAX)
        })
        .expect("a session is open")
    }

    /// The ballot position carrying scene choice `arg` in the live round.
    fn position_of_arg(channel: u64, arg: i64) -> usize {
        with_live::<DungeonOffering, _>(channel, move |l| {
            l.round
                .as_ref()
                .expect("a round is open")
                .options
                .iter()
                .position(|a| a.arg == arg)
                .expect("the arg is on the ballot")
        })
        .expect("a session is open")
    }

    // ── the write-once ballot through the collective adapter ─────────────────

    /// A ballot is write-once per derived identity, and the render snapshot reflects the tally
    /// — driven through the migrated `cast_ballot` core (the generic `CollectiveRound::cast`).
    #[test]
    fn a_ballot_is_write_once_through_the_collective_adapter() {
        let channel = 771_001;
        open_channel(channel, 7);
        let pos = position_of_arg(channel, KP_PRESS_ON as i64);

        match cast_ballot(channel, ident("a"), 0, pos) {
            BallotCast::Recorded(snap) => {
                assert_eq!(snap.tally[pos], 1, "the first ballot is tallied");
                assert_eq!(snap.ballots, 1);
            }
            other => panic!("the first vote records, got {other:?}"),
        }
        // The same identity's second ballot this round is refused (write-once).
        assert!(
            matches!(
                cast_ballot(channel, ident("a"), 0, pos),
                BallotCast::AlreadyVoted
            ),
            "one write-once ballot per identity"
        );
        // A second identity records.
        match cast_ballot(channel, ident("b"), 0, pos) {
            BallotCast::Recorded(snap) => {
                assert_eq!(snap.tally[pos], 2);
                assert_eq!(snap.ballots, 2);
            }
            other => panic!("a second voter records, got {other:?}"),
        }
        // A press for a round that already closed (a stale button) is rejected.
        assert!(
            matches!(
                cast_ballot(channel, ident("c"), 99, pos),
                BallotCast::StaleRound
            ),
            "a stale-round press is rejected"
        );
        // No session → NoSession.
        close_in::<DungeonOffering>(channel);
        assert!(matches!(
            cast_ballot(channel, ident("d"), 0, pos),
            BallotCast::NoSession
        ));
    }

    // ── the plurality winner as a REAL cap-bounded crowd turn ─────────────────

    /// A voted LEGAL move lands a REAL receipt — the ballot winner is resolved through
    /// `close_round` → `advance_collective` as one cap-bounded turn on the real executor, the
    /// receipt count grows, and the whole playthrough re-verifies by replay.
    #[test]
    fn a_voted_legal_move_lands_a_real_receipt_through_the_adapter() {
        let channel = 771_002;
        open_channel(channel, 7);
        let pos = position_of_arg(channel, KP_PRESS_ON as i64);
        assert!(matches!(
            cast_ballot(channel, ident("a"), 0, pos),
            BallotCast::Recorded(_)
        ));

        match close_round::<DungeonOffering>(channel) {
            CollectiveClose::Resolved(r) => {
                assert_eq!(r.tally.winner, KP_PRESS_ON as i64, "press-on won");
                match r.outcome {
                    Outcome::Landed { receipt, ended } => {
                        assert!(!ended, "pressing on does not end the Keep");
                        assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
                    }
                    other => panic!("a legal winner must land a real receipt, got {other:?}"),
                }
            }
            _ => panic!("a plurality round must resolve, got a non-resolved close"),
        }

        let (receipts, verified, room) = with_live::<DungeonOffering, _>(channel, |l| {
            (
                l.session.receipts_len(),
                l.offering.verify(&l.session).verified,
                l.session.current_passage_name(),
            )
        })
        .unwrap();
        assert_eq!(receipts, 2, "genesis + the crowd's committed turn");
        assert!(verified, "the honest playthrough re-verifies by replay");
        assert_eq!(room.as_deref(), Some("hall"), "the world advanced");
        close_in::<DungeonOffering>(channel);
    }

    /// A voted ILLEGAL move is a REAL executor refusal — world unchanged, no receipt (the
    /// anti-ghost tooth). Two survivable blows land; the killing blow past the HP floor
    /// (`FieldGte`) is refused on close, and the honest chain still re-verifies.
    #[test]
    fn a_voted_illegal_move_is_a_real_executor_refusal_no_receipt_through_the_adapter() {
        let channel = 771_003;
        open_channel(channel, 8);

        // Two survivable trade-blows (hp 50 → 30 → 10), each a real committed crowd turn.
        for i in 0..2u64 {
            let r = current_round(channel);
            let pos = position_of_arg(channel, KP_TRADE_BLOWS as i64);
            assert!(matches!(
                cast_ballot(channel, ident(&format!("v{i}")), r, pos),
                BallotCast::Recorded(_)
            ));
            match close_round::<DungeonOffering>(channel) {
                CollectiveClose::Resolved(res) => assert!(
                    matches!(res.outcome, Outcome::Landed { ended: false, .. }),
                    "a survivable blow lands"
                ),
                _ => panic!("a survivable blow must resolve and land"),
            }
        }
        let (hp, receipts_before) = with_live::<DungeonOffering, _>(channel, |l| {
            (l.session.read_var("hp"), l.session.receipts_len())
        })
        .unwrap();
        assert_eq!(hp, 10, "two blows dropped hp to 10");

        // The crowd votes the now-locked killing blow anyway — the REAL executor refuses.
        let r = current_round(channel);
        let pos = position_of_arg(channel, KP_TRADE_BLOWS as i64);
        assert!(matches!(
            cast_ballot(channel, ident("killer"), r, pos),
            BallotCast::Recorded(_)
        ));
        match close_round::<DungeonOffering>(channel) {
            CollectiveClose::Resolved(res) => assert!(
                matches!(res.outcome, Outcome::Refused(_)),
                "a killing blow is a real executor refusal"
            ),
            _ => panic!("the killing blow round must resolve to a refusal"),
        }

        let (receipts_after, hp_after, room, verified) =
            with_live::<DungeonOffering, _>(channel, |l| {
                (
                    l.session.receipts_len(),
                    l.session.read_var("hp"),
                    l.session.current_passage_name(),
                    l.offering.verify(&l.session).verified,
                )
            })
            .unwrap();
        assert_eq!(
            receipts_after, receipts_before,
            "anti-ghost: no receipt landed for the refused blow"
        );
        assert_eq!(hp_after, 10, "hp unchanged after the refusal");
        assert_eq!(
            room.as_deref(),
            Some("gatehall"),
            "still in the gatehall — the world did not move"
        );
        assert!(verified, "the honest prefix re-verifies after the refusal");
        close_in::<DungeonOffering>(channel);
    }

    /// The deterministic lowest-index tie-break, exercised through the real adapter: two
    /// voters split one ballot each across the two lowest options → the lowest index wins.
    #[test]
    fn a_tie_breaks_toward_the_lowest_option_through_the_adapter() {
        let channel = 771_004;
        open_channel(channel, 7);
        let (arg0, arg1) = with_live::<DungeonOffering, _>(channel, |l| {
            let opts = &l.round.as_ref().unwrap().options;
            (opts[0].arg, opts[1].arg)
        })
        .unwrap();
        let p0 = position_of_arg(channel, arg0);
        let p1 = position_of_arg(channel, arg1);

        assert!(matches!(
            cast_ballot(channel, ident("a"), 0, p1),
            BallotCast::Recorded(_)
        ));
        assert!(matches!(
            cast_ballot(channel, ident("b"), 0, p0),
            BallotCast::Recorded(_)
        ));

        match close_round::<DungeonOffering>(channel) {
            CollectiveClose::Resolved(r) => {
                assert_eq!(
                    r.tally.winner, arg0,
                    "a tie breaks toward the lowest option index"
                );
                let top = r.tally.winning_votes();
                assert!(
                    r.tally.counts.iter().filter(|c| c.votes == top).count() > 1,
                    "the tie-break was exercised (the top count is shared)"
                );
            }
            _ => panic!("the round must resolve"),
        }
        close_in::<DungeonOffering>(channel);
    }

    /// A full legal sequence re-verifies through the offering's own `verify` (replay).
    #[test]
    fn the_playthrough_reverifies_through_the_adapter() {
        let channel = 771_006;
        open_channel(channel, 9);

        // press on into the hall
        let r = current_round(channel);
        let pos = position_of_arg(channel, KP_PRESS_ON as i64);
        assert!(matches!(
            cast_ballot(channel, ident("a"), r, pos),
            BallotCast::Recorded(_)
        ));
        assert!(
            matches!(close_round::<DungeonOffering>(channel), CollectiveClose::Resolved(res) if res.outcome.landed())
        );

        // hall: claim red (choice 0)
        let r = current_round(channel);
        let pos = position_of_arg(channel, 0);
        assert!(matches!(
            cast_ballot(channel, ident("b"), r, pos),
            BallotCast::Recorded(_)
        ));
        assert!(
            matches!(close_round::<DungeonOffering>(channel), CollectiveClose::Resolved(res) if res.outcome.landed())
        );

        let verified =
            with_live::<DungeonOffering, _>(channel, |l| l.offering.verify(&l.session).verified)
                .unwrap();
        assert!(verified, "the legal playthrough re-verifies");
        close_in::<DungeonOffering>(channel);
    }

    // ── the fiction render surface over the migrated round ────────────────────

    /// The render snapshot + ballot rows reflect the live collective round: the gatehall's
    /// candidate moves, a zero tally before any vote, and the ungated press-on move unlocked.
    #[test]
    fn render_snapshot_reflects_the_live_round() {
        let channel = 771_005;
        open_channel(channel, 3);
        let snap =
            with_live::<DungeonOffering, _>(channel, |l| render_snapshot(l, KEEP_NAME)).unwrap();
        assert!(
            snap.options.len() >= 2,
            "the gatehall offers more than one candidate move"
        );
        assert_eq!(snap.round, 0);
        assert_eq!(snap.receipts, 1, "genesis only, before any turn");
        let press = snap
            .options
            .iter()
            .find(|o| o.choice_index == KP_PRESS_ON)
            .expect("press-on present");
        assert!(
            !press.label.starts_with('🔒'),
            "an ungated move is not locked"
        );
        assert!(snap.tally.iter().all(|&c| c == 0), "no ballots yet");
        assert!(!ballot_rows(&snap.options, snap.round).is_empty());
        close_in::<DungeonOffering>(channel);
    }

    // ── the voter id IS the cipherclerk-derived public key (deterministic) ─────

    #[test]
    fn the_voter_id_equals_the_derived_public_key_deterministically() {
        let bot_secret = [7u8; 32];
        let fed = [9u8; 32];
        let discord_user_id: u64 = 123456789012345678;
        let a = UserCipherclerk::derive(&bot_secret, discord_user_id, fed);
        let b = UserCipherclerk::derive(&bot_secret, discord_user_id, fed);
        assert_eq!(a.public_key_hex(), b.public_key_hex());
        assert_eq!(a.public_key_hex().len(), 64);
        let c = UserCipherclerk::derive(&bot_secret, discord_user_id + 1, fed);
        assert_ne!(a.public_key_hex(), c.public_key_hex());
    }

    // ── the channel-spin decision (the wired seam), driven purely ─────────────

    /// The channel-spin gate: a guild + the bot's thread perms spins a per-run THREAD
    /// with the right `SessionSpec` shape; a DM or a perms-poor guild falls back to the
    /// in-channel run (the fallback path the live `/dungeon` leans on).
    #[test]
    fn plan_thread_spin_gates_on_guild_and_perms() {
        use crate::orchestration::SurfaceKind;
        let full = Permissions::CREATE_PUBLIC_THREADS | Permissions::SEND_MESSAGES_IN_THREADS;

        // A guild + the thread perms → a thread SessionSpec of the right shape.
        let spec = plan_thread_spin(Some(42), Some(full), 555, 999, Some(7))
            .expect("a perms-holding guild spins a per-run thread");
        assert_eq!(spec.offering, "dungeon");
        assert_eq!(spec.session_id, "555", "keyed by the invoking channel");
        assert_eq!(spec.guild_id, 42);
        assert_eq!(spec.requested_by, 999);
        assert_eq!(spec.owner_id, 999, "the requester owns the run they start");
        assert_eq!(spec.admin_id, Some(7));
        assert_eq!(
            spec.authority,
            OpenAuthority::AdminOrSelfOwner,
            "self-service so any user may start a run"
        );
        assert!(!spec.private, "a dungeon is a collective, watchable crawl");
        assert_eq!(spec.queue_name.as_deref(), Some("dungeon-run"));
        assert_eq!(
            spec.surface,
            SurfaceKind::Thread {
                parent_channel_id: 555
            },
            "a thread under the invoking channel — not a whole new channel"
        );
        assert_eq!(spec.key(), "dungeon/555");

        // No guild (a DM) → no spin, fall back in-channel.
        assert!(
            plan_thread_spin(None, Some(full), 555, 999, None).is_none(),
            "a DM cannot thread — fall back in-channel"
        );
        // A guild but the bot lacks a required thread perm → no spin, fall back in-channel.
        let partial = Permissions::CREATE_PUBLIC_THREADS; // missing SEND_MESSAGES_IN_THREADS
        assert!(
            plan_thread_spin(Some(42), Some(partial), 555, 999, None).is_none(),
            "missing SEND_MESSAGES_IN_THREADS → no spin"
        );
        assert!(
            plan_thread_spin(Some(42), None, 555, 999, None).is_none(),
            "unknown app perms → no spin"
        );
    }
}
