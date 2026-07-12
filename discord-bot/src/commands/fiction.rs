//! `/dungeon` — a whole Discord channel plays a shared, AI-narrated dungeon on the
//! **REAL dregg executor**.
//!
//! The play path is [`dungeon_on_dregg`]'s committed universe — "The Warden's Keep" —
//! hosted on [`spween_dregg`]'s real [`WorldCell`]: the same `EmbeddedExecutor`, cell,
//! `CellProgram` and [`TurnReceipt`] the flagship substrate uses, NOT `attested-dm`'s
//! toy `WorldCell`/blake3 ledger. What the party pays for and plays is verifiable
//! substrate, not a LARP hash-chain.
//!
//! A channel opens a session, the bot posts the room (Bedrock/gemma narrates it, the
//! scene describes it) with a row of **buttons for the candidate moves**, and every
//! button press is a **ballot** — one write-once vote per Discord user per round,
//! attributed not to a nickname but to that user's derived **dregg identity**
//! (`cipherclerk::UserCipherclerk::derive(...).public_key_hex()`). When the round closes,
//! the **plurality winner** is applied as ONE real cap-bounded turn
//! ([`WorldCell::apply_choice`]): a legal move lands a real [`TurnReceipt`] (the receipt
//! chain grows); an illegal one — a move the executor's installed `StateConstraint`
//! refuses (a killing blow past the HP floor, a second grab of a `WriteOnce` relic, an
//! over-budget ward, a climb up a one-way stair) — is a real [`WorldError::Refused`]:
//! the crowd decided, the world disposed, nothing commits, no receipt (the anti-ghost
//! tooth). `/dungeon verify` re-verifies the whole receipt chain by REPLAY
//! ([`spween_dregg::verify_by_replay`]) — re-driving a fresh, identically-seeded
//! world-cell through the recorded choices and confirming it reproduces exactly the
//! committed state chain. A forged/reordered record fails.
//!
//! The executor is the SOURCE OF TRUTH: the AI narrates, the world resolves, the chain
//! remembers. A jailbroken narration cannot open a gated stair or mint an unearned
//! relic — only a move the verified executor admits ever changes the world.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use serenity::all::{
    ButtonStyle, ChannelId, CommandInteraction, CommandOptionType, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateCommand, CreateCommandOption, CreateEmbed,
    CreateEmbedFooter, CreateInteractionResponse, CreateInteractionResponseMessage, CreateMessage,
    Permissions,
};

use dreggnet_offerings::dungeon::{
    DungeonOffering, DungeonSession as OfferingSession, KEEP_NAME, KEEP_OBJECTIVE, TURN_CHOOSE,
};
use dreggnet_offerings::{
    Action as OfferingAction, DreggIdentity, Offering, Outcome, SessionConfig,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::orchestration::{OpenAuthority, SessionSpec};

/// The bot-branded teal (matches `embeds::DREGG_COLOR`).
const DUNGEON_COLOR: u32 = 0x7B2CBF;
/// The honest tagline that footers every dungeon surface.
const TAGLINE: &str = "the AI narrates · the world resolves · the chain remembers";

// ─────────────────────────────────────────────────────────────────────────────
// The REAL engine adapter — the bot's Discord frontend over the dreggnet-offerings
// core. `/dungeon` no longer carries its own `RealSession`: it CONSUMES the committed
// `DungeonOffering` (offering #0) over the SAME `spween-dregg` WorldCell it used to
// drive inline. The crate owns open / actions / advance (one real turn → Landed/Refused)
// / verify (replay); the bot owns the ballot (write-once rounds), the payment gate
// (`narrate_room_gated`), and the embeds. The old inline substrate seam is gone —
// proving the offering core carries exactly what the dungeon needs.
// ─────────────────────────────────────────────────────────────────────────────

/// The move outcome carried through the bot's rendering — the offering core's own
/// anti-ghost [`Outcome`]: a landed real `TurnReceipt`, or a real executor refusal.
type MoveOutcome = Outcome;

/// The stateless offering the bot drives (the free tier — the bot runs its OWN narrator
/// payment gate in [`narrate_room_gated`], so the offering's `price` is unused here).
fn offering() -> DungeonOffering {
    DungeonOffering::new()
}

/// The collective identity a plurality turn is attributed to. A dungeon round is a
/// CROWD decision (the winning move), not one mover — so the committed turn's session-
/// level actor is "the party". The write-once ballot below records the per-identity
/// votes; this names who the resolved turn is attributed to on the substrate.
fn party_actor() -> DreggIdentity {
    DreggIdentity("party".to_string())
}

/// **Build the ballot for the current room** from the offering's cap-gated actions, in
/// the SAME order the offering indexes them (so the ballot option's `choice_index` is
/// exactly the action `arg` [`WorldCell::apply_choice`] checks the gate case against). A
/// currently-ineligible action is marked `🔒` (a decoration; the executor is the sole
/// referee — a gated illegal move still surfaces as a real refusal on close).
fn round_options(session: &OfferingSession) -> Vec<VoteOption> {
    offering()
        .actions(session)
        .into_iter()
        .map(|a| {
            let label = if a.enabled {
                a.label
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

/// **Apply a winning choice as ONE real cap-bounded turn** through the offering core. A
/// legal move commits a real `TurnReceipt` ([`Outcome::Landed`]); an illegal one is a
/// real executor refusal ([`Outcome::Refused`]) that commits nothing (anti-ghost). The
/// bot never reaches the substrate directly — the offering's `advance` is the sole path.
fn apply_winner(session: &mut OfferingSession, choice_index: usize) -> MoveOutcome {
    let action = OfferingAction::new("", TURN_CHOOSE, choice_index as i64, true);
    offering().advance(session, action, party_actor())
}

// ─────────────────────────────────────────────────────────────────────────────
// The round / ballot model — the write-once vote, the tally, the plurality winner.
// (KEPT verbatim from the collective mechanism — the crowd decides, the world disposes.)
// ─────────────────────────────────────────────────────────────────────────────

/// One candidate move on the ballot — its human label and the real scene choice index it
/// resolves to (the index [`WorldCell::apply_choice`] checks the gate case against).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoteOption {
    /// The button label (e.g. `"Press on into the plundered hall"`, `"🔒 Trade blows"`).
    pub label: String,
    /// The scene choice index (within the current passage) this option applies.
    pub choice_index: usize,
}

/// **A voting round** — the candidate moves and the write-once ballots cast against them. A
/// voter is a **derived dregg public key** (hex), never a Discord nickname: a ballot is
/// attributable to a real cryptographic identity.
#[derive(Clone, Debug, Default)]
pub struct Round {
    /// The round number (monotonic per session). A ballot for a stale round is rejected.
    pub round: u64,
    /// The candidate moves, in stable order (the position is the ballot's option id).
    pub options: Vec<VoteOption>,
    /// The ballots cast: voter public-key hex → chosen option position. **Write-once**: a
    /// second vote from the same key is refused (see [`Round::cast`]).
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

    /// **Cast a write-once ballot.** `voter` is the voter's derived dregg public-key hex. The
    /// first vote is [`BallotOutcome::Recorded`]; any later vote from the same key is
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

    /// The vote count per option position, in option order.
    pub fn tally(&self) -> Vec<usize> {
        let mut counts = vec![0usize; self.options.len()];
        for &idx in self.ballots.values() {
            if idx < counts.len() {
                counts[idx] += 1;
            }
        }
        counts
    }

    /// **The plurality winner's option position** — the option with the most votes, ties
    /// broken **deterministically toward the lowest option index** (documented, reproducible).
    /// `None` only when there are no options at all; a round with options but zero ballots
    /// still resolves to option `0` (the deterministic default the crowd left to the world).
    pub fn winner(&self) -> Option<usize> {
        if self.options.is_empty() {
            return None;
        }
        let counts = self.tally();
        (0..self.options.len()).max_by_key(|&i| (counts[i], std::cmp::Reverse(i)))
    }
}

/// A per-channel play session — the real engine, the world's name, the live round, and how
/// the last narration was produced (never misreported).
pub struct DungeonSession {
    /// The offering-core play session (world-cell + receipt chain), from
    /// `dreggnet_offerings::dungeon` — the bot drives it through the [`Offering`] trait.
    pub session: OfferingSession,
    /// The world's display name.
    pub name: String,
    /// The live voting round.
    pub round: Round,
    /// How the current room narration was produced (bedrock / gemma / scripted).
    pub narrator: NarratorKind,
    /// The narration text posted for the current room — kept so a live vote re-render
    /// preserves the prose (a vote never re-hits the network, so it never misreports it).
    pub last_narration: String,
    /// If this run got its OWN orchestrated surface (a per-run thread spun via
    /// [`SessionOrchestrator`]), the session key to tear it down with at completion.
    /// `None` = the classic in-channel run (no orchestrated surface to archive).
    pub orchestrated_key: Option<String>,
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

/// The per-channel session store — keyed by Discord channel id. A module-global (behind a
/// `OnceLock<Mutex<…>>`) so it needs no change to `BotState`; every command locks it briefly
/// and never holds the guard across an `.await` (narration happens outside the lock).
fn sessions() -> &'static Mutex<HashMap<u64, DungeonSession>> {
    static SESSIONS: OnceLock<Mutex<HashMap<u64, DungeonSession>>> = OnceLock::new();
    SESSIONS.get_or_init(|| Mutex::new(HashMap::new()))
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

    // Deploy the real world-cell FIRST (no lock, no network) via the OFFERING core —
    // fail-closed if it refuses. The deterministic seed is the invoking channel id, so a
    // re-open reproduces the same world identity (what the replay verifier leans on).
    let session = match offering().open(SessionConfig::with_seed(invoking_channel)) {
        Ok(s) => s,
        Err(e) => {
            let embed = error_embed(
                "The Keep did not deploy",
                &format!("The world-cell deploy failed: {e}"),
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };

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

    // Insert the session + first round inside the lock, snapshot the render data, then
    // narrate OUTSIDE the lock (narration hits the network). Keyed by `target_channel` —
    // the thread id when spun, else the invoking channel — so a button press or
    // `/dungeon close` from inside that surface resolves against this session.
    let (room_name, room_desc, snap) = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        let options = round_options(&session);
        let room_name = session
            .current_passage_name()
            .unwrap_or_else(|| "the threshold".to_string());
        let room_desc = session.current_prose();
        let round = Round::new(0, options);
        let sess = DungeonSession {
            session,
            name: KEEP_NAME.to_string(),
            round,
            narrator: NarratorKind::Scripted,
            last_narration: String::new(),
            orchestrated_key,
        };
        let snap = render_snapshot(&sess);
        store.insert(target_channel, sess);
        (room_name, room_desc, snap)
    };

    let (narration, kind) =
        narrate_room_gated(state, command.user.id.get(), &room_name, &room_desc).await;
    if let Ok(mut store) = sessions().lock() {
        if let Some(sess) = store.get_mut(&target_channel) {
            sess.narrator = kind;
            sess.last_narration = narration.clone();
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
        // Posting into the thread failed — re-key the session under the invoking channel
        // (dropping the orchestrated key, since we will not run in the thread) and post
        // the room here instead, so the run still happens. The empty thread is left for
        // the orchestrator's own teardown paths.
        tracing::warn!("posting the dungeon room into the spun thread failed; playing in-channel");
        {
            let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
            if let Some(mut moved) = store.remove(&target_channel) {
                moved.orchestrated_key = None;
                store.insert(invoking_channel, moved);
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

    let render = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get_mut(&channel) {
            None => CloseRender::NoSession,
            Some(sess) => match sess.round.winner() {
                None => CloseRender::Empty,
                Some(winner_pos) => {
                    let winner = sess.round.options[winner_pos].clone();
                    let tally = sess.round.tally();
                    let votes_for_winner = tally.get(winner_pos).copied().unwrap_or(0);
                    let total_ballots = sess.round.ballots.len();
                    let round_no = sess.round.round;
                    let was_tie = is_tie(&tally, winner_pos);

                    // THE WORLD DISPOSES — resolve the crowd's choice as one real cap-bounded
                    // turn THROUGH THE OFFERING CORE (`advance`).
                    let outcome = apply_winner(&mut sess.session, winner.choice_index);
                    let receipts = sess.session.receipts_len();

                    let resolution = ResolvedRound {
                        world_name: sess.name.clone(),
                        round_no,
                        winner_label: winner.label.clone(),
                        votes_for_winner,
                        total_ballots,
                        was_tie,
                        result: describe_outcome(&outcome),
                        ended: sess.session.is_ended(),
                        receipts,
                    };

                    if sess.session.is_ended() {
                        CloseRender::Resolved {
                            resolution,
                            next_room_name: String::new(),
                            next_room_desc: String::new(),
                            next_snapshot: None,
                            // The run ended — hand back the spun thread (if any) at teardown.
                            teardown_key: sess.orchestrated_key.clone(),
                        }
                    } else {
                        let options = round_options(&sess.session);
                        let next = Round::new(round_no + 1, options);
                        sess.round = next;
                        let next_room_name = sess
                            .session
                            .current_passage_name()
                            .unwrap_or_else(|| "the dark".to_string());
                        let next_room_desc = sess.session.current_prose();
                        let snap = render_snapshot(sess);
                        CloseRender::Resolved {
                            resolution,
                            next_room_name,
                            next_room_desc,
                            next_snapshot: Some(snap),
                            teardown_key: None,
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

/// Whether the winning option `pos` shares its vote count with ANY OTHER option — i.e. the
/// deterministic lowest-index tie-break was exercised.
fn is_tie(tally: &[usize], pos: usize) -> bool {
    let top = tally.get(pos).copied().unwrap_or(0);
    tally.iter().enumerate().any(|(j, &c)| j != pos && c == top)
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
    let outcome = {
        let store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get(&channel) {
            None => VerifyOutcome::NoSession,
            Some(sess) => {
                let count = sess.session.receipts_len();
                // Re-verify by replay THROUGH THE OFFERING CORE (`Offering::verify`).
                let report = offering().verify(&sess.session);
                if report.verified {
                    VerifyOutcome::Result {
                        verified: true,
                        count,
                        name: sess.name.clone(),
                        break_msg: None,
                    }
                } else {
                    VerifyOutcome::Result {
                        verified: false,
                        count,
                        name: sess.name.clone(),
                        break_msg: Some(report.detail),
                    }
                }
            }
        }
    };
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
                            let snapshot = render_snapshot(sess);
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
/// lock is held so the network narration can happen afterwards without the lock.
#[derive(Clone)]
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

fn render_snapshot(sess: &DungeonSession) -> RenderSnapshot {
    let room_name = sess
        .session
        .current_passage_name()
        .unwrap_or_else(|| "the dark".to_string());
    RenderSnapshot {
        world_name: sess.name.clone(),
        round: sess.round.round,
        room_name,
        room_desc: sess.session.current_prose(),
        state_line: sess.session.state_line(),
        objective: KEEP_OBJECTIVE.to_string(),
        receipts: sess.session.receipts_len(),
        options: sess.round.options.clone(),
        tally: sess.round.tally(),
        ballots: sess.round.ballots.len(),
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
// Tests — the round/ballot logic, the REAL-engine seam (a legal winner lands a real
// receipt; an illegal winner is a real executor refusal), the deterministic voter-id.
// No live Discord required.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dungeon_on_dregg::{KP_PRESS_ON, KP_TRADE_BLOWS};

    fn opt(label: &str, choice_index: usize) -> VoteOption {
        VoteOption {
            label: label.to_string(),
            choice_index,
        }
    }

    /// Open a fresh Keep session through the OFFERING core (the same path `/dungeon start`
    /// drives): `DungeonOffering::open` deploys a real, deterministically-seeded world-cell.
    fn open_keep(seed: u64) -> OfferingSession {
        offering()
            .open(SessionConfig::with_seed(seed))
            .expect("the Keep opens on a real world-cell")
    }

    // ── (a) round / ballot logic ─────────────────────────────────────────────

    #[test]
    fn a_ballot_is_write_once_per_voter() {
        let mut round = Round::new(0, vec![opt("go north", 0), opt("look", 1)]);
        assert_eq!(round.cast("pubkey_alice", 0), BallotOutcome::Recorded);
        assert_eq!(round.cast("pubkey_alice", 1), BallotOutcome::AlreadyVoted);
        assert_eq!(round.tally(), vec![1, 0]);
        assert_eq!(round.cast("pubkey_bob", 1), BallotOutcome::Recorded);
        assert_eq!(round.tally(), vec![1, 1]);
    }

    #[test]
    fn a_bad_option_index_is_refused() {
        let mut round = Round::new(0, vec![opt("look", 0)]);
        assert_eq!(round.cast("pk", 9), BallotOutcome::BadOption);
        assert!(round.ballots.is_empty());
    }

    #[test]
    fn plurality_winner_is_the_most_voted() {
        let mut round = Round::new(0, vec![opt("north", 0), opt("south", 1), opt("look", 2)]);
        round.cast("a", 1);
        round.cast("b", 1);
        round.cast("c", 0);
        assert_eq!(round.winner(), Some(1));
    }

    #[test]
    fn ties_break_toward_the_lowest_option_index() {
        let mut round = Round::new(0, vec![opt("north", 0), opt("south", 1)]);
        round.cast("a", 0);
        round.cast("b", 1);
        assert_eq!(round.winner(), Some(0));
        assert!(is_tie(&round.tally(), 0));
    }

    #[test]
    fn an_empty_round_defaults_to_option_zero() {
        let round = Round::new(0, vec![opt("look", 0)]);
        assert_eq!(round.winner(), Some(0));
    }

    // ── (b) the REAL-engine seam ─────────────────────────────────────────────
    // These supersede the two previously-#[ignore]d attested-dm `sunken_vault` tests:
    // now they drive the REAL dungeon-on-dregg WorldCell (a landed move is a real
    // TurnReceipt; an illegal move is a real executor refusal; verify_by_replay holds).

    /// A voted LEGAL move lands a REAL receipt — the ballot winner is applied as one
    /// cap-bounded turn on the real executor, the receipt count grows, and the whole
    /// playthrough re-verifies by replay against a fresh identically-seeded world-cell.
    #[test]
    fn a_voted_legal_move_lands_a_real_receipt() {
        let mut sess = open_keep(7);
        assert_eq!(sess.current_passage_name().as_deref(), Some("gatehall"));
        assert_eq!(sess.receipts_len(), 1, "genesis is the first verified turn");

        // "Press on into the plundered hall" — an ungated, legal move (choice KP_PRESS_ON).
        let opts = round_options(&sess);
        assert!(
            opts.iter().any(|o| o.choice_index == KP_PRESS_ON),
            "the ballot offers the ungated press-on move"
        );
        match apply_winner(&mut sess, KP_PRESS_ON) {
            MoveOutcome::Landed { receipt, ended } => {
                assert!(!ended, "pressing on does not end the Keep");
                assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
            }
            other => panic!("a legal move must land a real receipt, got {other:?}"),
        }
        assert_eq!(sess.receipts_len(), 2, "a real verified turn landed");
        assert_eq!(
            sess.current_passage_name().as_deref(),
            Some("hall"),
            "the world advanced to the plundered hall"
        );

        // The real receipt chain re-verifies by replay, through the offering's `verify`.
        assert!(
            offering().verify(&sess).verified,
            "the honest playthrough re-verifies via verify_by_replay"
        );
    }

    /// A voted ILLEGAL move is a REAL executor refusal — world unchanged, no receipt
    /// (the anti-ghost tooth). Two survivable blows land; the killing blow past the HP
    /// floor (`FieldGte`) is refused, and the honest chain still re-verifies.
    #[test]
    fn a_voted_illegal_move_is_a_real_executor_refusal_no_receipt() {
        let mut sess = open_keep(8);

        // Two survivable trade-blows (hp 50 → 30 → 10), each a real committed turn.
        for _ in 0..2 {
            match apply_winner(&mut sess, KP_TRADE_BLOWS) {
                MoveOutcome::Landed { receipt, ended } => {
                    assert!(!ended);
                    assert_ne!(receipt.turn_hash, [0u8; 32]);
                }
                other => panic!("a survivable blow must land, got {other:?}"),
            }
        }
        assert_eq!(sess.read_var("hp"), 10, "two blows dropped hp to 10");
        let receipts_before = sess.receipts_len();

        // At hp 10 the gate-warden choice is now shown locked (its `{ hp >= 21 }` fails).
        let opts = round_options(&sess);
        let blow = opts
            .iter()
            .find(|o| o.choice_index == KP_TRADE_BLOWS)
            .expect("the trade-blows move is still on the ballot");
        assert!(
            blow.label.starts_with('🔒'),
            "the killing blow is decorated locked (condition eval), got {:?}",
            blow.label
        );

        // The crowd votes it anyway — the REAL executor refuses (FieldGte on the post-state).
        match apply_winner(&mut sess, KP_TRADE_BLOWS) {
            MoveOutcome::Refused(_) => {}
            other => panic!("a killing blow must be a real executor refusal, got {other:?}"),
        }
        // Anti-ghost: nothing committed.
        assert_eq!(
            sess.receipts_len(),
            receipts_before,
            "no receipt landed for the refused choice"
        );
        assert_eq!(sess.read_var("hp"), 10, "hp unchanged after the refusal");
        assert_eq!(
            sess.current_passage_name().as_deref(),
            Some("gatehall"),
            "still in the gatehall — the world did not move"
        );

        // The honest chain (genesis + two blows) still re-verifies by replay.
        assert!(
            offering().verify(&sess).verified,
            "the honest prefix re-verifies after the refusal"
        );
    }

    /// The recorded playthrough re-verifies through a full legal sequence via the offering's
    /// own `verify` (`verify_by_replay` under the hood).
    ///
    /// The forged/tamper tooth (a mutated committed step fails replay) is now OWNED BY THE
    /// ENGINE, not the frontend: it lives in `dreggnet_offerings::dungeon`'s
    /// `a_forged_choice_fails_replay`, which reaches the session's private `seed`/`scene` to
    /// forge the record. A frontend cannot — and by design must not — reach those internals,
    /// so the dedup put the tamper test where the substrate is owned.
    #[test]
    fn the_playthrough_reverifies_through_the_offering() {
        let mut sess = open_keep(9);
        // A legal opening: press on into the hall, claim the crown for the Red Hand.
        assert!(matches!(
            apply_winner(&mut sess, KP_PRESS_ON),
            MoveOutcome::Landed { .. }
        ));
        // hall: claim red (choice 0).
        assert!(matches!(
            apply_winner(&mut sess, 0),
            MoveOutcome::Landed { .. }
        ));
        assert!(
            offering().verify(&sess).verified,
            "the legal playthrough re-verifies"
        );
    }

    // ── (c) the voter id IS the cipherclerk-derived public key (deterministic) ──

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

    #[test]
    fn round_options_offer_the_start_room_moves() {
        let sess = open_keep(3);
        let options = round_options(&sess);
        assert!(
            options.len() >= 2,
            "the gatehall offers more than one candidate move"
        );
        // The ungated press-on move is present and NOT locked.
        let press = options
            .iter()
            .find(|o| o.choice_index == KP_PRESS_ON)
            .expect("press-on present");
        assert!(
            !press.label.starts_with('🔒'),
            "an ungated move is not locked"
        );
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
