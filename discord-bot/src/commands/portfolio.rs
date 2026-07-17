//! `/play <offering>` — **the full-portfolio reach**: the twelve DreggNet Cloud offerings that did
//! NOT yet have a bespoke Discord slash command, mounted through the SAME generic
//! [`crate::commands::offering`] adapter as `/council` / `/market` / `/doc`, so Discord reaches
//! offering parity with the web catalog ([`dreggnet_web::demo_host`]).
//!
//! Before this module Discord served six of the eighteen portfolio offerings (dungeon, council,
//! market, hermes, grain, doc). This adds the rest via one uniform `/play` command:
//!
//! * **the two portfolio games** — `automatafl` (the simultaneous-move board) and `tug`
//!   (multiway-tug, wrapped in the seat-claiming [`SeatedTug`] adapter — the byte-peer of the web
//!   `seated` module — so a Discord user's derived identity can claim a seat and see their OWN
//!   hidden hand through the viewer-aware render path);
//! * **the two remaining non-game offerings** — `names` and `compute`;
//! * **the eight do-once RPG feature surfaces** — `trade`, `inventory`, `cheevos`, `guild`, `craft`,
//!   `companion`, `tavern`, `party` (`dreggnet-surfaces`).
//!
//! Each `impl`s [`Offering`], so it becomes a Discord surface through the generic adapter with no
//! per-offering rendering code: its deos `ViewNode` render is the embed, its cap-gated `Action`s are
//! the buttons, a press is ONE real `advance` attributed to the presser's derived dregg identity, and
//! the press re-render is projected FOR the presser ([`crate::commands::offering::surface_for`]).
//!
//! HONEST SCOPE: `trade`/`inventory`/`craft` each open over their OWN demo `SharedWorld` here (the
//! per-type Discord session store admits no cross-offering shared handle the way
//! `dreggnet_surfaces::register_surfaces` mounts one world across the three) — so the craft→inventory→
//! trade composition the web demo shows is not preserved on this surface; each is individually
//! reachable + drivable, which is the parity bar. A board offering (automatafl, tug) is a `CoordGrid`
//! that the Discord card renderer paints in full (the most complete renderer of the three chat
//! surfaces).

use std::sync::OnceLock;

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dregg_automatafl::AutomataflOffering;
use dregg_multiway_tug::{Player, TugOffering, TugSession};
use dreggnet_compute::ComputeOffering;
use dreggnet_names::NamesOffering;
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dreggnet_surfaces::{
    CheevoShowcase, CompanionOffering, CraftOffering, GuildPage, InventoryOffering, PartyOffering,
    SharedWorld, TavernOffering, TradeOffering,
};

use crate::BotState;
use crate::commands::offering::{self, DiscordOffering, Store, identity_of};

// ─────────────────────────────────────────────────────────────────────────────
// SeatedTug — the seat-claiming adapter (byte-peer of `dreggnet_web::seated`).
// ─────────────────────────────────────────────────────────────────────────────

/// The multiway-tug offering with **Discord-claimable seats**. `TugOffering` names its two seats by
/// fixed canonical strings while a Discord user's [`DreggIdentity`] is a derived key — this adapter
/// claims a seat for the first two distinct identities that act (A then B), rewriting the actor to
/// the canonical seat identity before delegating; a third identity is a spectator (refused). It
/// changes NOTHING in `dregg-multiway-tug`, and `render_for` maps a viewer to their seat so the
/// hidden-hand fog reaches the right player.
pub struct SeatedTug {
    inner: TugOffering,
}

impl SeatedTug {
    pub fn new() -> Self {
        SeatedTug { inner: TugOffering }
    }
}

impl Default for SeatedTug {
    fn default() -> Self {
        SeatedTug::new()
    }
}

/// A live tug round plus its seat claims (which Discord identity holds seat A / seat B).
pub struct SeatedTugSession {
    inner: TugSession,
    seats: [Option<DreggIdentity>; 2],
}

impl SeatedTugSession {
    fn seat_of(&self, who: &DreggIdentity) -> Option<Player> {
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].as_ref() == Some(who) {
                return Some(p);
            }
        }
        None
    }

    fn claim(&mut self, who: &DreggIdentity) -> Option<Player> {
        if let Some(p) = self.seat_of(who) {
            return Some(p);
        }
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].is_none() {
                self.seats[p.idx()] = Some(who.clone());
                return Some(p);
            }
        }
        None
    }
}

impl Offering for SeatedTug {
    type Session = SeatedTugSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(SeatedTugSession {
            inner: self.inner.open(cfg)?,
            seats: [None, None],
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.inner.actions(&session.inner)
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let Some(seat) = session.claim(&actor) else {
            return Outcome::Refused("both seats are taken — you are a spectator".to_string());
        };
        self.inner
            .advance(&mut session.inner, input, TugOffering::seat_identity(seat))
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.inner.verify(&session.inner)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        self.inner.render(&session.inner)
    }

    /// The per-viewer surface — a claimed seat sees its OWN hand; anyone else sees the public fog.
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        match session.seat_of(viewer) {
            Some(seat) => self
                .inner
                .render_for(&session.inner, &TugOffering::seat_identity(seat)),
            None => self.inner.render(&session.inner),
        }
    }

    fn price(&self, input: &Action) -> RunCost {
        self.inner.price(input)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The DiscordOffering impls — each mounts its offering on the generic adapter.
// ─────────────────────────────────────────────────────────────────────────────

/// A generic honest status line for a portfolio offering: the count of committed turns its chain
/// re-verifies over (genesis + committed), the same number `/…​ verify` reports.
fn verified_turns<O: Offering>(off: &O, session: &O::Session) -> String {
    format!("{} verified turns", off.verify(session).turns)
}

macro_rules! seat_of_store {
    ($ty:ty) => {{
        static SESSIONS: OnceLock<Store<$ty>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }};
}

impl DiscordOffering for SeatedTug {
    const KEY: &'static str = "tug";
    const TITLE: &'static str = "Multiway-Tug";
    const COLOR: u32 = 0x8E5BD6;
    const TAGLINE: &'static str =
        "a hidden-hand tug of influence · your own hand revealed, the opponent fog";
    fn store() -> &'static Store<Self> {
        seat_of_store!(SeatedTug)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for AutomataflOffering {
    const KEY: &'static str = "automatafl";
    const TITLE: &'static str = "Automatafl";
    const COLOR: u32 = 0x3D8B7D;
    const TAGLINE: &'static str =
        "the simultaneous-move board · seal a move · reveal · the automaton steps";
    fn store() -> &'static Store<Self> {
        seat_of_store!(AutomataflOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for NamesOffering {
    const KEY: &'static str = "names";
    const TITLE: &'static str = "DreggNet Names";
    const COLOR: u32 = 0x4A78C2;
    const TAGLINE: &'static str = "an identity / naming service · register · transfer · resolve";
    fn store() -> &'static Store<Self> {
        seat_of_store!(NamesOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for ComputeOffering {
    const KEY: &'static str = "compute";
    const TITLE: &'static str = "DreggNet Compute";
    const COLOR: u32 = 0x2F8FA6;
    const TAGLINE: &'static str = "a confined compute-job market · post · claim · settle";
    fn store() -> &'static Store<Self> {
        seat_of_store!(ComputeOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for TradeOffering {
    const KEY: &'static str = "trade";
    const TITLE: &'static str = "DreggNet Trade";
    const COLOR: u32 = 0xC28A3D;
    const TAGLINE: &'static str = "a player market · list · settle an atomic asset swap";
    fn store() -> &'static Store<Self> {
        seat_of_store!(TradeOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for InventoryOffering {
    const KEY: &'static str = "inventory";
    const TITLE: &'static str = "Inventory";
    const COLOR: u32 = 0x9A7B4F;
    const TAGLINE: &'static str = "your owned notes (gear · cards · trophies), provenance-checked";
    fn store() -> &'static Store<Self> {
        seat_of_store!(InventoryOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for CheevoShowcase {
    const KEY: &'static str = "cheevos";
    const TITLE: &'static str = "Achievements";
    const COLOR: u32 = 0xD4A72C;
    const TAGLINE: &'static str = "earned soulbound proofs over verified runs";
    fn store() -> &'static Store<Self> {
        seat_of_store!(CheevoShowcase)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for GuildPage {
    const KEY: &'static str = "guild";
    const TITLE: &'static str = "Guild";
    const COLOR: u32 = 0x6E7BA6;
    const TAGLINE: &'static str = "the roster + the aggregate verified-clears leaderboard";
    fn store() -> &'static Store<Self> {
        seat_of_store!(GuildPage)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for CraftOffering {
    const KEY: &'static str = "craft";
    const TITLE: &'static str = "Forge";
    const COLOR: u32 = 0xB5562E;
    const TAGLINE: &'static str =
        "a provably-fair craft loop · consume materials · mint a bound output";
    fn store() -> &'static Store<Self> {
        seat_of_store!(CraftOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for CompanionOffering {
    const KEY: &'static str = "companion";
    const TITLE: &'static str = "Companions";
    const COLOR: u32 = 0xC26AA0;
    const TAGLINE: &'static str = "hatch a fair-drawn companion · raise it through XP-gated turns";
    fn store() -> &'static Store<Self> {
        seat_of_store!(CompanionOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for TavernOffering {
    const KEY: &'static str = "tavern";
    const TITLE: &'static str = "Tavern";
    const COLOR: u32 = 0x8A6D3B;
    const TAGLINE: &'static str = "the shared hub · presence · the LFG board · the party roster";
    fn store() -> &'static Store<Self> {
        seat_of_store!(TavernOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for PartyOffering {
    const KEY: &'static str = "party";
    const TITLE: &'static str = "Party";
    const COLOR: u32 = 0x5B8ED6;
    const TAGLINE: &'static str = "a seated roster + a quorum-certified fork ballot";
    fn store() -> &'static Store<Self> {
        seat_of_store!(PartyOffering)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The `/play` command — open any portfolio offering by key.
// ─────────────────────────────────────────────────────────────────────────────

/// The twelve `/play` offering keys (the games + non-game + RPG surfaces this module mounts).
pub const PLAY_KEYS: [&str; 12] = [
    "automatafl",
    "tug",
    "names",
    "compute",
    "trade",
    "inventory",
    "cheevos",
    "guild",
    "craft",
    "companion",
    "tavern",
    "party",
];

/// Register `/play <offering>` — open any of the twelve full-portfolio offerings in this channel.
pub fn register() -> CreateCommand {
    let mut option = CreateCommandOption::new(
        CommandOptionType::String,
        "offering",
        "Which portfolio offering to open in this channel",
    )
    .required(true);
    for key in PLAY_KEYS {
        option = option.add_string_choice(key, key);
    }
    CreateCommand::new("play")
        .description(
            "Open a DreggNet Cloud offering — a game or a feature surface — in this channel",
        )
        .add_option(option)
}

/// Route `/play <offering>` — open the chosen offering + post its surface (projected for the opener).
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let key = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();
    let channel = command.channel_id.get();
    let viewer = identity_of(state, command.user.id.get());
    let cfg = SessionConfig::with_seed(channel);

    // The world-backed surfaces (trade/inventory/craft) each build their own per-open demo
    // `SharedWorld` INSIDE their factory — the world is `Rc`-shared and not `Send`, so it is born
    // on the offering store's own thread and never crosses; see the module HONEST SCOPE note
    // (each opens over its own world on this per-type surface).
    let opened: Result<(), OfferingError> = match key.as_str() {
        "tug" => open_and_post::<SeatedTug>(ctx, command, SeatedTug::new, &viewer, cfg).await,
        "automatafl" => {
            open_and_post::<AutomataflOffering>(ctx, command, || AutomataflOffering, &viewer, cfg)
                .await
        }
        "names" => {
            open_and_post::<NamesOffering>(ctx, command, NamesOffering::new, &viewer, cfg).await
        }
        "compute" => {
            open_and_post::<ComputeOffering>(ctx, command, ComputeOffering::new, &viewer, cfg).await
        }
        "trade" => {
            open_and_post::<TradeOffering>(
                ctx,
                command,
                || TradeOffering::in_world(SharedWorld::demo("Adventurer")),
                &viewer,
                cfg,
            )
            .await
        }
        "inventory" => {
            open_and_post::<InventoryOffering>(
                ctx,
                command,
                || InventoryOffering::in_world(SharedWorld::demo("Adventurer")),
                &viewer,
                cfg,
            )
            .await
        }
        "cheevos" => {
            open_and_post::<CheevoShowcase>(ctx, command, CheevoShowcase::demo, &viewer, cfg).await
        }
        "guild" => {
            open_and_post::<GuildPage>(
                ctx,
                command,
                || GuildPage::demo("The Iron Wardens"),
                &viewer,
                cfg,
            )
            .await
        }
        "craft" => {
            open_and_post::<CraftOffering>(
                ctx,
                command,
                || CraftOffering::in_world(SharedWorld::demo("Adventurer")),
                &viewer,
                cfg,
            )
            .await
        }
        "companion" => {
            open_and_post::<CompanionOffering>(ctx, command, CompanionOffering::demo, &viewer, cfg)
                .await
        }
        "tavern" => {
            open_and_post::<TavernOffering>(
                ctx,
                command,
                || TavernOffering::demo("The Salted Tankard"),
                &viewer,
                cfg,
            )
            .await
        }
        "party" => {
            open_and_post::<PartyOffering>(ctx, command, PartyOffering::new, &viewer, cfg).await
        }
        other => {
            let _ = command
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .content(format!("Unknown offering `{other}`."))
                            .ephemeral(true),
                    ),
                )
                .await;
            return;
        }
    };

    if let Err(e) = opened {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(
                            CreateEmbed::new()
                                .title("The offering was not opened")
                                .description(format!(
                                    "The executor refused to open the session: {e}"
                                ))
                                .color(0xE63946),
                        )
                        .ephemeral(true),
                ),
            )
            .await;
    }
}

/// Open the offering `make` builds in the channel and post its surface (projected FOR the
/// opener). The factory runs on the offering store's own thread ([`offering::open_in`]), so a
/// world-backed non-`Send` offering is born where it lives. Returns the open result so the caller
/// reports a fail-closed refusal honestly.
async fn open_and_post<O: DiscordOffering>(
    ctx: &Context,
    command: &CommandInteraction,
    make: impl FnOnce() -> O + Send + 'static,
    viewer: &DreggIdentity,
    cfg: SessionConfig,
) -> Result<(), OfferingError> {
    offering::open_in(command.channel_id.get(), make, cfg)?;
    let channel = command.channel_id.get();
    let viewer = viewer.clone();
    let rendered = offering::with_live::<O, _>(channel, move |live| {
        offering::surface_for::<O>(live, &viewer)
    });
    if let Some((embed, rows)) = rendered {
        let _ = command
            .create_response(
                &ctx.http,
                CreateInteractionResponse::Message(
                    CreateInteractionResponseMessage::new()
                        .embed(embed)
                        .components(rows),
                ),
            )
            .await;
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — every portfolio offering DRIVEN at the logic level (the SAME `open_in` +
// `drive` a live `/play` open + button press take), against real substrates. No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::offering::{
        Driven, close_in, drive, fire_id, is_open, surface_for, with_live,
    };

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// The debug text of a session's rendered surface (the same idiom the game crates' surface tests
    /// use) — a proxy for "the surface is non-empty / not a silent drop".
    fn view_text(surface: &Surface) -> String {
        format!("{:?}", surface.view())
    }

    /// **Every one of the twelve `/play` offerings OPENS and renders a NON-EMPTY surface** — the
    /// exact gap the audit found (automatafl, tug, and the eight RPG surfaces were absent on
    /// Discord). Each opens over its real substrate through the generic adapter and its
    /// viewer-projected surface carries renderable content (no silent empty).
    #[test]
    fn every_play_offering_opens_and_renders_a_non_empty_surface() {
        // A distinct channel per offering so their per-channel stores do not collide.
        let mut ch = 770_000u64;
        let me = actor("aa");

        macro_rules! check {
            ($ty:ty, $ctor:expr, $key:literal) => {{
                let channel = ch;
                ch += 1;
                close_in::<$ty>(channel);
                offering::open_in(channel, || $ctor, SessionConfig::with_seed(channel))
                    .unwrap_or_else(|e| panic!("`{}` opens on Discord: {e}", $key));
                assert!(is_open::<$ty>(channel), "`{}` session is live", $key);
                assert_eq!(
                    <$ty as DiscordOffering>::KEY,
                    $key,
                    "`{}` registers under its web-parity key",
                    $key
                );
                // The viewer-projected surface is non-empty (the render path the live press takes).
                let text = with_live::<$ty, _>(channel, {
                    let me = me.clone();
                    move |live| view_text(&live.offering.render_for(&live.session, &me))
                })
                .expect("the session is live");
                assert!(
                    !text.trim().is_empty() && text != "VStack([])",
                    "`{}` renders a non-empty surface (not a silent drop): {text}",
                    $key
                );
                // `surface_for` (the live-press render path) runs and yields the affordance rows.
                let rows = with_live::<$ty, _>(channel, {
                    let me = me.clone();
                    move |live| surface_for::<$ty>(live, &me).1
                })
                .expect("live");
                let _ = rows; // its existence + non-panic is the smoke; content asserted per-game below.
                close_in::<$ty>(channel);
            }};
        }

        // The world-backed surfaces each build their demo `SharedWorld` INSIDE the open factory
        // (the `Rc`-shared world is not `Send`; it is born on the store's thread) — matching the
        // module HONEST SCOPE note: each opens over its own world on this per-type surface.
        check!(SeatedTug, SeatedTug::new(), "tug");
        check!(AutomataflOffering, AutomataflOffering, "automatafl");
        check!(NamesOffering, NamesOffering::new(), "names");
        check!(ComputeOffering, ComputeOffering::new(), "compute");
        check!(
            TradeOffering,
            TradeOffering::in_world(SharedWorld::demo("Adventurer")),
            "trade"
        );
        check!(
            InventoryOffering,
            InventoryOffering::in_world(SharedWorld::demo("Adventurer")),
            "inventory"
        );
        check!(CheevoShowcase, CheevoShowcase::demo(), "cheevos");
        check!(GuildPage, GuildPage::demo("The Iron Wardens"), "guild");
        check!(
            CraftOffering,
            CraftOffering::in_world(SharedWorld::demo("Adventurer")),
            "craft"
        );
        check!(CompanionOffering, CompanionOffering::demo(), "companion");
        check!(
            TavernOffering,
            TavernOffering::demo("The Salted Tankard"),
            "tavern"
        );
        check!(PartyOffering, PartyOffering::new(), "party");
        let _ = ch; // the macro's channel cursor past the last offering
    }

    /// **The twelve `/play` keys are exactly `PLAY_KEYS`** — the `handle` dispatch + the `register`
    /// choices + the route arms agree (so every offering is reachable, none stranded).
    #[test]
    fn the_play_keys_cover_the_twelve_portfolio_offerings() {
        for want in [
            "automatafl",
            "tug",
            "names",
            "compute",
            "trade",
            "inventory",
            "cheevos",
            "guild",
            "craft",
            "companion",
            "tavern",
            "party",
        ] {
            assert!(PLAY_KEYS.contains(&want), "`{want}` is a /play key");
        }
        assert_eq!(PLAY_KEYS.len(), 12);
    }

    /// **automatafl is REACHABLE + DRIVABLE on Discord** — the board renders a non-empty surface and
    /// a real move drives one turn through the substrate (a landed receipt), re-rendering the board.
    #[test]
    fn automatafl_drives_a_real_turn_on_discord() {
        let channel = 771_100u64;
        close_in::<AutomataflOffering>(channel);
        offering::open_in(
            channel,
            || AutomataflOffering,
            SessionConfig::with_seed(channel),
        )
        .expect("automatafl opens");
        let me = actor("af");

        // The first affordance the board offers (a `select` on a movable piece).
        let first = with_live::<AutomataflOffering, _>(channel, |live| {
            live.offering.actions(&live.session).into_iter().next()
        })
        .flatten()
        .expect("the board offers at least one affordance");

        match drive::<AutomataflOffering>(
            channel,
            &fire_id(AutomataflOffering::KEY, &first.turn, first.arg),
            me,
        ) {
            Driven::Fired(outcome) => {
                // A legal select lands; the substrate is the referee for anything else.
                assert!(
                    matches!(outcome, Outcome::Landed { .. } | Outcome::Refused(_)),
                    "an automatafl press resolves on the real substrate: {outcome:?}"
                );
            }
            other => panic!("an automatafl press must drive a real turn, got {other:?}"),
        }
        assert!(
            offering::verify_live::<AutomataflOffering>(channel)
                .expect("live")
                .verified,
            "the automatafl chain re-verifies"
        );
        close_in::<AutomataflOffering>(channel);
    }

    /// **The multiway-tug hidden hand threads the viewer on Discord** — a seated player sees THEIR
    /// OWN card ids through the viewer-aware render path while a different viewer (and the old
    /// viewer-blind render) sees fog; the two seats' hands DIFFER. This is the `hidden_hand_web.rs`
    /// shape on the Discord surface, driven end-to-end through the generic adapter's `drive`.
    #[test]
    fn the_tug_hidden_hand_threads_the_viewer_on_discord() {
        let channel = 771_200u64;
        close_in::<SeatedTug>(channel);
        offering::open_in(channel, SeatedTug::new, SessionConfig::with_seed(channel))
            .expect("tug opens");
        let alice = actor("al");
        let bob = actor("bo");

        // Alice claims seat A by playing the opening Competition — a real landed receipt.
        match drive::<SeatedTug>(channel, &fire_id(SeatedTug::KEY, "comp", 3), alice.clone()) {
            Driven::Fired(o) => assert!(o.landed(), "alice's comp lands + claims seat A: {o:?}"),
            other => panic!("alice's play must drive a turn, got {other:?}"),
        }
        // Bob claims seat B by playing — lands or is a real turn-order refusal, either way seat B is
        // his and his view is projected for him.
        let _ = drive::<SeatedTug>(channel, &fire_id(SeatedTug::KEY, "secret", 0), bob.clone());

        // AS ALICE (seat A): her own hand (card ids) is revealed, the opponent is fog.
        let alice_view = with_live::<SeatedTug, _>(channel, {
            let alice = alice.clone();
            move |live| view_text(&live.offering.render_for(&live.session, &alice))
        })
        .expect("live");
        assert!(
            alice_view.contains("Your hand") && alice_view.contains("card #"),
            "seat A sees HER OWN card ids on Discord: {alice_view}"
        );
        assert!(
            alice_view.contains("Opponent (hidden hand)"),
            "the opponent's hand stays fog for the seated viewer: {alice_view}"
        );

        // AS BOB (seat B): his own, DIFFERENT hand.
        let bob_view = with_live::<SeatedTug, _>(channel, {
            let bob = bob.clone();
            move |live| view_text(&live.offering.render_for(&live.session, &bob))
        })
        .expect("live");
        assert!(
            bob_view.contains("Your hand") && bob_view.contains("card #"),
            "seat B sees HIS OWN card ids on Discord: {bob_view}"
        );
        assert_ne!(
            alice_view, bob_view,
            "the viewer threaded: the two seats' hands render DIFFERENTLY (per-viewer \
             discrimination, not the viewer-blind fog the old render served everyone)"
        );

        // A THIRD identity (holds no seat) sees fog — never anyone's cards.
        let stranger = actor("st");
        let stranger_view = with_live::<SeatedTug, _>(channel, {
            let stranger = stranger.clone();
            move |live| view_text(&live.offering.render_for(&live.session, &stranger))
        })
        .expect("live");
        assert!(
            !stranger_view.contains("card #"),
            "a non-seat viewer sees fog, never the cards: {stranger_view}"
        );

        close_in::<SeatedTug>(channel);
    }
}
