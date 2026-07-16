# DreggNet Cloud — the Offering/Session abstraction

Status: **built** — this document is the design rationale; the code is canonical. The abstraction lives in
`dreggnet-offerings` (the `Offering` trait at `src/lib.rs:446`, the `Frontend` trait at `:572`,
`mock::MockFrontend` as the reference renderer), with four frontends (the discord-bot, `dreggnet-telegram`,
`dreggnet-wechat`, `dreggnet-web`) and offerings from the dungeon (#0, in-crate) through `dreggnet-hermes`
(#1, a confined agent) and `dreggnet-grain` (#2, a confined grain) to the Descent family (`daily_descent`,
`overworld`, `descent_tournament`) — one core, every surface. `DREGGNET-CLEANER-DESIGN.md` carries the
current-state framing. The dungeon is **offering #0** — the first instance of the general pattern: the cloud
hosts *offerings* (confined, verifiable, paid, per-session things) on the real dregg substrate.

## The shape every offering shares (the invariants every offering carries)
1. **A per-session confined thing** — a channel/thread hosts one live session.
2. **A confined intelligence/app** — the dungeon's narrator (jailed LLM); for others, a hosted Hermes agent or a grain.
3. **Real verifiable turns** — each input is a real executor turn -> a `TurnReceipt`; `verify_by_replay` re-checks the
   whole chain. The executor is the source of truth (a jailbroken narration cannot change the world).
4. **Payment-gated** — `dregg-pay` credits (dual-asset $DREGG/USDC); a paid action debits a credit; empty -> free tier.
5. **Optionally collective** — write-once ballots + quorum (collective-choice) when a crowd drives one session.

## The abstraction
```
trait Offering {
    type Session;                                   // the live confined state (a WorldCell, a Hermes jail, a grain)
    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError>;
    fn actions(&self, s: &Self::Session) -> Vec<Action>;         // candidate moves (ballot options / buttons)
    fn advance(&self, s: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome; // one real turn
    fn verify(&self, s: &Self::Session) -> VerifyReport;         // verify_by_replay / the offering's proof
    fn render(&self, s: &Self::Session) -> Surface;             // room/prose/state for the channel embed
    fn price(&self, input: &Action) -> RunCost;                 // what a paid action costs (credits)
}
```
- **Outcome** = `Landed(TurnReceipt) | Refused(reason)` — the same anti-ghost shape the dungeon uses.
- **Session** is offering-specific but always carries a real verifiable state chain.
- The bot never trusts the confined intelligence — it resolves the *typed Action* on the substrate, not the prose.
- The canonical definition is `dreggnet-offerings/src/lib.rs:446`; beyond this sketch it adds
  `advance_collective` (one real turn carrying a first-class `CollectiveDecision` — the electorate + the
  tally + the carrier, recorded beside the committed turn).

## The shared orchestration layer (the bot's job — the "Midjourney" layer)
`/start <offering>` -> the bot (admin) **spins a channel/thread** (via the dormant `discord_caps` engine + `GUILDS`/
`GUILD_MEMBERS` intents + a `guild_create` handler) -> `Offering::open` -> posts `render` with `actions` as buttons ->
each press is a ballot / a paid action (gate on `dregg-pay` credits) -> `Offering::advance` (a real turn) -> update
the embed -> on completion, `Offering::verify` + archive the thread. One lifecycle, every offering.

## Frontends — Discord is #0; Telegram, WeChat, web are the SAME offerings, different surfaces
The offering/session/payment/verify/ballot CORE is **frontend-agnostic**. A `Frontend` renders an offering's `Surface`
and collects `Action`s; the core resolves them on the substrate. So every surface reuses ONE core — only presentation
differs (and the executor stays the sole source of truth on all of them).
```
trait Frontend {
    fn identity(&self, user: PlatformUser) -> DreggIdentity;         // derive the user's dregg identity per platform
    fn spin_session(&self, off: &dyn Offering, cfg: SessionConfig) -> SessionSurface; // a thread/group/chat per session
    fn present(&self, s: &SessionSurface, surface: Surface);         // room/prose/state + the action controls
    fn collect(&self, ev: PlatformEvent) -> Option<(SessionId, Action, DreggIdentity)>; // a press/command -> an action
    fn teardown(&self, s: SessionSurface);                           // archive on completion
}
```
(The canonical definition, `dreggnet-offerings/src/lib.rs:572`, is generic over the platform's user + event types
— a Discord `ComponentInteraction`, a Telegram `CallbackQuery`, a web POST — and spins/tears down by `SessionId`.)
- **Discord (#0, built):** threads/channels + buttons + `GUILDS`/`GUILD_MEMBERS` intents; identity from the user's
  derived Ed25519 (`UserCipherclerk`).
- **Telegram (built — `dreggnet-telegram`):** `TelegramFrontend` over the core; identity = a BLAKE3-derived per-user
  Ed25519 (`UserCipherclerk`-mirroring, Telegram-scoped domain); the `Surface` walks into message text and the
  cap-gated `Action`s become inline-keyboard buttons whose `callback_data` carries `{turn, arg}`; drives through an
  injected `Transport` (`MockTransport` in tests — no token, no network needed).
- **WeChat (built — `dreggnet-wechat`):** `WeChatFrontend`; an Official Account forbids per-message buttons, so the
  canonical surface is a **numbered reply list** (affordances as a `1.`-indexed list; the user replies with the
  number), with an `api::MiniProgramCard` payload for the rich Mini-Program surface.
- **Web (built — `dreggnet-web`):** `WebFrontend` renders the deos `Surface` into an HTML fragment — a
  `<form>`/`<button>` per cap-gated affordance, each POSTing its `Action`; `WebState` hosts the axum surface.

**The factoring is in place:** the offering/session/payment/verify/ballot logic lives in the **frontend-agnostic
`dreggnet-offerings` crate** (no serenity/Discord dependency); the discord-bot consumes it (e.g.
`discord-bot/src/character_store.rs` is the sqlite backing of `dreggnet_offerings::character`'s `CharacterStore`);
Telegram/WeChat/web are more `Frontend` impls. `dregg-pay` (payments), the verifiable substrate
(WorldCell/receipts), and the collective are shared across all of them.

**REUSE the deos surface — do NOT reinvent `Surface`/`Action`.** The frontend-agnostic surface layer ALREADY EXISTS
and the bot already renders it: `deos-view` = a `ViewNode` (a moldable view of a cell); `starbridge-web-surface::
affordance` = a cell's **cap-gated affordances** (`AffordanceIntent`/`EffectSummary`), each firing a real dregg turn.
The bot's `/deos` (a cell's affordance surface → cap-gated buttons) and `/card` (a `deos_view` ViewNode → interactive
buttons that fire real turns + re-render, `deos_surface.rs`) are exactly this. The abstractions map onto it, not
beside it — and the code does: an offering's **`Surface` is a deos `ViewNode`/affordance surface**
(`Offering::render` returns exactly that); its **`Action`s are cap-gated affordances** (the `{turn, arg}` shape a
`ViewNode` button fires); a **`Frontend` is an affordance-renderer** (Discord — `deos_surface.rs`; Telegram/WeChat —
built, mapping the same affordances onto inline keyboards / OA numbered replies / a Mini-Program card; web —
`dreggnet-web`, rendering the same `Surface` to HTML forms). The dungeon's ballot buttons are just one
affordance shape. EVERYTHING — offerings AND plain deos cells (dregg-doc, the cockpit, a tally card, a grain view) —
flows through this ONE cap-gated, verifiable, moldable surface, on every frontend. That is the unification: the
offering/session layer sits *above* the deos affordance surface; the frontends are *renderers of affordances*; the
executor is the sole referee on all of them.

## Offerings
- **#0 dungeon (built)** — `dreggnet_offerings::dungeon::DungeonOffering` over the `dungeon_on_dregg` WorldCell +
  the narrator + ballots; the discord-bot drives it.
- **#1 hosted-hermes (built — `dreggnet-hermes`)** — a confined Hermes *agent* session: a per-session
  `AgentRuntime` + session-seed-derived root token, cap-gated tool workers (each a real rate-capped `ToolGateway`);
  the jailed agent produces typed Actions; turns are receipts. The first non-game offering.
- **#2 grain (built — `dreggnet-grain`)** — a Sandstorm-style grain session: the confined app is a cap-gated grain
  turn-cell admitted through the real `grain-turn` R2 minter under a rate-capped `ToolGrant`.
- **The Descent family (built, in-crate)** — `daily_descent` (a drand-beacon-seeded permadeath roguelite with a
  no-cheat leaderboard), `overworld` (verified-clear-gated region traversal), `descent_tournament` (a no-cheat
  bracket over verified runs via `dreggnet-tournament`).
- **web (built — `dreggnet-web`)** — the same offerings, a parallel surface.

## Current state
- The core: `dreggnet-offerings` — the `Offering` + `Frontend` traits, `mock::MockFrontend`, the character system
  (`character`), the `OfferingHost` (`host`), and the session-resume seam (`resume` — a live session re-opened
  from the durable store).
- Frontends: discord-bot (#0) · `dreggnet-telegram` · `dreggnet-wechat` · `dreggnet-web`.
- Offerings: dungeon #0 (in-crate) · `dreggnet-hermes` #1 · `dreggnet-grain` #2 · the Descent family — and the
  wider `dreggnet-*` constellation (~28 crates: market, guild, quest, tournament, tavern, …) rides the same rails.
- Shared underneath, on every surface: the substrate (WorldCell/receipts/verify), payments (`dregg-pay`
  dual-asset), the collective (ballots/quorum).
- Deploy caveat: none of this is hosted as a public service — "DreggNet Cloud" names the shape, not a live
  deployment.
