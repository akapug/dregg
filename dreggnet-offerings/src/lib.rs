//! # DreggNet Cloud — the frontend-agnostic Offering/Session core.
//!
//! The dungeon (`discord-bot/fiction.rs`) is **offering #0** — the first instance of a
//! general pattern: a **confined, verifiable, paid, per-session thing** hosted on the real
//! dregg substrate. This crate extracts that pattern into a reusable [`Offering`] trait and a
//! [`Frontend`] abstraction, so Telegram / WeChat / web frontends and hosted-Hermes / grain
//! offerings plug into ONE core. See `docs/DREGGNET-CLOUD-OFFERINGS.md` (the design).
//!
//! ## The shape every offering shares (proved end-to-end by the dungeon)
//! 1. **A per-session confined thing** — a channel/thread/chat hosts one live session.
//! 2. **A confined intelligence/app** — the dungeon's jailed narrator; elsewhere a hosted
//!    Hermes agent or a Sandstorm grain.
//! 3. **Real verifiable turns** — each input is a real executor turn → a [`TurnReceipt`];
//!    [`Offering::verify`] re-checks the whole chain (the executor is the source of truth — a
//!    jailbroken narration cannot change the world).
//! 4. **Payment-gated** — a paid action debits a run-credit ([`RunCost`]); empty → free tier.
//! 5. **Optionally collective** — write-once ballots + quorum when a crowd drives one session
//!    (the ballot lives one layer up, in the orchestrator/frontend; the core resolves the
//!    *typed [`Action`]* the crowd picked, on the substrate).
//!
//! ## The abstraction
//! An [`Offering`] is `open` / [`actions`](Offering::actions) / [`advance`](Offering::advance)
//! / [`verify`](Offering::verify) / [`render`](Offering::render) / [`price`](Offering::price).
//! Its `render` returns a **deos affordance [`Surface`]** (a [`deos_view::ViewNode`]); its
//! [`Action`]s are **cap-gated affordances** (the `{turn, arg}` shape a `ViewNode` button
//! fires); an [`advance`](Offering::advance) is **one real turn** whose [`Outcome`] is
//! `Landed(TurnReceipt)` or `Refused(reason)` — the same anti-ghost shape the dungeon uses.
//!
//! ## Frontends — Discord is #0; Telegram, WeChat, web are the SAME offerings, different surfaces
//! The offering/session/payment/verify CORE is frontend-agnostic (this crate carries **no**
//! serenity/Discord dependency). A [`Frontend`] is an **affordance-renderer**: it derives a
//! per-platform [`DreggIdentity`], `present`s an offering's [`Surface`] + [`Action`]s, and
//! `collect`s a platform event back into a typed `(SessionId, Action, DreggIdentity)`. The
//! core resolves that action on the substrate; the executor stays the sole referee on every
//! surface. [`mock::MockFrontend`] is the reference renderer the tests drive.

pub mod dungeon;
pub mod mock;

use dregg_app_framework::TurnReceipt;

/// A **deos affordance surface** — the frontend-agnostic, gpui-free serializable view-tree an
/// offering's [`render`](Offering::render) produces. It IS a [`deos_view::ViewNode`] (the doc's
/// mandate: reuse the deos surface, do not reinvent it). Every frontend is a *renderer of this
/// tree* — the native cockpit paints it to gpui widgets, `deos-view`'s `web`/`discord`
/// renderers paint it to HTML / a Discord embed, and [`mock::MockFrontend`] presents it in a
/// test. A newtype (not a bare alias) so it can carry surface-level helpers and read as a
/// first-class Offering concept.
#[derive(Debug, Clone)]
pub struct Surface(pub deos_view::ViewNode);

impl Surface {
    /// The underlying deos view-tree (for a renderer to walk).
    pub fn view(&self) -> &deos_view::ViewNode {
        &self.0
    }
}

/// A **cap-gated affordance** — one candidate move on an offering's surface. It is the deos
/// `{turn, arg}` affordance shape (exactly what a [`deos_view::ViewNode::Button`] /
/// [`deos_view::MenuItem`] fires), so an [`Action`] round-trips through a rendered [`Surface`]:
/// `render` paints an action into a button/menu-row carrying `(turn, arg)`; a [`Frontend`]
/// collects a press of `(turn, arg)` back into the same [`Action`].
///
/// `enabled` is the **cap tooth shown, not hidden**: a currently-ineligible affordance is
/// rendered dimmed (a `!enabled` menu row) rather than removed — but it is only a *decoration*.
/// The executor is the sole referee: firing a `!enabled` (or forged) action still lands as a
/// real [`Outcome::Refused`] on the substrate (the anti-ghost tooth).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Action {
    /// The human label (the button/menu-row text). E.g. `"Press on into the plundered hall"`.
    pub label: String,
    /// The affordance verb — its identity within the surface (the deos analogue of htmx's
    /// `hx-post` path). The dungeon uses `"choose"`; a Hermes offering might use `"prompt"`.
    pub turn: String,
    /// The affordance argument — for the dungeon, the scene choice index within the current
    /// passage (the index [`spween_dregg::WorldCell::apply_choice`] checks the gate case
    /// against). Carried as `i64` to match the deos `ViewNode` `{turn, arg}` wire shape.
    pub arg: i64,
    /// Whether the affordance is currently eligible (its scene/cap condition holds). A
    /// decoration for the surface (`false` → shown dimmed); the executor still refuses an
    /// ineligible move on `advance`.
    pub enabled: bool,
}

impl Action {
    /// A convenience constructor.
    pub fn new(label: impl Into<String>, turn: impl Into<String>, arg: i64, enabled: bool) -> Self {
        Action {
            label: label.into(),
            turn: turn.into(),
            arg,
            enabled,
        }
    }
}

/// The outcome of an [`advance`](Offering::advance) — the same anti-ghost shape the dungeon
/// uses. A legal move commits **one real verified turn** (a [`TurnReceipt`] chained on the
/// session's receipt chain); an illegal one is a real executor refusal — **nothing commits, no
/// receipt** (the anti-ghost tooth). The confined intelligence never decides this: the
/// executor resolves the typed [`Action`] on the substrate, not any prose.
#[derive(Debug, Clone)]
pub enum Outcome {
    /// The move landed as one verified, committed turn — a real [`TurnReceipt`].
    Landed {
        /// The committed turn's receipt (a genuine `turn_hash`, chained pre/post state).
        receipt: TurnReceipt,
        /// Whether this move ended the session (the offering reached a terminal state).
        ended: bool,
    },
    /// The real executor REFUSED the move (an installed gate bit): nothing committed, no
    /// receipt. Carries the executor's own reason.
    Refused(String),
}

impl Outcome {
    /// Did this move land a real receipt?
    pub fn landed(&self) -> bool {
        matches!(self, Outcome::Landed { .. })
    }
}

/// What a paid action costs, in **run-credits**. One credit maps to one
/// `dregg_pay::CreditLedger::debit` (priced at `PayConfig::price_per_run` atomic `$DREGG`, or a
/// flat USDC amount — the dual-asset model). `credits == 0` is the **free tier** (no debit).
///
/// The *substrate turn itself is free and verifiable* on every offering; a `RunCost > 0` prices
/// the offering's **confined intelligence** (the dungeon's Bedrock narration, a hosted-Hermes
/// agent call). The frontend/orchestrator debits the credit against the actor's balance before
/// serving the paid render; the core stays payment-model-agnostic (it names the cost, it does
/// not hold the ledger).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunCost {
    /// Run-credits debited when this action fires (`0` → free tier).
    pub credits: u64,
}

impl RunCost {
    /// The free tier — no credit debited.
    pub const fn free() -> Self {
        RunCost { credits: 0 }
    }

    /// A paid action costing `credits` run-credits.
    pub const fn credits(credits: u64) -> Self {
        RunCost { credits }
    }

    /// Whether this cost debits anything (i.e. is a paid-tier action).
    pub fn is_paid(&self) -> bool {
        self.credits > 0
    }
}

/// The result of [`Offering::verify`] — an offering's own proof that its session's committed
/// chain is honest. For a substrate-backed offering this is the outcome of re-verifying the
/// whole receipt chain **by replay** (re-driving a fresh, identically-seeded confined state
/// through the recorded inputs and confirming it reproduces exactly the committed state chain).
/// A forged / reordered / ineligible input breaks replay.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Whether the session's committed chain re-verifies.
    pub verified: bool,
    /// The number of real verified turns checked (genesis + committed steps).
    pub turns: usize,
    /// A human account — `"re-verified by replay"` on success, or the replay break on failure.
    pub detail: String,
}

impl VerifyReport {
    /// A passing report over `turns` verified turns.
    pub fn ok(turns: usize) -> Self {
        VerifyReport {
            verified: true,
            turns,
            detail: "re-verified by replay".to_string(),
        }
    }

    /// A failing report carrying the break reason.
    pub fn broken(turns: usize, detail: impl Into<String>) -> Self {
        VerifyReport {
            verified: false,
            turns,
            detail: detail.into(),
        }
    }
}

/// Configuration for opening a session. Offering-agnostic; an offering reads the fields it
/// needs (the dungeon uses `seed` for a deterministic, replay-verifiable world identity).
#[derive(Debug, Clone, Default)]
pub struct SessionConfig {
    /// A deterministic session seed — the offering re-derives an identically-seeded confined
    /// state from it when verifying by replay. `None` → the offering's default.
    pub seed: Option<u64>,
}

impl SessionConfig {
    /// A config pinning a deterministic seed.
    pub fn with_seed(seed: u64) -> Self {
        SessionConfig { seed: Some(seed) }
    }
}

/// An error opening an offering session (the confined thing refused to deploy).
#[derive(Debug, Clone)]
pub enum OfferingError {
    /// The confined substrate refused to deploy (carries the reason).
    Deploy(String),
}

impl std::fmt::Display for OfferingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OfferingError::Deploy(why) => write!(f, "offering deploy failed: {why}"),
        }
    }
}

impl std::error::Error for OfferingError {}

/// A **frontend-agnostic dregg identity** — the actor an [`Action`] is attributed to. It is a
/// derived cryptographic identity (an Ed25519 public key hex), NOT a platform nickname: a
/// [`Frontend`] derives it per-platform (Discord from the user's `UserCipherclerk`, Telegram
/// from the Telegram user id, …), and the SAME actor across platforms resolves to the SAME
/// identity iff the derivation inputs match. The core treats it opaquely.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DreggIdentity(pub String);

impl DreggIdentity {
    /// The public-key hex (or other opaque handle) this identity wraps.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A session's identity within a [`Frontend`] — the surface slot a session is presented in (a
/// Discord channel/thread id, a Telegram chat id, a web session token). Opaque to the core.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SessionId(pub String);

impl SessionId {
    /// Wrap a raw session key.
    pub fn new(id: impl Into<String>) -> Self {
        SessionId(id.into())
    }
}

/// **An offering** — a confined, verifiable, paid, per-session thing hosted on the real dregg
/// substrate. Every offering (dungeon #0, hosted-Hermes, a grain) implements this ONE trait;
/// every [`Frontend`] drives it through the SAME six methods.
///
/// The load-bearing invariant: [`advance`](Offering::advance) resolves the typed [`Action`] on
/// the substrate — the executor is the sole referee, never the confined intelligence. A legal
/// move lands a real [`TurnReceipt`]; an illegal one is a real refusal that commits nothing.
pub trait Offering {
    /// The live confined session state (a `WorldCell` playthrough, a Hermes jail, a grain).
    /// Carries a real verifiable state chain.
    type Session;

    /// Open a fresh session (deploy the confined thing, run its genesis turn). The seed in
    /// `cfg` pins a deterministic, replay-verifiable identity.
    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError>;

    /// The candidate moves available in the session's current state — the cap-gated affordances
    /// a frontend renders as buttons/menu-rows (a ballot's options when a crowd drives one).
    fn actions(&self, session: &Self::Session) -> Vec<Action>;

    /// **Advance the session by one real turn.** Resolves `input` on the substrate as ONE
    /// cap-bounded turn attributed to `actor`: a legal move lands a real [`TurnReceipt`]
    /// ([`Outcome::Landed`]); an illegal/ineligible/forged move is a real executor refusal
    /// ([`Outcome::Refused`]) that commits nothing (anti-ghost).
    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome;

    /// Re-verify the session's committed chain (by replay / the offering's own proof).
    fn verify(&self, session: &Self::Session) -> VerifyReport;

    /// Render the session's current state as a **deos affordance [`Surface`]** — room/prose/
    /// state plus the [`actions`](Offering::actions) as cap-gated affordances.
    fn render(&self, session: &Self::Session) -> Surface;

    /// What a paid action costs (run-credits). The free tier is [`RunCost::free`].
    fn price(&self, input: &Action) -> RunCost;
}

/// **A frontend** — an affordance-renderer over the ONE offering core. Discord is #0 (built);
/// Telegram / WeChat / web are more `Frontend` impls mapping the SAME [`Surface`] / [`Action`]s
/// onto inline keyboards / OA-menus / a web DOM. A frontend NEVER trusts a confined
/// intelligence and NEVER re-implements the offering logic: it derives identity, presents the
/// surface, collects a typed action, and hands it to the core.
///
/// This trait is generic over the platform's user + event types (a Discord `ComponentInteraction`,
/// a Telegram `CallbackQuery`, a web POST). The core stays agnostic to them.
pub trait Frontend {
    /// The platform's user handle (a Discord user id, a Telegram user id, a web session user).
    type PlatformUser;
    /// A platform interaction event (a button press, a slash command, a callback query).
    type PlatformEvent;

    /// Derive `user`'s frontend-agnostic [`DreggIdentity`] (per-platform: Discord from the
    /// derived Ed25519 key, Telegram from the user id, …). The SAME actor → the SAME identity.
    fn identity(&self, user: Self::PlatformUser) -> DreggIdentity;

    /// Open a surface slot for `session` (spin a thread/group/chat). Called by the orchestrator
    /// after [`Offering::open`], before the first [`present`](Frontend::present).
    fn spin_session(&mut self, session: SessionId);

    /// Present an offering's [`Surface`] + its [`Action`]s in `session`'s surface slot (paint
    /// the room + the action controls). Idempotent per render — a re-present replaces.
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]);

    /// Collect a platform event into a typed `(SessionId, Action, DreggIdentity)` — a press of
    /// a rendered affordance mapped back to the offering [`Action`] the core resolves. `None`
    /// if the event is not an affordance the frontend presented.
    fn collect(&self, ev: Self::PlatformEvent) -> Option<(SessionId, Action, DreggIdentity)>;

    /// Tear a session's surface down (archive the thread/chat on completion).
    fn teardown(&mut self, session: &SessionId);
}
