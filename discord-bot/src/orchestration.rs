//! The per-session channel/thread lifecycle — DreggNet Cloud's "Midjourney" layer.
//!
//! An *offering* (`docs/DREGGNET-CLOUD-OFFERINGS.md`) is a confined, verifiable,
//! paid, per-session thing: the dungeon is offering #0; hosted-Hermes and grains
//! are next. Every one of them wants the same Discord-side shape, and none of them
//! should have to know how Discord works to get it:
//!
//! > give this session a surface, gate it to the right people, file it with its
//! > siblings, and put it away when the run ends.
//!
//! That is this module. It is **offering-agnostic**: it knows about a
//! [`SessionSpec`], not about dungeons. `fiction.rs` (or a grain, or a hosted
//! Hermes) hands it a spec and gets back a [`LiveSession`] with a channel id.
//!
//! ## What it composes
//!
//! It does not call serenity. It drives [`crate::discord_caps`] — the capability
//! engine — by [`DiscordCapRegistry::register`]ing each guild-write as a cell and
//! then [`DiscordCapRegistry::exercise`]ing it. So a session's surface is spun by
//! *exercising capabilities*, and those capabilities are revoked at teardown; a
//! finished run leaves no live guild-write authority behind.
//!
//! It also closes the other dormant half: the [`EventBridge`]'s `channel_links`
//! map, which nothing ever populated. [`SessionOrchestrator::open`] links the
//! session's channel to the session's dregg queue, so messages posted in a session
//! surface become turns on that session's namespace — and unlinks it at teardown.
//!
//! ## The lifecycle
//!
//! ```text
//!   open(spec)
//!     ├─ authorize            (admin-gated; pure)
//!     ├─ ensure_category      register+exercise CreateCategory   -> category id  (cached per offering)
//!     ├─ surface              register+exercise CreateSessionChannel/Thread -> channel id
//!     ├─ link                 EventBridge::link_channel  (messages here become turns)
//!     ├─ role                 register+exercise AssignRole       (optional, run-scoped)
//!     └─ announce             register+exercise SendMessage      (optional)
//!
//!   teardown(session_id)
//!     ├─ archive              register+exercise ArchiveChannel/ArchiveThread
//!     ├─ role                 register+exercise RemoveRole       (hand the run-scoped role back)
//!     ├─ unlink               EventBridge::unlink_channel
//!     └─ revoke               unregister EVERY cap cell the session held
//! ```
//!
//! ## Pure plan, live drive
//!
//! Every decision — who may open a session, what the surface is called, which
//! capability with which fields, what teardown does — is made by a **pure**
//! `plan_*` / `authorize_*` function. [`SessionOrchestrator::open`] and
//! [`SessionOrchestrator::teardown`] are thin: they run the plan and send it. The
//! tests at the bottom drive the whole lifecycle at the plan level, which is where
//! all the logic actually is; what remains for a live guild is Discord's *response*
//! (whether the bot holds `MANAGE_CHANNELS`, what id gets minted).

use std::collections::HashMap;
use std::sync::Arc;

use serenity::all::Http;
use tokio::sync::RwLock;
use tracing::{info, warn};

use crate::channels;
use crate::discord_caps::{
    ChannelKind, ChannelQueueLink, DiscordCapError, DiscordCapRegistry, DiscordCapability,
    EventBridge, RegisteredDiscordCap,
};

// =============================================================================
// The spec an offering hands in
// =============================================================================

/// Where a session's surface lives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SurfaceKind {
    /// A dedicated channel for this session, optionally filed under the
    /// offering's category. Heavier (it shows in the sidebar), but it can carry
    /// its own permission overwrites — the only way to make a run *semi-private*.
    Channel,
    /// A thread under an existing channel. Lighter, and Discord archives threads
    /// natively — but a thread inherits its parent's permissions, so a private
    /// thread is gated by *membership*, not by an overwrite plan.
    Thread { parent_channel_id: u64 },
}

/// Who is allowed to spin a session surface. Creating channels and assigning roles
/// are guild-write privileges; this is the gate on them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenAuthority {
    /// Only the pinned admin (`config.admin_discord_id`) may open a session. This
    /// is the default, and it matches the offerings doc: *the bot (admin) spins the
    /// channel*. Note this DENIES when no admin is pinned — an unset
    /// `ADMIN_DISCORD_ID` must not silently mean "anyone may create channels".
    AdminOnly,
    /// The admin, or a user opening a session that they themselves own. This is the
    /// posture `/channel` already has (any user may claim their OWN channel), for
    /// offerings that want self-service.
    AdminOrSelfOwner,
}

/// What an offering asks the orchestrator for. Offering-agnostic: `offering` is
/// just a name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionSpec {
    /// The offering this session belongs to (`"dungeon"`, `"hosted-hermes"`, …).
    /// Sessions of one offering share a category and a queue namespace.
    pub offering: String,
    /// This session's id, unique within the offering.
    pub session_id: String,
    pub guild_id: u64,
    /// Who is asking for the session to be opened (the gate is applied to them).
    pub requested_by: u64,
    /// Whose session it is — gets access when the surface is private.
    pub owner_id: u64,
    /// The pinned admin, from `config.admin_discord_id`. Both the authority the
    /// gate checks against AND the party granted visibility into every session.
    pub admin_id: Option<u64>,
    pub authority: OpenAuthority,
    pub surface: SurfaceKind,
    /// `true` = semi-private (deny `@everyone` VIEW). `false` = a collective run
    /// the whole guild can watch.
    pub private: bool,
    /// File this session under the offering's category (minted on first use and
    /// reused thereafter). Ignored for threads — a thread's parent is its channel.
    pub group_under_category: bool,
    /// Where completed runs are re-filed. `None` = archive in place.
    pub archive_category_id: Option<u64>,
    /// A run-scoped role granted to the owner at open and handed BACK at teardown.
    pub role_id: Option<u64>,
    /// Link the surface to a dregg queue, so messages in it become turns
    /// (populates [`EventBridge`]'s links). `None` = no bridging.
    pub queue_name: Option<String>,
    /// Posted into the surface once it exists.
    pub announce: Option<String>,
    pub topic: Option<String>,
}

impl SessionSpec {
    /// A private, admin-gated, category-grouped **channel** session — the default
    /// posture, and the one the dungeon wants.
    pub fn new(
        offering: impl Into<String>,
        session_id: impl Into<String>,
        guild_id: u64,
        requested_by: u64,
        owner_id: u64,
    ) -> Self {
        Self {
            offering: offering.into(),
            session_id: session_id.into(),
            guild_id,
            requested_by,
            owner_id,
            admin_id: None,
            authority: OpenAuthority::AdminOnly,
            surface: SurfaceKind::Channel,
            private: true,
            group_under_category: true,
            archive_category_id: None,
            role_id: None,
            queue_name: None,
            announce: None,
            topic: None,
        }
    }

    /// Pin the admin (`config.admin_discord_id`) — the open-gate authority AND the
    /// party who sees every session.
    pub fn admin(mut self, admin_id: Option<u64>) -> Self {
        self.admin_id = admin_id;
        self
    }

    pub fn authority(mut self, authority: OpenAuthority) -> Self {
        self.authority = authority;
        self
    }

    /// Host this session in a thread under `parent_channel_id` instead of its own
    /// channel.
    pub fn in_thread(mut self, parent_channel_id: u64) -> Self {
        self.surface = SurfaceKind::Thread { parent_channel_id };
        self
    }

    /// A collective run the whole guild can watch.
    pub fn public(mut self) -> Self {
        self.private = false;
        self
    }

    pub fn role(mut self, role_id: Option<u64>) -> Self {
        self.role_id = role_id;
        self
    }

    pub fn queue(mut self, queue_name: impl Into<String>) -> Self {
        self.queue_name = Some(queue_name.into());
        self
    }

    pub fn announce(mut self, announce: impl Into<String>) -> Self {
        self.announce = Some(announce.into());
        self
    }

    pub fn topic(mut self, topic: impl Into<String>) -> Self {
        self.topic = Some(topic.into());
        self
    }

    pub fn archive_category(mut self, category_id: Option<u64>) -> Self {
        self.archive_category_id = category_id;
        self
    }

    /// The globally-unique key for this session.
    pub fn key(&self) -> String {
        format!("{}/{}", self.offering, self.session_id)
    }

    /// The name of this session's surface (Discord-normalized).
    pub fn surface_name(&self) -> String {
        channels::session_surface_name(&self.offering, &self.session_id)
    }

    /// The dregg namespace a message in this surface becomes a turn on.
    pub fn namespace_path(&self) -> String {
        format!(
            "/discord/{}/sessions/{}/{}",
            self.guild_id, self.offering, self.session_id
        )
    }
}

// =============================================================================
// The pure plan
// =============================================================================

/// One guild-write the orchestrator will register-then-exercise: the cell it is
/// registered under, and the capability itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlannedCap {
    pub cell_id: String,
    pub capability: DiscordCapability,
}

/// The cell id a session's `action` capability is registered under. Deterministic
/// and session-scoped, so two concurrent runs of one offering never collide, and a
/// session's cells are enumerable at teardown.
pub fn cell_id_for(offering: &str, session_id: &str, action: &str) -> String {
    format!("discord/session/{offering}/{session_id}/{action}")
}

/// May `spec.requested_by` open this session? Pure — the whole gate.
pub fn authorize_open(spec: &SessionSpec) -> Result<(), OrchestrationError> {
    let is_admin = spec.admin_id == Some(spec.requested_by);
    let allowed = match spec.authority {
        // No admin pinned => nobody is the admin => denied. An unset
        // ADMIN_DISCORD_ID must not read as "everyone is admin".
        OpenAuthority::AdminOnly => is_admin,
        OpenAuthority::AdminOrSelfOwner => is_admin || spec.requested_by == spec.owner_id,
    };
    if allowed {
        Ok(())
    } else {
        Err(OrchestrationError::Unauthorized {
            requested_by: spec.requested_by,
        })
    }
}

/// The cell a per-(guild, offering) category is minted under. Shared by every run
/// of an offering — NOT per-session — so the second run reuses the first's category
/// instead of stacking duplicates, and a `guild_create` bootstrap mints the SAME
/// cell a later session reuses.
pub fn offering_category_cell(guild_id: u64, offering: &str) -> String {
    format!("discord/category/{guild_id}/{offering}")
}

/// The CATEGORY write for an offering, independent of any one session. This is the
/// single definition of "the offering's category": both [`plan_category`] (open
/// path) and [`plan_bootstrap`] (guild_create path) go through it, so the category
/// a bootstrap prepares is byte-for-byte the one an `open()` files its session
/// under.
pub fn plan_offering_category(guild_id: u64, offering: &str) -> PlannedCap {
    PlannedCap {
        cell_id: offering_category_cell(guild_id, offering),
        capability: DiscordCapability::CreateCategory {
            guild_id,
            name: channels::category_name_for(offering),
        },
    }
}

/// The CATEGORY this offering's sessions are filed under, if it groups them.
/// `None` for a thread session (its parent is its channel) or when grouping is off.
pub fn plan_category(spec: &SessionSpec) -> Option<PlannedCap> {
    if !spec.group_under_category || matches!(spec.surface, SurfaceKind::Thread { .. }) {
        return None;
    }
    Some(plan_offering_category(spec.guild_id, &spec.offering))
}

/// The session's SURFACE, given the resolved parent category (`None` = top-level,
/// or a thread). This is the child half of the category/child plan.
pub fn plan_surface(spec: &SessionSpec, category_id: Option<u64>) -> PlannedCap {
    let cell_id = cell_id_for(&spec.offering, &spec.session_id, "surface");
    let name = spec.surface_name();

    let capability = match spec.surface {
        SurfaceKind::Thread { parent_channel_id } => DiscordCapability::CreateSessionThread {
            channel_id: parent_channel_id,
            name,
            private: spec.private,
        },
        SurfaceKind::Channel => DiscordCapability::CreateSessionChannel {
            guild_id: spec.guild_id,
            name,
            kind: ChannelKind::Text,
            topic: spec.topic.clone(),
            category_id,
            owner_id: spec.owner_id,
            admin_id: spec.admin_id,
            private: spec.private,
        },
    };

    PlannedCap {
        cell_id,
        capability,
    }
}

/// Everything that can only be planned once the surface EXISTS and its id is known.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PostOpenPlan {
    /// The run-scoped role granted to the owner.
    pub role: Option<PlannedCap>,
    /// The opening message posted into the surface.
    pub announce: Option<PlannedCap>,
    /// The queue link that makes messages in this surface into dregg turns.
    pub queue_link: Option<ChannelQueueLink>,
}

/// Plan the post-creation steps for a session whose surface is `channel_id`.
pub fn plan_post_open(spec: &SessionSpec, channel_id: u64) -> PostOpenPlan {
    PostOpenPlan {
        role: spec.role_id.map(|role_id| PlannedCap {
            cell_id: cell_id_for(&spec.offering, &spec.session_id, "role"),
            capability: DiscordCapability::AssignRole {
                guild_id: spec.guild_id,
                user_id: spec.owner_id,
                role_id,
            },
        }),
        announce: spec.announce.as_ref().map(|content| PlannedCap {
            cell_id: cell_id_for(&spec.offering, &spec.session_id, "announce"),
            capability: DiscordCapability::SendMessage {
                channel_id,
                content: content.clone(),
            },
        }),
        queue_link: spec.queue_name.as_ref().map(|queue_name| ChannelQueueLink {
            channel_id,
            guild_id: spec.guild_id,
            queue_name: queue_name.clone(),
            namespace_path: spec.namespace_path(),
        }),
    }
}

/// The teardown of a session whose surface is `channel_id`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TeardownPlan {
    /// Archive the surface (thread: archive+lock; channel: rename, re-file,
    /// read-only tombstone).
    pub archive: PlannedCap,
    /// Hand the run-scoped role BACK. A role granted for the duration of a run that
    /// outlives the run is a lingering grant.
    pub role: Option<PlannedCap>,
}

/// Plan the teardown. Pure.
pub fn plan_teardown(spec: &SessionSpec, channel_id: u64) -> TeardownPlan {
    let archive_cap = match spec.surface {
        SurfaceKind::Thread { .. } => DiscordCapability::ArchiveThread { channel_id },
        SurfaceKind::Channel => DiscordCapability::ArchiveChannel {
            guild_id: spec.guild_id,
            channel_id,
            archived_name: channels::archived_name_for(&spec.surface_name()),
            owner_id: spec.owner_id,
            admin_id: spec.admin_id,
            archive_category_id: spec.archive_category_id,
        },
    };

    TeardownPlan {
        archive: PlannedCap {
            cell_id: cell_id_for(&spec.offering, &spec.session_id, "archive"),
            capability: archive_cap,
        },
        role: spec.role_id.map(|role_id| PlannedCap {
            cell_id: cell_id_for(&spec.offering, &spec.session_id, "role-release"),
            capability: DiscordCapability::RemoveRole {
                guild_id: spec.guild_id,
                user_id: spec.owner_id,
                role_id,
            },
        }),
    }
}

// =============================================================================
// The guild-create bootstrap: what a guild needs BEFORE any session opens
// =============================================================================

/// What must be in place in a guild BEFORE the first session of an offering can
/// open: the per-offering CATEGORY its runs are filed under, and the base role ids
/// its sessions grant. A `guild_create` handler ensures this the moment the bot
/// joins (or restarts against) a guild, so the first `/dungeon` neither pays the
/// category-mint round-trip on the user's critical path nor lands its channel
/// un-filed.
///
/// Offering-agnostic, exactly like [`SessionSpec`]: `offering` is just a name, and
/// the dungeon, hosted-Hermes and grains all bootstrap the same way.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OfferingBootstrap {
    pub offering: String,
    pub guild_id: u64,
    /// Who the bootstrap's guild-writes are attributed to in the audit log — the
    /// bot/admin acting on `guild_create`, not any end user.
    pub registered_by: u64,
    /// Mint-if-absent the per-offering category. `false` for a threads-only
    /// offering, whose sessions live under an existing channel rather than a
    /// category (see [`SurfaceKind::Thread`]).
    pub ensure_category: bool,
    /// The base role ids this offering's sessions assign at open. Bootstrap RECORDS
    /// them (so a handler can verify them against the live guild's role list); it
    /// deliberately does NOT mint them. Role *creation* would need a `CreateRole`
    /// [`DiscordCapability`] the engine does not expose, and driving
    /// `serenity`'s `create_role` directly would break this layer's invariant that
    /// the ONE place a guild write happens is [`DiscordCapRegistry::exercise`]. A
    /// base role that does not already exist surfaces at `AssignRole` time, per run.
    pub base_role_ids: Vec<u64>,
}

impl OfferingBootstrap {
    /// A category-grouped offering bootstrap — the default, and what the dungeon
    /// wants (one `dreggnet-dungeon` category holding every run).
    pub fn new(offering: impl Into<String>, guild_id: u64, registered_by: u64) -> Self {
        Self {
            offering: offering.into(),
            guild_id,
            registered_by,
            ensure_category: true,
            base_role_ids: Vec::new(),
        }
    }

    /// A threads-only offering: its sessions open under an existing channel, so
    /// there is no per-offering category to prepare.
    pub fn without_category(mut self) -> Self {
        self.ensure_category = false;
        self
    }

    /// Declare the base role ids this offering's sessions grant (recorded, not
    /// minted — see [`OfferingBootstrap::base_role_ids`]).
    pub fn base_roles(mut self, ids: impl IntoIterator<Item = u64>) -> Self {
        self.base_role_ids = ids.into_iter().collect();
        self
    }
}

/// The one guild-write a bootstrap drives — the per-offering category — or `None`
/// for a threads-only offering that files nothing under a category. Pure, and it
/// resolves to the SAME [`PlannedCap`] a later [`plan_category`] does, so bootstrap
/// and open agree on one category per offering.
pub fn plan_bootstrap(spec: &OfferingBootstrap) -> Option<PlannedCap> {
    if !spec.ensure_category {
        return None;
    }
    Some(plan_offering_category(spec.guild_id, &spec.offering))
}

/// What a bootstrap prepared for an offering in a guild.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BootstrapReport {
    pub offering: String,
    pub guild_id: u64,
    /// The category every session of this offering will be filed under — minted
    /// here if absent, then cached so the first session reuses it. `None` for a
    /// threads-only offering.
    pub category_id: Option<u64>,
    /// The base role ids the offering declared (recorded, not minted — see
    /// [`OfferingBootstrap::base_role_ids`]).
    pub base_role_ids: Vec<u64>,
}

// =============================================================================
// The live session
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionState {
    Open,
    Archived,
}

/// A session whose surface exists.
#[derive(Debug, Clone)]
pub struct LiveSession {
    pub spec: SessionSpec,
    /// The channel or thread hosting the session.
    pub channel_id: u64,
    /// The category it is filed under, if any.
    pub category_id: Option<u64>,
    pub state: SessionState,
    /// Every capability cell this session holds — revoked at teardown.
    pub cap_cells: Vec<String>,
    pub opened_at: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OrchestrationError {
    /// The requester may not open sessions (see [`OpenAuthority`]).
    Unauthorized { requested_by: u64 },
    /// No such session.
    UnknownSession(String),
    /// The session is already archived.
    AlreadyArchived(String),
    /// A guild write failed.
    Discord(DiscordCapError),
    /// Discord accepted a create but returned no id — should not happen; treated as
    /// a hard failure rather than papered over with a 0.
    NoIdReturned(String),
}

impl std::fmt::Display for OrchestrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrchestrationError::Unauthorized { requested_by } => write!(
                f,
                "user {requested_by} may not open sessions here (admin-gated)"
            ),
            OrchestrationError::UnknownSession(k) => write!(f, "unknown session: {k}"),
            OrchestrationError::AlreadyArchived(k) => write!(f, "session already archived: {k}"),
            OrchestrationError::Discord(e) => write!(f, "discord: {e}"),
            OrchestrationError::NoIdReturned(what) => {
                write!(f, "Discord created a {what} but returned no id")
            }
        }
    }
}

impl std::error::Error for OrchestrationError {}

impl From<DiscordCapError> for OrchestrationError {
    fn from(e: DiscordCapError) -> Self {
        OrchestrationError::Discord(e)
    }
}

/// The session→surface lifecycle, shared by every offering.
///
/// Hold ONE of these on `BotState` (see the module docs for the wiring the main
/// loop owns). It keeps the live session table and the per-offering category
/// cache; the capability registry and the event bridge are passed in, because they
/// already live on `BotState` too.
#[derive(Debug, Default)]
pub struct SessionOrchestrator {
    /// `spec.key()` -> the live session.
    sessions: RwLock<HashMap<String, LiveSession>>,
    /// `(guild_id, offering)` -> the category every session of that offering is
    /// filed under. Cached so the second run of an offering REUSES the first run's
    /// category instead of minting a duplicate.
    categories: RwLock<HashMap<(u64, String), u64>>,
}

impl SessionOrchestrator {
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up a live session.
    pub async fn get(&self, key: &str) -> Option<LiveSession> {
        self.sessions.read().await.get(key).cloned()
    }

    /// Every session of an offering (open and archived).
    pub async fn list_for_offering(&self, offering: &str) -> Vec<LiveSession> {
        self.sessions
            .read()
            .await
            .values()
            .filter(|s| s.spec.offering == offering)
            .cloned()
            .collect()
    }

    /// Pre-seed a known category (an offering whose category already exists in the
    /// guild), so the orchestrator does not mint a second one.
    pub async fn seed_category(&self, guild_id: u64, offering: &str, category_id: u64) {
        self.categories
            .write()
            .await
            .insert((guild_id, offering.to_string()), category_id);
    }

    /// OPEN a session: spin its surface, gate it, link it, announce it.
    ///
    /// Idempotent — re-opening a live session returns the existing one rather than
    /// minting a second channel (the same posture `/channel` has).
    pub async fn open(
        &self,
        spec: SessionSpec,
        caps: &DiscordCapRegistry,
        bridge: &EventBridge,
        http: &Arc<Http>,
    ) -> Result<LiveSession, OrchestrationError> {
        authorize_open(&spec)?;

        let key = spec.key();
        if let Some(existing) = self.get(&key).await {
            if existing.state == SessionState::Open {
                return Ok(existing);
            }
        }

        let mut cap_cells = Vec::new();

        // 1. The offering's category (minted once, then reused).
        let category_id = self.ensure_category(&spec, caps, http).await?;

        // 2. The surface itself.
        let surface = plan_surface(&spec, category_id);
        let channel_id = self
            .drive(caps, http, &surface, &spec)
            .await?
            .ok_or_else(|| OrchestrationError::NoIdReturned("session surface".into()))?;
        cap_cells.push(surface.cell_id.clone());

        // 3. Everything that needed the surface to exist first.
        let post = plan_post_open(&spec, channel_id);

        // The link that makes a message in this surface a dregg turn. This is the
        // map nothing ever populated.
        if let Some(link) = post.queue_link {
            bridge.link_channel(link).await;
        }

        if let Some(role) = &post.role {
            self.drive(caps, http, role, &spec).await?;
            cap_cells.push(role.cell_id.clone());
        }
        if let Some(announce) = &post.announce {
            self.drive(caps, http, announce, &spec).await?;
            cap_cells.push(announce.cell_id.clone());
        }

        let session = LiveSession {
            spec,
            channel_id,
            category_id,
            state: SessionState::Open,
            cap_cells,
            opened_at: now_secs(),
        };
        self.sessions
            .write()
            .await
            .insert(key.clone(), session.clone());

        info!(
            session = %key,
            channel_id,
            ?category_id,
            "Opened session surface"
        );
        Ok(session)
    }

    /// TEAR DOWN a session: archive the surface, hand back the run-scoped role,
    /// unlink the queue, and REVOKE every capability cell the session held.
    ///
    /// The revocation is the part that matters: a finished run must not leave a
    /// live `CreateChannel`/`AssignRole` cell lying in the registry for someone to
    /// exercise later.
    pub async fn teardown(
        &self,
        key: &str,
        caps: &DiscordCapRegistry,
        bridge: &EventBridge,
        http: &Arc<Http>,
    ) -> Result<LiveSession, OrchestrationError> {
        let mut session = self
            .get(key)
            .await
            .ok_or_else(|| OrchestrationError::UnknownSession(key.to_string()))?;
        if session.state == SessionState::Archived {
            return Err(OrchestrationError::AlreadyArchived(key.to_string()));
        }

        let plan = plan_teardown(&session.spec, session.channel_id);

        self.drive(caps, http, &plan.archive, &session.spec).await?;
        if let Some(role) = &plan.role {
            self.drive(caps, http, role, &session.spec).await?;
        }

        // Stop turning messages in the archived surface into turns.
        bridge.unlink_channel(session.channel_id).await;

        // Revoke every cell this session held, including the teardown cells.
        for cell in session
            .cap_cells
            .iter()
            .chain(std::iter::once(&plan.archive.cell_id))
            .chain(plan.role.iter().map(|c| &c.cell_id))
        {
            caps.unregister(cell).await;
        }
        // NOTE: the CATEGORY cell is deliberately NOT revoked — it is shared by
        // every session of the offering, and the next run reuses it.

        session.state = SessionState::Archived;
        session.cap_cells.clear();
        self.sessions
            .write()
            .await
            .insert(key.to_string(), session.clone());

        info!(session = %key, channel_id = session.channel_id, "Archived session surface");
        Ok(session)
    }

    /// GUILD-CREATE BOOTSTRAP for one offering: ensure everything it needs in a
    /// guild BEFORE its first session opens. Drives the per-offering category live
    /// (mint-if-absent, then cache) so a later `open()` finds it ready. Idempotent:
    /// a second bootstrap of an offering whose category is already cached mints
    /// nothing and issues no guild-write.
    ///
    /// A `guild_create` handler calls this for every offering the guild hosts. Base
    /// roles are recorded, not minted (see [`OfferingBootstrap::base_role_ids`]).
    pub async fn bootstrap_offering(
        &self,
        spec: &OfferingBootstrap,
        caps: &DiscordCapRegistry,
        http: &Arc<Http>,
    ) -> Result<BootstrapReport, OrchestrationError> {
        let category_id = if spec.ensure_category {
            Some(
                self.ensure_offering_category(
                    spec.guild_id,
                    &spec.offering,
                    caps,
                    http,
                    spec.registered_by,
                )
                .await?,
            )
        } else {
            None
        };

        info!(
            offering = %spec.offering,
            guild_id = spec.guild_id,
            ?category_id,
            base_roles = spec.base_role_ids.len(),
            "Bootstrapped offering"
        );
        Ok(BootstrapReport {
            offering: spec.offering.clone(),
            guild_id: spec.guild_id,
            category_id,
            base_role_ids: spec.base_role_ids.clone(),
        })
    }

    /// GUILD-CREATE BOOTSTRAP for a whole guild — every offering it hosts, in one
    /// call from the `guild_create` handler. Fails fast on the first offering that
    /// cannot be prepared, so a guild the bot lacks `MANAGE_CHANNELS` in surfaces
    /// the error rather than silently half-preparing.
    pub async fn bootstrap_guild(
        &self,
        specs: &[OfferingBootstrap],
        caps: &DiscordCapRegistry,
        http: &Arc<Http>,
    ) -> Result<Vec<BootstrapReport>, OrchestrationError> {
        let mut reports = Vec::with_capacity(specs.len());
        for spec in specs {
            reports.push(self.bootstrap_offering(spec, caps, http).await?);
        }
        Ok(reports)
    }

    /// Resolve this offering's category for a session, minting it on first use.
    async fn ensure_category(
        &self,
        spec: &SessionSpec,
        caps: &DiscordCapRegistry,
        http: &Arc<Http>,
    ) -> Result<Option<u64>, OrchestrationError> {
        // A thread session or an ungrouped one files under no category.
        if plan_category(spec).is_none() {
            return Ok(None);
        }
        let id = self
            .ensure_offering_category(spec.guild_id, &spec.offering, caps, http, spec.requested_by)
            .await?;
        Ok(Some(id))
    }

    /// Resolve (mint-if-absent) the per-offering category and cache it. The single
    /// place a category is minted — shared by the open path and the guild_create
    /// bootstrap, so both consult and populate the SAME cache and neither mints a
    /// duplicate. A cache hit returns without touching the guild at all.
    async fn ensure_offering_category(
        &self,
        guild_id: u64,
        offering: &str,
        caps: &DiscordCapRegistry,
        http: &Arc<Http>,
        registered_by: u64,
    ) -> Result<u64, OrchestrationError> {
        let cache_key = (guild_id, offering.to_string());
        if let Some(id) = self.categories.read().await.get(&cache_key) {
            return Ok(*id);
        }

        let planned = plan_offering_category(guild_id, offering);
        let id = self
            .drive_cap(caps, http, &planned, guild_id, registered_by)
            .await?
            .ok_or_else(|| OrchestrationError::NoIdReturned("category".into()))?;
        self.categories.write().await.insert(cache_key, id);
        Ok(id)
    }

    /// Register a planned capability and exercise it, attributed to this session's
    /// requester — the one place this layer touches the guild.
    async fn drive(
        &self,
        caps: &DiscordCapRegistry,
        http: &Arc<Http>,
        planned: &PlannedCap,
        spec: &SessionSpec,
    ) -> Result<Option<u64>, OrchestrationError> {
        self.drive_cap(caps, http, planned, spec.guild_id, spec.requested_by)
            .await
    }

    /// Register a planned capability and exercise it — the primitive both the
    /// session path (`drive`) and the guild_create bootstrap go through. Returns the
    /// id Discord minted, if any. A write that does not land leaves no cell behind.
    async fn drive_cap(
        &self,
        caps: &DiscordCapRegistry,
        http: &Arc<Http>,
        planned: &PlannedCap,
        guild_id: u64,
        registered_by: u64,
    ) -> Result<Option<u64>, OrchestrationError> {
        caps.register(RegisteredDiscordCap {
            cell_id: planned.cell_id.clone(),
            uri: None,
            capability: planned.capability.clone(),
            guild_id,
            registered_by,
        })
        .await;

        match caps.exercise(&planned.cell_id, http).await {
            Ok(outcome) => Ok(outcome.created_id),
            Err(e) => {
                warn!(cell = %planned.cell_id, error = %e, "Guild-write failed");
                // Do not leave a cell registered for a write that did not land.
                caps.unregister(&planned.cell_id).await;
                Err(e.into())
            }
        }
    }
}

fn now_secs() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// =============================================================================
// Tests — the lifecycle, driven at the level where the logic lives
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use serenity::all::{ChannelId, Permissions, RoleId, UserId};

    const GUILD: u64 = 1111;
    const ADMIN: u64 = 3333;
    const PLAYER: u64 = 2222;
    const CATEGORY: u64 = 4444;
    const CHANNEL: u64 = 5555;
    const ROLE: u64 = 6666;

    /// The dungeon's spec: a private, admin-gated, category-grouped channel run
    /// with a run-scoped role, a queue link and an announcement.
    fn dungeon_spec() -> SessionSpec {
        SessionSpec::new("dungeon", "a1b2c3", GUILD, ADMIN, PLAYER)
            .admin(Some(ADMIN))
            .role(Some(ROLE))
            .queue("dungeon-run")
            .announce("The dungeon awakens.")
            .topic("a dungeon run")
    }

    // ─── the gate ────────────────────────────────────────────────────────────

    #[test]
    fn admin_may_open_a_session() {
        assert_eq!(authorize_open(&dungeon_spec()), Ok(()));
    }

    #[test]
    fn a_non_admin_may_not_open_an_admin_only_session() {
        let mut spec = dungeon_spec();
        spec.requested_by = PLAYER; // the player asks for their own run...
        assert_eq!(
            authorize_open(&spec),
            Err(OrchestrationError::Unauthorized {
                requested_by: PLAYER
            }),
            "AdminOnly means AdminOnly, even for the session's own owner"
        );
    }

    #[test]
    fn self_service_lets_the_owner_open_their_own_session_only() {
        let mut spec = dungeon_spec().authority(OpenAuthority::AdminOrSelfOwner);
        spec.requested_by = PLAYER;
        assert_eq!(authorize_open(&spec), Ok(()), "owner opens their own run");

        // ...but a THIRD party still may not open a session on someone else's behalf.
        spec.requested_by = 9999;
        assert_eq!(
            authorize_open(&spec),
            Err(OrchestrationError::Unauthorized { requested_by: 9999 })
        );
    }

    #[test]
    fn an_unpinned_admin_does_not_mean_everyone_is_admin() {
        // The footgun: ADMIN_DISCORD_ID unset. `admin_id: None` must not compare
        // equal to "the requester is the admin".
        let spec = dungeon_spec().admin(None);
        assert_eq!(
            authorize_open(&spec),
            Err(OrchestrationError::Unauthorized {
                requested_by: ADMIN
            }),
            "with no admin pinned, AdminOnly must DENY, not open the guild up"
        );
    }

    // ─── the category / child plan ───────────────────────────────────────────

    #[test]
    fn the_category_child_plan_is_well_formed() {
        let spec = dungeon_spec();

        // The parent: one category per offering, named for the offering.
        let category = plan_category(&spec).expect("a grouped offering plans a category");
        assert_eq!(category.cell_id, "discord/category/1111/dungeon");
        assert_eq!(
            category.capability,
            DiscordCapability::CreateCategory {
                guild_id: GUILD,
                name: "dreggnet-dungeon".into(),
            }
        );

        // The child: the session channel, filed under the category id the parent
        // minted, and gated to owner + admin.
        let surface = plan_surface(&spec, Some(CATEGORY));
        assert_eq!(surface.cell_id, "discord/session/dungeon/a1b2c3/surface");
        assert_eq!(
            surface.capability,
            DiscordCapability::CreateSessionChannel {
                guild_id: GUILD,
                name: "dungeon-a1b2c3".into(),
                kind: ChannelKind::Text,
                topic: Some("a dungeon run".into()),
                category_id: Some(CATEGORY),
                owner_id: PLAYER,
                admin_id: Some(ADMIN),
                private: true,
            }
        );
    }

    #[test]
    fn the_planned_session_channel_produces_the_gated_serenity_request() {
        // The plan is only as good as the request it becomes. Drive the planned
        // capability all the way to the body `exercise()` would send.
        let spec = dungeon_spec();
        let DiscordCapability::CreateSessionChannel {
            name,
            kind,
            topic,
            category_id,
            guild_id,
            owner_id,
            admin_id,
            private,
        } = plan_surface(&spec, Some(CATEGORY)).capability
        else {
            panic!("a channel session plans a CreateSessionChannel");
        };

        let overwrites =
            crate::discord_caps::session_overwrites(guild_id, owner_id, admin_id, private);
        let req = crate::discord_caps::build_session_channel_request(
            &name,
            &kind,
            topic.as_deref(),
            category_id,
            overwrites,
            "r",
        );
        let body = serde_json::to_value(&req).unwrap();

        assert_eq!(body["name"], "dungeon-a1b2c3");
        assert_eq!(
            body["parent_id"],
            serde_json::to_value(ChannelId::new(CATEGORY)).unwrap()
        );

        let ovr = body["permission_overwrites"].as_array().unwrap();
        assert_eq!(ovr.len(), 3);
        // @everyone (role id == guild id) denied VIEW_CHANNEL.
        let everyone = ovr
            .iter()
            .find(|o| o["id"] == serde_json::to_value(RoleId::new(GUILD)).unwrap())
            .expect("@everyone is on the plan");
        assert_eq!(
            everyone["deny"],
            serde_json::to_value(Permissions::VIEW_CHANNEL).unwrap()
        );
        // The player and the admin may both view + post.
        for who in [PLAYER, ADMIN] {
            let m = ovr
                .iter()
                .find(|o| o["id"] == serde_json::to_value(UserId::new(who)).unwrap())
                .expect("a participant overwrite");
            assert_eq!(
                m["allow"],
                serde_json::to_value(
                    Permissions::VIEW_CHANNEL
                        | Permissions::SEND_MESSAGES
                        | Permissions::READ_MESSAGE_HISTORY
                )
                .unwrap()
            );
        }
    }

    #[test]
    fn a_thread_session_plans_no_category_and_a_thread_surface() {
        let spec = dungeon_spec().in_thread(7777);
        assert!(
            plan_category(&spec).is_none(),
            "a thread's parent is its channel, not a category"
        );
        assert_eq!(
            plan_surface(&spec, None).capability,
            DiscordCapability::CreateSessionThread {
                channel_id: 7777,
                name: "dungeon-a1b2c3".into(),
                private: true,
            }
        );
    }

    #[test]
    fn an_ungrouped_session_plans_no_category_and_a_top_level_channel() {
        let mut spec = dungeon_spec();
        spec.group_under_category = false;
        assert!(plan_category(&spec).is_none());
        let DiscordCapability::CreateSessionChannel { category_id, .. } =
            plan_surface(&spec, None).capability
        else {
            panic!("expected a channel");
        };
        assert_eq!(category_id, None);
    }

    // ─── post-open: the role, the announce, and the queue LINK ───────────────

    #[test]
    fn post_open_assigns_the_role_announces_and_links_the_queue() {
        let spec = dungeon_spec();
        let post = plan_post_open(&spec, CHANNEL);

        assert_eq!(
            post.role.unwrap().capability,
            DiscordCapability::AssignRole {
                guild_id: GUILD,
                user_id: PLAYER,
                role_id: ROLE,
            },
            "the run-scoped role goes to the session's OWNER, not the admin who opened it"
        );

        let announce = post.announce.expect("an announce was requested");
        assert_eq!(announce.cell_id, "discord/session/dungeon/a1b2c3/announce");
        assert_eq!(
            announce.capability,
            DiscordCapability::SendMessage {
                channel_id: CHANNEL, // the surface that did not exist at plan time
                content: "The dungeon awakens.".into(),
            }
        );

        // The EventBridge link — the map that nothing populated before.
        let link = post.queue_link.expect("a queue was requested");
        assert_eq!(link.channel_id, CHANNEL);
        assert_eq!(link.guild_id, GUILD);
        assert_eq!(link.queue_name, "dungeon-run");
        assert_eq!(
            link.namespace_path, "/discord/1111/sessions/dungeon/a1b2c3",
            "messages in the surface become turns on THIS session's namespace"
        );
    }

    #[test]
    fn a_spec_that_asks_for_nothing_extra_plans_nothing_extra() {
        let spec = SessionSpec::new("grain", "g1", GUILD, ADMIN, PLAYER).admin(Some(ADMIN));
        let post = plan_post_open(&spec, CHANNEL);
        assert!(post.role.is_none());
        assert!(post.announce.is_none());
        assert!(post.queue_link.is_none(), "no queue => no bridge link");
    }

    // ─── teardown ────────────────────────────────────────────────────────────

    #[test]
    fn tearing_down_a_channel_session_is_well_formed() {
        let spec = dungeon_spec().archive_category(Some(8888));
        let plan = plan_teardown(&spec, CHANNEL);

        assert_eq!(
            plan.archive.cell_id,
            "discord/session/dungeon/a1b2c3/archive"
        );
        assert_eq!(
            plan.archive.capability,
            DiscordCapability::ArchiveChannel {
                guild_id: GUILD,
                channel_id: CHANNEL,
                archived_name: "archived-dungeon-a1b2c3".into(),
                owner_id: PLAYER,
                admin_id: Some(ADMIN),
                archive_category_id: Some(8888),
            }
        );

        // The run-scoped role is handed BACK — the grant does not outlive the run.
        assert_eq!(
            plan.role.expect("the role is released").capability,
            DiscordCapability::RemoveRole {
                guild_id: GUILD,
                user_id: PLAYER,
                role_id: ROLE,
            }
        );
    }

    #[test]
    fn tearing_down_a_thread_session_archives_the_thread() {
        let spec = dungeon_spec().in_thread(7777).role(None);
        let plan = plan_teardown(&spec, CHANNEL);
        assert_eq!(
            plan.archive.capability,
            DiscordCapability::ArchiveThread {
                channel_id: CHANNEL
            }
        );
        assert!(plan.role.is_none());
    }

    #[test]
    fn the_teardown_archive_name_matches_the_name_the_surface_was_created_with() {
        // The teardown renames the channel it created — so the archived name must be
        // derived from the SAME surface name the open plan used, or teardown renames
        // a channel that never existed under that name.
        let spec = dungeon_spec();
        let DiscordCapability::CreateSessionChannel { name: created, .. } =
            plan_surface(&spec, Some(CATEGORY)).capability
        else {
            panic!("expected a channel");
        };
        let DiscordCapability::ArchiveChannel {
            archived_name: dead,
            ..
        } = plan_teardown(&spec, CHANNEL).archive.capability
        else {
            panic!("expected a channel archive");
        };
        assert_eq!(dead, channels::archived_name_for(&created));
        assert_eq!(dead, "archived-dungeon-a1b2c3");
    }

    // ─── the whole lifecycle, as cells ───────────────────────────────────────

    #[test]
    fn every_session_cell_is_session_scoped_so_concurrent_runs_never_collide() {
        let a = dungeon_spec();
        let mut b = dungeon_spec();
        b.session_id = "d4e5f6".into();

        let cells = |s: &SessionSpec| {
            let mut v = vec![plan_surface(s, Some(CATEGORY)).cell_id];
            let post = plan_post_open(s, CHANNEL);
            v.extend(post.role.map(|c| c.cell_id));
            v.extend(post.announce.map(|c| c.cell_id));
            let td = plan_teardown(s, CHANNEL);
            v.push(td.archive.cell_id);
            v.extend(td.role.map(|c| c.cell_id));
            v
        };

        let (ca, cb) = (cells(&a), cells(&b));
        assert_eq!(ca.len(), 5, "surface + role + announce + archive + release");
        for cell in &ca {
            assert!(
                !cb.contains(cell),
                "cell {cell} is shared between two concurrent runs"
            );
        }

        // ...but the CATEGORY cell IS shared: both runs file under one category.
        assert_eq!(plan_category(&a), plan_category(&b));
    }

    #[tokio::test]
    async fn the_orchestrator_refuses_to_open_for_a_non_admin_before_touching_discord() {
        // The gate runs BEFORE any guild write — so this drives the real `open()`
        // with an unusable Http and still returns Unauthorized, not a network error.
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let bridge = EventBridge::new("http://localhost:0".into());
        let http = Arc::new(Http::new("Bot invalid"));

        let mut spec = dungeon_spec();
        spec.requested_by = PLAYER;

        let err = orch.open(spec, &caps, &bridge, &http).await;
        assert_eq!(
            err.unwrap_err(),
            OrchestrationError::Unauthorized {
                requested_by: PLAYER
            }
        );
        assert!(
            caps.list_for_guild(GUILD).await.is_empty(),
            "a refused open must not leave a registered guild-write capability behind"
        );
    }

    #[tokio::test]
    async fn a_failed_guild_write_leaves_no_registered_capability_behind() {
        // With an invalid token every write fails. The orchestrator must not leave
        // the cell it registered sitting in the registry as a live authority.
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let bridge = EventBridge::new("http://localhost:0".into());
        let http = Arc::new(Http::new("Bot invalid"));

        let err = orch
            .open(dungeon_spec(), &caps, &bridge, &http)
            .await
            .unwrap_err();
        assert!(matches!(err, OrchestrationError::Discord(_)));

        assert!(
            caps.list_for_guild(GUILD).await.is_empty(),
            "a failed write must not leave its cell registered"
        );
        assert!(
            orch.get("dungeon/a1b2c3").await.is_none(),
            "a session whose surface never got created is not a live session"
        );
    }

    #[tokio::test]
    async fn tearing_down_an_unknown_session_is_an_error_not_a_panic() {
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let bridge = EventBridge::new("http://localhost:0".into());
        let http = Arc::new(Http::new("Bot invalid"));

        let err = orch
            .teardown("dungeon/nope", &caps, &bridge, &http)
            .await
            .unwrap_err();
        assert_eq!(
            err,
            OrchestrationError::UnknownSession("dungeon/nope".into())
        );
    }

    #[tokio::test]
    async fn a_seeded_category_is_reused_rather_than_re_minted() {
        let orch = SessionOrchestrator::new();
        orch.seed_category(GUILD, "dungeon", CATEGORY).await;
        // The cache is what `ensure_category` consults before minting; seeding it is
        // how an offering whose category already exists avoids a duplicate.
        assert_eq!(
            orch.categories
                .read()
                .await
                .get(&(GUILD, "dungeon".to_string())),
            Some(&CATEGORY)
        );
    }

    // ─── guild_create bootstrap ──────────────────────────────────────────────

    #[test]
    fn the_bootstrap_category_plan_produces_the_create_category_request() {
        let boot = OfferingBootstrap::new("dungeon", GUILD, ADMIN);
        let planned = plan_bootstrap(&boot).expect("a grouped offering bootstraps a category");
        assert_eq!(planned.cell_id, "discord/category/1111/dungeon");

        let DiscordCapability::CreateCategory { guild_id, name } = planned.capability else {
            panic!("a bootstrap plans a CreateCategory");
        };
        assert_eq!(guild_id, GUILD);
        assert_eq!(name, "dreggnet-dungeon");

        // The exact request `exercise(CreateCategory { .. })` would put on the wire.
        let body =
            serde_json::to_value(crate::discord_caps::build_category_request(&name, "r")).unwrap();
        assert_eq!(body["name"], "dreggnet-dungeon");
        assert_eq!(
            body["type"],
            serde_json::to_value(serenity::all::ChannelType::Category).unwrap()
        );
        assert!(
            body.get("parent_id").is_none(),
            "Discord does not nest categories"
        );
    }

    #[test]
    fn bootstrap_prepares_the_exact_category_a_later_open_reuses() {
        // The load-bearing invariant: the category a guild_create bootstrap mints
        // MUST be byte-for-byte the one a later open() files its session under — same
        // cell id, same capability — or the bootstrap prepares one category and the
        // first session mints a second, orphaning it.
        let boot = OfferingBootstrap::new("dungeon", GUILD, ADMIN);
        let sess = dungeon_spec();
        assert_eq!(
            plan_bootstrap(&boot),
            plan_category(&sess),
            "bootstrap and open must resolve to ONE category per offering"
        );
    }

    #[test]
    fn a_threads_only_offering_bootstraps_no_category() {
        let boot = OfferingBootstrap::new("chat", GUILD, ADMIN).without_category();
        assert!(
            plan_bootstrap(&boot).is_none(),
            "a threads-only offering files nothing under a category"
        );
    }

    #[tokio::test]
    async fn bootstrapping_a_seeded_offering_reuses_its_category_without_a_guild_write() {
        // A guild whose category already exists (seeded) is prepared with NO guild
        // write — proven by driving the real bootstrap with an unusable Http and
        // still getting the seeded id back. This is what makes guild_create cheap on
        // a restart.
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let http = Arc::new(Http::new("Bot invalid"));
        orch.seed_category(GUILD, "dungeon", CATEGORY).await;

        let report = orch
            .bootstrap_offering(
                &OfferingBootstrap::new("dungeon", GUILD, ADMIN).base_roles([ROLE]),
                &caps,
                &http,
            )
            .await
            .expect("a seeded category needs no guild write");
        assert_eq!(report.category_id, Some(CATEGORY));
        assert_eq!(
            report.base_role_ids,
            vec![ROLE],
            "declared base roles are carried through to the report"
        );
        assert!(
            caps.list_for_guild(GUILD).await.is_empty(),
            "reusing a cached category registers no capability"
        );
    }

    #[tokio::test]
    async fn a_categoryless_bootstrap_touches_no_guild_and_reports_no_category() {
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let http = Arc::new(Http::new("Bot invalid"));

        let report = orch
            .bootstrap_offering(
                &OfferingBootstrap::new("chat", GUILD, ADMIN).without_category(),
                &caps,
                &http,
            )
            .await
            .expect("a threads-only offering prepares nothing to fail on");
        assert_eq!(report.category_id, None);
        assert!(caps.list_for_guild(GUILD).await.is_empty());
    }

    #[tokio::test]
    async fn a_failed_bootstrap_leaves_no_registered_capability_and_caches_nothing() {
        // With an invalid token the category mint fails. The bootstrap must not leave
        // the cell it registered sitting as a live authority, NOR cache a bogus id —
        // a retry after the guild grants MANAGE_CHANNELS must still mint.
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let http = Arc::new(Http::new("Bot invalid"));

        let err = orch
            .bootstrap_offering(
                &OfferingBootstrap::new("dungeon", GUILD, ADMIN),
                &caps,
                &http,
            )
            .await
            .unwrap_err();
        assert!(matches!(err, OrchestrationError::Discord(_)));
        assert!(
            caps.list_for_guild(GUILD).await.is_empty(),
            "a failed bootstrap leaves no cell registered"
        );
        assert!(
            orch.categories
                .read()
                .await
                .get(&(GUILD, "dungeon".to_string()))
                .is_none(),
            "a failed mint must not cache a category id"
        );
    }

    #[tokio::test]
    async fn bootstrap_guild_prepares_every_offering_it_hosts() {
        let orch = SessionOrchestrator::new();
        let caps = DiscordCapRegistry::new();
        let http = Arc::new(Http::new("Bot invalid"));
        orch.seed_category(GUILD, "dungeon", CATEGORY).await;
        orch.seed_category(GUILD, "hosted-hermes", 4445).await;

        let reports = orch
            .bootstrap_guild(
                &[
                    OfferingBootstrap::new("dungeon", GUILD, ADMIN),
                    OfferingBootstrap::new("hosted-hermes", GUILD, ADMIN),
                ],
                &caps,
                &http,
            )
            .await
            .expect("both offerings' categories are seeded");
        assert_eq!(reports.len(), 2);
        assert_eq!(reports[0].category_id, Some(CATEGORY));
        assert_eq!(reports[1].category_id, Some(4445));
    }
}
