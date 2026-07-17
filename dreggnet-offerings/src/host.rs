//! # `OfferingHost` — the frontend-agnostic multi-offering registry.
//!
//! The generic offering router that today only exists Discord-side (`discord-bot/offering.rs` —
//! a `DiscordOffering` registry + per-offering `Store<O>` sessions + `route_component`), **lifted
//! to the core** so every frontend (web, Telegram, WeChat) drives ALL offerings through ONE object.
//!
//! An [`OfferingHost`] is a registry of heterogeneous [`Offering`]s by **key** (`"dungeon"`,
//! `"council"`, `"market"`) plus their live per-`(offering, session)` state. It exposes the SAME six
//! offering verbs a frontend needs — [`list_offerings`](OfferingHost::list_offerings) /
//! [`open`](OfferingHost::open) / [`actions`](OfferingHost::actions) /
//! [`advance`](OfferingHost::advance) / [`render`](OfferingHost::render) /
//! [`verify`](OfferingHost::verify) — driving ANY offering purely through its [`Offering`] trait.
//!
//! ## The Session-erasure shape (the load-bearing design)
//!
//! [`Offering::Session`] is an ASSOCIATED type: a [`dungeon::DungeonSession`](crate::dungeon), a
//! council session, and a market session are three *different, unrelated* types (one even holds
//! `!Send` `Rc`-backed ballot caps — see the discord-bot `Store` note). They cannot live in one
//! `HashMap<_, Session>`. So the host does NOT collapse the `Session` type: each registered offering
//! is stored behind a **type-erased [`OfferingSlot`] trait object** ([`Hosted<O>`]) that owns its own
//! `HashMap<SessionId, O::Session>` privately and exposes the offering verbs with the session type
//! **erased behind the [`SessionId`] handle**. The host holds `BTreeMap<key, Box<dyn OfferingSlot>>`
//! — heterogeneous offerings, one registry, the polymorphic `Session` preserved (never boxed into a
//! lossy `Any`, never forced `Send`).
//!
//! ## Reuse across frontends
//!
//! This host is the frontend-agnostic core the Discord adapter's per-offering `Store` generalises:
//! `dreggnet-web` drives it (a multi-offering web catalog); a Telegram / WeChat frontend adopts the
//! SAME host unchanged (each maps the host's [`Surface`]/[`Action`]s onto its own controls). Because
//! some sessions are `!Send`, a frontend that needs a `Send + Sync` handle (an axum `State`) confines
//! the host to one owning thread and ships jobs to it — exactly what the discord-bot `Store` does and
//! what `dreggnet-web`'s host wrapper does; the host itself stays a plain synchronous object.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use crate::lifecycle::{Clock, PolicyRefusal, SessionPolicy, SweepReport, quota_key};
use crate::resume::{SessionMoveLog, SessionResumeStore};
use crate::signed::{Attribution, SignedAction, SignedError, verify_signed};
use crate::{
    Action, CollectiveDecision, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, SessionId, Surface, VerifyReport,
};

/// A **catalog entry** — one registered offering's public identity + its live-session count, for a
/// frontend to paint a browse list ([`OfferingHost::list_offerings`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OfferingInfo {
    /// The offering's registry key (the URL/route segment — `"dungeon"`, `"council"`, `"market"`).
    pub key: String,
    /// The human title (the catalog card's heading).
    pub title: String,
    /// How many sessions of this offering are currently open in the host.
    pub open_sessions: usize,
}

/// An error driving the host — the offering key or session was unknown, or the offering refused to
/// deploy a session. A read miss (`actions`/`render`/`verify` on an absent offering/session) is a
/// plain `None`; only [`open`](OfferingHost::open)/[`ensure_open`](OfferingHost::ensure_open) return
/// this (a deploy can genuinely fail, and that must not be swallowed).
#[derive(Debug, Clone)]
pub enum HostError {
    /// No offering is registered under this key.
    UnknownOffering(String),
    /// The offering refused to deploy the session (carries the offering's own reason).
    Deploy(OfferingError),
    /// No live session under this id (a routing miss the `Result`-shaped
    /// [`advance_signed`](OfferingHost::advance_signed) reports explicitly, where the
    /// `Option`-shaped verbs answer `None`).
    UnknownSession {
        /// The offering key the miss was under.
        key: String,
        /// The absent session id.
        id: SessionId,
    },
    /// A [`SignedAction`] failed verification — forged/tampered ([`SignedError::BadSignature`]),
    /// replayed ([`SignedError::StaleCounter`]), or malformed ([`SignedError::MalformedKey`]).
    /// Nothing advanced, nothing was recorded (anti-ghost).
    Signature(SignedError),
    /// A [`SessionPolicy`] gate refused the open — the variant names WHICH limit tripped
    /// (per-actor quota / open rate / offering capacity), so a surface answers with the honest
    /// status (a 429 with a retry-after) instead of a generic failure. Nothing was opened.
    Policy(PolicyRefusal),
    /// A persisted move-log exists for this session but REFUSED to reopen on lazy resume
    /// (tampered / undeployable — fail-closed, nothing left live, the durable file kept). The
    /// host refuses rather than shadowing the durable record with a fresh genesis whose advances
    /// would append garbage to it.
    ResumeFailed {
        /// The offering key.
        key: String,
        /// The session whose persisted log refused to reopen.
        id: SessionId,
        /// The resume refusal, verbatim.
        reason: String,
    },
}

impl std::fmt::Display for HostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HostError::UnknownOffering(k) => write!(f, "no offering registered under key {k:?}"),
            HostError::Deploy(e) => write!(f, "{e}"),
            HostError::UnknownSession { key, id } => {
                write!(f, "no live session {:?} under offering {key:?}", id.0)
            }
            HostError::Signature(e) => write!(f, "signed advance refused: {e}"),
            HostError::Policy(r) => write!(f, "open refused by session policy: {r}"),
            HostError::ResumeFailed { key, id, reason } => write!(
                f,
                "persisted session {:?} under offering {key:?} refused to reopen: {reason}",
                id.0
            ),
        }
    }
}

impl std::error::Error for HostError {}

/// An error **resuming** a session from its [`SessionMoveLog`] — reopening it by replaying the log
/// ([`OfferingHost::resume`]). Fail-closed: a session either reopens to its authentic committed state
/// or it does not reopen at all (no partial / forged session is left live).
#[derive(Debug, Clone)]
pub enum ResumeError {
    /// The log names an offering key that is not registered on this host.
    UnknownOffering(String),
    /// The offering refused to deploy the fresh session the replay re-drives from.
    Deploy(OfferingError),
    /// A live session already occupies the log's id (a resume never clobbers a running session).
    AlreadyOpen(SessionId),
    /// **A logged advance did not land on re-drive** — the executor REFUSED it: a forged, ineligible,
    /// reordered, or otherwise tampered move spliced into the log. The same anti-ghost gate a live
    /// move hits, so a tampered log cannot reopen to a forged state; it fails to reopen. Carries the
    /// 0-based index of the offending move and the executor's own reason. The partially-resumed
    /// session is rolled back (closed) before this returns.
    Refused {
        /// The 0-based index into [`SessionMoveLog::moves`] of the move that was refused.
        index: usize,
        /// The executor's reason for refusing it.
        reason: String,
    },
}

impl std::fmt::Display for ResumeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResumeError::UnknownOffering(k) => {
                write!(f, "no offering registered under key {k:?}")
            }
            ResumeError::Deploy(e) => write!(f, "{e}"),
            ResumeError::AlreadyOpen(id) => {
                write!(f, "a session is already open under id {:?}", id.0)
            }
            ResumeError::Refused { index, reason } => write!(
                f,
                "resume refused: logged move #{index} did not land on re-drive ({reason}) — \
                 the log is tampered"
            ),
        }
    }
}

impl std::error::Error for ResumeError {}

/// **The type-erased offering slot** — one registered offering plus its live sessions, with the
/// [`Offering::Session`] type erased. This is the seam that lets heterogeneous offerings (whose
/// `Session` types are unrelated, some `!Send`) share ONE registry: the concrete session lives
/// privately inside the slot ([`Hosted<O>`]'s `HashMap<SessionId, O::Session>`), and every verb is
/// addressed by the opaque [`SessionId`] handle. A frontend never names a `Session` type.
///
/// It is a private trait (the host is the sole surface); `Hosted<O>` is its only implementor.
trait OfferingSlot {
    /// The offering's human title.
    fn title(&self) -> &str;
    /// The number of live sessions this slot holds.
    fn open_count(&self) -> usize;
    /// Whether `id` names a live session here.
    fn is_open(&self, id: &SessionId) -> bool;
    /// The live session ids (sorted), for enumeration.
    fn session_ids(&self) -> Vec<SessionId>;
    /// Open a session under `id` (deploy the confined thing). Erases `O::Session` into `self`.
    fn open(&mut self, id: SessionId, cfg: SessionConfig) -> Result<(), OfferingError>;
    /// Drop a session.
    fn close(&mut self, id: &SessionId) -> bool;
    /// The current cap-gated affordances of session `id` (`None` if absent).
    fn actions(&self, id: &SessionId) -> Option<Vec<Action>>;
    /// The cap-gated affordances of session `id` AS `viewer` sees them (`None` if absent) — threads
    /// the viewer to [`Offering::actions_for`] across the erasure boundary.
    fn actions_for(&self, id: &SessionId, viewer: &DreggIdentity) -> Option<Vec<Action>>;
    /// Advance session `id` by one real turn (`None` if absent).
    fn advance(&mut self, id: &SessionId, input: Action, actor: DreggIdentity) -> Option<Outcome>;
    /// Advance session `id` by one real crowd turn (`None` if absent).
    fn advance_collective(
        &mut self,
        id: &SessionId,
        input: Action,
        decision: CollectiveDecision,
    ) -> Option<Outcome>;
    /// Render session `id`'s current surface (`None` if absent).
    fn render(&self, id: &SessionId) -> Option<Surface>;
    /// Render session `id`'s surface AS `viewer` sees it (`None` if absent) — threads the viewer to
    /// [`Offering::render_for`] across the erasure boundary (the hidden-hand / fog-of-war projection).
    fn render_for(&self, id: &SessionId, viewer: &DreggIdentity) -> Option<Surface>;
    /// Re-verify session `id`'s committed chain (`None` if absent).
    fn verify(&self, id: &SessionId) -> Option<VerifyReport>;
    /// What `input` would cost in session `id` (`None` if absent).
    fn price(&self, id: &SessionId, input: &Action) -> Option<RunCost>;
}

/// **The concrete slot** — an [`Offering`] `O` and its live `O::Session`s, keyed by [`SessionId`].
/// Implements [`OfferingSlot`] by delegating every verb to `O`'s trait methods over the addressed
/// session. This is where the `Session` type is *held* (not erased); the erasure is the
/// `dyn OfferingSlot` the host stores it behind.
struct Hosted<O: Offering> {
    title: String,
    offering: O,
    sessions: HashMap<SessionId, O::Session>,
}

impl<O: Offering> OfferingSlot for Hosted<O> {
    fn title(&self) -> &str {
        &self.title
    }

    fn open_count(&self) -> usize {
        self.sessions.len()
    }

    fn is_open(&self, id: &SessionId) -> bool {
        self.sessions.contains_key(id)
    }

    fn session_ids(&self) -> Vec<SessionId> {
        let mut ids: Vec<SessionId> = self.sessions.keys().cloned().collect();
        ids.sort_by(|a, b| a.0.cmp(&b.0));
        ids
    }

    fn open(&mut self, id: SessionId, cfg: SessionConfig) -> Result<(), OfferingError> {
        let session = self.offering.open(cfg)?;
        self.sessions.insert(id, session);
        Ok(())
    }

    fn close(&mut self, id: &SessionId) -> bool {
        self.sessions.remove(id).is_some()
    }

    fn actions(&self, id: &SessionId) -> Option<Vec<Action>> {
        let s = self.sessions.get(id)?;
        Some(self.offering.actions(s))
    }

    fn actions_for(&self, id: &SessionId, viewer: &DreggIdentity) -> Option<Vec<Action>> {
        let s = self.sessions.get(id)?;
        Some(self.offering.actions_for(s, viewer))
    }

    fn advance(&mut self, id: &SessionId, input: Action, actor: DreggIdentity) -> Option<Outcome> {
        let s = self.sessions.get_mut(id)?;
        Some(self.offering.advance(s, input, actor))
    }

    fn advance_collective(
        &mut self,
        id: &SessionId,
        input: Action,
        decision: CollectiveDecision,
    ) -> Option<Outcome> {
        let s = self.sessions.get_mut(id)?;
        Some(self.offering.advance_collective(s, input, decision))
    }

    fn render(&self, id: &SessionId) -> Option<Surface> {
        let s = self.sessions.get(id)?;
        Some(self.offering.render(s))
    }

    fn render_for(&self, id: &SessionId, viewer: &DreggIdentity) -> Option<Surface> {
        let s = self.sessions.get(id)?;
        Some(self.offering.render_for(s, viewer))
    }

    fn verify(&self, id: &SessionId) -> Option<VerifyReport> {
        let s = self.sessions.get(id)?;
        Some(self.offering.verify(s))
    }

    fn price(&self, id: &SessionId, input: &Action) -> Option<RunCost> {
        // `price` reads only the offering (not the session), but a price for an absent session is a
        // routing miss — gate on presence so the host answers `None`, not a phantom cost.
        if !self.sessions.contains_key(id) {
            return None;
        }
        Some(self.offering.price(input))
    }
}

/// **The frontend-agnostic multi-offering host.** Registers heterogeneous [`Offering`]s by key and
/// drives them all through the same verbs. See the module doc for the Session-erasure shape.
///
/// Not itself `Send`/`Sync` (a registered offering's session may be `!Send`); a frontend needing a
/// thread-crossing handle confines it to one owning thread (see `dreggnet-web`).
#[derive(Default)]
pub struct OfferingHost {
    /// The registered offerings, key → erased slot. `BTreeMap` so the catalog order is stable.
    slots: BTreeMap<String, Box<dyn OfferingSlot>>,
    /// A monotone counter minting fresh session ids for [`open`](OfferingHost::open).
    counter: u64,
    /// **The per-session move-log** — the reproducible public input (seed + ordered landed advances)
    /// of every live session, keyed by `(offering key, session id)`. Grown on
    /// [`open`](OfferingHost::open_session) (the seed) and each landed [`advance`](OfferingHost::advance).
    /// A session survives restart by REPLAYING its log ([`resume`](OfferingHost::resume)), not by a
    /// trusted state blob. Held in memory here; mirrored to a durable [`SessionResumeStore`] when one
    /// is attached.
    logs: HashMap<(String, SessionId), SessionMoveLog>,
    /// An optional durable persistence seam for the move-logs. When attached
    /// ([`with_resume_store`](OfferingHost::with_resume_store)), the host writes each open + landed
    /// advance THROUGH to it, and [`resume_all`](OfferingHost::resume_all) replays every stored log
    /// on boot. The in-process default is `None` (logs live only in memory).
    resume_store: Option<Box<dyn SessionResumeStore>>,
    /// **The signed-advance replay ledger** — the last consumed [`SignedAction::counter`] per
    /// `(offering key, session id, signer pubkey hex)`. [`advance_signed`](OfferingHost::advance_signed)
    /// requires each envelope's counter to be strictly greater than the entry here and consumes it
    /// on every successful verification (even an executor-refused move burns its counter — a
    /// verified envelope is single-use, so a captured one can never be re-presented later when the
    /// session state might have made its move legal). In-memory, like the live sessions it guards
    /// — and, with a resume store attached, WRITTEN THROUGH to it on every consumption (so the
    /// floors survive lifecycle eviction and a process restart; see [`crate::lifecycle`]).
    signed_counters: HashMap<(String, SessionId, String), u64>,
    /// **The session-lifecycle policy** ([`crate::lifecycle`]) — all-`None` (the default) is the
    /// unbounded pre-lifecycle behavior, byte-identical (nothing tracked, nothing refused).
    policy: SessionPolicy,
    /// The injected time source the policy runs on ([`with_policy`](OfferingHost::with_policy)).
    /// `None` until a policy is attached; no wall clock is ever read outside it.
    clock: Option<Box<dyn Clock>>,
    /// Per-live-session last-touched stamps (seconds), `(key, id) → t` — fed by open / advance /
    /// render, read by the TTL sweep and the LRU capacity eviction. `RefCell` so the read-shaped
    /// verbs (`render`/`render_for`, `&self`) can stamp activity; the host is single-thread-
    /// confined by design (see the module doc), so the interior mutability is uncontended.
    /// Only populated while a policy is armed.
    touched: RefCell<HashMap<(String, SessionId), u64>>,
    /// Which quota key FRESH-MINTED each live session (for freeing the quota slot on
    /// close/eviction). Only populated while a policy is armed and the open carried an opener.
    openers: HashMap<(String, SessionId), String>,
    /// Live fresh-minted session count per opener quota key (the `max_opens_per_actor` gate).
    minted_live: HashMap<String, usize>,
    /// Last fresh-mint time per opener quota key (the `min_open_interval_secs` gate).
    last_minted_at: HashMap<String, u64>,
}

impl OfferingHost {
    /// A fresh host with no offerings registered.
    pub fn new() -> Self {
        OfferingHost::default()
    }

    /// **Attach a durable [`SessionResumeStore`]** — the session-resume persistence seam. With one
    /// attached, the host writes each session OPEN (its seed) and each LANDED advance through to the
    /// store, so the move-logs outlive the process; [`resume_all`](OfferingHost::resume_all) replays
    /// every stored log on the next boot, reopening each session to its identical committed state. The
    /// reference impl is [`crate::resume::InMemoryResumeStore`]; the durable sqlite impl is the
    /// discord-bot's follow-up. Additive: a host with no store keeps its move-logs in memory only.
    pub fn with_resume_store(mut self, store: Box<dyn SessionResumeStore>) -> Self {
        self.resume_store = Some(store);
        self
    }

    /// **Arm a [`SessionPolicy`]** with its injected [`Clock`] — the session-lifecycle seam
    /// ([`crate::lifecycle`]): per-offering capacity (LRU eviction), per-opener quotas + open
    /// rate, and the idle-TTL [`sweep`](OfferingHost::sweep). An all-`None` policy (the default)
    /// arms nothing — the unbounded pre-lifecycle behavior, byte-identical. Attach BEFORE
    /// [`resume_all`](OfferingHost::resume_all) so boot-resumed sessions get last-touched stamps.
    pub fn with_policy(mut self, policy: SessionPolicy, clock: impl Clock + 'static) -> Self {
        self.policy = policy;
        self.clock = Some(Box::new(clock));
        self
    }

    /// The armed [`SessionPolicy`] (the default unbounded one if none was attached).
    pub fn policy(&self) -> &SessionPolicy {
        &self.policy
    }

    /// **Register an offering** under `key` with a human `title`. Any [`Offering`] whose session is
    /// `'static` plugs in — the session type is erased behind the slot, so heterogeneous offerings
    /// (a dungeon, a council, a market) coexist. Re-registering a key replaces it.
    pub fn register<O>(&mut self, key: impl Into<String>, title: impl Into<String>, offering: O)
    where
        O: Offering + 'static,
        O::Session: 'static,
    {
        let slot = Hosted {
            title: title.into(),
            offering,
            sessions: HashMap::new(),
        };
        self.slots.insert(key.into(), Box::new(slot));
    }

    /// Whether an offering is registered under `key`.
    pub fn has(&self, key: &str) -> bool {
        self.slots.contains_key(key)
    }

    /// The registered offering keys, in stable (catalog) order.
    pub fn keys(&self) -> Vec<String> {
        self.slots.keys().cloned().collect()
    }

    /// **The catalog** — every registered offering's key + title + live-session count, in stable
    /// order. A frontend paints this as the browse list (each entry a "play" link).
    pub fn list_offerings(&self) -> Vec<OfferingInfo> {
        self.slots
            .iter()
            .map(|(key, slot)| OfferingInfo {
                key: key.clone(),
                title: slot.title().to_string(),
                open_sessions: slot.open_count(),
            })
            .collect()
    }

    /// The title of the offering registered under `key` (`None` if unregistered).
    pub fn title(&self, key: &str) -> Option<&str> {
        self.slots.get(key).map(|s| s.title())
    }

    /// **Open a fresh session** of offering `key`, minting a new [`SessionId`] and returning it. The
    /// session is seeded deterministically from its minted id (a re-open under the same id is the
    /// same replay-verifiable session). Errors if `key` is unregistered or the offering refuses to
    /// deploy. Attribution-less (no per-actor gates); see [`open_as`](OfferingHost::open_as).
    pub fn open(&mut self, key: &str) -> Result<SessionId, HostError> {
        self.open_as(key, None)
    }

    /// [`open`](OfferingHost::open) with the opener's [`Attribution`] — the per-actor lifecycle
    /// gates (open quota, open rate) key on it when a policy is armed; `None` skips them (there
    /// is no actor to key), leaving capacity + TTL as the backstops. `Signed` quotas are real
    /// enforcement, `Asserted` quotas are advisory (a forgeable label) — see [`crate::lifecycle`].
    pub fn open_as(
        &mut self,
        key: &str,
        opener: Option<&Attribution>,
    ) -> Result<SessionId, HostError> {
        if !self.has(key) {
            return Err(HostError::UnknownOffering(key.to_string()));
        }
        self.admit_fresh_open(key, opener)?;
        self.counter += 1;
        let id = SessionId::new(format!("{key}-{}", self.counter));
        let cfg = SessionConfig::with_seed(seed_from_id(&id.0));
        self.open_session(key, id.clone(), cfg)?;
        self.note_fresh_open(key, &id, opener);
        Ok(id)
    }

    /// **Ensure a session is open** under a caller-chosen `id` (the web surface's route param): open
    /// it (seeded from the id) iff it is not already live. Returns `true` if it was newly opened,
    /// `false` if it already existed (or resumed from the durable store — not a fresh world).
    /// Errors if `key` is unregistered or the deploy is refused. Attribution-less; see
    /// [`ensure_open_as`](OfferingHost::ensure_open_as).
    pub fn ensure_open(&mut self, key: &str, id: &SessionId) -> Result<bool, HostError> {
        self.ensure_open_as(key, id, None)
    }

    /// [`ensure_open`](OfferingHost::ensure_open) with the opener's [`Attribution`] — the
    /// lifecycle-aware web/adapter entry:
    ///
    /// 1. a LIVE session is touched (kept hot) and returned as existing — no gate applies (it is
    ///    not an open);
    /// 2. an absent session whose move-log the attached store holds is **lazily RESUMED by
    ///    replay** (capacity-gated — it re-enters memory, LRU-evicting a colder session if
    ///    needed) — this is the hot/cold working-set model: an evicted session's next touch
    ///    brings it back, state intact. A log that refuses to reopen is [`HostError::ResumeFailed`]
    ///    (fail-closed — never shadowed by a fresh genesis appending to the durable record);
    /// 3. only a genuinely NEW session is a fresh mint, and only a fresh mint runs the per-actor
    ///    gates (rate, quota) + the capacity gate ([`HostError::Policy`] names the tripped limit).
    pub fn ensure_open_as(
        &mut self,
        key: &str,
        id: &SessionId,
        opener: Option<&Attribution>,
    ) -> Result<bool, HostError> {
        if !self.has(key) {
            return Err(HostError::UnknownOffering(key.to_string()));
        }
        if self.is_open(key, id) {
            self.touch(key, id);
            return Ok(false);
        }
        if self.lazy_resume(key, id)? {
            return Ok(false);
        }
        self.admit_fresh_open(key, opener)?;
        let cfg = SessionConfig::with_seed(seed_from_id(&id.0));
        self.open_session(key, id.clone(), cfg)?;
        self.note_fresh_open(key, id, opener);
        Ok(true)
    }

    // ── The lifecycle gates + bookkeeping (no-ops while the policy is unbounded) ──

    /// The current policy time (0 if no clock is attached — only reachable with the unbounded
    /// policy, where nothing reads it).
    fn now(&self) -> u64 {
        self.clock.as_ref().map(|c| c.now()).unwrap_or(0)
    }

    /// Stamp session `(key, id)` as touched now (open / advance / render activity). A no-op while
    /// the policy is unbounded (nothing tracked — the byte-identical legacy path).
    fn touch(&self, key: &str, id: &SessionId) {
        if self.policy.is_unbounded() {
            return;
        }
        let now = self.now();
        self.touched
            .borrow_mut()
            .insert((key.to_string(), id.clone()), now);
    }

    /// Admit a FRESH session mint under `key` by `opener`: the per-actor rate + quota gates
    /// (skipped for attribution-less opens), then a TTL sweep (idle sessions are reaped exactly
    /// when capacity is about to be judged), then the capacity gate (LRU-evicting if permitted).
    fn admit_fresh_open(
        &mut self,
        key: &str,
        opener: Option<&Attribution>,
    ) -> Result<(), HostError> {
        if self.policy.is_unbounded() {
            return Ok(());
        }
        let now = self.now();
        if let Some(att) = opener {
            let qk = quota_key(att);
            if let Some(min) = self.policy.min_open_interval_secs {
                if let Some(&last) = self.last_minted_at.get(&qk) {
                    let next = last.saturating_add(min);
                    if now < next {
                        return Err(HostError::Policy(PolicyRefusal::OpenRate {
                            retry_after_secs: next - now,
                        }));
                    }
                }
            }
            if let Some(limit) = self.policy.max_opens_per_actor {
                if self.minted_live.get(&qk).copied().unwrap_or(0) >= limit {
                    return Err(HostError::Policy(PolicyRefusal::ActorQuota {
                        actor: qk,
                        limit,
                    }));
                }
            }
        }
        self.sweep(now);
        self.admit_capacity(key)
    }

    /// Admit one more live session under `key` against the per-offering capacity cap, LRU-evicting
    /// the coldest evictable session(s) if the policy permits; refuses ([`PolicyRefusal::Capacity`])
    /// when the cap is full and nothing is evictable.
    fn admit_capacity(&mut self, key: &str) -> Result<(), HostError> {
        let Some(limit) = self.policy.max_sessions_per_offering else {
            return Ok(());
        };
        loop {
            let count = self.slots.get(key).map(|s| s.open_count()).unwrap_or(0);
            if count < limit {
                return Ok(());
            }
            if !self.evict_coldest(key) {
                return Err(HostError::Policy(PolicyRefusal::Capacity {
                    key: key.to_string(),
                    limit,
                }));
            }
        }
    }

    /// Record a successful fresh mint: the touched stamp + (when an opener was named) its quota
    /// slot and rate stamp. A no-op while the policy is unbounded.
    fn note_fresh_open(&mut self, key: &str, id: &SessionId, opener: Option<&Attribution>) {
        if self.policy.is_unbounded() {
            return;
        }
        self.touch(key, id);
        if let Some(att) = opener {
            let qk = quota_key(att);
            *self.minted_live.entry(qk.clone()).or_insert(0) += 1;
            self.openers
                .insert((key.to_string(), id.clone()), qk.clone());
            self.last_minted_at.insert(qk, self.now());
        }
    }

    /// Free session `(key, id)`'s lifecycle bookkeeping (touched stamp + minted-quota slot) —
    /// shared by eviction and [`close`](OfferingHost::close).
    fn drop_lifecycle_bookkeeping(&mut self, key: &str, id: &SessionId) {
        self.touched
            .borrow_mut()
            .remove(&(key.to_string(), id.clone()));
        if let Some(qk) = self.openers.remove(&(key.to_string(), id.clone())) {
            if let Some(n) = self.minted_live.get_mut(&qk) {
                *n = n.saturating_sub(1);
                if *n == 0 {
                    self.minted_live.remove(&qk);
                }
            }
        }
    }

    /// **Lazily resume `(key, id)` from the attached store's persisted move-log**, if one exists:
    /// `Ok(true)` = resumed (capacity-admitted, replayed, touched); `Ok(false)` = no persisted log
    /// (the caller proceeds to a fresh mint / an honest miss); `Err` = a log exists but capacity
    /// refused or the replay refused it ([`HostError::ResumeFailed`], fail-closed).
    fn lazy_resume(&mut self, key: &str, id: &SessionId) -> Result<bool, HostError> {
        let Some(log) = self.resume_store.as_ref().and_then(|s| s.load(key, id)) else {
            return Ok(false);
        };
        self.admit_capacity(key)?;
        self.resume(&log).map_err(|e| HostError::ResumeFailed {
            key: key.to_string(),
            id: id.clone(),
            reason: e.to_string(),
        })?;
        Ok(true)
    }

    /// **Evict session `(key, id)`** — drop the live slot + in-memory bookkeeping, under the two
    /// safety rules (see [`crate::lifecycle`]): with a store the durable move-log stays (the
    /// session resumes lazily on its next touch) and the signed-replay floors are moved into the
    /// store (dropped from memory only if the store CONFIRMS it persisted them — fail-closed);
    /// without a store (the lossy opt-in path) the floors are RETAINED in memory so a captured
    /// envelope can never replay onto a fresh mint of the same id.
    fn evict(&mut self, key: &str, id: &SessionId) {
        if let Some(store) = &self.resume_store {
            let floors: Vec<(String, u64)> = self
                .signed_counters
                .iter()
                .filter(|((k, i, _), _)| k == key && i == id)
                .map(|((_, _, pk), c)| (pk.clone(), *c))
                .collect();
            // Already written through on each consumption; re-record (merge-max, idempotent) and
            // drop from memory only on the store's confirmation.
            if floors.is_empty() || store.record_signed_counters(key, id, &floors) {
                self.signed_counters
                    .retain(|(k, i, _), _| !(k == key && i == id));
            }
        }
        if let Some(slot) = self.slots.get_mut(key) {
            slot.close(id);
        }
        // The in-memory log is dropped either way: with a store the durable copy is authoritative
        // (lazy resume reloads it); without one the session is lossily gone (keeping a log with no
        // live session would be a silent half-resume lane the store-less host never services).
        self.logs.remove(&(key.to_string(), id.clone()));
        self.drop_lifecycle_bookkeeping(key, id);
    }

    /// Evict the COLDEST (longest-idle) session of offering `key`, if eviction is permitted at
    /// all (a store is attached, or the policy opted into lossy eviction). `false` if nothing was
    /// evicted (capacity must then refuse).
    fn evict_coldest(&mut self, key: &str) -> bool {
        if self.resume_store.is_none() && !self.policy.evict_unpersisted {
            return false;
        }
        let coldest = {
            let touched = self.touched.borrow();
            self.slots
                .get(key)
                .map(|s| s.session_ids())
                .unwrap_or_default()
                .into_iter()
                // Tie-break equal stamps by id (sorted order) — `min_by_key` alone keeps the
                // LAST minimum, which would make same-second eviction nondeterministic.
                .min_by_key(|id| {
                    (
                        touched
                            .get(&(key.to_string(), id.clone()))
                            .copied()
                            .unwrap_or(0),
                        id.0.clone(),
                    )
                })
        };
        match coldest {
            Some(id) => {
                self.evict(key, &id);
                true
            }
            None => false,
        }
    }

    /// **The idle-TTL sweep** — evict every live session untouched for MORE than
    /// [`SessionPolicy::idle_ttl_secs`] seconds as of `now`, under the eviction-safety rules: a
    /// persisted session is dropped from memory and resumes lazily on its next touch (state
    /// intact); an UNpersisted one is evicted only under the lossy
    /// [`evict_unpersisted`](SessionPolicy::evict_unpersisted) opt-in, else RETAINED (and
    /// reported). A no-op (empty report) with no TTL armed. `now` is the caller's time — the
    /// injected-clock convenience is [`sweep_now`](OfferingHost::sweep_now); the host also sweeps
    /// opportunistically before judging capacity on each fresh open.
    pub fn sweep(&mut self, now: u64) -> SweepReport {
        let mut report = SweepReport::default();
        let Some(ttl) = self.policy.idle_ttl_secs else {
            return report;
        };
        let candidates: Vec<(String, SessionId)> = {
            let touched = self.touched.borrow();
            self.slots
                .iter()
                .flat_map(|(key, slot)| {
                    slot.session_ids()
                        .into_iter()
                        .map(move |id| (key.clone(), id))
                })
                .filter(|(key, id)| {
                    let t = touched
                        .get(&(key.clone(), id.clone()))
                        .copied()
                        .unwrap_or(0);
                    now.saturating_sub(t) > ttl
                })
                .collect()
        };
        let evictable = self.resume_store.is_some() || self.policy.evict_unpersisted;
        for (key, id) in candidates {
            if evictable {
                self.evict(&key, &id);
                report.evicted.push((key, id));
            } else {
                report.retained_unpersisted.push((key, id));
            }
        }
        report
    }

    /// [`sweep`](OfferingHost::sweep) at the armed policy's own [`Clock`] — what a deployment's
    /// periodic sweeper calls. A no-op with no policy/TTL armed.
    pub fn sweep_now(&mut self) -> SweepReport {
        let now = self.now();
        self.sweep(now)
    }

    /// Open a session under an explicit `id` and `cfg` (the low-level opener the two public
    /// constructors share). Errors if `key` is unregistered or the deploy is refused.
    /// **Below the lifecycle gates**: the policy-aware entries are [`open_as`](OfferingHost::open_as)
    /// / [`ensure_open_as`](OfferingHost::ensure_open_as); a direct caller of this low-level seam
    /// takes on its own capacity discipline.
    pub fn open_session(
        &mut self,
        key: &str,
        id: SessionId,
        cfg: SessionConfig,
    ) -> Result<(), HostError> {
        let slot = self
            .slots
            .get_mut(key)
            .ok_or_else(|| HostError::UnknownOffering(key.to_string()))?;
        slot.open(id.clone(), cfg.clone())
            .map_err(HostError::Deploy)?;
        // Establish the session's move-log with its seed (the reproducible public input's root); a
        // re-open of a known id keeps the existing log rather than dropping its recorded advances.
        self.logs
            .entry((key.to_string(), id.clone()))
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), cfg.clone()));
        if let Some(store) = &self.resume_store {
            store.record_open(key, &id, &cfg);
        }
        Ok(())
    }

    /// Whether session `id` of offering `key` is live.
    pub fn is_open(&self, key: &str, id: &SessionId) -> bool {
        self.slots.get(key).map(|s| s.is_open(id)).unwrap_or(false)
    }

    /// The live session ids of offering `key` (sorted); empty for an unregistered key.
    pub fn session_ids(&self, key: &str) -> Vec<SessionId> {
        self.slots
            .get(key)
            .map(|s| s.session_ids())
            .unwrap_or_default()
    }

    /// Close (drop) session `id` of offering `key`. `true` if a session was removed. Also drops the
    /// session's move-log (in memory + the durable store) — a closed session is not resumed on boot.
    pub fn close(&mut self, key: &str, id: &SessionId) -> bool {
        let removed = self
            .slots
            .get_mut(key)
            .map(|s| s.close(id))
            .unwrap_or(false);
        if removed {
            self.logs.remove(&(key.to_string(), id.clone()));
            if let Some(store) = &self.resume_store {
                store.forget(key, id);
            }
            self.drop_lifecycle_bookkeeping(key, id);
        }
        removed
    }

    /// The current cap-gated affordances of session `(key, id)` — the buttons/forms a frontend
    /// paints. `None` if the offering or session is absent.
    pub fn actions(&self, key: &str, id: &SessionId) -> Option<Vec<Action>> {
        self.slots.get(key)?.actions(id)
    }

    /// The cap-gated affordances of session `(key, id)` **AS `viewer` sees them** — the per-actor
    /// projection ([`Offering::actions_for`]) threaded through the erasure boundary. Where
    /// [`actions`](OfferingHost::actions) paints the anonymous set, this dims/omits affordances the
    /// viewer lacks the cap for (a document region, a seat). `None` if the offering or session is
    /// absent. The web/Telegram/WeChat frontends that hold the acting identity call THIS so a viewer
    /// is offered only what they can fire.
    pub fn actions_for(
        &self,
        key: &str,
        id: &SessionId,
        viewer: &DreggIdentity,
    ) -> Option<Vec<Action>> {
        self.slots.get(key)?.actions_for(id, viewer)
    }

    /// **Advance session `(key, id)` by one real turn** — resolve `input` on the substrate as ONE
    /// cap-bounded turn attributed to `actor` (a legal move lands a real [`Outcome::Landed`]; an
    /// illegal one is a real [`Outcome::Refused`] that commits nothing). `None` if the offering or
    /// session is absent (routing miss, before the substrate).
    pub fn advance(
        &mut self,
        key: &str,
        id: &SessionId,
        input: Action,
        actor: DreggIdentity,
    ) -> Option<Outcome> {
        // Lazy resume-on-touch: an evicted-but-persisted session transparently reopens by replay
        // before the turn resolves (the hot/cold working-set model). A missing/refused log stays
        // an honest `None` miss on this Option-shaped verb.
        if !self.is_open(key, id) && !matches!(self.lazy_resume(key, id), Ok(true)) {
            return None;
        }
        let out = self
            .slots
            .get_mut(key)?
            .advance(id, input.clone(), actor.clone());
        if out.is_some() {
            self.touch(key, id);
        }
        // A LANDED advance is a committed step of the session's reproducible public input — append it
        // to the move-log (and mirror it to the durable store). A REFUSED move committed nothing, so
        // it records nothing (the anti-ghost tooth: the log holds only what actually landed, which is
        // exactly what replaying it must re-land).
        if let Some(o) = &out {
            if o.landed() {
                let attribution = Attribution::from(actor.clone());
                self.record_landed(key, id, input, actor, attribution);
            }
        }
        out
    }

    /// **Advance session `(key, id)` by one SIGNATURE-VERIFIED turn** — the signed twin of
    /// [`advance`](OfferingHost::advance), and the consumer the bare-string actor path never had:
    /// the turn's actor is a **verified Ed25519 public key**, not an asserted label.
    ///
    /// Fail-closed, in order — nothing advances and nothing is recorded on any refusal:
    ///
    /// 1. the offering must be registered ([`HostError::UnknownOffering`]) and the session live
    ///    ([`HostError::UnknownSession`]) — the routing gates, before any crypto;
    /// 2. the envelope must verify ([`crate::signed::verify_signed`]): a forged/tampered/spliced
    ///    signature is [`SignedError::BadSignature`], a replayed counter is
    ///    [`SignedError::StaleCounter`] (the host holds the per-`(key, session, pubkey)` ledger and
    ///    requires strictly-increasing counters), a malformed key is [`SignedError::MalformedKey`]
    ///    — each surfaced as [`HostError::Signature`];
    /// 3. on success the verified counter is CONSUMED (single-use even if the executor then
    ///    refuses the move) and the action delegates to the **existing advance path** with the
    ///    verified [`DreggIdentity`] (the canonical pubkey hex — the same handle the adapters'
    ///    cipherclerks derive), so the executor stays the sole referee and a landed move is
    ///    recorded into the resume log exactly as an unsigned one is — but with
    ///    [`Attribution::Signed`] provenance instead of `Asserted`.
    pub fn advance_signed(
        &mut self,
        key: &str,
        id: &SessionId,
        sa: SignedAction,
    ) -> Result<Outcome, HostError> {
        if !self.has(key) {
            return Err(HostError::UnknownOffering(key.to_string()));
        }
        if !self.is_open(key, id) {
            // Lazy resume-on-touch: an evicted-but-persisted session reopens by replay (its
            // signed-replay floors reload with it — see `resume`), so a signed turn lands on the
            // authentic state and a captured pre-eviction envelope still finds its counter burnt.
            match self.lazy_resume(key, id) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(HostError::UnknownSession {
                        key: key.to_string(),
                        id: id.clone(),
                    });
                }
                Err(e) => return Err(e),
            }
        }
        // The replay ledger is keyed by the canonical (lowercase) pubkey hex, so a re-cased
        // presentation of the same key cannot open a second counter lane.
        let ledger_key = (
            key.to_string(),
            id.clone(),
            sa.actor_pubkey_hex.to_ascii_lowercase(),
        );
        let expected = match self.signed_counters.get(&ledger_key) {
            None => 0,
            // A consumed u64::MAX leaves NO acceptable next counter — the lane is exhausted;
            // refuse (fail-closed) rather than overflow into re-admitting a replay.
            Some(last) => match last.checked_add(1) {
                Some(n) => n,
                None => {
                    return Err(HostError::Signature(SignedError::StaleCounter {
                        presented: sa.counter,
                        expected: u64::MAX,
                    }));
                }
            },
        };
        let actor = verify_signed(key, id, expected, &sa).map_err(HostError::Signature)?;
        // Consume the counter NOW: a verified envelope is single-use whether or not the executor
        // lands the move (see the `signed_counters` field doc for why). With a store attached the
        // consumed floor is WRITTEN THROUGH beside the move-log, so it survives lifecycle
        // eviction and a process restart (a wiped floor would re-admit a captured envelope). A
        // store that does not persist floors (`record_signed_counters` default) keeps the
        // in-memory ledger as the floor of record — eviction then retains it (fail-closed).
        let signer_hex = ledger_key.2.clone();
        self.signed_counters.insert(ledger_key, sa.counter);
        if let Some(store) = &self.resume_store {
            let _ = store.record_signed_counters(key, id, &[(signer_hex, sa.counter)]);
        }

        let out = self
            .slots
            .get_mut(key)
            .expect("offering present (checked above)")
            .advance(id, sa.action.clone(), actor.clone())
            .ok_or_else(|| HostError::UnknownSession {
                key: key.to_string(),
                id: id.clone(),
            })?;
        self.touch(key, id);
        if out.landed() {
            let attribution = Attribution::Signed {
                pubkey_hex: actor.0.clone(),
            };
            self.record_landed(key, id, sa.action, actor, attribution);
        }
        Ok(out)
    }

    /// The last consumed [`SignedAction::counter`] for `(key, id, pubkey_hex)`, if any signed
    /// advance has verified there — what a signer reads to pick its next counter (`last + 1`).
    pub fn signed_counter(&self, key: &str, id: &SessionId, pubkey_hex: &str) -> Option<u64> {
        self.signed_counters
            .get(&(key.to_string(), id.clone(), pubkey_hex.to_ascii_lowercase()))
            .copied()
    }

    /// Append a landed advance to the session's in-memory move-log and mirror it to the durable
    /// store (if attached), carrying its [`Attribution`] trust level. Shared by
    /// [`advance`](OfferingHost::advance) / [`advance_signed`](OfferingHost::advance_signed) /
    /// [`advance_collective`](OfferingHost::advance_collective).
    fn record_landed(
        &mut self,
        key: &str,
        id: &SessionId,
        input: Action,
        actor: DreggIdentity,
        attribution: Attribution,
    ) {
        if let Some(store) = &self.resume_store {
            store.record_landed_attributed(key, id, &input, &actor, &attribution);
        }
        self.logs
            .entry((key.to_string(), id.clone()))
            .or_insert_with(|| SessionMoveLog::new(key, id.clone(), SessionConfig::default()))
            .record_attributed(input, actor, attribution);
    }

    /// Advance session `(key, id)` by one real **crowd** turn carrying a [`CollectiveDecision`] (the
    /// plurality analogue of [`advance`](OfferingHost::advance)). `None` if absent.
    pub fn advance_collective(
        &mut self,
        key: &str,
        id: &SessionId,
        input: Action,
        decision: CollectiveDecision,
    ) -> Option<Outcome> {
        let carrier = decision.carrier.clone();
        let out = self
            .slots
            .get_mut(key)?
            .advance_collective(id, input.clone(), decision);
        if out.is_some() {
            self.touch(key, id);
        }
        // Record a landed crowd turn as `(action, carrier)` — the substrate admits exactly one typed
        // move attributed to the mover of record, and re-driving that reproduces the committed STATE
        // chain (the crowd's electorate/tally is beside-the-committed-turn provenance, not part of the
        // replayed state — a named residual for a richer collective-aware log).
        if let Some(o) = &out {
            if o.landed() {
                let attribution = Attribution::from(carrier.clone());
                self.record_landed(key, id, input, carrier, attribution);
            }
        }
        out
    }

    /// Render session `(key, id)`'s current [`Surface`] (`None` if absent). A successful render
    /// is a lifecycle TOUCH (a viewed session stays hot under the idle-TTL sweep).
    pub fn render(&self, key: &str, id: &SessionId) -> Option<Surface> {
        let surface = self.slots.get(key)?.render(id)?;
        self.touch(key, id);
        Some(surface)
    }

    /// Render session `(key, id)`'s current [`Surface`] **AS `viewer` sees it** — the per-viewer
    /// projection ([`Offering::render_for`]) threaded through the erasure boundary: the viewer's own
    /// hidden state (a card hand) is revealed while every other player's stays fog. `None` if the
    /// offering or session is absent. The frontend that knows the acting identity calls THIS (not the
    /// viewer-blind [`render`](OfferingHost::render)) so the right projection reaches the right person.
    pub fn render_for(&self, key: &str, id: &SessionId, viewer: &DreggIdentity) -> Option<Surface> {
        let surface = self.slots.get(key)?.render_for(id, viewer)?;
        self.touch(key, id);
        Some(surface)
    }

    /// Re-verify session `(key, id)`'s committed chain (`None` if absent).
    pub fn verify(&self, key: &str, id: &SessionId) -> Option<VerifyReport> {
        self.slots.get(key)?.verify(id)
    }

    /// What `input` would cost in session `(key, id)` (`None` if absent).
    pub fn price(&self, key: &str, id: &SessionId, input: &Action) -> Option<RunCost> {
        self.slots.get(key)?.price(id, input)
    }

    // ── The session-resume seam — move-log export, replay-resume, and a state commitment ──

    /// **Export session `(key, id)`'s move-log** — its reproducible public input (the seed + the
    /// ordered landed advances). This is the small, un-forgeable footprint a frontend persists (to a
    /// [`SessionResumeStore`]) and re-drives with [`resume`](OfferingHost::resume) to reopen the
    /// session after a restart. `None` if no session was opened under `(key, id)`.
    pub fn move_log(&self, key: &str, id: &SessionId) -> Option<SessionMoveLog> {
        self.logs.get(&(key.to_string(), id.clone())).cloned()
    }

    /// **A commitment of session `(key, id)`'s committed state** — a fingerprint over its rendered
    /// surface + its replay-verified turn count. Two sessions in the identical committed state
    /// fingerprint identically; a session in a different state fingerprints differently. This is the
    /// observable a resume asserts against: a session reopened by replaying its move-log
    /// ([`resume`](OfferingHost::resume)) fingerprints IDENTICALLY to the original (non-vacuously —
    /// a session driven to a different state does not). `None` if the session is absent.
    pub fn commitment(&self, key: &str, id: &SessionId) -> Option<Vec<u8>> {
        let surface = self.render(key, id)?;
        let report = self.verify(key, id)?;
        let mut h = blake3::Hasher::new();
        h.update(format!("{:?}", surface.0).as_bytes());
        h.update(&(report.turns as u64).to_le_bytes());
        h.update(&[report.verified as u8]);
        Some(h.finalize().as_bytes().to_vec())
    }

    /// **Reopen a session by REPLAYING its move-log** — the durable-store closure. Deploys a fresh
    /// session under the log's recorded `cfg` (the same seed), then re-drives every logged advance in
    /// order through the real executor. A legal log re-lands every move and reopens the session to its
    /// **identical committed state** ([`commitment`](OfferingHost::commitment) matches the original) —
    /// the state was never trusted, it was re-derived from the inputs.
    ///
    /// Fail-closed: a **tampered** log (a forged / ineligible / reordered advance spliced in) is
    /// REFUSED by the executor on re-drive ([`ResumeError::Refused`]) — the partially-resumed session
    /// is rolled back and nothing is left live. A tampered log cannot reopen to a forged state; it
    /// fails to reopen. Errors also if the log's offering key is unregistered
    /// ([`ResumeError::UnknownOffering`]), the fresh deploy is refused ([`ResumeError::Deploy`]), or a
    /// live session already occupies the id ([`ResumeError::AlreadyOpen`] — a resume never clobbers a
    /// running session). On success returns the reopened [`SessionId`].
    pub fn resume(&mut self, log: &SessionMoveLog) -> Result<SessionId, ResumeError> {
        if !self.has(&log.key) {
            return Err(ResumeError::UnknownOffering(log.key.clone()));
        }
        if self.is_open(&log.key, &log.id) {
            return Err(ResumeError::AlreadyOpen(log.id.clone()));
        }
        // Deploy a fresh session under the recorded seed (the replay root). Bypass the recording
        // wrapper (`open_session` would re-establish the log; we set it authoritatively below).
        {
            let slot = self
                .slots
                .get_mut(&log.key)
                .ok_or_else(|| ResumeError::UnknownOffering(log.key.clone()))?;
            slot.open(log.id.clone(), log.cfg.clone())
                .map_err(ResumeError::Deploy)?;
        }
        // Re-drive each logged advance through the REAL executor. A move that does not land is a
        // tampered log — the executor refused it (the same anti-ghost gate a live move hits).
        for (index, m) in log.moves.iter().enumerate() {
            let out = self
                .slots
                .get_mut(&log.key)
                .expect("slot present (just opened)")
                .advance(&log.id, m.action.clone(), m.actor.clone());
            let landed = matches!(&out, Some(o) if o.landed());
            if !landed {
                // Roll back the partially-resumed session — fail-closed, nothing left live.
                if let Some(slot) = self.slots.get_mut(&log.key) {
                    slot.close(&log.id);
                }
                let reason = match out {
                    Some(Outcome::Refused(why)) => why,
                    _ => "the move is not on the current ballot".to_string(),
                };
                return Err(ResumeError::Refused { index, reason });
            }
        }
        // The session reopened to its authentic state; adopt the log so further advances append to it.
        self.logs
            .insert((log.key.clone(), log.id.clone()), log.clone());
        // Reload the persisted signed-replay floors (merge MAX-wise — an in-memory floor is never
        // lowered), so a captured pre-eviction/pre-restart envelope still finds its counter burnt.
        if let Some(store) = &self.resume_store {
            for (pk, c) in store.load_signed_counters(&log.key, &log.id) {
                self.signed_counters
                    .entry((log.key.clone(), log.id.clone(), pk))
                    .and_modify(|v| *v = (*v).max(c))
                    .or_insert(c);
            }
        }
        self.touch(&log.key, &log.id);
        Ok(log.id.clone())
    }

    /// **Boot-resume every session recorded in the attached [`SessionResumeStore`]** — the restart
    /// path. Loads every stored move-log and [`resume`](OfferingHost::resume)s it, reopening each live
    /// session to its identical committed state. Returns each log paired with its resume result
    /// (`Ok(id)` reopened, `Err` a tampered / undeployable / already-open log). A no-op returning
    /// empty if no store is attached. Register the offerings BEFORE calling this (a log for an
    /// unregistered key resolves to [`ResumeError::UnknownOffering`]).
    pub fn resume_all(&mut self) -> Vec<(SessionMoveLog, Result<SessionId, ResumeError>)> {
        let logs = match &self.resume_store {
            Some(store) => store.all(),
            None => Vec::new(),
        };
        logs.into_iter()
            .map(|log| {
                let outcome = self.resume(&log);
                (log, outcome)
            })
            .collect()
    }
}

/// A deterministic session seed from a session id — `blake3(id)`'s low 8 bytes as a `u64`. The
/// SAME derivation `dreggnet-web` uses, so a host-minted id and a web route id seed identically.
fn seed_from_id(id: &str) -> u64 {
    let h = blake3::hash(id.as_bytes());
    let b = h.as_bytes();
    u64::from_le_bytes(b[..8].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dungeon::{DungeonOffering, TURN_CHOOSE};
    use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

    /// A trivial second [`Offering`] with an UNRELATED `Session` type (`u64`), so the host holds two
    /// heterogeneous session types at once — the erasure proof at the unit level. Each `advance`
    /// increments the counter and lands a synthetic (empty) receipt; verify always holds.
    struct CounterOffering;

    impl Offering for CounterOffering {
        type Session = u64;

        fn open(&self, _cfg: SessionConfig) -> Result<u64, OfferingError> {
            Ok(0)
        }
        fn actions(&self, session: &u64) -> Vec<Action> {
            vec![Action::new(
                format!("tick (now {session})"),
                "tick",
                1,
                true,
            )]
        }
        fn advance(&self, session: &mut u64, input: Action, _actor: DreggIdentity) -> Outcome {
            if input.turn != "tick" {
                return Outcome::Refused(format!("unknown: {}", input.turn));
            }
            *session += input.arg.max(0) as u64;
            Outcome::Landed {
                receipt: dregg_app_framework::TurnReceipt::default(),
                ended: false,
            }
        }
        fn verify(&self, session: &u64) -> VerifyReport {
            VerifyReport::ok(*session as usize)
        }
        fn render(&self, session: &u64) -> Surface {
            Surface(deos_view::ViewNode::Text(format!("counter = {session}")))
        }
        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    /// The host holds two HETEROGENEOUS offerings (a `DungeonSession` and a `u64` session) in ONE
    /// registry, and drives BOTH through the erased [`SessionId`] handle: open → advance (a real
    /// dungeon turn + a counter tick) → render → verify, each landing through the trait object.
    #[test]
    fn the_host_routes_two_heterogeneous_offerings_through_the_erased_handle() {
        let mut host = OfferingHost::new();
        host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        host.register("counter", "A Counter", CounterOffering);

        // The catalog lists both, in stable (BTree) order.
        let catalog = host.list_offerings();
        assert_eq!(catalog.len(), 2);
        assert_eq!(catalog[0].key, "counter");
        assert_eq!(catalog[1].key, "dungeon");

        // Open one session of each — heterogeneous `Session` types, one registry.
        let dungeon = host.open("dungeon").expect("dungeon opens");
        let counter = host.open("counter").expect("counter opens");

        // Drive a real dungeon turn through the erased handle.
        let actor = DreggIdentity("web:alice".to_string());
        let out = host
            .advance(
                "dungeon",
                &dungeon,
                Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
                actor.clone(),
            )
            .expect("dungeon session is live");
        assert!(out.landed(), "the dungeon move landed a real receipt");

        // Drive the counter offering (a different Session type) through the SAME host.
        let out = host
            .advance(
                "counter",
                &counter,
                Action::new("tick", "tick", 5, true),
                actor,
            )
            .expect("counter session is live");
        assert!(out.landed());

        // Both render + verify through the erased slot.
        assert!(host.render("dungeon", &dungeon).is_some());
        assert!(host.render("counter", &counter).is_some());
        assert!(host.verify("dungeon", &dungeon).unwrap().verified);
        let cv = host.verify("counter", &counter).unwrap();
        assert!(
            cv.verified && cv.turns == 5,
            "counter session advanced to 5"
        );

        // The catalog now reports one open session each.
        let catalog = host.list_offerings();
        assert_eq!(catalog[0].open_sessions, 1);
        assert_eq!(catalog[1].open_sessions, 1);
    }

    /// A full winning dungeon line PLAYS THROUGH the host (open → four advances → clear → verify),
    /// proving the erased handle carries a whole real playthrough, not just one turn.
    #[test]
    fn a_winning_dungeon_line_plays_through_the_host() {
        let mut host = OfferingHost::new();
        host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        let id = host.open("dungeon").expect("opens");
        let actor = DreggIdentity("party".to_string());

        for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND, KP_SEIZE] {
            let out = host
                .advance(
                    "dungeon",
                    &id,
                    Action::new("move", TURN_CHOOSE, arg as i64, true),
                    actor.clone(),
                )
                .expect("live");
            assert!(out.landed(), "move {arg} landed");
        }
        let report = host.verify("dungeon", &id).expect("live");
        assert!(
            report.verified,
            "the winning line re-verifies: {}",
            report.detail
        );
        assert_eq!(report.turns, 5, "genesis + four committed turns");
    }

    /// Routing misses are honest: an unregistered offering key, and an absent session, are `None`
    /// (a frontend-level miss before the substrate) — never a panic, never a phantom turn.
    #[test]
    fn routing_misses_are_none_not_panics() {
        let mut host = OfferingHost::new();
        host.register("dungeon", "The Warden's Keep", DungeonOffering::new());

        // Unknown offering key.
        assert!(host.actions("nope", &SessionId::new("x")).is_none());
        assert!(matches!(
            host.open("nope"),
            Err(HostError::UnknownOffering(_))
        ));

        // Known offering, absent session.
        assert!(host.render("dungeon", &SessionId::new("ghost")).is_none());
        assert!(
            host.advance(
                "dungeon",
                &SessionId::new("ghost"),
                Action::new("x", TURN_CHOOSE, 0, true),
                DreggIdentity("a".to_string()),
            )
            .is_none()
        );
    }
}
