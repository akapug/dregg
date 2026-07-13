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

use std::collections::{BTreeMap, HashMap};

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
}

impl std::fmt::Display for HostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HostError::UnknownOffering(k) => write!(f, "no offering registered under key {k:?}"),
            HostError::Deploy(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for HostError {}

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
}

impl OfferingHost {
    /// A fresh host with no offerings registered.
    pub fn new() -> Self {
        OfferingHost::default()
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
    /// deploy.
    pub fn open(&mut self, key: &str) -> Result<SessionId, HostError> {
        self.counter += 1;
        let id = SessionId::new(format!("{key}-{}", self.counter));
        let cfg = SessionConfig::with_seed(seed_from_id(&id.0));
        self.open_session(key, id.clone(), cfg)?;
        Ok(id)
    }

    /// **Ensure a session is open** under a caller-chosen `id` (the web surface's route param): open
    /// it (seeded from the id) iff it is not already live. Returns `true` if it was newly opened,
    /// `false` if it already existed. Errors if `key` is unregistered or the deploy is refused.
    pub fn ensure_open(&mut self, key: &str, id: &SessionId) -> Result<bool, HostError> {
        if !self.has(key) {
            return Err(HostError::UnknownOffering(key.to_string()));
        }
        if self.is_open(key, id) {
            return Ok(false);
        }
        let cfg = SessionConfig::with_seed(seed_from_id(&id.0));
        self.open_session(key, id.clone(), cfg)?;
        Ok(true)
    }

    /// Open a session under an explicit `id` and `cfg` (the low-level opener the two public
    /// constructors share). Errors if `key` is unregistered or the deploy is refused.
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
        slot.open(id, cfg).map_err(HostError::Deploy)
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

    /// Close (drop) session `id` of offering `key`. `true` if a session was removed.
    pub fn close(&mut self, key: &str, id: &SessionId) -> bool {
        self.slots
            .get_mut(key)
            .map(|s| s.close(id))
            .unwrap_or(false)
    }

    /// The current cap-gated affordances of session `(key, id)` — the buttons/forms a frontend
    /// paints. `None` if the offering or session is absent.
    pub fn actions(&self, key: &str, id: &SessionId) -> Option<Vec<Action>> {
        self.slots.get(key)?.actions(id)
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
        self.slots.get_mut(key)?.advance(id, input, actor)
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
        self.slots
            .get_mut(key)?
            .advance_collective(id, input, decision)
    }

    /// Render session `(key, id)`'s current [`Surface`] (`None` if absent).
    pub fn render(&self, key: &str, id: &SessionId) -> Option<Surface> {
        self.slots.get(key)?.render(id)
    }

    /// Re-verify session `(key, id)`'s committed chain (`None` if absent).
    pub fn verify(&self, key: &str, id: &SessionId) -> Option<VerifyReport> {
        self.slots.get(key)?.verify(id)
    }

    /// What `input` would cost in session `(key, id)` (`None` if absent).
    pub fn price(&self, key: &str, id: &SessionId, input: &Action) -> Option<RunCost> {
        self.slots.get(key)?.price(id, input)
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
