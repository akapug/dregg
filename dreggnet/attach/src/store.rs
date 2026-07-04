//! The per-subject **session store** — and **the cap-scoping teeth**: a signed-in
//! user sees + drives ONLY their own sessions. Another user's session is isolated;
//! a request for it (read, stream, or verify) resolves to nothing.
//!
//! The authority model is the dregg webauth `dga1_` forward-auth: Caddy verifies
//! the presented capability and echoes the credential's stable **subject**
//! (`dregg:<16 hex>`, [`dreggnet_webauth::subject_of`]) onto the upstream request
//! as `X-Dregg-Subject`. That subject IS the cap holder = the session owner. So
//! scoping is one rule applied uniformly:
//!
//! > a session is reachable by a user **iff** `session.owner() == subject`.
//!
//! The store generates the session id and stamps the **verified** subject as the
//! owner at create time — never a body/param field a caller could spoof — so a
//! user can neither create a session as someone else nor reach another's by id.

use std::collections::BTreeMap;
use std::sync::Mutex;

use crate::driver::{DemoDriver, SessionDriver};
use crate::session::{AgentSession, GoalRequest, Owned};

/// The default per-subject live-session quota — how many sessions one signed-in
/// subject may hold at once (the exhaustion-vector backstop). A tenant cannot pin
/// unbounded sessions (each holds a confined run + receipt chain in memory).
pub const DEFAULT_MAX_PER_SUBJECT: usize = 16;

/// The default global live-session cap across ALL subjects (the connection-limit
/// backstop) — bounds total store memory regardless of how many subjects connect.
pub const DEFAULT_MAX_TOTAL: usize = 2048;

/// Why a session could not be created.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum StoreError {
    /// The subject already holds the maximum number of live sessions.
    #[error("session quota reached for this subject ({limit}); close one to open another")]
    SubjectQuota {
        /// The per-subject ceiling.
        limit: usize,
    },
    /// The global live-session cap is reached (server at capacity).
    #[error("the server is at its global session capacity ({limit}); retry shortly")]
    GlobalQuota {
        /// The global ceiling.
        limit: usize,
    },
}

/// An unguessable 64-bit word for the random half of a session id. `RandomState`
/// keys from the OS RNG at construction, so hashing a fixed value under a fresh
/// key yields entropy a remote caller cannot predict — no extra crypto dependency.
fn rand_word() -> u64 {
    use std::hash::{BuildHasher, Hasher};
    let mut h = std::collections::hash_map::RandomState::new().build_hasher();
    h.write_u8(0xD6);
    h.finish()
}

/// Keep only the items owned by `subject` — the single cap-scoping filter every
/// read rides. Pure, total, order-preserving.
pub fn scope<T: Owned + Clone>(items: &[T], subject: &str) -> Vec<T> {
    items
        .iter()
        .filter(|i| i.owner() == subject)
        .cloned()
        .collect()
}

/// The in-memory session store: it drives goals into sessions (via a
/// [`SessionDriver`]) and serves them back cap-scoped to their owner.
///
/// The shipped store uses the [`DemoDriver`] (the green-standalone path). The
/// reviewed-go swap is [`SessionStore::with_driver`] over a driver backed by the
/// live hosted session backend — the cap-scoping teeth below hold identically
/// over live sessions.
pub struct SessionStore {
    driver: Box<dyn SessionDriver>,
    inner: Mutex<Inner>,
    /// Max live sessions per subject (the per-tenant quota).
    max_per_subject: usize,
    /// Max live sessions across all subjects (the global cap).
    max_total: usize,
}

#[derive(Default)]
struct Inner {
    sessions: BTreeMap<String, AgentSession>,
    next: u64,
}

impl Default for SessionStore {
    fn default() -> Self {
        SessionStore::new()
    }
}

impl SessionStore {
    /// A store over the deterministic demo driver (reproducible per-session roots).
    pub fn new() -> SessionStore {
        SessionStore::with_driver(Box::new(DemoDriver::seeded([0xA7u8; 32])))
    }

    /// A store over a custom [`SessionDriver`] (the reviewed-go live backend), with
    /// the default per-subject + global quotas.
    pub fn with_driver(driver: Box<dyn SessionDriver>) -> SessionStore {
        SessionStore {
            driver,
            inner: Mutex::new(Inner::default()),
            max_per_subject: DEFAULT_MAX_PER_SUBJECT,
            max_total: DEFAULT_MAX_TOTAL,
        }
    }

    /// Set the per-subject + global live-session quotas (the exhaustion-vector
    /// backstop). `0` for either disables that bound (not recommended in prod).
    pub fn with_quota(mut self, max_per_subject: usize, max_total: usize) -> SessionStore {
        self.max_per_subject = max_per_subject;
        self.max_total = max_total;
        self
    }

    /// Mint the next stable session id (`sess_<counter><random>`).
    ///
    /// The id is the monotone counter (collision-free, and the high-order part so
    /// "newest first" still sorts) followed by an OS-seeded random word
    /// (unguessable). So a session id is NOT an enumeration oracle: a tenant cannot
    /// walk `sess_000001, sess_000002, …` and probe for other tenants' ids. Access
    /// is already cap-scoped to the owner (a non-owned id 404s); this removes the
    /// predictable-id surface underneath that, defence in depth.
    fn next_id(&self) -> String {
        let mut g = self.inner.lock().expect("session store mutex");
        g.next += 1;
        format!("sess_{:08x}{:016x}", g.next, rand_word())
    }

    /// **Create + drive** a session for the *verified* `owner` (never a spoofable
    /// field), enforcing the per-subject + global session quotas. The store mints
    /// the id, drives the goal confined, stores the session under that owner, and
    /// returns it — or [`StoreError`] when the owner (or the server) is at capacity,
    /// closing the resource-exhaustion vector (a tenant cannot pin unbounded
    /// sessions; the server's total memory is bounded).
    pub fn create(&self, req: &GoalRequest, owner: &str) -> Result<AgentSession, StoreError> {
        // Check the quotas BEFORE driving the goal (no work for a refused create).
        {
            let g = self.inner.lock().expect("session store mutex");
            if let Some(e) = self.quota_check(&g, owner) {
                return Err(e);
            }
        }
        let id = self.next_id();
        let session = self.driver.drive(req, owner, &id);
        let mut g = self.inner.lock().expect("session store mutex");
        // Re-check under the lock (another thread may have filled the quota during
        // the drive) — fail-closed on the race.
        if let Some(e) = self.quota_check(&g, owner) {
            return Err(e);
        }
        g.sessions.insert(id, session.clone());
        Ok(session)
    }

    /// `Some(error)` iff admitting one more session for `subject` would breach the
    /// per-subject or global quota. `0` disables a bound.
    fn quota_check(&self, inner: &Inner, subject: &str) -> Option<StoreError> {
        if self.max_total != 0 && inner.sessions.len() >= self.max_total {
            return Some(StoreError::GlobalQuota {
                limit: self.max_total,
            });
        }
        if self.max_per_subject != 0 {
            let owned = inner
                .sessions
                .values()
                .filter(|s| s.owner() == subject)
                .count();
            if owned >= self.max_per_subject {
                return Some(StoreError::SubjectQuota {
                    limit: self.max_per_subject,
                });
            }
        }
        None
    }

    /// **Fork** one of `subject`'s sessions — the cell superpower (`fork = scale`)
    /// surfaced as a real cockpit action, and a live **attenuation** demo. The
    /// child's authority is a *subset* of the parent's by construction: the same
    /// (or fewer) caps, and **half the budget ceiling** — a fork can never
    /// out-reach its parent. The child is a fresh, independently re-witnessable
    /// session owned by the same subject, linked back via [`AgentSession::parent`].
    ///
    /// Returns `None` (no existence oracle) when `parent_id` is not the subject's —
    /// you can only fork your own sessions; the cap-scoping teeth hold identically.
    pub fn fork_for(&self, parent_id: &str, subject: &str) -> Option<AgentSession> {
        let parent = self.get_for_subject(parent_id, subject)?;

        // A fork is a new live session — it counts against the quota too, so a
        // tenant cannot exhaust the store by forking. Over quota → None (no new
        // session), the same fail-closed shape as a missing parent.
        {
            let g = self.inner.lock().expect("session store mutex");
            if self.quota_check(&g, subject).is_some() {
                return None;
            }
        }

        // Attenuate: derive the child bundle from the parent's granted caps (a
        // subset), and halve the ceiling. Both are ≤ the parent — strictly less
        // authority, the lattice descent made tangible.
        let services: Vec<String> = parent
            .caps()
            .iter()
            .filter_map(|c| c.strip_prefix("invoke:").map(str::to_string))
            .collect();
        let cells: Vec<String> = parent
            .caps()
            .iter()
            .filter_map(|c| c.strip_prefix("cell-write:").map(str::to_string))
            .collect();
        let budget = (parent.budget() / 2).max(1);

        let mut req = GoalRequest::new(format!("fork of: {}", parent.goal()), budget);
        req.services = services;
        req.cells = cells;
        let req = req.sanitized();

        let id = self.next_id();
        let mut child = self.driver.drive(&req, subject, &id);
        child.parent = Some(parent_id.to_string());
        let mut g = self.inner.lock().expect("session store mutex");
        g.sessions.insert(id, child.clone());
        Some(child)
    }

    /// **Cap-scoped get** — the teeth: returns the session **iff** it is owned by
    /// `subject`. A request for another subject's session resolves to `None`
    /// (isolation), indistinguishable from a non-existent id (no existence oracle).
    pub fn get_for_subject(&self, id: &str, subject: &str) -> Option<AgentSession> {
        let g = self.inner.lock().expect("session store mutex");
        g.sessions.get(id).filter(|s| s.owner() == subject).cloned()
    }

    /// Every session owned by `subject`, newest first — the user's "my sessions".
    pub fn list_for(&self, subject: &str) -> Vec<AgentSession> {
        let g = self.inner.lock().expect("session store mutex");
        let mut v: Vec<AgentSession> =
            scope(&g.sessions.values().cloned().collect::<Vec<_>>(), subject);
        v.sort_by(|a, b| b.id.cmp(&a.id));
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    fn req(goal: &str) -> GoalRequest {
        GoalRequest::new(goal, 50)
            .with_service("run_tests")
            .with_cell("/goal")
    }

    // ── TOOTH: session ids are not an enumeration oracle ──────────────────────
    // A tenant must not be able to guess another tenant's session id by walking a
    // sequence. The id carries a monotone counter (uniqueness + ordering) AND an
    // OS-seeded random word (unguessability), so neither half alone lets a caller
    // predict the next/other ids.
    #[test]
    fn session_ids_are_unguessable_not_sequential() {
        let store = SessionStore::new();
        let a = store.create(&req("g1"), ALICE).unwrap();
        let b = store.create(&req("g2"), ALICE).unwrap();
        // Not the old sequential form (`sess_000001`/`sess_000002`).
        assert_ne!(a.id, "sess_000001");
        assert_ne!(b.id, "sess_000002");
        assert_ne!(a.id, b.id);
        // The random tails differ — the id is not derivable from the counter alone.
        let tail = |id: &str| {
            id.trim_start_matches("sess_")
                .chars()
                .rev()
                .take(16)
                .collect::<String>()
        };
        assert_ne!(
            tail(&a.id),
            tail(&b.id),
            "the random half must differ across ids"
        );
        // Knowing one id does not reveal the other (no shared guessable suffix).
        assert!(store.get_for_subject("sess_000002", ALICE).is_none());
    }

    // ── TOOTH: a user reaches ONLY their own session, never another's ──────────
    #[test]
    fn a_user_reaches_only_their_own_session() {
        let store = SessionStore::new();
        let a = store.create(&req("alice's goal"), ALICE).unwrap();
        let b = store.create(&req("bob's SECRET goal"), BOB).unwrap();
        assert_ne!(a.id, b.id);

        // Alice gets her own.
        assert!(store.get_for_subject(&a.id, ALICE).is_some());
        // Alice CANNOT reach bob's session by id — isolated, indistinguishable
        // from a non-existent id.
        assert!(
            store.get_for_subject(&b.id, ALICE).is_none(),
            "bob's session is isolated from alice"
        );
        // Bob cannot reach alice's either.
        assert!(store.get_for_subject(&a.id, BOB).is_none());
        // Each owner reaches their own.
        assert!(store.get_for_subject(&b.id, BOB).is_some());
    }

    // ── TOOTH: the owner is the VERIFIED subject, stamped at create ────────────
    #[test]
    fn the_owner_is_the_creating_subject() {
        let store = SessionStore::new();
        let s = store.create(&req("g"), ALICE).unwrap();
        assert_eq!(s.owner, ALICE, "owned by the creating (verified) subject");
        // A stranger never owns it, regardless of the goal text.
        assert!(
            store
                .get_for_subject(&s.id, "dregg:0000000000000000")
                .is_none()
        );
    }

    // ── TOOTH: 'my sessions' lists are disjoint across subjects ────────────────
    #[test]
    fn my_sessions_are_disjoint_across_subjects() {
        let store = SessionStore::new();
        store.create(&req("a1"), ALICE).unwrap();
        store.create(&req("a2"), ALICE).unwrap();
        store.create(&req("b1"), BOB).unwrap();

        let alice = store.list_for(ALICE);
        let bob = store.list_for(BOB);
        assert_eq!(alice.len(), 2);
        assert_eq!(bob.len(), 1);
        assert!(alice.iter().all(|s| s.owner == ALICE));
        assert!(bob.iter().all(|s| s.owner == BOB));
        let a_ids: std::collections::BTreeSet<_> = alice.iter().map(|s| &s.id).collect();
        let b_ids: std::collections::BTreeSet<_> = bob.iter().map(|s| &s.id).collect();
        assert!(
            a_ids.is_disjoint(&b_ids),
            "no shared session across subjects"
        );
    }

    // ── a fork is owned by the subject, ATTENUATED, and re-witnesses ───────────
    #[test]
    fn a_fork_is_attenuated_and_re_witnessable() {
        use dreggnet_exec::live::verify_live;
        let store = SessionStore::new();
        let parent = store.create(&req("ship the release"), ALICE).unwrap();
        let child = store
            .fork_for(&parent.id, ALICE)
            .expect("alice forks her own");

        // Same owner, linked to the parent, distinct id.
        assert_eq!(child.owner, ALICE);
        assert_eq!(child.parent.as_deref(), Some(parent.id.as_str()));
        assert_ne!(child.id, parent.id);
        // STRICTLY LESS authority: the child's ceiling is below the parent's.
        assert!(child.budget() < parent.budget(), "the fork is attenuated");
        // It is a real, independently re-witnessable session.
        assert!(verify_live(&child.run).is_ok(), "the fork re-witnesses");
        // And it shows up in the subject's own list.
        assert!(store.list_for(ALICE).iter().any(|s| s.id == child.id));
    }

    // ── TOOTH: you can only fork YOUR OWN session ──────────────────────────────
    #[test]
    fn forking_anothers_session_is_refused() {
        let store = SessionStore::new();
        let alice = store.create(&req("alice's goal"), ALICE).unwrap();
        // Bob cannot fork Alice's session — isolated, no existence oracle.
        assert!(store.fork_for(&alice.id, BOB).is_none());
        // A non-existent id is likewise None (indistinguishable).
        assert!(store.fork_for("sess_ffffff", ALICE).is_none());
    }

    // ── an unknown subject has no sessions ─────────────────────────────────────
    #[test]
    fn an_unknown_subject_has_nothing() {
        let store = SessionStore::new();
        store.create(&req("g"), ALICE).unwrap();
        assert!(store.list_for("dregg:stranger00000000").is_empty());
    }

    // ── TOOTH: a per-subject quota bounds the exhaustion vector ────────────────
    #[test]
    fn a_subject_cannot_exceed_its_session_quota() {
        // A tiny quota: 2 per subject, 10 global.
        let store = SessionStore::new().with_quota(2, 10);
        // Alice fills her quota.
        store.create(&req("a1"), ALICE).unwrap();
        store.create(&req("a2"), ALICE).unwrap();
        // The third is refused with the per-subject quota error — no session minted.
        assert!(matches!(
            store.create(&req("a3"), ALICE),
            Err(StoreError::SubjectQuota { limit: 2 })
        ));
        assert_eq!(
            store.list_for(ALICE).len(),
            2,
            "no third session was stored"
        );
        // BOB is unaffected by ALICE's quota (it is per-subject).
        store.create(&req("b1"), BOB).unwrap();
        assert_eq!(store.list_for(BOB).len(), 1);
        // Forking is also bounded — Alice at quota cannot fork a new session either.
        let parent = store.list_for(ALICE)[0].clone();
        assert!(
            store.fork_for(&parent.id, ALICE).is_none(),
            "a fork over quota is refused (no new session)"
        );
    }

    // ── TOOTH: the global cap bounds total store memory ────────────────────────
    #[test]
    fn the_global_cap_bounds_total_sessions() {
        // Global cap of 2, generous per-subject.
        let store = SessionStore::new().with_quota(100, 2);
        store.create(&req("a1"), ALICE).unwrap();
        store.create(&req("b1"), BOB).unwrap();
        // A third session by ANY subject is refused — the server is at capacity.
        assert!(matches!(
            store.create(&req("c1"), "dregg:cccc2222cccc2222"),
            Err(StoreError::GlobalQuota { limit: 2 })
        ));
    }
}
