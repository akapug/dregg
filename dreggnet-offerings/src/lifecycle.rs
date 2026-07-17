//! # `lifecycle` — SESSION LIFECYCLE: the host-layer cap/TTL/eviction policy.
//!
//! The structural fix for backlog G2 (`docs/EXCELLENCE-BACKLOG-2026-07-16.md`): the web surface
//! and the discord bot each reimplemented session management and each got the same wounds —
//! **unbounded growth** (any URL mints a real live session, forever) and **zero throttling**.
//! The fix lives ONCE, here, in the [`OfferingHost`](crate::OfferingHost), inherited by every
//! surface that drives it: a [`SessionPolicy`] caps live sessions per offering, caps fresh opens
//! per actor, rate-limits opens, and TTL-sweeps idle sessions — with eviction made SAFE by the
//! durable resume seam (an evicted persisted session resumes lazily on its next touch, state
//! intact: hot sessions in memory, cold on disk).
//!
//! ## The policy (all `None` = today's unbounded behavior, byte-identical)
//!
//! [`SessionPolicy`] is attached with [`OfferingHost::with_policy`](crate::OfferingHost::with_policy)
//! together with a [`Clock`] (time is INJECTED — a wall-clock [`SystemClock`] in deployment, a
//! [`ManualClock`] in tests — never read ambiently inside the logic). A host without a policy, or
//! with the default all-`None` policy, tracks nothing and refuses nothing: the pre-lifecycle
//! behavior, byte-identical.
//!
//! ## Eviction safety — the two rules
//!
//! 1. **A session may only be evicted if it can come back, or the policy explicitly accepts the
//!    loss.** With a resume store attached, every open + landed advance is already written through
//!    (the durable move-log IS the session), so eviction just drops the live slot + in-memory
//!    bookkeeping and the session resumes by replay on its next touch. Without a store, eviction
//!    is REFUSED unless the policy opts into it by name ([`SessionPolicy::evict_unpersisted`] —
//!    honest lossy shedding for a deployment whose sessions were ephemeral anyway).
//! 2. **Eviction must never reset a signed-replay floor.** The host's per-`(offering, session,
//!    pubkey)` counter ledger is what refuses a replayed [`SignedAction`](crate::SignedAction);
//!    wiping it at eviction would let a captured envelope replay after resume. The choice made
//!    here (the counter-survival design):
//!    - the host **writes each consumed counter through** to the attached store the moment
//!      [`advance_signed`](crate::OfferingHost::advance_signed) consumes it (so the floors survive
//!      not just eviction but a hard process restart — `resume`/`resume_all` reload them,
//!      merge-max, never lowering an in-memory floor);
//!    - at eviction the floors are re-recorded to the store and dropped from memory ONLY if the
//!      store confirms it persisted them ([`SessionResumeStore::record_signed_counters`]
//!      (crate::resume::SessionResumeStore::record_signed_counters) returns `true`; the default
//!      impl returns `false` so a legacy store that never heard of counters causes the host to
//!      RETAIN the floors in memory — fail-closed, a small map instead of a replay hole);
//!    - a **lossy** eviction (no store) always retains the floors in memory: the session id can be
//!      re-minted fresh (same deterministic seed), and a wiped ledger would let every captured
//!      envelope re-drive it. A few `u64`s per signer is the price of a closed replay lane.
//!
//! ## The trust boundary of per-actor quotas — stated, not laundered
//!
//! Opener quotas key on the opener's [`Attribution`](crate::Attribution):
//! - a **`Signed`** opener's quota keys on its VERIFIED pubkey — this quota is real enforcement
//!   (minting a fresh key costs a keypair, and rung-2 device-held keys make it a real identity);
//! - an **`Asserted`** opener's quota keys on the asserted label — a forgeable cookie/param, so
//!   this quota is ADVISORY: it stops accidental runaway (a crawler, a stuck client), not a
//!   determined attacker who mints labels. The real backstops against that attacker are the
//!   per-offering capacity cap + the idle TTL, which key on nothing forgeable.
//!
//! The two lanes are namespaced (`s:<pubkey>` vs `a:<label>`) so an asserted label can never
//! collide into — or spend — a signed key's quota.

use std::cell::Cell;
use std::rc::Rc;

use crate::SessionId;
use crate::signed::Attribution;

// ─────────────────────────────────────────────────────────────────────────────
// TIME — injected, never read ambiently.
// ─────────────────────────────────────────────────────────────────────────────

/// **An injected time source** — seconds (a monotone-enough epoch; deployment uses UNIX seconds
/// via [`SystemClock`], tests drive a [`ManualClock`]). The host never reads a wall clock inside
/// its logic; every `now` flows through the one clock attached with
/// [`OfferingHost::with_policy`](crate::OfferingHost::with_policy).
pub trait Clock {
    /// The current time, in seconds.
    fn now(&self) -> u64;
}

/// The deployment [`Clock`] — UNIX epoch seconds from the system clock.
#[derive(Debug, Clone, Copy, Default)]
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    }
}

/// **The deterministic test [`Clock`]** — a hand-cranked time the tests advance explicitly.
/// Cheaply [`Clone`]able (an `Rc` share of one cell), so a test hands one clone to the host and
/// keeps another to drive time; `!Send`, like the host it serves.
#[derive(Debug, Clone, Default)]
pub struct ManualClock(Rc<Cell<u64>>);

impl ManualClock {
    /// A manual clock starting at `start` seconds.
    pub fn new(start: u64) -> Self {
        ManualClock(Rc::new(Cell::new(start)))
    }

    /// Set the clock to an absolute time.
    pub fn set(&self, now: u64) {
        self.0.set(now);
    }

    /// Advance the clock by `secs`.
    pub fn advance(&self, secs: u64) {
        self.0.set(self.0.get().saturating_add(secs));
    }
}

impl Clock for ManualClock {
    fn now(&self) -> u64 {
        self.0.get()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE POLICY.
// ─────────────────────────────────────────────────────────────────────────────

/// **The session-lifecycle policy** — every knob `None` (the [`Default`]) is today's unbounded
/// behavior, byte-identical: nothing tracked, nothing refused, nothing evicted. Each `Some` arms
/// one gate. See the module doc for the eviction-safety and quota trust-boundary rules.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SessionPolicy {
    /// Cap on LIVE sessions per offering. An open past the cap first tries to EVICT the
    /// coldest (longest-idle) evictable session of that offering (LRU); if nothing is evictable
    /// the open is refused ([`PolicyRefusal::Capacity`]).
    pub max_sessions_per_offering: Option<usize>,
    /// Cap on live sessions FRESH-MINTED per opener (quota-keyed on the opener's
    /// [`Attribution`] — see the module doc's trust boundary: `Signed` quotas are real,
    /// `Asserted` quotas are advisory). Eviction/close of a minted session frees its slot.
    /// Opens with no opener attribution are not per-actor gated (there is no actor to key);
    /// capacity + TTL still bound them.
    pub max_opens_per_actor: Option<usize>,
    /// Idle time-to-live: a session untouched (no open / advance / render) for MORE than this
    /// many seconds is evicted by [`sweep`](crate::OfferingHost::sweep) — safely (resumable from
    /// the store) or, only under [`evict_unpersisted`](SessionPolicy::evict_unpersisted), lossily.
    pub idle_ttl_secs: Option<u64>,
    /// Minimum seconds between FRESH session mints per opener (the anti-burst rate gate; a touch
    /// or lazy resume of an existing session is never rate-gated). Like the quota, keyed on the
    /// opener attribution and skipped for attribution-less opens.
    pub min_open_interval_secs: Option<u64>,
    /// **The honest lossy-eviction opt-in.** Without a resume store an evicted session is GONE
    /// (no move-log survives to resume from); by default the host therefore refuses to evict
    /// unpersisted sessions (capacity refuses instead; the TTL sweep reports them as retained).
    /// Set this `true` only for a deployment whose sessions are ephemeral anyway (they would not
    /// survive a restart either) and where shedding the coldest beats unbounded growth.
    pub evict_unpersisted: bool,
}

impl SessionPolicy {
    /// The unbounded (default) policy — today's behavior, byte-identical.
    pub fn unbounded() -> Self {
        SessionPolicy::default()
    }

    /// Whether every gate is disarmed (all four knobs `None`) — the host then tracks nothing
    /// and refuses nothing, exactly the pre-lifecycle behavior.
    pub fn is_unbounded(&self) -> bool {
        self.max_sessions_per_offering.is_none()
            && self.max_opens_per_actor.is_none()
            && self.idle_ttl_secs.is_none()
            && self.min_open_interval_secs.is_none()
    }
}

/// **Why a policy gate refused an open** — each variant names the limit that tripped, so a
/// surface can answer with the honest status (a 429, a retry-after) instead of a generic error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyRefusal {
    /// The opener is at its live fresh-mint quota ([`SessionPolicy::max_opens_per_actor`]).
    ActorQuota {
        /// The opener's quota key (`s:<pubkey>` for a signed opener, `a:<label>` for an
        /// asserted one — see the module doc's trust boundary).
        actor: String,
        /// The quota that is full.
        limit: usize,
    },
    /// The opener minted a session too recently ([`SessionPolicy::min_open_interval_secs`]).
    OpenRate {
        /// Seconds until the opener's next mint would be admitted.
        retry_after_secs: u64,
    },
    /// The offering is at its live-session cap and nothing was evictable
    /// ([`SessionPolicy::max_sessions_per_offering`]).
    Capacity {
        /// The offering at capacity.
        key: String,
        /// The cap that is full.
        limit: usize,
    },
}

impl std::fmt::Display for PolicyRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolicyRefusal::ActorQuota { actor, limit } => write!(
                f,
                "open quota reached: opener {actor:?} already holds {limit} live session(s)"
            ),
            PolicyRefusal::OpenRate { retry_after_secs } => write!(
                f,
                "opening too fast: next open admitted in {retry_after_secs}s"
            ),
            PolicyRefusal::Capacity { key, limit } => write!(
                f,
                "offering {key:?} is at its {limit}-session capacity and no session is evictable"
            ),
        }
    }
}

/// **What a [`sweep`](crate::OfferingHost::sweep) did** — which sessions were evicted (safe to
/// resume from the store, or lossily under the named opt-in), and which idle-past-TTL sessions
/// were RETAINED because evicting them would lose state the policy did not agree to lose.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SweepReport {
    /// The sessions evicted this sweep, `(offering key, session id)`.
    pub evicted: Vec<(String, SessionId)>,
    /// Idle-past-TTL sessions kept live: no resume store is attached and the policy did not opt
    /// into lossy eviction ([`SessionPolicy::evict_unpersisted`] is `false`).
    pub retained_unpersisted: Vec<(String, SessionId)>,
}

impl SweepReport {
    /// Whether the sweep changed nothing (nothing evicted, nothing flagged retained).
    pub fn is_empty(&self) -> bool {
        self.evicted.is_empty() && self.retained_unpersisted.is_empty()
    }
}

/// The quota key an opener [`Attribution`] buckets under — `s:<pubkey>` for a verified signer,
/// `a:<label>` for an asserted label. Namespaced so a forgeable asserted label can never collide
/// into (or spend) a signed key's quota. See the module doc's trust boundary.
pub(crate) fn quota_key(a: &Attribution) -> String {
    match a {
        Attribution::Signed { pubkey_hex } => format!("s:{pubkey_hex}"),
        Attribution::Asserted { label } => format!("a:{label}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The manual clock is shared through its clones (one host handle, one test handle), and the
    /// default policy is honestly unbounded.
    #[test]
    fn manual_clock_shares_and_default_policy_is_unbounded() {
        let clock = ManualClock::new(10);
        let host_handle = clock.clone();
        clock.advance(5);
        assert_eq!(host_handle.now(), 15);
        host_handle.set(100);
        assert_eq!(clock.now(), 100);

        assert!(SessionPolicy::default().is_unbounded());
        assert!(
            !SessionPolicy {
                idle_ttl_secs: Some(1),
                ..SessionPolicy::default()
            }
            .is_unbounded()
        );
        // The lossy opt-in alone arms no gate — it only names what an armed gate may do.
        assert!(
            SessionPolicy {
                evict_unpersisted: true,
                ..SessionPolicy::default()
            }
            .is_unbounded()
        );
    }

    /// Signed and asserted openers bucket into DISJOINT quota namespaces even over the same
    /// string — a forged label cannot spend a signed key's quota.
    #[test]
    fn quota_keys_namespace_signed_and_asserted() {
        let s = quota_key(&Attribution::Signed {
            pubkey_hex: "ab".repeat(32),
        });
        let a = quota_key(&Attribution::Asserted {
            label: "ab".repeat(32),
        });
        assert_ne!(s, a);
        assert!(s.starts_with("s:"));
        assert!(a.starts_with("a:"));
    }
}
