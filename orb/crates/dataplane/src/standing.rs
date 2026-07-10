//! Per-source STANDING counters for the reactor accept path — the state the
//! sans-IO serve fold structurally cannot carry.
//!
//! The proven serve stages `Reactor.Stage.ConnLimit` / `StickTable` / `Slowloris`
//! decide on PER-SOURCE STANDING state (how many connections a source has open
//! right now, its aggregated request rate, how long its header phase has run). The
//! serve fold is one stateless `ByteArray -> ByteArray` call per request
//! (`ctxOfMetered` supplies only the client IP + a per-connection sequence number),
//! so that standing state cannot ride the fold: it lives in the ACCEPT PATH, which
//! owns the connection lifecycle. This module is that store.
//!
//! ## No lock on the hot path
//!
//! A [`Standing`] is created ONCE PER SHARD and only ever touched by that shard's
//! single event-loop thread (io_uring / kqueue). Increments and decrements are
//! therefore plain field writes — no atomic, no mutex, nothing shared across
//! shards. Per-source parallelism is by partition (each shard owns its own
//! sources' counters for the connections it accepted); there is no global map to
//! contend on. This mirrors the shard-local `Conn`/`Slab` discipline in `uring.rs`.
//!
//! ## The accept/close discipline (decrement-exactly-once)
//!
//! [`Standing::on_accept`] is called EXACTLY ONCE per connection that enters the
//! shard's slab, at accept; [`Standing::on_close`] EXACTLY ONCE at close (every
//! close path funnels through the reactor's single `close`). So
//! `active(ip) = #accepted(ip) - #closed(ip)` and never goes negative — this is
//! the invariant proven in `Reactor/StandingCounters.lean` (`conn_conservation`).
//! A counter leak (a missing decrement) would wedge the limiter permanently, so
//! the once-each discipline is load-bearing and is both proven and live-tested.

use std::collections::HashMap;
use std::net::IpAddr;
use std::time::{Duration, Instant};

/// A per-source REQUEST-RATE window: how many request arrivals from this source have
/// landed since the window opened, and when it opened. The window is a fixed span
/// (`rate-window`) that AGES — once the span elapses the window is reset (`start`
/// advanced, `count` zeroed), so a source that pauses recovers and the counter never
/// leaks. This is the standing state the reactor consults against the `rate-limit`
/// cap; the proven decision (`Reactor.Stage.StickTable.admits` / `resp429`) decides.
struct RateWindow {
    /// When the current window opened (the last reset instant).
    start: Instant,
    /// Request arrivals counted in the current (unelapsed) window.
    count: u32,
}

/// **The slowloris expiry decision** — mirrors `Reactor.Stage.Slowloris.expired`:
/// with protection enabled (`timeout != 0`) a header phase that began at `started`
/// is expired at `now` iff the elapsed span has reached the timeout
/// (`now - started >= timeout`). A zero `timeout` disables the gate (never expires).
/// Total; the reactor drops an expired connection with the proven `resp408`.
pub fn header_expired(timeout: Duration, started: Instant, now: Instant) -> bool {
    !timeout.is_zero() && now.duration_since(started) >= timeout
}

/// Per-source standing counters owned by a single shard thread.
#[derive(Default)]
pub struct Standing {
    /// Active concurrent connections per source IP. An entry is dropped when it
    /// falls to zero, so the map's size is bounded by the number of sources with
    /// at least one live connection — a flood that opens and closes leaves no
    /// residue (no unbounded growth from transient peers).
    active: HashMap<IpAddr, u32>,
    /// Per-source request-rate window (for the `rate-limit`/`429` gate). An entry
    /// is created on a source's first arrival and reclaimed by [`Standing::rate_prune`]
    /// once its window has fully elapsed (an idle source leaves no residue), so the
    /// map stays bounded by the sources active within the last window.
    rate: HashMap<IpAddr, RateWindow>,
}

impl Standing {
    pub fn new() -> Self {
        Standing {
            active: HashMap::new(),
            rate: HashMap::new(),
        }
    }

    /// **Note a request arrival from `ip` against the rate gate.** Ages the source's
    /// window first (if the fixed `window` span has elapsed since it opened, reset it
    /// — the sliding-window recovery, no leak), then counts this arrival. Returns
    /// `true` iff the arrival is OVER `limit` (the reactor then answers `429` and
    /// closes WITHOUT dispatching). `limit == 0` disables the gate entirely (always
    /// `false`, no bookkeeping) — the unlimited default. Called once per accepted
    /// connection, on the single shard thread (no lock).
    pub fn rate_note(&mut self, ip: IpAddr, limit: u32, window: Duration, now: Instant) -> bool {
        if limit == 0 {
            return false;
        }
        let w = self.rate.entry(ip).or_insert(RateWindow {
            start: now,
            count: 0,
        });
        // The window AGES: once its span has elapsed, open a fresh window. This is the
        // recovery edge — a source that stops for a full window is counted from zero
        // again, so the limiter can never wedge a source that has gone quiet.
        if now.duration_since(w.start) >= window {
            w.start = now;
            w.count = 0;
        }
        w.count = w.count.saturating_add(1);
        w.count > limit
    }

    /// The source's current in-window arrival count (`0` for an unseen source, or one
    /// whose window has elapsed but not yet been re-noted). For tests / introspection.
    pub fn rate_count(&self, ip: IpAddr, window: Duration, now: Instant) -> u32 {
        match self.rate.get(&ip) {
            Some(w) if now.duration_since(w.start) < window => w.count,
            _ => 0,
        }
    }

    /// Reclaim rate-window entries whose window has fully elapsed by `now` — idle
    /// sources leave no residue, bounding the map to sources active within the last
    /// `window`. Called opportunistically off the shard's periodic sweep, mirroring
    /// the drop-at-zero discipline of the connection counter.
    pub fn rate_prune(&mut self, window: Duration, now: Instant) {
        self.rate
            .retain(|_, w| now.duration_since(w.start) < window);
    }

    /// The source's current active-connection count (`0` for an unseen source).
    /// Read on the accept path BEFORE this connection's own increment: the gate
    /// admits iff this count is under the configured cap.
    pub fn active(&self, ip: IpAddr) -> u32 {
        self.active.get(&ip).copied().unwrap_or(0)
    }

    /// Record a newly accepted connection from `ip` (increment). Called exactly
    /// once per connection that enters the slab, at accept.
    pub fn on_accept(&mut self, ip: IpAddr) {
        *self.active.entry(ip).or_insert(0) += 1;
    }

    /// Record a connection from `ip` closing (decrement). Called exactly once per
    /// connection that entered the slab, at close (all paths: served, EOF, error,
    /// refusal-after-503). Drops the entry at zero so the map stays bounded.
    /// Saturating at zero as defence in depth — the accept/close discipline keeps
    /// it exact, but a stray decrement can never wrap below zero and wedge the gate.
    pub fn on_close(&mut self, ip: IpAddr) {
        if let Some(n) = self.active.get_mut(&ip) {
            *n = n.saturating_sub(1);
            if *n == 0 {
                self.active.remove(&ip);
            }
        }
    }
}

/// A SHARED per-source counter for the thread-per-connection blocking reactor,
/// whose accept loop and per-connection worker threads run concurrently (unlike
/// the single-threaded shard reactors, which use [`Standing`] with no lock).
///
/// Sharded into `STRIPES` independent buckets keyed by a hash of the source IP, so
/// two different sources almost never contend and there is NO single global mutex
/// on the accept path — the contention on any one stripe is `1/STRIPES` of the
/// source population. (The blocking reactor is the portable fallback, not the
/// flagship hot path; the io_uring / kqueue shards use the lock-free [`Standing`].)
/// The accept/close discipline is identical: increment once at accept, decrement
/// once when the worker thread returns.
pub struct SharedStanding {
    stripes: Vec<std::sync::Mutex<HashMap<IpAddr, u32>>>,
    /// Striped per-source request-rate windows, for the blocking reactor's `429`
    /// gate — the same fixed-sliding-window discipline as [`Standing::rate_note`],
    /// striped so concurrent accept threads from different sources rarely contend.
    rate_stripes: Vec<std::sync::Mutex<HashMap<IpAddr, RateWindow>>>,
}

const STRIPES: usize = 64;

impl Default for SharedStanding {
    fn default() -> Self {
        Self::new()
    }
}

impl SharedStanding {
    pub fn new() -> Self {
        let stripes = (0..STRIPES)
            .map(|_| std::sync::Mutex::new(HashMap::new()))
            .collect();
        let rate_stripes = (0..STRIPES)
            .map(|_| std::sync::Mutex::new(HashMap::new()))
            .collect();
        SharedStanding {
            stripes,
            rate_stripes,
        }
    }

    fn stripe(&self, ip: IpAddr) -> &std::sync::Mutex<HashMap<IpAddr, u32>> {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        ip.hash(&mut h);
        &self.stripes[(h.finish() as usize) % STRIPES]
    }

    fn rate_stripe(&self, ip: IpAddr) -> &std::sync::Mutex<HashMap<IpAddr, RateWindow>> {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        ip.hash(&mut h);
        &self.rate_stripes[(h.finish() as usize) % STRIPES]
    }

    /// Note a request arrival from `ip` against the rate gate (striped, atomic per
    /// source). Ages the source's window, counts the arrival, and returns `true` iff
    /// it is OVER `limit` (refuse `429`). `limit == 0` disables the gate. Mirrors
    /// [`Standing::rate_note`] exactly, one stripe held for the check-and-count.
    pub fn rate_note(&self, ip: IpAddr, limit: u32, window: Duration, now: Instant) -> bool {
        if limit == 0 {
            return false;
        }
        let mut g = self.rate_stripe(ip).lock().unwrap();
        let w = g.entry(ip).or_insert(RateWindow {
            start: now,
            count: 0,
        });
        if now.duration_since(w.start) >= window {
            w.start = now;
            w.count = 0;
        }
        w.count = w.count.saturating_add(1);
        w.count > limit
    }

    /// Atomically read the source's active count and, iff it is under `cap` (or
    /// `cap == 0` = unlimited), increment and admit. Returns `true` when admitted.
    /// The check-and-increment is a single critical section so concurrent accepts
    /// from one source cannot both slip past the boundary (no TOCTOU over-admit).
    pub fn admit(&self, ip: IpAddr, cap: u32) -> bool {
        let mut g = self.stripe(ip).lock().unwrap();
        let n = g.get(&ip).copied().unwrap_or(0);
        if cap != 0 && n >= cap {
            return false;
        }
        *g.entry(ip).or_insert(0) += 1;
        true
    }

    /// Decrement the source's active count (drops the entry at zero). Called
    /// exactly once per admitted connection when its worker thread returns.
    pub fn on_close(&self, ip: IpAddr) {
        let mut g = self.stripe(ip).lock().unwrap();
        if let Some(n) = g.get_mut(&ip) {
            *n = n.saturating_sub(1);
            if *n == 0 {
                g.remove(&ip);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::Ipv4Addr;

    fn ip(a: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(10, 0, 0, a))
    }

    #[test]
    fn accept_close_is_conserved() {
        let mut s = Standing::new();
        assert_eq!(s.active(ip(1)), 0);
        // Open four from one source; a fifth would see active == 4.
        for _ in 0..4 {
            s.on_accept(ip(1));
        }
        assert_eq!(s.active(ip(1)), 4);
        // A different source is independent (per-source, not global).
        s.on_accept(ip(2));
        assert_eq!(s.active(ip(2)), 1);
        assert_eq!(s.active(ip(1)), 4);
        // Close them all — the counter returns to zero (no leak) and the entry
        // is reclaimed.
        for _ in 0..4 {
            s.on_close(ip(1));
        }
        assert_eq!(s.active(ip(1)), 0);
        assert!(s.active.get(&ip(1)).is_none());
    }

    #[test]
    fn decrement_never_underflows() {
        let mut s = Standing::new();
        // A close with no matching accept is a no-op, never a wrap.
        s.on_close(ip(9));
        assert_eq!(s.active(ip(9)), 0);
    }

    #[test]
    fn open_close_repeatedly_no_residue() {
        let mut s = Standing::new();
        for _ in 0..1000 {
            s.on_accept(ip(7));
            s.on_close(ip(7));
        }
        assert_eq!(s.active(ip(7)), 0);
        assert!(s.active.is_empty());
    }

    #[test]
    fn rate_window_admits_then_429s_then_recovers() {
        let mut s = Standing::new();
        let t0 = Instant::now();
        let win = Duration::from_secs(10);
        let limit = 3u32;
        // The first `limit` arrivals are under the cap (not over).
        assert!(!s.rate_note(ip(1), limit, win, t0)); // count 1
        assert!(!s.rate_note(ip(1), limit, win, t0)); // 2
        assert!(!s.rate_note(ip(1), limit, win, t0)); // 3
        assert_eq!(s.rate_count(ip(1), win, t0), 3);
        // The 4th (and further) arrivals WITHIN the window are over the cap → 429.
        assert!(s.rate_note(ip(1), limit, win, t0)); // 4 > 3
        assert!(s.rate_note(ip(1), limit, win, t0)); // 5 > 3
        // A different source is independent (per-source, not global).
        assert!(!s.rate_note(ip(2), limit, win, t0));
        // After the window fully elapses the window AGES: the source is counted from
        // zero again and is served (recovery — no leak).
        let t1 = t0 + Duration::from_secs(11);
        assert_eq!(s.rate_count(ip(1), win, t1), 0);
        assert!(!s.rate_note(ip(1), limit, win, t1)); // fresh window, count 1
    }

    #[test]
    fn rate_disabled_never_fires() {
        let mut s = Standing::new();
        let t0 = Instant::now();
        // limit 0 = unlimited: never over, and it records no state.
        for _ in 0..1000 {
            assert!(!s.rate_note(ip(3), 0, Duration::from_secs(1), t0));
        }
        assert!(s.rate.is_empty());
    }

    #[test]
    fn rate_prune_reclaims_idle_sources() {
        let mut s = Standing::new();
        let t0 = Instant::now();
        let win = Duration::from_secs(5);
        s.rate_note(ip(4), 10, win, t0);
        s.rate_note(ip(5), 10, win, t0);
        assert_eq!(s.rate.len(), 2);
        // Well past the window: both entries are idle and reclaimed.
        let t1 = t0 + Duration::from_secs(6);
        s.rate_prune(win, t1);
        assert!(s.rate.is_empty());
    }

    #[test]
    fn header_expired_matches_the_proven_rule() {
        let started = Instant::now();
        let timeout = Duration::from_millis(100);
        // In time: not expired.
        assert!(!header_expired(timeout, started, started));
        assert!(!header_expired(
            timeout,
            started,
            started + Duration::from_millis(50)
        ));
        // At/over the deadline: expired.
        assert!(header_expired(timeout, started, started + timeout));
        assert!(header_expired(
            timeout,
            started,
            started + Duration::from_millis(200)
        ));
        // Disabled (zero timeout): never expires.
        assert!(!header_expired(
            Duration::ZERO,
            started,
            started + Duration::from_secs(3600)
        ));
    }
}
