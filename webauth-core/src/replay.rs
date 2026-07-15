//! A bounded, single-use **nonce cache** that upgrades the stateless login
//! challenge from *time-bounded* replay resistance to genuine *single-use*.
//!
//! ## The gap this closes
//!
//! [`crate::challenge`] is a stateless keyed-MAC nonce: it proves *this* service
//! minted the challenge and it has not expired, but on its own it records no
//! consumption — so a captured `{credential, challenge, signature}` POST could be
//! replayed for the whole (~120s) TTL window. That is a real, if small, window.
//!
//! This cache records each challenge nonce the moment it is *successfully*
//! consumed at `POST /login`, so a second POST with the same nonce is rejected as
//! a replay. It is deliberately small and bounded: because every entry carries
//! the challenge's own short expiry, expired entries are pruned on the fly, so
//! the cache never holds more than roughly one TTL window of in-flight logins.
//!
//! ## Honest scope
//!
//! This is per-process state. Across a replica fleet a nonce consumed at replica
//! A is not (yet) known at replica B — so single-use is *per replica* unless a
//! shared store backs it. That is the documented residual: a sticky-session or
//! shared-cache deployment gets true fleet-wide single-use; a round-robin fleet
//! without one still gets per-replica single-use plus the 120s MAC bound. The
//! interface ([`NonceCache::consume`]) is exactly what a shared-store backend
//! would implement, so the upgrade is a drop-in.

use std::collections::HashMap;
use std::sync::Mutex;

/// A bounded set of recently-consumed challenge nonces, keyed by the 16-byte
/// nonce, valued by the challenge's own expiry (unix seconds) for pruning.
#[derive(Debug)]
pub struct NonceCache {
    max: usize,
    enabled: bool,
    inner: Mutex<HashMap<[u8; 16], u64>>,
}

impl NonceCache {
    /// A cache holding at most `max` in-flight nonces. `enabled == false` makes
    /// [`NonceCache::consume`] always accept (single-use disabled — falls back to
    /// the 120s MAC bound).
    pub fn new(enabled: bool, max: usize) -> Self {
        Self {
            max: max.max(1),
            enabled,
            inner: Mutex::new(HashMap::new()),
        }
    }

    /// Attempt to consume `nonce` (whose challenge expires at `exp`, unix
    /// seconds) at wall-clock `now`. Returns `true` if this is the FIRST use
    /// (the login may proceed); `false` if the nonce was already consumed (a
    /// replay) or the cache is saturated with live nonces.
    ///
    /// When disabled, always returns `true`.
    pub fn consume(&self, nonce: [u8; 16], exp: u64, now: u64) -> bool {
        if !self.enabled {
            return true;
        }
        let mut map = self.inner.lock().unwrap();
        // Prune everything already past its challenge expiry — bounds the cache
        // to ~one TTL window regardless of login volume.
        map.retain(|_, &mut e| e > now);
        if map.contains_key(&nonce) {
            return false; // replay
        }
        if map.len() >= self.max {
            // Saturated with still-live nonces: fail closed rather than grow.
            return false;
        }
        map.insert(nonce, exp);
        true
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.inner.lock().unwrap().len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_use_accepts_replay_rejects() {
        let c = NonceCache::new(true, 1024);
        let n = [7u8; 16];
        assert!(c.consume(n, 200, 100), "first use accepted");
        assert!(!c.consume(n, 200, 100), "replay rejected");
        // A different nonce is independent.
        assert!(c.consume([8u8; 16], 200, 100));
    }

    #[test]
    fn expired_entries_are_pruned() {
        let c = NonceCache::new(true, 1024);
        let n = [1u8; 16];
        assert!(c.consume(n, 200, 100));
        assert_eq!(c.len(), 1);
        // After the challenge expiry passes, a later consume prunes it — and the
        // same nonce could only reappear if the MAC still validated (it won't,
        // being expired), so pruning is safe and keeps the cache bounded.
        assert!(c.consume([2u8; 16], 500, 300));
        assert_eq!(c.len(), 1, "the expired entry was pruned");
    }

    #[test]
    fn disabled_always_accepts() {
        let c = NonceCache::new(false, 1024);
        let n = [3u8; 16];
        assert!(c.consume(n, 200, 100));
        assert!(c.consume(n, 200, 100), "disabled cache never blocks");
    }

    #[test]
    fn saturation_fails_closed() {
        let c = NonceCache::new(true, 2);
        assert!(c.consume([1u8; 16], 999, 0));
        assert!(c.consume([2u8; 16], 999, 0));
        assert!(!c.consume([3u8; 16], 999, 0), "saturated cache refuses");
    }
}
