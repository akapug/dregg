//! Per-client **rate limiting** and **escalating lockout** for the auth edge.
//!
//! An agent-facing auth edge with zero per-IP throttling is not production: a
//! flood of `/login` or `/auth` attempts is unbounded work, and an unthrottled
//! break-glass / proof-of-possession endpoint is an online brute-force oracle.
//! This module adds two dependency-free, bounded-memory limiters keyed by a
//! client identity string (the peer IP, or a trusted `X-Forwarded-For`):
//!
//! * [`TokenBucket`] — a classic token bucket (burst capacity + steady refill)
//!   for the general request rate on sensitive endpoints. Fast path: one lock,
//!   O(1). Idle buckets are evicted so memory stays bounded under a spray of
//!   distinct source IPs.
//! * [`Lockout`] — an escalating back-off keyed on *failed* attempts
//!   (a wrong break-glass token, a failed PoP signature). After `threshold`
//!   consecutive failures the client is locked out for a window that doubles with
//!   each further failure, capped at `max`. A success clears it. This turns a
//!   brute-force loop into an exponentially slowing crawl.
//!
//! Time is passed in as `now_ms` (unix milliseconds) so the logic is fully
//! deterministic under test; the server supplies wall-clock ms.

use std::collections::HashMap;
use std::sync::Mutex;

/// A single client's token bucket.
#[derive(Clone, Copy, Debug)]
struct Bucket {
    tokens: f64,
    last_ms: u64,
}

/// A per-client token-bucket rate limiter with bounded memory.
#[derive(Debug)]
pub struct TokenBucket {
    capacity: f64,
    refill_per_ms: f64,
    max_keys: usize,
    inner: Mutex<HashMap<String, Bucket>>,
}

impl TokenBucket {
    /// A limiter allowing bursts of `burst` and a steady `per_min` sustained
    /// rate, tracking at most `max_keys` distinct clients (idle clients are
    /// evicted first). A `per_min` of 0 disables the limiter (always allows).
    pub fn new(burst: u32, per_min: u32, max_keys: usize) -> Self {
        Self {
            capacity: burst.max(1) as f64,
            refill_per_ms: (per_min as f64) / 60_000.0,
            max_keys: max_keys.max(1),
            inner: Mutex::new(HashMap::new()),
        }
    }

    /// Is `key` allowed one unit of work at `now_ms`? Consumes a token on
    /// success. When disabled (`per_min == 0`) always allows.
    pub fn allow(&self, key: &str, now_ms: u64) -> bool {
        if self.refill_per_ms == 0.0 {
            return true;
        }
        let mut map = self.inner.lock().unwrap();
        // Bound memory: if we are about to add a new key and are at capacity,
        // drop clients whose buckets have fully refilled (idle — nothing lost).
        if !map.contains_key(key) && map.len() >= self.max_keys {
            let cap = self.capacity;
            let refill = self.refill_per_ms;
            map.retain(|_, b| {
                let filled =
                    (b.tokens + (now_ms.saturating_sub(b.last_ms) as f64) * refill).min(cap);
                filled < cap - f64::EPSILON
            });
            // Still full of active clients: refuse the new one (fail-closed under
            // a genuine distributed flood rather than growing without bound).
            if map.len() >= self.max_keys {
                return false;
            }
        }
        let b = map.entry(key.to_string()).or_insert(Bucket {
            tokens: self.capacity,
            last_ms: now_ms,
        });
        let elapsed = now_ms.saturating_sub(b.last_ms) as f64;
        b.tokens = (b.tokens + elapsed * self.refill_per_ms).min(self.capacity);
        b.last_ms = now_ms;
        if b.tokens >= 1.0 {
            b.tokens -= 1.0;
            true
        } else {
            false
        }
    }

    #[cfg(test)]
    fn tracked(&self) -> usize {
        self.inner.lock().unwrap().len()
    }
}

/// A failed-attempt record for one client.
#[derive(Clone, Copy, Debug, Default)]
struct Fail {
    count: u32,
    locked_until_ms: u64,
}

/// An escalating lockout keyed on consecutive failed attempts.
#[derive(Debug)]
pub struct Lockout {
    threshold: u32,
    base_ms: u64,
    max_ms: u64,
    max_keys: usize,
    inner: Mutex<HashMap<String, Fail>>,
}

impl Lockout {
    /// Lock a client out after `threshold` consecutive failures; the first
    /// lockout is `base_secs`, doubling with each further failure up to
    /// `max_secs`. A `threshold` of 0 disables lockout.
    pub fn new(threshold: u32, base_secs: u64, max_secs: u64, max_keys: usize) -> Self {
        Self {
            threshold,
            base_ms: base_secs.saturating_mul(1000),
            max_ms: max_secs.saturating_mul(1000),
            max_keys: max_keys.max(1),
            inner: Mutex::new(HashMap::new()),
        }
    }

    /// Is `key` currently allowed (not locked out) at `now_ms`?
    pub fn allowed(&self, key: &str, now_ms: u64) -> bool {
        if self.threshold == 0 {
            return true;
        }
        let map = self.inner.lock().unwrap();
        match map.get(key) {
            Some(f) => now_ms >= f.locked_until_ms,
            None => true,
        }
    }

    /// Record a failed attempt for `key`; may arm or extend a lockout.
    pub fn record_failure(&self, key: &str, now_ms: u64) {
        if self.threshold == 0 {
            return;
        }
        let mut map = self.inner.lock().unwrap();
        // Opportunistic prune of stale, unlocked entries so memory stays bounded.
        if map.len() >= self.max_keys {
            map.retain(|_, f| now_ms < f.locked_until_ms);
        }
        let f = map.entry(key.to_string()).or_default();
        f.count = f.count.saturating_add(1);
        if f.count >= self.threshold {
            let over = f.count - self.threshold; // 0 on the first lockout
            let shift = over.min(20); // avoid overflow; 2^20 * base is already huge
            let window = self.base_ms.saturating_mul(1u64 << shift).min(self.max_ms);
            f.locked_until_ms = now_ms.saturating_add(window);
        }
    }

    /// Clear any failure state for `key` (call on a successful auth).
    pub fn record_success(&self, key: &str) {
        if self.threshold == 0 {
            return;
        }
        self.inner.lock().unwrap().remove(key);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bucket_allows_burst_then_throttles() {
        // burst 3, 60/min → 1 token/sec refill.
        let rl = TokenBucket::new(3, 60, 1024);
        assert!(rl.allow("a", 0));
        assert!(rl.allow("a", 0));
        assert!(rl.allow("a", 0));
        assert!(!rl.allow("a", 0), "4th in the same instant is throttled");
        // One second later, exactly one token has refilled.
        assert!(rl.allow("a", 1000));
        assert!(!rl.allow("a", 1000));
    }

    #[test]
    fn bucket_is_per_key() {
        let rl = TokenBucket::new(1, 60, 1024);
        assert!(rl.allow("a", 0));
        assert!(!rl.allow("a", 0));
        assert!(rl.allow("b", 0), "a different client has its own budget");
    }

    #[test]
    fn bucket_disabled_when_per_min_zero() {
        let rl = TokenBucket::new(1, 0, 1024);
        for _ in 0..1000 {
            assert!(rl.allow("a", 0));
        }
    }

    #[test]
    fn bucket_evicts_idle_keys_under_pressure() {
        let rl = TokenBucket::new(4, 240, 2); // capacity 4, refill 4/sec
        assert!(rl.allow("a", 0));
        assert!(rl.allow("b", 0));
        assert_eq!(rl.tracked(), 2);
        // Much later, a and b have fully refilled (idle). A new client c evicts them.
        assert!(rl.allow("c", 10_000));
        assert!(rl.tracked() <= 2, "idle keys were evicted, memory bounded");
    }

    #[test]
    fn lockout_escalates_and_clears_on_success() {
        // threshold 3, base 2s, max 60s.
        let lo = Lockout::new(3, 2, 60, 1024);
        assert!(lo.allowed("a", 0));
        lo.record_failure("a", 0);
        lo.record_failure("a", 0);
        assert!(lo.allowed("a", 0), "under threshold, still allowed");
        lo.record_failure("a", 0); // 3rd failure → 2s lockout
        assert!(!lo.allowed("a", 0));
        assert!(!lo.allowed("a", 1999));
        assert!(lo.allowed("a", 2000), "lockout window elapsed");
        // 4th failure → doubled to 4s.
        lo.record_failure("a", 2000);
        assert!(!lo.allowed("a", 2000));
        assert!(!lo.allowed("a", 5999));
        assert!(lo.allowed("a", 6000));
        // A success wipes the record.
        lo.record_success("a");
        assert!(lo.allowed("a", 6000));
        lo.record_failure("a", 6000);
        assert!(lo.allowed("a", 6000), "counter reset after success");
    }

    #[test]
    fn lockout_caps_at_max() {
        let lo = Lockout::new(1, 1, 4, 1024);
        for _ in 0..20 {
            lo.record_failure("a", 0);
        }
        // Even after many failures the window is capped at 4s, not astronomical.
        assert!(!lo.allowed("a", 3999));
        assert!(lo.allowed("a", 4000));
    }

    #[test]
    fn lockout_disabled_when_threshold_zero() {
        let lo = Lockout::new(0, 1, 4, 1024);
        for _ in 0..100 {
            lo.record_failure("a", 0);
        }
        assert!(lo.allowed("a", 0));
    }
}
