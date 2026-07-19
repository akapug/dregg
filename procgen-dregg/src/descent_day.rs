//! # `descent_day` — THE ONE (day_key, seed) both The Descent's processes resolve.
//!
//! The Descent is played in two processes that must agree on ONE world:
//!
//! - the **Discord bot** opens today's run, plays it, and — on a win — POSTs the run's
//!   reproducible input to the web board;
//! - the **web** (`dreggnet-web`) opens the day, re-executes the submitted moves against its own
//!   identically-seeded world, ranks the run, and mints its shareable run-card.
//!
//! Before this module they resolved their days SEPARATELY (the bot through its live-beacon cache
//! with an offline date-derived fallback; the web from a hardcoded demo epoch), and the bot sent no
//! `day` at all — so the web re-executed the bot's moves in a DIFFERENT world, the re-execution
//! never verified, and the share link was structurally dead. This module is the single seed
//! selection both drive, plus the **day key** that carries WHICH world a run was played in across
//! the process boundary.
//!
//! ## The day key is re-derivable, not a label
//!
//! A [`DescentDay`]'s [`key`](DescentDay::key) names its own provenance, so a receiver can
//! RE-DERIVE the seed from the key alone rather than trusting the sender:
//!
//! ```text
//!   d{utc_day}-off        the OFFLINE date-derived day  — a pure function of the UTC day
//!   d{utc_day}-r{round}   a drand `quicknet` day        — re-derived by FETCHING + BLS-VERIFYING
//!                                                          that round ([`resolve_day_key`])
//! ```
//!
//! Both halves are fail-closed. A malformed key resolves to nothing. A beacon key whose round is
//! not the one the schedule binds to its day ([`crate::beacon::quicknet_round_for_utc_day`]) is
//! REFUSED before any network touch, and a round outside a narrow day window is refused too — so a
//! public submit endpoint that resolves a caller-supplied key cannot be steered into fetching
//! arbitrary rounds, and cannot be handed a favourable already-published round. A fetched round
//! that fails the BLS pairing check yields no day.
//!
//! ## Honest scope
//!
//! The OFFLINE day is a real daily rotation, NOT a fresh beacon reveal: its epoch is a
//! domain-separated hash of the UTC day number over the pinned published round. It is the
//! agreed-upon world when no live reveal has reached a host — which is exactly the case the two
//! processes previously disagreed about. `DaySource` carries the distinction so no surface can
//! render the offline day as if it were today's live drand reveal.

use crate::beacon::{
    DailyBeacon, FetchError, PINNED_FALLBACK_SIG_HEX, RoundFetch, current_utc_day,
    quicknet_round_for_utc_day, verified_beacon_from_body,
};
use crate::{CommittedSeed, daily_seed};

/// Domain tag for the OFFLINE, date-derived epoch — distinct from every live beacon path, so a
/// date-seeded day can never alias a beacon-seeded one.
pub const DOMAIN_OFFLINE_DATE_SEED: &[u8] = b"dregg-descent-offline-date-seed-v1";

/// How many UTC days either side of "today" a caller-supplied day key may name. A submitted run
/// is for today (a clock skew / a run that straddles midnight is the ±1); anything further is
/// refused, so a public endpoint resolving a key can never be walked across the round space.
pub const DAY_KEY_WINDOW: u64 = 1;

/// **Where a day's world came from** — carried on every [`DescentDay`] so a surface labels the day
/// it serves rather than guessing, and so a receiver knows how to RE-DERIVE the seed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DaySource {
    /// A BLS-verified drand `quicknet` round — a genuine fresh reveal.
    Beacon {
        /// The round the day's epoch is `H(signature)` of.
        round: u64,
    },
    /// The OFFLINE, date-derived day: it rotates each UTC day and everyone derives the identical
    /// world, but it is NOT a fresh beacon-verified reveal.
    OfflineDate,
}

impl DaySource {
    /// Whether this day is a genuine fresh beacon reveal (`false` = the offline date-derived day).
    pub fn is_live_beacon(&self) -> bool {
        matches!(self, DaySource::Beacon { .. })
    }
}

/// **One resolved descent day** — the UTC day, its provenance, the committed epoch value, the
/// derived [`CommittedSeed`] every world/board/run is drawn from, and the cross-process
/// [`key`](DescentDay::key).
#[derive(Clone, Debug)]
pub struct DescentDay {
    /// Days since the unix epoch — the calendar day this world belongs to.
    pub utc_day: u64,
    /// Live drand round, or the offline date-derived day.
    pub source: DaySource,
    /// The committed epoch value folded through [`daily_seed`] (a verified beacon output, or the
    /// date-derived epoch). This is what a browser hands `DescentWorld::new`.
    pub epoch: [u8; 32],
    /// The day's committed seed — the world, the board universe, and every run share it.
    pub seed: CommittedSeed,
    /// The re-derivable cross-process day key (see the module docs).
    pub key: String,
}

impl DescentDay {
    /// The committed epoch value as lowercase hex — what the in-browser `DescentWorld::new(epoch)`
    /// opens the identical world from.
    pub fn epoch_hex(&self) -> String {
        hex::encode(self.epoch)
    }

    /// A short hex provenance tag of the day's seed (first 4 bytes) — the same tag the surfaces
    /// print beside a board, and the tail of the day's `dregg://descent/b3_…` content address.
    pub fn seed_tag(&self) -> String {
        hex::encode(&self.seed.as_bytes()[..4])
    }

    /// The canonical `dregg://descent/b3_<seed-tag>` address for this day — a well-formed descent
    /// content address whose tail changes with the day, so a client that keys a world by its addr
    /// gets a fresh one each day.
    pub fn descent_uri(&self) -> String {
        format!("dregg://descent/b3_{}", self.seed_tag())
    }
}

/// The OFFLINE date-derived **epoch** for a UTC day: a domain-separated hash of the day number over
/// the pinned published round's signature. Pure — every process derives the identical value with no
/// network, which is what makes it the agreed-upon world when no live reveal has landed.
pub fn offline_date_epoch(utc_day: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(DOMAIN_OFFLINE_DATE_SEED);
    h.update(&hex::decode(PINNED_FALLBACK_SIG_HEX).expect("the pinned drand signature decodes"));
    h.update(&utc_day.to_le_bytes());
    *h.finalize().as_bytes()
}

/// The OFFLINE date-derived **seed** for a UTC day — [`offline_date_epoch`] through
/// [`daily_seed`].
pub fn offline_date_seed(utc_day: u64) -> CommittedSeed {
    daily_seed(&offline_date_epoch(utc_day))
}

/// The cross-process day key for a `(utc_day, source)` pair (see the module docs).
pub fn day_key(utc_day: u64, source: DaySource) -> String {
    match source {
        DaySource::Beacon { round } => format!("d{utc_day}-r{round}"),
        DaySource::OfflineDate => format!("d{utc_day}-off"),
    }
}

/// Parse a day key back to `(utc_day, source)`. `None` on ANY malformed key — the shape is exact,
/// so an arbitrary caller string never becomes a day.
pub fn parse_day_key(key: &str) -> Option<(u64, DaySource)> {
    let rest = key.strip_prefix('d')?;
    let (day_s, tail) = rest.split_once('-')?;
    let utc_day: u64 = day_s.parse().ok()?;
    let source = if tail == "off" {
        DaySource::OfflineDate
    } else {
        let round: u64 = tail.strip_prefix('r')?.parse().ok()?;
        DaySource::Beacon { round }
    };
    Some((utc_day, source))
}

/// The OFFLINE date-derived day for a UTC day number — fully resolved, no network.
pub fn offline_day(utc_day: u64) -> DescentDay {
    let epoch = offline_date_epoch(utc_day);
    DescentDay {
        utc_day,
        source: DaySource::OfflineDate,
        epoch,
        seed: daily_seed(&epoch),
        key: day_key(utc_day, DaySource::OfflineDate),
    }
}

/// **Today's** offline date-derived day (the system clock's UTC day). This is the day BOTH
/// processes serve when no live drand reveal has reached them — so they agree by construction.
pub fn todays_offline_day() -> DescentDay {
    offline_day(current_utc_day())
}

/// Build the day a **verified** drand beacon opens for `utc_day`. Fail-closed: the beacon's own
/// [`DailyBeacon::seed`] runs the BLS pairing check first, so a forged reveal yields no day.
pub fn beacon_day(
    utc_day: u64,
    beacon: &DailyBeacon,
) -> Result<DescentDay, dregg_dice::VerifyError> {
    let seed = beacon.seed()?;
    Ok(DescentDay {
        utc_day,
        source: DaySource::Beacon {
            round: beacon.round,
        },
        epoch: *beacon.epoch_commitment(),
        seed,
        key: day_key(
            utc_day,
            DaySource::Beacon {
                round: beacon.round,
            },
        ),
    })
}

/// Why a caller-supplied day key could not be resolved to a world. Every variant is fail-closed —
/// no day is opened unless the key re-derived to a seed the receiver computed ITSELF.
#[derive(Debug)]
pub enum DayKeyError {
    /// The key is not a `d{utc_day}-off` / `d{utc_day}-r{round}` key.
    Malformed,
    /// The key names a UTC day further than [`DAY_KEY_WINDOW`] from the receiver's today. Refused
    /// BEFORE any network touch.
    OutOfWindow {
        /// The day the key named.
        named: u64,
        /// The receiver's current UTC day.
        today: u64,
    },
    /// The key names a round that is not the one the drand schedule binds to its day — a
    /// favourable-round pick. Refused BEFORE any network touch.
    RoundNotScheduled {
        /// The round the key named.
        named: u64,
        /// The round [`quicknet_round_for_utc_day`] binds to that day.
        scheduled: u64,
    },
    /// The round could not be fetched, did not parse, or FAILED the BLS pairing check.
    Fetch(FetchError),
}

impl std::fmt::Display for DayKeyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DayKeyError::Malformed => write!(f, "not a descent day key"),
            DayKeyError::OutOfWindow { named, today } => write!(
                f,
                "day key names UTC day {named}, outside ±{DAY_KEY_WINDOW} of today ({today})"
            ),
            DayKeyError::RoundNotScheduled { named, scheduled } => write!(
                f,
                "day key names drand round {named}, but that day's scheduled round is {scheduled}"
            ),
            DayKeyError::Fetch(e) => write!(f, "the day's drand round did not resolve: {e}"),
        }
    }
}

impl std::error::Error for DayKeyError {}

/// **Re-derive the world a day key names** — the receiver's half of the cross-process wire. The
/// key is never trusted: an offline key is re-derived PURELY, and a beacon key is re-derived by
/// FETCHING that round and running the BLS pairing check ([`verified_beacon_from_body`]), after
/// two pure refusals (the day window and the schedule-bound round) that keep a caller-supplied key
/// from steering the fetch.
///
/// Blocking on the beacon path (the transport is [`RoundFetch`]); drive it off a `spawn_blocking`.
pub fn resolve_day_key<F: RoundFetch + ?Sized>(
    fetcher: &F,
    api_base: &str,
    key: &str,
    today: u64,
) -> Result<DescentDay, DayKeyError> {
    let (utc_day, source) = parse_day_key(key).ok_or(DayKeyError::Malformed)?;
    if utc_day.abs_diff(today) > DAY_KEY_WINDOW {
        return Err(DayKeyError::OutOfWindow {
            named: utc_day,
            today,
        });
    }
    match source {
        DaySource::OfflineDate => Ok(offline_day(utc_day)),
        DaySource::Beacon { round } => {
            let scheduled = quicknet_round_for_utc_day(utc_day);
            if round != scheduled {
                return Err(DayKeyError::RoundNotScheduled {
                    named: round,
                    scheduled,
                });
            }
            let body = fetcher
                .fetch_round(api_base, round)
                .map_err(DayKeyError::Fetch)?;
            let beacon = verified_beacon_from_body(round, &body).map_err(DayKeyError::Fetch)?;
            // `beacon_day` re-runs the pairing check inside `seed()`; a verified beacon cannot fail
            // here, and a forged one never reached this line.
            beacon_day(utc_day, &beacon).map_err(|e| DayKeyError::Fetch(FetchError::Verify(e)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::beacon::{PINNED_FALLBACK_ROUND, pinned_fallback_beacon};

    /// THE POINT: two processes that each resolve "today" offline land on the IDENTICAL key AND the
    /// identical seed — so a run played in one re-executes in the other.
    #[test]
    fn two_processes_resolving_today_offline_agree_on_the_key_and_the_seed() {
        let a = todays_offline_day();
        let b = offline_day(current_utc_day());
        assert_eq!(a.key, b.key);
        assert_eq!(a.seed.as_bytes(), b.seed.as_bytes());
        // NON-VACUOUS: a different day is a different world.
        let tomorrow = offline_day(a.utc_day + 1);
        assert_ne!(a.key, tomorrow.key);
        assert_ne!(a.seed.as_bytes(), tomorrow.seed.as_bytes());
    }

    /// A key round-trips, and the RECEIVER re-derives the sender's seed from the key ALONE — the
    /// property the share link depends on.
    #[test]
    fn an_offline_key_re_derives_the_senders_seed() {
        let sent = todays_offline_day();
        let (utc_day, source) = parse_day_key(&sent.key).expect("the key parses");
        assert_eq!(utc_day, sent.utc_day);
        assert_eq!(source, DaySource::OfflineDate);
        let received = resolve_day_key(&NoFetch, "unused://", &sent.key, sent.utc_day)
            .expect("an offline key needs no network");
        assert_eq!(received.seed.as_bytes(), sent.seed.as_bytes());
        assert_eq!(received.epoch, sent.epoch);
    }

    /// The epoch a browser opens the day from derives the SAME seed the server drew the board from
    /// (the `/descent/play` ↔ board weld).
    #[test]
    fn the_published_epoch_derives_the_days_seed() {
        let day = todays_offline_day();
        assert_eq!(daily_seed(&day.epoch).as_bytes(), day.seed.as_bytes());
        assert_eq!(day.epoch_hex().len(), 64);
        assert!(day.descent_uri().starts_with("dregg://descent/b3_"));
    }

    /// A transport that MUST NOT be reached — proves the pure refusals fire before any network.
    struct NoFetch;
    impl RoundFetch for NoFetch {
        fn fetch_round(&self, _api_base: &str, _round: u64) -> Result<String, FetchError> {
            panic!("the fetch transport must not be reached on a refused / offline key")
        }
    }

    /// A malformed key, an out-of-window day, and an off-schedule round are ALL refused WITHOUT
    /// touching the transport — a public endpoint resolving a caller-supplied key cannot be steered.
    #[test]
    fn a_hostile_day_key_is_refused_before_any_fetch() {
        let today = current_utc_day();
        for bad in ["", "today", "d-off", "dxx-off", "d100", "d100-q7", "d100-r"] {
            assert!(
                matches!(
                    resolve_day_key(&NoFetch, "unused://", bad, today),
                    Err(DayKeyError::Malformed)
                ),
                "{bad} must be malformed"
            );
        }
        // A far-away day (the round-space walk) — refused on the window, no fetch.
        let far = day_key(today + 900, DaySource::Beacon { round: 12 });
        assert!(matches!(
            resolve_day_key(&NoFetch, "unused://", &far, today),
            Err(DayKeyError::OutOfWindow { .. })
        ));
        // Today's day but a hand-picked favourable round — refused on the schedule, no fetch.
        let picked = day_key(
            today,
            DaySource::Beacon {
                round: PINNED_FALLBACK_ROUND,
            },
        );
        assert!(
            matches!(
                resolve_day_key(&NoFetch, "unused://", &picked, today),
                Err(DayKeyError::RoundNotScheduled { .. })
            ),
            "a round the schedule does not bind to that day is refused"
        );
    }

    /// The BEACON half of the wire, driven WITHOUT a network.
    ///
    /// Two legs, both non-vacuous:
    /// * [`beacon_day`] over the REAL published round vector yields the day whose seed is that
    ///   beacon's own — the success path a live day takes.
    /// * [`resolve_day_key`] on a correctly-SCHEDULED round gets past both pure guards and reaches
    ///   the transport, and what decides the outcome there is the BLS pairing check: a body carrying
    ///   a signature that is not that round's is refused as a VERIFY failure, not a schedule one. So
    ///   the fetch-and-verify wiring is real, and a forged reveal opens no day.
    ///
    /// (The two legs are separate because the pinned interop vector is round 1_000_000, which the
    /// UTC-day schedule never binds to a day exactly — rounds advance 28_800 per day — so no single
    /// key can be both schedule-valid and signed by the one signature we hold offline.)
    #[test]
    fn the_beacon_half_verifies_the_round_it_opens_a_day_from() {
        let beacon = pinned_fallback_beacon();
        let utc_day = current_utc_day();

        // Leg 1 — a VERIFIED beacon becomes a day whose seed is that beacon's.
        let day = beacon_day(utc_day, &beacon).expect("a real published round opens a day");
        assert!(day.source.is_live_beacon());
        assert_eq!(day.seed.as_bytes(), beacon.seed().unwrap().as_bytes());
        assert_eq!(
            day.key,
            day_key(
                utc_day,
                DaySource::Beacon {
                    round: PINNED_FALLBACK_ROUND
                }
            )
        );
        // A forged beacon opens NO day (fail-closed) — the leg that makes leg 1 non-vacuous.
        let mut sig = hex::decode(PINNED_FALLBACK_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged = DailyBeacon::quicknet(PINNED_FALLBACK_ROUND, sig);
        assert!(
            beacon_day(utc_day, &forged).is_err(),
            "a forged reveal opens no day"
        );

        // Leg 2 — a SCHEDULE-VALID key reaches the transport, and the pairing check is what decides.
        struct Mock {
            body: String,
            hit: std::cell::Cell<bool>,
        }
        impl RoundFetch for Mock {
            fn fetch_round(&self, _b: &str, _r: u64) -> Result<String, FetchError> {
                self.hit.set(true);
                Ok(self.body.clone())
            }
        }
        let scheduled = quicknet_round_for_utc_day(utc_day);
        let key = day_key(utc_day, DaySource::Beacon { round: scheduled });
        let mock = Mock {
            // A well-formed body for the RIGHT round, carrying a signature that is not its own.
            body: format!(
                "{{\"round\":{scheduled},\"randomness\":\"00\",\"signature\":\"{PINNED_FALLBACK_SIG_HEX}\"}}"
            ),
            hit: std::cell::Cell::new(false),
        };
        let out = resolve_day_key(&mock, "mock://", &key, utc_day);
        assert!(
            mock.hit.get(),
            "a schedule-valid key DOES reach the transport"
        );
        assert!(
            matches!(out, Err(DayKeyError::Fetch(FetchError::Verify(_)))),
            "the BLS pairing check is what decides a fetched round, got {out:?}"
        );
    }
}
