//! # `beacon` — the drand-beacon → daily-seed wire (the "single most valuable wire").
//!
//! [`daily_seed`](crate::daily_seed) turns a **committed epoch value** into a fresh, fair
//! dungeon seed everyone can re-derive. This module supplies that epoch value from a REAL
//! **threshold public-randomness beacon** (drand / League of Entropy), closing the gap the
//! crate docs name: with a genuine beacon output the daily seed is
//! **unpredictable-until-revealed**, **identical world-wide**, and **verifiable by
//! re-derivation** — the three properties a "today's dungeon everyone plays" needs.
//!
//! ```text
//!   drand round (round, threshold-BLS signature)
//!        │  verify_beacon_round  (BLS pairing e(sig,g2)==e(H(round),pk), output==H(sig))
//!        ▼
//!   beacon output  =  H(signature)   ── the committed epoch value ──▶  daily_seed  ──▶  CommittedSeed
//!        │                                                                                   │
//!        ▼                                                                                   ▼
//!   (unpredictable until the round matures)                                     the day's procgen dungeon
//! ```
//!
//! ## Why the three properties hold
//!
//! - **Unpredictable-until-revealed.** A drand round's output is a *threshold* BLS signature
//!   by the network's distributed key: no coalition below threshold can produce it, so the
//!   day's signature — and therefore the day's seed — does not exist until the round matures.
//!   You cannot grind a favourable dungeon: a forged signature is REFUSED by the pairing check
//!   ([`DailyBeacon::verify`]), and the round is a deterministic function of the day
//!   ([`quicknet_round_for_utc_day`]), so no favourable-round picking either.
//! - **Identical world-wide.** The seed is a pure function of the (public) beacon output, and
//!   the dungeon is a pure function of the seed. Everyone who sees the round derives the same
//!   `CommittedSeed` and re-generates the byte-identical dungeon.
//! - **Verifiable by re-derivation.** Holding only public data — the round, the signature, and
//!   the genesis-pinned drand group key — anyone runs [`DailyBeacon::verify`] then
//!   [`daily_seed`](crate::daily_seed) and re-derives the exact seed, then
//!   [`regenerate`](crate::regenerate) the byte-identical `.dungeon`.
//!
//! ## Honest scope
//!
//! - The **verification** is real drand interop (a BLS pairing check against the pinned
//!   `quicknet` group key; the crate's own tests verify a real published round). The
//!   **producer** half — *fetching* `(round, signature)` from a drand node over HTTP — is a
//!   named client seam, not embedded here (a `DailyBeacon` is built from an already-fetched
//!   round). This keeps the verifier a pure function of public data.
//! - "Unpredictable" is the drand **threshold assumption** (no sub-threshold coalition signs a
//!   future round). This wire *binds* that beacon and makes each day's binding verifiable; it
//!   does not re-prove the threshold assumption.

use dregg_dice::{
    Beacon, BeaconParams, BeaconSchedule, DrandBeacon, VerifyError, verify_beacon_round,
};

use crate::{CommittedSeed, daily_seed};

/// drand `quicknet` genesis unix time (seconds) — the chain's round-1 epoch.
/// Source: `https://api.drand.sh/52db9ba7…c84e971/info` (`genesis_time`).
pub const DRAND_QUICKNET_GENESIS_TIME: u64 = 1_692_803_367;
/// drand `quicknet` round period (seconds). Source: the same `info` endpoint (`period`).
pub const DRAND_QUICKNET_PERIOD_SECS: u64 = 3;

/// The `quicknet` round that has matured at unix time `unix_secs` (the latest round whose
/// signature exists by then). A deterministic function of the clock, so a schedule cannot be
/// nudged to a favourable already-published round.
pub fn quicknet_round_at(unix_secs: u64) -> u64 {
    if unix_secs <= DRAND_QUICKNET_GENESIS_TIME {
        return 1;
    }
    (unix_secs - DRAND_QUICKNET_GENESIS_TIME) / DRAND_QUICKNET_PERIOD_SECS + 1
}

/// The `quicknet` round bound to a UTC **day number** (days since the unix epoch) — the round
/// matured at that day's 00:00:00 UTC. "Today's dungeon" uses today's day number, so the round
/// (and therefore the seed) is a pure, un-grindable function of the date.
///
/// A different day number gives a different round — and once that round is fetched + verified,
/// a different signature, a different output, a different seed, and a different dungeon.
pub fn quicknet_round_for_utc_day(day_number: u64) -> u64 {
    quicknet_round_at(day_number.saturating_mul(86_400))
}

/// A **verifiable daily beacon opening** — one matured public-randomness round bound to a day.
/// Holds exactly the public data a re-deriver needs: the genesis-pinned beacon params (drand
/// group key + scheme, or a hash-chain anchor), the round, its output, and (for a threshold
/// [`dregg_dice::DrandBeacon`]) the round's BLS signature. [`DailyBeacon::verify`] re-checks it
/// with no network; [`DailyBeacon::seed`] turns a verified opening into the day's dungeon seed.
#[derive(Clone, Debug)]
pub struct DailyBeacon {
    /// The genesis-pinned beacon parameters (which network/scheme produced the round).
    pub params: BeaconParams,
    /// The matured round this day draws from.
    pub round: u64,
    /// The beacon output for `round` — the committed epoch value fed to [`daily_seed`].
    /// For drand this is `H(signature)`.
    pub output: [u8; 32],
    /// The round's threshold-BLS signature (drand path), re-checked by the pairing in
    /// [`verify_beacon_round`]. Empty for a hash-chain (single-operator / test) beacon.
    pub signature: Vec<u8>,
}

impl DailyBeacon {
    /// Build a daily beacon from a fetched **drand `quicknet`** round: pins the live network's
    /// group key + scheme and derives the output as drand randomness `H(signature)` (via the
    /// crate's own beacon, so no crypto is duplicated). The signature is NOT trusted here —
    /// [`DailyBeacon::verify`] re-checks it against the pinned key by pairing.
    pub fn quicknet(round: u64, signature: Vec<u8>) -> DailyBeacon {
        // The schedule is irrelevant to a single round's output; pin it to `round`.
        let schedule = BeaconSchedule {
            base_round: round,
            stride: 0,
        };
        let mut beacon = DrandBeacon::quicknet(schedule);
        beacon.insert_round(round, signature.clone());
        let output = beacon.round_output(round);
        DailyBeacon {
            params: beacon.params(),
            round,
            output,
            signature,
        }
    }

    /// Build a daily beacon from explicit parts (a general [`BeaconParams`] — e.g. a
    /// hash-chain test beacon, or a drand round assembled elsewhere). `output` must be the
    /// beacon's output for `round`; `signature` is the round signature (empty for hash-chain).
    pub fn from_parts(
        params: BeaconParams,
        round: u64,
        output: [u8; 32],
        signature: Vec<u8>,
    ) -> DailyBeacon {
        DailyBeacon {
            params,
            round,
            output,
            signature,
        }
    }

    /// **Verify the beacon opening** — the source-free check a re-deriver runs with only public
    /// data. For drand: the BLS pairing `e(sig, g2) == e(H(round), pk)` against the pinned group
    /// key, then `output == H(signature)`. A forged/mutated signature, a wrong round, or a wrong
    /// group key are each rejected — so a favourable-dungeon grind by faking the reveal fails.
    pub fn verify(&self) -> Result<(), VerifyError> {
        verify_beacon_round(&self.params, self.round, &self.output, &self.signature)
    }

    /// The committed epoch value (the verified beacon output) this day's seed derives from.
    pub fn epoch_commitment(&self) -> &[u8; 32] {
        &self.output
    }

    /// **The day's dungeon seed** — verify the opening, then fold the beacon output through
    /// [`daily_seed`]. Everyone who verifies the same round arrives at the identical
    /// [`CommittedSeed`], and thus the byte-identical dungeon. A beacon that does not verify
    /// yields no seed (fail-closed).
    pub fn seed(&self) -> Result<CommittedSeed, VerifyError> {
        self.verify()?;
        Ok(daily_seed(&self.output))
    }
}

/// **Generate today's dungeon from a verified daily beacon** — verify the opening, derive the
/// day's [`CommittedSeed`], and [`generate`](crate::generate) the procgen dungeon. The returned
/// [`GeneratedDungeon`](crate::GeneratedDungeon) re-generates byte-for-byte from the same
/// verified round, and a different day's round gives a different dungeon.
pub fn generate_daily(beacon: &DailyBeacon) -> Result<crate::GeneratedDungeon, VerifyError> {
    let seed = beacon.seed()?;
    Ok(crate::generate(&seed))
}

// ═══════════════════════════════════════════════════════════════════════════════
// The LIVE producer half — fetch today's real `quicknet` round over HTTP, verify it.
//
// The verifier above ([`DailyBeacon::verify`]) was always real drand interop; what was
// the NAMED client seam is closed here: a genuine HTTP GET of today's `quicknet` round
// from a drand node, parsed, built into a [`DailyBeacon`], and BLS-VERIFIED (the same
// pairing check) before it can seed a day. A forged / tampered round fails the pairing
// check and is refused (fail-closed) — it never becomes a dungeon seed. The pinned
// published round ([`pinned_fallback_beacon`]) stays the offline/test fallback: a real
// BLS-verifiable reveal, so an offline day is still beacon-seeded (never a fabricated
// seed), and [`todays_beacon_or_pinned`] serves live-or-pinned transparently.
// ═══════════════════════════════════════════════════════════════════════════════

/// The drand `quicknet` chain hash — the API path segment naming the network whose
/// group key [`dregg_dice`] pins. Source: the drand League-of-Entropy public API.
pub const DRAND_QUICKNET_CHAIN_HASH: &str =
    "52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971";

/// The default drand HTTP API base (the public League-of-Entropy endpoint). A caller may
/// override it (a mirror / a private relay) via the `api_base` argument.
pub const DRAND_API_BASE: &str = "https://api.drand.sh";

/// A pinned, REAL published `quicknet` round — the offline/test fallback for when a live fetch is
/// unavailable (no network, a drand outage). Round 1_000_000 and its threshold-BLS signature; the
/// same vector `dregg-dice`'s interop test pins. Its pairing check holds, so the offline day is a
/// genuine beacon-seeded day (not a fabricated seed).
pub const PINNED_FALLBACK_ROUND: u64 = 1_000_000;
/// The pinned fallback round's threshold-BLS signature (hex) — re-checked by pairing on every use.
pub const PINNED_FALLBACK_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

/// Why a **live** drand fetch could not produce a verified beacon. Every variant is fail-closed:
/// nothing seeds a day unless the fetched round PASSED the pairing check.
#[derive(Debug)]
pub enum FetchError {
    /// The HTTP GET failed (unreachable node, a non-2xx status, a transport error).
    Http(String),
    /// The response body did not parse as a drand round (missing/!numeric `round`, missing/!hex
    /// `signature`), or the returned round did not match the requested one.
    Parse(String),
    /// The round was fetched + parsed but its threshold-BLS signature FAILED the pairing check
    /// against the pinned `quicknet` group key — a forged / tampered / wrong-network round.
    Verify(VerifyError),
}

impl std::fmt::Display for FetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FetchError::Http(m) => write!(f, "drand HTTP fetch failed: {m}"),
            FetchError::Parse(m) => write!(f, "drand round did not parse: {m}"),
            FetchError::Verify(e) => write!(f, "drand round failed BLS verification: {e:?}"),
        }
    }
}

impl std::error::Error for FetchError {}

/// The URL of a specific `quicknet` round on a drand HTTP API base — a pure function (no network),
/// so the request target is testable without a socket.
pub fn quicknet_round_url(api_base: &str, round: u64) -> String {
    format!(
        "{}/{}/public/{}",
        api_base.trim_end_matches('/'),
        DRAND_QUICKNET_CHAIN_HASH,
        round
    )
}

/// Parse a drand `public/{round}` JSON body into `(round, signature_bytes)` — a pure function. The
/// beacon **output** is re-derived from the signature by [`DailyBeacon::quicknet`] (as `H(sig)`),
/// so only the round number and the signature are read; the body's `randomness` is not trusted.
pub fn parse_round_json(body: &str) -> Result<(u64, Vec<u8>), FetchError> {
    let v: serde_json::Value =
        serde_json::from_str(body).map_err(|e| FetchError::Parse(e.to_string()))?;
    let round = v
        .get("round")
        .and_then(|r| r.as_u64())
        .ok_or_else(|| FetchError::Parse("missing or non-numeric `round`".to_string()))?;
    let sig_hex = v
        .get("signature")
        .and_then(|s| s.as_str())
        .ok_or_else(|| FetchError::Parse("missing or non-string `signature`".to_string()))?;
    let sig = hex::decode(sig_hex)
        .map_err(|e| FetchError::Parse(format!("`signature` is not hex: {e}")))?;
    Ok((round, sig))
}

/// Build a **verified** [`DailyBeacon`] from a fetched round body — parse, build, and BLS-verify in
/// one fail-closed step. A body whose signature does not pass the pairing check against the pinned
/// `quicknet` group key is [`FetchError::Verify`]; a `round` other than `expected_round` is
/// [`FetchError::Parse`] (the node returned the wrong round). This is the pure core the live
/// [`fetch_quicknet_round`] wraps, so the verify path is exercised without a network.
pub fn verified_beacon_from_body(
    expected_round: u64,
    body: &str,
) -> Result<DailyBeacon, FetchError> {
    let (round, signature) = parse_round_json(body)?;
    if round != expected_round {
        return Err(FetchError::Parse(format!(
            "requested round {expected_round} but the node returned round {round}"
        )));
    }
    let beacon = DailyBeacon::quicknet(round, signature);
    beacon.verify().map_err(FetchError::Verify)?;
    Ok(beacon)
}

/// One blocking HTTP GET of a URL, returning the response body text. Blocking (not async): the
/// caller drives it from a `spawn_blocking` on their own runtime, keeping this crate free of an
/// ambient tokio dependency at its API.
fn http_get(url: &str) -> Result<String, FetchError> {
    let client = reqwest::blocking::Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .user_agent("dregg-descent-beacon/1.0")
        .build()
        .map_err(|e| FetchError::Http(e.to_string()))?;
    let resp = client
        .get(url)
        .send()
        .map_err(|e| FetchError::Http(e.to_string()))?;
    if !resp.status().is_success() {
        return Err(FetchError::Http(format!(
            "drand node returned HTTP {}",
            resp.status()
        )));
    }
    resp.text().map_err(|e| FetchError::Http(e.to_string()))
}

/// **Fetch + verify a specific `quicknet` round over HTTP.** GET the round from `api_base`, parse
/// the body, build the [`DailyBeacon`], and BLS-verify it against the pinned group key before
/// returning — the returned beacon is ALWAYS verified (a forged / tampered round is refused). This
/// is a blocking call; drive it off a `spawn_blocking` on an async runtime.
pub fn fetch_quicknet_round(api_base: &str, round: u64) -> Result<DailyBeacon, FetchError> {
    let url = quicknet_round_url(api_base, round);
    let body = http_get(&url)?;
    verified_beacon_from_body(round, &body)
}

/// The current UTC **day number** (days since the unix epoch) from the system clock — the day
/// [`quicknet_round_for_utc_day`] binds today's round to.
pub fn current_utc_day() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() / 86_400)
        .unwrap_or(0)
}

/// **Fetch + verify TODAY's `quicknet` round** — the round bound to the current UTC day
/// ([`quicknet_round_for_utc_day`]), fetched live from `api_base` and BLS-verified. This is The
/// Descent's real daily beacon: unpredictable until the round matured, identical world-wide, and
/// verifiable by re-derivation. Blocking; drive it off a `spawn_blocking`.
pub fn fetch_todays_beacon(api_base: &str) -> Result<DailyBeacon, FetchError> {
    let round = quicknet_round_for_utc_day(current_utc_day());
    fetch_quicknet_round(api_base, round)
}

/// The pinned offline-fallback beacon — a real published, BLS-verifiable `quicknet` round. Always
/// verifies (a genuine reveal), so an offline / pre-fetch day is still beacon-seeded.
pub fn pinned_fallback_beacon() -> DailyBeacon {
    DailyBeacon::quicknet(
        PINNED_FALLBACK_ROUND,
        hex::decode(PINNED_FALLBACK_SIG_HEX).expect("the pinned drand signature decodes"),
    )
}

/// **Today's beacon, live-or-pinned.** Try a live drand fetch of today's UTC-day round (BLS-verified);
/// on ANY failure — no network, a drand outage, a wrong/forged round — fall back to the pinned
/// published round. Either way the returned beacon is VERIFIED: a forged live round is refused (the
/// pinned reveal stands in) and the pinned reveal is itself a genuine BLS-verifiable round, so The
/// Descent always opens on a real beacon-seeded day, never a fabricated seed.
pub fn todays_beacon_or_pinned(api_base: &str) -> DailyBeacon {
    match fetch_todays_beacon(api_base) {
        Ok(beacon) => beacon,
        Err(_) => pinned_fallback_beacon(),
    }
}

#[cfg(test)]
mod fetch_tests {
    use super::*;

    /// A drand `public/{round}` JSON body for the pinned published round — the exact shape a
    /// drand node returns (`{round, randomness, signature}`), built from a real verifiable
    /// signature so the verify path is driven WITHOUT a network.
    fn pinned_round_body() -> String {
        // randomness = H(signature); re-derived by the beacon, so any value is fine here — we set
        // the real output so the body is byte-faithful to what a node serves.
        let beacon = pinned_fallback_beacon();
        format!(
            "{{\"round\":{},\"randomness\":\"{}\",\"signature\":\"{}\"}}",
            PINNED_FALLBACK_ROUND,
            hex::encode(beacon.output),
            PINNED_FALLBACK_SIG_HEX,
        )
    }

    /// THE LIVE-FETCH VERIFY PATH, DRIVEN OFFLINE: a real published round body parses, builds, and
    /// BLS-VERIFIES, and derives the day's seed — the exact path `fetch_quicknet_round` runs after
    /// the GET, exercised without a socket.
    #[test]
    fn a_real_fetched_round_body_verifies_and_seeds_the_day() {
        let beacon = verified_beacon_from_body(PINNED_FALLBACK_ROUND, &pinned_round_body())
            .expect("a real published round body verifies");
        // The verified beacon derives a day seed (fail-closed: verify ran inside `seed`).
        let seed = beacon
            .seed()
            .expect("a verified beacon yields the day's seed");
        // Determinism: the same fetched round re-derives the identical seed.
        assert_eq!(
            seed.as_bytes(),
            pinned_fallback_beacon().seed().unwrap().as_bytes(),
            "the fetched round derives the same seed everyone re-derives"
        );
    }

    /// A FORGED / tampered round body is REFUSED by the pairing check (fail-closed) — a favourable
    /// dungeon cannot be grinded by faking the reveal. NON-VACUOUS: the honest body above verifies.
    #[test]
    fn a_forged_fetched_round_body_is_refused() {
        // Flip one nibble of the signature hex — the pairing check must reject it.
        let mut sig = hex::decode(PINNED_FALLBACK_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged_body = format!(
            "{{\"round\":{},\"randomness\":\"00\",\"signature\":\"{}\"}}",
            PINNED_FALLBACK_ROUND,
            hex::encode(&sig),
        );
        let out = verified_beacon_from_body(PINNED_FALLBACK_ROUND, &forged_body);
        assert!(
            matches!(out, Err(FetchError::Verify(_))),
            "a forged round signature fails the BLS pairing check, got {out:?}"
        );
    }

    /// A wrong-round response (the node returned a different round than requested) is refused before
    /// any verify — the schedule cannot be nudged to a favourable already-published round.
    #[test]
    fn a_wrong_round_response_is_refused() {
        let out = verified_beacon_from_body(PINNED_FALLBACK_ROUND + 1, &pinned_round_body());
        assert!(
            matches!(out, Err(FetchError::Parse(_))),
            "a round mismatch is refused, got {out:?}"
        );
    }

    /// A malformed body is a parse error (fail-closed), not a panic.
    #[test]
    fn a_malformed_body_is_a_parse_error() {
        assert!(matches!(
            verified_beacon_from_body(PINNED_FALLBACK_ROUND, "not json"),
            Err(FetchError::Parse(_))
        ));
        assert!(matches!(
            verified_beacon_from_body(PINNED_FALLBACK_ROUND, "{\"round\":1}"),
            Err(FetchError::Parse(_))
        ));
    }

    /// The request URL is the canonical drand `public/{round}` path (pure — no network).
    #[test]
    fn the_round_url_is_the_canonical_drand_path() {
        assert_eq!(
            quicknet_round_url("https://api.drand.sh", 1_000_000),
            format!("https://api.drand.sh/{DRAND_QUICKNET_CHAIN_HASH}/public/1000000")
        );
        // A trailing slash on the base is normalized.
        assert_eq!(
            quicknet_round_url("https://api.drand.sh/", 42),
            format!("https://api.drand.sh/{DRAND_QUICKNET_CHAIN_HASH}/public/42")
        );
    }

    /// THE OFFLINE FALLBACK, DRIVEN: a live fetch against an unreachable base FAILS, and
    /// `todays_beacon_or_pinned` falls back to the pinned round — which itself VERIFIES + seeds a
    /// day. So an offline day is still a genuine beacon-seeded day.
    #[test]
    fn an_unreachable_fetch_falls_back_to_the_verified_pinned_round() {
        // Port 9 (discard) on loopback: the GET fails fast (refused), no external network.
        let unreachable = "http://127.0.0.1:9/drand";
        assert!(
            fetch_todays_beacon(unreachable).is_err(),
            "an unreachable node fails the live fetch"
        );
        let beacon = todays_beacon_or_pinned(unreachable);
        // The fallback beacon is verified and seeds the day.
        assert!(
            beacon.seed().is_ok(),
            "the pinned fallback verifies + seeds a day"
        );
    }

    /// A LIVE network fetch of today's real `quicknet` round — verifies the round exists, the BLS
    /// pairing check holds, and the day seed derives. Network-gated (ignored by default so the
    /// offline suite stays green); run with `--ignored` on a networked host to validate live drand.
    #[test]
    #[ignore = "hits the live drand network; run with --ignored on a networked host"]
    fn live_drand_fetch_of_todays_round_verifies() {
        let beacon =
            fetch_todays_beacon(DRAND_API_BASE).expect("today's live drand round verifies");
        let seed = beacon.seed().expect("the live round derives today's seed");
        assert_ne!(seed.as_bytes(), &[0u8; 32], "a real seed");
    }
}
