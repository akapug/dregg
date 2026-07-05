//! The web-surface capability vocabulary on top of the [`crate::cred`] core.
//!
//! A DreggNet web surface (ops, grafana, the gateway admin) requires one named
//! **capability** string — `ops-admin`, `grafana-view`, `gateway-admin`. A
//! credential grants a set of caps via a single first-party caveat:
//!
//! ```text
//! AnyOf([ AttrEq{cap, "ops-admin"}, AttrEq{cap, "grafana-view"} ])
//! ```
//!
//! The forward-auth service verifies the presented credential against a context
//! binding `cap = <the surface's required capability>` and `clock = now`. The
//! `AnyOf` admits iff the requested cap is one the credential was granted. To
//! confine to a sub-agent, [`attenuate_caps`] appends a *narrower* `AnyOf` — the
//! caveat meet then rejects any cap outside the narrowed set, so a `grafana-view`
//! credential can never reach `ops-admin` (the no-amplify property, proven in
//! `cred::tests::attenuation_only_narrows`).

use crate::account_id::{self, ACCT_CAVEAT_KEY};
use crate::cred::{Caveat, Context, Credential, Pred, RootKey};

/// The request attribute key a capability is matched on.
pub const CAP_KEY: &str = "cap";

/// Build the single caveat that grants exactly `caps`.
fn cap_caveat(caps: &[String]) -> Caveat {
    Caveat::FirstParty(Pred::AnyOf(
        caps.iter()
            .map(|c| Pred::AttrEq {
                key: CAP_KEY.to_string(),
                value: c.clone(),
            })
            .collect(),
    ))
}

/// Mint a credential granting `caps`, optionally expiring at `until` (a unix
/// second / clock reading; `None` = no expiry).
pub fn mint_caps(
    root: &RootKey,
    caps: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let mut caveats = vec![cap_caveat(&caps)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    root.mint(caveats)
}

/// Narrow an existing credential to a subset of caps (and/or a tighter expiry).
/// Appends a confining `AnyOf` caveat — can only ever *remove* reach.
pub fn attenuate_caps(
    cred: Credential,
    caps: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let mut caveats = vec![cap_caveat(&caps)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    cred.attenuate(caveats)
}

/// Build the verification context for a request to `required_cap` at clock `now`.
pub fn cap_context(required_cap: &str, now: u64) -> Context {
    Context::new().at(now).attr(CAP_KEY, required_cap)
}

/// Mint a **re-anchored session credential** (Tier 1): a short-lived auth token
/// for the account whose stable, key-derived id is `account_id_hex`
/// ([`account_id::account_id_hex`] of the account's inception key), granting
/// `caps`, expiring `ttl_secs` after `issued_at`.
///
/// The credential carries:
///  * an `acct = <account-id-hex>` first-party caveat — so [`crate::subject_of`]
///    returns the SAME `dregg:<account-id>` subject across every re-issue (a key
///    rotation, a guardian recovery, a fresh login). The account — and every
///    resource `org`/`dregg-secrets`/`console`/`guard`/`billing` scopes to it —
///    survives, because the subject is the account's identity, not this token's
///    tail;
///  * the cap grant;
///  * a `NotAfter` expiry — the Tier-0 default that bounds a leaked token's life.
///
/// The token is minted under `root` (the control-plane issuer's authoritative
/// key for the account); the offline forward-auth verifier stays a pure session
/// checker. Rotation/recovery/revocation of the account happen on the substrate
/// identity cell whose id IS `account_id_hex` — the depend-on-substrate weld.
pub fn mint_session(
    root: &RootKey,
    account_id_hex: &str,
    caps: impl IntoIterator<Item = impl Into<String>>,
    issued_at: u64,
    ttl_secs: u64,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let caveats = vec![
        Caveat::FirstParty(Pred::AttrEq {
            key: ACCT_CAVEAT_KEY.to_string(),
            value: account_id_hex.to_string(),
        }),
        cap_caveat(&caps),
        Caveat::FirstParty(Pred::NotAfter {
            at: issued_at.saturating_add(ttl_secs),
        }),
    ];
    root.mint(caveats)
}

/// Re-anchor an existing session for the same account under a fresh issue: drop
/// the old expiry, mint a new token carrying the SAME `acct` claim and a fresh
/// TTL. Convenience over [`mint_session`] when the inception pubkey is in hand.
pub fn mint_session_for(
    root: &RootKey,
    inception_pubkey: &[u8; 32],
    caps: impl IntoIterator<Item = impl Into<String>>,
    issued_at: u64,
    ttl_secs: u64,
) -> Credential {
    mint_session(
        root,
        &account_id::account_id_hex(inception_pubkey),
        caps,
        issued_at,
        ttl_secs,
    )
}
