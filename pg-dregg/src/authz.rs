//! The authorization CORE — postgres-independent.
//!
//! Everything that decides authorization lives here as plain Rust, so it is
//! provable with `cargo test` (no postgres, no `cargo-pgrx`). The `#[pg_extern]`
//! wrappers in [`crate`] (gated behind the `pgrx` feature) only marshal SQL
//! types into these functions.
//!
//! ## What this module is responsible for (the M1 thesis)
//!
//! 1. **decode + verify** a `dga1_…` credential against the issuer public key
//!    (delegated wholesale to the proven [`dregg_auth::credential`] core);
//! 2. the **verified-credential LRU**, so the per-row cost collapses from an
//!    ed25519 signature-chain verify to a [`Pred`] re-evaluation over the row's
//!    `(action, resource, now)`;
//! 3. the **instant revocation** check (the registry lives at the extension
//!    layer — `dregg-auth` is deliberately revocation-free, see its Cargo.toml);
//! 4. the **attenuation-narrowing** property, observable through this surface.
//!
//! The assurance boundary (docs/PG-DREGG.md §4): the *capability decision* is
//! the verified `dregg-auth` decision; the LRU + revocation set this module adds
//! are conventional code, tested here directly.

use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Mutex;
use std::sync::OnceLock;

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, Refusal};

// ============================================================================
// Issuer key (process-local trust root)
// ============================================================================

/// The issuer public key for this process, parsed once. `None` until set; a
/// missing key makes every decision DENY (fail-closed).
///
/// In the pgrx wrappers this is populated from the `dregg.issuer_pubkey` GUC;
/// in `cargo test` it is set explicitly by the test harness.
static ISSUER_PK: OnceLock<Mutex<Option<PublicKey>>> = OnceLock::new();

fn issuer_slot() -> &'static Mutex<Option<PublicKey>> {
    ISSUER_PK.get_or_init(|| Mutex::new(None))
}

/// Install the issuer public key from its hex form. Returns `false` (and leaves
/// the slot cleared) on a malformed key — fail-closed.
pub fn set_issuer_pubkey_hex(hex: &str) -> bool {
    match PublicKey::from_hex(hex) {
        Ok(pk) => {
            *issuer_slot().lock().unwrap() = Some(pk);
            true
        }
        Err(_) => {
            *issuer_slot().lock().unwrap() = None;
            false
        }
    }
}

/// Install the issuer public key directly (used by the pgrx layer once it has a
/// `PublicKey`, and by tests).
pub fn set_issuer_pubkey(pk: PublicKey) {
    *issuer_slot().lock().unwrap() = Some(pk);
}

/// Clear the issuer key (no key configured ⇒ every decision denies).
pub fn clear_issuer_pubkey() {
    *issuer_slot().lock().unwrap() = None;
}

/// The configured issuer key, or `None` (⇒ deny).
fn issuer_pk() -> Option<PublicKey> {
    *issuer_slot().lock().unwrap()
}

// ============================================================================
// The verified-credential LRU (MANDATORY in M1)
// ============================================================================
//
// The expensive part of a decision is the ed25519 signature-chain verify on
// decode. We cache the decoded+VERIFIED `Credential` keyed by the token STRING,
// so the per-row cost on a scan collapses to:
//
//     (LRU hit) + (revocation check) + (Pred re-eval over THIS row's ctx)
//
// `Credential` is not `Clone`, and re-evaluating caveats needs the live
// `Credential`, so the cache holds the decoded credential behind the LRU lock
// and the caveat re-evaluation runs while the entry is borrowed.
//
// IMPORTANT — what is cached is "this token string decoded and its SIGNATURE
// CHAIN verified against the current issuer key". The cache does NOT memoize the
// admit/deny verdict, because that verdict depends on (action, resource, now)
// and on the revocation set, both of which vary per row / per statement. So a
// cache hit still runs the caveat evaluation and the revocation check every
// time — only the ed25519 work is saved. This is what keeps revocation INSTANT
// even with the cache hot (see `decide`).

const LRU_CAP: usize = 256;

struct Lru {
    /// token-string -> decoded+chain-verified credential.
    map: HashMap<String, Credential>,
    /// recency order; front = least-recently-used.
    order: VecDeque<String>,
}

impl Lru {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            order: VecDeque::new(),
        }
    }

    fn touch(&mut self, key: &str) {
        if let Some(pos) = self.order.iter().position(|k| k == key) {
            self.order.remove(pos);
        }
        self.order.push_back(key.to_string());
    }

    fn insert(&mut self, key: String, cred: Credential) {
        if self.map.len() >= LRU_CAP && !self.map.contains_key(&key) {
            if let Some(evict) = self.order.pop_front() {
                self.map.remove(&evict);
            }
        }
        self.map.insert(key.clone(), cred);
        self.touch(&key);
    }
}

static LRU: OnceLock<Mutex<Lru>> = OnceLock::new();

fn lru() -> &'static Mutex<Lru> {
    LRU.get_or_init(|| Mutex::new(Lru::new()))
}

/// How many entries the LRU currently holds (for tests / introspection).
pub fn lru_len() -> usize {
    lru().lock().unwrap().map.len()
}

/// Clear the LRU (test isolation; also the right thing to call if the issuer key
/// is rotated, since cached credentials were chain-verified under the old key).
pub fn lru_clear() {
    let mut l = lru().lock().unwrap();
    l.map.clear();
    l.order.clear();
}

// ============================================================================
// The instant-revocation registry (extension-layer; dregg-auth has none)
// ============================================================================
//
// `dregg-auth` is revocation-free at the token layer (its Cargo.toml excludes
// `dregg-token`'s `rand-deps` feature where the RevocationRegistry lives). So
// the revocation set lives HERE, keyed on a stable per-credential id.
//
// The id we key on is `dregg_cap_id` = the credential TAIL (a BLAKE3 commitment
// to the entire signed chain, `Credential::tail`, public + offline). It is a
// cryptographic id of EXACTLY this credential: revoking it denies precisely the
// credential presented, on the very next check — instant, not bounded-staleness.
//
// HONEST SCOPE: because the tail commits the whole chain, an *attenuated child*
// has a different tail than its parent, so revoking a parent's id does NOT
// auto-revoke children already minted from it. Revocation here is per-credential
// (revoke the exact token in circulation). A registry keyed on the root nonce
// (which survives attenuation) would need a `nonce()` accessor that
// `dregg-auth` does not currently expose; that is the natural follow-up if
// "revoke a credential and all its descendants" is wanted. For M1 the test
// revokes the exact presented token and the row vanishes on the next statement,
// which is the instant-revocation thesis.
//
// In the pgrx deployment this in-memory set is the backend-local mirror of a
// `dregg.revoked(id text primary key)` table; a production deployment would
// consult that table (or a published Merkle non-membership root) per eval. The
// in-memory set is what the `cargo test` core proves the SEMANTICS of.

static REVOKED: OnceLock<Mutex<std::collections::HashSet<String>>> = OnceLock::new();

fn revoked() -> &'static Mutex<std::collections::HashSet<String>> {
    REVOKED.get_or_init(|| Mutex::new(std::collections::HashSet::new()))
}

/// Mark a credential id (its `dregg_cap_id`, the hex tail) revoked.
pub fn revoke(id: &str) {
    revoked().lock().unwrap().insert(id.to_string());
}

/// Lift a revocation (test/admin).
pub fn unrevoke(id: &str) {
    revoked().lock().unwrap().remove(id);
}

/// Clear all revocations (test isolation).
pub fn revoked_clear() {
    revoked().lock().unwrap().clear();
}

fn is_revoked(id: &str) -> bool {
    revoked().lock().unwrap().contains(id)
}

// ============================================================================
// The credential id (stable per-credential, the revocation key)
// ============================================================================

/// The stable id of the credential a token encodes: the hex of its
/// `Credential::tail` (a BLAKE3 commitment to the whole signed chain). `None`
/// if the token does not decode. This is the value the revocation registry
/// keys on and what `dregg_cap_id` returns at the SQL boundary.
///
/// NOTE: this decodes only (structural validation); it does not prove the
/// issuer signature. The id is a content commitment, used for revocation
/// lookup; the *authorization* decision (`decide`) independently verifies the
/// chain.
pub fn cap_id(token: &str) -> Option<String> {
    let cred = Credential::decode(token).ok()?;
    Some(hex(&cred.tail()))
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ============================================================================
// The core decision
// ============================================================================

/// A structured outcome, so the bool / explain / subject surfaces all share one
/// code path.
pub enum Outcome {
    Allowed,
    Denied(String),
}

impl Outcome {
    pub fn allowed(&self) -> bool {
        matches!(self, Outcome::Allowed)
    }
    pub fn reason(&self) -> String {
        match self {
            Outcome::Allowed => "allowed".to_string(),
            Outcome::Denied(r) => r.clone(),
        }
    }
}

/// The whole M1 decision, fail-closed at every step:
///
/// 1. issuer key configured? (else deny — "no issuer key configured")
/// 2. `now` non-negative? (else deny — a negative clock never wraps into authority)
/// 3. token decodes? (else deny — the wire error)
/// 4. **revocation**: is this credential's id revoked? (if so, deny INSTANTLY —
///    this is checked on EVERY call, including LRU hits, so a revocation lands on
///    the very next row-check)
/// 5. **decode+verify via the LRU**: a cache hit skips the ed25519 chain verify;
///    a miss decodes, verifies the chain against the issuer key, and on success
///    caches it. Then the caveats are (re-)evaluated against THIS row's context.
///
/// The caveat re-evaluation and the revocation check ALWAYS run, even on a hot
/// LRU — only the signature-chain work is cached. That is why the cache is sound
/// despite revocation being able to change within a statement.
pub fn decide(token: &str, action: &str, resource: &str, now: i64) -> Outcome {
    let Some(pk) = issuer_pk() else {
        return Outcome::Denied("no issuer key configured".to_string());
    };
    let Ok(now) = u64::try_from(now) else {
        return Outcome::Denied("clock is negative".to_string());
    };

    // Revocation is consulted BEFORE we trust any cached verification, and on
    // every call — instant revocation, not bounded-staleness.
    if let Some(id) = cap_id(token) {
        if is_revoked(&id) {
            return Outcome::Denied("revoked".to_string());
        }
    }

    let mut ctx = Context::new()
        .at(now)
        .attr("action", action)
        .attr("resource", resource);
    // The `subject` attribute, when the credential carries one, is bound to the
    // credential's OWN declared subject (read off the chain). This makes the
    // subject caveat self-satisfying — it identifies the holder, it does not
    // gate the request — while keeping the subject on the signed chain so
    // `dregg_cap_subject` can recover it and an auditor can trust it. (A token
    // that wanted to gate on a *request-supplied* subject would use a different
    // attribute key; `subject` is reserved for the credential's own identity.)
    if let Some(subj) = subject_of_decoded(token) {
        ctx = ctx.attr("subject", subj);
    }

    let mut l = lru().lock().unwrap();
    if l.map.contains_key(token) {
        l.touch(token);
        let cred = l.map.get(token).expect("just checked");
        // Cache hit: the chain is already verified; re-evaluate caveats only.
        return verdict(reverify_caveats_only(cred, &ctx));
    }

    // Cache miss: decode + full verify (signature chain + caveats) against the
    // issuer key. On a verified chain, cache the credential for future rows.
    let cred = match Credential::decode(token) {
        Ok(c) => c,
        Err(e) => return Outcome::Denied(format!("decode failed: {e}")),
    };
    let result = cred.verify(&pk, &ctx);
    // Cache iff the signature chain itself is sound. A caveat refusal still
    // means the chain verified, so the credential is safe to cache (the next
    // row may satisfy its caveats). A signature/key/proof refusal means a
    // forged or stripped chain — never cache it.
    let chain_sound = match &result {
        Ok(()) => true,
        Err(r) => !is_chain_refusal(r),
    };
    if chain_sound {
        l.insert(token.to_string(), cred);
    }
    verdict(result)
}

/// Map a `verify` result to an [`Outcome`].
fn verdict(result: Result<(), Refusal>) -> Outcome {
    match result {
        Ok(()) => Outcome::Allowed,
        Err(r) => Outcome::Denied(r.to_string()),
    }
}

/// Re-evaluate ONLY the first-party caveats of an already-chain-verified
/// credential against a fresh context — the cheap per-row path. Mirrors the
/// caveat-meet phase of `Credential::verify` (step 3) without the ed25519 chain
/// re-verification (steps 1-2), which the LRU already paid for.
///
/// Third-party caveats are conservatively treated here as "must re-run the full
/// verify": this M1 path only fast-paths first-party credentials. If any
/// third-party caveat is present we signal that by returning a deny that names
/// it; M1 tokens are first-party (resource/action/temporal), so the fast path is
/// exact for the M1 surface. (The `decide` cache-miss path runs the full
/// `verify`, third-party discharge included; only the hot-cache fast path is
/// first-party-only, and it fails CLOSED on a third-party caveat.)
fn reverify_caveats_only(cred: &Credential, ctx: &Context) -> Result<(), Refusal> {
    for (block, caveat) in cred.caveats() {
        match caveat {
            Caveat::FirstParty(p) => match p.eval(ctx) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(Refusal::CaveatRefused {
                        block,
                        requires: p.explain(),
                    });
                }
                Err(unbound) => {
                    return Err(Refusal::ContextIncomplete {
                        block,
                        requires: p.explain(),
                        unbound,
                    });
                }
            },
            Caveat::ThirdParty {
                gateway, caveat_id, ..
            } => {
                // Fail-closed on the fast path: a third-party caveat needs a
                // presented discharge, which the fast path does not carry.
                return Err(Refusal::MissingDischarge {
                    block,
                    caveat_id: hex(caveat_id),
                    gateway: hex(&gateway[..8]),
                });
            }
        }
    }
    Ok(())
}

/// True iff a refusal indicates a FORGED / STRIPPED chain (signature, key, or
/// proof-of-possession), as opposed to an authentic-chain caveat refusal. Used
/// to decide whether a credential is safe to cache.
fn is_chain_refusal(r: &Refusal) -> bool {
    matches!(
        r,
        Refusal::ProofMismatch
            | Refusal::BadSignature { .. }
            | Refusal::MalformedKey { .. }
            | Refusal::MalformedGatewayKey
    )
}

// ============================================================================
// Explain + subject
// ============================================================================

/// The human-readable reason for the decision (the `explain` discipline at the
/// SQL boundary). `"allowed"` on success, otherwise the first violated
/// requirement; the revocation and no-key cases name themselves.
pub fn explain(token: &str, action: &str, resource: &str, now: i64) -> String {
    decide(token, action, resource, now).reason()
}

/// The confined subject the token names, or `None` if the token's chain does not
/// verify under the issuer key. Convention: the subject is a first-party
/// `AttrEq { key: "subject", value: … }` caveat installed in the root block at
/// mint time (the `dregg_mint` convention). We require the CHAIN to verify
/// (forged tokens yield `None`); a missing-clock or unsatisfied caveat does not
/// hide the subject, since the subject is read off the chain, not gated on it.
pub fn subject(token: &str) -> Option<String> {
    let pk = issuer_pk()?;
    let cred = Credential::decode(token).ok()?;
    // Verify the chain. We bind nothing else; the only refusals we treat as
    // "no subject" are the FORGED-chain ones. A caveat refusal (e.g. expired)
    // still means the chain is authentic, so the subject is recoverable.
    let probe = Context::new();
    if let Err(r) = cred.verify(&pk, &probe) {
        if is_chain_refusal(&r) {
            return None;
        }
    }
    subject_in(&cred)
}

/// Read the declared subject off a DECODED credential (no issuer-key check):
/// the value of the first-party `AttrEq { key: "subject", … }` caveat. Used both
/// to bind the self-identifying `subject` attribute in `decide` and (after a
/// chain check) by `subject`.
fn subject_of_decoded(token: &str) -> Option<String> {
    let cred = Credential::decode(token).ok()?;
    subject_in(&cred)
}

fn subject_in(cred: &Credential) -> Option<String> {
    for (_, caveat) in cred.caveats() {
        if let Caveat::FirstParty(Pred::AttrEq { key, value }) = caveat {
            if key == "subject" {
                return Some(value.clone());
            }
        }
    }
    None
}

// ============================================================================
// Tests — the M1 thesis, proven at the Rust level (no postgres needed).
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_auth::credential::{Caveat, Pred, RootKey};

    /// The decision core uses process-global state (issuer key, LRU, revocation
    /// set) — exactly as it will in a postgres backend process. The tests share
    /// that process, so they SERIALIZE on this guard: each test owns the global
    /// state for its body. (A poisoned lock from a prior panic is fine to reuse;
    /// we recover it.)
    static SERIAL: Mutex<()> = Mutex::new(());
    fn lock() -> std::sync::MutexGuard<'static, ()> {
        SERIAL.lock().unwrap_or_else(|p| p.into_inner())
    }

    /// A fixed seed → deterministic root, so the issuer key is stable per test.
    fn root() -> RootKey {
        RootKey::from_seed([7u8; 32])
    }

    /// Install this root's public key as the process issuer key, and reset the
    /// per-process caches so tests do not bleed into each other.
    fn install(root: &RootKey) {
        set_issuer_pubkey(root.public());
        lru_clear();
        revoked_clear();
    }

    /// Mint the M1 token: read under any "org/42/" resource, until clock 2000,
    /// subject "agent-1".
    fn mint_org42(root: &RootKey) -> Credential {
        root.mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "subject".into(),
                value: "agent-1".into(),
            }),
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into(),
            }),
            Caveat::FirstParty(Pred::NotAfter { at: 2000 }),
        ])
    }

    #[test]
    fn attenuation_narrows_through_the_core() {
        let _g = lock();
        let root = root();
        install(&root);

        // Root token: read on any org/42/ resource.
        let root_tok = mint_org42(&root).encode();
        // Attenuated child: confined to org/42/public/ only.
        let narrowed = mint_org42(&root)
            .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/public/".into(),
            })])
            .encode();

        // The ROOT admits both a public and a private resource.
        assert!(decide(&root_tok, "read", "org/42/public/doc1", 1000).allowed());
        assert!(decide(&root_tok, "read", "org/42/private/doc9", 1000).allowed());

        // The NARROWED child admits the public resource...
        assert!(decide(&narrowed, "read", "org/42/public/doc1", 1000).allowed());
        // ...but is STRICTLY narrowed: the private resource the parent admitted
        // is now denied. The no-amplify property, observed through the core.
        assert!(!decide(&narrowed, "read", "org/42/private/doc9", 1000).allowed());

        // Temporal narrowing: past the NotAfter expiry, denied.
        assert!(!decide(&narrowed, "read", "org/42/public/doc1", 3000).allowed());

        // The admitted set of the child is a STRICT SUBSET of the parent's:
        // there exists a request the parent admits and the child denies, and
        // none the child admits that the parent denies.
        let resources = [
            "org/42/public/doc1",
            "org/42/public/doc2",
            "org/42/private/doc9",
            "org/99/public/doc1",
        ];
        let parent_admits: Vec<bool> = resources
            .iter()
            .map(|r| decide(&root_tok, "read", r, 1000).allowed())
            .collect();
        let child_admits: Vec<bool> = resources
            .iter()
            .map(|r| decide(&narrowed, "read", r, 1000).allowed())
            .collect();
        // subset: child ⇒ parent for every request
        for (c, p) in child_admits.iter().zip(parent_admits.iter()) {
            assert!(!c || *p, "child admitted a request the parent denied");
        }
        // strict: at least one request the parent admits and the child denies
        assert!(
            parent_admits
                .iter()
                .zip(child_admits.iter())
                .any(|(p, c)| *p && !*c),
            "narrowing was not strict"
        );
    }

    #[test]
    fn instant_revocation_denies_on_the_next_check() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();

        // Admits before revocation.
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());

        // Revoke this credential's stable id.
        let id = cap_id(&tok).expect("token decodes");
        revoke(&id);

        // The SAME query is now denied — instantly, on the very next check,
        // even though the LRU is hot (the decode+verify was cached above). The
        // revocation check runs before the cache is trusted.
        let out = decide(&tok, "read", "org/42/public/doc1", 1000);
        assert!(!out.allowed());
        assert_eq!(out.reason(), "revoked");

        // Lifting the revocation restores access (the registry is the only
        // thing that changed; the credential never did).
        unrevoke(&id);
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());
    }

    #[test]
    fn forged_token_is_denied_fail_closed() {
        let _g = lock();
        let root = root();
        install(&root);

        // A token from a DIFFERENT issuer must not verify under our key.
        let other = RootKey::from_seed([9u8; 32]);
        let foreign = mint_org42(&other).encode();
        assert!(!decide(&foreign, "read", "org/42/public/doc1", 1000).allowed());

        // Garbage / wrong-prefix tokens are denied, not panicked.
        assert!(!decide("not-a-token", "read", "org/42/public/doc1", 1000).allowed());
        assert!(!decide("dga1_!!!notbase64!!!", "read", "x", 1000).allowed());
        assert!(!decide("", "read", "x", 1000).allowed());
    }

    #[test]
    fn expired_and_wrong_action_are_denied() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();

        // Past NotAfter ⇒ denied.
        assert!(!decide(&tok, "read", "org/42/public/doc1", 9999).allowed());
        // Wrong action (token is confined to action=read) ⇒ denied.
        assert!(!decide(&tok, "write", "org/42/public/doc1", 1000).allowed());
        // Resource outside the prefix ⇒ denied.
        assert!(!decide(&tok, "read", "org/99/public/doc1", 1000).allowed());
    }

    #[test]
    fn no_issuer_key_denies_everything() {
        let _g = lock();
        // Clear the issuer key explicitly (other tests may have set it).
        *issuer_slot().lock().unwrap() = None;
        lru_clear();
        revoked_clear();
        let root = root();
        let tok = mint_org42(&root).encode();
        let out = decide(&tok, "read", "org/42/public/doc1", 1000);
        assert!(!out.allowed());
        assert_eq!(out.reason(), "no issuer key configured");
    }

    #[test]
    fn negative_clock_is_denied_not_wrapped() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();
        let out = decide(&tok, "read", "org/42/public/doc1", -1);
        assert!(!out.allowed());
        assert_eq!(out.reason(), "clock is negative");
    }

    #[test]
    fn lru_caches_then_evicts_but_verdict_is_stable() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();

        assert_eq!(lru_len(), 0);
        // First call: cache miss, full verify, cached.
        assert!(decide(&tok, "read", "org/42/public/doc1", 1000).allowed());
        assert_eq!(lru_len(), 1);
        // Second call on the SAME token: cache hit; verdict unchanged.
        assert!(decide(&tok, "read", "org/42/public/doc2", 1000).allowed());
        assert_eq!(lru_len(), 1);
        // A cache HIT still re-evaluates caveats: a row outside the prefix is
        // denied even though the chain verify was cached.
        assert!(!decide(&tok, "read", "org/99/x", 1000).allowed());

        // A forged token is NOT cached (chain refusal).
        let other = RootKey::from_seed([3u8; 32]);
        let foreign = mint_org42(&other).encode();
        assert!(!decide(&foreign, "read", "org/42/public/doc1", 1000).allowed());
        assert_eq!(lru_len(), 1, "forged token must not be cached");
    }

    #[test]
    fn subject_recovered_only_for_authentic_chain() {
        let _g = lock();
        let root = root();
        install(&root);
        let tok = mint_org42(&root).encode();
        assert_eq!(subject(&tok).as_deref(), Some("agent-1"));

        // Even an EXPIRED-but-authentic token still names its subject (the
        // subject is read off the verified chain, not gated on the caveats).
        // (mint_org42 has NotAfter 2000; subject() binds no clock, so the
        // temporal caveat is ContextIncomplete — a non-chain refusal — and the
        // subject is still recovered.)
        assert_eq!(subject(&tok).as_deref(), Some("agent-1"));

        // A foreign-issuer token yields no subject (chain does not verify).
        let other = RootKey::from_seed([9u8; 32]);
        let foreign = mint_org42(&other).encode();
        assert_eq!(subject(&foreign), None);

        // Garbage yields no subject.
        assert_eq!(subject("nope"), None);
    }
}
