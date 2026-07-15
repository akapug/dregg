//! `credext` — the forward-auth reads and proof-of-possession verbs over the
//! real `dga1_` [`Credential`], ported from the prior operated layer.
//!
//! Everything here is derived from `dregg_agent::cred`'s public surface
//! (`verify`, the canonical wire form) — no parallel implementation of the
//! chain or its digests. The native credential already carries `tail_hex` and
//! `first_attr` as inherent methods; this module adds the four the web edge
//! still needs:
//!
//! - [`CredentialExt::is_expired`] — the 401-vs-403 expiry probe;
//! - [`CredentialExt::verify_chain`] — chain-only genuineness (the login gate);
//! - [`CredentialExt::proof_public`] / [`CredentialExt::sign_challenge`] — the
//!   bearer-tail-key proof-of-possession pair, with [`verify_pop`] the server
//!   side.
//!
//! The named parent-crate ask stands: `dregg_agent::cred` exposing
//! `proof_public()` / `sign_challenge()` / a public caveat iterator would let
//! the wire round-trip below be deleted.

use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::Deserialize;

use dregg_agent::cred::{
    CREDENTIAL_PREFIX, Caveat, Context, Credential, KeyError, Pred, PublicKey, Refusal,
};

/// Why the local read of the credential's canonical wire form failed. The only
/// way this arises in practice is a `dregg_agent` wire-schema bump (a v2 layout)
/// that this crate's `BearerWire` mirror no longer parses — in which case the
/// edge must return a clean `500`, NEVER panic and kill the worker thread. The
/// clean fix (the parent crate exposing `proof_public()` / a caveat iterator) is
/// named in the module docs; until then this typed error is the graceful guard.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum WireReadError {
    #[error("credential wire form did not carry the expected `dga1_` prefix")]
    BadPrefix,
    #[error("credential wire body was not valid base64url")]
    BadBase64,
    #[error(
        "credential wire body did not match the known v1 postcard schema \
         (a dregg-agent schema bump? the edge fails closed rather than panicking)"
    )]
    BadSchema,
}

/// The temporal validity of a credential relative to a clock reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Validity {
    /// Every temporal caveat is satisfied at `now`.
    Valid,
    /// A `NotBefore` / `Within.not_before` gate has not yet opened (vesting).
    NotYetValid,
    /// A `NotAfter` / `Within.not_after` gate has passed (expired).
    Expired,
}

/// The forward-auth reads and PoP verbs over the real [`Credential`].
pub trait CredentialExt {
    /// Is this credential expired at wall-clock `now`? True iff any
    /// first-party `NotAfter { at }` (or a `Within` upper bound) it carries is
    /// already past. Used at the auth edge to distinguish an EXPIRED-but-genuine
    /// session (→ 401, re-login) from a genuine session that merely lacks the
    /// surface's cap (→ 403).
    ///
    /// Fail-closed: if the credential's wire form cannot be read (a schema bump),
    /// this returns `true` (treat as expired → denied) rather than panicking. Use
    /// [`CredentialExt::validity`] when the caller wants to distinguish that case
    /// (and surface a `500`) from a genuinely-expired token.
    fn is_expired(&self, now: u64) -> bool;

    /// The full temporal [`Validity`] of the credential at `now` — honoring
    /// `NotBefore` and `Within.not_before` (not-yet-valid) as well as the
    /// `NotAfter` upper bound. Returns [`WireReadError`] if the wire form cannot
    /// be read, so the login/whoami gate can answer `500` instead of a misleading
    /// `401`. The `/auth` core path additionally binds the clock in its context
    /// meet, so a not-yet-valid token is refused there regardless.
    fn validity(&self, now: u64) -> Result<Validity, WireReadError>;

    /// Verify ONLY the ed25519 signature chain + the proof-of-possession, with
    /// NO caveat evaluation — establishes "this is a genuine, untampered
    /// credential issued by `root`, and the presenter holds its bearer tail
    /// key" independent of any per-surface context.
    ///
    /// The **login gate** rides this: at login the target surface (and thus
    /// its required capability) is not yet known, so login proves genuine
    /// issuance + possession here, and the per-surface caveat meet is then
    /// enforced on every auth check by [`Credential::verify`].
    fn verify_chain(&self, root: &PublicKey) -> Result<(), Refusal>;

    /// The public half of the credential's **bearer tail key** — the key a
    /// [`Credential::attenuate`] would sign the next block under, and the key
    /// a holder proves possession of by signing a login challenge
    /// ([`CredentialExt::sign_challenge`] / [`verify_pop`]).
    ///
    /// Fail-closed: on an unreadable wire form this returns the all-zero key,
    /// which is not the holder's key, so [`verify_pop`] against it can only fail.
    /// Prefer [`CredentialExt::try_proof_public`] to surface the error as a `500`.
    fn proof_public(&self) -> [u8; 32];

    /// [`CredentialExt::proof_public`], surfacing a wire-read failure instead of
    /// masking it as an all-zero key. The login PoP path uses this to return a
    /// clean `500` on a schema bump rather than a confusing PoP failure.
    fn try_proof_public(&self) -> Result<[u8; 32], WireReadError>;

    /// Sign an opaque login challenge with the bearer tail key — the client
    /// side of the proof-of-possession handshake. The verifier checks it with
    /// [`verify_pop`] against [`CredentialExt::proof_public`].
    fn sign_challenge(&self, msg: &[u8]) -> [u8; 64];
}

impl CredentialExt for Credential {
    fn is_expired(&self, now: u64) -> bool {
        // Fail-closed: an unreadable wire form is treated as expired (denied),
        // never a panic. `validity` distinguishes the schema-error case.
        !matches!(
            self.validity(now),
            Ok(Validity::Valid) | Ok(Validity::NotYetValid)
        )
    }

    fn validity(&self, now: u64) -> Result<Validity, WireReadError> {
        // Scan every temporal caveat across all blocks. Expiry dominates a
        // not-yet-valid verdict (an expired-and-not-yet-valid window is expired),
        // matching the fail-closed reading the `/auth` context meet gives.
        let mut not_yet = false;
        for caveat in wire_caveats(self)? {
            if let Caveat::FirstParty(p) = caveat {
                match p {
                    Pred::NotAfter { at } if now > at => return Ok(Validity::Expired),
                    Pred::NotBefore { at } if now < at => not_yet = true,
                    Pred::Within {
                        not_before,
                        not_after,
                    } => {
                        if now > not_after {
                            return Ok(Validity::Expired);
                        }
                        if now < not_before {
                            not_yet = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(if not_yet {
            Validity::NotYetValid
        } else {
            Validity::Valid
        })
    }

    fn verify_chain(&self, root: &PublicKey) -> Result<(), Refusal> {
        // `Credential::verify` checks proof-of-possession and the ed25519
        // block chain strictly BEFORE any caveat evaluation, so probing with
        // an empty context isolates the chain verdict exactly: a chain-class
        // refusal is decisive, and a caveat/discharge refusal can only arise
        // once the chain has already verified.
        match self.verify(root, &Context::new()) {
            Err(
                chain @ (Refusal::ProofMismatch
                | Refusal::BadSignature { .. }
                | Refusal::MalformedKey { .. }),
            ) => Err(chain),
            _ => Ok(()),
        }
    }

    fn proof_public(&self) -> [u8; 32] {
        self.try_proof_public().unwrap_or([0u8; 32])
    }

    fn try_proof_public(&self) -> Result<[u8; 32], WireReadError> {
        Ok(bearer_key(self)?.verifying_key().to_bytes())
    }

    fn sign_challenge(&self, msg: &[u8]) -> [u8; 64] {
        // Client-side helper (tests / a reference signer): the credential was
        // just minted locally, so its wire form is by construction the v1 schema.
        bearer_key(self)
            .expect("a locally-minted credential encodes to the v1 schema")
            .sign(msg)
            .to_bytes()
    }
}

// ---------------------------------------------------------------------------
// The bearer tail key + caveats, read back from the crate's own canonical wire
// form.
//
// A `dga1_` credential is a BEARER token: the encoded form carries the tail
// (proof-of-possession / attenuation) key seed and every block's caveats.
// `dregg_agent::cred` does not (yet) expose the tail key or a public caveat
// iterator on the in-memory `Credential`, so the verbs above round-trip through
// `Credential::encode` — the crate's own canonical serialization — and read the
// v1 schema (`CredentialWire { nonce, blocks[{caveats, next_pub, sig}],
// proof_seed }`, whose field/variant order is the load-bearing postcard layout
// shared with breadstuffs `dregg-auth`). This is the ONE piece of wire-schema
// knowledge kept locally.
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
#[allow(dead_code)] // postcard is positional: leading fields must parse to reach the rest
struct BearerBlockWire {
    caveats: Vec<Caveat>,
    next_pub: [u8; 32],
    sig: Vec<u8>,
}

#[derive(Deserialize)]
#[allow(dead_code)]
struct BearerWire {
    nonce: [u8; 32],
    blocks: Vec<BearerBlockWire>,
    proof_seed: [u8; 32],
}

fn wire(cred: &Credential) -> Result<BearerWire, WireReadError> {
    let enc = cred.encode();
    // Schema guard: each step returns a typed error instead of `.expect()`-ing,
    // so a `dregg_agent` wire-schema bump degrades to a clean `500` at the edge
    // rather than panicking mid-request and killing the worker thread.
    let body = enc
        .strip_prefix(CREDENTIAL_PREFIX)
        .ok_or(WireReadError::BadPrefix)?;
    let bytes = URL_SAFE_NO_PAD
        .decode(body)
        .map_err(|_| WireReadError::BadBase64)?;
    postcard::from_bytes(&bytes).map_err(|_| WireReadError::BadSchema)
}

fn bearer_key(cred: &Credential) -> Result<SigningKey, WireReadError> {
    Ok(SigningKey::from_bytes(&wire(cred)?.proof_seed))
}

/// Every caveat across all blocks, in block order (the expiry scan).
fn wire_caveats(cred: &Credential) -> Result<Vec<Caveat>, WireReadError> {
    Ok(wire(cred)?
        .blocks
        .into_iter()
        .flat_map(|b| b.caveats)
        .collect())
}

/// Verify a proof-of-possession signature: does `sig` over `msg` verify under
/// the ed25519 public key `pubkey`? The server side of the login handshake —
/// `pubkey` is the presented credential's [`CredentialExt::proof_public`],
/// `msg` is the domain-tagged login challenge. Fail-closed: a malformed
/// key/sig is `false`.
pub fn verify_pop(pubkey: &[u8; 32], msg: &[u8], sig: &[u8; 64]) -> bool {
    match VerifyingKey::from_bytes(pubkey) {
        Ok(vk) => vk.verify(msg, &Signature::from_bytes(sig)).is_ok(),
        Err(_) => false,
    }
}

// ===========================================================================
// Small hex helpers (display/config plumbing; the credential parsers are
// dregg-agent's)
// ===========================================================================

/// Lowercase hex of arbitrary bytes.
pub fn hex(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

/// Parse exactly 64 hex chars into 32 bytes.
pub fn unhex32(s: &str) -> Result<[u8; 32], KeyError> {
    let s = s.trim();
    if s.len() != 64 || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(KeyError("expected 64 hex chars".to_string()));
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = (chunk[0] as char).to_digit(16).unwrap() as u8;
        let lo = (chunk[1] as char).to_digit(16).unwrap() as u8;
        out[i] = (hi << 4) | lo;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::cred::RootKey;

    #[test]
    fn expiry_reads_the_wire_caveats() {
        let root = RootKey::from_seed([1u8; 32]);
        let cred = root.mint([Caveat::FirstParty(Pred::NotAfter { at: 1_000 })]);
        assert!(!cred.is_expired(999));
        assert!(cred.is_expired(1_001));
        // An attenuated tighter expiry also reads (caveats across ALL blocks).
        let tight = cred.attenuate([Caveat::FirstParty(Pred::NotAfter { at: 500 })]);
        assert!(tight.is_expired(501));
    }

    #[test]
    fn validity_honors_not_before_and_not_after() {
        let root = RootKey::from_seed([5u8; 32]);
        // A vesting window: valid only within [1000, 2000].
        let cred = root.mint([Caveat::FirstParty(Pred::Within {
            not_before: 1_000,
            not_after: 2_000,
        })]);
        assert_eq!(cred.validity(999), Ok(Validity::NotYetValid));
        assert_eq!(cred.validity(1_500), Ok(Validity::Valid));
        assert_eq!(cred.validity(2_001), Ok(Validity::Expired));
        // A bare NotBefore is not-yet-valid before it opens, then valid.
        let vest = root.mint([Caveat::FirstParty(Pred::NotBefore { at: 5_000 })]);
        assert_eq!(vest.validity(4_999), Ok(Validity::NotYetValid));
        assert_eq!(vest.validity(5_000), Ok(Validity::Valid));
        // is_expired treats both Valid and NotYetValid as "not expired" (the
        // 401-vs-403 probe is about lapse, not vesting — the /auth clock meet
        // rejects a not-yet-valid token on its own).
        assert!(!vest.is_expired(4_999));
        // A NotBefore-only token never lapses (no NotAfter): still not expired.
        assert!(!vest.is_expired(u64::MAX));
    }

    #[test]
    fn verify_chain_isolates_genuineness_from_caveats() {
        let root = RootKey::from_seed([2u8; 32]);
        let attacker = RootKey::from_seed([3u8; 32]);
        // A credential with an (unsatisfiable-here) caveat still chain-verifies…
        let cred = root.mint([Caveat::FirstParty(Pred::AttrEq {
            key: "cap".into(),
            value: "ops-admin".into(),
        })]);
        assert!(cred.verify_chain(&root.public()).is_ok());
        // …but not under the wrong root.
        assert!(cred.verify_chain(&attacker.public()).is_err());
    }

    #[test]
    fn pop_round_trips_and_fails_closed() {
        let root = RootKey::from_seed([4u8; 32]);
        let cred = root.mint([]);
        let msg = b"login challenge bytes";
        let sig = cred.sign_challenge(msg);
        assert!(verify_pop(&cred.proof_public(), msg, &sig));
        // Wrong message / wrong key → refused.
        assert!(!verify_pop(&cred.proof_public(), b"other", &sig));
        let other = root.mint([]);
        assert!(!verify_pop(&other.proof_public(), msg, &sig));
    }

    #[test]
    fn hex_round_trips() {
        let bytes = [0xABu8; 32];
        assert_eq!(unhex32(&hex(&bytes)).unwrap(), bytes);
        assert!(unhex32("zz").is_err());
    }
}
