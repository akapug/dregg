//! # `link_kel` — the D1 LINK/UNLINK memo convention + the pure event-fold.
//!
//! This is **brick 2** of the identity DEEP version
//! (`docs/IDENTITY-LINK-DEEP-VERSION-DESIGN.md`, stage D1). Brick 1
//! ([`crate::link_registry::account_id_of_root`]) made the TSV join key the
//! stable, inception-derived account id. Brick 2 defines what a link looks like
//! when it rides K's identity cell as an **`ixn` (interaction) turn** instead of
//! a bare TSV line — so links inherit chaining, receipts, federation witnesses,
//! and portable `verify_export` — and provides the **pure fold** that reads an
//! ordered LINK/UNLINK event list down to the current stable account id.
//!
//! ## What is here (all churn-independent Rust: serde/format + ed25519 + blake3)
//!
//! - [`LinkMemo`] — the canonical bytes a link/unlink event carries in its
//!   turn action/memo. Domain-tagged ([`LINK_MEMO_DOMAIN`]), NUL-delimited,
//!   injective; it wraps the existing [`crate::link_claim`] attestation (the
//!   platform / uid / custodial / root / challenge fields) plus a `LINK`/`UNLINK`
//!   verb and K's ed25519 signature. [`LinkMemo::to_bytes`] /
//!   [`LinkMemo::from_bytes`] round-trip it.
//! - [`fold_link_events`] — the **pure** resolver core: verify each event's K
//!   signature, enforce one-cell (one root) and monotonic order, fold
//!   `LINK`/`UNLINK` latest-wins per custodial into the current active binding
//!   set, and expose the cell's stable account id.
//! - [`resolve_root_from_events`] — the thin `custodial → account_id` seam,
//!   the cell-reading analogue of
//!   [`crate::link_registry::LinkStore::resolve_root_account`], testable with
//!   **no live node**.
//!
//! ## What the fold does NOT do (the honest D1 ceiling — see the design doc)
//!
//! - It **does not** replay key rotation. It pins a *single* signing root K for
//!   the whole event stream and derives the account id from it. On the real
//!   cell, K may rotate: the account id stays fixed (it is inception-derived)
//!   while new link events are signed by the *new* key set. That binding — link
//!   signature vs. the key set exhibited at each event, and `cell ==
//!   derive_raw(K_inception, account_root_token())` — is the **node-side**
//!   `verify_export` extension (design §1.2/§4), not this churn-independent core.
//! - It **does not** enforce *append-only-ness* or "only K may append" as a
//!   cell-program rule. In D1 that is carried by K's signature in the payload
//!   (checked here) and by the KEL's chain/receipts (checked node-side). The
//!   *enforced* links register is **D2 — AIR authored in Lean** (design §1.3),
//!   never a hand-written Rust constraint.
//! - It **does not** re-check challenge *freshness*. Freshness is a link-TIME
//!   property (the frontend checks it via [`crate::link_claim::verify_link_claim`]
//!   before the turn is ever submitted); at fold time the challenge is long
//!   expired and only the *signature over it* (non-repudiation) matters.

use std::collections::HashMap;

use ed25519_dalek::{Signature, VerifyingKey};

use crate::account_id::account_id_hex;
use crate::link_claim::{LinkClaimError, link_claim_message};

/// The domain-separation prefix of the on-turn link/unlink **memo** encoding.
/// Distinct from [`crate::link_claim::LINK_CLAIM_DOMAIN`] (the signed
/// attestation) and from the offering-turn domain, so a memo blob can never be
/// mistaken for either. The verb byte lives immediately after this prefix.
pub const LINK_MEMO_DOMAIN: &str = "dregg-identity-link-memo-v1:";

/// The domain-separation prefix of the **UNLINK** signed attestation — the
/// sibling of [`crate::link_claim::LINK_CLAIM_DOMAIN`]. K signs [`unlink_claim_message`] under
/// this domain, so a `LINK` signature can never be replayed as an `UNLINK`
/// (the domains differ ⇒ the signed bytes differ ⇒ `verify_strict` fails).
pub const UNLINK_CLAIM_DOMAIN: &str = "dregg-identity-unlink-v1:";

/// LINK or UNLINK — the verb a link event carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkVerb {
    /// K attests it controls this platform account (binds `custodial → K`).
    Link,
    /// K revokes a prior link over the same `(platform, uid)` — a revocation
    /// event; history is preserved (the KEL never rewrites), the fold just
    /// stops resolving the custodial.
    Unlink,
}

impl LinkVerb {
    /// Stable byte for the memo encoding.
    fn byte(self) -> u8 {
        match self {
            LinkVerb::Link => 1,
            LinkVerb::Unlink => 2,
        }
    }

    fn from_byte(b: u8) -> Option<LinkVerb> {
        match b {
            1 => Some(LinkVerb::Link),
            2 => Some(LinkVerb::Unlink),
            _ => None,
        }
    }
}

/// The canonical bytes of one link/unlink event as it rides an `ixn` turn's
/// action/memo. The turn hash commits these bytes (so tampering breaks the KEL
/// chain), and the embedded [`signature`](LinkMemo::signature) is K's
/// non-repudiable authorization over the [`crate::link_claim`] (or unlink)
/// attestation message.
///
/// Wire layout ([`to_bytes`](LinkMemo::to_bytes)):
///
/// ```text
/// LINK_MEMO_DOMAIN ‖ verb(1) ‖ platform ‖ 0 ‖ platform_uid ‖ 0 ‖
///   custodial_pubkey_hex ‖ 0 ‖ challenge ‖ 0 ‖ root_pubkey(32) ‖ signature(64)
/// ```
///
/// The four text fields are NUL-delimited (each is NUL-free by construction —
/// ascii platform, decimal uid, hex key, base64url challenge — and NUL is
/// refused by the encoder); the two fixed-width byte fields trail so the
/// decoder can split them off by length.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkMemo {
    /// LINK or UNLINK.
    pub verb: LinkVerb,
    /// The platform this event is for (`"discord"`, `"telegram"`, `"web"`).
    pub platform: String,
    /// The platform account id (decimal uid string for Discord/Telegram).
    pub platform_uid: String,
    /// The platform's CUSTODIAL dregg pubkey (lowercase hex) — the key
    /// resolution maps FROM.
    pub custodial_pubkey_hex: String,
    /// The user-held ROOT key K's pubkey (raw 32 bytes) — the signer. The
    /// stable account id is [`account_id_hex`] of this (or, under rotation, of
    /// K's inception key; see the module note).
    pub root_pubkey: [u8; 32],
    /// The freshness challenge the attestation was signed over (see
    /// [`crate::challenge`]). Bound into the signed message; freshness itself is
    /// a link-TIME check, not re-evaluated at fold time.
    pub challenge: String,
    /// K's ed25519 signature over the verb-appropriate attestation message
    /// ([`link_claim_message`] for LINK, [`unlink_claim_message`] for UNLINK).
    pub signature: [u8; 64],
}

impl LinkMemo {
    /// Encode the canonical on-turn bytes. `None` if any text field carries a
    /// NUL (the delimiter) — the same collision-hardening guard the extension
    /// signer and [`crate::link_claim`] use.
    pub fn to_bytes(&self) -> Option<Vec<u8>> {
        for f in [
            &self.platform,
            &self.platform_uid,
            &self.custodial_pubkey_hex,
            &self.challenge,
        ] {
            if f.as_bytes().contains(&0) {
                return None;
            }
        }
        let mut m = Vec::with_capacity(
            LINK_MEMO_DOMAIN.len()
                + 1
                + self.platform.len()
                + self.platform_uid.len()
                + self.custodial_pubkey_hex.len()
                + self.challenge.len()
                + 4
                + 32
                + 64,
        );
        m.extend_from_slice(LINK_MEMO_DOMAIN.as_bytes());
        m.push(self.verb.byte());
        m.extend_from_slice(self.platform.as_bytes());
        m.push(0);
        m.extend_from_slice(self.platform_uid.as_bytes());
        m.push(0);
        m.extend_from_slice(self.custodial_pubkey_hex.as_bytes());
        m.push(0);
        m.extend_from_slice(self.challenge.as_bytes());
        m.push(0);
        m.extend_from_slice(&self.root_pubkey);
        m.extend_from_slice(&self.signature);
        Some(m)
    }

    /// Decode the canonical on-turn bytes produced by [`to_bytes`](LinkMemo::to_bytes).
    /// `None` on the wrong domain, an unknown verb byte, a bad field count, a
    /// short buffer, or non-UTF-8 text — a malformed memo is skipped, never a
    /// panic.
    pub fn from_bytes(bytes: &[u8]) -> Option<LinkMemo> {
        let rest = bytes.strip_prefix(LINK_MEMO_DOMAIN.as_bytes())?;
        let (&verb_byte, body) = rest.split_first()?;
        let verb = LinkVerb::from_byte(verb_byte)?;
        // The trailing 96 bytes are root(32) ‖ signature(64); everything before
        // them is the four NUL-delimited, NUL-terminated text fields.
        if body.len() < 96 {
            return None;
        }
        let (text, tail) = body.split_at(body.len() - 96);
        let mut parts = text.split(|&c| c == 0);
        let platform = parts.next()?;
        let platform_uid = parts.next()?;
        let custodial = parts.next()?;
        let challenge = parts.next()?;
        // The four fields were each NUL-terminated, so `split` yields a final
        // empty part and nothing after it. Anything else means an extra/missing
        // delimiter — reject.
        if !parts.next()?.is_empty() || parts.next().is_some() {
            return None;
        }
        let root_pubkey: [u8; 32] = tail[..32].try_into().ok()?;
        let signature: [u8; 64] = tail[32..].try_into().ok()?;
        Some(LinkMemo {
            verb,
            platform: String::from_utf8(platform.to_vec()).ok()?,
            platform_uid: String::from_utf8(platform_uid.to_vec()).ok()?,
            custodial_pubkey_hex: String::from_utf8(custodial.to_vec()).ok()?,
            challenge: String::from_utf8(challenge.to_vec()).ok()?,
            root_pubkey,
            signature,
        })
    }

    /// The exact attestation message K signed for this event — [`link_claim_message`]
    /// (reused verbatim, byte-pinned) for LINK, [`unlink_claim_message`] for
    /// UNLINK. The root hex is the CANONICAL lowercase hex of
    /// [`root_pubkey`](LinkMemo::root_pubkey), so a memo can never name a
    /// different root than the key that signed it.
    pub fn signed_message(&self) -> Result<Vec<u8>, LinkClaimError> {
        let root_hex = hex::encode(self.root_pubkey);
        match self.verb {
            LinkVerb::Link => link_claim_message(
                &self.platform,
                &self.platform_uid,
                &self.custodial_pubkey_hex,
                &root_hex,
                &self.challenge,
            ),
            LinkVerb::Unlink => unlink_claim_message(
                &self.platform,
                &self.platform_uid,
                &self.custodial_pubkey_hex,
                &root_hex,
                &self.challenge,
            ),
        }
    }

    /// Verify K's signature over this memo's attestation message. Does NOT check
    /// challenge freshness (a fold-time property; see the module note) — only
    /// that the holder of [`root_pubkey`](LinkMemo::root_pubkey) authorized this
    /// exact `(verb, platform, uid, custodial, challenge)` tuple.
    pub fn verify_signature(&self) -> Result<(), LinkClaimError> {
        let msg = self.signed_message()?;
        let vk =
            VerifyingKey::from_bytes(&self.root_pubkey).map_err(|_| LinkClaimError::BadRootKey)?;
        let sig = Signature::from_bytes(&self.signature);
        vk.verify_strict(&msg, &sig)
            .map_err(|_| LinkClaimError::BadSignature)
    }
}

/// The canonical UNLINK attestation message — the byte-for-byte sibling of
/// [`link_claim_message`] under [`UNLINK_CLAIM_DOMAIN`]:
///
/// `UNLINK_CLAIM_DOMAIN ‖ platform ‖ 0 ‖ platform_uid ‖ 0 ‖ custodial_pubkey_hex
///  ‖ 0 ‖ root_pubkey_hex ‖ 0 ‖ challenge`
///
/// The distinct domain is the whole point: it makes an UNLINK signature
/// unforgeable from a LINK one and vice versa.
pub fn unlink_claim_message(
    platform: &str,
    platform_uid: &str,
    custodial_pubkey_hex: &str,
    root_pubkey_hex: &str,
    challenge: &str,
) -> Result<Vec<u8>, LinkClaimError> {
    for field in [
        platform,
        platform_uid,
        custodial_pubkey_hex,
        root_pubkey_hex,
        challenge,
    ] {
        if field.as_bytes().contains(&0) {
            return Err(LinkClaimError::FieldContainsNul);
        }
    }
    let mut m = Vec::with_capacity(
        UNLINK_CLAIM_DOMAIN.len()
            + platform.len()
            + platform_uid.len()
            + custodial_pubkey_hex.len()
            + root_pubkey_hex.len()
            + challenge.len()
            + 4,
    );
    m.extend_from_slice(UNLINK_CLAIM_DOMAIN.as_bytes());
    m.extend_from_slice(platform.as_bytes());
    m.push(0);
    m.extend_from_slice(platform_uid.as_bytes());
    m.push(0);
    m.extend_from_slice(custodial_pubkey_hex.as_bytes());
    m.push(0);
    m.extend_from_slice(root_pubkey_hex.as_bytes());
    m.push(0);
    m.extend_from_slice(challenge.as_bytes());
    Ok(m)
}

/// One link event in KEL order: the KEL-assigned sequence position plus the
/// signed [`LinkMemo`]. `seq` is the ledger's ordering (dense monotonic per
/// cell, with gaps where non-link `ixn`/`rot` turns sit between links); the
/// fold only requires it strictly increase. `seq` is NOT part of the signed
/// memo — order is the KEL's job (`prior_event_digest` chaining, enforced
/// node-side); this field models that order for the pure fold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkEvent {
    /// The event's position in the cell's KEL (KERI `s`).
    pub seq: u64,
    /// The signed link/unlink memo.
    pub memo: LinkMemo,
}

impl LinkEvent {
    /// Convenience constructor.
    pub fn new(seq: u64, memo: LinkMemo) -> Self {
        LinkEvent { seq, memo }
    }
}

/// One currently-active link binding after the fold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActiveLink {
    /// The platform (`"discord"`, `"telegram"`, `"web"`).
    pub platform: String,
    /// The platform account id.
    pub platform_uid: String,
}

/// The result of folding a verified, ordered link-event list: the cell's stable
/// account id plus the set of custodial keys currently linked to it.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LinkResolution {
    /// K's stable, inception-derived account id (lowercase hex) — the cell's
    /// owner. Every event in one stream resolves here; `None` only when the
    /// event list was empty. All `resolve_root` hits return THIS id.
    pub account_id: Option<String>,
    /// custodial_pubkey_hex (lowercase) → its current active link. A custodial
    /// is present iff its latest event was a LINK.
    active: HashMap<String, ActiveLink>,
}

impl LinkResolution {
    /// Resolve a custodial pubkey to the cell's stable account id — the
    /// cell-reading analogue of
    /// [`crate::link_registry::LinkStore::resolve_root_account`]. `None` if that
    /// custodial's latest event was an UNLINK, it was never linked, or the list
    /// was empty.
    pub fn resolve_root(&self, custodial_pubkey_hex: &str) -> Option<String> {
        let key = custodial_pubkey_hex.to_ascii_lowercase();
        if self.active.contains_key(&key) {
            self.account_id.clone()
        } else {
            None
        }
    }

    /// The active link for a custodial, if any (for `platforms_for_root`-style
    /// display).
    pub fn active_link(&self, custodial_pubkey_hex: &str) -> Option<&ActiveLink> {
        self.active.get(&custodial_pubkey_hex.to_ascii_lowercase())
    }

    /// Every currently-active link on this cell.
    pub fn active_links(&self) -> impl Iterator<Item = &ActiveLink> {
        self.active.values()
    }

    /// How many DISTINCT platforms are currently linked to this human — the
    /// `platforms_count` the linked-platforms credential attests
    /// ([`crate::linked_platforms`]).
    pub fn linked_platform_count(&self) -> usize {
        let mut seen: Vec<&str> = self.active.values().map(|a| a.platform.as_str()).collect();
        seen.sort_unstable();
        seen.dedup();
        seen.len()
    }

    /// Whether a link to the named platform is currently active.
    pub fn has_platform(&self, platform: &str) -> bool {
        self.active.values().any(|a| a.platform == platform)
    }
}

/// Why folding a link-event list failed (fail-closed — the whole fold is
/// refused, never a partial resolution).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkFoldError {
    /// Two events out of KEL order (`seq` did not strictly increase). The KEL's
    /// chain guarantees dense monotonic order node-side; a caller that passes a
    /// mis-ordered list is refused here.
    OutOfOrder { seq: u64, prev_seq: u64 },
    /// An event whose signing root differs from the stream's established root —
    /// a foreign event spliced into another cell's log. (Under rotation the
    /// per-event key set is checked node-side; see the module note.)
    ForeignCell { seq: u64 },
    /// The event's `root_pubkey` is not a valid ed25519 point.
    BadRootKey { seq: u64 },
    /// K's signature did not verify over the event's attestation message — a
    /// forged, tampered, or cross-verb-spliced event.
    BadSignature { seq: u64 },
    /// A memo field carried a NUL (the delimiter) and no canonical message
    /// exists — a malformed event.
    MalformedField { seq: u64 },
}

fn fold_err(seq: u64, e: LinkClaimError) -> LinkFoldError {
    match e {
        LinkClaimError::FieldContainsNul => LinkFoldError::MalformedField { seq },
        LinkClaimError::BadRootKey => LinkFoldError::BadRootKey { seq },
        LinkClaimError::BadSignature => LinkFoldError::BadSignature { seq },
        // Fold never checks freshness, so a challenge error cannot arise here;
        // classify it defensively as a malformed event rather than panic.
        LinkClaimError::StaleChallenge(_) => LinkFoldError::MalformedField { seq },
    }
}

/// The pure resolver core: verify + fold an ordered LINK/UNLINK event list into
/// the current active binding set. Fail-closed.
///
/// For each event, in order: (1) `seq` must strictly increase; (2) the signing
/// root must equal the first event's root (one cell = one root, the
/// churn-independent stand-in for the node-side `cell ==
/// derive_raw(K_inception, ..)` check); (3) K's signature must verify over the
/// event's attestation message. Then the verb is applied latest-wins per
/// custodial: LINK installs/refreshes the binding, UNLINK removes it. The stable
/// account id is [`account_id_hex`] of the established root.
///
/// This is the testable heart of the cell-reading `resolve_root` (design §1.2
/// steps 2–4), exercised with **no live node**. The node-side `verify_export`
/// wraps it with the chain/receipt/witness teeth and the rotation-aware key-set
/// binding (design §8).
pub fn fold_link_events(events: &[LinkEvent]) -> Result<LinkResolution, LinkFoldError> {
    let mut cell_root: Option<[u8; 32]> = None;
    let mut prev_seq: Option<u64> = None;
    let mut active: HashMap<String, ActiveLink> = HashMap::new();

    for ev in events {
        let seq = ev.seq;

        // (1) monotonic KEL order.
        if let Some(p) = prev_seq
            && seq <= p
        {
            return Err(LinkFoldError::OutOfOrder { seq, prev_seq: p });
        }
        prev_seq = Some(seq);

        // (2) one cell = one signing root.
        match cell_root {
            None => cell_root = Some(ev.memo.root_pubkey),
            Some(r) if r == ev.memo.root_pubkey => {}
            Some(_) => return Err(LinkFoldError::ForeignCell { seq }),
        }

        // (3) K authorized this exact event.
        ev.memo.verify_signature().map_err(|e| fold_err(seq, e))?;

        // Fold latest-wins per custodial.
        let key = ev.memo.custodial_pubkey_hex.to_ascii_lowercase();
        match ev.memo.verb {
            LinkVerb::Link => {
                active.insert(
                    key,
                    ActiveLink {
                        platform: ev.memo.platform.clone(),
                        platform_uid: ev.memo.platform_uid.clone(),
                    },
                );
            }
            LinkVerb::Unlink => {
                active.remove(&key);
            }
        }
    }

    Ok(LinkResolution {
        account_id: cell_root.map(|r| account_id_hex(&r)),
        active,
    })
}

/// Resolve a custodial pubkey to the cell's stable account id from an ordered
/// LINK/UNLINK event list — the cell-reading analogue of
/// [`crate::link_registry::LinkStore::resolve_root_account`], with **no live
/// node**. `None` if the fold refuses (forged/out-of-order/foreign event) or the
/// custodial is not currently linked.
///
/// Use [`fold_link_events`] directly when you need to distinguish "refused" from
/// "unlinked", or when you want the whole active binding set (e.g. the
/// linked-platforms credential attributes).
pub fn resolve_root_from_events(
    events: &[LinkEvent],
    custodial_pubkey_hex: &str,
) -> Option<String> {
    fold_link_events(events)
        .ok()?
        .resolve_root(custodial_pubkey_hex)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::link_registry::{InMemoryLinkStore, LinkRecord, LinkStore, account_id_of_root};
    use ed25519_dalek::{Signer, SigningKey};

    fn k() -> SigningKey {
        SigningKey::from_bytes(&[3u8; 32])
    }

    /// Play the client: build the verb-appropriate attestation message and sign
    /// it with K, producing a well-formed [`LinkMemo`].
    fn signed_memo(
        sk: &SigningKey,
        verb: LinkVerb,
        platform: &str,
        uid: &str,
        custodial: &str,
        challenge: &str,
    ) -> LinkMemo {
        let root = sk.verifying_key().to_bytes();
        let mut memo = LinkMemo {
            verb,
            platform: platform.into(),
            platform_uid: uid.into(),
            custodial_pubkey_hex: custodial.into(),
            root_pubkey: root,
            challenge: challenge.into(),
            signature: [0u8; 64],
        };
        let sig = sk.sign(&memo.signed_message().unwrap());
        memo.signature = sig.to_bytes();
        memo
    }

    /// The memo encodes and decodes byte-for-byte (the wire-drift killer for the
    /// on-turn format).
    #[test]
    fn memo_round_trips() {
        let sk = k();
        let memo = signed_memo(
            &sk,
            LinkVerb::Link,
            "discord",
            "6913902526",
            "aa",
            "chal-xyz",
        );
        let bytes = memo.to_bytes().expect("well-formed memo encodes");
        let back = LinkMemo::from_bytes(&bytes).expect("its own bytes decode");
        assert_eq!(memo, back);
        // A truncated / re-tagged buffer does not decode.
        assert!(LinkMemo::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        assert!(LinkMemo::from_bytes(b"not-the-domain").is_none());
    }

    /// A genuine memo's signature verifies; the same fields under UNLINK do NOT
    /// (distinct domain) — a LINK signature can't be replayed as an UNLINK.
    #[test]
    fn verb_domains_are_unspliceable() {
        let sk = k();
        let link = signed_memo(&sk, LinkVerb::Link, "telegram", "42", "cc", "chal");
        assert_eq!(link.verify_signature(), Ok(()));
        // Reuse the LINK signature but flip the verb to UNLINK → refused.
        let mut spliced = link.clone();
        spliced.verb = LinkVerb::Unlink;
        assert_eq!(
            spliced.verify_signature(),
            Err(LinkClaimError::BadSignature)
        );
    }

    /// LINK → UNLINK → LINK folds to a live binding; ending on UNLINK folds to
    /// none. Latest event wins per custodial.
    #[test]
    fn link_unlink_relink_folds() {
        let sk = k();
        let want = Some(account_id_hex(&sk.verifying_key().to_bytes()));

        let relink = vec![
            LinkEvent::new(
                0,
                signed_memo(&sk, LinkVerb::Link, "discord", "111", "custD", "c0"),
            ),
            LinkEvent::new(
                3,
                signed_memo(&sk, LinkVerb::Unlink, "discord", "111", "custD", "c1"),
            ),
            LinkEvent::new(
                7,
                signed_memo(&sk, LinkVerb::Link, "discord", "111", "custD", "c2"),
            ),
        ];
        assert_eq!(resolve_root_from_events(&relink, "custD"), want);

        // Same, but stop at the UNLINK → the custodial no longer resolves.
        let unlinked = &relink[..2];
        assert_eq!(resolve_root_from_events(unlinked, "custD"), None);
        // ...and the fold still SUCCEEDS (unlinked is a valid state, not an error).
        let res = fold_link_events(unlinked).expect("unlink is a valid fold");
        assert_eq!(res.account_id, want); // the cell still belongs to K
        assert_eq!(res.resolve_root("custD"), None);
    }

    /// A forged event (signature does not verify under the named root) is
    /// refused — the whole fold fails closed.
    #[test]
    fn a_forged_event_is_rejected() {
        let sk = k();
        // Sign a genuine memo, then tamper the uid it claims — signature no
        // longer matches the message.
        let mut forged = signed_memo(&sk, LinkVerb::Link, "discord", "111", "custD", "c0");
        forged.platform_uid = "999".into();
        let events = vec![LinkEvent::new(0, forged)];
        assert_eq!(
            fold_link_events(&events),
            Err(LinkFoldError::BadSignature { seq: 0 })
        );
        assert_eq!(resolve_root_from_events(&events, "custD"), None);
    }

    /// An out-of-order event list (seq not strictly increasing) is refused.
    #[test]
    fn out_of_order_events_are_rejected() {
        let sk = k();
        let events = vec![
            LinkEvent::new(
                0,
                signed_memo(&sk, LinkVerb::Link, "discord", "111", "custD", "c0"),
            ),
            LinkEvent::new(
                5,
                signed_memo(&sk, LinkVerb::Link, "telegram", "222", "custT", "c1"),
            ),
            LinkEvent::new(
                5,
                signed_memo(&sk, LinkVerb::Link, "web", "333", "custW", "c2"),
            ),
        ];
        assert_eq!(
            fold_link_events(&events),
            Err(LinkFoldError::OutOfOrder {
                seq: 5,
                prev_seq: 5
            })
        );
    }

    /// A second cell's event (a different signing root) spliced into the stream
    /// is refused — one fold is one cell.
    #[test]
    fn a_foreign_cell_event_is_rejected() {
        let sk = k();
        let other = SigningKey::from_bytes(&[9u8; 32]);
        let events = vec![
            LinkEvent::new(
                0,
                signed_memo(&sk, LinkVerb::Link, "discord", "111", "custD", "c0"),
            ),
            LinkEvent::new(
                1,
                signed_memo(&other, LinkVerb::Link, "telegram", "222", "custT", "c1"),
            ),
        ];
        assert_eq!(
            fold_link_events(&events),
            Err(LinkFoldError::ForeignCell { seq: 1 })
        );
    }

    /// THE cross-check: the cell-fold and the shipped TSV `resolve_root_account`
    /// return the SAME stable account id for the equivalent link set. This is
    /// what makes the migration (design §5) a cache-source swap behind an
    /// unchanged resolver, not a re-keying.
    #[test]
    fn fold_matches_resolve_root_account_for_the_equivalent_tsv() {
        let sk = k();
        let root_hex = hex::encode(sk.verifying_key().to_bytes());

        // Two platforms linked to one K, as cell events...
        let events = vec![
            LinkEvent::new(
                0,
                signed_memo(&sk, LinkVerb::Link, "discord", "111", "custD", "c0"),
            ),
            LinkEvent::new(
                1,
                signed_memo(&sk, LinkVerb::Link, "telegram", "222", "custT", "c1"),
            ),
        ];
        // ...and the byte-equivalent TSV records.
        let mut store = InMemoryLinkStore::default();
        store
            .record(&LinkRecord {
                root_pubkey_hex: root_hex.clone(),
                platform: "discord".into(),
                platform_uid: "111".into(),
                custodial_pubkey_hex: "custD".into(),
                verified_at: 100,
            })
            .unwrap();
        store
            .record(&LinkRecord {
                root_pubkey_hex: root_hex.clone(),
                platform: "telegram".into(),
                platform_uid: "222".into(),
                custodial_pubkey_hex: "custT".into(),
                verified_at: 101,
            })
            .unwrap();

        for custodial in ["custD", "custT"] {
            let from_events = resolve_root_from_events(&events, custodial);
            let from_tsv = store.resolve_root_account(custodial).unwrap();
            assert_eq!(from_events, from_tsv, "custodial {custodial}");
            assert_eq!(from_events, Some(account_id_of_root(&root_hex).unwrap()));
        }
        // Distinct platforms, one human.
        let res = fold_link_events(&events).unwrap();
        assert_eq!(res.linked_platform_count(), 2);
        assert!(res.has_platform("discord") && res.has_platform("telegram"));
        assert_eq!(resolve_root_from_events(&events, "stranger"), None);
    }
}
