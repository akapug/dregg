//! The key hierarchy + envelope encryption — the at-rest confidentiality core.
//!
//! ## The hierarchy (envelope encryption)
//!
//! ```text
//!   KMS root (32 bytes)                      ── the trust anchor
//!     └─ per-account KEK = BLAKE3.derive_key("…account-kek", root ‖ account)
//!          └─ per-secret DEK (fresh random per secret VERSION)
//!               · the secret value is sealed under the DEK   (XChaCha20-Poly1305)
//!               · the DEK is wrapped under the account KEK    (XChaCha20-Poly1305)
//! ```
//!
//! At rest a secret version is an [`Envelope`]: `{ wrapped_dek, body }`. Neither
//! the value nor the DEK is ever stored in the clear. The account id is bound in
//! as AEAD associated data on BOTH layers, so an envelope cannot be lifted from
//! one account's store and opened under another's KEK (a tamper/replay tooth).
//!
//! ## What this protects against — and the honest limit
//!
//! Envelope encryption defeats **at-rest compromise**: someone who steals the
//! serialized store (the DB, a backup, a disk image) but NOT the KMS root learns
//! nothing — every byte at rest is ciphertext, and the root is never written
//! beside it.
//!
//! It does **NOT**, by itself, blind the **operator**. If the host holds the KMS
//! root ([`KmsRoot::operator_held`]) it can derive any account KEK and unwrap any
//! DEK — so an operator who *wants* to read tenant plaintext can. That is the
//! honest limit, surfaced as [`KmsRoot::operator_can_read`]. The path to genuine
//! operator-blindness is a **tenant-held root** ([`KmsRoot::tenant_held`] /
//! BYO-KMS): the tenant keeps the 32 bytes (in their wallet / an external KMS /
//! an HSM / a TEE), hands the store only the derived material at use-time, and
//! the operator never possesses the anchor. The store code is identical either
//! way; only *who holds the root* changes, and that is the real security
//! boundary — named, not hidden.

use zeroize::Zeroizing;

use crate::SecretError;

/// BLAKE3 derive-key context for the per-account KEK. Versioned with the wire.
const ACCOUNT_KEK_CTX: &str = "dreggnet-secrets v1 account-kek";

/// Who holds the KMS root — the real security boundary for operator-visibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootHolder {
    /// The host/operator holds the root. Envelope encryption protects the store
    /// at rest, but the operator CAN derive+decrypt tenant plaintext if it
    /// chooses. The honest default for a managed service.
    Operator,
    /// The tenant holds the root (BYO-KMS). The operator never possesses the
    /// anchor, so it genuinely cannot read tenant plaintext — the upgrade path
    /// to true operator-blindness.
    Tenant,
}

/// The KMS root — the trust anchor of the whole hierarchy. Zeroized on drop.
pub struct KmsRoot {
    root: Zeroizing<[u8; 32]>,
    holder: RootHolder,
}

impl KmsRoot {
    /// An **operator-held** root from a 32-byte seed. Protects the store at rest;
    /// the operator can still derive+decrypt (see [`operator_can_read`](Self::operator_can_read)).
    pub fn operator_held(seed: [u8; 32]) -> KmsRoot {
        KmsRoot {
            root: Zeroizing::new(seed),
            holder: RootHolder::Operator,
        }
    }

    /// A **tenant-held** root (BYO-KMS) from a 32-byte seed the tenant controls.
    /// The operator never sees this — true operator-blindness.
    pub fn tenant_held(seed: [u8; 32]) -> KmsRoot {
        KmsRoot {
            root: Zeroizing::new(seed),
            holder: RootHolder::Tenant,
        }
    }

    /// Generate a fresh operator-held root from OS randomness.
    pub fn generate_operator() -> KmsRoot {
        KmsRoot::operator_held(fresh_32())
    }

    /// Generate a fresh tenant-held root from OS randomness.
    pub fn generate_tenant() -> KmsRoot {
        KmsRoot::tenant_held(fresh_32())
    }

    /// Who holds this root.
    pub fn holder(&self) -> RootHolder {
        self.holder
    }

    /// **The honest limit, surfaced.** `true` iff the operator can derive+decrypt
    /// tenant plaintext (an operator-held root). `false` for a tenant-held root.
    /// A surface that claims operator-blindness MUST check this is `false`.
    pub fn operator_can_read(&self) -> bool {
        matches!(self.holder, RootHolder::Operator)
    }

    /// Derive the per-account key-encryption-key (KEK), domain-separated and
    /// bound to the account id. Zeroized on drop.
    pub(crate) fn account_kek(&self, account: &str) -> Zeroizing<[u8; 32]> {
        let mut h = blake3::Hasher::new_derive_key(ACCOUNT_KEK_CTX);
        h.update(&self.root[..]);
        h.update(account.as_bytes());
        Zeroizing::new(*h.finalize().as_bytes())
    }
}

impl std::fmt::Debug for KmsRoot {
    /// REDACTED — the root never prints (a confinement tooth).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KmsRoot")
            .field("root", &"<redacted>")
            .field("holder", &self.holder)
            .finish()
    }
}

/// A sealed secret version: the value sealed under a fresh DEK, the DEK wrapped
/// under the account KEK. The on-disk / on-the-wire form. Carries NO plaintext.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Envelope {
    /// `AEAD(account_kek, dek)` — nonce ‖ ciphertext.
    wrapped_dek: Vec<u8>,
    /// `AEAD(dek, plaintext)` — nonce ‖ ciphertext.
    body: Vec<u8>,
}

impl Envelope {
    /// Seal `plaintext` for `account`: fresh DEK → seal the value → wrap the DEK
    /// under the account KEK. The account id is the AEAD associated data on both
    /// layers (cross-account move/replay fails to open).
    pub fn seal(kms: &KmsRoot, account: &str, plaintext: &[u8]) -> Envelope {
        let aad = account.as_bytes();
        let dek = Zeroizing::new(fresh_32());
        let body = aead_seal(&dek, aad, plaintext);
        let kek = kms.account_kek(account);
        let wrapped_dek = aead_seal(&kek, aad, &dek[..]);
        Envelope { wrapped_dek, body }
    }

    /// Open the envelope for `account`: unwrap the DEK under the account KEK,
    /// then decrypt the value. Fails closed (no plaintext) on any tamper, a
    /// wrong root, or a cross-account move (AAD mismatch).
    pub fn open(&self, kms: &KmsRoot, account: &str) -> Result<Zeroizing<Vec<u8>>, SecretError> {
        let aad = account.as_bytes();
        let kek = kms.account_kek(account);
        let dek_vec = aead_open(&kek, aad, &self.wrapped_dek).map_err(|_| {
            SecretError::Crypto("DEK unwrap failed (wrong root / tamper / wrong account)".into())
        })?;
        let dek: [u8; 32] = dek_vec[..]
            .try_into()
            .map_err(|_| SecretError::Crypto("unwrapped DEK is not 32 bytes".into()))?;
        let dek = Zeroizing::new(dek);
        let pt = aead_open(&dek, aad, &self.body)
            .map_err(|_| SecretError::Crypto("value decrypt failed (tamper)".into()))?;
        Ok(Zeroizing::new(pt))
    }

    /// The opaque at-rest bytes (for the no-plaintext-leak scan: this is ALL the
    /// operator's storage layer ever holds for a secret version).
    pub fn wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.wrapped_dek.len() + self.body.len());
        out.extend_from_slice(&self.wrapped_dek);
        out.extend_from_slice(&self.body);
        out
    }
}

// ───────────────────────────── the AEAD primitive ───────────────────────────
//
// XChaCha20-Poly1305: a vetted AEAD with a 192-bit nonce, so a per-message
// RANDOM nonce is collision-safe without a counter. Wire form: 24-byte nonce
// prefix ‖ ciphertext+tag.

const XNONCE_LEN: usize = 24;

fn aead_seal(key: &[u8; 32], aad: &[u8], plaintext: &[u8]) -> Vec<u8> {
    use chacha20poly1305::aead::{Aead, KeyInit, Payload};
    use chacha20poly1305::{XChaCha20Poly1305, XNonce};

    let cipher = XChaCha20Poly1305::new_from_slice(key).expect("32-byte key");
    let mut nonce = [0u8; XNONCE_LEN];
    getrandom::fill(&mut nonce).expect("operating-system randomness is available");
    let nonce = XNonce::from_slice(&nonce);
    let ct = cipher
        .encrypt(
            nonce,
            Payload {
                msg: plaintext,
                aad,
            },
        )
        .expect("AEAD encryption is total");
    let mut out = Vec::with_capacity(XNONCE_LEN + ct.len());
    out.extend_from_slice(nonce.as_slice());
    out.extend_from_slice(&ct);
    out
}

fn aead_open(key: &[u8; 32], aad: &[u8], blob: &[u8]) -> Result<Vec<u8>, ()> {
    use chacha20poly1305::aead::{Aead, KeyInit, Payload};
    use chacha20poly1305::{XChaCha20Poly1305, XNonce};

    if blob.len() < XNONCE_LEN {
        return Err(());
    }
    let (nonce, ct) = blob.split_at(XNONCE_LEN);
    let cipher = XChaCha20Poly1305::new_from_slice(key).map_err(|_| ())?;
    let nonce = XNonce::from_slice(nonce);
    cipher
        .decrypt(nonce, Payload { msg: ct, aad })
        .map_err(|_| ())
}

fn fresh_32() -> [u8; 32] {
    let mut b = [0u8; 32];
    getrandom::fill(&mut b).expect("operating-system randomness is available");
    b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn envelope_roundtrips() {
        let kms = KmsRoot::operator_held([1u8; 32]);
        let env = Envelope::seal(&kms, "acct-A", b"DB_URL=postgres://secret");
        let pt = env.open(&kms, "acct-A").unwrap();
        assert_eq!(&pt[..], b"DB_URL=postgres://secret");
    }

    #[test]
    fn at_rest_is_ciphertext_only() {
        let kms = KmsRoot::operator_held([2u8; 32]);
        let secret = b"super-secret-value-xyz";
        let env = Envelope::seal(&kms, "acct-A", secret);
        // Neither the value nor the DEK appears in the at-rest bytes.
        let bytes = env.wire_bytes();
        assert!(
            !contains(&bytes, secret),
            "plaintext leaked into the envelope"
        );
    }

    #[test]
    fn cross_account_move_fails_to_open() {
        let kms = KmsRoot::operator_held([3u8; 32]);
        let env = Envelope::seal(&kms, "acct-A", b"value");
        // The SAME root, a DIFFERENT account: AAD + KEK both differ → no open.
        assert!(env.open(&kms, "acct-B").is_err());
    }

    #[test]
    fn wrong_root_fails_to_open() {
        let real = KmsRoot::operator_held([4u8; 32]);
        let attacker = KmsRoot::operator_held([5u8; 32]);
        let env = Envelope::seal(&real, "acct-A", b"value");
        assert!(env.open(&attacker, "acct-A").is_err());
    }

    #[test]
    fn tampering_the_body_fails_closed() {
        let kms = KmsRoot::operator_held([6u8; 32]);
        let mut env = Envelope::seal(&kms, "acct-A", b"value");
        let n = env.body.len();
        env.body[n - 1] ^= 0xff; // flip a tag byte
        assert!(env.open(&kms, "acct-A").is_err());
    }

    #[test]
    fn holder_surfaces_the_operator_limit() {
        assert!(KmsRoot::operator_held([0u8; 32]).operator_can_read());
        assert!(!KmsRoot::tenant_held([0u8; 32]).operator_can_read());
    }

    fn contains(haystack: &[u8], needle: &[u8]) -> bool {
        haystack.windows(needle.len()).any(|w| w == needle)
    }
}
