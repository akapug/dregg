//! ECIES note encryption for committed (privacy-preserving) notes.
//!
//! When a committed turn creates a note for a recipient, the recipient must
//! learn the note's *opening* — `(value, asset_type, blinding)` — so they can
//! later spend it (recompute the value commitment and produce a range/spend
//! proof). That opening must travel encrypted: only the recipient may read it,
//! and a tamper of the ciphertext must be detected.
//!
//! # Construction (the same ECIES box as [`crate::seal`])
//!
//! This composes the established sealer construction rather than inventing a
//! new one:
//!
//! - **Recipient key**: an X25519 public key (the recipient's stealth *view*
//!   key — see [`crate::stealth::StealthMetaAddress::view_pubkey`]).
//! - **Encrypt**: fresh ephemeral X25519 keypair; `DH(ephemeral_secret,
//!   recipient_public)` → BLAKE3 `derive_key` KDF (domain-separated, both public
//!   keys mixed in for session binding) → ChaCha20-Poly1305 AEAD over the
//!   serialized opening. The ephemeral public key is published in the box.
//! - **Decrypt**: `DH(recipient_secret, ephemeral_public)` → same KDF → AEAD
//!   open. The Poly1305 tag authenticates the ciphertext, so any tamper (wrong
//!   key, flipped byte, swapped ephemeral key) fails closed.
//! - **Forward secrecy**: every note uses a fresh ephemeral keypair.
//!
//! The wire form is a flat byte string `ephemeral_pubkey (32) || nonce (12) ||
//! ciphertext` so it drops straight into `Effect::NoteCreate { encrypted_note }`.

use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroize;

/// The plaintext opening of a committed note, recoverable only by the recipient.
///
/// This is exactly the secret a holder needs to later *spend* the note: the
/// cleartext `value` and `asset_type`, plus the 32-byte `blinding` factor used
/// in the Pedersen/Ristretto value commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotePlaintext {
    /// The note's cleartext value.
    pub value: u64,
    /// The asset type identifier.
    pub asset_type: u64,
    /// The 32-byte blinding factor (canonical little-endian scalar encoding).
    pub blinding: [u8; 32],
}

impl Drop for NotePlaintext {
    fn drop(&mut self) {
        self.blinding.zeroize();
    }
}

impl NotePlaintext {
    /// Versioned, fixed-layout serialization of the opening.
    ///
    /// `version(1) || value_le(8) || asset_type_le(8) || blinding(32)` = 49 bytes.
    fn serialize(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(49);
        buf.push(1u8); // version
        buf.extend_from_slice(&self.value.to_le_bytes());
        buf.extend_from_slice(&self.asset_type.to_le_bytes());
        buf.extend_from_slice(&self.blinding);
        buf
    }

    fn deserialize(data: &[u8]) -> Option<Self> {
        if data.len() != 49 || data[0] != 1 {
            return None;
        }
        let value = u64::from_le_bytes(data[1..9].try_into().ok()?);
        let asset_type = u64::from_le_bytes(data[9..17].try_into().ok()?);
        let mut blinding = [0u8; 32];
        blinding.copy_from_slice(&data[17..49]);
        Some(NotePlaintext {
            value,
            asset_type,
            blinding,
        })
    }
}

/// Errors from note decryption.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NoteDecryptError {
    /// The ciphertext is too short to contain the ECIES header.
    Truncated,
    /// AEAD authentication failed: wrong key or tampered ciphertext.
    DecryptionFailed,
    /// The decrypted bytes are not a valid note opening.
    MalformedPlaintext,
}

impl core::fmt::Display for NoteDecryptError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NoteDecryptError::Truncated => write!(f, "encrypted note is truncated"),
            NoteDecryptError::DecryptionFailed => {
                write!(f, "note decryption failed (wrong key or tampered)")
            }
            NoteDecryptError::MalformedPlaintext => {
                write!(f, "decrypted note opening is malformed")
            }
        }
    }
}

impl std::error::Error for NoteDecryptError {}

/// Wire header sizes.
const EPH_LEN: usize = 32;
const NONCE_LEN: usize = 12;
const HEADER_LEN: usize = EPH_LEN + NONCE_LEN;

/// Encrypt a note opening to the recipient's X25519 public key.
///
/// Returns the flat ECIES box `ephemeral_pubkey || nonce || ciphertext`,
/// ready to place in `Effect::NoteCreate { encrypted_note }`.
pub fn encrypt_note_to(recipient_x25519_pub: &[u8; 32], plaintext: &NotePlaintext) -> Vec<u8> {
    let mut eph_bytes = [0u8; 32];
    getrandom::fill(&mut eph_bytes).expect("getrandom failed");
    let ephemeral_secret = StaticSecret::from(eph_bytes);
    let ephemeral_public = PublicKey::from(&ephemeral_secret);

    let recipient_public = PublicKey::from(*recipient_x25519_pub);
    let shared = ephemeral_secret.diffie_hellman(&recipient_public);

    let enc_key = derive_note_key(
        shared.as_bytes(),
        ephemeral_public.as_bytes(),
        recipient_x25519_pub,
    );

    // Per-note nonce derived from fresh entropy; bound to the ephemeral key.
    // (A fresh ephemeral keypair per note already precludes nonce reuse under
    // one key; the random nonce is belt-and-suspenders.)
    let nonce = derive_nonce(ephemeral_public.as_bytes());

    let pt = plaintext.serialize();
    let ciphertext = encrypt(&enc_key, &nonce, &pt);

    let mut out = Vec::with_capacity(HEADER_LEN + ciphertext.len());
    out.extend_from_slice(ephemeral_public.as_bytes());
    out.extend_from_slice(&nonce[..NONCE_LEN]);
    out.extend_from_slice(&ciphertext);
    out
}

/// Decrypt a note opening with the recipient's X25519 *secret* (view) key.
///
/// Returns the recovered `(value, asset_type, blinding)`. Fails closed on a
/// wrong key or any tamper of the box.
pub fn decrypt_note(
    recipient_x25519_secret: &[u8; 32],
    encrypted_note: &[u8],
) -> Result<NotePlaintext, NoteDecryptError> {
    if encrypted_note.len() < HEADER_LEN {
        return Err(NoteDecryptError::Truncated);
    }
    let mut eph = [0u8; 32];
    eph.copy_from_slice(&encrypted_note[..EPH_LEN]);
    let mut nonce12 = [0u8; NONCE_LEN];
    nonce12.copy_from_slice(&encrypted_note[EPH_LEN..HEADER_LEN]);
    let ciphertext = &encrypted_note[HEADER_LEN..];

    let recipient_secret = StaticSecret::from(*recipient_x25519_secret);
    let recipient_public = PublicKey::from(&recipient_secret);
    let ephemeral_public = PublicKey::from(eph);
    let shared = recipient_secret.diffie_hellman(&ephemeral_public);

    let enc_key = derive_note_key(
        shared.as_bytes(),
        ephemeral_public.as_bytes(),
        recipient_public.as_bytes(),
    );

    let pt = decrypt(&enc_key, &nonce12, ciphertext).ok_or(NoteDecryptError::DecryptionFailed)?;
    NotePlaintext::deserialize(&pt).ok_or(NoteDecryptError::MalformedPlaintext)
}

// --- Internal helpers (mirroring `crate::seal`) ---

/// Derive the AEAD key from the raw X25519 shared secret using BLAKE3's KDF
/// mode. Raw DH output is biased and must never be used directly; both public
/// keys are mixed in to bind the key to this session (KCI resistance), and the
/// context string provides domain separation from `seal`/`stealth`.
fn derive_note_key(
    shared_secret: &[u8; 32],
    ephemeral_public: &[u8; 32],
    recipient_public: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-note encryption v1");
    hasher.update(shared_secret);
    hasher.update(ephemeral_public);
    hasher.update(recipient_public);
    *hasher.finalize().as_bytes()
}

/// Derive a 12-byte AEAD nonce from fresh entropy, bound to the ephemeral key.
fn derive_nonce(ephemeral_public: &[u8; 32]) -> [u8; NONCE_LEN] {
    let mut entropy = [0u8; 16];
    getrandom::fill(&mut entropy).expect("getrandom failed");
    let mut hasher = blake3::Hasher::new_derive_key("dregg-note nonce v1");
    hasher.update(ephemeral_public);
    hasher.update(&entropy);
    let full = *hasher.finalize().as_bytes();
    let mut nonce = [0u8; NONCE_LEN];
    nonce.copy_from_slice(&full[..NONCE_LEN]);
    nonce
}

fn encrypt(key: &[u8; 32], nonce: &[u8; NONCE_LEN], plaintext: &[u8]) -> Vec<u8> {
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new(key.into());
    let aead_nonce = chacha20poly1305::Nonce::from_slice(nonce);
    cipher
        .encrypt(aead_nonce, plaintext)
        .expect("encryption should not fail")
}

fn decrypt(key: &[u8; 32], nonce: &[u8; NONCE_LEN], ciphertext: &[u8]) -> Option<Vec<u8>> {
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new(key.into());
    let aead_nonce = chacha20poly1305::Nonce::from_slice(nonce);
    cipher.decrypt(aead_nonce, ciphertext).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stealth::StealthKeys;

    fn sample() -> NotePlaintext {
        NotePlaintext {
            value: 1_234_567,
            asset_type: 7,
            blinding: {
                let mut b = [0u8; 32];
                b[0] = 0x9A;
                b[31] = 0x42;
                b
            },
        }
    }

    #[test]
    fn roundtrip_recovers_opening() {
        // Recipient's stealth view key is an X25519 keypair.
        let keys = StealthKeys::from_keys([0x11; 32], [0x22; 32]);
        let meta = keys.meta_address();

        let pt = sample();
        let boxed = encrypt_note_to(&meta.view_pubkey, &pt);

        let recovered = decrypt_note(&keys.view_private_key, &boxed).expect("decrypt");
        assert_eq!(recovered.value, pt.value);
        assert_eq!(recovered.asset_type, pt.asset_type);
        assert_eq!(recovered.blinding, pt.blinding);
    }

    /// TOOTH: a wrong recipient key cannot decrypt — fails closed.
    #[test]
    fn wrong_key_fails() {
        let keys = StealthKeys::from_keys([0x11; 32], [0x22; 32]);
        let meta = keys.meta_address();
        let boxed = encrypt_note_to(&meta.view_pubkey, &sample());

        // A different recipient's view secret.
        let wrong = StealthKeys::from_keys([0x33; 32], [0x44; 32]);
        let err = decrypt_note(&wrong.view_private_key, &boxed).unwrap_err();
        assert_eq!(err, NoteDecryptError::DecryptionFailed);
    }

    /// TOOTH: a tampered ciphertext byte is detected by the AEAD tag.
    #[test]
    fn tampered_ciphertext_fails() {
        let keys = StealthKeys::from_keys([0xAB; 32], [0xCD; 32]);
        let meta = keys.meta_address();
        let mut boxed = encrypt_note_to(&meta.view_pubkey, &sample());

        // Flip a byte in the ciphertext region (after the 44-byte header).
        let last = boxed.len() - 1;
        boxed[last] ^= 0x01;
        let err = decrypt_note(&keys.view_private_key, &boxed).unwrap_err();
        assert_eq!(err, NoteDecryptError::DecryptionFailed);
    }

    /// TOOTH: a swapped ephemeral key (header tamper) breaks the shared secret.
    #[test]
    fn tampered_ephemeral_fails() {
        let keys = StealthKeys::from_keys([0x01; 32], [0x02; 32]);
        let meta = keys.meta_address();
        let mut boxed = encrypt_note_to(&meta.view_pubkey, &sample());

        boxed[0] ^= 0xFF; // corrupt the ephemeral pubkey
        let err = decrypt_note(&keys.view_private_key, &boxed).unwrap_err();
        assert_eq!(err, NoteDecryptError::DecryptionFailed);
    }

    /// A truncated box is rejected without panicking.
    #[test]
    fn truncated_box_rejected() {
        let keys = StealthKeys::from_keys([0x07; 32], [0x08; 32]);
        let short = vec![0u8; HEADER_LEN - 1];
        assert_eq!(
            decrypt_note(&keys.view_private_key, &short).unwrap_err(),
            NoteDecryptError::Truncated
        );
    }

    /// Distinct encryptions of the same opening differ (fresh ephemeral each).
    #[test]
    fn encryptions_are_randomized() {
        let keys = StealthKeys::from_keys([0x55; 32], [0x66; 32]);
        let meta = keys.meta_address();
        let pt = sample();
        let a = encrypt_note_to(&meta.view_pubkey, &pt);
        let b = encrypt_note_to(&meta.view_pubkey, &pt);
        assert_ne!(a, b, "fresh ephemeral key must randomize the box");
        // Both still decrypt to the same opening.
        assert_eq!(
            decrypt_note(&keys.view_private_key, &a).unwrap(),
            decrypt_note(&keys.view_private_key, &b).unwrap()
        );
    }
}
