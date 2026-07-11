//! The dregg unlock attestation: the canonical bytes the oracle set signs, and the
//! parser for the Solana **ed25519 native-program** instruction that carries those
//! signatures.
//!
//! ## The signed message — dual of the lock attestation
//!
//! The mint direction is attested by `SolanaLockAttestation` in
//! `bridge/src/solana_mirror.rs`. Its signed bytes are (lines 115-123):
//!
//! ```text
//! SolanaLockAttestation::canonical_payload = lock_id ‖ spl_mint ‖ amount_le ‖ recipient ‖ epoch_le
//! SolanaLockAttestation::message_hash      = BLAKE3-derive_key("dregg-solana-mirror-v1", canonical_payload)
//! signature                                = ed25519_sign(message_hash)          (solana_mirror.rs:157-158)
//! ```
//!
//! The unlock (redeem) direction is the DUAL, over the fields of
//! `SolanaUnlockRequest` (`bridge/src/solana_mirror.rs:188`):
//! `{ spl_mint, amount, solana_recipient, redeem_id }`. This module defines its
//! canonical form, domain-separated from the lock direction so a lock attestation
//! signature can never be replayed as an unlock authorization (and vice-versa):
//!
//! ```text
//! unlock_canonical_payload = spl_mint ‖ amount_le ‖ solana_recipient ‖ redeem_id
//! unlock_message_hash      = BLAKE3-derive_key("dregg-solana-unlock-v1", unlock_canonical_payload)
//! oracle signature         = ed25519_sign(unlock_message_hash)
//! ```
//!
//! CROSS-CRATE SEAM (CLOSED): `bridge/src/solana_mirror.rs::SolanaUnlockRequest` now
//! exposes matching `canonical_payload` / `message_hash` (same field order, same
//! `dregg-solana-unlock-v1` domain), so the oracle relayer signs exactly the bytes
//! this module verifies. A GOLDEN 32-byte hash for a fixed input is pinned in BOTH
//! crates' tests (`hash_is_domain_separated_and_binds_every_field` here,
//! `solana_unlock_message_hash_golden` on the bridge), so any drift on either side
//! turns one suite red.

/// BLAKE3 `derive_key` context for the unlock direction. Distinct from the lock
/// direction's `"dregg-solana-mirror-v1"` (`solana_mirror.rs:51`) so the two signing
/// domains never collide.
pub const SOLANA_UNLOCK_DOMAIN: &str = "dregg-solana-unlock-v1";

/// Serialized length of the unlock canonical payload:
/// `spl_mint(32) ‖ amount_le(8) ‖ solana_recipient(32) ‖ redeem_id(32)`.
pub const UNLOCK_PAYLOAD_LEN: usize = 32 + 8 + 32 + 32;

/// The canonical bytes the oracle set signs for an unlock — the dual of
/// `SolanaLockAttestation::canonical_payload` (`solana_mirror.rs:115`).
pub fn unlock_canonical_payload(
    spl_mint: &[u8; 32],
    amount: u64,
    solana_recipient: &[u8; 32],
    redeem_id: &[u8; 32],
) -> [u8; UNLOCK_PAYLOAD_LEN] {
    let mut p = [0u8; UNLOCK_PAYLOAD_LEN];
    p[0..32].copy_from_slice(spl_mint);
    p[32..40].copy_from_slice(&amount.to_le_bytes());
    p[40..72].copy_from_slice(solana_recipient);
    p[72..104].copy_from_slice(redeem_id);
    p
}

/// The domain-separated 32-byte message hash the oracle signs — the dual of
/// `SolanaLockAttestation::message_hash` (`solana_mirror.rs:126-129`), using the
/// same BLAKE3 `derive_key` construction so it is byte-for-byte reproducible on the
/// bridge side.
pub fn unlock_message_hash(
    spl_mint: &[u8; 32],
    amount: u64,
    solana_recipient: &[u8; 32],
    redeem_id: &[u8; 32],
) -> [u8; 32] {
    let payload = unlock_canonical_payload(spl_mint, amount, solana_recipient, redeem_id);
    let mut h = blake3::Hasher::new_derive_key(SOLANA_UNLOCK_DOMAIN);
    h.update(&payload);
    *h.finalize().as_bytes()
}

// ---------------------------------------------------------------------------
// ed25519 native-program instruction parsing
// ---------------------------------------------------------------------------
//
// The Ed25519SigVerify native program (`solana_program::ed25519_program::id()`) is
// a PRECOMPILE: the runtime verifies every ed25519-program instruction in a
// transaction BEFORE any on-chain instruction executes; a bad signature aborts the
// whole transaction. So if our `unlock` is executing, every ed25519-program
// instruction present has already been verified as a real (pubkey, message, sig).
//
// We reconstruct which (pubkey, message) pairs were verified by parsing the
// instruction data. Layout (see solana-ed25519-program 2.2, `lib.rs`):
//
//   [ num_signatures: u8 ][ padding: u8 ]
//   num_signatures × Ed25519SignatureOffsets {   // 14 bytes, little-endian
//       signature_offset:            u16,
//       signature_instruction_index: u16,
//       public_key_offset:           u16,
//       public_key_instruction_index:u16,
//       message_data_offset:         u16,
//       message_data_size:           u16,
//       message_instruction_index:   u16,
//   }
//   ... referenced data (pubkey/sig/message), possibly in this or another instruction.
//
// An `*_instruction_index` of `u16::MAX` means "this instruction's own data".

/// Bytes of one 14-byte `Ed25519SignatureOffsets` entry.
pub const SIGNATURE_OFFSETS_SERIALIZED_SIZE: usize = 14;
/// Header bytes (num_signatures + padding) before the first offsets entry.
pub const SIGNATURE_OFFSETS_START: usize = 2;
/// A pubkey referenced by the offsets is 32 bytes.
pub const PUBKEY_SERIALIZED_SIZE: usize = 32;
/// The self-instruction sentinel for an `*_instruction_index`.
pub const IX_INDEX_CURRENT: u16 = u16::MAX;

/// A single (pubkey, message) claim carried by an ed25519 instruction, as raw
/// references (index + offset + size) that a caller resolves against instruction
/// data. Resolving is separated from parsing so the parser is pure/unit-testable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ed25519Ref {
    pub public_key_ix: u16,
    pub public_key_off: u16,
    pub message_ix: u16,
    pub message_off: u16,
    pub message_size: u16,
}

fn read_u16_le(data: &[u8], off: usize) -> Option<u16> {
    let b = data.get(off..off + 2)?;
    Some(u16::from_le_bytes([b[0], b[1]]))
}

/// Parse an ed25519 native-program instruction's `data` into a `Vec` of its
/// per-signature (pubkey, message) references. Returns `None` if the data is
/// malformed (which, for a precompile-verified instruction, cannot happen — a
/// malformed one would have aborted the transaction); we still fail closed.
pub fn parse_ed25519_refs(data: &[u8]) -> Option<Vec<Ed25519Ref>> {
    if data.len() < SIGNATURE_OFFSETS_START {
        return None;
    }
    let num_signatures = data[0] as usize;
    let expected = num_signatures
        .checked_mul(SIGNATURE_OFFSETS_SERIALIZED_SIZE)?
        .checked_add(SIGNATURE_OFFSETS_START)?;
    if data.len() < expected {
        return None;
    }
    let mut out = Vec::with_capacity(num_signatures);
    for i in 0..num_signatures {
        let start = i
            .checked_mul(SIGNATURE_OFFSETS_SERIALIZED_SIZE)?
            .checked_add(SIGNATURE_OFFSETS_START)?;
        // field order: sig_off, sig_ix, pk_off, pk_ix, msg_off, msg_size, msg_ix
        let public_key_off = read_u16_le(data, start + 4)?;
        let public_key_ix = read_u16_le(data, start + 6)?;
        let message_off = read_u16_le(data, start + 8)?;
        let message_size = read_u16_le(data, start + 10)?;
        let message_ix = read_u16_le(data, start + 12)?;
        out.push(Ed25519Ref {
            public_key_ix,
            public_key_off,
            message_ix,
            message_off,
            message_size,
        });
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn payload_is_dual_of_lock_field_order() {
        // spl_mint ‖ amount_le ‖ solana_recipient ‖ redeem_id
        let mint = [0x11u8; 32];
        let recipient = [0x22u8; 32];
        let redeem = [0x33u8; 32];
        let amount: u64 = 0x0102_0304_0506_0708;
        let p = unlock_canonical_payload(&mint, amount, &recipient, &redeem);
        assert_eq!(p.len(), 104);
        assert_eq!(&p[0..32], &mint);
        assert_eq!(&p[32..40], &amount.to_le_bytes());
        assert_eq!(
            &p[32..40],
            &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01],
            "amount is little-endian"
        );
        assert_eq!(&p[40..72], &recipient);
        assert_eq!(&p[72..104], &redeem);
    }

    #[test]
    fn hash_is_domain_separated_and_binds_every_field() {
        let base = unlock_message_hash(&[1u8; 32], 100, &[2u8; 32], &[3u8; 32]);
        // CROSS-CRATE GOLDEN: the bridge's SolanaUnlockRequest::message_hash pins
        // this SAME 32-byte array for this SAME input (bridge/src/solana_mirror.rs,
        // solana_unlock_message_hash_golden). If the payload layout or the
        // "dregg-solana-unlock-v1" domain drifts on either side, one suite goes red.
        assert_eq!(
            base,
            [
                28, 62, 5, 62, 129, 119, 208, 102, 202, 202, 65, 37, 134, 24, 125, 71, 85, 212, 9,
                127, 76, 5, 242, 153, 252, 118, 141, 38, 77, 191, 65, 189
            ]
        );
        // A change to ANY field changes the hash.
        assert_ne!(
            base,
            unlock_message_hash(&[9u8; 32], 100, &[2u8; 32], &[3u8; 32])
        );
        assert_ne!(
            base,
            unlock_message_hash(&[1u8; 32], 101, &[2u8; 32], &[3u8; 32])
        );
        assert_ne!(
            base,
            unlock_message_hash(&[1u8; 32], 100, &[9u8; 32], &[3u8; 32])
        );
        assert_ne!(
            base,
            unlock_message_hash(&[1u8; 32], 100, &[2u8; 32], &[9u8; 32])
        );
    }

    #[test]
    fn hash_matches_reference_blake3_derive_key() {
        // Independently recompute using the raw blake3 API to catch any drift in the
        // construction (domain string / payload layout).
        let mint = [7u8; 32];
        let recipient = [8u8; 32];
        let redeem = [9u8; 32];
        let amount = 42_000_000u64;
        let mut payload = Vec::new();
        payload.extend_from_slice(&mint);
        payload.extend_from_slice(&amount.to_le_bytes());
        payload.extend_from_slice(&recipient);
        payload.extend_from_slice(&redeem);
        let mut h = blake3::Hasher::new_derive_key(SOLANA_UNLOCK_DOMAIN);
        h.update(&payload);
        let expected = *h.finalize().as_bytes();
        assert_eq!(
            unlock_message_hash(&mint, amount, &recipient, &redeem),
            expected
        );
    }

    /// Build a self-contained ed25519 instruction data blob the way the solana-sdk
    /// helper does (all data in-instruction, indices = u16::MAX) and check the parser
    /// recovers the (pubkey, message) reference.
    #[test]
    fn parse_recovers_self_contained_refs() {
        let pubkey = [0xAAu8; 32];
        let signature = [0xBBu8; 64];
        let message = [0xCCu8; 32];

        let data_start = SIGNATURE_OFFSETS_START + SIGNATURE_OFFSETS_SERIALIZED_SIZE; // 16
        let public_key_offset = data_start; // 16
        let signature_offset = public_key_offset + PUBKEY_SERIALIZED_SIZE; // 48
        let message_offset = signature_offset + 64; // 112

        let mut data = Vec::new();
        data.push(1u8); // num_signatures
        data.push(0u8); // padding
                        // offsets entry (14 bytes): sig_off, sig_ix, pk_off, pk_ix, msg_off, msg_size, msg_ix
        data.extend_from_slice(&(signature_offset as u16).to_le_bytes());
        data.extend_from_slice(&IX_INDEX_CURRENT.to_le_bytes());
        data.extend_from_slice(&(public_key_offset as u16).to_le_bytes());
        data.extend_from_slice(&IX_INDEX_CURRENT.to_le_bytes());
        data.extend_from_slice(&(message_offset as u16).to_le_bytes());
        data.extend_from_slice(&(message.len() as u16).to_le_bytes());
        data.extend_from_slice(&IX_INDEX_CURRENT.to_le_bytes());
        // referenced data
        data.extend_from_slice(&pubkey);
        data.extend_from_slice(&signature);
        data.extend_from_slice(&message);

        let refs = parse_ed25519_refs(&data).expect("parses");
        assert_eq!(refs.len(), 1);
        let r = refs[0];
        assert_eq!(r.public_key_ix, IX_INDEX_CURRENT);
        assert_eq!(r.public_key_off as usize, public_key_offset);
        assert_eq!(r.message_ix, IX_INDEX_CURRENT);
        assert_eq!(r.message_off as usize, message_offset);
        assert_eq!(r.message_size as usize, message.len());

        // and the referenced slices are what we put in
        assert_eq!(
            &data[r.public_key_off as usize..r.public_key_off as usize + 32],
            &pubkey
        );
        assert_eq!(
            &data[r.message_off as usize..r.message_off as usize + r.message_size as usize],
            &message
        );
    }

    #[test]
    fn parse_rejects_truncated() {
        assert!(parse_ed25519_refs(&[]).is_none());
        // claims 1 signature but no offsets follow
        assert!(parse_ed25519_refs(&[1u8, 0u8]).is_none());
    }
}
