//! The program-owned config account schema (the vault's on-chain state).
//!
//! This is the program's OWN account schema (not the relayer-facing one — that is
//! the 72-byte lock record in [`crate::record`]). It records the mint being
//! mirrored, the **oracle key-set + threshold** that authorizes an unlock, the SPL
//! token vault account, the vault-authority PDA bump, and the monotonic lock nonce
//! that makes each `lock_id` unique.
//!
//! ## Trust model (v2 — the oracle set)
//!
//! v1 gated [`crate::instruction::LockInstruction::Unlock`] on a SINGLE configured
//! ed25519 `unlock_authority` signer — a one-key trust residual. v2 replaces that
//! with an M-of-N ed25519 **oracle key-set**: an unlock must carry a threshold of
//! valid signatures, from DISTINCT configured oracle keys, over the canonical
//! [`crate::attestation::unlock_message_hash`] of the `SolanaUnlockRequest`. See
//! [`crate::attestation`] and the `unlock` processor.
//!
//! ## Fail-closed / NOMAD-LAW
//!
//! [`VaultConfig::unpack`] REJECTS any config whose `oracle_count == 0`,
//! `oracle_threshold == 0`, or `oracle_threshold > oracle_count`. An empty key-set
//! or a zero threshold can therefore never be loaded, so it can never authorize an
//! unlock — an all-zero (uninitialized) account is refused by both the magic byte
//! and the `count == 0` guard.

use crate::error::LockError;

/// A one-byte schema tag so an uninitialized (all-zero) or foreign account is not
/// mistaken for a valid config.
pub const CONFIG_MAGIC: u8 = 0xD9;

/// Schema version. v1 (single `unlock_authority`) is superseded by v2 (oracle set).
/// Bumped so an old-layout account can never be mis-read as a new one.
pub const CONFIG_VERSION: u8 = 2;

/// Maximum size of the oracle key-set (N). Fixed so the account layout is a
/// constant size (fail-closed: no length field an attacker could grow).
pub const MAX_ORACLE_KEYS: usize = 16;

/// Fixed serialized size of [`VaultConfig`].
///   magic(1) ‖ version(1) ‖ mint(32) ‖ vault_token_account(32)
///   ‖ vault_authority_bump(1) ‖ nonce_le(8) ‖ oracle_threshold(1) ‖ oracle_count(1)
///   ‖ oracle_keys(32 * MAX_ORACLE_KEYS)  = 588
pub const CONFIG_LEN: usize = 1 + 1 + 32 + 32 + 1 + 8 + 1 + 1 + 32 * MAX_ORACLE_KEYS;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VaultConfig {
    /// The $DREGG SPL mint this vault mirrors.
    pub mint: [u8; 32],
    /// The SPL token account custodying locked $DREGG (SPL authority = vault-authority PDA).
    pub vault_token_account: [u8; 32],
    /// Bump of the vault-authority PDA (seeds `[b"vault_authority", config]`).
    pub vault_authority_bump: u8,
    /// Monotonic counter; the next lock consumes this value then increments it.
    /// Feeds the per-lock record PDA seed, making each `lock_id` unique.
    pub nonce: u64,
    /// Threshold M: the minimum number of DISTINCT configured oracle keys whose
    /// ed25519 signature over the unlock message hash must be present. `1 <= M <= N`.
    pub oracle_threshold: u8,
    /// N: the number of populated oracle keys (`1 <= N <= MAX_ORACLE_KEYS`).
    pub oracle_count: u8,
    /// The oracle verifying key-set. Exactly `oracle_count` leading entries are
    /// meaningful; the tail is zero-padded and NEVER consulted (see [`Self::oracle_keys_active`]).
    pub oracle_keys: [[u8; 32]; MAX_ORACLE_KEYS],
}

impl VaultConfig {
    /// The active oracle keys (the first `oracle_count`). The zero-padded tail is
    /// excluded, so the all-zero pubkey is never treated as a configured signer.
    pub fn oracle_keys_active(&self) -> &[[u8; 32]] {
        &self.oracle_keys[..self.oracle_count as usize]
    }

    /// Is `key` one of the active configured oracle keys?
    pub fn contains_oracle(&self, key: &[u8; 32]) -> bool {
        self.oracle_keys_active().iter().any(|k| k == key)
    }

    /// Validate the oracle-set invariants (used by InitVault before writing, and by
    /// [`Self::unpack`] after reading). Fail-closed:
    ///   * `1 <= oracle_count <= MAX_ORACLE_KEYS`
    ///   * `1 <= oracle_threshold <= oracle_count`  (NOMAD-LAW: M=0 is refused)
    ///   * no active key is all-zero
    ///   * no duplicate active keys
    pub fn validate_oracle_set(&self) -> Result<(), LockError> {
        let n = self.oracle_count as usize;
        if n == 0 || n > MAX_ORACLE_KEYS {
            return Err(LockError::InvalidOracleSet);
        }
        let m = self.oracle_threshold as usize;
        if m == 0 || m > n {
            return Err(LockError::InvalidOracleSet);
        }
        for (i, k) in self.oracle_keys_active().iter().enumerate() {
            if k == &[0u8; 32] {
                return Err(LockError::InvalidOracleSet);
            }
            // reject a duplicate key inside the active set
            if self.oracle_keys_active()[..i].iter().any(|p| p == k) {
                return Err(LockError::InvalidOracleSet);
            }
        }
        Ok(())
    }

    pub fn pack_into(&self, dst: &mut [u8]) -> Result<(), LockError> {
        if dst.len() != CONFIG_LEN {
            return Err(LockError::AccountState);
        }
        // Never serialize a config that violates the oracle invariants.
        self.validate_oracle_set()?;
        dst[0] = CONFIG_MAGIC;
        dst[1] = CONFIG_VERSION;
        dst[2..34].copy_from_slice(&self.mint);
        dst[34..66].copy_from_slice(&self.vault_token_account);
        dst[66] = self.vault_authority_bump;
        dst[67..75].copy_from_slice(&self.nonce.to_le_bytes());
        dst[75] = self.oracle_threshold;
        dst[76] = self.oracle_count;
        let mut off = 77;
        for key in &self.oracle_keys {
            dst[off..off + 32].copy_from_slice(key);
            off += 32;
        }
        Ok(())
    }

    pub fn unpack(src: &[u8]) -> Result<Self, LockError> {
        if src.len() != CONFIG_LEN {
            return Err(LockError::AccountState);
        }
        if src[0] != CONFIG_MAGIC || src[1] != CONFIG_VERSION {
            return Err(LockError::AccountState);
        }
        let mut mint = [0u8; 32];
        mint.copy_from_slice(&src[2..34]);
        let mut vault_token_account = [0u8; 32];
        vault_token_account.copy_from_slice(&src[34..66]);
        let vault_authority_bump = src[66];
        let mut n = [0u8; 8];
        n.copy_from_slice(&src[67..75]);
        let oracle_threshold = src[75];
        let oracle_count = src[76];
        let mut oracle_keys = [[0u8; 32]; MAX_ORACLE_KEYS];
        let mut off = 77;
        for key in &mut oracle_keys {
            key.copy_from_slice(&src[off..off + 32]);
            off += 32;
        }
        let cfg = Self {
            mint,
            vault_token_account,
            vault_authority_bump,
            nonce: u64::from_le_bytes(n),
            oracle_threshold,
            oracle_count,
            oracle_keys,
        };
        // NOMAD-LAW enforced at load time: a config with an empty key-set or a zero
        // threshold cannot be loaded, hence can never authorize an unlock.
        cfg.validate_oracle_set()?;
        Ok(cfg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(keys: &[[u8; 32]], threshold: u8) -> VaultConfig {
        let mut oracle_keys = [[0u8; 32]; MAX_ORACLE_KEYS];
        for (slot, k) in oracle_keys.iter_mut().zip(keys.iter()) {
            *slot = *k;
        }
        VaultConfig {
            mint: [1u8; 32],
            vault_token_account: [3u8; 32],
            vault_authority_bump: 254,
            nonce: 0x0102_0304_0506_0708,
            oracle_threshold: threshold,
            oracle_count: keys.len() as u8,
            oracle_keys,
        }
    }

    #[test]
    fn config_roundtrip() {
        let c = sample(&[[10u8; 32], [11u8; 32], [12u8; 32]], 2);
        let mut buf = [0u8; CONFIG_LEN];
        c.pack_into(&mut buf).unwrap();
        assert_eq!(buf[0], CONFIG_MAGIC);
        assert_eq!(buf[1], CONFIG_VERSION);
        assert_eq!(VaultConfig::unpack(&buf).unwrap(), c);
    }

    #[test]
    fn unpack_rejects_bad_magic() {
        let buf = [0u8; CONFIG_LEN]; // magic byte 0, not CONFIG_MAGIC
        assert_eq!(VaultConfig::unpack(&buf), Err(LockError::AccountState));
    }

    #[test]
    fn unpack_rejects_wrong_version() {
        let mut buf = [0u8; CONFIG_LEN];
        buf[0] = CONFIG_MAGIC;
        buf[1] = 1; // old version
        assert_eq!(VaultConfig::unpack(&buf), Err(LockError::AccountState));
    }

    #[test]
    fn unpack_rejects_wrong_len() {
        assert_eq!(
            VaultConfig::unpack(&[CONFIG_MAGIC; CONFIG_LEN - 1]),
            Err(LockError::AccountState)
        );
    }

    /// NOMAD-LAW: a well-formed config header but with threshold 0 must not load.
    #[test]
    fn unpack_rejects_zero_threshold() {
        let c = sample(&[[10u8; 32], [11u8; 32]], 2);
        let mut buf = [0u8; CONFIG_LEN];
        c.pack_into(&mut buf).unwrap();
        buf[75] = 0; // force threshold = 0 on the wire
        assert_eq!(VaultConfig::unpack(&buf), Err(LockError::InvalidOracleSet));
    }

    /// NOMAD-LAW: an empty key-set (count 0) must not load.
    #[test]
    fn unpack_rejects_empty_key_set() {
        let c = sample(&[[10u8; 32], [11u8; 32]], 2);
        let mut buf = [0u8; CONFIG_LEN];
        c.pack_into(&mut buf).unwrap();
        buf[76] = 0; // force count = 0
        assert_eq!(VaultConfig::unpack(&buf), Err(LockError::InvalidOracleSet));
    }

    #[test]
    fn unpack_rejects_threshold_gt_count() {
        let c = sample(&[[10u8; 32], [11u8; 32]], 2);
        let mut buf = [0u8; CONFIG_LEN];
        c.pack_into(&mut buf).unwrap();
        buf[75] = 3; // M = 3 > N = 2
        assert_eq!(VaultConfig::unpack(&buf), Err(LockError::InvalidOracleSet));
    }

    #[test]
    fn validate_rejects_zero_key_in_active_set() {
        let c = sample(&[[10u8; 32], [0u8; 32]], 2);
        assert_eq!(c.validate_oracle_set(), Err(LockError::InvalidOracleSet));
    }

    #[test]
    fn validate_rejects_duplicate_key() {
        let c = sample(&[[10u8; 32], [10u8; 32]], 2);
        assert_eq!(c.validate_oracle_set(), Err(LockError::InvalidOracleSet));
    }

    #[test]
    fn contains_oracle_ignores_padding() {
        let c = sample(&[[10u8; 32], [11u8; 32]], 2);
        assert!(c.contains_oracle(&[10u8; 32]));
        assert!(c.contains_oracle(&[11u8; 32]));
        // the zero-padded tail is never a member
        assert!(!c.contains_oracle(&[0u8; 32]));
        assert!(!c.contains_oracle(&[12u8; 32]));
    }
}
