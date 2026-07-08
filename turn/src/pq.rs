//! Post-quantum (ML-DSA-65, FIPS 204) half of the HYBRID turn-authorization
//! perimeter — end-to-end quantum-safety for user/agent TURNS, not just
//! consensus finality.
//!
//! The classical ed25519 signature and this ML-DSA signature cover the SAME
//! canonical message — [`crate::executor::TurnExecutor::compute_signing_message`]
//! for an inner action ([`crate::action::Authorization::HybridSignature`]), and
//! `Turn::hash()` for the outer envelope (`dregg_sdk::SignedTurn`). A hybrid
//! authorization verifies only when BOTH halves check (`classical ∧ pq`), so
//! forging a turn requires breaking ed25519 discrete-log AND module-lattice
//! SIS/LWE simultaneously.
//!
//! ## Deterministic derivation
//!
//! The ML-DSA key is derived DETERMINISTICALLY from the same 32-byte ed25519
//! seed the classical identity uses ([`MlDsaTurnKey::from_ed25519_seed`], FIPS
//! 204 `ML-DSA.KeyGen(ξ = seed)`), so a cipherclerk, a node, and a genesis
//! fixture built from one mnemonic all agree on the PQ public key with no
//! separate ceremony. The verifier cannot derive another party's PQ *public*
//! key from their ed25519 *public* key, so the ML-DSA public key is carried in
//! the hybrid envelope — self-contained during the staged rollout, exactly as
//! the consensus HybridPq quorum carries its per-signer keys.
//!
//! ## Staged, fail-closed
//!
//! The client always signs both halves. The verifier checks the PQ half when
//! present and REJECTS a present-but-invalid PQ half (fail-CLOSED) even before
//! the PQ half is mandatory. Whether the PQ half is *required* is gated by
//! `TurnExecutor::require_pq` (default off), matching the consensus HybridPq
//! default-off rollout.

use fips204::ml_dsa_65;
use fips204::traits::{KeyGen as _, SerDes as _, Signer as _, Verifier as _};

/// Domain-separation context for the ML-DSA half of a HYBRID *turn*
/// authorization (FIPS 204 `ctx`, bound into every signature). Distinct from
/// the consensus quorum context (`dregg-hybrid-qc-v1`) so a turn-path PQ
/// signature can never be replayed as a quorum-certificate half, and vice
/// versa. Signer and verifier MUST agree on it.
pub const HYBRID_TURN_PQ_CTX: &[u8] = b"dregg-hybrid-turn-v1";

/// Serialized length of an ML-DSA-65 public key (FIPS 204 = 1952 bytes).
pub const ML_DSA_PK_LEN: usize = ml_dsa_65::PK_LEN;

/// Serialized length of an ML-DSA-65 signature (FIPS 204).
pub const ML_DSA_SIG_LEN: usize = ml_dsa_65::SIG_LEN;

/// The PQ half of a hybrid identity: an ML-DSA-65 signing key plus its
/// serialized public key. Held alongside the classical `ed25519_dalek::SigningKey`
/// and derived from the SAME seed.
#[derive(Clone)]
pub struct MlDsaTurnKey {
    secret: ml_dsa_65::PrivateKey,
    public_bytes: [u8; ml_dsa_65::PK_LEN],
}

impl core::fmt::Debug for MlDsaTurnKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MlDsaTurnKey(..)")
    }
}

impl MlDsaTurnKey {
    /// Derive the ML-DSA-65 keypair DETERMINISTICALLY from a 32-byte ed25519
    /// seed (`ML-DSA.KeyGen` from `ξ = seed`). Same seed → same PQ key, so the
    /// PQ public key matches across cipherclerk / node / genesis without a
    /// separate ceremony.
    pub fn from_ed25519_seed(seed: &[u8; 32]) -> Self {
        let (pk, sk) = ml_dsa_65::KG::keygen_from_seed(seed);
        Self {
            secret: sk,
            public_bytes: pk.into_bytes(),
        }
    }

    /// The serialized ML-DSA-65 public key (carried in the hybrid envelope so
    /// the verifier is self-contained during the staged rollout).
    pub fn public_bytes(&self) -> Vec<u8> {
        self.public_bytes.to_vec()
    }

    /// Sign `message` under [`HYBRID_TURN_PQ_CTX`] (hedged from OS entropy).
    /// `None` only on the vanishingly rare internal RNG failure.
    pub fn sign(&self, message: &[u8]) -> Option<Vec<u8>> {
        self.secret
            .try_sign(message, HYBRID_TURN_PQ_CTX)
            .ok()
            .map(|s| s.to_vec())
    }
}

/// Verify an ML-DSA-65 signature over `message` under [`HYBRID_TURN_PQ_CTX`].
///
/// Returns `false` — never a panic — on a wrong-length public key, a
/// wrong-length signature, an undecodable key, or a failed cryptographic check.
/// This is the fail-CLOSED primitive: a present-but-invalid PQ half must make
/// the whole hybrid authorization reject, regardless of `require_pq`.
pub fn ml_dsa_verify(public_bytes: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
    let Ok(pk_arr) = <[u8; ml_dsa_65::PK_LEN]>::try_from(public_bytes) else {
        return false;
    };
    let Ok(sig) = <[u8; ml_dsa_65::SIG_LEN]>::try_from(sig_bytes) else {
        return false;
    };
    let Ok(vk) = ml_dsa_65::PublicKey::try_from_bytes(pk_arr) else {
        return false;
    };
    vk.verify(message, &sig, HYBRID_TURN_PQ_CTX)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_derivation_same_seed_same_key() {
        let seed = [7u8; 32];
        let a = MlDsaTurnKey::from_ed25519_seed(&seed);
        let b = MlDsaTurnKey::from_ed25519_seed(&seed);
        assert_eq!(a.public_bytes(), b.public_bytes());
        assert_eq!(a.public_bytes().len(), ML_DSA_PK_LEN);
    }

    #[test]
    fn sign_then_verify_roundtrips() {
        let key = MlDsaTurnKey::from_ed25519_seed(&[3u8; 32]);
        let msg = b"the same canonical signing message both halves cover";
        let sig = key.sign(msg).expect("ml-dsa sign");
        assert!(ml_dsa_verify(&key.public_bytes(), msg, &sig));
    }

    #[test]
    fn forged_signature_rejected_fail_closed() {
        let key = MlDsaTurnKey::from_ed25519_seed(&[3u8; 32]);
        let msg = b"canonical message";
        let mut sig = key.sign(msg).expect("ml-dsa sign");
        // Flip one byte: a present-but-invalid PQ half must fail closed.
        sig[0] ^= 0xff;
        assert!(!ml_dsa_verify(&key.public_bytes(), msg, &sig));
        // Wrong message under a valid signature also rejects.
        let good = key.sign(msg).unwrap();
        assert!(!ml_dsa_verify(
            &key.public_bytes(),
            b"different message",
            &good
        ));
        // Empty / malformed inputs reject rather than panic.
        assert!(!ml_dsa_verify(&[], msg, &good));
        assert!(!ml_dsa_verify(&key.public_bytes(), msg, &[]));
    }
}
