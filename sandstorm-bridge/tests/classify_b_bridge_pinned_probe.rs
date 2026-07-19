//! LANE classify-B — reachability PROOF for `sandstorm-bridge/src/bridge.rs`'s
//! `RootAttestation::verify` cofactored ed25519 leg. Proof-by-EXECUTION.
//!
//! CLASSIFICATION: this is a FIRST-PARTY dregg grain-serve attestation (the grain
//! OWNER signs `(grain_cell_id ‖ data_root)`), NOT a Bitcoin/BIP-340 (Schnorr)
//! external-scheme mirror — the brief's "MAY be an external mirror" resolves to
//! NO. The verifying key is `expected_owner`, supplied by the CALLER from an
//! INDEPENDENT channel (the ledger/federation), never from the wire attestation.
//! `verify` uses `expected_owner` as the verifying key and only uses the
//! wire-carried `self.signer` as an EQUALITY GUARD (`self.signer == expected_owner`).
//! So an attacker cannot substitute a small-order VERIFYING key — the cofactored
//! vs strict distinction is INERT here. VERDICT: PINNED-KEY (defense-in-depth).
//!
//! Run: `cargo test -p sandstorm-bridge --test classify_b_bridge_pinned_probe`

use ed25519_dalek::SigningKey;
use sandstorm_bridge::{DataRoot, RootAttestation};

/// The identity-point small-order ed25519 encoding — a no-secret forgery key.
const SMALL_ORDER: [u8; 32] = [
    0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,
];

fn root() -> DataRoot {
    DataRoot::from_root_bytes([7u8; 32])
}

/// The honest owner attestation verifies under the owner's key (positive control).
#[test]
fn honest_owner_attestation_verifies() {
    let owner = SigningKey::from_bytes(&[3u8; 32]);
    let att = RootAttestation::sign(&owner, "cell:grain-a", &root());
    assert!(att.verify(&owner.verifying_key()));
}

/// The verifying key is PINNED to the caller-supplied `expected_owner`: a wire
/// attestation that declares a SMALL-ORDER `signer` (the substitution a
/// cofactored-verify attack needs) is rejected outright, because verify checks
/// `self.signer == expected_owner` and the ledger owner key is not small-order.
#[test]
fn a_small_order_signer_substitution_is_rejected() {
    let owner = SigningKey::from_bytes(&[3u8; 32]);
    // Attacker forges an attestation claiming a small-order signer + the classic
    // no-secret sig (R = small-order point, s = 0).
    let mut sig = vec![0u8; 64];
    sig[..32].copy_from_slice(&SMALL_ORDER);
    let forged = RootAttestation {
        grain_cell_id: "cell:grain-a".to_string(),
        data_root: root(),
        signer: SMALL_ORDER,
        signature: sig,
    };
    // Against the real ledger owner key: rejected at the signer-equality guard —
    // the small-order verifying key never even reaches the ed25519 verify.
    assert!(
        !forged.verify(&owner.verifying_key()),
        "a wire-declared small-order signer must not authenticate against the pinned owner key"
    );
    // Even if the attacker declares self.signer == the real owner key, they cannot
    // produce a valid sig without the owner secret, and the verifying key is the
    // real (non-small-order) owner key, so the cofactored leg rejects the forgery.
    let mut sig2 = vec![0u8; 64];
    sig2[..32].copy_from_slice(&owner.verifying_key().to_bytes());
    let forged2 = RootAttestation {
        grain_cell_id: "cell:grain-a".to_string(),
        data_root: root(),
        signer: owner.verifying_key().to_bytes(),
        signature: sig2,
    };
    assert!(
        !forged2.verify(&owner.verifying_key()),
        "no-secret sig against the pinned (non-small-order) owner key must be rejected"
    );
}
