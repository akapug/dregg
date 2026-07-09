//! Integration test for `AppCipherclerk::sign_action`.
//!
//! Lives in `tests/` (not `src/`) because the `no_unchecked.rs` grep
//! guard fences off `Authorization::Unchecked` anywhere under `src/` —
//! including inside `#[cfg(test)]` modules. This test deliberately
//! starts from an `Unchecked` action and verifies that `sign_action`
//! replaces the authorization with a real signature.

use dregg_app_framework::{
    Action, AgentCipherclerk, AppCipherclerk, Authorization, CellId, DelegationMode, symbol,
};

#[test]
fn sign_action_overwrites_unchecked() {
    let sdk = AgentCipherclerk::new();
    let cclerk = AppCipherclerk::new(sdk, [0u8; 32]);
    let target = CellId::from_bytes([1u8; 32]);

    // Start from a builder-built action with Unchecked authorization.
    let unsigned = Action {
        target,
        method: symbol("noop"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    let signed = cclerk.sign_action(unsigned);
    // Since the hybrid flip, sign_action emits HybridSignature (ed25519 +
    // ML-DSA over the same canonical message).
    assert!(matches!(
        signed.authorization,
        Authorization::HybridSignature { .. }
    ));

    // And it's a real non-zero signature carrying the PQ half.
    if let Authorization::HybridSignature {
        ed25519, ml_dsa, ..
    } = signed.authorization
    {
        assert!(ed25519 != [0u8; 64], "ed25519 half must be non-zero");
        assert!(!ml_dsa.is_empty(), "PQ half must be present");
    }
}
