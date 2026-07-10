//! mldsa_live_sign.rs — the RUNNING-BINARY gate for the ML-DSA-65 SIGN side of "the crate leaves the
//! LIVE TCB", written HONESTLY about what is real today.
//!
//! ## What is real vs. what is the follow-up (read this before trusting a green)
//!
//! The VERIFY side is done and deployed: BRICK 8's FULL-BYTE `MlDsaVerifyReal.verifyCore` is the authority
//! behind the deployed `dregg_pq::ml_dsa_verify` (see `mldsa_live_verify.rs`), so the `fips204` crate has
//! left the node's VERIFY TCB.
//!
//! The SIGN side has NOT reached that bar. The only extracted sign object that exists today is the SCALAR
//! (n=1) `Dregg2.Crypto.Fips204Verify.signCore` — a `"s1 s2 t0 μ y"` → `"c̃ z h"` / `"REJECT"`
//! Fiat–Shamir-with-aborts object, `@[export]`ed as `dregg_fips204_sign`. There is NO full-byte sign core
//! (no `install_lean_sign_core_real`, no `dregg_fips204_sign_real`, no `shadow_fips204_sign_real`), and the
//! DEPLOYED byte-level signer `dregg_pq::MlDsaKey::sign` produces its 3309-byte signature by calling the
//! `fips204` crate directly — it does NOT consult any Lean sign core. So **the `fips204` crate has NOT left
//! the node's SIGN TCB.** The real, full-byte sign core is the named follow-up: the same 8-brick real build
//! the verify side got (SHAKE / negacyclic ring / samplers are already bricks — reuse them; sign adds
//! MakeHint and the rejection loop over the real 1952/4032/3309-byte codec).
//!
//! This gate therefore proves exactly two things, and claims nothing more:
//!
//!   (A) POSITIVE — the extracted, verified SCALAR sign object runs LIVE in the deployed binary. Driving
//!       the EXACT production install (`dregg_node::install_mldsa_verified_sign_core()`) wires
//!       `Fips204Verify.signCore` behind `dregg_pq::ml_dsa_sign_core`; an honest sample SIGNS to the
//!       accepted wire and that signature ROUND-TRIPS through the extracted (scalar) `verifyCore` — both
//!       verdicts computed by the leanc-native Lean objects, the `fips204` crate consulted for neither. A
//!       rejected sample is honestly `Some(None)` (resample), never a faked accept.
//!
//!   (B) HONEST RESIDUAL — the DEPLOYED byte-level sign path is still crate-signed. `MlDsaKey::sign`
//!       produces a real 3309-byte signature via the `fips204` crate; that signature is ACCEPTED by the
//!       Lean-verified REAL verify core (verify left the TCB) but was PRODUCED by the crate, not by any
//!       Lean sign object — the scalar core operates on 5-int wires, a different dimension entirely. This
//!       test asserts that residual out loud so a green here can never be mistaken for "sign left the TCB".

use dregg_node::{
    MlDsaSignCoreInstall, MlDsaVerifyCoreInstall, install_mldsa_verified_sign_core,
    install_mldsa_verified_verify_core,
};

/// Drive the EXACT production sign-core install and fail loudly if the linked archive lacks the export
/// (a green must mean the verified sign object actually ran live on this build, never a vacuous skip).
fn install_sign_core_or_panic() {
    match install_mldsa_verified_sign_core() {
        MlDsaSignCoreInstall::Installed | MlDsaSignCoreInstall::AlreadyInstalled => {}
        MlDsaSignCoreInstall::ExportAbsent => panic!(
            "BLOCKER: the Lean archive linked into this test binary does NOT export `dregg_fips204_sign` \
             (`fips204_sign_core_available()` is false), so the verified SCALAR sign core cannot be \
             installed and `ml_dsa_sign_core` would return None. Rebuild dregg-lean-ffi against a \
             HEAD-matching archive that lake-builds `Dregg2.Crypto.Fips204Verify`, then re-run."
        ),
    }
}

/// (A) The extracted, verified SCALAR sign core runs live and its output round-trips through the extracted
/// (scalar) verify core — both verdicts from the Lean objects, the `fips204` crate consulted for neither.
#[test]
fn verified_scalar_sign_core_runs_live_and_roundtrips() {
    install_sign_core_or_panic();
    assert!(
        dregg_pq::lean_sign_core_installed(),
        "after install, the Lean-verified (scalar) sign core must be installed behind ml_dsa_sign_core"
    );

    // Honest sample: secret (s1,s2,t0)=(5,1,3), message μ=7, mask y=40 → accepted signature (c̃,z,h)=(7,45,0).
    // This routes through the LIVE Lean archive (`shadow_fips204_sign` over the leanc-native `signCore`).
    let sig_wire = dregg_pq::ml_dsa_sign_core("5 1 3 7 40")
        .expect("sign core installed ⇒ Some(_)")
        .expect("honest sample ⇒ an accepted signature, not REJECT");
    assert_eq!(
        sig_wire, "7 45 0",
        "the live Lean signCore emits the accepted signature wire for the honest sample"
    );

    // ROUND-TRIP through the extracted (scalar) verifyCore, ALSO run live via the Lean archive. The public
    // key thi = s1 + s2 − t0 = 5 + 1 − 3 = 3; prefix the signature with `thi μ` = `3 7`.
    let verify_wire = format!("3 7 {sig_wire}");
    let lean_verdict = dregg_lean_ffi::shadow_fips204_verify(&verify_wire)
        .expect("the linked archive exports the (scalar) verify core");
    assert_eq!(
        lean_verdict, "1",
        "the extracted signCore output ACCEPTS through the extracted verifyCore — the verified \
         sign→verify round-trip runs live, the fips204 crate consulted for neither direction"
    );

    // A sample the rejection gate fails is honestly Some(None) (resample) — NOT a faked accept.
    assert_eq!(
        dregg_pq::ml_dsa_sign_core("5 1 3 7 261888"),
        Some(None),
        "a bad-mask sample (lowGap fails) is honestly rejected (retry), via the live Lean core"
    );
    assert_eq!(
        dregg_pq::ml_dsa_sign_core("5 1 3 7 1000000"),
        Some(None),
        "an out-of-norm response is honestly rejected (retry), via the live Lean core"
    );
    assert_eq!(
        dregg_pq::ml_dsa_sign_core("garbage"),
        Some(None),
        "a malformed sign wire fails closed (never a spurious signature)"
    );

    eprintln!(
        "PROVED (A): the extracted verified SCALAR sign core (`Fips204Verify.signCore`) runs LIVE in the \
         deployed binary; an honest sample signs and round-trips through the extracted verifyCore, and bad \
         samples honestly reject. This is the n=1 model — NOT the deployed byte-level signer."
    );
}

/// (B) The HONEST RESIDUAL: the deployed byte-level sign is still crate-signed. `MlDsaKey::sign` produces a
/// real 3309-byte signature via the `fips204` crate — accepted by the Lean-verified REAL verify core, but
/// PRODUCED by the crate, not by any Lean sign object. The crate has NOT left the node's SIGN TCB.
#[test]
fn deployed_byte_sign_is_still_crate_signed_named_residual() {
    // Install BOTH the real verify core (so we can show verify is Lean-backed) and the scalar sign core.
    match install_mldsa_verified_verify_core() {
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled => {}
        MlDsaVerifyCoreInstall::ExportAbsent => panic!(
            "BLOCKER: archive lacks `dregg_fips204_verify_real`; rebuild against a HEAD-matching archive."
        ),
    }
    install_sign_core_or_panic();

    // The DEPLOYED byte-level signer: `MlDsaKey::sign` → `fips204` crate → a real 3309-byte signature.
    let key = dregg_pq::MlDsaKey::from_ed25519_seed(&[3u8; 32]);
    let ctx: &[u8] = b"dregg-node-live-sign-ctx-v1";
    let msg: &[u8] = b"the deployed byte-level ML-DSA sign is still produced by the fips204 crate";
    let sig = key.sign(ctx, msg);
    assert_eq!(
        sig.len(),
        dregg_pq::ML_DSA_SIG_LEN,
        "the deployed signer emits a real full-byte ML-DSA-65 signature (3309 bytes)"
    );

    // That crate-produced signature IS accepted by the Lean-verified REAL verify core (verify has left the
    // TCB) — but nothing about producing it went through Lean.
    assert!(
        dregg_pq::ml_dsa_verify(&key.public_bytes(), ctx, msg, &sig),
        "the crate-produced signature is accepted by the deployed Lean-routed verify"
    );

    // The residual, made concrete: the extracted sign object is the SCALAR model — its input/output live in
    // a 5-int / 3-int world, not the 3309-byte world the deployed signer produces. There is no full-byte
    // sign core to route `MlDsaKey::sign` through, so the crate remains the byte-level sign authority.
    let scalar_sig = dregg_pq::ml_dsa_sign_core("5 1 3 7 40")
        .expect("scalar sign core installed")
        .expect("honest sample accepts");
    assert_eq!(
        scalar_sig, "7 45 0",
        "the only extracted sign object emits a 3-int scalar wire — not the 3309-byte signature the \
         deployed `MlDsaKey::sign` produces; there is NO full-byte sign core to route the deployed \
         signer through"
    );
    assert!(
        scalar_sig.len() < dregg_pq::ML_DSA_SIG_LEN,
        "dimension gap: the scalar sign wire is orders smaller than a real ML-DSA-65 signature"
    );

    eprintln!(
        "RESIDUAL (B): the deployed byte-level `MlDsaKey::sign` is STILL produced by the `fips204` crate \
         (a real 3309-byte signature, Lean-VERIFIED but crate-SIGNED). The only extracted sign object is \
         the n=1 scalar `signCore`. The crate has NOT left the node's SIGN TCB — the real full-byte sign \
         core (same 8-brick build as verify, adding MakeHint + rejection loop) is the follow-up."
    );
}
