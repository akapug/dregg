//! Lazy PQ route registration must inspect linked exports without initializing Lean.
//!
//! This is an isolated test binary so no sibling test can initialize the process-global runtime
//! before the structural assertions. Registration installs the same six function pointers the SDK
//! installs from `AgentRuntime::new`; the first actual Lean call then proves the existing one-shot
//! initializer and known-answer path still run.

#![cfg(feature = "lean-lib")]

use dregg_pq::{
    MlDsaKeygenCoreRealInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
    MlKemDecapsCoreInstall, MlKemEncapsCoreInstall, MlKemKeygenCoreInstall,
};

#[test]
fn pq_route_discovery_is_lazy_but_first_real_call_initializes() {
    assert_eq!(
        dregg_lean_ffi::lean_runtime_init_status(),
        None,
        "an isolated process must begin before the default Lean initializer"
    );

    let verify = dregg_pq::install_verified_mldsa_verify_core(
        dregg_lean_ffi::fips204_verify_real_export_present,
        |wire| dregg_lean_ffi::shadow_fips204_verify_real(wire).ok(),
    );
    let sign = dregg_pq::install_verified_mldsa_sign_core_real(
        dregg_lean_ffi::fips204_sign_real_export_present,
        |wire| dregg_lean_ffi::shadow_fips204_sign_real(wire).ok(),
    );
    let mldsa_keygen = dregg_pq::install_verified_mldsa_keygen_core_real(
        dregg_lean_ffi::mldsa_keygen_real_export_present,
        |wire| dregg_lean_ffi::shadow_mldsa_keygen_real(wire).ok(),
    );
    let encaps = dregg_pq::install_verified_mlkem_encaps_core(
        dregg_lean_ffi::mlkem_encaps_real_export_present,
        |wire| dregg_lean_ffi::shadow_mlkem_encaps_real(wire).ok(),
    );
    let decaps = dregg_pq::install_verified_mlkem_decaps_core(
        dregg_lean_ffi::mlkem_decaps_real_export_present,
        |wire| dregg_lean_ffi::shadow_mlkem_decaps_real(wire).ok(),
    );
    let mlkem_keygen = dregg_pq::install_verified_mlkem_keygen_core(
        dregg_lean_ffi::mlkem_keygen_real_export_present,
        |wire| dregg_lean_ffi::shadow_mlkem_keygen_real(wire).ok(),
    );

    assert_eq!(verify, MlDsaVerifyCoreInstall::Installed);
    assert_eq!(sign, MlDsaSignCoreRealInstall::Installed);
    assert_eq!(mldsa_keygen, MlDsaKeygenCoreRealInstall::Installed);
    assert_eq!(encaps, MlKemEncapsCoreInstall::Installed);
    assert_eq!(decaps, MlKemDecapsCoreInstall::Installed);
    assert_eq!(mlkem_keygen, MlKemKeygenCoreInstall::Installed);

    assert_eq!(
        dregg_lean_ffi::lean_runtime_init_status(),
        None,
        "symbol discovery and six route installs must not initialize Lean"
    );

    // NIST ACVP ML-DSA-65 keygen vector kg26, shared with
    // `mldsa_keygen_dispatch`: this public API can only succeed through the
    // full-byte keygen callback installed above. The digest commits all 1952
    // expected public-key bytes without duplicating the large vector here.
    let xi26 = [
        0xa9, 0x91, 0xfd, 0x42, 0xb0, 0x71, 0xd4, 0x9c, 0x48, 0xae, 0x3e, 0x75, 0xc6, 0x47, 0x45,
        0x9e, 0x0d, 0xaa, 0xd1, 0xe1, 0xba, 0x35, 0x6a, 0x04, 0x80, 0x19, 0x12, 0xd3, 0x29, 0x4b,
        0xcf, 0xf8,
    ];
    let key = dregg_pq::MlDsaKey::from_ed25519_seed(&xi26);
    assert_eq!(key.public_bytes().len(), dregg_pq::ML_DSA_PK_LEN);
    assert_eq!(
        blake3::hash(&key.public_bytes()).to_hex().as_str(),
        "def581b81977c7f6ff10ebe0ab358bf78b6a86850087ef0b30274086b8ae0c77",
        "installed verified keygen route did not produce NIST ACVP kg26"
    );
    assert!(matches!(
        dregg_lean_ffi::lean_runtime_init_status(),
        Some(Ok(()))
    ));
}
