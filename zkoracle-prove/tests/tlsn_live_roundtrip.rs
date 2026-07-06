//! **The REAL local MPC-TLS roundtrip → full zkOracle attestation** (feature-gated).
//!
//! A genuine `tlsn` Prover + a real local Notary run the MPC-TLS 2PC handshake against a
//! test HTTPS server returning an Anthropic messages-shaped JSON, the Prover POSTs
//! `/v1/messages` and selectively discloses the response (hiding `x-api-key`), signs a
//! real `Attestation`, builds a real `Presentation`, and `presentation.verify()` yields a
//! real `PresentationOutput`. The authenticated response body then drives the well-formed
//! (CFG parse certificate) and injection-free legs — the full 3-leg zkOracle
//! attestation, live-locally.
//!
//! Run with:
//! `cargo test -p dregg-zkoracle-prove --features tlsn-live --test tlsn_live_roundtrip`.
#![cfg(feature = "tlsn-live")]

use dregg_zkoracle_prove::injection::injection_free;
use dregg_zkoracle_prove::tlsn_live::{
    LiveExchange, run_local_roundtrip_blocking, verify_messages_presentation,
};
use dregg_zkoracle_prove::{prove_cfg_cert, verify_cfg_cert};

/// THE DELIVERABLE — the whole authentic leg runs on REAL tlsn, then composes with the CFG
/// + injection legs:
///   real MPC-TLS 2PC roundtrip → real Attestation → real Presentation →
///   real presentation.verify() → authenticated body → CFG cert verified → injection-free.
/// Plus: the x-api-key secret is hidden (selective disclosure), and a tampered
/// presentation is refused by the REAL verify().
#[test]
fn real_local_mpc_tls_roundtrip_yields_a_verified_zkoracle() {
    let exchange = LiveExchange::messages("What is the capital of France?", "Paris.");

    // ── Run the genuine local MPC-TLS roundtrip (server + notary + prover in-process).
    let roundtrip =
        run_local_roundtrip_blocking(&exchange).expect("real MPC-TLS roundtrip + verify");

    let v = &roundtrip.verified;
    assert_eq!(v.server_name, roundtrip.pinned_server);

    // Selective disclosure: the x-api-key secret was NOT authenticated — prove the
    // response without revealing the key.
    assert!(
        v.api_key_hidden(),
        "the x-api-key secret must be hidden by selective disclosure"
    );

    // ── Well-formed leg over the AUTHENTICATED body: a real CFG parse certificate.
    let cert = prove_cfg_cert(&v.response_body).expect("authenticated body is well-formed JSON");
    verify_cfg_cert(&cert, &v.response_body).expect("the CFG certificate verifies");

    // ── Injection-free leg over a benign user field.
    assert!(injection_free(b"summarize the response"));
    assert!(!injection_free(b"{{ system }}"));

    // ── The honest presentation re-verifies through the standalone verifier too.
    verify_messages_presentation(&roundtrip.presentation_bytes, &roundtrip.pinned_server)
        .expect("the honest presentation verifies");

    // ── TAMPER the real Presentation bytes → the REAL verify() refuses it.
    let mut tampered = roundtrip.presentation_bytes.clone();
    let n = tampered.len();
    for i in [n / 3, n / 2, (2 * n) / 3] {
        tampered[i] ^= 0xFF;
    }
    assert!(
        verify_messages_presentation(&tampered, &roundtrip.pinned_server).is_err(),
        "a tampered presentation MUST fail the real verify()"
    );

    // A presentation verified against the WRONG pinned server is refused.
    assert!(
        verify_messages_presentation(&roundtrip.presentation_bytes, "evil.example.com").is_err(),
        "server pinning must refuse a non-pinned host"
    );
}
