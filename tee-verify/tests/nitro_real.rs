//! Verify the REAL AWS Nitro attestation document captured end-to-end from a live
//! enclave (us-east-1, c5.xlarge, debug-mode) whose app bound `user_data = [0xAB; 32]`.

use dregg_tee_verify::verify_nitro_core;

const REAL_DOC: &[u8] = include_bytes!("data/nitro_att.bin");

#[test]
fn verifies_real_live_nitro_doc_and_extracts_bound_report_data() {
    let (claims, ts_ms) = verify_nitro_core(REAL_DOC)
        .expect("the real Nitro doc must verify: COSE sig + chain to the pinned AWS root");

    // The enclave app bound exactly this commitment into user_data.
    assert_eq!(
        claims.report_data, [0xABu8; 32],
        "report_data must equal the commitment the enclave bound"
    );
    assert!(claims.tcb_ok);
    assert!(ts_ms > 1_700_000_000_000, "doc timestamp looks real (ms)");
    println!(
        "OK real Nitro doc: measurement={} report_data={} ts_ms={}",
        hex::encode(claims.measurement),
        hex::encode(claims.report_data),
        ts_ms
    );
}

#[test]
fn tampering_the_signed_bytes_is_rejected() {
    // Flip a byte in the middle of the payload region -> COSE sig (or parse) must fail.
    let mut doc = REAL_DOC.to_vec();
    let mid = doc.len() / 2;
    doc[mid] ^= 0xFF;
    assert!(
        verify_nitro_core(&doc).is_err(),
        "a tampered doc must not verify"
    );
}

#[test]
fn a_truncated_doc_is_rejected() {
    assert!(verify_nitro_core(&REAL_DOC[..REAL_DOC.len() / 2]).is_err());
}
