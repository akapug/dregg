//! CANARY (A2) — `presentation_descriptor_witness.rs:179`'s shape: the "golden" is defined AS the
//! artifact the production loader reads, so the assertion below compares the file to itself and
//! holds no matter how corrupt the file is.

const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/canary.json");

#[test]
fn dispatch_serves_the_byte_pinned_golden() {
    assert_eq!(
        canary_circuit::descriptor_by_name("x").unwrap(),
        GOLDEN_JSON
    );
}
