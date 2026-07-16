//! The compliant exemplar (mirrors the real `turn_chain_emit_gate.rs`): the Lean-pinned literal is
//! asserted byte-equal to the checked-in artifact, so the two CANNOT silently diverge.

const GOLDEN_JSON: &str = r#"{"name":"canary-desc::v1","ir":2,"trace_width":24,"constraints":[]}"#;

#[test]
fn lean_bytes_equal_the_checked_in_artifact() {
    let checked_in = include_str!("../../circuit/descriptors/by-name/canary.json");
    assert_eq!(GOLDEN_JSON, checked_in.strip_suffix('\n').unwrap());
}
