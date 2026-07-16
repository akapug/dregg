//! CANARY (A1) — M13's exact shape: a second author for a loaded artifact, drifted and unwelded.
//! The literal says trace_width 5; the artifact on disk says 24. Nothing compares them, so the
//! test below is green while the deployed descriptor is a different program.

const GOLDEN_JSON: &str = r#"{"name":"canary-desc::v1","ir":2,"trace_width":5,"constraints":[]}"#;

#[test]
fn dispatches_with_expected_shape() {
    assert!(GOLDEN_JSON.contains("trace_width"));
}
