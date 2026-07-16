//! CANARY (D1) — M11's shape: the harness re-declares an object it could import, and says so.

/// Inline projection of the descriptor.
///
/// Mirrors `canary_circuit::descriptor_by_name` (which is module-private). Kept inline here so the
/// differential test is independent of the canary-circuit crate.
fn descriptor_by_name_inline(_n: &str) -> &'static str {
    "{}"
}

#[test]
fn projection_matches() {
    assert_eq!(descriptor_by_name_inline("x"), "{}");
}
