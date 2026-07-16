//! A deliberately low-resolution stand-in, LABELED as such and off the live path. This is the
//! iterative/approximative method working correctly, and the gates must leave it alone — a gate
//! that punishes a labeled placeholder is a gate that gets deleted.

/// A toy descriptor for the shape tests. Mirrors `canary_circuit::descriptor_by_name`.
// mirror-gate: allow(D1) — deliberate low-resolution stand-in; the real weld lands in the
// descriptor-transport lane. Off every live path: nothing outside this test constructs it.
fn toy_descriptor() -> String {
    "{}".to_string()
}

#[test]
fn toy_shape() {
    assert_eq!(toy_descriptor(), "{}");
}
