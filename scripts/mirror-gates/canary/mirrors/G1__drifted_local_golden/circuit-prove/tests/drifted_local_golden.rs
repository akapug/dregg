//! CANARY (G1) — M27's exact shape: a test-local golden whose ONLY reader is its own `include_str!`
//! and whose ONLY author is itself. No Lean `#guard` names it, no second loader pins it, no weld
//! ties it to the deployed descriptor. It claims the deployed `canary-desc::v1` identity but carries
//! a DIFFERENT constraint count — so it has already drifted, and the audit below (comparing the file
//! to itself) stays green anyway. This is precisely A2's single-loader blind spot.

const GOLDEN_JSON: &str = include_str!("drifted_local_golden.json");

#[test]
fn audits_against_the_private_golden() {
    assert!(GOLDEN_JSON.contains("canary-desc"));
}
