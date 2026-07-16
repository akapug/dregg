//! A test-local golden done RIGHT — the false-positive test for G1. The golden is `include_str!`ed
//! AND asserted byte-equal to the tracked descriptors artifact, so it has a second author (the
//! artifact on disk) and cannot silently drift. G1 must leave it alone: a gate that punishes a
//! welded golden is a gate that gets switched off.

const GOLDEN_JSON: &str = include_str!("welded_local_golden.json");

#[test]
fn the_golden_is_welded_to_the_deployed_descriptor() {
    let deployed = include_str!("../../circuit/descriptors/by-name/canary.json");
    assert_eq!(GOLDEN_JSON, deployed.strip_suffix('\n').unwrap_or(deployed));
}
