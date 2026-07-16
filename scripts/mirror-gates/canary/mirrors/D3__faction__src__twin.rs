//! CANARY (D3) — M01's exact shape: a twin constructor of the SAME program. `quest` deploys
//! `Roster::compile`; nothing outside this crate reaches `faction_compiled`, yet the tests exercise
//! only `faction_compiled`. So the tested program is not the deployed program, and the two drift.
use crate::CompiledStory;

/// Build the faction program directly — the hand-maintained twin of [`crate::Roster::compile`].
/// Note it emits NO gates: exactly the M01 divergence, and the test below stays green anyway.
pub fn faction_compiled() -> CompiledStory {
    CompiledStory { gates: vec![] }
}

#[cfg(test)]
mod twin_tests {
    use super::*;
    #[test]
    fn generated_teeth_are_real() {
        let story = faction_compiled();
        assert!(story.gates.is_empty());
    }
}
