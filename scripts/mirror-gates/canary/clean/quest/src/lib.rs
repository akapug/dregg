//! The external live-path consumer — this is what makes `Roster::compile` "deployed".
use canary_faction::Roster;

pub fn deploy() -> canary_faction::CompiledStory {
    Roster.compile()
}
