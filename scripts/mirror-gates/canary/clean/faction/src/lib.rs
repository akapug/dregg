//! One constructor of the program. `quest` deploys it; the tests exercise the same one.

pub struct CompiledStory {
    pub gates: Vec<String>,
}

pub struct Roster;

impl Roster {
    /// Compile the roster into the program. THE single constructor — there is no twin to drift
    /// against, so "the tested program is the deployed program" is a tautology here.
    pub fn compile(&self) -> CompiledStory {
        CompiledStory {
            gates: vec!["monotonic(rep)".into()],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn teeth_are_real() {
        let story = Roster.compile();
        assert_eq!(story.gates.len(), 1);
    }
}
