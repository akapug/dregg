//! Backward-compatible re-exports for relational predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates::relational`].

pub use crate::dsl::predicates::{
    RelationalOp as RelationType, RelationalPredicateWitness, RelationalWitness,
    compute_value_commitment,
};
