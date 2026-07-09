//! Backward-compatible re-exports for predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates`].

pub use crate::dsl::predicates::{
    PREDICATE_DIFF_BITS, PredicateAir, PredicateOp, PredicateType, PredicateWitness,
    compute_fact_commitment,
};
