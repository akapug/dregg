//! Backward-compatible re-exports for arithmetic predicate AIR types.
//!
//! The production implementation lives in [`crate::dsl::predicates::arithmetic`].

pub use crate::dsl::predicates::{
    ArithExpr, ArithPredicate, CompareOp, compute_arithmetic_fact_commitment,
};

/// Backward-compatible witness struct for arithmetic predicates.
pub struct ArithmeticPredicateWitness {
    pub inputs: Vec<u32>,
    pub predicate: ArithPredicate,
    pub fact_commitment: crate::field::BabyBear,
}
