//! The Private Convex Engine at T>1 — iterated `x ← prox(x − τ·A·x)` with a proven noise budget.
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §2. OWNED by the `convex_engine` lane.
//! Consumes `convex_step::{SignedCt, PublicLinearStep, convex_linear_step}` (T=1, already built + tested).
//! Depends on `metatheory/Bfv/Noise.lean`'s T-composition bound for `max_iterations_for_params`.
#![allow(dead_code, unused_variables)]

use crate::convex_step::{PublicLinearStep, SignedCt};

pub type Result<T> = std::result::Result<T, ConvexEngineError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvexEngineError {
    NoiseBudgetExceeded { requested: u32, ceiling: u32 },
    DimMismatch,
}

/// T iterations of x ← prox(x − τ·A·x). Refuses fail-closed when T exceeds the proven-safe ceiling.
pub fn convex_solve(
    x0: &[SignedCt],
    step: &PublicLinearStep,
    prox_lo: i64,
    prox_hi: i64,
    iterations: u32,
    t: u64,
) -> Result<Vec<SignedCt>> {
    todo!("convex_engine lane: iterate convex_linear_step + prox with the noise-budget guard")
}
/// The proven-safe iteration ceiling for these params (from Bfv/Noise.lean's T-composition bound).
pub fn max_iterations_for_params(step: &PublicLinearStep, t: u64) -> u32 {
    todo!("convex_engine lane: the Lean-proven T ceiling")
}
