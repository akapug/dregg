//! Cell programs: state transition logic carried by cells.
//!
//! A cell program defines valid state transitions. The executor checks the program's
//! constraints on every state-modifying action. This turns cells from "accounts with
//! permissions" into "smart contracts with privacy."
//!
//! # Slot caveats (lifted-enum v1)
//!
//! `StateConstraint` is the **slot-caveat vocabulary**: a closed lifted enum that
//! authors compose to declare a cell's perpetual invariants. The lift is described
//! in `SLOT-CAVEATS-DESIGN.md` (Lane G) and refined by `SLOT-CAVEATS-EVALUATION.md`
//! (eval — adopted 21-variant set instead of 14).
//!
//! ## `Precondition` vs `StateConstraint`
//!
//! These are **distinct surfaces with overlapping atoms**.
//!
//! - **[`crate::Preconditions`]** are **per-Action**: one-shot "given the current
//!   state, is this Action valid to apply?" Carried in `Action::preconditions`,
//!   signed-over by the submitter, evaluated *before* effects run. Scope:
//!   per-action evaluation, see-then-set guard.
//! - **[`StateConstraint`]** is **per-CellProgram-slot**: perpetual "every
//!   transition of this slot must satisfy X." Carried in `Cell::program`,
//!   signed-over at cell creation, evaluated *after* state-modifying effects
//!   on every turn. Scope: per-slot lifetime invariant.
//!
//! They share the predicate-atom alphabet (slot-equals, height-bound,
//! sender-membership) and share [`crate::preconditions::EvalContext`], but the
//! wrapper enums stay distinct because they live in different signing contexts.
//!
//! # Use cases
//!
//! - **Private DEX order**: cell holds (asset, amount, price). The matching
//!   predicate is part of the cell. A filler proves they satisfy the predicate
//!   without seeing the full order details.
//! - **Sealed auction**: cell holds committed bid. On reveal, proves
//!   `bid > minimum` and bid was committed before deadline.
//! - **NFT with provenance**: cell holds ownership + history. Transfer proves
//!   valid chain without revealing full provenance to the public.
//!
//! # Module layout
//!
//! The program surface is split by responsibility, but its public surface is
//! flat — every `pub` item is re-exported here so `crate::program::X` resolves
//! exactly as before the split:
//!
//! - [`types`] — the core program / constraint data types (`CellProgram`,
//!   `StateConstraint`, `SimpleStateConstraint`, `HeapAtom`, guards, witness
//!   carriers) and their pure constructors / sugar.
//! - [`collection`] — the collection-predicate vocabulary (`ElemPredAtom`,
//!   `CollPred`) and the heap-collection readers.
//! - [`error`] — [`ProgramError`] and its `Display` / `Error` impls.
//! - [`eval`] — the interpreter: program evaluation, every `evaluate_*` helper,
//!   the heap-atom evaluator, and the public commitment / field helpers.
//! - [`view`] — the self-describing live-view projection (`*View` types).

// Shared imports re-exported `pub(crate)` so the submodules pick them up via
// `use super::*;`. They are NOT part of the crate's external surface (the flat
// `program::X` re-exports below only forward the submodules' own `pub` items).
pub(crate) use serde::{Deserialize, Serialize};

pub(crate) use crate::preconditions::EvalContext;
pub(crate) use crate::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError,
    WitnessedPredicateRegistry,
};
pub(crate) use crate::state::{CellState, FIELD_ZERO, FieldElement, STATE_SLOTS};

mod collection;
mod error;
mod eval;
mod oracle;
mod types;
mod view;

#[cfg(test)]
mod tests;

pub use collection::*;
pub use error::*;
pub use eval::*;
pub use oracle::*;
pub use types::*;
pub use view::*;
