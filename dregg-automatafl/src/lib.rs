//! # dregg-automatafl — the verified automatafl (n=2) board-transition AIR.
//!
//! A hand-authored Custom-VK circuit checking `new == apply_turn(old, moves)`
//! (`Dregg2.Games.Automatafl.applyTurn`), gated by `StateConstraint::Custom`. The
//! reference oracle (`reference`) computes the next board off-circuit; the AIR
//! (`air` + `moves`) RE-CHECKS it with low-degree DSL gates, random-access board
//! reads (one-hot dot products), and a bit-decomposition range gadget — HASH-FREE,
//! Merkle-free, Lookup-free, so it dodges every custom-leaf-adapter residual and
//! folds through `prove_custom_leaf_with_commitment` →
//! `prove_turn_chain_recursive` → `verify_history`.
//!
//! Staged: **D1** the automaton-step-only AIR; **D2** + single-move apply; **D3**
//! + the n=2 resolution. `Builder::air_accepts` shadows "the leaf proves" for the
//! fast refinement battery; the `#[ignore]` SLOW tests drive the real leaf proof +
//! recursion fold + light-client accept.

pub mod air;
pub mod builder;
pub mod moves;
pub mod reference;

pub use air::{build_d1, build_d1_honest, build_d2, build_d2_honest, build_d3, build_d3_honest};
pub use builder::Builder;
pub use reference::{Board, Move, apply_turn, automaton_step};
