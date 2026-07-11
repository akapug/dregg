//! # `game-turn-slice` — the D-crown de-risk vertical slice.
//!
//! The one-turn proof that a game's rules-as-a-`CellProgram` become a real
//! circuit-proven turn verified by the real recursive-fold light client
//! ([`dregg_lightclient::verify_history`]), re-witnessing nothing.
//!
//! There is no runtime API here — the deliverable is the integration test
//! `tests/game_turn_slice.rs`, which DRIVES the real path end-to-end:
//!   1. the teeth-lowering probe (`cellprogram_to_descriptor2` on each game tooth's
//!      circuit encoding — which lower, which are REFUSED, with the exact blocker);
//!   2. a game `CellProgram` (combat damage-conservation + an alive flag) proved as a
//!      foldable custom leaf, bound to a `Custom`-effect `FinalizedTurn`, folded via
//!      `prove_turn_chain_recursive`, and ACCEPTED by `verify_history`;
//!   3. two non-vacuous forgeries the light client / fold REJECTS.
//!
//! It consumes the real crates (circuit-prove, lightclient, cell, turn); it adds no
//! new lowering. See the test's module docs for the honest teeth-lowering verdict.
//!
//! ## Phase-D LOWERING — the `StateConstraint → ConstraintExpr` bridge ([`compiler`])
//!
//! The de-risk found the real gap: there is NO compiler between the executor referee
//! (`dregg_cell::program::CellProgram` / `StateConstraint`) and the circuit-DSL
//! `CellProgram` the custom-leaf adapter consumes, and the ORDERING teeth
//! (`FieldGte`/`FieldLte`/`Monotonic`/…) have no inequality primitive to lower onto. The
//! [`compiler`] module is that bridge: it maps each algebraic tooth to a single
//! `Polynomial`/`Binary`, and lowers every ordering tooth through a real bit-decomposition
//! RANGE GADGET (Binary bit columns + a recomposition `Polynomial` — never a refused
//! `Lookup`). `tests/game_program_compiler.rs` DRIVES a whole game `CellProgram` (incl. a
//! `FieldGte` HP-floor and a `Monotonic` level ratchet) through the gadget →
//! `prove_custom_leaf_with_commitment`: the honest leaf ACCEPTS + its in-circuit commitment
//! binds; a FORGED ordering-violating witness has NO satisfying leaf.

pub mod compiler;
