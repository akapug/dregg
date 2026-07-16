//! # The general parameter-composition verifier
//!
//! The Custom-VK AIR that a Braid resolver — and every future creature, entity, item, or
//! institution system — lives in. It proves a **bounded nonlinear composition over typed
//! projections**, and it contains no game.
//!
//! This is the §9.3 component of `docs/design/HOARDLIGHT-LIVING-WORLD.md`, built to the
//! shape that doc demands:
//!
//! > The resonance proof will become the most reused and most tempting-to-hardcode
//! > component. Its public inputs must be a bounded list of typed projections plus roots
//! > and roles — not a fixed Rust struct whose field count encodes Stage 1.
//!
//! ## What it proves
//!
//! > Given the canonical ordered list of typed projections committed by `subjects_root`,
//! > and the versioned law committed by `ruleset_root`, the value committed by
//! > `outcome_commitment` is the composition that law licenses — and the per-term
//! > contributions committed by `explanation_root` are the terms it is made of.
//!
//! `outcome = Σ_linear coeff · P[role].params[i] + Σ_knots coeff · P[a].params[i] · P[b].params[j]`
//!
//! The **knots** are the point. `AffineLe`/`AffineEq` — the declarative StateConstraint
//! vocabulary — are LINEAR: nothing in them multiplies two state values. A knot is a
//! degree-3 gate `coeff · val_a · val_b` over two subjects' params, so a nonlinear
//! composition MUST be a Custom VK with a hand-written AIR. That is settled, and this is
//! that AIR in its general form.
//!
//! ## Why it is general (what a new game costs)
//!
//! | new thing | cost |
//! |---|---|
//! | new balance numbers | a new `ruleset_root` — data |
//! | new roles / new role vocabulary | data (a role is an opaque `u64` the ruleset addresses) |
//! | new params, new param meanings | data (params are witnessed; `param_count` is a PI) |
//! | new knots (new nonlinear relations) | data |
//! | a whole new creature/entity/institution system | data |
//! | more subjects / params / knots than the bounds | a new [`ComposeShape`] = a new VK (a size class, like a bigger board) |
//! | **a kernel or AIR edit** | **never** |
//!
//! Nothing in [`air`]'s types is a field count, a param count, a role list, or a rule
//! table. [`ComposeShape`] carries only MAXIMA, which double as the fuel/DoS meter
//! ([`ComposeShape::hash_sites`]) — a host prices a composition from the shape alone,
//! without seeing its content.
//!
//! ## The public inputs
//!
//! See [`pi`]. `[old_commit8 ‖ new_commit8]` is the Custom-VK door's state-binding ABI
//! (`dregg_circuit::effect_vm::custom_state_binding`); the app PIs are the ABI version,
//! four counts, and the four roots. **The layout is constant in the number of subjects** —
//! `subjects_root` binds the whole canonical ordered list at ~124 bits rather than
//! spending a PI slot per subject, which is exactly the "field count encodes Stage 1"
//! cul-de-sac §9.3 forbids.
//!
//! ## The budget (measured — `tests/size.rs`)
//!
//! Against the deployed caps `MAX_TRACE_WIDTH = 1024`, `MAX_CONSTRAINT_DEGREE = 8`,
//! `MAX_PUBLIC_INPUTS = 64`, all at the deployable `W = 8` binding width:
//!
//! ```text
//!   shape                      cols   deg  PIs  app  sites   verdict
//!   n2 p2  l1  k1               259    3    53   37    88    FITS
//!   n3 p4  l3  k2               475    3    53   37   168    FITS   <- proved as a leaf
//!   n4 p8  l8  k6 (realistic)  1027    3    53   37   368    3 OVER  (identity_bits=28)
//!   n4 p8  l8  k6 (realistic)   999    3    53   37   368    FITS    (identity_bits=24)
//!   n6 p8  l12 k10             1654    3    53   37   560    EXCEEDS -> segment
//!   n8 p16 l16 k16             3079    3    53   37   952    EXCEEDS -> segment
//! ```
//!
//! Degree is **3** everywhere (cap 8) — the knot `coeff · val_a · val_b` and the
//! `sel_j · selp_p · param` read are the only cubics, so degree is never the binding
//! constraint. PIs are **53/64 (37/48 app)** and CONSTANT in every bound — growing the
//! scene never touches the layout.
//!
//! **Segmentation is NOT needed at the realistic shape.** It lands 3 columns over at the
//! default 28-bit identity namespace and fits at 999/1024 over a 24-bit one (16.7M
//! identities) — `tests/prove_fold.rs` proves that saturated shape as a SINGLE foldable
//! leaf. The lever is real rather than a fudge: the ordering tooth's range gadgets are the
//! AIR's biggest cost (`identity_bits` per subject + `identity_bits+1` per comparison,
//! ~200 columns at n=4), which is exactly why the namespace width is a SHAPE field.
//!
//! ### The segmentation plan (needed for growth past ~n4/p8, not for Stage 1)
//!
//! The digest chains are the natural cut: they are 368 of the 1027 columns and the only
//! part that scales with `W`.
//!
//! * **Segment A (composition)** — subjects, ruleset, role/param resolution, the knots,
//!   the outcome, the contributions. Everything except the four wide chains (~659 cols).
//! * **Segments B_d (digest)**, one per stream `d ∈ {subjects, ruleset, outcome,
//!   explanation}` — the `W` chains over that stream's felts.
//!
//! The seam is the pattern the deployed fold ALREADY uses for the custom leaf's
//! commitment (`prove_custom_binding_node_segmented` `connect`s a claimed commitment,
//! lane by lane, to what the leaf computes in-circuit): segment A exposes its stream
//! columns, each B_d exposes `[its stream ‖ its root]`, and the binding node `connect`s
//! A's stream lanes to B_d's stream lanes and B_d's root lanes to the PI. The connected
//! width is the stream length (46 felts for subjects, 72 for the ruleset at the realistic
//! shape), so it is a fold-node cost, not a new mechanism. This is the automatafl width
//! residual in the same shape and closed the same way — named here, not discovered later.
//!
//! ## Honest scope
//!
//! Things this crate does NOT do, stated at current resolution:
//!
//! 1. **The outcome is not welded into the cell state.** `[old8 ‖ new8]` ride the door and
//!    the EXECUTOR welds them to the cell's roots, but nothing yet requires the cell's new
//!    state to CONTAIN `outcome_commitment`. That weld needs cell-state-layout knowledge,
//!    which is app-specific; its general form is an executor-enforced atom ("the new state
//!    carries the sub-proof's published outcome commitment"), and it is the named residual.
//! 2. **Identity faithfulness is the projection layer's obligation.** The duplicate tooth
//!    refuses two subjects sharing an identity, over the identities it is GIVEN; that an
//!    identity names a distinct real entity is upstream (see [`model::Subject::identity`]).
//! 3. **The binding width costs 8x what it should.** The one-site 8-felt primitive
//!    (`MerkleHash8`) is refused by the custom-leaf lowering, so ~124-bit roots are built
//!    from 8 parallel 4-ary chains. See [`digest`] and [`shape::DEPLOYABLE_DIGEST_FELTS`].
//! 4. **The identity namespace is bounded** (`identity_bits <= 28`, a shape field). Not a
//!    hidden count, but a real limit: the ordering comparison goes VACUOUS on a full-width
//!    31-bit value, so an unbounded identity would give an ordering tooth that looks
//!    present and enforces nothing. A shape that would defeat the margin is REFUSED
//!    ([`ComposeShape::identity_bits_sound`]) rather than silently built.
//! 5. **A role is a KEY.** Roles are unique per composition, which is what makes
//!    `role -> subject` a function (and the outcome non-malleable). Several same-kind
//!    participants therefore take distinct tags (`equipped_0`, `equipped_1`), not a
//!    repeated one — a designed semantic, not an oversight.
//! 6. **Selective disclosure is a commitment opening, not a proof.** Params are private
//!    witness and never public; a caller discloses by opening `subjects_root` /
//!    `explanation_root`. A zero-knowledge *predicate* over a hidden param (rather than
//!    revealing it) is a further ruleset term, not a new mechanism.

pub mod air;
pub mod builder;
pub mod digest;
pub mod field;
pub mod model;
pub mod pi;
pub mod reference;
pub mod shape;

pub use air::{ComposeAir, Forgery, build, build_forged};
pub use builder::{Builder, Head};
pub use model::{ComposeError, Composition, Knot, LinearTerm, Ruleset, Subject};
pub use reference::{Composed, compose_over};
pub use shape::{ComposeShape, DEPLOYABLE_DIGEST_FELTS, PARAM_COMPOSE_ABI_VERSION};
