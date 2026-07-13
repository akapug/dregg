//! # The emitter: a [`CheckedLayout`] → a `CellProgram::Cases` of archetype teeth.
//!
//! Generalizes `spween-dregg`'s `compile_scene` shape: a permissive genesis case (for
//! seeding the initial state) + one `move`-guarded case carrying EVERY component's
//! invariant tooth. Because `CellProgram::Cases` is method-default-deny, an unknown
//! method is `NoTransitionCaseMatched` (a forged move is refused), and the `move` case's
//! conjuncted teeth make the executor admit a move IFF every declared component
//! invariant holds on the post-state — the refinement the allocator promises.

use dregg_app_framework::{
    CellProgram, StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
};
use dregg_cell::program::HeapAtom;

use crate::layout::{Assignment, CheckedLayout, Slot};
use crate::schema::Archetype;

/// The dispatch method a seeding (genesis) turn presents. Its case is permissive so an
/// author can seed the initial state (owner key, starting hp) without the move teeth
/// (WriteOnce would otherwise reject setting an unset identity twice, etc.).
pub const GENESIS_METHOD: &str = "genesis";

/// The dispatch method a gameplay move presents. Its case carries every component's
/// invariant tooth.
pub const MOVE_METHOD: &str = "move";

/// Why a checked layout could not be lowered to teeth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmitError {
    /// A register archetype landed on a heap slot (or vice-versa) — an internal
    /// placement inconsistency the allocator should never produce.
    Placement { component: String },
    /// An invariant's `other` field did not resolve to a register slot at emit time.
    UnresolvedInvariantTarget { component: String, other: String },
}

impl core::fmt::Display for EmitError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EmitError::Placement { component } => {
                write!(f, "`{component}` archetype/slot placement mismatch")
            }
            EmitError::UnresolvedInvariantTarget { component, other } => {
                write!(
                    f,
                    "invariant `{component}` target `{other}` did not resolve"
                )
            }
        }
    }
}

impl std::error::Error for EmitError {}

fn register_index(a: &Assignment) -> Result<u8, EmitError> {
    match a.slot {
        Slot::Register(r) => Ok(r),
        Slot::Heap(_) => Err(EmitError::Placement {
            component: a.component.clone(),
        }),
    }
}

fn heap_key(a: &Assignment) -> Result<u64, EmitError> {
    match a.slot {
        Slot::Heap(k) => Ok(k),
        Slot::Register(_) => Err(EmitError::Placement {
            component: a.component.clone(),
        }),
    }
}

/// The teeth one component's archetype compiles to.
pub fn teeth_for(
    a: &Assignment,
    layout: &CheckedLayout,
) -> Result<Vec<StateConstraint>, EmitError> {
    Ok(match &a.archetype {
        Archetype::Stat { min, max } => {
            let index = register_index(a)?;
            vec![
                StateConstraint::FieldGte {
                    index,
                    value: field_from_u64(*min),
                },
                StateConstraint::FieldLte {
                    index,
                    value: field_from_u64(*max),
                },
            ]
        }
        Archetype::Resource => vec![StateConstraint::Monotonic {
            index: register_index(a)?,
        }],
        Archetype::Identity => vec![StateConstraint::WriteOnce {
            index: register_index(a)?,
        }],
        Archetype::Invariant { other, delta } => {
            let index = register_index(a)?;
            let other_slot = layout.resolve(other).and_then(|s| match s {
                Slot::Register(r) => Some(r),
                Slot::Heap(_) => None,
            });
            let other_index = other_slot.ok_or_else(|| EmitError::UnresolvedInvariantTarget {
                component: a.component.clone(),
                other: other.clone(),
            })?;
            vec![StateConstraint::FieldLteOther {
                index,
                other: other_index,
                delta: *delta,
            }]
        }
        Archetype::Collection => vec![StateConstraint::HeapField {
            key: heap_key(a)?,
            atom: HeapAtom::Monotonic,
        }],
    })
}

/// Lower a checked layout to a `CellProgram::Cases`: a permissive genesis case + a
/// `move` case whose constraints are the conjunction of every component's teeth.
pub fn emit_program(layout: &CheckedLayout) -> Result<CellProgram, EmitError> {
    let mut move_teeth: Vec<StateConstraint> = Vec::new();
    for a in layout.assignments() {
        move_teeth.extend(teeth_for(a, layout)?);
    }

    let cases = vec![
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(GENESIS_METHOD),
            },
            constraints: vec![],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(MOVE_METHOD),
            },
            constraints: move_teeth,
        },
    ];
    Ok(CellProgram::Cases(cases))
}
