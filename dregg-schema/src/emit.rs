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
use spween_dregg::GENESIS_DONE_EXT_KEY;

use crate::layout::{Assignment, CheckedLayout, Slot};
use crate::schema::Archetype;

/// The dispatch method a seeding (genesis) turn presents. Seeding needs its OWN case
/// (the executor's `Cases` dispatch is method-default-deny) that does NOT carry the move
/// teeth (`WriteOnce` would reject seeding an identity, a `Monotonic` resource cannot be
/// set from an absent baseline, etc.). But an EMPTY genesis case is a universal
/// write-hatch: `apply_raw("genesis", [SetField(slot, V)])` POST-DEPLOY re-hits the
/// permissive case and commits ARBITRARY writes to ANY slot, routing around every move
/// tooth. So the genesis case is instead made ONE-SHOT — see [`genesis_oneshot_teeth`].
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

/// Lower a checked layout to a `CellProgram::Cases`: a ONE-SHOT genesis case + a `move`
/// case whose constraints are the conjunction of every component's teeth, plus the
/// genesis-sentinel freeze.
///
/// ## The genesis write-hatch, closed at the root (ported from `spween-dregg`)
///
/// The genesis case cannot carry the move teeth (seeding an identity/resource from a
/// blank baseline must be free), so before this it carried EMPTY constraints — and
/// `WorldCell::apply_raw` re-dispatches ANY method with no one-shot guard. A POST-DEPLOY
/// `seed()` / `apply_raw("genesis", [SetField(slot, V)])` re-hit the permissive case and
/// committed arbitrary writes to ANY slot (e.g. `hp` past its `Stat` cap), routing around
/// every `move` tooth — a universal write-hatch on every deployed schema.
///
/// The fix makes the genesis case a `0 → 1` transition on [`GENESIS_DONE_EXT_KEY`]
/// (`Equals{1} ∧ DeltaEquals{1}`): admissible EXACTLY once (at the first seed, sentinel
/// still field-zero), jointly UNSATISFIABLE for every later genesis turn regardless of
/// which slot a stapled `SetField` targets — no per-slot dependence. The `move` case
/// freezes the sentinel (`Immutable`) so no move can reset it to re-open genesis.
///
/// This reuses spween's `WorldCell` machinery verbatim: `program_requires_genesis_sentinel`
/// keys off the INSTALLED PROGRAM (a genesis case carrying a `HeapField` over
/// [`GENESIS_DONE_EXT_KEY`]), so `deploy_compiled` births the sentinel at field-zero and
/// `commit` injects the `0 → 1` write on the `"genesis"` method automatically — no
/// change needed on the world side, because a schema game IS a `spween_dregg::WorldCell`.
pub fn emit_program(layout: &CheckedLayout) -> Result<CellProgram, EmitError> {
    let mut move_teeth: Vec<StateConstraint> = Vec::new();
    for a in layout.assignments() {
        move_teeth.extend(teeth_for(a, layout)?);
    }
    // FREEZE the genesis-done sentinel on the move case: a move never touches it, so
    // `Immutable` admits the unchanged key — but a stapled `move` that tried to RESET
    // the sentinel to re-open the one-shot genesis is REFUSED.
    move_teeth.push(genesis_sentinel_freeze());

    let cases = vec![
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(GENESIS_METHOD),
            },
            constraints: genesis_oneshot_teeth(),
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

/// The ONE-SHOT genesis teeth: the `0 → 1` transition on [`GENESIS_DONE_EXT_KEY`].
/// `Equals{1} ∧ DeltaEquals{1}` holds iff `old == 0 ∧ new == 1` — admissible exactly
/// once (at the first seed, sentinel still field-zero), jointly UNSATISFIABLE for every
/// post-deploy genesis turn (`old == 1` forces `Δ == 0 ≠ 1`, and `Δ == 1` forces
/// `new == 2 ≠ 1`). The genesis case carries NO `Immutable` — it must perform the
/// `0 → 1` write itself (`WorldCell::commit` injects it on the `"genesis"` method).
pub fn genesis_oneshot_teeth() -> Vec<StateConstraint> {
    vec![
        StateConstraint::HeapField {
            key: GENESIS_DONE_EXT_KEY,
            atom: HeapAtom::Equals {
                value: field_from_u64(1),
            },
        },
        StateConstraint::HeapField {
            key: GENESIS_DONE_EXT_KEY,
            atom: HeapAtom::DeltaEquals { d: 1 },
        },
    ]
}

/// Freeze the genesis-done sentinel on a NON-genesis case: `HeapField{Immutable}` admits
/// the unchanged key (no case but genesis ever writes it) but REFUSES any write — so no
/// other method can reset the sentinel to re-open the one-shot genesis.
pub fn genesis_sentinel_freeze() -> StateConstraint {
    StateConstraint::HeapField {
        key: GENESIS_DONE_EXT_KEY,
        atom: HeapAtom::Immutable,
    }
}
