//! **`invoke()` — cells-as-service-objects method dispatch at the USERSPACE layer.**
//!
//! A cell already does method-dispatch: an [`Action`] carries a `method:
//! Symbol` + `args`, and a [`dregg_cell::CellProgram::Cases`] program scopes a
//! transition to a method via [`dregg_cell::TransitionGuard::MethodIs`]. The
//! [`dregg_cell::InterfaceDescriptor`] gives that interface a first-class,
//! content-addressed TYPE (a set of [`dregg_cell::MethodSig`]s rooted at an
//! `interface_id`).
//!
//! This module is the **`invoke()` front door**. The load-bearing design decision
//! is twofold:
//!
//! 1. It lives *slightly higher than the effect-VM primitive*, NOT as a kernel
//!    [`Effect`]. There is no `Effect::Invoke`. Method-matching is a USERSPACE
//!    routing concern; the kernel and the circuit keep seeing only the effects
//!    they already know.
//! 2. The interface *instance* is a USERSPACE object — it is NOT a committed
//!    field of the cell. The descriptor is resolved at this layer, either DERIVED
//!    on the fly from the cell's `CellProgram::Cases`, or looked up from a
//!    userspace [`InterfaceRegistry`].
//!
//! # The split: pure core below, cipherclerk wrappers here
//!
//! The pure routing core — [`InvokeAuthority`], [`InvokeRefused`],
//! [`InterfaceRegistry`], [`resolve_against`], [`resolve_invocation`] — lives in
//! the lower `dregg-payable` crate (so the SDK reuses it too) and is re-exported
//! here unchanged. This module keeps only the cipherclerk-bound, signed-`Turn`
//! builders [`invoke`] / [`invoke_with_descriptor`], which resolve through that
//! core and then sign + wrap with the framework [`AppCipherclerk`].
//!
//! The `Effect` enum is UNCHANGED: no new variant, no non-exhaustive match.
//! `invoke()` is sugar that resolves to effects the kernel already enforces and
//! the circuit already witnesses; the cell-commitment is untouched because the
//! interface lives entirely in userspace.

use dregg_cell::Cell;
use dregg_cell::interface::InterfaceDescriptor;
use dregg_turn::Turn;
use dregg_turn::action::Effect;
use dregg_types::CellId;

use crate::cipherclerk::AppCipherclerk;

// The pure routing core lives in `dregg-payable` (low enough for the SDK to reuse
// it). Re-exported here so existing `dregg_app_framework::invoke::*` consumers are
// unchanged.
pub use dregg_payable::routing::{
    InterfaceRegistry, InvokeAuthority, InvokeRefused, resolve_against, resolve_invocation,
};

/// **`invoke(cell, method, args)` — the userspace front door.**
///
/// Resolves `method` against the cell's interface (derived from its program, OR
/// — via [`invoke_with_descriptor`] — an explicit userspace descriptor), routes
/// it through the verified DFA, gates semantics + auth, then SIGNS the desugared
/// [`Action`] with `cipherclerk` and wraps it in a [`Turn`] ready for the normal
/// executor path. The returned turn carries the underlying existing effects — the
/// kernel and circuit see only effects they already know; there is NO
/// `Effect::Invoke`, and no cell-commitment dependency.
pub fn invoke(
    cipherclerk: &AppCipherclerk,
    cell: &Cell,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    let descriptor = InterfaceDescriptor::derive_replayable(&cell.program);
    invoke_with_descriptor(
        cipherclerk,
        cell.id(),
        &descriptor,
        method,
        args,
        effects,
        authority,
    )
}

/// [`invoke`] against an EXPLICIT userspace descriptor (e.g. from an
/// [`InterfaceRegistry`]) rather than the derived-from-program one — for cells
/// whose interface carries richer per-method auth/semantics than the program
/// alone expresses.
#[allow(clippy::too_many_arguments)]
pub fn invoke_with_descriptor(
    cipherclerk: &AppCipherclerk,
    target: CellId,
    descriptor: &InterfaceDescriptor,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    invoke_with_descriptor_with_witnesses(
        cipherclerk,
        target,
        descriptor,
        method,
        args,
        effects,
        authority,
        Vec::new(),
    )
}

/// [`invoke_with_descriptor`] with canonical action witness blobs attached
/// **before** the action is signed.
///
/// Witness-attached cell predicates (for example a `CountGe` exhibit) are
/// executor inputs, not userspace metadata. The action hash covers
/// `witness_blobs`, so callers must not build/sign first and append them later.
/// This builder keeps the ordinary method-resolution/authentication path and
/// changes only the signed action payload.
#[allow(clippy::too_many_arguments)]
pub fn invoke_with_descriptor_with_witnesses(
    cipherclerk: &AppCipherclerk,
    target: CellId,
    descriptor: &InterfaceDescriptor,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
    witness_blobs: Vec<dregg_turn::action::WitnessBlob>,
) -> Result<Turn, InvokeRefused> {
    let (action, _sig) = resolve_against(target, descriptor, method, args, effects, authority)?;
    let mut action = action;
    action.witness_blobs = witness_blobs;
    let signed = cipherclerk.sign_action(action);
    Ok(cipherclerk.make_turn(signed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::interface::method_symbol;
    use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};

    /// A cell whose `Cases` program dispatches on the given methods (so its
    /// derived interface exposes them, all Replayable).
    fn cell_dispatching(method_names: &[&str]) -> Cell {
        let cases = method_names
            .iter()
            .map(|name| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(name),
                },
                constraints: vec![],
            })
            .collect();
        let mut cell = Cell::with_balance([7u8; 32], [0u8; 32], 0);
        cell.program = CellProgram::Cases(cases);
        cell
    }

    fn an_effect(cell: CellId) -> Effect {
        Effect::SetField {
            cell,
            index: 0,
            value: [1u8; 32],
        }
    }

    #[test]
    fn invoke_resolves_through_the_reexported_core() {
        // The framework's re-exported routing core resolves a program-dispatched
        // method to its underlying effect (the `dregg-payable` core, used here).
        let cell = cell_dispatching(&["send"]);
        let (action, _) = resolve_invocation(
            &cell,
            "send",
            vec![],
            vec![an_effect(cell.id())],
            InvokeAuthority::None,
        )
        .expect("a program-dispatched method resolves through the re-exported core");
        assert_eq!(action.method, method_symbol("send"));
    }
}
