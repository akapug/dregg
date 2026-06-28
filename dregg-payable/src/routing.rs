//! **The userspace method-routing core — `resolve_against` / `resolve_invocation`.**
//!
//! A cell already does method-dispatch: an [`Action`] carries a `method:
//! Symbol` + `args`, and a [`dregg_cell::CellProgram::Cases`] program scopes a
//! transition to a method via [`dregg_cell::TransitionGuard::MethodIs`]. The
//! [`InterfaceDescriptor`] gives that interface a first-class, content-addressed
//! TYPE (a set of [`MethodSig`]s rooted at an `interface_id`).
//!
//! This module is the pure routing core of the `invoke()` front door: it routes
//! a method against a cell's interface (derived-from-program or registry-supplied)
//! through the VERIFIED DFA router, gates the method's semantics + authority, and
//! DESUGARS to an ordinary [`Action`] carrying the underlying existing effects.
//! There is NO `Effect::Invoke` and NO cell-commitment dependency: the interface
//! is a userspace object, not a committed cell field.
//!
//! It carries NO cipherclerk and NO executor (it depends only on
//! `dregg-cell`/`dregg-turn`/`dregg-types`), so it sits low enough that both the
//! SDK and the app framework reuse it. The cipherclerk-bound, signed-`Turn`
//! wrappers (`invoke`, `invoke_with_descriptor`) live up in
//! `dregg-app-framework` and delegate here.

use std::collections::HashMap;

use dregg_cell::Cell;
use dregg_cell::interface::{InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::action::{Action, Effect};
use dregg_types::CellId;

/// The authority a caller presents when invoking a method.
///
/// [`resolve_against`] checks this against the method's declared
/// [`AuthRequired`] BEFORE building any effect — the cap-gate. This is the
/// *userspace declaration* of what the caller can satisfy; the actual
/// cryptographic check (a real signature/proof binding the action hash) is
/// performed downstream by the executor when the desugared turn runs. The gate
/// here is the early, legible refusal: an `auth_required: Signature` method
/// invoked by a caller holding only [`InvokeAuthority::None`] is rejected at the
/// front door rather than producing a turn the executor would later reject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvokeAuthority {
    /// The caller holds no special authority (only methods declaring
    /// [`AuthRequired::None`] may be invoked).
    None,
    /// The caller can produce a valid signature from the cell's key.
    Signature,
    /// The caller can produce a valid ZK proof against the cell's key.
    Proof,
    /// The caller holds a custom authority identified by its `vk_hash` (must
    /// match the method's `AuthRequired::Custom { vk_hash }`).
    Custom { vk_hash: [u8; 32] },
}

impl InvokeAuthority {
    /// Does this caller authority satisfy a method's declared `auth_required`?
    ///
    /// Mirrors the executor's auth-tier semantics:
    /// - [`AuthRequired::None`] — satisfied by anything.
    /// - [`AuthRequired::Signature`] — needs [`InvokeAuthority::Signature`].
    /// - [`AuthRequired::Proof`] — needs [`InvokeAuthority::Proof`].
    /// - [`AuthRequired::Either`] — needs `Signature` OR `Proof`.
    /// - [`AuthRequired::Impossible`] — never satisfied (a permanently locked
    ///   method has no invocation).
    /// - [`AuthRequired::Custom { vk_hash }`] — needs a matching
    ///   [`InvokeAuthority::Custom`].
    pub fn satisfies(self, required: &AuthRequired) -> bool {
        match required {
            AuthRequired::None => true,
            AuthRequired::Signature => self == InvokeAuthority::Signature,
            AuthRequired::Proof => self == InvokeAuthority::Proof,
            AuthRequired::Either => {
                matches!(self, InvokeAuthority::Signature | InvokeAuthority::Proof)
            }
            AuthRequired::Impossible => false,
            AuthRequired::Custom { vk_hash } => {
                matches!(self, InvokeAuthority::Custom { vk_hash: held } if held == *vk_hash)
            }
        }
    }
}

/// **A userspace registry of cell interfaces.**
///
/// The interface descriptor is NOT a committed field of a cell — it lives in
/// userspace. An app that wants richer per-method auth/semantics than
/// [`InterfaceDescriptor::derive_replayable`] gives (which makes every
/// program-dispatched method `Replayable` with `AuthRequired::None`) registers
/// the explicit descriptor here and resolves through it.
#[derive(Clone, Debug, Default)]
pub struct InterfaceRegistry {
    by_cell: HashMap<CellId, InterfaceDescriptor>,
}

impl InterfaceRegistry {
    /// A new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register the interface a cell exposes (overwriting any prior entry).
    pub fn register(&mut self, cell: CellId, descriptor: InterfaceDescriptor) {
        self.by_cell.insert(cell, descriptor);
    }

    /// The registered descriptor for a cell, if any.
    pub fn get(&self, cell: &CellId) -> Option<&InterfaceDescriptor> {
        self.by_cell.get(cell)
    }

    /// Resolve the descriptor for a cell: the explicitly-registered one if
    /// present, else the interface DERIVED from the cell's program
    /// ([`InterfaceDescriptor::derive_replayable`]). This is the canonical
    /// userspace resolution — always succeeds (a cell with no method-dispatch
    /// derives the empty interface).
    pub fn resolve(&self, cell: &Cell) -> InterfaceDescriptor {
        match self.by_cell.get(&cell.id()) {
            Some(d) => d.clone(),
            None => InterfaceDescriptor::derive_replayable(&cell.program),
        }
    }
}

/// Why a method invocation was refused at the userspace front door (before any
/// turn is fired). Each variant is a fail-closed refusal: no effect is built,
/// nothing is submitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InvokeRefused {
    /// The method name does not route to any declared method of the resolved
    /// interface (via the verified DFA router). Unknown method, fail-closed.
    UnknownMethod {
        /// The method name that did not route.
        method: String,
    },
    /// The method is declared but its authority requirement is not satisfied by
    /// the caller's presented [`InvokeAuthority`].
    Unauthorized {
        /// The method name.
        method: String,
        /// What the method requires.
        required: AuthRequired,
    },
    /// The method is a [`Semantics::Serviced`] method — its answer rides the OFE
    /// cross-cell-read, NOT a pure-replay effect desugar. `invoke()` does not
    /// fire it; the serviced-answer carrier is the named seam (no kernel effect).
    ServicedSeam {
        /// The method name.
        method: String,
    },
}

impl std::fmt::Display for InvokeRefused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownMethod { method } => {
                write!(
                    f,
                    "method `{method}` is not a declared method of the interface"
                )
            }
            Self::Unauthorized { method, required } => write!(
                f,
                "method `{method}` requires {required:?}; caller authority is insufficient"
            ),
            Self::ServicedSeam { method } => write!(
                f,
                "method `{method}` is a Serviced method; its answer rides the OFE cross-cell-read \
                 (named seam) — no effect desugar"
            ),
        }
    }
}

impl std::error::Error for InvokeRefused {}

/// **Resolve a method invocation into an [`Action`]** against an EXPLICIT
/// descriptor — the pure routing core, with no cipherclerk and no executor.
///
/// The `descriptor` is the userspace interface for `target` (resolved by the
/// caller, e.g. via [`InterfaceRegistry::resolve`]). There is NO commitment
/// check: the interface is a userspace object, not a committed cell field.
///
/// Performs route-method → gate-semantics → cap-gate-auth and returns the
/// desugared, UNSIGNED [`Action`] carrying the underlying `effects` targeting the
/// resolved method symbol, alongside the matched [`MethodSig`].
pub fn resolve_against(
    target: CellId,
    descriptor: &InterfaceDescriptor,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<(Action, MethodSig), InvokeRefused> {
    // (2) Route the method through the VERIFIED DFA router (not an ad-hoc find).
    let symbol = method_symbol(method);
    let sig = descriptor
        .route_method(&symbol)
        .ok_or_else(|| InvokeRefused::UnknownMethod {
            method: method.to_string(),
        })?
        .clone();

    // (3) Serviced methods do not desugar to a replay effect — named seam.
    if sig.semantics == Semantics::Serviced {
        return Err(InvokeRefused::ServicedSeam {
            method: method.to_string(),
        });
    }

    // (4) Cap-gate on the method's declared authority.
    if !authority.satisfies(&sig.auth_required) {
        return Err(InvokeRefused::Unauthorized {
            method: method.to_string(),
            required: sig.auth_required.clone(),
        });
    }

    // (5) Desugar to an ordinary Action targeting the method symbol, carrying the
    //     underlying existing effects. No new Effect variant: the kernel/circuit
    //     see only effects they already know. The action is unsigned here; the
    //     cipherclerk path signs it.
    let action = Action {
        target,
        method: symbol,
        args,
        authorization: dregg_turn::action::Authorization::unsigned_placeholder(),
        preconditions: Default::default(),
        effects,
        may_delegate: dregg_turn::action::DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: Vec::new(),
    };

    Ok((action, sig))
}

/// **Resolve a method invocation against the interface DERIVED from the cell's
/// program** — the no-registry path.
///
/// Resolves the cell's interface in userspace via
/// [`InterfaceDescriptor::derive_replayable`] (reads only `cell.program`, no
/// commitment), then routes/gates/desugars via [`resolve_against`]. Every method
/// a derived interface exposes is `Replayable` with `AuthRequired::None`, so for
/// richer auth use an [`InterfaceRegistry`] + [`resolve_against`].
pub fn resolve_invocation(
    cell: &Cell,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<(Action, MethodSig), InvokeRefused> {
    let descriptor = InterfaceDescriptor::derive_replayable(&cell.program);
    resolve_against(cell.id(), &descriptor, method, args, effects, authority)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig};
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
    fn invoke_of_replayable_method_desugars_to_underlying_effect() {
        let cell = cell_dispatching(&["send", "dequeue"]);
        let effects = vec![an_effect(cell.id())];

        let (action, sig) = resolve_invocation(
            &cell,
            "send",
            vec![],
            effects.clone(),
            InvokeAuthority::None,
        )
        .expect("a program-dispatched method must resolve from the derived interface");

        assert_eq!(action.method, method_symbol("send"));
        assert_eq!(action.target, cell.id());
        assert_eq!(action.effects.len(), 1);
        assert!(matches!(action.effects[0], Effect::SetField { .. }));
        assert_eq!(sig.semantics, Semantics::Replayable);
    }

    #[test]
    fn invoke_refuses_unknown_method() {
        let cell = cell_dispatching(&["send"]);
        let refused = resolve_invocation(
            &cell,
            "undeclared",
            vec![],
            vec![an_effect(cell.id())],
            InvokeAuthority::Signature,
        )
        .unwrap_err();
        assert!(matches!(refused, InvokeRefused::UnknownMethod { .. }));
    }

    #[test]
    fn registry_descriptor_carries_auth_and_serviced_semantics() {
        let cell = cell_dispatching(&["send", "close", "peek"]);
        let desc = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("send")),
            MethodSig {
                args_schema: ArgsSchema::Fixed(1),
                auth_required: AuthRequired::Signature,
                ..MethodSig::replayable(method_symbol("close"))
            },
            MethodSig {
                semantics: Semantics::Serviced,
                ..MethodSig::replayable(method_symbol("peek"))
            },
        ]);
        let mut reg = InterfaceRegistry::new();
        reg.register(cell.id(), desc);
        let resolved = reg.resolve(&cell);

        let refused = resolve_against(
            cell.id(),
            &resolved,
            "close",
            vec![[0u8; 32]],
            vec![an_effect(cell.id())],
            InvokeAuthority::None,
        )
        .unwrap_err();
        assert!(matches!(
            refused,
            InvokeRefused::Unauthorized {
                required: AuthRequired::Signature,
                ..
            }
        ));

        let (action, _) = resolve_against(
            cell.id(),
            &resolved,
            "close",
            vec![[0u8; 32]],
            vec![an_effect(cell.id())],
            InvokeAuthority::Signature,
        )
        .expect("signature caller satisfies the Signature gate");
        assert_eq!(action.method, method_symbol("close"));

        let seam = resolve_against(
            cell.id(),
            &resolved,
            "peek",
            vec![],
            vec![],
            InvokeAuthority::None,
        )
        .unwrap_err();
        assert!(matches!(seam, InvokeRefused::ServicedSeam { .. }));
    }

    #[test]
    fn registry_falls_back_to_derived_when_unregistered() {
        let cell = cell_dispatching(&["send"]);
        let reg = InterfaceRegistry::new();
        let resolved = reg.resolve(&cell);
        assert!(resolved.method(&method_symbol("send")).is_some());
        let (action, _) = resolve_against(
            cell.id(),
            &resolved,
            "send",
            vec![],
            vec![an_effect(cell.id())],
            InvokeAuthority::None,
        )
        .expect("derived-fallback send resolves");
        assert_eq!(action.method, method_symbol("send"));
    }

    #[test]
    fn authority_satisfies_tiers() {
        assert!(InvokeAuthority::None.satisfies(&AuthRequired::None));
        assert!(!InvokeAuthority::None.satisfies(&AuthRequired::Signature));
        assert!(InvokeAuthority::Signature.satisfies(&AuthRequired::Signature));
        assert!(InvokeAuthority::Signature.satisfies(&AuthRequired::Either));
        assert!(InvokeAuthority::Proof.satisfies(&AuthRequired::Either));
        assert!(!InvokeAuthority::Signature.satisfies(&AuthRequired::Proof));
        assert!(!InvokeAuthority::Signature.satisfies(&AuthRequired::Impossible));
        let vk = [9u8; 32];
        assert!(
            InvokeAuthority::Custom { vk_hash: vk }
                .satisfies(&AuthRequired::Custom { vk_hash: vk })
        );
        assert!(
            !InvokeAuthority::Custom { vk_hash: [1u8; 32] }
                .satisfies(&AuthRequired::Custom { vk_hash: vk })
        );
    }
}
