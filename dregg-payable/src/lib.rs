//! # `dregg-payable` — the `Payable` DSI + the userspace method-routing core.
//!
//! This crate holds the ONE verified source of truth for two intertwined
//! userspace concerns, low enough in the stack that BOTH the SDK
//! (`dregg-sdk`) and the application framework (`dregg-app-framework`) depend
//! on it instead of re-deriving them:
//!
//! 1. **The method-routing core** ([`routing`]): [`resolve_against`] /
//!    [`resolve_invocation`] route a method against a cell's
//!    [`InterfaceDescriptor`] through the VERIFIED DFA router, gate the
//!    method's semantics + authority, and DESUGAR to an ordinary [`Action`]
//!    carrying the underlying existing effects — no `Effect::Invoke`, no new
//!    commitment field. [`InvokeAuthority`] / [`InvokeRefused`] /
//!    [`InterfaceRegistry`] are its vocabulary.
//! 2. **The `Payable` DSI** ([`payable`]): the dregg standard interface for
//!    cross-app VALUE FLOW. A `pay` routes through the shared
//!    [`payable_descriptor`] and desugars to the ONE conserving kernel effect
//!    ([`Effect::Transfer`], per-asset Σδ=0). [`resolve_pay`] is that desugar,
//!    and it is the SAME path the app framework's signed-turn `pay` and the
//!    SDK's metered tool-gateway charge both go through — one route table, one
//!    cap gate, one conserved effect, not a parallel hand-rolled `Transfer`.
//!
//! The cipherclerk-bound, signed-`Turn`-building wrappers (`invoke`,
//! `invoke_with_descriptor`, the free `pay`) stay UP in `dregg-app-framework`
//! (they need `AppCipherclerk`, which is above the SDK); they delegate to the
//! pure core here. The [`Payable`] trait's signed-`Turn` `pay` is expressed
//! over the tiny [`ActionSigner`] abstraction so it can live here while
//! `AppCipherclerk` (the real signer) supplies the implementation.

pub mod payable;
pub mod routing;

pub use payable::{
    ActionSigner, AssetId, BALANCE_METHOD, PAY_METHOD, Payable, balance_method_sig, pay_args,
    pay_effects, pay_method_sig, payable_descriptor, resolve_pay,
};
pub use routing::{
    InterfaceRegistry, InvokeAuthority, InvokeRefused, resolve_against, resolve_invocation,
};
