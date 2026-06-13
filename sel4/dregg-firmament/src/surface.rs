//! The SURFACE backing — a window IS a dregg cell's surface capability.
//!
//! `docs/DREGG-DESKTOP-OS.md` casts the dregg-native desktop as **the firmament
//! made visual**: a window is a `Capability{ target: Surface(cell), rights }` on
//! the SAME `(target, rights)` handle that today resolves [`crate::Target::Local`]
//! (an seL4 syscall) and [`crate::Target::Distributed`] (a real executor turn).
//! A surface is not a new kind of authority — it is a dregg **cell** whose state
//! is rendered as glass. Holding a window means holding a cap over that cell;
//! attenuating the window (read-only mirror, input-disabled view, a clipped
//! sub-region) is attenuating the cap; delegating the window to another app is
//! delegating the cap; revoking it is revoking the cap. All through the SAME
//! gate as every other firmament cap.
//!
//! Concretely this backing is the [`crate::DistributedBacking`] machinery aimed
//! at a cell that backs a surface: it holds a real [`dregg_cell::Ledger`] and a
//! real [`dregg_turn::TurnExecutor`], and
//!
//! - [`SurfaceBacking::invoke`] resolves a surface cap by reading the surface
//!   cell out of the real ledger and checking `requested ⊆ held` via the REAL
//!   [`dregg_cell::is_attenuation`] (e.g. an app asking to *draw* into a surface
//!   it only holds a read-only mirror of is refused — the same direction the
//!   kernel's cap-rights check enforces locally).
//! - [`SurfaceBacking::delegate`] runs a GENUINE `Effect::GrantCapability` turn
//!   through [`dregg_turn::TurnExecutor::execute`], so handing a window to
//!   another cell gates on `granted ⊆ held` enforced by the real executor. A
//!   WIDENING surface grant (handing out *more* rights over the glass than you
//!   hold — e.g. promoting a read-only mirror to a writable surface) is rejected
//!   by the executor with `DelegationDenied`. There is no separate "surface
//!   authority" to reinvent; the compositor multiplexes capabilities, it does
//!   not mint authority.
//!
//! The payoff this makes load-bearing: "a window = a cell's surface capability"
//! is REAL, validated by a turn against the deployed executor, with zero new
//! trust surface and zero drivers — exactly the bridge the local and
//! distributed backings already proved, reused for the glass.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnExecutor,
    TurnResult,
};

use crate::{Backing, Bounds, Resolution, ResolveError, Rights};

/// The surface backing: a real dregg ledger + executor, where each cell backs a
/// rendered surface (a window). `n` is the number of machines the surfaces are
/// spread across; `n = 1` is the firmament's collapsed limit — the compositor
/// and the apps share one box, so a surface revoke is immediate (the glass goes
/// dark the instant the syscall returns) and a present is synchronous.
pub struct SurfaceBacking {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The distance parameter for THIS surface fabric (how spread the surface
    /// cells are). `n = 1` = compositor + apps co-located; `n > 1` = a surface
    /// whose backing cell lives on another machine (a remote window).
    pub n: u32,
}

impl SurfaceBacking {
    /// A fresh single-machine (`n = 1`) surface fabric with an empty ledger.
    pub fn new() -> Self {
        SurfaceBacking {
            ledger: Ledger::new(),
            executor: TurnExecutor::new(ComputronCosts::zero()),
            n: 1,
        }
    }

    /// Set the distance parameter (the number of machines the surfaces span).
    /// `n = 1` keeps the strong local bounds (immediate dark-on-revoke,
    /// synchronous present); `n > 1` relaxes them (a remote window over the
    /// wire — the same reach-out the distributed backing models).
    pub fn with_distance(mut self, n: u32) -> Self {
        self.n = n;
        self
    }

    /// Seed a SURFACE cell into the real ledger with permissive permissions,
    /// returning its [`CellId`]. This is the cell whose state is rendered as a
    /// window; the deterministic key derivation mirrors the protocol-test
    /// generators so surfaces are addressable by seed.
    pub fn seed_surface(&mut self, seed: u8) -> CellId {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(7);
        let mut cell = Cell::with_balance(pk, [0u8; 32], 10_000);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let id = cell.id();
        self.ledger.insert_cell(cell).expect("seed surface cell");
        id
    }

    /// Grant `holder` an ORIGINAL capability over the `surface` cell with
    /// `rights` — the compositor minting a window handle into an app's c-list
    /// (the powerbox handing an app a surface). The compositor multiplexes
    /// capabilities; it does not invent authority — so this is the SAME
    /// original-grant shape as [`crate::DistributedBacking::install`].
    pub fn install(&mut self, holder: CellId, surface: CellId, rights: Rights) {
        let cell = self.ledger.get_mut(&holder).expect("holder cell exists");
        // Replace any auto-granted cap to `surface` with one at exactly `rights`.
        if let Some(slot) = cell.capabilities.lookup_by_target(&surface).map(|c| c.slot) {
            cell.capabilities.revoke(slot);
        }
        cell.capabilities.grant(surface, rights);
    }

    /// Resolve (invoke) a holder's capability over a `surface` with `rights` —
    /// e.g. presenting/drawing into the window.
    ///
    /// Models a turn that resolves the surface cap against real cell-state: the
    /// held cap must exist and cover the requested `rights` (`requested ⊆ held`,
    /// the REAL [`dregg_cell::is_attenuation`]). An app holding only a
    /// read-only mirror that asks for a wider authority than it holds is refused
    /// — the same cap-rights direction the kernel enforces for a local frame.
    /// Returns a [`Resolution`] with the `n`-parametrized bounds (collapsing to
    /// strong-local at `n = 1`).
    pub fn invoke(
        &self,
        holder: CellId,
        surface: CellId,
        rights: &Rights,
    ) -> Result<Resolution, ResolveError> {
        let cell = self.ledger.get(&holder).ok_or(ResolveError::TargetNotFound)?;
        let held = cell
            .capabilities
            .lookup_by_target(&surface)
            .ok_or(ResolveError::TargetNotFound)?;
        if !dregg_cell::is_attenuation(&held.permissions, rights) {
            return Err(ResolveError::Unauthorized(format!(
                "dregg surface cap-authority check: requested {:?} exceeds held {:?} over surface",
                rights, held.permissions
            )));
        }
        Ok(Resolution {
            backing: Backing::DistributedTurn,
            bounds: Bounds::distributed(self.n),
            note: format!(
                "turn resolved surface cap (held {:?}, n={})",
                held.permissions, self.n
            ),
        })
    }

    /// `recKDelegateAtten` for a SURFACE — handing a window to another cell,
    /// run as a GENUINE turn through the real executor.
    ///
    /// `granter` issues `Effect::GrantCapability(surface, narrower)` to
    /// `recipient` (e.g. sharing a clipped read-only view of a window with
    /// another app). The REAL executor enforces `granted ⊆ held`: it commits
    /// iff the surface grant is attenuating, and rejects with `DelegationDenied`
    /// otherwise. A WIDENING surface grant — handing out more authority over the
    /// glass than you hold — is refused by the executor, byte-for-byte the
    /// deployed semantics. Returns `Ok(())` on a committed (attenuating) grant;
    /// `Err(BackingRejected)` if the executor refused.
    pub fn delegate(
        &mut self,
        granter: CellId,
        recipient: CellId,
        surface: CellId,
        narrower: Rights,
    ) -> Result<(), ResolveError> {
        let nonce = self.ledger.get(&granter).expect("granter exists").state.nonce();
        let cap = CapabilityRef {
            target: surface,
            slot: 0, // rewritten by the executor on grant
            permissions: narrower,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        let action = Action {
            target: granter,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![Effect::GrantCapability { from: granter, to: recipient, cap }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        let turn = Turn {
            agent: granter,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let result = self.executor.execute(&turn, &mut self.ledger);
        match result {
            r if r.is_committed() => Ok(()),
            TurnResult::Rejected { reason, .. } => Err(ResolveError::BackingRejected(format!(
                "executor refused surface grant: {:?}",
                reason
            ))),
            other => Err(ResolveError::BackingRejected(format!("unexpected: {:?}", other))),
        }
    }

    /// Does `recipient` hold a cap over the `surface`? (Used to confirm a
    /// window-share landed — the surface analog of
    /// [`crate::DistributedBacking::holds_cap`].)
    pub fn holds_cap(&self, recipient: CellId, surface: CellId) -> bool {
        self.ledger
            .get(&recipient)
            .map(|c| c.capabilities.lookup_by_target(&surface).is_some())
            .unwrap_or(false)
    }

    /// The rights `recipient` holds over the `surface`, if any.
    pub fn rights_held(&self, recipient: CellId, surface: CellId) -> Option<Rights> {
        self.ledger
            .get(&recipient)
            .and_then(|c| c.capabilities.lookup_by_target(&surface).map(|r| r.permissions.clone()))
    }
}

impl Default for SurfaceBacking {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_executor_enforces_attenuation_on_surface_share() {
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let other = fab.seed_surface(1);
        let window = fab.seed_surface(2);

        // The app holds a writable (Either) surface cap over the window.
        fab.install(app, window, AuthRequired::Either);

        // Sharing a NARROWER view (Either -> Signature, a read-only-mirror-shaped
        // narrowing) COMMITS through the real executor.
        assert!(fab
            .delegate(app, other, window, AuthRequired::Signature)
            .is_ok());
        assert!(fab.holds_cap(other, window));
        assert_eq!(
            fab.rights_held(other, window),
            Some(AuthRequired::Signature)
        );
    }

    #[test]
    fn real_executor_rejects_widening_surface_share() {
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let other = fab.seed_surface(1);
        let window = fab.seed_surface(2);

        // The app holds only a read-only mirror (Signature) of the window.
        fab.install(app, window, AuthRequired::Signature);

        // Handing out a WIDER surface authority (Signature -> None, promoting a
        // read-only mirror to a fully-authorized surface) is REJECTED by the
        // real executor (DelegationDenied), and the other app gets nothing.
        let r = fab.delegate(app, other, window, AuthRequired::None);
        assert!(r.is_err());
        assert!(!fab.holds_cap(other, window));
    }
}
