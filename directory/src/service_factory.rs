//! **Service-FACTORY crafting** — craft a factory whose creations ARE services.
//!
//! Where [`crate::Directory`] is the name→handle table and
//! [`crate::service_index::ServiceIndex`] is the discover-by-interface index, a
//! [`ServiceFactory`] is the *constructor* side: it crafts a
//! [`dregg_cell::factory::FactoryDescriptor`] that PRODUCES service cells. A cell
//! born from a service factory is, by construction, a cell that publishes a known
//! [`InterfaceDescriptor`] — so it is immediately discoverable in the directory
//! and announces exactly the interface the factory was crafted for.
//!
//! # The crafting move
//!
//! A cell publishes a service interface by doing method-dispatch: a
//! [`CellProgram::Cases`] program with [`TransitionGuard::MethodIs`] guards
//! auto-derives its [`InterfaceDescriptor`]
//! ([`InterfaceDescriptor::derive_replayable`], the cells-as-service-objects
//! model). [`ServiceFactory::craft`] therefore:
//!
//! 1. builds the **interface-publishing child program** — a `Cases` program whose
//!    guards are exactly the crafted method set (plus an `Always` catch-all so a
//!    born cell still commits ordinary housekeeping writes),
//! 2. derives that program's [`InterfaceDescriptor`] — the interface every
//!    creation will publish,
//! 3. binds a [`FactoryDescriptor`] to it: `child_program_vk =
//!    canonical_program_vk(child_program)`, so the constructor contract is
//!    transparently "this factory produces cells running THIS program / THIS
//!    interface". The `factory_vk` is derived from the interface id + mode, so a
//!    service factory's identity is a function of the service it produces.
//!
//! [`ServiceFactory::birth`] then validates a creation against the descriptor (the
//! real [`FactoryDescriptor::validate_creation`] gate) and yields a
//! [`BornService`] — the new cell id (derived `derive_raw(owner, token)`, matching
//! the executor's `apply_create_cell_from_factory`), the interface-publishing
//! program, the published interface, and a factory [`Provenance`]. The born
//! service then [`BornService::announce`]s itself: a canonical announce record
//! whose payload is byte-identical to the `starbridge-v2` service-directory slice
//! (topic `dregg.directory.announce`, data `[interface_id, cell, method_count]`),
//! ready to register into a [`crate::service_index::ServiceIndex`].
//!
//! # The honest seam (named, not hidden)
//!
//! The deployed `Effect::CreateCellFromFactory` executor arm
//! (`turn/src/executor/apply.rs`) installs the born cell's `program` from the
//! descriptor's *perpetual slot caveats* as `CellProgram::Predicate(...)` plus the
//! child-VK identifier — it does NOT yet install a `Cases` interface-publishing
//! program. So a literally-on-ledger factory birth would publish the EMPTY
//! interface. This module models the birth at the crafting layer (binding the
//! `Cases` program by VK and carrying it on the [`BornService`]), which is the
//! faithful description the renderer-independent card and the executor read; the
//! executor program-install (so an on-ledger birth publishes the `Cases`
//! interface, not just the Predicate caveats) is the named, VK-touching follow-on.

use dregg_cell::CellMode;
use dregg_cell::factory::{
    CapGrant, CapTarget, CapTemplate, FactoryCreationParams, FactoryDescriptor, FactoryError,
    Provenance, canonical_program_vk,
};
use dregg_cell::id::CellId;
use dregg_cell::interface::{InterfaceDescriptor, Symbol, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};

/// The canonical announce topic — the symbol an announcement carries. Identical to
/// the `starbridge-v2` service-directory slice's `announce_topic`, so an
/// announcement crafted here and one emitted from the cockpit match byte-for-byte.
pub fn announce_topic() -> Symbol {
    method_symbol("dregg.directory.announce")
}

/// **A crafted factory that produces SERVICE cells.**
///
/// Holds the [`FactoryDescriptor`] (the constructor contract a validator inspects),
/// the interface-publishing child [`CellProgram`] every creation runs, and the
/// [`InterfaceDescriptor`] that program publishes.
#[derive(Clone, Debug)]
pub struct ServiceFactory {
    descriptor: FactoryDescriptor,
    child_program: CellProgram,
    interface: InterfaceDescriptor,
}

impl ServiceFactory {
    /// **Craft a service factory** whose creations publish exactly `methods`.
    ///
    /// `methods` is the set of method names the produced service offers; `mode`
    /// is whether creations are sovereign or hosted. Duplicate method names
    /// collapse to one method (the interface is auto-derived + deduplicated).
    pub fn craft(methods: &[&str], mode: CellMode) -> Self {
        let child_program = interface_publishing_program(methods);
        let interface = InterfaceDescriptor::derive_replayable(&child_program);
        let child_program_vk = canonical_program_vk(&child_program);
        let factory_vk = derive_service_factory_vk(&interface.interface_id, &mode);

        let descriptor = FactoryDescriptor {
            factory_vk,
            child_program_vk: Some(child_program_vk),
            child_vk_strategy: None,
            // A born service holds one self-cap: the owner's authority over its
            // own cell. Signature-gated, non-attenuatable — the baseline a
            // service needs to take its own owner-signed turns.
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            }],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: mode,
            creation_budget: None,
        };

        ServiceFactory {
            descriptor,
            child_program,
            interface,
        }
    }

    /// The constructor contract — what this factory is allowed to produce.
    pub fn descriptor(&self) -> &FactoryDescriptor {
        &self.descriptor
    }

    /// The factory's own VK hash (its directory identity, a function of the
    /// interface it produces + its mode).
    pub fn factory_vk(&self) -> [u8; 32] {
        self.descriptor.factory_vk
    }

    /// The interface every creation publishes.
    pub fn interface(&self) -> &InterfaceDescriptor {
        &self.interface
    }

    /// The interface-publishing child program every creation runs.
    pub fn child_program(&self) -> &CellProgram {
        &self.child_program
    }

    /// The creation parameters this factory uses to birth a service for the given
    /// owner / token domain (the child program VK, a self-cap grant).
    fn creation_params(&self, owner_pubkey: [u8; 32]) -> FactoryCreationParams {
        FactoryCreationParams {
            mode: self.descriptor.default_mode.clone(),
            program_vk: self.descriptor.child_program_vk,
            initial_fields: vec![],
            initial_caps: vec![CapGrant {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: false,
            }],
            owner_pubkey,
        }
    }

    /// **Birth a service** from this factory — a new cell that publishes the
    /// factory's interface.
    ///
    /// Validates the creation against the descriptor (the real
    /// [`FactoryDescriptor::validate_creation`] gate — a forged child VK, an
    /// out-of-template cap, or a mode mismatch is refused here), then derives the
    /// new cell id exactly as the executor does (`derive_raw(owner, token)`) and
    /// returns the [`BornService`]. The born service's program is the
    /// interface-publishing `Cases` program, so its [`BornService::derived_interface`]
    /// equals this factory's [`Self::interface`].
    pub fn birth(
        &self,
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        height: u64,
    ) -> Result<BornService, FactoryError> {
        let params = self.creation_params(owner_pubkey);
        self.descriptor.validate_creation(&params)?;

        let cell = CellId::derive_raw(&owner_pubkey, &token_id);
        Ok(BornService {
            cell,
            program: self.child_program.clone(),
            interface: self.interface.clone(),
            provenance: Provenance::from_factory(self.descriptor.factory_vk, None, height),
            mode: self.descriptor.default_mode.clone(),
        })
    }
}

/// **A service cell born from a [`ServiceFactory`].**
///
/// Carries the new cell id, the interface-publishing program, the interface it
/// publishes, and the factory [`Provenance`] (who created it, under what factory
/// VK). A born service is immediately discoverable (its
/// [`Self::derived_interface`]) and announceable ([`Self::announce`]).
#[derive(Clone, Debug)]
pub struct BornService {
    /// The new cell's id (`derive_raw(owner, token)`, matching the executor).
    pub cell: CellId,
    /// The interface-publishing program the cell runs.
    pub program: CellProgram,
    /// The interface the cell publishes (carried for convenience; equals
    /// [`Self::derived_interface`]).
    pub interface: InterfaceDescriptor,
    /// The factory provenance (which factory VK created this cell).
    pub provenance: Provenance,
    /// Whether the born cell is sovereign or hosted.
    pub mode: CellMode,
}

impl BornService {
    /// Re-derive the interface the born cell ACTUALLY publishes from its live
    /// program — the same `derive_replayable` a `discover()` scan runs. A faithful
    /// birth yields `derived_interface().interface_id == self.interface.interface_id`.
    pub fn derived_interface(&self) -> InterfaceDescriptor {
        InterfaceDescriptor::derive_replayable(&self.program)
    }

    /// Whether the born cell genuinely publishes the interface named by
    /// `interface_id` — re-derived from its program, not trusted from a flag.
    pub fn publishes(&self, interface_id: &[u8; 32]) -> bool {
        self.derived_interface().interface_id == *interface_id
    }

    /// **Auto-announce** this born service — the publish half.
    ///
    /// Produces the canonical [`AnnounceRecord`] (`announcer`'s turn references the
    /// service). The record's payload is byte-identical to the `starbridge-v2`
    /// service-directory slice's `Effect::EmitEvent` data, so an announcement
    /// crafted here can be wrapped into a real verified turn by the caller and a
    /// `discover()` scan reads it back the same way.
    pub fn announce(&self, announcer: CellId) -> AnnounceRecord {
        AnnounceRecord {
            topic: announce_topic(),
            interface_id: self.interface.interface_id,
            service: self.cell,
            method_count: self.interface.methods.len(),
            announcer,
        }
    }
}

/// **A service announcement record** — the publish event, renderer-independent.
///
/// The same shape the `starbridge-v2` slice emits as an `Effect::EmitEvent` and the
/// same a `discover()` scan reads back. Kept dependency-light (no `dregg-turn`):
/// the caller wraps [`Self::event_data`] into the announcer's verified turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnnounceRecord {
    /// The announce topic (`dregg.directory.announce`).
    pub topic: Symbol,
    /// The announced service's interface content-address.
    pub interface_id: [u8; 32],
    /// The announced service cell.
    pub service: CellId,
    /// How many methods the announced interface publishes.
    pub method_count: usize,
    /// The announcer (the operator whose turn carries this — NOT the service).
    pub announcer: CellId,
}

impl AnnounceRecord {
    /// The `Effect::EmitEvent` `data` felts: `[interface_id, service_cell,
    /// method_count]`. Identical to the `starbridge-v2` slice's announce payload.
    pub fn event_data(&self) -> Vec<[u8; 32]> {
        let mut count_felt = [0u8; 32];
        count_felt[..8].copy_from_slice(&(self.method_count as u64).to_le_bytes());
        vec![self.interface_id, *self.service.as_bytes(), count_felt]
    }
}

/// Build the interface-publishing child program: a [`CellProgram::Cases`] with one
/// [`TransitionGuard::MethodIs`] case per method, plus an `Always` catch-all so a
/// born cell still commits ordinary (non-method) housekeeping writes. The
/// `Always` case contributes no method to the derived interface — `derive_replayable`
/// collects only `MethodIs` guards.
fn interface_publishing_program(methods: &[&str]) -> CellProgram {
    let mut cases: Vec<TransitionCase> = methods
        .iter()
        .map(|name| TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(name),
            },
            constraints: vec![],
        })
        .collect();
    cases.push(TransitionCase {
        guard: TransitionGuard::Always,
        constraints: vec![],
    });
    CellProgram::Cases(cases)
}

/// Derive a service factory's VK from the interface it produces + its mode, so the
/// factory's directory identity is a deterministic function of the service it
/// crafts.
fn derive_service_factory_vk(interface_id: &[u8; 32], mode: &CellMode) -> [u8; 32] {
    let mode_byte = match mode {
        CellMode::Hosted => 0u8,
        CellMode::Sovereign => 1u8,
    };
    let mut hasher = blake3::Hasher::new_derive_key("dregg-service-factory-vk-v1");
    hasher.update(interface_id);
    hasher.update(&[mode_byte]);
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn craft_binds_the_factory_to_the_interface_it_produces() {
        let f = ServiceFactory::craft(&["send", "dequeue"], CellMode::Hosted);

        // The factory's interface is exactly the crafted method set.
        assert_eq!(f.interface().methods.len(), 2);
        assert!(f.interface().method(&method_symbol("send")).is_some());
        assert!(f.interface().method(&method_symbol("dequeue")).is_some());

        // The descriptor binds the child program VK to that exact program.
        assert_eq!(
            f.descriptor().child_program_vk,
            Some(canonical_program_vk(f.child_program()))
        );
        // The factory identity is a function of the interface it produces.
        let same = ServiceFactory::craft(&["dequeue", "send"], CellMode::Hosted);
        assert_eq!(
            f.factory_vk(),
            same.factory_vk(),
            "same interface + mode ⇒ same factory vk (order-independent)"
        );
        let other = ServiceFactory::craft(&["send"], CellMode::Hosted);
        assert_ne!(f.factory_vk(), other.factory_vk());
        // Mode is part of the factory identity.
        let sov = ServiceFactory::craft(&["send", "dequeue"], CellMode::Sovereign);
        assert_ne!(f.factory_vk(), sov.factory_vk());
    }

    #[test]
    fn birth_produces_a_service_that_publishes_the_interface() {
        let f = ServiceFactory::craft(&["write", "read"], CellMode::Hosted);
        let born = f.birth([0x11; 32], [0x22; 32], 100).unwrap();

        // The cell id matches the executor's own derivation.
        assert_eq!(born.cell, CellId::derive_raw(&[0x11; 32], &[0x22; 32]));

        // THE KEY FACT: the born service genuinely publishes the factory's
        // interface — re-derived from its live program, not trusted from a flag.
        assert!(born.publishes(&f.interface().interface_id));
        assert_eq!(
            born.derived_interface().interface_id,
            f.interface().interface_id
        );

        // Provenance records the crafting factory.
        assert_eq!(born.provenance.created_by_factory, Some(f.factory_vk()));
    }

    #[test]
    fn born_service_announces_the_interface_it_publishes() {
        let f = ServiceFactory::craft(&["ping"], CellMode::Hosted);
        let born = f.birth([0x33; 32], [0x44; 32], 7).unwrap();
        let announcer = CellId::derive_raw(&[0xAA; 32], &[0xBB; 32]);

        let rec = born.announce(announcer);
        assert_eq!(rec.topic, announce_topic());
        assert_eq!(rec.interface_id, f.interface().interface_id);
        assert_eq!(rec.service, born.cell);
        assert_eq!(rec.method_count, 1);
        assert_eq!(rec.announcer, announcer);

        // The payload's first felt is the announced interface_id, exactly the
        // shape a `discover()` scan reads back (the slice's announce data layout).
        let data = rec.event_data();
        assert_eq!(data.len(), 3);
        assert_eq!(data[0], f.interface().interface_id);
        assert_eq!(data[1], *born.cell.as_bytes());
        assert_eq!(u64::from_le_bytes(data[2][..8].try_into().unwrap()), 1);
    }

    #[test]
    fn birth_validates_against_the_real_factory_gate() {
        // A born cell from a well-formed craft always validates (the self-cap
        // grant is within the crafted template, the child VK matches).
        let f = ServiceFactory::craft(&["m"], CellMode::Sovereign);
        assert!(f.birth([1; 32], [2; 32], 0).is_ok());

        // The descriptor's own gate refuses a creation whose child VK lies — an
        // over-reach the factory layer catches before any cell is born.
        let mut bad_params = f.creation_params([1; 32]);
        bad_params.program_vk = Some([0xFF; 32]); // not the crafted child VK
        let err = f.descriptor().validate_creation(&bad_params).unwrap_err();
        assert!(matches!(err, FactoryError::ProgramMismatch { .. }));
    }
}
