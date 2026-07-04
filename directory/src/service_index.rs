//! **Discover services by INTERFACE and by METHOD** — the deepened discovery
//! face, plus federation-wide scope.
//!
//! The base [`crate::Directory`] discovers by name / tag / [`crate::EntryKind`].
//! A *service* directory wants more: find every cell that offers interface `X`, or
//! every cell that offers method `Y`, by the cells-as-service-objects model. A
//! [`ServiceIndex`] adds that — it keys announced services by name like the base
//! directory, but each record carries the service's [`InterfaceDescriptor`], so:
//!
//! - [`ServiceIndex::discover_by_interface`] finds every live service whose
//!   interface content-address matches a target `interface_id`.
//! - [`ServiceIndex::discover_by_method`] finds every live service that offers a
//!   given method symbol — resolved through the SAME verified `dregg-dfa` router
//!   the executor's dispatch uses ([`InterfaceDescriptor::route_method`]), not an
//!   ad-hoc scan.
//! - [`ServiceIndex::membership_witness`] produces the light-client-witnessable
//!   proof that a discovered service genuinely offers a method (the existing DFA
//!   route-membership AIR), so discovery is not a trusted claim.
//!
//! Announcement is gated by the anti-forgery tooth [`InterfaceDescriptor::verify_id`]:
//! a record whose carried `interface_id` does not match its own methods is
//! refused ([`ServiceIndexError::ForgedInterface`]) — you cannot announce a service
//! under an interface id it does not actually publish.
//!
//! Revocation + expiry mirror the base directory: a revoked or expired record is
//! invisible to discovery and lookup, [`ServiceIndex::gc_expired`] sweeps it.
//!
//! # Federation scope
//!
//! [`FederatedServiceIndex`] composes a local [`ServiceIndex`] with peer indices,
//! catalogued by a [`crate::MetaDirectory`] (the directory-of-directories for
//! federation peer discovery). `discover_by_interface` / `discover_by_method` then
//! sweep the local image AND every peer federation, tagging each hit with the
//! federation it came from — the whole-federation sibling of the local scan,
//! the model a "local ⇄ federation" toggle reads.

use std::collections::BTreeMap;

use dregg_cell::interface::{InterfaceDescriptor, Symbol};

use crate::service_factory::BornService;
use crate::{DiscoveryFilter, EntryKind, MetaDirectory, PeerHandle, ResourceHandle};

/// One **announced service** in the index — a directory entry enriched with the
/// service's typed interface, so it can be found by interface or by method.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceRecord {
    /// The legible directory name the service is announced under.
    pub name: String,
    /// The sturdy-ref handle that resolves to the service cell.
    pub handle: ResourceHandle,
    /// The service's published interface (its method set + content-address).
    pub interface: InterfaceDescriptor,
    /// What kind of resource this is (typically [`EntryKind::Service`]).
    pub kind: EntryKind,
    /// Filtering tags.
    pub tags: Vec<String>,
    /// Block height at announcement.
    pub announced_at: u64,
    /// Optional expiry height. `None` = no expiry.
    pub expires_at: Option<u64>,
    /// Whether the announcement has been revoked.
    pub revoked: bool,
}

impl ServiceRecord {
    /// Whether this record is live at `height` — neither revoked nor expired.
    pub fn is_live(&self, height: u64) -> bool {
        if self.revoked {
            return false;
        }
        match self.expires_at {
            Some(exp) => height <= exp,
            None => true,
        }
    }
}

/// Errors an announcement / lookup can raise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServiceIndexError {
    /// The interface descriptor's carried id does not match its own methods — a
    /// forged descriptor. You cannot announce a service under an interface id it
    /// does not actually publish.
    ForgedInterface { name: String },
    /// The name is already announced with a different service.
    AlreadyAnnounced { name: String },
    /// The named service is absent.
    NotFound { name: String },
    /// The named service is revoked.
    Revoked { name: String },
    /// The named service has expired.
    Expired { name: String },
}

impl std::fmt::Display for ServiceIndexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ForgedInterface { name } => {
                write!(f, "announcement '{name}' carries a forged interface id")
            }
            Self::AlreadyAnnounced { name } => {
                write!(
                    f,
                    "service '{name}' already announced with a different value"
                )
            }
            Self::NotFound { name } => write!(f, "service not found: '{name}'"),
            Self::Revoked { name } => write!(f, "service '{name}' has been revoked"),
            Self::Expired { name } => write!(f, "service '{name}' has expired"),
        }
    }
}

impl std::error::Error for ServiceIndexError {}

/// **An index of announced services, discoverable by interface and by method.**
///
/// Records are keyed by announced name (sorted, so discovery order is
/// deterministic). The local federation id tags hits when this index is composed
/// into a [`FederatedServiceIndex`].
#[derive(Clone, Debug)]
pub struct ServiceIndex {
    federation_id: [u8; 32],
    records: BTreeMap<String, ServiceRecord>,
}

impl ServiceIndex {
    /// A new, empty index for the given federation.
    pub fn new(federation_id: [u8; 32]) -> Self {
        ServiceIndex {
            federation_id,
            records: BTreeMap::new(),
        }
    }

    /// The federation this index catalogs.
    pub fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    /// **ANNOUNCE** a service under `name`, carrying its interface.
    ///
    /// Refuses a forged descriptor (one whose carried `interface_id` does not match
    /// its methods) and a name collision with a different existing service.
    #[allow(clippy::too_many_arguments)]
    pub fn announce(
        &mut self,
        name: &str,
        handle: ResourceHandle,
        interface: InterfaceDescriptor,
        kind: EntryKind,
        tags: Vec<String>,
        height: u64,
        expires_at: Option<u64>,
    ) -> Result<(), ServiceIndexError> {
        // Anti-forgery tooth: the descriptor must hash to its own id.
        if !interface.verify_id() {
            return Err(ServiceIndexError::ForgedInterface {
                name: name.to_string(),
            });
        }

        if let Some(existing) = self.records.get(name) {
            // Idempotent on the same (handle, interface); conflict otherwise.
            let same = existing.handle == handle
                && existing.interface.interface_id == interface.interface_id
                && !existing.revoked;
            if !same {
                return Err(ServiceIndexError::AlreadyAnnounced {
                    name: name.to_string(),
                });
            }
        }

        self.records.insert(
            name.to_string(),
            ServiceRecord {
                name: name.to_string(),
                handle,
                interface,
                kind,
                tags,
                announced_at: height,
                expires_at,
                revoked: false,
            },
        );
        Ok(())
    }

    /// **Announce a freshly-[`BornService`]** to this index — the slice-1↔slice-2
    /// weld: a crafted service factory births a service, and the service announces
    /// itself into the directory under `name`. The handle resolves to the born
    /// cell in this index's federation with the given `swiss` bearer secret; the
    /// kind is [`EntryKind::Service`]; the interface is the one the cell publishes.
    pub fn announce_born(
        &mut self,
        name: &str,
        born: &BornService,
        swiss: [u8; 32],
        tags: Vec<String>,
        expires_at: Option<u64>,
    ) -> Result<(), ServiceIndexError> {
        let handle = ResourceHandle::new(self.federation_id, *born.cell.as_bytes(), swiss);
        self.announce(
            name,
            handle,
            born.interface.clone(),
            EntryKind::Service,
            tags,
            born.provenance.creation_height,
            expires_at,
        )
    }

    /// **DISCOVER BY INTERFACE** — every live service whose interface
    /// content-address matches `interface_id`.
    pub fn discover_by_interface(
        &self,
        interface_id: &[u8; 32],
        height: u64,
    ) -> Vec<&ServiceRecord> {
        self.records
            .values()
            .filter(|r| r.is_live(height) && r.interface.interface_id == *interface_id)
            .collect()
    }

    /// **DISCOVER BY METHOD** — every live service that offers `method`, resolved
    /// through the verified `dregg-dfa` router ([`InterfaceDescriptor::route_method`]),
    /// the same dispatch the executor uses. An undeclared method finds nothing
    /// (fail-closed).
    pub fn discover_by_method(&self, method: &Symbol, height: u64) -> Vec<&ServiceRecord> {
        self.records
            .values()
            .filter(|r| r.is_live(height) && r.interface.route_method(method).is_some())
            .collect()
    }

    /// **DISCOVER by directory filter** — name prefix / required tags / kind, over
    /// live records (revoked + expired excluded; `include_revoked` re-admits
    /// revoked but expiry is always enforced).
    pub fn discover(&self, filter: &DiscoveryFilter, height: u64) -> Vec<&ServiceRecord> {
        self.records
            .values()
            .filter(|r| {
                // Expiry is always enforced; revocation is filter-controlled.
                let expired = matches!(r.expires_at, Some(exp) if height > exp);
                if expired {
                    return false;
                }
                if r.revoked && !filter.include_revoked {
                    return false;
                }
                if let Some(prefix) = &filter.name_prefix {
                    if !r.name.starts_with(prefix) {
                        return false;
                    }
                }
                if let Some(kind) = &filter.kind {
                    if &r.kind != kind {
                        return false;
                    }
                }
                if !filter.required_tags.is_empty() {
                    let tagset: std::collections::HashSet<&String> = r.tags.iter().collect();
                    if !filter.required_tags.iter().all(|t| tagset.contains(t)) {
                        return false;
                    }
                }
                true
            })
            .collect()
    }

    /// The light-client-witnessable proof that the service announced under `name`
    /// genuinely offers `method` — the serialized DFA route-membership `AirTrace`
    /// together with the route-table root it binds. `None` if the service is
    /// absent, not live, or does not offer the method (fail-closed). The caller
    /// re-checks via [`InterfaceDescriptor::verify_route_membership`].
    pub fn membership_witness(
        &self,
        name: &str,
        method: &Symbol,
        height: u64,
    ) -> Option<(Vec<u8>, [u8; 32])> {
        let record = self.records.get(name)?;
        if !record.is_live(height) {
            return None;
        }
        record.interface.route_membership_witness(method)
    }

    /// Look up a service by name, with revocation + expiry errors.
    pub fn lookup(&self, name: &str, height: u64) -> Result<&ServiceRecord, ServiceIndexError> {
        let record = self
            .records
            .get(name)
            .ok_or_else(|| ServiceIndexError::NotFound {
                name: name.to_string(),
            })?;
        if record.revoked {
            return Err(ServiceIndexError::Revoked {
                name: name.to_string(),
            });
        }
        if matches!(record.expires_at, Some(exp) if height > exp) {
            return Err(ServiceIndexError::Expired {
                name: name.to_string(),
            });
        }
        Ok(record)
    }

    /// Revoke an announcement. Subsequent discovery + lookup skip it.
    pub fn revoke(&mut self, name: &str) -> Result<(), ServiceIndexError> {
        let record = self
            .records
            .get_mut(name)
            .ok_or_else(|| ServiceIndexError::NotFound {
                name: name.to_string(),
            })?;
        record.revoked = true;
        Ok(())
    }

    /// Drop expired records. Returns the count removed.
    pub fn gc_expired(&mut self, height: u64) -> usize {
        let before = self.records.len();
        self.records.retain(|_, r| match r.expires_at {
            Some(exp) => height <= exp,
            None => true,
        });
        before - self.records.len()
    }

    /// Number of records (including revoked, pre-GC).
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Whether the index has no records.
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }
}

/// A discovery hit from a [`FederatedServiceIndex`], tagged with its origin.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FederatedHit<'a> {
    /// The federation the hit came from.
    pub federation_id: [u8; 32],
    /// Whether the hit is in the local image (vs. a peer federation).
    pub local: bool,
    /// The discovered service record.
    pub record: &'a ServiceRecord,
}

/// **A federation-wide service index** — a local [`ServiceIndex`] plus peer
/// indices catalogued by a [`MetaDirectory`].
///
/// `discover_by_interface` / `discover_by_method` sweep the local image first, then
/// each peer federation in the meta-directory's (sorted) peer order, tagging every
/// hit with its origin federation. This is the whole-federation sibling of the
/// local scan: the same query, widened to peers.
#[derive(Clone, Debug)]
pub struct FederatedServiceIndex {
    local: ServiceIndex,
    peers: BTreeMap<[u8; 32], ServiceIndex>,
    meta: MetaDirectory,
}

impl FederatedServiceIndex {
    /// A federation index over the given local image, with no peers yet.
    pub fn new(local: ServiceIndex) -> Self {
        FederatedServiceIndex {
            local,
            peers: BTreeMap::new(),
            meta: MetaDirectory::new(),
        }
    }

    /// Register a peer federation: catalog its [`PeerHandle`] in the meta-directory
    /// and attach its service index. Keyed by the peer's federation id.
    pub fn add_peer(&mut self, peer: PeerHandle, index: ServiceIndex) {
        let fed = peer.federation_id;
        self.meta.add_peer(peer);
        self.peers.insert(fed, index);
    }

    /// The local service index.
    pub fn local(&self) -> &ServiceIndex {
        &self.local
    }

    /// The local service index, mutably (to announce into it).
    pub fn local_mut(&mut self) -> &mut ServiceIndex {
        &mut self.local
    }

    /// The peer catalog (the directory-of-directories backing federation scope).
    pub fn meta(&self) -> &MetaDirectory {
        &self.meta
    }

    /// A peer federation's index by id.
    pub fn peer(&self, federation_id: &[u8; 32]) -> Option<&ServiceIndex> {
        self.peers.get(federation_id)
    }

    /// **DISCOVER BY INTERFACE across the federation** — local first, then each
    /// peer in the meta-directory's peer order.
    pub fn discover_by_interface(
        &self,
        interface_id: &[u8; 32],
        height: u64,
    ) -> Vec<FederatedHit<'_>> {
        let mut hits: Vec<FederatedHit<'_>> = self
            .local
            .discover_by_interface(interface_id, height)
            .into_iter()
            .map(|record| FederatedHit {
                federation_id: self.local.federation_id(),
                local: true,
                record,
            })
            .collect();
        for peer in self.meta.peers() {
            if let Some(index) = self.peers.get(&peer.federation_id) {
                for record in index.discover_by_interface(interface_id, height) {
                    hits.push(FederatedHit {
                        federation_id: peer.federation_id,
                        local: false,
                        record,
                    });
                }
            }
        }
        hits
    }

    /// **DISCOVER BY METHOD across the federation** — local first, then each peer.
    pub fn discover_by_method(&self, method: &Symbol, height: u64) -> Vec<FederatedHit<'_>> {
        let mut hits: Vec<FederatedHit<'_>> = self
            .local
            .discover_by_method(method, height)
            .into_iter()
            .map(|record| FederatedHit {
                federation_id: self.local.federation_id(),
                local: true,
                record,
            })
            .collect();
        for peer in self.meta.peers() {
            if let Some(index) = self.peers.get(&peer.federation_id) {
                for record in index.discover_by_method(method, height) {
                    hits.push(FederatedHit {
                        federation_id: peer.federation_id,
                        local: false,
                        record,
                    });
                }
            }
        }
        hits
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::service_factory::ServiceFactory;
    use dregg_cell::CellMode;
    use dregg_cell::interface::method_symbol;

    fn handle(seed: u8) -> ResourceHandle {
        ResourceHandle::new(
            [seed; 32],
            [seed.wrapping_add(1); 32],
            [seed.wrapping_add(2); 32],
        )
    }

    /// THE END-TO-END WELD: craft a service factory → birth a service → announce it
    /// → discover it by interface AND by method.
    #[test]
    fn crafted_factory_birth_is_announced_and_discoverable_by_interface_and_method() {
        let factory = ServiceFactory::craft(&["send", "dequeue"], CellMode::Hosted);
        let born = factory.birth([0x11; 32], [0x22; 32], 100).unwrap();

        let mut index = ServiceIndex::new([0xFE; 32]);
        index
            .announce_born("mailbox", &born, [0x99; 32], vec!["mail".into()], None)
            .unwrap();

        // Discover by interface: the born service surfaces under the factory's id.
        let by_iface = index.discover_by_interface(&factory.interface().interface_id, 100);
        assert_eq!(by_iface.len(), 1);
        assert_eq!(by_iface[0].handle.cell_id, *born.cell.as_bytes());

        // Discover by method: each offered method finds it; an undeclared one does not.
        assert_eq!(
            index.discover_by_method(&method_symbol("send"), 100).len(),
            1
        );
        assert_eq!(
            index
                .discover_by_method(&method_symbol("dequeue"), 100)
                .len(),
            1
        );
        assert!(
            index
                .discover_by_method(&method_symbol("undeclared"), 100)
                .is_empty(),
            "an over-reach method query finds nothing (fail-closed)"
        );
    }

    #[test]
    fn membership_witness_proves_a_discovered_service_offers_the_method() {
        let factory = ServiceFactory::craft(&["write"], CellMode::Hosted);
        let born = factory.birth([1; 32], [2; 32], 0).unwrap();
        let mut index = ServiceIndex::new([7; 32]);
        index
            .announce_born("store", &born, [3; 32], vec![], None)
            .unwrap();

        // A declared method yields a membership witness that verifies via the DFA AIR.
        let write = method_symbol("write");
        let (proof, root) = index.membership_witness("store", &write, 0).unwrap();
        assert_eq!(root, born.interface.to_route_table().commitment);
        assert!(born.interface.verify_route_membership(&write, &proof));

        // An undeclared method has no witness (fail-closed).
        assert!(
            index
                .membership_witness("store", &method_symbol("nope"), 0)
                .is_none()
        );
    }

    #[test]
    fn announcing_a_forged_interface_is_refused() {
        let mut index = ServiceIndex::new([0; 32]);
        // Build a real interface, then corrupt its carried id so verify_id fails.
        let factory = ServiceFactory::craft(&["m"], CellMode::Hosted);
        let mut forged = factory.interface().clone();
        forged.interface_id = [0xFF; 32];
        assert!(!forged.verify_id());

        let err = index
            .announce("x", handle(1), forged, EntryKind::Service, vec![], 0, None)
            .unwrap_err();
        assert!(matches!(err, ServiceIndexError::ForgedInterface { .. }));
        assert!(index.is_empty(), "no forged service was recorded");
    }

    #[test]
    fn revoke_and_expiry_hide_a_service_from_discovery() {
        let factory = ServiceFactory::craft(&["ping"], CellMode::Hosted);
        let id = factory.interface().interface_id;
        let born = factory.birth([4; 32], [5; 32], 10).unwrap();

        let mut index = ServiceIndex::new([0; 32]);
        index
            .announce_born("svc", &born, [6; 32], vec![], Some(50))
            .unwrap();

        // Live at height 20.
        assert_eq!(index.discover_by_interface(&id, 20).len(), 1);
        // Expired at height 100.
        assert!(index.discover_by_interface(&id, 100).is_empty());
        assert!(matches!(
            index.lookup("svc", 100),
            Err(ServiceIndexError::Expired { .. })
        ));

        // Revoked → invisible even while unexpired.
        index.revoke("svc").unwrap();
        assert!(index.discover_by_interface(&id, 20).is_empty());
        assert!(matches!(
            index.lookup("svc", 20),
            Err(ServiceIndexError::Revoked { .. })
        ));

        // GC at height 100 removes the expired record.
        assert_eq!(index.gc_expired(100), 1);
        assert!(index.is_empty());
    }

    #[test]
    fn discover_by_filter_matches_kind_and_tags() {
        let factory = ServiceFactory::craft(&["m"], CellMode::Hosted);
        let born = factory.birth([1; 32], [2; 32], 0).unwrap();
        let mut index = ServiceIndex::new([0; 32]);
        index
            .announce_born(
                "svc",
                &born,
                [3; 32],
                vec!["storage".into(), "fast".into()],
                None,
            )
            .unwrap();

        // Matching tag + kind.
        let hits = index.discover(
            &DiscoveryFilter {
                required_tags: vec!["storage".into()],
                kind: Some(EntryKind::Service),
                ..Default::default()
            },
            0,
        );
        assert_eq!(hits.len(), 1);

        // A tag it does not carry excludes it.
        let miss = index.discover(
            &DiscoveryFilter {
                required_tags: vec!["oracle".into()],
                ..Default::default()
            },
            0,
        );
        assert!(miss.is_empty());
    }

    #[test]
    fn federation_scope_discovers_local_and_peer_services() {
        // A shared interface offered in two federations.
        let factory = ServiceFactory::craft(&["quote"], CellMode::Hosted);
        let id = factory.interface().interface_id;

        let mut local = ServiceIndex::new([0x01; 32]);
        let local_born = factory.birth([0xA0; 32], [0xA1; 32], 0).unwrap();
        local
            .announce_born("local-quote", &local_born, [0; 32], vec![], None)
            .unwrap();

        let mut peer_index = ServiceIndex::new([0x02; 32]);
        let peer_born = factory.birth([0xB0; 32], [0xB1; 32], 0).unwrap();
        peer_index
            .announce_born("peer-quote", &peer_born, [0; 32], vec![], None)
            .unwrap();

        let mut fed = FederatedServiceIndex::new(local);
        fed.add_peer(
            PeerHandle {
                federation_id: [0x02; 32],
                directory: handle(0x02),
                label: Some("peer-2".into()),
            },
            peer_index,
        );

        // By interface across the federation: local + peer.
        let hits = fed.discover_by_interface(&id, 0);
        assert_eq!(hits.len(), 2);
        assert!(
            hits.iter()
                .any(|h| h.local && h.federation_id == [0x01; 32])
        );
        assert!(
            hits.iter()
                .any(|h| !h.local && h.federation_id == [0x02; 32])
        );

        // By method across the federation, same reach.
        let by_method = fed.discover_by_method(&method_symbol("quote"), 0);
        assert_eq!(by_method.len(), 2);

        // The peer is catalogued in the meta-directory (federation scope's backing).
        assert_eq!(fed.meta().len(), 1);
        assert!(fed.peer(&[0x02; 32]).is_some());
    }
}
