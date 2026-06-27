//! CapTP session state between two federation peers.
//!
//! A `CapSession` tracks the bidirectional capability exchange between two nodes:
//! what we export to the peer, what we import from the peer, and pending promise
//! resolutions.

use std::collections::HashMap;

use dregg_cell::AuthRequired;
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

use crate::StrandId;

/// A CapTP session between two federations/peers.
///
/// Each session tracks:
/// - **Exports**: capabilities we make available to the remote peer
/// - **Imports**: capabilities the remote peer has made available to us
/// - **Promises**: pending asynchronous resolutions (eventual references)
/// - **Epoch**: a monotonically increasing generation counter, preventing stale
///   messages from old sessions from being processed in the new session.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapSession {
    /// The remote peer's identity (typically their federation node ID).
    pub peer_id: [u8; 32],
    /// The remote peer's strand identity in the unified lace model.
    ///
    /// In the unified model, CapTP sessions are bilateral between strands.
    /// When set, this identifies the specific strand we are communicating with.
    /// When `None`, the session uses the legacy `peer_id` (which was a federation/group ID).
    ///
    /// New code should set this; when both `peer_strand` and `peer_id` are set,
    /// prefer `peer_strand` for GC keying and addressing.
    #[serde(default)]
    pub peer_strand: Option<StrandId>,
    /// Session epoch: incremented each time a new session is established with
    /// the same peer. Messages carrying a stale epoch are rejected.
    pub epoch: u64,
    /// Capabilities we export TO this peer.
    pub exports: HashMap<CellId, ExportEntry>,
    /// Capabilities we import FROM this peer.
    pub imports: HashMap<CellId, ImportEntry>,
    /// Promise resolution table (keyed by promise ID).
    pub promises: HashMap<u64, PromiseState>,
    /// Monotonically increasing sequence number for promise IDs.
    next_promise_id: u64,
}

/// An export entry: a capability we make available to the remote peer.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExportEntry {
    /// The local cell being exported.
    pub cell_id: CellId,
    /// What permissions the remote peer has.
    pub permissions: AuthRequired,
    /// Reference count: how many times the remote has imported this.
    pub ref_count: u32,
}

/// An import entry: a capability the remote peer has made available to us.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImportEntry {
    /// The remote cell we have a reference to.
    pub remote_cell_id: CellId,
    /// What permissions we have on the remote cell.
    pub permissions: AuthRequired,
    /// Whether this import is currently live (connected).
    pub live: bool,
}

/// State of a pending promise in the CapTP session.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PromiseState {
    /// The promise is pending — not yet resolved.
    Pending,
    /// The promise resolved to a live capability reference.
    Fulfilled { cell_id: CellId },
    /// The promise was broken (the remote disconnected or revoked).
    Broken { reason: String },
}

impl CapSession {
    /// Create a new CapTP session with a peer (epoch 0).
    pub fn new(peer_id: [u8; 32]) -> Self {
        Self {
            peer_id,
            peer_strand: None,
            epoch: 0,
            exports: HashMap::new(),
            imports: HashMap::new(),
            promises: HashMap::new(),
            next_promise_id: 0,
        }
    }

    /// Create a new CapTP session with an explicit epoch.
    ///
    /// Use this when re-establishing a session with a peer that previously had
    /// a session (the epoch should be incremented from the previous session's epoch).
    pub fn with_epoch(peer_id: [u8; 32], epoch: u64) -> Self {
        Self {
            peer_id,
            peer_strand: None,
            epoch,
            exports: HashMap::new(),
            imports: HashMap::new(),
            promises: HashMap::new(),
            next_promise_id: 0,
        }
    }

    /// Create a new CapTP session addressed by strand ID (unified lace model).
    ///
    /// In the unified model, sessions are bilateral between strands.
    /// The `peer_id` is set to the strand ID for backward compatibility
    /// with code that reads `peer_id`.
    pub fn with_strand(peer_strand: StrandId, epoch: u64) -> Self {
        Self {
            peer_id: peer_strand,
            peer_strand: Some(peer_strand),
            epoch,
            exports: HashMap::new(),
            imports: HashMap::new(),
            promises: HashMap::new(),
            next_promise_id: 0,
        }
    }

    /// Export a capability to the remote peer.
    ///
    /// If the cell is already exported, increments its reference count.
    /// Returns the cell ID that the remote should use to refer to it.
    pub fn export(&mut self, cell_id: CellId, permissions: AuthRequired) -> CellId {
        let entry = self.exports.entry(cell_id).or_insert(ExportEntry {
            cell_id,
            permissions: permissions.clone(),
            ref_count: 0,
        });
        entry.ref_count += 1;
        // Narrow permissions if the new export is more restrictive
        if permissions.is_narrower_or_equal(&entry.permissions) {
            entry.permissions = permissions;
        }
        cell_id
    }

    /// Release an export (decrement reference count).
    ///
    /// Returns `true` if the export was fully released (ref_count reached 0).
    pub fn release_export(&mut self, cell_id: &CellId) -> bool {
        if let Some(entry) = self.exports.get_mut(cell_id) {
            entry.ref_count = entry.ref_count.saturating_sub(1);
            if entry.ref_count == 0 {
                self.exports.remove(cell_id);
                return true;
            }
        }
        false
    }

    /// Record an import from the remote peer.
    pub fn import(&mut self, remote_cell_id: CellId, permissions: AuthRequired) {
        self.imports.insert(
            remote_cell_id,
            ImportEntry {
                remote_cell_id,
                permissions,
                live: true,
            },
        );
    }

    /// Mark an import as disconnected (not live).
    pub fn disconnect_import(&mut self, remote_cell_id: &CellId) {
        if let Some(entry) = self.imports.get_mut(remote_cell_id) {
            entry.live = false;
        }
    }

    /// Create a new pending promise, returning its ID.
    pub fn create_promise(&mut self) -> u64 {
        let id = self.next_promise_id;
        self.next_promise_id += 1;
        self.promises.insert(id, PromiseState::Pending);
        id
    }

    /// Fulfill a promise with a resolved capability.
    pub fn fulfill_promise(&mut self, promise_id: u64, cell_id: CellId) -> bool {
        if let Some(state) = self.promises.get_mut(&promise_id)
            && matches!(state, PromiseState::Pending)
        {
            *state = PromiseState::Fulfilled { cell_id };
            return true;
        }
        false
    }

    /// Break a promise (e.g., remote disconnected).
    pub fn break_promise(&mut self, promise_id: u64, reason: String) -> bool {
        if let Some(state) = self.promises.get_mut(&promise_id)
            && matches!(state, PromiseState::Pending)
        {
            *state = PromiseState::Broken { reason };
            return true;
        }
        false
    }

    /// Get the state of a promise.
    pub fn promise_state(&self, promise_id: u64) -> Option<&PromiseState> {
        self.promises.get(&promise_id)
    }

    /// Returns true if this session has any live imports or exports.
    pub fn is_active(&self) -> bool {
        !self.exports.is_empty() || self.imports.values().any(|i| i.live)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn session_export_import() {
        let mut session = CapSession::new([0x11; 32]);
        let cell = CellId([0xaa; 32]);

        // Export
        session.export(cell, AuthRequired::Signature);
        assert_eq!(session.exports.len(), 1);
        assert_eq!(session.exports[&cell].ref_count, 1);

        // Export same cell again — ref count increases
        session.export(cell, AuthRequired::Signature);
        assert_eq!(session.exports[&cell].ref_count, 2);

        // Release one ref
        assert!(!session.release_export(&cell));
        assert_eq!(session.exports[&cell].ref_count, 1);

        // Release last ref
        assert!(session.release_export(&cell));
        assert!(session.exports.is_empty());
    }

    #[test]
    fn session_promises() {
        let mut session = CapSession::new([0x22; 32]);

        let p1 = session.create_promise();
        let p2 = session.create_promise();
        assert_eq!(p1, 0);
        assert_eq!(p2, 1);

        assert!(matches!(
            session.promise_state(p1),
            Some(PromiseState::Pending)
        ));

        // Fulfill p1
        let cell = CellId([0xbb; 32]);
        assert!(session.fulfill_promise(p1, cell));
        assert!(matches!(
            session.promise_state(p1),
            Some(PromiseState::Fulfilled { .. })
        ));

        // Can't fulfill twice
        assert!(!session.fulfill_promise(p1, cell));

        // Break p2
        assert!(session.break_promise(p2, "disconnected".into()));
        assert!(matches!(
            session.promise_state(p2),
            Some(PromiseState::Broken { .. })
        ));
    }

    #[test]
    fn session_active_tracking() {
        let mut session = CapSession::new([0x33; 32]);
        assert!(!session.is_active());

        let cell = CellId([0xcc; 32]);
        session.import(cell, AuthRequired::None);
        assert!(session.is_active());

        session.disconnect_import(&cell);
        assert!(!session.is_active());

        // Export makes it active again
        session.export(CellId([0xdd; 32]), AuthRequired::Signature);
        assert!(session.is_active());
    }

    #[test]
    fn session_epoch_tracks_generation() {
        // First session: epoch 0 (default)
        let session1 = CapSession::new([0x44; 32]);
        assert_eq!(session1.epoch, 0);

        // New session with explicit epoch (simulates re-establishment)
        let session2 = CapSession::with_epoch([0x44; 32], 5);
        assert_eq!(session2.epoch, 5);

        // Epoch is distinct from the default — stale messages from epoch 0
        // should be rejected when the current session is epoch 5.
        assert_ne!(session1.epoch, session2.epoch);
    }

    #[test]
    fn session_epoch_scopes_drop_rights_per_session() {
        // F-12: session/epoch ids scope drop rights PER REF. A re-export under a new
        // epoch does NOT transfer drop rights for the old epoch's refs; each epoch may
        // drop exactly the refs it minted, and only those. (Before the F-12 fix, the
        // most-recent re-export overwrote the whole holder's session id, stealing the
        // original epoch's drop rights — and handing the new epoch the power to reclaim
        // refs it never minted.)
        use crate::FederationId;
        use crate::gc::{DropResult, ExportGcManager};

        let mut gc = ExportGcManager::new();
        let cell = CellId([0x55; 32]);
        let fed = FederationId([0x66; 32]);

        // A ref was minted during epoch 1.
        gc.record_export_with_session(cell, fed, 100, 1);
        // Epoch 1 torn down, epoch 2 established; a re-export adds a SECOND ref under
        // epoch 2 — epoch 1's ref is untouched.
        gc.record_export_with_session(cell, fed, 200, 2);
        assert_eq!(gc.get(&cell).unwrap().total_refs, 2);

        // A DropRef from epoch 2 may only drop epoch 2's ref (still held by epoch 1).
        assert_eq!(
            gc.process_drop_with_session(cell, fed, 2),
            DropResult::StillHeld
        );
        // Epoch 2 cannot then reach into epoch 1's surviving ref — rejected.
        assert_eq!(
            gc.process_drop_with_session(cell, fed, 2),
            DropResult::Invalid
        );
        assert_eq!(gc.get(&cell).unwrap().total_refs, 1);

        // Epoch 1 retains the right to drop the ref IT minted — the last ref reclaims.
        assert_eq!(
            gc.process_drop_with_session(cell, fed, 1),
            DropResult::CanRevoke
        );
    }
}
